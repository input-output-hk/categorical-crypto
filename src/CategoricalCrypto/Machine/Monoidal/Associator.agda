{-# OPTIONS --safe #-}

-- ============================================================================
-- The associator of the machine category is natural, at `_≅ᴹ_`:
--
--     ((a ⊗₁ b) ⊗₁ d) ∘ ⊗-assoc⃖  ≅ᴹ  ⊗-assoc⃖ ∘ (a ⊗₁ (b ⊗₁ d))
--
-- The forward square is derived from this one and the iso laws in
-- `CategoricalCrypto.Machine.MonoidalCategory`.
--
-- A crossing forwarder is a reindexed identity (`Xfwd-dom`/`Xfwd-cod`, in
-- `Machine.Reindex.Post`), so composing with one is a pure relabelling
-- (`∘-collapse-dom`/`∘-collapse-cod`), and each side collapses to a `Reindex`
-- of the tensor.  Normalising the two tensors to `Pair`-nests
-- (`⊗₁-norm-l`/`⊗₁-norm-r`) leaves a single pointwise equation between two
-- routings, which is a finite case split closed by `refl`.
--
-- `Machine.Monoidal.Unitors` and `Machine.Monoidal.Braiding` follow the same
-- recipe with their own normalisers.
-- ============================================================================


open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Forwarder
open import CategoricalCrypto.Machine.Reindex.Post
open import CategoricalCrypto.Machine.Reindex.Collapse
open import CategoricalCrypto.Machine.Reindex.PairAssoc

open import categorical-crypto.Prelude hiding (id; _∘_)
import Data.Sum.Base as ⊎
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults


module CategoricalCrypto.Machine.Monoidal.Associator where

open Channel

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine πᵢ ∘κᵢ cdᵢ Xφ asc3ᵢ

  -- ========================================================================
  -- Normalising a tensor to a `Pair`-nest.  `_⊗₁_` IS a `Reindex` of a `Pair`
  -- (definitionally), so all that happens here is that the nested `Reindex`es
  -- are fused and the composite routing is replaced by the permutation it
  -- computes to.
  -- ========================================================================

  nrᵢ : ∀ {A A' B B' D D'}
      → inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D')))
      → inType ((A ⊗ᵀ A') ⊗₀ ((B ⊗ᵀ B') ⊗₀ (D ⊗ᵀ D')))
  nrᵢ (inj₁ (inj₁ x))        = inj₁ (inj₁ x)
  nrᵢ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  nrᵢ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  nrᵢ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  nrᵢ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  nrᵢ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  nrₒ : ∀ {A A' B B' D D'}
      → outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D')))
      → outType ((A ⊗ᵀ A') ⊗₀ ((B ⊗ᵀ B') ⊗₀ (D ⊗ᵀ D')))
  nrₒ (inj₁ (inj₁ x))        = inj₁ (inj₁ x)
  nrₒ (inj₁ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₁ x))
  nrₒ (inj₁ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₁ x))
  nrₒ (inj₂ (inj₁ x))        = inj₁ (inj₂ x)
  nrₒ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₁ (inj₂ x))
  nrₒ (inj₂ (inj₂ (inj₂ x))) = inj₂ (inj₂ (inj₂ x))

  pt-nrᵢ : ∀ {A A' B B' D D'}
           (i : inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D'))))
         → ⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
              (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In}))
              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}) i)
           ≡ nrᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-nrᵢ (inj₁ (inj₁ _))        = refl
  pt-nrᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-nrᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-nrᵢ (inj₂ (inj₁ _))        = refl
  pt-nrᵢ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-nrᵢ (inj₂ (inj₂ (inj₂ _))) = refl

  pt-nrₒ : ∀ {A A' B B' D D'}
           (o : outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ (A' ⊗₀ (B' ⊗₀ D'))))
         → ⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
              (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out}))
              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}) o)
           ≡ nrₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-nrₒ (inj₁ (inj₁ _))        = refl
  pt-nrₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-nrₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-nrₒ (inj₂ (inj₁ _))        = refl
  pt-nrₒ (inj₂ (inj₂ (inj₁ _))) = refl
  pt-nrₒ (inj₂ (inj₂ (inj₂ _))) = refl

  ⊗₁-norm-r : ∀ {A A' B B' D D'}
              (m : Machine A A') (n₁ : Machine B B') (n₂ : Machine D D')
            → (m ⊗₁ (n₁ ⊗₁ n₂))
              ≅ᴹ Reindex (Pair m (Pair n₁ n₂)) (nrᵢ {A} {A'} {B} {B'} {D} {D'})
                                               (nrₒ {A} {A'} {B} {B'} {D} {D'})
  ⊗₁-norm-r {A} {A'} {B} {B'} {D} {D'} m n₁ n₂ =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}))
                              (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}))
                (Pair-Reindexʳ m (Pair n₁ n₂) (app (⊗σ {B} {B'} {D} {D'} {In}))
                                              (app (⊗σ {B} {B'} {D} {D'} {Out}))))
    (≅ᴹ-trans (Reindex-fuse (Pair m (Pair n₁ n₂))
                 (⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                     (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In})))
                 (⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                     (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out})))
                 (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}))
                 (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out})))
              (Reindex-cong (Pair m (Pair n₁ n₂))
                 (λ i → ⊎ᵢ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                           (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {In}))
                           (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {In}) i))
                 (nrᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → ⊎ₒ {A} {A'} {B ⊗₀ B' ᵀ} {(D ⊗₀ D' ᵀ) ᵀ} {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'}
                           (λ x → x) (app (⊗σ {B} {B'} {D} {D'} {Out}))
                           (app (⊗σ {A} {A'} {B ⊗₀ D} {B' ⊗₀ D'} {Out}) o))
                 (nrₒ {A} {A'} {B} {B'} {D} {D'}) pt-nrᵢ pt-nrₒ))

  nlᵢ : ∀ {A A' B B' D D'}
      → inType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → inType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  nlᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  nlᵢ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  nlᵢ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  nlᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  nlᵢ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  nlᵢ (inj₂ (inj₂ x))        = inj₂ (inj₂ x)

  nlₒ : ∀ {A A' B B' D D'}
      → outType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → outType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  nlₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  nlₒ (inj₁ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₁ x))
  nlₒ (inj₁ (inj₂ x))        = inj₂ (inj₁ x)
  nlₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  nlₒ (inj₂ (inj₁ (inj₂ x))) = inj₁ (inj₂ (inj₂ x))
  nlₒ (inj₂ (inj₂ x))        = inj₂ (inj₂ x)

  pt-nlᵢ : ∀ {A A' B B' D D'}
           (i : inType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → ⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
              (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x)
              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}) i)
           ≡ nlᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-nlᵢ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-nlᵢ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-nlᵢ (inj₁ (inj₂ _))        = refl
  pt-nlᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-nlᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-nlᵢ (inj₂ (inj₂ _))        = refl

  pt-nlₒ : ∀ {A A' B B' D D'}
           (o : outType (((A ⊗₀ B) ⊗₀ D) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → ⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
              (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x)
              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}) o)
           ≡ nlₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-nlₒ (inj₁ (inj₁ (inj₁ _))) = refl
  pt-nlₒ (inj₁ (inj₁ (inj₂ _))) = refl
  pt-nlₒ (inj₁ (inj₂ _))        = refl
  pt-nlₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-nlₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-nlₒ (inj₂ (inj₂ _))        = refl

  ⊗₁-norm-l : ∀ {A A' B B' D D'}
              (m : Machine A A') (n₁ : Machine B B') (n₂ : Machine D D')
            → ((m ⊗₁ n₁) ⊗₁ n₂)
              ≅ᴹ Reindex (Pair (Pair m n₁) n₂) (nlᵢ {A} {A'} {B} {B'} {D} {D'})
                                               (nlₒ {A} {A'} {B} {B'} {D} {D'})
  ⊗₁-norm-l {A} {A'} {B} {B'} {D} {D'} m n₁ n₂ =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}))
                              (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}))
                (Pair-Reindexˡ (Pair m n₁) n₂ (app (⊗σ {A} {A'} {B} {B'} {In}))
                                              (app (⊗σ {A} {A'} {B} {B'} {Out}))))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair m n₁) n₂)
                 (⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                     (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x))
                 (⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                     (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x))
                 (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}))
                 (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out})))
              (Reindex-cong (Pair (Pair m n₁) n₂)
                 (λ i → ⊎ᵢ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                           (app (⊗σ {A} {A'} {B} {B'} {In})) (λ x → x)
                           (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {In}) i))
                 (nlᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → ⊎ₒ {A ⊗₀ A' ᵀ} {(B ⊗₀ B' ᵀ) ᵀ} {D} {D'} {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'}
                           (app (⊗σ {A} {A'} {B} {B'} {Out})) (λ x → x)
                           (app (⊗σ {A ⊗₀ B} {A' ⊗₀ B'} {D} {D'} {Out}) o))
                 (nlₒ {A} {A'} {B} {B'} {D} {D'}) pt-nlᵢ pt-nlₒ))

  -- `Pair-asc3` is the bridge between the two `Pair`-nests.

  αfᵢ : ∀ {A B D} → inType (A ⊗₀ (B ⊗₀ D))
                  → inType ((A ⊗₀ B) ⊗₀ D)
  αfᵢ {A} {B} {D} = app (⊗-assoc⃖ᵢ {A} {B} {D})

  αfₒ : ∀ {A B D} → outType ((A ⊗₀ B) ⊗₀ D)
                  → outType (A ⊗₀ (B ⊗₀ D))
  αfₒ {A} {B} {D} = app (⊗-assoc⃖ₒ {A} {B} {D})

  αfᵢ⁻ : ∀ {A B D} → inType ((A ⊗₀ B) ⊗₀ D)
                   → inType (A ⊗₀ (B ⊗₀ D))
  αfᵢ⁻ = ⊎.assocʳ

  αfₒ⁻ : ∀ {A B D} → outType (A ⊗₀ (B ⊗₀ D))
                   → outType ((A ⊗₀ B) ⊗₀ D)
  αfₒ⁻ (inj₁ x)        = inj₁ (inj₁ x)
  αfₒ⁻ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  αfₒ⁻ (inj₂ (inj₂ z)) = inj₂ z

  αfₒ-l : ∀ {A B D} β → αfₒ⁻ {A} {B} {D} (αfₒ {A} {B} {D} β) ≡ β
  αfₒ-l (inj₁ (inj₁ _)) = refl
  αfₒ-l (inj₁ (inj₂ _)) = refl
  αfₒ-l (inj₂ _)        = refl

  αfₒ-r : ∀ {A B D} α → αfₒ {A} {B} {D} (αfₒ⁻ {A} {B} {D} α) ≡ α
  αfₒ-r (inj₁ _)        = refl
  αfₒ-r (inj₂ (inj₁ _)) = refl
  αfₒ-r (inj₂ (inj₂ _)) = refl

  αfᵢ-l : ∀ {A B D} a → αfᵢ⁻ {A} {B} {D} (αfᵢ {A} {B} {D} a) ≡ a
  αfᵢ-l (inj₁ _)        = refl
  αfᵢ-l (inj₂ (inj₁ _)) = refl
  αfᵢ-l (inj₂ (inj₂ _)) = refl

  αfᵢ-r : ∀ {A B D} b → αfᵢ {A} {B} {D} (αfᵢ⁻ {A} {B} {D} b) ≡ b
  αfᵢ-r (inj₁ (inj₁ _)) = refl
  αfᵢ-r (inj₁ (inj₂ _)) = refl
  αfᵢ-r (inj₂ _)        = refl

  α-Φdom : ∀ {A B D}
         → ⊗-assoc⃖ {A} {B} {D}
           ≅ᴹ Reindex (CC.id {(A ⊗₀ B) ⊗₀ D})
                (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A ⊗₀ B) ⊗₀ D} (αfᵢ {A} {B} {D}))
                (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A ⊗₀ B) ⊗₀ D} (αfₒ⁻ {A} {B} {D}))
  α-Φdom {A} {B} {D} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {A} {B} {D}) (⊗-assoc⃖ₒ {A} {B} {D}))
             (Xfwd-dom (αfᵢ {A} {B} {D}) (αfₒ {A} {B} {D}) (αfₒ⁻ {A} {B} {D}) αfₒ-l αfₒ-r)

  α-Φcod : ∀ {A B D}
         → ⊗-assoc⃖ {A} {B} {D}
           ≅ᴹ Reindex (CC.id {A ⊗₀ (B ⊗₀ D)})
                (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A ⊗₀ (B ⊗₀ D)} {(A ⊗₀ B) ⊗₀ D} (αfₒ {A} {B} {D}))
                (cdₒ {A ⊗₀ (B ⊗₀ D)} {A ⊗₀ (B ⊗₀ D)} {(A ⊗₀ B) ⊗₀ D} (αfᵢ⁻ {A} {B} {D}))
  α-Φcod {A} {B} {D} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {A} {B} {D}) (⊗-assoc⃖ₒ {A} {B} {D}))
             (Xfwd-cod (αfᵢ {A} {B} {D}) (αfₒ {A} {B} {D}) (αfᵢ⁻ {A} {B} {D}) αfᵢ-l αfᵢ-r)

  α-lhs : ∀ {A A' B B' D D'} (a : Machine A A') (b : Machine B B') (d : Machine D D')
        → (((a ⊗₁ b) ⊗₁ d) CC.∘ ⊗-assoc⃖ {A} {B} {D})
          ≅ᴹ Reindex ((a ⊗₁ b) ⊗₁ d)
               (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ {A} {B} {D}))
               (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ⁻ {A} {B} {D}))
  α-lhs {A} {A'} {B} {B'} {D} {D'} a b d =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (α-Φdom {A} {B} {D}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {(A ⊗₀ B) ⊗₀ D}) ((a ⊗₁ b) ⊗₁ d)
                              (αfᵢ {A} {B} {D}) (αfₒ⁻ {A} {B} {D}))
              (Reindex-resp-≅ᴹ
                 (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ {A} {B} {D}))
                 (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ⁻ {A} {B} {D}))
                 ∘-identityʳ-≅ᴹ))

  α-rhs : ∀ {A A' B B' D D'} (a : Machine A A') (b : Machine B B') (d : Machine D D')
        → (⊗-assoc⃖ {A'} {B'} {D'} CC.∘ (a ⊗₁ (b ⊗₁ d)))
          ≅ᴹ Reindex (a ⊗₁ (b ⊗₁ d))
               (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ {A'} {B'} {D'}))
               (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ⁻ {A'} {B'} {D'}))
  α-rhs {A} {A'} {B} {B'} {D} {D'} a b d =
    ≅ᴹ-trans (∘-resp-≅ᴹ (α-Φcod {A'} {B'} {D'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod (a ⊗₁ (b ⊗₁ d)) (CC.id {A' ⊗₀ (B' ⊗₀ D')})
                              (αfₒ {A'} {B'} {D'}) (αfᵢ⁻ {A'} {B'} {D'}))
              (Reindex-resp-≅ᴹ
                 (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ {A'} {B'} {D'}))
                 (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ⁻ {A'} {B'} {D'}))
                 ∘-identityˡ-≅ᴹ))

  αNᵢ : ∀ {A A' B B' D D'}
      → inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → inType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  αNᵢ (inj₁ (inj₁ x))        = inj₁ (inj₁ (inj₁ x))
  αNᵢ (inj₁ (inj₂ (inj₁ y))) = inj₁ (inj₂ (inj₁ y))
  αNᵢ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₁ z)
  αNᵢ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  αNᵢ (inj₂ (inj₁ (inj₂ y))) = inj₁ (inj₂ (inj₂ y))
  αNᵢ (inj₂ (inj₂ z))        = inj₂ (inj₂ z)

  αNₒ : ∀ {A A' B B' D D'}
      → outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D'))
      → outType (((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B')) ⊗₀ (D ⊗ᵀ D'))
  αNₒ (inj₁ (inj₁ x))        = inj₁ (inj₁ (inj₁ x))
  αNₒ (inj₁ (inj₂ (inj₁ y))) = inj₁ (inj₂ (inj₁ y))
  αNₒ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₁ z)
  αNₒ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  αNₒ (inj₂ (inj₁ (inj₂ y))) = inj₁ (inj₂ (inj₂ y))
  αNₒ (inj₂ (inj₂ z))        = inj₂ (inj₂ z)

  pt-αLᵢ : ∀ {A A' B B' D D'}
           (i : inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → nlᵢ {A} {A'} {B} {B'} {D} {D'}
             (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ {A} {B} {D}) i)
           ≡ αNᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-αLᵢ (inj₁ (inj₁ _))        = refl
  pt-αLᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-αLᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-αLᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-αLᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-αLᵢ (inj₂ (inj₂ _))        = refl

  pt-αLₒ : ∀ {A A' B B' D D'}
           (o : outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → nlₒ {A} {A'} {B} {B'} {D} {D'}
             (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ⁻ {A} {B} {D}) o)
           ≡ αNₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-αLₒ (inj₁ (inj₁ _))        = refl
  pt-αLₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-αLₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-αLₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-αLₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-αLₒ (inj₂ (inj₂ _))        = refl

  pt-αRᵢ : ∀ {A A' B B' D D'}
           (i : inType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → asc3ᵢ {A} {A'} {B} {B'} {D} {D'}
             (nrᵢ {A} {A'} {B} {B'} {D} {D'}
               (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                    (αfₒ {A'} {B'} {D'}) i))
           ≡ αNᵢ {A} {A'} {B} {B'} {D} {D'} i
  pt-αRᵢ (inj₁ (inj₁ _))        = refl
  pt-αRᵢ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-αRᵢ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-αRᵢ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-αRᵢ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-αRᵢ (inj₂ (inj₂ _))        = refl

  pt-αRₒ : ∀ {A A' B B' D D'}
           (o : outType ((A ⊗₀ (B ⊗₀ D)) ⊗ᵀ ((A' ⊗₀ B') ⊗₀ D')))
         → asc3ₒ {A} {A'} {B} {B'} {D} {D'}
             (nrₒ {A} {A'} {B} {B'} {D} {D'}
               (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                    (αfᵢ⁻ {A'} {B'} {D'}) o))
           ≡ αNₒ {A} {A'} {B} {B'} {D} {D'} o
  pt-αRₒ (inj₁ (inj₁ _))        = refl
  pt-αRₒ (inj₁ (inj₂ (inj₁ _))) = refl
  pt-αRₒ (inj₁ (inj₂ (inj₂ _))) = refl
  pt-αRₒ (inj₂ (inj₁ (inj₁ _))) = refl
  pt-αRₒ (inj₂ (inj₁ (inj₂ _))) = refl
  pt-αRₒ (inj₂ (inj₂ _))        = refl

  α-lhs-norm : ∀ {A A' B B' D D'} (a : Machine A A') (b : Machine B B') (d : Machine D D')
             → (((a ⊗₁ b) ⊗₁ d) CC.∘ ⊗-assoc⃖ {A} {B} {D})
               ≅ᴹ Reindex (Pair (Pair a b) d) (αNᵢ {A} {A'} {B} {B'} {D} {D'})
                                              (αNₒ {A} {A'} {B} {B'} {D} {D'})
  α-lhs-norm {A} {A'} {B} {B'} {D} {D'} a b d =
    ≅ᴹ-trans (α-lhs a b d)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ {A} {B} {D}))
                 (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ⁻ {A} {B} {D}))
                 (⊗₁-norm-l a b d))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair a b) d)
                 (nlᵢ {A} {A'} {B} {B'} {D} {D'})
                 (nlₒ {A} {A'} {B} {B'} {D} {D'})
                 (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ {A} {B} {D}))
                 (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ⁻ {A} {B} {D})))
              (Reindex-cong (Pair (Pair a b) d)
                 (λ i → nlᵢ {A} {A'} {B} {B'} {D} {D'}
                            (dmᵢ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfᵢ {A} {B} {D}) i))
                 (αNᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → nlₒ {A} {A'} {B} {B'} {D} {D'}
                            (dmₒ {(A ⊗₀ B) ⊗₀ D} {A ⊗₀ (B ⊗₀ D)} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfₒ⁻ {A} {B} {D}) o))
                 (αNₒ {A} {A'} {B} {B'} {D} {D'}) pt-αLᵢ pt-αLₒ)))

  α-rhs-norm : ∀ {A A' B B' D D'} (a : Machine A A') (b : Machine B B') (d : Machine D D')
             → (⊗-assoc⃖ {A'} {B'} {D'} CC.∘ (a ⊗₁ (b ⊗₁ d)))
               ≅ᴹ Reindex (Pair (Pair a b) d) (αNᵢ {A} {A'} {B} {B'} {D} {D'})
                                              (αNₒ {A} {A'} {B} {B'} {D} {D'})
  α-rhs-norm {A} {A'} {B} {B'} {D} {D'} a b d =
    ≅ᴹ-trans (α-rhs a b d)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ {A'} {B'} {D'}))
                 (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ⁻ {A'} {B'} {D'}))
                 (⊗₁-norm-r a b d))
    (≅ᴹ-trans (Reindex-fuse (Pair a (Pair b d))
                 (nrᵢ {A} {A'} {B} {B'} {D} {D'})
                 (nrₒ {A} {A'} {B} {B'} {D} {D'})
                 (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfₒ {A'} {B'} {D'}))
                 (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'} (αfᵢ⁻ {A'} {B'} {D'})))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (λ i → nrᵢ {A} {A'} {B} {B'} {D} {D'}
                            (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfₒ {A'} {B'} {D'}) i))
                 (λ o → nrₒ {A} {A'} {B} {B'} {D} {D'}
                            (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfᵢ⁻ {A'} {B'} {D'}) o))
                 (Pair-asc3 a b d))
    (≅ᴹ-trans (Reindex-fuse (Pair (Pair a b) d)
                 (asc3ᵢ {A} {A'} {B} {B'} {D} {D'})
                 (asc3ₒ {A} {A'} {B} {B'} {D} {D'})
                 (λ i → nrᵢ {A} {A'} {B} {B'} {D} {D'}
                            (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfₒ {A'} {B'} {D'}) i))
                 (λ o → nrₒ {A} {A'} {B} {B'} {D} {D'}
                            (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfᵢ⁻ {A'} {B'} {D'}) o)))
              (Reindex-cong (Pair (Pair a b) d)
                 (λ i → asc3ᵢ {A} {A'} {B} {B'} {D} {D'}
                          (nrᵢ {A} {A'} {B} {B'} {D} {D'}
                            (cdᵢ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfₒ {A'} {B'} {D'}) i)))
                 (αNᵢ {A} {A'} {B} {B'} {D} {D'})
                 (λ o → asc3ₒ {A} {A'} {B} {B'} {D} {D'}
                          (nrₒ {A} {A'} {B} {B'} {D} {D'}
                            (cdₒ {A ⊗₀ (B ⊗₀ D)} {A' ⊗₀ (B' ⊗₀ D')} {(A' ⊗₀ B') ⊗₀ D'}
                                 (αfᵢ⁻ {A'} {B'} {D'}) o)))
                 (αNₒ {A} {A'} {B} {B'} {D} {D'}) pt-αRᵢ pt-αRₒ)))))

  ⊗-assoc⃖-natural : ∀ {A A' B B' D D'}
                     (a : Machine A A') (b : Machine B B') (d : Machine D D')
                   → (((a ⊗₁ b) ⊗₁ d) CC.∘ ⊗-assoc⃖)
                     ≅ᴹ (⊗-assoc⃖ CC.∘ (a ⊗₁ (b ⊗₁ d)))
  ⊗-assoc⃖-natural a b d =
    ≅ᴹ-trans (α-lhs-norm a b d) (≅ᴹ-sym (α-rhs-norm a b d))

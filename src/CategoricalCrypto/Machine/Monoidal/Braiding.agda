{-# OPTIONS --safe #-}

-- ============================================================================
-- Naturality of the symmetry `⊗-symₘ`:
--
--     ⊗-symₘ ∘ (f ⊗₁ g)  ≅ᴹ  (g ⊗₁ f) ∘ ⊗-symₘ
--
-- The proof follows `CategoricalCrypto.Machine.Monoidal.Naturality` to the
-- letter.  `⊗-symₘ` is a crossing forwarder, hence a reindexed identity
-- (`Xfwd-dom`/`Xfwd-cod`), so composing with it is a pure relabelling
-- (`∘-collapse-dom`/`∘-collapse-cod`) and each side collapses to a `Reindex`
-- of a tensor.  A tensor IS a `Reindex` of a `Pair`, so fusing leaves one
-- `Reindex (Pair f g) …` on the left and one `Reindex (Pair g f) …` on the
-- right; `Pair-swap` bridges the two nests, and what remains is a pointwise
-- equation between two routings, a four-way case split closed by `refl`.
-- ============================================================================

open import CategoricalCrypto.Machine.Iso using (∘-identityˡ-≅ᴹ; ∘-identityʳ-≅ᴹ)
open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Forwarder
open import CategoricalCrypto.Machine.Reindex.FwdId
open import CategoricalCrypto.Machine.Reindex.Collapse
open import CategoricalCrypto.Machine.Reindex.Swap

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Monoidal.Braiding where

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine πᵢ ∘κᵢ cdᵢ Xφ swᵢ

  -- ---- `⊗-symₘ`'s message maps, and their inverses ----------------------

  σfᵢ : ∀ {A B} → Channel.inType (A ⊗₀ B) → Channel.inType (B ⊗₀ A)
  σfᵢ {A} {B} = app (⊗-symᵢ {A} {B})

  σfₒ : ∀ {A B} → Channel.outType (B ⊗₀ A) → Channel.outType (A ⊗₀ B)
  σfₒ {A} {B} = app (⊗-symₒ {A} {B})

  σfᵢ⁻ : ∀ {A B} → Channel.inType (B ⊗₀ A) → Channel.inType (A ⊗₀ B)
  σfᵢ⁻ (inj₁ b) = inj₂ b
  σfᵢ⁻ (inj₂ a) = inj₁ a

  σfₒ⁻ : ∀ {A B} → Channel.outType (A ⊗₀ B) → Channel.outType (B ⊗₀ A)
  σfₒ⁻ (inj₁ a) = inj₂ a
  σfₒ⁻ (inj₂ b) = inj₁ b

  σfₒ-l : ∀ {A B} β → σfₒ⁻ {A} {B} (σfₒ {A} {B} β) ≡ β
  σfₒ-l (inj₁ _) = refl
  σfₒ-l (inj₂ _) = refl

  σfₒ-r : ∀ {A B} α → σfₒ {A} {B} (σfₒ⁻ {A} {B} α) ≡ α
  σfₒ-r (inj₁ _) = refl
  σfₒ-r (inj₂ _) = refl

  σfᵢ-l : ∀ {A B} a → σfᵢ⁻ {A} {B} (σfᵢ {A} {B} a) ≡ a
  σfᵢ-l (inj₁ _) = refl
  σfᵢ-l (inj₂ _) = refl

  σfᵢ-r : ∀ {A B} b → σfᵢ {A} {B} (σfᵢ⁻ {A} {B} b) ≡ b
  σfᵢ-r (inj₁ _) = refl
  σfᵢ-r (inj₂ _) = refl

  -- ---- the forwarder as a reindexed identity, both ways -----------------

  σ-Φdom : ∀ {A B}
         → ⊗-symₘ {A} {B}
           ≅ᴹ Reindex (CC.id {B ⊗₀ A})
                (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B ⊗₀ A} (σfᵢ {A} {B}))
                (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B ⊗₀ A} (σfₒ⁻ {A} {B}))
  σ-Φdom {A} {B} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-symᵢ {A} {B}) (⊗-symₒ {A} {B}))
             (Xfwd-dom (σfᵢ {A} {B}) (σfₒ {A} {B}) (σfₒ⁻ {A} {B}) σfₒ-l σfₒ-r)

  σ-Φcod : ∀ {A B}
         → ⊗-symₘ {A} {B}
           ≅ᴹ Reindex (CC.id {A ⊗₀ B})
                (cdᵢ {A ⊗₀ B} {A ⊗₀ B} {B ⊗₀ A} (σfₒ {A} {B}))
                (cdₒ {A ⊗₀ B} {A ⊗₀ B} {B ⊗₀ A} (σfᵢ⁻ {A} {B}))
  σ-Φcod {A} {B} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-symᵢ {A} {B}) (⊗-symₒ {A} {B}))
             (Xfwd-cod (σfᵢ {A} {B}) (σfₒ {A} {B}) (σfᵢ⁻ {A} {B}) σfᵢ-l σfᵢ-r)

  -- ---- the two collapses ------------------------------------------------

  σ-lhs : ∀ {A A' B B'} (f : Machine A A') (g : Machine B B')
        → (⊗-symₘ {A'} {B'} CC.∘ (f ⊗₁ g))
          ≅ᴹ Reindex (f ⊗₁ g)
               (cdᵢ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfₒ {A'} {B'}))
               (cdₒ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfᵢ⁻ {A'} {B'}))
  σ-lhs {A} {A'} {B} {B'} f g =
    ≅ᴹ-trans (∘-resp-≅ᴹ (σ-Φcod {A'} {B'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod (f ⊗₁ g) (CC.id {A' ⊗₀ B'})
                              (σfₒ {A'} {B'}) (σfᵢ⁻ {A'} {B'}))
              (Reindex-resp-≅ᴹ
                 (cdᵢ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfₒ {A'} {B'}))
                 (cdₒ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfᵢ⁻ {A'} {B'}))
                 ∘-identityˡ-≅ᴹ))

  σ-rhs : ∀ {A A' B B'} (f : Machine A A') (g : Machine B B')
        → ((g ⊗₁ f) CC.∘ ⊗-symₘ {A} {B})
          ≅ᴹ Reindex (g ⊗₁ f)
               (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}))
               (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}))
  σ-rhs {A} {A'} {B} {B'} f g =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (σ-Φdom {A} {B}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {B ⊗₀ A}) (g ⊗₁ f)
                              (σfᵢ {A} {B}) (σfₒ⁻ {A} {B}))
              (Reindex-resp-≅ᴹ
                 (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}))
                 (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}))
                 ∘-identityʳ-≅ᴹ))

  -- ---- the one routing both sides produce, into the `Pair f g` nest -----

  σNᵢ : ∀ {A A' B B'}
      → Channel.inType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A'))
      → Channel.inType ((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B'))
  σNᵢ (inj₁ (inj₁ a))  = inj₁ (inj₁ a)
  σNᵢ (inj₁ (inj₂ b))  = inj₂ (inj₁ b)
  σNᵢ (inj₂ (inj₁ b')) = inj₂ (inj₂ b')
  σNᵢ (inj₂ (inj₂ a')) = inj₁ (inj₂ a')

  σNₒ : ∀ {A A' B B'}
      → Channel.outType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A'))
      → Channel.outType ((A ⊗ᵀ A') ⊗₀ (B ⊗ᵀ B'))
  σNₒ (inj₁ (inj₁ a))  = inj₁ (inj₁ a)
  σNₒ (inj₁ (inj₂ b))  = inj₂ (inj₁ b)
  σNₒ (inj₂ (inj₁ b')) = inj₂ (inj₂ b')
  σNₒ (inj₂ (inj₂ a')) = inj₁ (inj₂ a')

  pt-σLᵢ : ∀ {A A' B B'} (i : Channel.inType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A')))
         → app (⊗σ {A} {A'} {B} {B'} {In})
             (cdᵢ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfₒ {A'} {B'}) i)
           ≡ σNᵢ {A} {A'} {B} {B'} i
  pt-σLᵢ (inj₁ (inj₁ _)) = refl
  pt-σLᵢ (inj₁ (inj₂ _)) = refl
  pt-σLᵢ (inj₂ (inj₁ _)) = refl
  pt-σLᵢ (inj₂ (inj₂ _)) = refl

  pt-σLₒ : ∀ {A A' B B'} (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A')))
         → app (⊗σ {A} {A'} {B} {B'} {Out})
             (cdₒ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfᵢ⁻ {A'} {B'}) o)
           ≡ σNₒ {A} {A'} {B} {B'} o
  pt-σLₒ (inj₁ (inj₁ _)) = refl
  pt-σLₒ (inj₁ (inj₂ _)) = refl
  pt-σLₒ (inj₂ (inj₁ _)) = refl
  pt-σLₒ (inj₂ (inj₂ _)) = refl

  pt-σRᵢ : ∀ {A A' B B'} (i : Channel.inType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A')))
         → swᵢ {B} {B'} {A} {A'}
             (app (⊗σ {B} {B'} {A} {A'} {In})
               (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}) i))
           ≡ σNᵢ {A} {A'} {B} {B'} i
  pt-σRᵢ (inj₁ (inj₁ _)) = refl
  pt-σRᵢ (inj₁ (inj₂ _)) = refl
  pt-σRᵢ (inj₂ (inj₁ _)) = refl
  pt-σRᵢ (inj₂ (inj₂ _)) = refl

  pt-σRₒ : ∀ {A A' B B'} (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (B' ⊗₀ A')))
         → swₒ {B} {B'} {A} {A'}
             (app (⊗σ {B} {B'} {A} {A'} {Out})
               (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}) o))
           ≡ σNₒ {A} {A'} {B} {B'} o
  pt-σRₒ (inj₁ (inj₁ _)) = refl
  pt-σRₒ (inj₁ (inj₂ _)) = refl
  pt-σRₒ (inj₂ (inj₁ _)) = refl
  pt-σRₒ (inj₂ (inj₂ _)) = refl

  -- ---- the two sides, normalised to the same `Reindex` -------------------

  -- `f ⊗₁ g` IS `Reindex (Pair f g) (app ⊗σ) (app ⊗σ)`, so the outer
  -- relabelling fuses straight in.
  σ-lhs-norm : ∀ {A A' B B'} (f : Machine A A') (g : Machine B B')
             → (⊗-symₘ {A'} {B'} CC.∘ (f ⊗₁ g))
               ≅ᴹ Reindex (Pair f g) (σNᵢ {A} {A'} {B} {B'}) (σNₒ {A} {A'} {B} {B'})
  σ-lhs-norm {A} {A'} {B} {B'} f g =
    ≅ᴹ-trans (σ-lhs f g)
    (≅ᴹ-trans (Reindex-fuse (Pair f g)
                 (app (⊗σ {A} {A'} {B} {B'} {In}))
                 (app (⊗σ {A} {A'} {B} {B'} {Out}))
                 (cdᵢ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfₒ {A'} {B'}))
                 (cdₒ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfᵢ⁻ {A'} {B'})))
              (Reindex-cong (Pair f g)
                 (λ i → app (⊗σ {A} {A'} {B} {B'} {In})
                            (cdᵢ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfₒ {A'} {B'}) i))
                 (σNᵢ {A} {A'} {B} {B'})
                 (λ o → app (⊗σ {A} {A'} {B} {B'} {Out})
                            (cdₒ {A ⊗₀ B} {A' ⊗₀ B'} {B' ⊗₀ A'} (σfᵢ⁻ {A'} {B'}) o))
                 (σNₒ {A} {A'} {B} {B'}) pt-σLᵢ pt-σLₒ))

  -- The right side lands in the `Pair g f` nest; `Pair-swap` turns it around.
  σ-rhs-norm : ∀ {A A' B B'} (f : Machine A A') (g : Machine B B')
             → ((g ⊗₁ f) CC.∘ ⊗-symₘ {A} {B})
               ≅ᴹ Reindex (Pair f g) (σNᵢ {A} {A'} {B} {B'}) (σNₒ {A} {A'} {B} {B'})
  σ-rhs-norm {A} {A'} {B} {B'} f g =
    ≅ᴹ-trans (σ-rhs f g)
    (≅ᴹ-trans (Reindex-fuse (Pair g f)
                 (app (⊗σ {B} {B'} {A} {A'} {In}))
                 (app (⊗σ {B} {B'} {A} {A'} {Out}))
                 (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}))
                 (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B})))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ
                 (λ i → app (⊗σ {B} {B'} {A} {A'} {In})
                            (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}) i))
                 (λ o → app (⊗σ {B} {B'} {A} {A'} {Out})
                            (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}) o))
                 (Pair-swap g f))
    (≅ᴹ-trans (Reindex-fuse (Pair f g)
                 (swᵢ {B} {B'} {A} {A'})
                 (swₒ {B} {B'} {A} {A'})
                 (λ i → app (⊗σ {B} {B'} {A} {A'} {In})
                            (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}) i))
                 (λ o → app (⊗σ {B} {B'} {A} {A'} {Out})
                            (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}) o)))
              (Reindex-cong (Pair f g)
                 (λ i → swᵢ {B} {B'} {A} {A'}
                          (app (⊗σ {B} {B'} {A} {A'} {In})
                            (dmᵢ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfᵢ {A} {B}) i)))
                 (σNᵢ {A} {A'} {B} {B'})
                 (λ o → swₒ {B} {B'} {A} {A'}
                          (app (⊗σ {B} {B'} {A} {A'} {Out})
                            (dmₒ {B ⊗₀ A} {A ⊗₀ B} {B' ⊗₀ A'} (σfₒ⁻ {A} {B}) o)))
                 (σNₒ {A} {A'} {B} {B'}) pt-σRᵢ pt-σRₒ))))

  -- ========================================================================
  -- `⊗-symₘ` is natural.
  -- ========================================================================

  σ-natural : ∀ {A A' B B'} (f : Machine A A') (g : Machine B B')
            → (⊗-symₘ {A'} {B'} CC.∘ (f ⊗₁ g)) ≅ᴹ ((g ⊗₁ f) CC.∘ ⊗-symₘ {A} {B})
  σ-natural f g = ≅ᴹ-trans (σ-lhs-norm f g) (≅ᴹ-sym (σ-rhs-norm f g))

{-# OPTIONS --safe #-}

-- ============================================================================
-- Naturality of the two unitors, `λ⇒ : I ⊗₀ A → A` and `ρ⇒ : A ⊗₀ I → A`:
--
--     λ⇒ ∘ (id ⊗₁ f)  ≅ᴹ  f ∘ λ⇒            ρ⇒ ∘ (f ⊗₁ id)  ≅ᴹ  f ∘ ρ⇒
--
-- The recipe is the one `Machine.Monoidal.Naturality` uses for the
-- associator.  A unitor is a total-function forwarder, hence a reindexed
-- identity (`Xfwd-dom`/`Xfwd-cod`), so composing with it is a pure relabelling
-- (`∘-collapse-dom`/`∘-collapse-cod`) and each side collapses to a `Reindex`
-- of a tensor once the identity is cancelled.  The one structural fact needed
-- here is that tensoring with `CC.id {I}` is itself a relabelling of `f`
-- (`Pair-unitˡ`/`Pair-unitʳ`): the unit channel has no messages, so the
-- identity on it never steps.  What remains is a pointwise equation between
-- two routings, closed by a finite case split and `refl`.
-- ============================================================================

open import CategoricalCrypto.Machine.Category using (∘-identityˡ-≅ᴹ; ∘-identityʳ-≅ᴹ)
open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Forwarder
open import CategoricalCrypto.Machine.Reindex.FwdId
open import CategoricalCrypto.Machine.Reindex.Collapse
open import CategoricalCrypto.Machine.Reindex.Unit

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Monoidal.Unitors where

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine πᵢ ∘κᵢ cdᵢ Xφ unitˡᵢ

  -- ========================================================================
  -- The left unitor `λ⇒` is natural.
  -- ========================================================================

  -- ---- `λ⇒`'s message maps, and their inverses ---------------------------

  λfᵢ : ∀ {A} → Channel.inType (I ⊗₀ A) → Channel.inType A
  λfᵢ {A} = app (⊗-left-neutral {In} {A})

  λfₒ : ∀ {A} → Channel.outType A → Channel.outType (I ⊗₀ A)
  λfₒ {A} = app (⊗-left-intro {Out} {I} {A})

  λfᵢ⁻ : ∀ {A} → Channel.inType A → Channel.inType (I ⊗₀ A)
  λfᵢ⁻ a = inj₂ a

  λfₒ⁻ : ∀ {A} → Channel.outType (I ⊗₀ A) → Channel.outType A
  λfₒ⁻ (inj₁ ())
  λfₒ⁻ (inj₂ α) = α

  λfₒ-l : ∀ {A} (β : Channel.outType A) → λfₒ⁻ {A} (λfₒ {A} β) ≡ β
  λfₒ-l _ = refl

  λfₒ-r : ∀ {A} (α : Channel.outType (I ⊗₀ A)) → λfₒ {A} (λfₒ⁻ {A} α) ≡ α
  λfₒ-r (inj₁ ())
  λfₒ-r (inj₂ _) = refl

  λfᵢ-l : ∀ {A} (a : Channel.inType (I ⊗₀ A)) → λfᵢ⁻ {A} (λfᵢ {A} a) ≡ a
  λfᵢ-l (inj₁ ())
  λfᵢ-l (inj₂ _) = refl

  λfᵢ-r : ∀ {A} (b : Channel.inType A) → λfᵢ {A} (λfᵢ⁻ {A} b) ≡ b
  λfᵢ-r _ = refl

  -- ---- the forwarder as a reindexed identity, both ways -----------------

  λ-Φdom : ∀ {A}
         → λ⇒ {A}
           ≅ᴹ Reindex (CC.id {A}) (dmᵢ {A} {I ⊗₀ A} {A} (λfᵢ {A}))
                                  (dmₒ {A} {I ⊗₀ A} {A} (λfₒ⁻ {A}))
  λ-Φdom {A} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-left-neutral {In} {A}) (⊗-left-intro {Out} {I} {A}))
             (Xfwd-dom (λfᵢ {A}) (λfₒ {A}) (λfₒ⁻ {A}) (λfₒ-l {A}) (λfₒ-r {A}))

  λ-Φcod : ∀ {A}
         → λ⇒ {A}
           ≅ᴹ Reindex (CC.id {I ⊗₀ A}) (cdᵢ {I ⊗₀ A} {I ⊗₀ A} {A} (λfₒ {A}))
                                        (cdₒ {I ⊗₀ A} {I ⊗₀ A} {A} (λfᵢ⁻ {A}))
  λ-Φcod {A} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-left-neutral {In} {A}) (⊗-left-intro {Out} {I} {A}))
             (Xfwd-cod (λfᵢ {A}) (λfₒ {A}) (λfᵢ⁻ {A}) (λfᵢ-l {A}) (λfᵢ-r {A}))

  -- ---- the two collapses ------------------------------------------------

  λ-lhs : ∀ {A A'} (f : Machine A A')
        → (λ⇒ {A'} CC.∘ (CC.id {I} ⊗₁ f))
          ≅ᴹ Reindex (CC.id {I} ⊗₁ f) (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}))
                                        (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'}))
  λ-lhs {A} {A'} f =
    ≅ᴹ-trans (∘-resp-≅ᴹ (λ-Φcod {A'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod (CC.id {I} ⊗₁ f) (CC.id {I ⊗₀ A'}) (λfₒ {A'}) (λfᵢ⁻ {A'}))
              (Reindex-resp-≅ᴹ (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}))
                               (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'}))
                               ∘-identityˡ-≅ᴹ))

  λ-rhs : ∀ {A A'} (f : Machine A A')
        → (f CC.∘ λ⇒ {A})
          ≅ᴹ Reindex f (dmᵢ {A} {I ⊗₀ A} {A'} (λfᵢ {A})) (dmₒ {A} {I ⊗₀ A} {A'} (λfₒ⁻ {A}))
  λ-rhs {A} {A'} f =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (λ-Φdom {A}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {A}) f (λfᵢ {A}) (λfₒ⁻ {A}))
              (Reindex-resp-≅ᴹ (dmᵢ {A} {I ⊗₀ A} {A'} (λfᵢ {A}))
                               (dmₒ {A} {I ⊗₀ A} {A'} (λfₒ⁻ {A}))
                               ∘-identityʳ-≅ᴹ))

  -- ---- `CC.id {I} ⊗₁ f` as a `Reindex` of `f` ----------------------------

  λTᵢ : ∀ {A A'} → Channel.inType ((I ⊗₀ A) ⊗ᵀ (I ⊗₀ A')) → Channel.inType (A ⊗ᵀ A')
  λTᵢ (inj₁ (inj₁ ()))
  λTᵢ (inj₁ (inj₂ a))  = inj₁ a
  λTᵢ (inj₂ (inj₁ ()))
  λTᵢ (inj₂ (inj₂ a')) = inj₂ a'

  λTₒ : ∀ {A A'} → Channel.outType ((I ⊗₀ A) ⊗ᵀ (I ⊗₀ A')) → Channel.outType (A ⊗ᵀ A')
  λTₒ (inj₁ (inj₁ ()))
  λTₒ (inj₁ (inj₂ a))  = inj₁ a
  λTₒ (inj₂ (inj₁ ()))
  λTₒ (inj₂ (inj₂ a')) = inj₂ a'

  pt-λTᵢ : ∀ {A A'} (i : Channel.inType ((I ⊗₀ A) ⊗ᵀ (I ⊗₀ A')))
         → unitˡᵢ {A} {A'} (app (⊗σ {I} {I} {A} {A'} {In}) i) ≡ λTᵢ {A} {A'} i
  pt-λTᵢ (inj₁ (inj₁ ()))
  pt-λTᵢ (inj₁ (inj₂ _)) = refl
  pt-λTᵢ (inj₂ (inj₁ ()))
  pt-λTᵢ (inj₂ (inj₂ _)) = refl

  pt-λTₒ : ∀ {A A'} (o : Channel.outType ((I ⊗₀ A) ⊗ᵀ (I ⊗₀ A')))
         → unitˡₒ {A} {A'} (app (⊗σ {I} {I} {A} {A'} {Out}) o) ≡ λTₒ {A} {A'} o
  pt-λTₒ (inj₁ (inj₁ ()))
  pt-λTₒ (inj₁ (inj₂ _)) = refl
  pt-λTₒ (inj₂ (inj₁ ()))
  pt-λTₒ (inj₂ (inj₂ _)) = refl

  ⊗₁-unitˡ : ∀ {A A'} (f : Machine A A')
           → (CC.id {I} ⊗₁ f) ≅ᴹ Reindex f (λTᵢ {A} {A'}) (λTₒ {A} {A'})
  ⊗₁-unitˡ {A} {A'} f =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {I} {I} {A} {A'} {In}))
                              (app (⊗σ {I} {I} {A} {A'} {Out}))
                              (Pair-unitˡ f))
    (≅ᴹ-trans (Reindex-fuse f (unitˡᵢ {A} {A'}) (unitˡₒ {A} {A'})
                 (app (⊗σ {I} {I} {A} {A'} {In})) (app (⊗σ {I} {I} {A} {A'} {Out})))
              (Reindex-cong f
                 (λ i → unitˡᵢ {A} {A'} (app (⊗σ {I} {I} {A} {A'} {In}) i))
                 (λTᵢ {A} {A'})
                 (λ o → unitˡₒ {A} {A'} (app (⊗σ {I} {I} {A} {A'} {Out}) o))
                 (λTₒ {A} {A'}) pt-λTᵢ pt-λTₒ))

  -- ---- the one routing both sides produce -------------------------------

  λNᵢ : ∀ {A A'} → Channel.inType ((I ⊗₀ A) ⊗ᵀ A') → Channel.inType (A ⊗ᵀ A')
  λNᵢ (inj₁ (inj₁ ()))
  λNᵢ (inj₁ (inj₂ a)) = inj₁ a
  λNᵢ (inj₂ b)        = inj₂ b

  λNₒ : ∀ {A A'} → Channel.outType ((I ⊗₀ A) ⊗ᵀ A') → Channel.outType (A ⊗ᵀ A')
  λNₒ (inj₁ (inj₁ ()))
  λNₒ (inj₁ (inj₂ a)) = inj₁ a
  λNₒ (inj₂ b)        = inj₂ b

  pt-λLᵢ : ∀ {A A'} (i : Channel.inType ((I ⊗₀ A) ⊗ᵀ A'))
         → λTᵢ {A} {A'} (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}) i) ≡ λNᵢ {A} {A'} i
  pt-λLᵢ (inj₁ (inj₁ ()))
  pt-λLᵢ (inj₁ (inj₂ _)) = refl
  pt-λLᵢ (inj₂ _)        = refl

  pt-λLₒ : ∀ {A A'} (o : Channel.outType ((I ⊗₀ A) ⊗ᵀ A'))
         → λTₒ {A} {A'} (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'}) o) ≡ λNₒ {A} {A'} o
  pt-λLₒ (inj₁ (inj₁ ()))
  pt-λLₒ (inj₁ (inj₂ _)) = refl
  pt-λLₒ (inj₂ _)        = refl

  pt-λRᵢ : ∀ {A A'} (i : Channel.inType ((I ⊗₀ A) ⊗ᵀ A'))
         → dmᵢ {A} {I ⊗₀ A} {A'} (λfᵢ {A}) i ≡ λNᵢ {A} {A'} i
  pt-λRᵢ (inj₁ (inj₁ ()))
  pt-λRᵢ (inj₁ (inj₂ _)) = refl
  pt-λRᵢ (inj₂ _)        = refl

  pt-λRₒ : ∀ {A A'} (o : Channel.outType ((I ⊗₀ A) ⊗ᵀ A'))
         → dmₒ {A} {I ⊗₀ A} {A'} (λfₒ⁻ {A}) o ≡ λNₒ {A} {A'} o
  pt-λRₒ (inj₁ (inj₁ ()))
  pt-λRₒ (inj₁ (inj₂ _)) = refl
  pt-λRₒ (inj₂ _)        = refl

  -- ---- the two sides, normalised to the same `Reindex` -------------------

  λ-lhs-norm : ∀ {A A'} (f : Machine A A')
             → (λ⇒ {A'} CC.∘ (CC.id {I} ⊗₁ f))
               ≅ᴹ Reindex f (λNᵢ {A} {A'}) (λNₒ {A} {A'})
  λ-lhs-norm {A} {A'} f =
    ≅ᴹ-trans (λ-lhs f)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}))
                               (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'}))
                               (⊗₁-unitˡ f))
    (≅ᴹ-trans (Reindex-fuse f (λTᵢ {A} {A'}) (λTₒ {A} {A'})
                 (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}))
                 (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'})))
              (Reindex-cong f
                 (λ i → λTᵢ {A} {A'} (cdᵢ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfₒ {A'}) i))
                 (λNᵢ {A} {A'})
                 (λ o → λTₒ {A} {A'} (cdₒ {I ⊗₀ A} {I ⊗₀ A'} {A'} (λfᵢ⁻ {A'}) o))
                 (λNₒ {A} {A'}) pt-λLᵢ pt-λLₒ)))

  λ-rhs-norm : ∀ {A A'} (f : Machine A A')
             → (f CC.∘ λ⇒ {A}) ≅ᴹ Reindex f (λNᵢ {A} {A'}) (λNₒ {A} {A'})
  λ-rhs-norm {A} {A'} f =
    ≅ᴹ-trans (λ-rhs f)
             (Reindex-cong f
                (dmᵢ {A} {I ⊗₀ A} {A'} (λfᵢ {A})) (λNᵢ {A} {A'})
                (dmₒ {A} {I ⊗₀ A} {A'} (λfₒ⁻ {A})) (λNₒ {A} {A'}) pt-λRᵢ pt-λRₒ)

  -- ---- `λ⇒` is natural ----------------------------------------------------

  λ⇒-natural : ∀ {A A'} (f : Machine A A')
             → (λ⇒ {A'} CC.∘ (CC.id {I} ⊗₁ f)) ≅ᴹ (f CC.∘ λ⇒ {A})
  λ⇒-natural f = ≅ᴹ-trans (λ-lhs-norm f) (≅ᴹ-sym (λ-rhs-norm f))

  -- ========================================================================
  -- The right unitor `ρ⇒` is natural.  Mirror image of the above, with the
  -- unit on the other side of every sum.
  -- ========================================================================

  -- ---- `ρ⇒`'s message maps, and their inverses ---------------------------

  ρfᵢ : ∀ {A} → Channel.inType (A ⊗₀ I) → Channel.inType A
  ρfᵢ {A} = app (⊗-right-neutral {In} {A})

  ρfₒ : ∀ {A} → Channel.outType A → Channel.outType (A ⊗₀ I)
  ρfₒ {A} = app (⊗-right-intro {Out} {A} {I})

  ρfᵢ⁻ : ∀ {A} → Channel.inType A → Channel.inType (A ⊗₀ I)
  ρfᵢ⁻ a = inj₁ a

  ρfₒ⁻ : ∀ {A} → Channel.outType (A ⊗₀ I) → Channel.outType A
  ρfₒ⁻ (inj₁ α) = α
  ρfₒ⁻ (inj₂ ())

  ρfₒ-l : ∀ {A} (β : Channel.outType A) → ρfₒ⁻ {A} (ρfₒ {A} β) ≡ β
  ρfₒ-l _ = refl

  ρfₒ-r : ∀ {A} (α : Channel.outType (A ⊗₀ I)) → ρfₒ {A} (ρfₒ⁻ {A} α) ≡ α
  ρfₒ-r (inj₁ _) = refl
  ρfₒ-r (inj₂ ())

  ρfᵢ-l : ∀ {A} (a : Channel.inType (A ⊗₀ I)) → ρfᵢ⁻ {A} (ρfᵢ {A} a) ≡ a
  ρfᵢ-l (inj₁ _) = refl
  ρfᵢ-l (inj₂ ())

  ρfᵢ-r : ∀ {A} (b : Channel.inType A) → ρfᵢ {A} (ρfᵢ⁻ {A} b) ≡ b
  ρfᵢ-r _ = refl

  -- ---- the forwarder as a reindexed identity, both ways -----------------

  ρ-Φdom : ∀ {A}
         → ρ⇒ {A}
           ≅ᴹ Reindex (CC.id {A}) (dmᵢ {A} {A ⊗₀ I} {A} (ρfᵢ {A}))
                                  (dmₒ {A} {A ⊗₀ I} {A} (ρfₒ⁻ {A}))
  ρ-Φdom {A} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-right-neutral {In} {A}) (⊗-right-intro {Out} {A} {I}))
             (Xfwd-dom (ρfᵢ {A}) (ρfₒ {A}) (ρfₒ⁻ {A}) (ρfₒ-l {A}) (ρfₒ-r {A}))

  ρ-Φcod : ∀ {A}
         → ρ⇒ {A}
           ≅ᴹ Reindex (CC.id {A ⊗₀ I}) (cdᵢ {A ⊗₀ I} {A ⊗₀ I} {A} (ρfₒ {A}))
                                        (cdₒ {A ⊗₀ I} {A ⊗₀ I} {A} (ρfᵢ⁻ {A}))
  ρ-Φcod {A} =
    ≅ᴹ-trans (tfm'-is-Xfwd (⊗-right-neutral {In} {A}) (⊗-right-intro {Out} {A} {I}))
             (Xfwd-cod (ρfᵢ {A}) (ρfₒ {A}) (ρfᵢ⁻ {A}) (ρfᵢ-l {A}) (ρfᵢ-r {A}))

  -- ---- the two collapses ------------------------------------------------

  ρ-lhs : ∀ {A A'} (f : Machine A A')
        → (ρ⇒ {A'} CC.∘ (f ⊗₁ CC.id {I}))
          ≅ᴹ Reindex (f ⊗₁ CC.id {I}) (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}))
                                        (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'}))
  ρ-lhs {A} {A'} f =
    ≅ᴹ-trans (∘-resp-≅ᴹ (ρ-Φcod {A'}) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-collapse-cod (f ⊗₁ CC.id {I}) (CC.id {A' ⊗₀ I}) (ρfₒ {A'}) (ρfᵢ⁻ {A'}))
              (Reindex-resp-≅ᴹ (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}))
                               (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'}))
                               ∘-identityˡ-≅ᴹ))

  ρ-rhs : ∀ {A A'} (f : Machine A A')
        → (f CC.∘ ρ⇒ {A})
          ≅ᴹ Reindex f (dmᵢ {A} {A ⊗₀ I} {A'} (ρfᵢ {A})) (dmₒ {A} {A ⊗₀ I} {A'} (ρfₒ⁻ {A}))
  ρ-rhs {A} {A'} f =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (ρ-Φdom {A}))
    (≅ᴹ-trans (∘-collapse-dom (CC.id {A}) f (ρfᵢ {A}) (ρfₒ⁻ {A}))
              (Reindex-resp-≅ᴹ (dmᵢ {A} {A ⊗₀ I} {A'} (ρfᵢ {A}))
                               (dmₒ {A} {A ⊗₀ I} {A'} (ρfₒ⁻ {A}))
                               ∘-identityʳ-≅ᴹ))

  -- ---- `f ⊗₁ CC.id {I}` as a `Reindex` of `f` ----------------------------

  ρTᵢ : ∀ {A A'} → Channel.inType ((A ⊗₀ I) ⊗ᵀ (A' ⊗₀ I)) → Channel.inType (A ⊗ᵀ A')
  ρTᵢ (inj₁ (inj₁ a))  = inj₁ a
  ρTᵢ (inj₁ (inj₂ ()))
  ρTᵢ (inj₂ (inj₁ a')) = inj₂ a'
  ρTᵢ (inj₂ (inj₂ ()))

  ρTₒ : ∀ {A A'} → Channel.outType ((A ⊗₀ I) ⊗ᵀ (A' ⊗₀ I)) → Channel.outType (A ⊗ᵀ A')
  ρTₒ (inj₁ (inj₁ a))  = inj₁ a
  ρTₒ (inj₁ (inj₂ ()))
  ρTₒ (inj₂ (inj₁ a')) = inj₂ a'
  ρTₒ (inj₂ (inj₂ ()))

  pt-ρTᵢ : ∀ {A A'} (i : Channel.inType ((A ⊗₀ I) ⊗ᵀ (A' ⊗₀ I)))
         → unitʳᵢ {A} {A'} (app (⊗σ {A} {A'} {I} {I} {In}) i) ≡ ρTᵢ {A} {A'} i
  pt-ρTᵢ (inj₁ (inj₁ _)) = refl
  pt-ρTᵢ (inj₁ (inj₂ ()))
  pt-ρTᵢ (inj₂ (inj₁ _)) = refl
  pt-ρTᵢ (inj₂ (inj₂ ()))

  pt-ρTₒ : ∀ {A A'} (o : Channel.outType ((A ⊗₀ I) ⊗ᵀ (A' ⊗₀ I)))
         → unitʳₒ {A} {A'} (app (⊗σ {A} {A'} {I} {I} {Out}) o) ≡ ρTₒ {A} {A'} o
  pt-ρTₒ (inj₁ (inj₁ _)) = refl
  pt-ρTₒ (inj₁ (inj₂ ()))
  pt-ρTₒ (inj₂ (inj₁ _)) = refl
  pt-ρTₒ (inj₂ (inj₂ ()))

  ⊗₁-unitʳ : ∀ {A A'} (f : Machine A A')
           → (f ⊗₁ CC.id {I}) ≅ᴹ Reindex f (ρTᵢ {A} {A'}) (ρTₒ {A} {A'})
  ⊗₁-unitʳ {A} {A'} f =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A} {A'} {I} {I} {In}))
                              (app (⊗σ {A} {A'} {I} {I} {Out}))
                              (Pair-unitʳ f))
    (≅ᴹ-trans (Reindex-fuse f (unitʳᵢ {A} {A'}) (unitʳₒ {A} {A'})
                 (app (⊗σ {A} {A'} {I} {I} {In})) (app (⊗σ {A} {A'} {I} {I} {Out})))
              (Reindex-cong f
                 (λ i → unitʳᵢ {A} {A'} (app (⊗σ {A} {A'} {I} {I} {In}) i))
                 (ρTᵢ {A} {A'})
                 (λ o → unitʳₒ {A} {A'} (app (⊗σ {A} {A'} {I} {I} {Out}) o))
                 (ρTₒ {A} {A'}) pt-ρTᵢ pt-ρTₒ))

  -- ---- the one routing both sides produce -------------------------------

  ρNᵢ : ∀ {A A'} → Channel.inType ((A ⊗₀ I) ⊗ᵀ A') → Channel.inType (A ⊗ᵀ A')
  ρNᵢ (inj₁ (inj₁ a)) = inj₁ a
  ρNᵢ (inj₁ (inj₂ ()))
  ρNᵢ (inj₂ b)        = inj₂ b

  ρNₒ : ∀ {A A'} → Channel.outType ((A ⊗₀ I) ⊗ᵀ A') → Channel.outType (A ⊗ᵀ A')
  ρNₒ (inj₁ (inj₁ a)) = inj₁ a
  ρNₒ (inj₁ (inj₂ ()))
  ρNₒ (inj₂ b)        = inj₂ b

  pt-ρLᵢ : ∀ {A A'} (i : Channel.inType ((A ⊗₀ I) ⊗ᵀ A'))
         → ρTᵢ {A} {A'} (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}) i) ≡ ρNᵢ {A} {A'} i
  pt-ρLᵢ (inj₁ (inj₁ _)) = refl
  pt-ρLᵢ (inj₁ (inj₂ ()))
  pt-ρLᵢ (inj₂ _)        = refl

  pt-ρLₒ : ∀ {A A'} (o : Channel.outType ((A ⊗₀ I) ⊗ᵀ A'))
         → ρTₒ {A} {A'} (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'}) o) ≡ ρNₒ {A} {A'} o
  pt-ρLₒ (inj₁ (inj₁ _)) = refl
  pt-ρLₒ (inj₁ (inj₂ ()))
  pt-ρLₒ (inj₂ _)        = refl

  pt-ρRᵢ : ∀ {A A'} (i : Channel.inType ((A ⊗₀ I) ⊗ᵀ A'))
         → dmᵢ {A} {A ⊗₀ I} {A'} (ρfᵢ {A}) i ≡ ρNᵢ {A} {A'} i
  pt-ρRᵢ (inj₁ (inj₁ _)) = refl
  pt-ρRᵢ (inj₁ (inj₂ ()))
  pt-ρRᵢ (inj₂ _)        = refl

  pt-ρRₒ : ∀ {A A'} (o : Channel.outType ((A ⊗₀ I) ⊗ᵀ A'))
         → dmₒ {A} {A ⊗₀ I} {A'} (ρfₒ⁻ {A}) o ≡ ρNₒ {A} {A'} o
  pt-ρRₒ (inj₁ (inj₁ _)) = refl
  pt-ρRₒ (inj₁ (inj₂ ()))
  pt-ρRₒ (inj₂ _)        = refl

  -- ---- the two sides, normalised to the same `Reindex` -------------------

  ρ-lhs-norm : ∀ {A A'} (f : Machine A A')
             → (ρ⇒ {A'} CC.∘ (f ⊗₁ CC.id {I}))
               ≅ᴹ Reindex f (ρNᵢ {A} {A'}) (ρNₒ {A} {A'})
  ρ-lhs-norm {A} {A'} f =
    ≅ᴹ-trans (ρ-lhs f)
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}))
                               (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'}))
                               (⊗₁-unitʳ f))
    (≅ᴹ-trans (Reindex-fuse f (ρTᵢ {A} {A'}) (ρTₒ {A} {A'})
                 (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}))
                 (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'})))
              (Reindex-cong f
                 (λ i → ρTᵢ {A} {A'} (cdᵢ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfₒ {A'}) i))
                 (ρNᵢ {A} {A'})
                 (λ o → ρTₒ {A} {A'} (cdₒ {A ⊗₀ I} {A' ⊗₀ I} {A'} (ρfᵢ⁻ {A'}) o))
                 (ρNₒ {A} {A'}) pt-ρLᵢ pt-ρLₒ)))

  ρ-rhs-norm : ∀ {A A'} (f : Machine A A')
             → (f CC.∘ ρ⇒ {A}) ≅ᴹ Reindex f (ρNᵢ {A} {A'}) (ρNₒ {A} {A'})
  ρ-rhs-norm {A} {A'} f =
    ≅ᴹ-trans (ρ-rhs f)
             (Reindex-cong f
                (dmᵢ {A} {A ⊗₀ I} {A'} (ρfᵢ {A})) (ρNᵢ {A} {A'})
                (dmₒ {A} {A ⊗₀ I} {A'} (ρfₒ⁻ {A})) (ρNₒ {A} {A'}) pt-ρRᵢ pt-ρRₒ)

  -- ---- `ρ⇒` is natural ----------------------------------------------------

  ρ⇒-natural : ∀ {A A'} (f : Machine A A')
             → (ρ⇒ {A'} CC.∘ (f ⊗₁ CC.id {I})) ≅ᴹ (f CC.∘ ρ⇒ {A})
  ρ⇒-natural f = ≅ᴹ-trans (ρ-lhs-norm f) (≅ᴹ-sym (ρ-rhs-norm f))

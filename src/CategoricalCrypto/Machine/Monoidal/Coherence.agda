{-# OPTIONS --safe #-}

-- ============================================================================
-- The coherence laws of the structural forwarders of `Machine.Core`: the
-- associator, the unitors and the symmetry are isomorphisms, they satisfy the
-- triangle, pentagon and hexagon identities, and the Kleisli shuffles
-- (`∘ᴷ-fwd`, `mid4`, `⊗ᴷ-fwd`, `absorb-regroup`) are composites of them.
--
-- Every machine involved is a crossing forwarder, so each side of each law
-- collapses to a single `Xfwd` through `Machine.Forwarder`'s algebra
-- (`tfm'-is-Xfwd`, `∘-Xfwd`, `⊗₁-Xfwd`), and `Xfwd-≅ᴹ` reduces the law to a
-- pointwise equation between two routings of the same channel atoms.  Each
-- routing is the atom-preserving bijection between two bracketings, and there
-- is only one, so every case is `refl` (or absurd, for a port of `I`).
--
-- Those computations are what needs the `unfolding`: `app` of a `⇒-solver`
-- term does not reduce until `_⊗₀_` does, and `⊗mapᵢ`/`⊗mapₒ` sit inside
-- `Machine.Forwarder`'s own `opaque` block, which `Xφ` opens.
-- ============================================================================

open import CategoricalCrypto.Machine.Forwarder
  using (∘-Xfwd; ⊗₁-Xfwd; Xfwd-≅ᴹ; Xφ; Xfwd; ⊗mapᵢ; ⊗mapₒ;
         tfm'-is-Xfwd; id-is-Xfwd)

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Monoidal.Coherence where

open Channel

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion
            ⊗-combine Xφ

  ∘-collapse : ∀ {A B C} {M : Machine B C} {N : Machine A B}
               {f₂ : inType B → inType C} {g₂ : outType C → outType B}
               {f₁ : inType A → inType B} {g₁ : outType B → outType A}
             → M ≅ᴹ Xfwd f₂ g₂ → N ≅ᴹ Xfwd f₁ g₁
             → (M CC.∘ N) ≅ᴹ Xfwd (λ a → f₂ (f₁ a)) (λ o → g₁ (g₂ o))
  ∘-collapse φ ψ = ≅ᴹ-trans (∘-resp-≅ᴹ φ ψ) ∘-Xfwd

  ⊗-collapse : ∀ {A B C D} {M : Machine A B} {N : Machine C D}
               {f₁ : inType A → inType B} {g₁ : outType B → outType A}
               {f₂ : inType C → inType D} {g₂ : outType D → outType C}
             → M ≅ᴹ Xfwd f₁ g₁ → N ≅ᴹ Xfwd f₂ g₂
             → (M ⊗₁ N) ≅ᴹ Xfwd (⊗mapᵢ f₁ f₂) (⊗mapₒ g₁ g₂)
  ⊗-collapse φ ψ = ≅ᴹ-trans (⊗₁-resp-≅ᴹ φ ψ) ⊗₁-Xfwd

  Xfwd-bridge : ∀ {A B} {M N : Machine A B}
                {f f' : inType A → inType B}
                {g g' : outType B → outType A}
              → M ≅ᴹ Xfwd f g → N ≅ᴹ Xfwd f' g'
              → (∀ a → f a ≡ f' a) → (∀ o → g o ≡ g' o) → M ≅ᴹ N
  Xfwd-bridge φ ψ ef eg = ≅ᴹ-trans φ (≅ᴹ-trans (Xfwd-≅ᴹ ef eg) (≅ᴹ-sym ψ))

  α-isoˡ : ∀ {A B C} → (⊗-assoc⃖ {A} {B} {C} CC.∘ ⊗-assoc {A} {B} {C}) ≅ᴹ CC.id
  α-isoˡ {A} {B} {C} =
    Xfwd-bridge lhs id-is-Xfwd
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
    where
    lhs : (⊗-assoc⃖ {A} {B} {C} CC.∘ ⊗-assoc {A} {B} {C})
          ≅ᴹ Xfwd (λ a → app (⊗-assoc⃖ᵢ {A} {B} {C}) (app (⊗-assocᵢ {A} {B} {C}) a))
                  (λ o → app (⊗-assocₒ {A} {B} {C}) (app (⊗-assoc⃖ₒ {A} {B} {C}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {A} {B} {C}) (⊗-assoc⃖ₒ {A} {B} {C}))
                     (tfm'-is-Xfwd (⊗-assocᵢ {A} {B} {C}) (⊗-assocₒ {A} {B} {C}))

  α-isoʳ : ∀ {A B C} → (⊗-assoc {A} {B} {C} CC.∘ ⊗-assoc⃖ {A} {B} {C}) ≅ᴹ CC.id
  α-isoʳ {A} {B} {C} =
    Xfwd-bridge lhs id-is-Xfwd
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
    where
    lhs : (⊗-assoc {A} {B} {C} CC.∘ ⊗-assoc⃖ {A} {B} {C})
          ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {A} {B} {C}) (app (⊗-assoc⃖ᵢ {A} {B} {C}) a))
                  (λ o → app (⊗-assoc⃖ₒ {A} {B} {C}) (app (⊗-assocₒ {A} {B} {C}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {A} {B} {C}) (⊗-assocₒ {A} {B} {C}))
                     (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {A} {B} {C}) (⊗-assoc⃖ₒ {A} {B} {C}))

  ρ-isoˡ : ∀ {A} → (ρ⇐ {A} CC.∘ ρ⇒ {A}) ≅ᴹ CC.id
  ρ-isoˡ {A} =
    Xfwd-bridge lhs id-is-Xfwd
      (λ { (inj₁ _) → refl ; (inj₂ ()) })
      (λ { (inj₁ _) → refl ; (inj₂ ()) })
    where
    lhs : (ρ⇐ {A} CC.∘ ρ⇒ {A})
          ≅ᴹ Xfwd (λ a → app (⊗-right-intro {In} {A} {I}) (app (⊗-right-neutral {In} {A}) a))
                  (λ o → app (⊗-right-intro {Out} {A} {I}) (app (⊗-right-neutral {Out} {A}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-right-intro {In} {A} {I}) (⊗-right-neutral {Out} {A}))
                     (tfm'-is-Xfwd (⊗-right-neutral {In} {A}) (⊗-right-intro {Out} {A} {I}))

  ρ-isoʳ : ∀ {A} → (ρ⇒ {A} CC.∘ ρ⇐ {A}) ≅ᴹ CC.id
  ρ-isoʳ {A} = Xfwd-bridge lhs id-is-Xfwd (λ _ → refl) (λ _ → refl)
    where
    lhs : (ρ⇒ {A} CC.∘ ρ⇐ {A})
          ≅ᴹ Xfwd (λ a → app (⊗-right-neutral {In} {A}) (app (⊗-right-intro {In} {A} {I}) a))
                  (λ o → app (⊗-right-neutral {Out} {A}) (app (⊗-right-intro {Out} {A} {I}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-right-neutral {In} {A}) (⊗-right-intro {Out} {A} {I}))
                     (tfm'-is-Xfwd (⊗-right-intro {In} {A} {I}) (⊗-right-neutral {Out} {A}))

  λ-isoˡ : ∀ {A} → (λ⇐ {A} CC.∘ λ⇒ {A}) ≅ᴹ CC.id
  λ-isoˡ {A} =
    Xfwd-bridge lhs id-is-Xfwd
      (λ { (inj₁ ()) ; (inj₂ _) → refl })
      (λ { (inj₁ ()) ; (inj₂ _) → refl })
    where
    lhs : (λ⇐ {A} CC.∘ λ⇒ {A})
          ≅ᴹ Xfwd (λ a → app (⊗-left-intro {In} {I} {A}) (app (⊗-left-neutral {In} {A}) a))
                  (λ o → app (⊗-left-intro {Out} {I} {A}) (app (⊗-left-neutral {Out} {A}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-left-intro {In} {I} {A}) (⊗-left-neutral {Out} {A}))
                     (tfm'-is-Xfwd (⊗-left-neutral {In} {A}) (⊗-left-intro {Out} {I} {A}))

  λ-isoʳ : ∀ {A} → (λ⇒ {A} CC.∘ λ⇐ {A}) ≅ᴹ CC.id
  λ-isoʳ {A} = Xfwd-bridge lhs id-is-Xfwd (λ _ → refl) (λ _ → refl)
    where
    lhs : (λ⇒ {A} CC.∘ λ⇐ {A})
          ≅ᴹ Xfwd (λ a → app (⊗-left-neutral {In} {A}) (app (⊗-left-intro {In} {I} {A}) a))
                  (λ o → app (⊗-left-neutral {Out} {A}) (app (⊗-left-intro {Out} {I} {A}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-left-neutral {In} {A}) (⊗-left-intro {Out} {I} {A}))
                     (tfm'-is-Xfwd (⊗-left-intro {In} {I} {A}) (⊗-left-neutral {Out} {A}))

  σ-σ : ∀ {A B} → (⊗-symₘ {B} {A} CC.∘ ⊗-symₘ {A} {B}) ≅ᴹ CC.id
  σ-σ {A} {B} =
    Xfwd-bridge lhs id-is-Xfwd
      (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
    where
    lhs : (⊗-symₘ {B} {A} CC.∘ ⊗-symₘ {A} {B})
          ≅ᴹ Xfwd (λ a → app (⊗-symᵢ {B} {A}) (app (⊗-symᵢ {A} {B}) a))
                  (λ o → app (⊗-symₒ {A} {B}) (app (⊗-symₒ {B} {A}) o))
    lhs = ∘-collapse (tfm'-is-Xfwd (⊗-symᵢ {B} {A}) (⊗-symₒ {B} {A}))
                     (tfm'-is-Xfwd (⊗-symᵢ {A} {B}) (⊗-symₒ {A} {B}))

  triangle : ∀ {A B} → ((CC.id {A} ⊗₁ λ⇒ {B}) CC.∘ ⊗-assoc {A} {I} {B}) ≅ᴹ (ρ⇒ {A} ⊗₁ CC.id {B})
  triangle {A} {B} =
    Xfwd-bridge lhs rhs
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ ())) ; (inj₂ _) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
    where
    l₁ : (CC.id {A} ⊗₁ λ⇒ {B})
         ≅ᴹ Xfwd (⊗mapᵢ {A} {A} {I ⊗₀ B} {B} (λ x → x) (app (⊗-left-neutral {In} {B})))
                 (⊗mapₒ {A} {A} {I ⊗₀ B} {B} (λ x → x) (app (⊗-left-intro {Out} {I} {B})))
    l₁ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-left-neutral {In} {B}) (⊗-left-intro {Out} {I} {B}))

    lhs : ((CC.id {A} ⊗₁ λ⇒ {B}) CC.∘ ⊗-assoc {A} {I} {B})
          ≅ᴹ Xfwd (λ a → ⊗mapᵢ {A} {A} {I ⊗₀ B} {B} (λ x → x) (app (⊗-left-neutral {In} {B}))
                                (app (⊗-assocᵢ {A} {I} {B}) a))
                  (λ o → app (⊗-assocₒ {A} {I} {B})
                             (⊗mapₒ {A} {A} {I ⊗₀ B} {B} (λ x → x) (app (⊗-left-intro {Out} {I} {B})) o))
    lhs = ∘-collapse l₁ (tfm'-is-Xfwd (⊗-assocᵢ {A} {I} {B}) (⊗-assocₒ {A} {I} {B}))

    rhs : (ρ⇒ {A} ⊗₁ CC.id {B})
          ≅ᴹ Xfwd (⊗mapᵢ {A ⊗₀ I} {A} {B} {B} (app (⊗-right-neutral {In} {A})) (λ x → x))
                  (⊗mapₒ {A ⊗₀ I} {A} {B} {B} (app (⊗-right-intro {Out} {A} {I})) (λ x → x))
    rhs = ⊗-collapse (tfm'-is-Xfwd (⊗-right-neutral {In} {A}) (⊗-right-intro {Out} {A} {I})) id-is-Xfwd

  pentagon : ∀ {A B C D}
           → ((CC.id {A} ⊗₁ ⊗-assoc {B} {C} {D})
              CC.∘ (⊗-assoc {A} {B ⊗₀ C} {D} CC.∘ (⊗-assoc {A} {B} {C} ⊗₁ CC.id {D})))
             ≅ᴹ (⊗-assoc {A} {B} {C ⊗₀ D} CC.∘ ⊗-assoc {A ⊗₀ B} {C} {D})
  pentagon {A} {B} {C} {D} =
    Xfwd-bridge lhs rhs
      (λ { (inj₁ (inj₁ (inj₁ _))) → refl ; (inj₁ (inj₁ (inj₂ _))) → refl
         ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl
         ; (inj₂ (inj₂ (inj₁ _))) → refl ; (inj₂ (inj₂ (inj₂ _))) → refl })
    where
    l₁ : (⊗-assoc {A} {B} {C} ⊗₁ CC.id {D})
         ≅ᴹ Xfwd (⊗mapᵢ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocᵢ {A} {B} {C})) (λ x → x))
                 (⊗mapₒ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocₒ {A} {B} {C})) (λ x → x))
    l₁ = ⊗-collapse (tfm'-is-Xfwd (⊗-assocᵢ {A} {B} {C}) (⊗-assocₒ {A} {B} {C})) id-is-Xfwd

    l₂ : (⊗-assoc {A} {B ⊗₀ C} {D} CC.∘ (⊗-assoc {A} {B} {C} ⊗₁ CC.id {D}))
         ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {A} {B ⊗₀ C} {D})
                            (⊗mapᵢ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocᵢ {A} {B} {C})) (λ x → x) a))
                 (λ o → ⊗mapₒ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocₒ {A} {B} {C})) (λ x → x)
                              (app (⊗-assocₒ {A} {B ⊗₀ C} {D}) o))
    l₂ = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {A} {B ⊗₀ C} {D}) (⊗-assocₒ {A} {B ⊗₀ C} {D})) l₁

    l₃ : (CC.id {A} ⊗₁ ⊗-assoc {B} {C} {D})
         ≅ᴹ Xfwd (⊗mapᵢ {A} {A} {(B ⊗₀ C) ⊗₀ D} {B ⊗₀ (C ⊗₀ D)} (λ x → x) (app (⊗-assocᵢ {B} {C} {D})))
                 (⊗mapₒ {A} {A} {(B ⊗₀ C) ⊗₀ D} {B ⊗₀ (C ⊗₀ D)} (λ x → x) (app (⊗-assocₒ {B} {C} {D})))
    l₃ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-assocᵢ {B} {C} {D}) (⊗-assocₒ {B} {C} {D}))

    lhs : ((CC.id {A} ⊗₁ ⊗-assoc {B} {C} {D})
           CC.∘ (⊗-assoc {A} {B ⊗₀ C} {D} CC.∘ (⊗-assoc {A} {B} {C} ⊗₁ CC.id {D})))
          ≅ᴹ Xfwd (λ a → ⊗mapᵢ {A} {A} {(B ⊗₀ C) ⊗₀ D} {B ⊗₀ (C ⊗₀ D)} (λ x → x) (app (⊗-assocᵢ {B} {C} {D}))
                           (app (⊗-assocᵢ {A} {B ⊗₀ C} {D})
                                (⊗mapᵢ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocᵢ {A} {B} {C})) (λ x → x) a)))
                  (λ o → ⊗mapₒ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)} {D} {D} (app (⊗-assocₒ {A} {B} {C})) (λ x → x)
                           (app (⊗-assocₒ {A} {B ⊗₀ C} {D})
                                (⊗mapₒ {A} {A} {(B ⊗₀ C) ⊗₀ D} {B ⊗₀ (C ⊗₀ D)} (λ x → x) (app (⊗-assocₒ {B} {C} {D})) o)))
    lhs = ∘-collapse l₃ l₂

    rhs : (⊗-assoc {A} {B} {C ⊗₀ D} CC.∘ ⊗-assoc {A ⊗₀ B} {C} {D})
          ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {A} {B} {C ⊗₀ D}) (app (⊗-assocᵢ {A ⊗₀ B} {C} {D}) a))
                  (λ o → app (⊗-assocₒ {A ⊗₀ B} {C} {D}) (app (⊗-assocₒ {A} {B} {C ⊗₀ D}) o))
    rhs = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {A} {B} {C ⊗₀ D}) (⊗-assocₒ {A} {B} {C ⊗₀ D}))
                     (tfm'-is-Xfwd (⊗-assocᵢ {A ⊗₀ B} {C} {D}) (⊗-assocₒ {A ⊗₀ B} {C} {D}))

  hexagon : ∀ {A B C}
          → ((CC.id {B} ⊗₁ ⊗-symₘ {A} {C})
             CC.∘ (⊗-assoc {B} {A} {C} CC.∘ (⊗-symₘ {A} {B} ⊗₁ CC.id {C})))
            ≅ᴹ (⊗-assoc {B} {C} {A} CC.∘ (⊗-symₘ {A} {B ⊗₀ C} CC.∘ ⊗-assoc {A} {B} {C}))
  hexagon {A} {B} {C} =
    Xfwd-bridge lhs rhs
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
    where
    l₁ : (⊗-symₘ {A} {B} ⊗₁ CC.id {C})
         ≅ᴹ Xfwd (⊗mapᵢ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symᵢ {A} {B})) (λ x → x))
                 (⊗mapₒ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symₒ {A} {B})) (λ x → x))
    l₁ = ⊗-collapse (tfm'-is-Xfwd (⊗-symᵢ {A} {B}) (⊗-symₒ {A} {B})) id-is-Xfwd

    l₂ : (⊗-assoc {B} {A} {C} CC.∘ (⊗-symₘ {A} {B} ⊗₁ CC.id {C}))
         ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {B} {A} {C})
                            (⊗mapᵢ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symᵢ {A} {B})) (λ x → x) a))
                 (λ o → ⊗mapₒ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symₒ {A} {B})) (λ x → x)
                              (app (⊗-assocₒ {B} {A} {C}) o))
    l₂ = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {B} {A} {C}) (⊗-assocₒ {B} {A} {C})) l₁

    l₃ : (CC.id {B} ⊗₁ ⊗-symₘ {A} {C})
         ≅ᴹ Xfwd (⊗mapᵢ {B} {B} {A ⊗₀ C} {C ⊗₀ A} (λ x → x) (app (⊗-symᵢ {A} {C})))
                 (⊗mapₒ {B} {B} {A ⊗₀ C} {C ⊗₀ A} (λ x → x) (app (⊗-symₒ {A} {C})))
    l₃ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-symᵢ {A} {C}) (⊗-symₒ {A} {C}))

    lhs : ((CC.id {B} ⊗₁ ⊗-symₘ {A} {C})
           CC.∘ (⊗-assoc {B} {A} {C} CC.∘ (⊗-symₘ {A} {B} ⊗₁ CC.id {C})))
          ≅ᴹ Xfwd (λ a → ⊗mapᵢ {B} {B} {A ⊗₀ C} {C ⊗₀ A} (λ x → x) (app (⊗-symᵢ {A} {C}))
                           (app (⊗-assocᵢ {B} {A} {C})
                                (⊗mapᵢ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symᵢ {A} {B})) (λ x → x) a)))
                  (λ o → ⊗mapₒ {A ⊗₀ B} {B ⊗₀ A} {C} {C} (app (⊗-symₒ {A} {B})) (λ x → x)
                           (app (⊗-assocₒ {B} {A} {C})
                                (⊗mapₒ {B} {B} {A ⊗₀ C} {C ⊗₀ A} (λ x → x) (app (⊗-symₒ {A} {C})) o)))
    lhs = ∘-collapse l₃ l₂

    r₁ : (⊗-symₘ {A} {B ⊗₀ C} CC.∘ ⊗-assoc {A} {B} {C})
         ≅ᴹ Xfwd (λ a → app (⊗-symᵢ {A} {B ⊗₀ C}) (app (⊗-assocᵢ {A} {B} {C}) a))
                 (λ o → app (⊗-assocₒ {A} {B} {C}) (app (⊗-symₒ {A} {B ⊗₀ C}) o))
    r₁ = ∘-collapse (tfm'-is-Xfwd (⊗-symᵢ {A} {B ⊗₀ C}) (⊗-symₒ {A} {B ⊗₀ C}))
                    (tfm'-is-Xfwd (⊗-assocᵢ {A} {B} {C}) (⊗-assocₒ {A} {B} {C}))

    rhs : (⊗-assoc {B} {C} {A} CC.∘ (⊗-symₘ {A} {B ⊗₀ C} CC.∘ ⊗-assoc {A} {B} {C}))
          ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {B} {C} {A})
                             (app (⊗-symᵢ {A} {B ⊗₀ C}) (app (⊗-assocᵢ {A} {B} {C}) a)))
                  (λ o → app (⊗-assocₒ {A} {B} {C})
                             (app (⊗-symₒ {A} {B ⊗₀ C}) (app (⊗-assocₒ {B} {C} {A}) o)))
    rhs = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {B} {C} {A}) (⊗-assocₒ {B} {C} {A})) r₁

  ∘ᴷ-fwd-decomp : ∀ {C E₁ E₂}
    → ∘ᴷ-fwd {C} {E₁} {E₂} ≅ᴹ ((CC.id {C} ⊗₁ ⊗-symₘ {E₂} {E₁}) CC.∘ ⊗-assoc {C} {E₂} {E₁})
  ∘ᴷ-fwd-decomp {C} {E₁} {E₂} =
    Xfwd-bridge (tfm'-is-Xfwd (∘ᴷ-fwdᵢ {C} {E₁} {E₂}) (∘ᴷ-fwdₒ {C} {E₁} {E₂})) rhs
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
    where
    r₁ : (CC.id {C} ⊗₁ ⊗-symₘ {E₂} {E₁})
         ≅ᴹ Xfwd (⊗mapᵢ {C} {C} {E₂ ⊗₀ E₁} {E₁ ⊗₀ E₂} (λ x → x) (app (⊗-symᵢ {E₂} {E₁})))
                 (⊗mapₒ {C} {C} {E₂ ⊗₀ E₁} {E₁ ⊗₀ E₂} (λ x → x) (app (⊗-symₒ {E₂} {E₁})))
    r₁ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-symᵢ {E₂} {E₁}) (⊗-symₒ {E₂} {E₁}))

    rhs : ((CC.id {C} ⊗₁ ⊗-symₘ {E₂} {E₁}) CC.∘ ⊗-assoc {C} {E₂} {E₁})
          ≅ᴹ Xfwd (λ a → ⊗mapᵢ {C} {C} {E₂ ⊗₀ E₁} {E₁ ⊗₀ E₂} (λ x → x) (app (⊗-symᵢ {E₂} {E₁}))
                                (app (⊗-assocᵢ {C} {E₂} {E₁}) a))
                  (λ o → app (⊗-assocₒ {C} {E₂} {E₁})
                             (⊗mapₒ {C} {C} {E₂ ⊗₀ E₁} {E₁ ⊗₀ E₂} (λ x → x) (app (⊗-symₒ {E₂} {E₁})) o))
    rhs = ∘-collapse r₁ (tfm'-is-Xfwd (⊗-assocᵢ {C} {E₂} {E₁}) (⊗-assocₒ {C} {E₂} {E₁}))

  mid4-decomp : ∀ {P Q R S}
    → mid4 {P} {Q} {R} {S}
      ≅ᴹ (⊗-assoc⃖ {P} {R} {Q ⊗₀ S}
          CC.∘ ((CC.id {P} ⊗₁ (⊗-assoc {R} {Q} {S} CC.∘ ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S})))
                CC.∘ ⊗-assoc {P} {Q} {R ⊗₀ S}))
  mid4-decomp {P} {Q} {R} {S} =
    Xfwd-bridge (tfm'-is-Xfwd (mid4σᵢ {P} {Q} {R} {S}) (mid4σₒ {P} {Q} {R} {S})) rhs
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl
         ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl
         ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
    where
    r₁ : (⊗-symₘ {Q} {R} ⊗₁ CC.id {S})
         ≅ᴹ Xfwd (⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x))
                 (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x))
    r₁ = ⊗-collapse (tfm'-is-Xfwd (⊗-symᵢ {Q} {R}) (⊗-symₒ {Q} {R})) id-is-Xfwd

    r₂ : ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S})
         ≅ᴹ Xfwd (λ a → ⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x)
                               (app (⊗-assoc⃖ᵢ {Q} {R} {S}) a))
                 (λ o → app (⊗-assoc⃖ₒ {Q} {R} {S})
                            (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x) o))
    r₂ = ∘-collapse r₁ (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {Q} {R} {S}) (⊗-assoc⃖ₒ {Q} {R} {S}))

    r₃ : (⊗-assoc {R} {Q} {S} CC.∘ ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S}))
         ≅ᴹ Xfwd (λ a → app (⊗-assocᵢ {R} {Q} {S})
                            (⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x)
                                   (app (⊗-assoc⃖ᵢ {Q} {R} {S}) a)))
                 (λ o → app (⊗-assoc⃖ₒ {Q} {R} {S})
                            (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x)
                                   (app (⊗-assocₒ {R} {Q} {S}) o)))
    r₃ = ∘-collapse (tfm'-is-Xfwd (⊗-assocᵢ {R} {Q} {S}) (⊗-assocₒ {R} {Q} {S})) r₂

    r₄ : (CC.id {P} ⊗₁ (⊗-assoc {R} {Q} {S} CC.∘ ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S})))
         ≅ᴹ Xfwd (⊗mapᵢ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                    (λ a → app (⊗-assocᵢ {R} {Q} {S})
                               (⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x)
                                      (app (⊗-assoc⃖ᵢ {Q} {R} {S}) a))))
                 (⊗mapₒ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                    (λ o → app (⊗-assoc⃖ₒ {Q} {R} {S})
                               (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x)
                                      (app (⊗-assocₒ {R} {Q} {S}) o))))
    r₄ = ⊗-collapse id-is-Xfwd r₃

    r₅ : ((CC.id {P} ⊗₁ (⊗-assoc {R} {Q} {S} CC.∘ ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S})))
          CC.∘ ⊗-assoc {P} {Q} {R ⊗₀ S})
         ≅ᴹ Xfwd (λ a → ⊗mapᵢ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                          (λ a → app (⊗-assocᵢ {R} {Q} {S})
                                     (⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x)
                                            (app (⊗-assoc⃖ᵢ {Q} {R} {S}) a)))
                          (app (⊗-assocᵢ {P} {Q} {R ⊗₀ S}) a))
                 (λ o → app (⊗-assocₒ {P} {Q} {R ⊗₀ S})
                          (⊗mapₒ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                             (λ o → app (⊗-assoc⃖ₒ {Q} {R} {S})
                                        (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x)
                                               (app (⊗-assocₒ {R} {Q} {S}) o)))
                             o))
    r₅ = ∘-collapse r₄ (tfm'-is-Xfwd (⊗-assocᵢ {P} {Q} {R ⊗₀ S}) (⊗-assocₒ {P} {Q} {R ⊗₀ S}))

    rhs : (⊗-assoc⃖ {P} {R} {Q ⊗₀ S}
           CC.∘ ((CC.id {P} ⊗₁ (⊗-assoc {R} {Q} {S} CC.∘ ((⊗-symₘ {Q} {R} ⊗₁ CC.id {S}) CC.∘ ⊗-assoc⃖ {Q} {R} {S})))
                 CC.∘ ⊗-assoc {P} {Q} {R ⊗₀ S}))
          ≅ᴹ Xfwd (λ a → app (⊗-assoc⃖ᵢ {P} {R} {Q ⊗₀ S})
                          (⊗mapᵢ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                             (λ a → app (⊗-assocᵢ {R} {Q} {S})
                                        (⊗mapᵢ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symᵢ {Q} {R})) (λ x → x)
                                               (app (⊗-assoc⃖ᵢ {Q} {R} {S}) a)))
                             (app (⊗-assocᵢ {P} {Q} {R ⊗₀ S}) a)))
                  (λ o → app (⊗-assocₒ {P} {Q} {R ⊗₀ S})
                          (⊗mapₒ {P} {P} {Q ⊗₀ (R ⊗₀ S)} {R ⊗₀ (Q ⊗₀ S)} (λ x → x)
                             (λ o → app (⊗-assoc⃖ₒ {Q} {R} {S})
                                        (⊗mapₒ {Q ⊗₀ R} {R ⊗₀ Q} {S} {S} (app (⊗-symₒ {Q} {R})) (λ x → x)
                                               (app (⊗-assocₒ {R} {Q} {S}) o)))
                             (app (⊗-assoc⃖ₒ {P} {R} {Q ⊗₀ S}) o)))
    rhs = ∘-collapse (tfm'-is-Xfwd (⊗-assoc⃖ᵢ {P} {R} {Q ⊗₀ S}) (⊗-assoc⃖ₒ {P} {R} {Q ⊗₀ S})) r₅

  -- Both halves of `⊗ᴷ-fwd` and of `mid4` are `⇒-solver` at the same type,
  -- and the solver is deterministic, so the two machines coincide.
  ⊗ᴷ-fwd-decomp : ∀ {B₁ E₁ B₂ E₂} → ⊗ᴷ-fwd {B₁} {E₁} {B₂} {E₂} ≅ᴹ mid4 {B₁} {E₁} {B₂} {E₂}
  ⊗ᴷ-fwd-decomp = ≅ᴹ-refl

  absorb-regroup-decomp : ∀ {X Y Z W}
    → absorb-regroup {X} {Y} {Z} {W}
      ≅ᴹ ((CC.id {X} ⊗₁ ⊗-assoc {W} {Z} {Y})
          CC.∘ ((CC.id {X} ⊗₁ ⊗-symₘ {Y} {W ⊗₀ Z}) CC.∘ ⊗-assoc {X} {Y} {W ⊗₀ Z}))
  absorb-regroup-decomp {X} {Y} {Z} {W} =
    Xfwd-bridge (tfm'-is-Xfwd (absorb-regroupσᵢ {X} {Y} {Z} {W}) (absorb-regroupσₒ {X} {Y} {Z} {W})) rhs
      (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl
         ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
      (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl
         ; (inj₂ (inj₂ (inj₁ _))) → refl ; (inj₂ (inj₂ (inj₂ _))) → refl })
    where
    r₁ : (CC.id {X} ⊗₁ ⊗-symₘ {Y} {W ⊗₀ Z})
         ≅ᴹ Xfwd (⊗mapᵢ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symᵢ {Y} {W ⊗₀ Z})))
                 (⊗mapₒ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symₒ {Y} {W ⊗₀ Z})))
    r₁ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-symᵢ {Y} {W ⊗₀ Z}) (⊗-symₒ {Y} {W ⊗₀ Z}))

    r₂ : ((CC.id {X} ⊗₁ ⊗-symₘ {Y} {W ⊗₀ Z}) CC.∘ ⊗-assoc {X} {Y} {W ⊗₀ Z})
         ≅ᴹ Xfwd (λ a → ⊗mapᵢ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symᵢ {Y} {W ⊗₀ Z}))
                               (app (⊗-assocᵢ {X} {Y} {W ⊗₀ Z}) a))
                 (λ o → app (⊗-assocₒ {X} {Y} {W ⊗₀ Z})
                            (⊗mapₒ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symₒ {Y} {W ⊗₀ Z})) o))
    r₂ = ∘-collapse r₁ (tfm'-is-Xfwd (⊗-assocᵢ {X} {Y} {W ⊗₀ Z}) (⊗-assocₒ {X} {Y} {W ⊗₀ Z}))

    r₃ : (CC.id {X} ⊗₁ ⊗-assoc {W} {Z} {Y})
         ≅ᴹ Xfwd (⊗mapᵢ {X} {X} {(W ⊗₀ Z) ⊗₀ Y} {W ⊗₀ (Z ⊗₀ Y)} (λ x → x) (app (⊗-assocᵢ {W} {Z} {Y})))
                 (⊗mapₒ {X} {X} {(W ⊗₀ Z) ⊗₀ Y} {W ⊗₀ (Z ⊗₀ Y)} (λ x → x) (app (⊗-assocₒ {W} {Z} {Y})))
    r₃ = ⊗-collapse id-is-Xfwd (tfm'-is-Xfwd (⊗-assocᵢ {W} {Z} {Y}) (⊗-assocₒ {W} {Z} {Y}))

    rhs : ((CC.id {X} ⊗₁ ⊗-assoc {W} {Z} {Y})
           CC.∘ ((CC.id {X} ⊗₁ ⊗-symₘ {Y} {W ⊗₀ Z}) CC.∘ ⊗-assoc {X} {Y} {W ⊗₀ Z}))
          ≅ᴹ Xfwd (λ a → ⊗mapᵢ {X} {X} {(W ⊗₀ Z) ⊗₀ Y} {W ⊗₀ (Z ⊗₀ Y)} (λ x → x) (app (⊗-assocᵢ {W} {Z} {Y}))
                           (⊗mapᵢ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symᵢ {Y} {W ⊗₀ Z}))
                                  (app (⊗-assocᵢ {X} {Y} {W ⊗₀ Z}) a)))
                  (λ o → app (⊗-assocₒ {X} {Y} {W ⊗₀ Z})
                           (⊗mapₒ {X} {X} {Y ⊗₀ (W ⊗₀ Z)} {(W ⊗₀ Z) ⊗₀ Y} (λ x → x) (app (⊗-symₒ {Y} {W ⊗₀ Z}))
                                  (⊗mapₒ {X} {X} {(W ⊗₀ Z) ⊗₀ Y} {W ⊗₀ (Z ⊗₀ Y)} (λ x → x) (app (⊗-assocₒ {W} {Z} {Y})) o)))
    rhs = ∘-collapse r₃ r₂

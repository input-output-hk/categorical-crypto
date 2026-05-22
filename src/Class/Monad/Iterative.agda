{-# OPTIONS --safe #-}

-- Iterative-monad structure (Bloom-Esik / Hasegawa style).
--
-- An iterative monad is a monad with an `iter` operator
--
--   iter : (X → M (X ⊎ A)) → X → M A
--
-- intuitively running a step function `f` repeatedly: at each step
-- `f x` decides whether to keep looping (`inj₁ x'`) or to terminate
-- with a final result (`inj₂ a`).
--
-- Equipping a Kleisli category with such an operator is exactly what
-- it takes to give it a *traced symmetric monoidal* structure over the
-- coproduct tensor (⊎, ⊥). The axioms below are the ones we need to
-- derive the four traced-monoidal laws (vanishing₁, vanishing₂,
-- superposing, yanking) on `SFunᵉ`.

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext
open import Class.Prelude using (Typeω)

module Class.Monad.Iterative where

-- Continuation used by `iter-fix`'s RHS, given a *named* form so that
-- the equational step doesn't fall foul of Agda's extended-lambda
-- comparison (two syntactically identical λ-where lambdas are *not*
-- definitionally equal).  Parametric in the `iter` operator itself
-- so the record can reference it.
iter-cont : ∀ {M : Type↑} ⦃ _ : Monad M ⦄ {A X : Type}
          → ((X → M (X ⊎ A)) → X → M A)
          → (X → M (X ⊎ A)) → X ⊎ A → M A
iter-cont iter₀ f (inj₁ x') = iter₀ f x'
iter-cont iter₀ f (inj₂ a)  = return a

-- "Strengthen" an iter body with a side state that the body doesn't
-- touch. The body returns its loop value paired with the same side
-- state on both branches.
strengthen : ∀ {M : Type↑} ⦃ _ : Monad M ⦄ {S A X : Type}
           → (X → M (X ⊎ A)) → (S × X) → M ((S × X) ⊎ (S × A))
strengthen f (s , x) = f x >>= λ where (inj₁ x') → return (inj₁ (s , x'))
                                       (inj₂ a)  → return (inj₂ (s , a))

-- Continuation for `iter-conjugate`'s RHS: routes inj₁/inj₂ outputs
-- through the state-morphism `φ` and value-morphism `ψ`. Named so the
-- callers' RHS lambda matches the one in the axiom statement.
iter-conj-step : ∀ {M : Type↑} ⦃ _ : Monad M ⦄ {A B X S₁ S₂ : Type}
                 (φ : S₁ → S₂) (ψ : A → B)
               → (S₁ × X) ⊎ (S₁ × A)
               → M ((S₂ × X) ⊎ (S₂ × B))
iter-conj-step φ ψ (inj₁ (s₁' , x')) = return (inj₁ (φ s₁' , x'))
iter-conj-step φ ψ (inj₂ (s₁' , a))  = return (inj₂ (φ s₁' , ψ a))

-- "Combine" two iter bodies into one whose loop variable is a sum of
-- the two. Both bodies may either loop on their own variable, emit a
-- final A, or switch to the other variable's iter — i.e., this is the
-- *full* Bekič / codiagonal shape rather than the asymmetric form
-- where only fx can switch sides.
combine : ∀ {M : Type↑} ⦃ _ : Monad M ⦄ {S A X Y : Type}
        → ((S × X) → M ((S × X) ⊎ (S × (A ⊎ Y))))
        → ((S × Y) → M ((S × Y) ⊎ (S × (A ⊎ X))))
        → (S × (X ⊎ Y)) → M ((S × (X ⊎ Y)) ⊎ (S × A))
combine fx fy (s , inj₁ x) = fx (s , x) >>= λ where
  (inj₁ (s' , x')) → return (inj₁ (s' , inj₁ x'))
  (inj₂ (s' , inj₁ a)) → return (inj₂ (s' , a))
  (inj₂ (s' , inj₂ y)) → return (inj₁ (s' , inj₂ y))
combine fx fy (s , inj₂ y) = fy (s , y) >>= λ where
  (inj₁ (s' , y')) → return (inj₁ (s' , inj₂ y'))
  (inj₂ (s' , inj₁ a)) → return (inj₂ (s' , a))
  (inj₂ (s' , inj₂ x)) → return (inj₁ (s' , inj₁ x))

-- Named dispatch helper for `iter-vanishing-2`: routes the fy-iter's
-- terminator output. A-output terminates; X-output continues into the
-- flat combine iter at inj₁ x. Named so equational reasoning at the
-- call site can match it definitionally. Parametric in the `iter`
-- operator so it can be defined before the IterativeMonad record.
vanishing-2-dispatch : ∀ {M : Type↑} ⦃ _ : Monad M ⦄ {S A X Y : Type}
  (iter₀ : ∀ {A X : Type} → (X → M (X ⊎ A)) → X → M A)
  (fx : (S × X) → M ((S × X) ⊎ (S × (A ⊎ Y))))
  (fy : (S × Y) → M ((S × Y) ⊎ (S × (A ⊎ X))))
  → (S × (A ⊎ X)) → M (S × A)
vanishing-2-dispatch iter₀ fx fy (s' , inj₁ a) = return (s' , a)
vanishing-2-dispatch iter₀ fx fy (s' , inj₂ x) = iter₀ (combine fx fy) (s' , inj₁ x)

record IterativeMonad (M : Type↑)
  ⦃ Monad-M : Monad M     ⦄
  ⦃ M-Laws  : MonadLaws M ⦄
  : Typeω where

  field
    -- The iteration operator.
    iter : ∀ {A X : Type} → (X → M (X ⊎ A)) → X → M A

    -- Fixpoint / unfolding: one step of iteration.
    iter-fix : ∀ {A X : Type} {f : X → M (X ⊎ A)} (x : X)
             → iter f x ≡ (f x >>= iter-cont iter f)

    -- iter respects pointwise equality of its functional argument.
    iter-cong : ∀ {A X : Type} {f g : X → M (X ⊎ A)}
              → (∀ x → f x ≡ g x) → ∀ x → iter f x ≡ iter g x

    -- Naturality (post-composition / "right-shift"): post-composing
    -- `iter f`'s result with `h : A → M B` is the same as iterating
    -- `f` with each `inj₂ a` output replaced by `h a >>= return ∘ inj₂`.
    iter-nat : ∀ {A B X : Type} (f : X → M (X ⊎ A)) (h : A → M B) (x : X)
             → (iter f x >>= h)
             ≡ iter (λ x' → f x' >>= λ where
                                       (inj₁ x'') → return (inj₁ x'')
                                       (inj₂ a)   → h a >>= λ b → return (inj₂ b)) x

    -- Parameter axiom (Bloom-Esik): iter preserves a side state that
    -- the body doesn't touch.  `strengthen f` extends `f` with a side
    -- state that travels along unchanged.
    iter-strengthen : ∀ {A X S : Type} (s : S) (f : X → M (X ⊎ A)) (x : X)
                    → iter (strengthen f) (s , x)
                    ≡ (iter f x >>= λ a → return (s , a))

    -- Codiagonal / "Bekič" (in a state-aware form): a single iteration
    -- over a sum loop X ⊎ Y is the same as nested iteration — outer
    -- loop on X with the body invoking an inner iter on Y when an
    -- inj₂ y arises. The inner Y-iter, when it terminates, may either
    -- emit a final A (outer iter is done) or switch back to X
    -- (outer iter continues at the new X-value). This is the full
    -- Bekič identity, needed for proving vanishing₂.
    iter-codiag : ∀ {A X Y S : Type}
      (fx : (S × X) → M ((S × X) ⊎ (S × (A ⊎ Y))))
      (fy : (S × Y) → M ((S × Y) ⊎ (S × (A ⊎ X))))
      (s : S) (x : X)
      → iter (combine fx fy) (s , inj₁ x)
      ≡ iter (λ (s' , x') → fx (s' , x') >>= λ where
                                              (inj₁ (s'' , x'')) → return (inj₁ (s'' , x''))
                                              (inj₂ (s'' , inj₁ a)) → return (inj₂ (s'' , a))
                                              (inj₂ (s'' , inj₂ y)) →
                                                iter fy (s'' , y) >>= λ where
                                                  (s''' , inj₁ a)  → return (inj₂ (s''' , a))
                                                  (s''' , inj₂ x'') → return (inj₁ (s''' , x''))) (s , x)

    -- Codiagonal Y-direction: symmetric counterpart of `iter-codiag`,
    -- starting from `inj₂ y` instead of `inj₁ x`. Loops fy as outer,
    -- with fx as inner when fy's terminator outputs an X-value. fx's
    -- inner iter can either produce final A or switch back to the
    -- outer Y-loop.
    iter-codiag-y : ∀ {A X Y S : Type}
      (fx : (S × X) → M ((S × X) ⊎ (S × (A ⊎ Y))))
      (fy : (S × Y) → M ((S × Y) ⊎ (S × (A ⊎ X))))
      (s : S) (y : Y)
      → iter (combine fx fy) (s , inj₂ y)
      ≡ iter (λ (s' , y') → fy (s' , y') >>= λ where
                                              (inj₁ (s'' , y'')) → return (inj₁ (s'' , y''))
                                              (inj₂ (s'' , inj₁ a)) → return (inj₂ (s'' , a))
                                              (inj₂ (s'' , inj₂ x)) →
                                                iter fx (s'' , x) >>= λ where
                                                  (s''' , inj₁ a)   → return (inj₂ (s''' , a))
                                                  (s''' , inj₂ y'') → return (inj₁ (s''' , y''))) (s , y)

    -- "iter-vanishing-2": the Bloom-Esik / Hasegawa vanishing axiom
    -- for nested iter, Y-direction. Doing a Y-iter on fy, then on
    -- X-output continuing as the flat combine-iter at inj₁ x, equals
    -- doing the flat combine-iter at inj₂ y directly.
    --
    -- This expresses the fixpoint-uniqueness property at iter level
    -- that iter-codiag-y alone does not entail: that the same iter
    -- on combine is reached whether we "start by looping Y" (LHS) or
    -- "start by routing directly into combine" (RHS).
    iter-vanishing-2 : ∀ {A X Y S : Type}
      (fx : (S × X) → M ((S × X) ⊎ (S × (A ⊎ Y))))
      (fy : (S × Y) → M ((S × Y) ⊎ (S × (A ⊎ X))))
      (s : S) (y : Y)
      → (iter fy (s , y) >>= vanishing-2-dispatch iter fx fy)
        ≡ iter (combine fx fy) (s , inj₂ y)

    -- "Uniformity" / "conjugation": if body `g` on `(φ s, x)` is f's
    -- behaviour on `(s, x)` with states pushed through `φ : S₁ → S₂`
    -- and values pushed through `ψ : A → B`, then `iter g (φ s, x)`
    -- factors through `iter f (s, x)` by the same maps.
    --
    -- This is Bloom-Esik / Hasegawa uniformity, specialised to
    -- state-and-value-only morphisms (the loop variable type X stays
    -- the same). Uses the named `iter-conj-cont` continuation so the
    -- premise's lambda matches the inline one used by callers.
    iter-conjugate : ∀ {A B X S₁ S₂ : Type}
      (φ : S₁ → S₂)
      (ψ : A → B)
      (f : (S₁ × X) → M ((S₁ × X) ⊎ (S₁ × A)))
      (g : (S₂ × X) → M ((S₂ × X) ⊎ (S₂ × B)))
      → (∀ s₁ x → g (φ s₁ , x) ≡ (f (s₁ , x) >>= iter-conj-step φ ψ))
      → ∀ s₁ x → iter g (φ s₁ , x)
               ≡ (iter f (s₁ , x) >>= λ (s₁' , a) → return (φ s₁' , ψ a))

open IterativeMonad ⦃...⦄ public

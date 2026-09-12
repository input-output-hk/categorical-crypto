{-# OPTIONS --safe --without-K #-}

-- The setup's environment presheaf, read as an action on graded morphisms:
--
--     Env D        = the carrier of ℰ D        prefix W f = μ W X ∘ T₁ W f
--     pull h e     = ℰ h e                     run W f e  = pull (prefix W f) e
--     regradeEnv W s e = pull (sub (id ⊗ s)) e
--
-- `prefix W f` is the very context `_≈ᵁ_` quantifies over, so `run` is that
-- relation's element-level reading and `run-resp-≈ᵁ`/`runs⇒≈ᵁ` are its two
-- directions: the U-kernel is retained here, not weakened to the bare kernel
-- `_≈ℰ_`.  Absorbing a simulator is the presheaf's action on `sub` rather than
-- a separate operation, which is all `run-sub` says — `sub-decomp` pulled back.
--
-- The direction is contravariant: `s : Y ⇒ X` turns a grade-`Y` resource into a
-- grade-`X` one while pulling a grade-`X` environment back to grade `Y`.
--
-- Nothing here uses a verdict object, a closed run, `GradeStable`, or an
-- invertible `μ`, and grades (`ℐ.Obj`) stay a parameter distinct from objects
-- (`𝒞.Obj`).  `docs/presheaf-action.md` is the design note.

open import Categories.Functor using (Functor)

open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.UCSetup using (UCSetup)

module CategoricalCrypto.Abstract2.Action
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import CategoricalCrypto.Abstract2

open AbstractUC setup public

private module E = Functor ℰ

private variable
  A B D D′ D″ : 𝒞.Obj
  W X Y : ℐ.Obj

------------------------------------------------------------------------
-- Environments

Env : 𝒞.Obj → Set cs
Env D = Setoid.Carrier (E.F₀ D)

infix 4 _≈Env_

_≈Env_ : Env D → Env D → Set ℓs
_≈Env_ {D} = Setoid._≈_ (E.F₀ D)

≈Env-refl : {u : Env D} → u ≈Env u
≈Env-refl {D} = Setoid.refl (E.F₀ D)

≈Env-sym : {u v : Env D} → u ≈Env v → v ≈Env u
≈Env-sym {D} = Setoid.sym (E.F₀ D)

≈Env-trans : {u v w : Env D} → u ≈Env v → v ≈Env w → u ≈Env w
≈Env-trans {D} = Setoid.trans (E.F₀ D)

-- The presheaf's three laws, at elements.
pull : D 𝒞.⇒ D′ → Env D′ → Env D
pull h e = E.F₁ h ⟨$⟩ e

pull-cong : (h : D 𝒞.⇒ D′) {u v : Env D′} → u ≈Env v → pull h u ≈Env pull h v
pull-cong h = Func.cong (E.F₁ h)

pull-resp-≈ : {h k : D 𝒞.⇒ D′} → h 𝒞.≈ k → (e : Env D′) → pull h e ≈Env pull k e
pull-resp-≈ eq _ = E.F-resp-≈ eq

pull-∘ : (v : D′ 𝒞.⇒ D″) (u : D 𝒞.⇒ D′) (e : Env D″)
       → pull (v 𝒞.∘ u) e ≈Env pull u (pull v e)
pull-∘ _ _ _ = E.homomorphism

------------------------------------------------------------------------
-- The action on graded morphisms

prefix : (W : ℐ.Obj) → A 𝒞.⇒ T₀ X B → T₀ W A 𝒞.⇒ T₀ (W ⊗₀ X) B
prefix {X = X} W f = μ W X 𝒞.∘ T₁ W f

run : (W : ℐ.Obj) (f : A 𝒞.⇒ T₀ X B) → Env (T₀ (W ⊗₀ X) B) → Env (T₀ W A)
run W f e = pull (prefix W f) e

regradeEnv : (W : ℐ.Obj) (s : Y ℐ.⇒ X) → Env (T₀ (W ⊗₀ X) B) → Env (T₀ (W ⊗₀ Y) B)
regradeEnv W s e = pull (sub (ℐ.id ⊗₁ s)) e

run-sub : (W : ℐ.Obj) (s : Y ℐ.⇒ X) (g : A 𝒞.⇒ T₀ Y B) (e : Env (T₀ (W ⊗₀ X) B))
        → run W (sub s 𝒞.∘ g) e ≈Env run W g (regradeEnv W s e)
run-sub W s g e = ≈Env-trans (pull-resp-≈ (sub-decomp s g W) e)
                             (pull-∘ (sub (ℐ.id ⊗₁ s)) (prefix W g) e)

------------------------------------------------------------------------
-- …is the U-kernel, element by element

run-resp-≈ᵁ : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g
            → (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → run W f e ≈Env run W g e
run-resp-≈ᵁ u W _ = KE.run∼ (u W)

runs⇒≈ᵁ : {f g : A 𝒞.⇒ T₀ X B}
        → ((W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → run W f e ≈Env run W g e)
        → f ≈ᵁ g
runs⇒≈ᵁ h W = KE.mk∼ λ {e} → h W e

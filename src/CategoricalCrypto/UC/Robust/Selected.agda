{-# OPTIONS --safe --without-K #-}

-- A selected environment class with a real closure proof, so that the
-- `ClosedUnder` premise of `UC.Robust` is exercised at something other than
-- `⊤ᴬ`.
--
-- `Factors V` is the class of environments that reach the resource port only
-- through a designated interface `V`: pulled back along SOME grade morphism
-- into `V` from a grade-`V` environment.  Closure is then the presheaf's
-- functoriality — the simulator composes into the attacker — and the class is
-- a genuine subset: an environment whose grade admits no morphism into `V` is
-- not in it.
--
-- It is nonetheless closed under EVERY simulator, and that is not an accident:
-- `ClosedUnder Adm s` IS closure of the attacker collection under
-- precomposition by `s`, so any class cut out by a precomposition-closed
-- condition is closed at every `s`.  A class that separates the two — a fixed
-- query budget, which a simulator's own queries can exhaust — needs the
-- quantitative enrichment (`docs/uc-presheaf-preservation-plan.md` §2.2, §4),
-- not another qualitative condition.

import Categories.Category.Monoidal.Reasoning as MonR

open import Data.Product.Base using (Σ-syntax; _,_)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UCSetup using (UCSetup)

module CategoricalCrypto.UC.Robust.Selected
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import CategoricalCrypto.UC.Robust setup public

private module MI = MonR ℐ.monoidal

private variable
  A B : 𝒞.Obj
  V W X Y : ℐ.Obj
  p : Level

Factors : (V : ℐ.Obj) → Admissible B (ℓ ⊔ cs ⊔ ℓs)
Factors {B = B} V W X e =
  Σ[ a ∈ X ℐ.⇒ V ] Σ[ d ∈ Env (T₀ (W ⊗₀ V) B) ] e ≈Env regradeEnv W a d

regrade-∘ : (W : ℐ.Obj) (a : X ℐ.⇒ V) (s : Y ℐ.⇒ X) (d : Env (T₀ (W ⊗₀ V) B))
          → regradeEnv W s (regradeEnv W a d) ≈Env regradeEnv W (a ℐ.∘ s) d
regrade-∘ W a s d =
  ≈Env-trans (≈Env-sym (pull-∘ (sub (ℐ.id ⊗₁ a)) (sub (ℐ.id ⊗₁ s)) d))
             (pull-resp-≈ merge d)
  where merge : sub (ℐ.id ⊗₁ a) 𝒞.∘ sub (ℐ.id ⊗₁ s) 𝒞.≈ sub (ℐ.id ⊗₁ (a ℐ.∘ s))
        merge = let open 𝒞 in ⟺ sub-homomorphism ○ sub-resp-≈ MI.merge₂ʳ

factors-resp : (V : ℐ.Obj) → Respects≈Env (Factors {B} V)
factors-resp _ eq (a , d , p) = a , d , ≈Env-trans (≈Env-sym eq) p

factors-closed : (V : ℐ.Obj) (s : Y ℐ.⇒ X) → ClosedUnder (Factors {B} V) s
factors-closed _ s W e (a , d , p) =
  a ℐ.∘ s , d , ≈Env-trans (pull-cong (sub (ℐ.id ⊗₁ s)) p) (regrade-∘ W a s d)

uc-preserves-factors : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (V : ℐ.Obj)
                       {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} (s : Y ℐ.⇒ X)
                     → f ≈ᵁ sub s 𝒞.∘ g
                     → Robust P (Factors V) g → Robust P (Factors V) f
uc-preserves-factors P V s u = uc-preserves-at P (Factors V) s u (factors-closed V s)

{-# OPTIONS --safe --without-K #-}

-- Qualitative UC preservation over an arbitrary `UCSetup`: what an emulation
-- carries when nothing numerical is in play.
--
-- A property of a run is `SaturatedProperty`, a predicate on a fiber of the
-- environment presheaf that `_≈Env_` may not refute; `Robust P Adm f` says the
-- property holds of `run W f e` at every admissible environment.  Preservation
-- is then saturation plus `Abstract2.Action.run-sub`: absorbing the simulator
-- is the presheaf's own action, so a `Adm`-environment of the real system is an
-- `Adm`-environment of the ideal one with the simulator in front — provided
-- `Adm` is closed under that action, which is `ClosedUnder` and a PREMISE.
--
-- `P W` deliberately does not see the resource grade, which the simulator
-- moves; a grade-dependent property would need a transport premise, and
-- hiding it in the definition is what this shape avoids.  `⊤ᴬ` recovers
-- unrestricted robustness — at the cost of saying nothing about which
-- environments a bound was ever claimed for.
--
-- SCOPE.  No numerical bound, no query count, and nothing about a simulator
-- being silent or total (`docs/uc-presheaf-preservation-plan.md` §2.3): those
-- are enrichment obligations this statement makes visible.  The independently
-- scoped `UCBase` theorem is `UC.Robust.Observation`.

open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤)

open import Level using (Level; 0ℓ; _⊔_; suc)

open import CategoricalCrypto.UCSetup using (UCSetup)

module CategoricalCrypto.UC.Robust
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import CategoricalCrypto.Abstract2.Action setup public

private variable
  A B : 𝒞.Obj
  W X X′ Y : ℐ.Obj
  d p : Level

------------------------------------------------------------------------
-- Saturated properties and admissible environments

-- What the setup's environment equality cannot see.  `saturated` is exactly
-- `_≈Env_`-invariance, which is what makes the carry below premise-free in the
-- property and lets the whole cost sit in `ClosedUnder`.
record SaturatedProperty (p : Level) (D : 𝒞.Obj) : Set (cs ⊔ ℓs ⊔ suc p) where
  field
    holds     : Env D → Set p
    saturated : {u v : Env D} → u ≈Env v → holds u → holds v

open SaturatedProperty public

-- A class of environments, at each ancilla and resource grade.
Admissible : (B : 𝒞.Obj) (d : Level) → Set (o ⊔ cs ⊔ suc d)
Admissible B d = (W X : ℐ.Obj) → Env (T₀ (W ⊗₀ X) B) → Set d

⊤ᴬ : Admissible B 0ℓ
⊤ᴬ _ _ _ = ⊤

-- Representation independence, stated apart from `ClosedUnder`: the carry
-- itself uses the exact pulled-back element and never needs this.
Respects≈Env : Admissible B d → Set (o ⊔ cs ⊔ ℓs ⊔ d)
Respects≈Env {B = B} Adm = {W X : ℐ.Obj} {u v : Env (T₀ (W ⊗₀ X) B)}
                         → u ≈Env v → Adm W X u → Adm W X v

-- The simulator slide as an obligation on the class, not a new action.
ClosedUnder : Admissible B d → Y ℐ.⇒ X → Set (o ⊔ cs ⊔ d)
ClosedUnder {B = B} {Y = Y} {X = X} Adm s =
  (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → Adm W X e → Adm W Y (regradeEnv W s e)

------------------------------------------------------------------------
-- Robustness

-- Both arguments stay EXPLICIT: `Robust P Adm f` reduces to a Π type whose
-- body applies `holds (P W)`, which no use site can invert.
Robust : ((W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) → Admissible B d
       → A 𝒞.⇒ T₀ X B → Set (o ⊔ cs ⊔ d ⊔ p)
Robust {B = B} {X = X} P Adm f =
  (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → Adm W X e → holds (P W) (run W f e)

-- Invariance read at the environments rather than at the runs: `_≈ᵁ_` IS
-- agreement of every run (`Action.run-resp-≈ᵁ`), and that is all a saturated
-- property needs.
robust-resp-≈ᵁ : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (Adm : Admissible B d)
                 {f g : A 𝒞.⇒ T₀ X B}
               → f ≈ᵁ g → Robust P Adm g → Robust P Adm f
robust-resp-≈ᵁ P Adm u rob W e adm =
  saturated (P W) (≈Env-sym (run-resp-≈ᵁ u W e)) (rob W e adm)

robust-sub : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (Adm : Admissible B d)
             {g : A 𝒞.⇒ T₀ Y B} (s : Y ℐ.⇒ X)
           → ClosedUnder Adm s → Robust P Adm g → Robust P Adm (sub s 𝒞.∘ g)
robust-sub P Adm {g} s cl rob W e adm =
  saturated (P W) (≈Env-sym (run-sub W s g e)) (rob W (regradeEnv W s e) (cl W e adm))

------------------------------------------------------------------------
-- Preservation

-- At an explicit simulator, because a class that is not closed under arbitrary
-- simulators — a fixed-budget one, say — must not obtain closure merely from
-- `f ≤UC g`.  `Abstract2.≤UC⇒dummy` is what turns the order into this pair.
uc-preserves-at : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (Adm : Admissible B d)
                  {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} (s : Y ℐ.⇒ X)
                → f ≈ᵁ sub s 𝒞.∘ g → ClosedUnder Adm s
                → Robust P Adm g → Robust P Adm f
uc-preserves-at P Adm s u cl rob = robust-resp-≈ᵁ P Adm u (robust-sub P Adm s cl rob)

uc-preserves : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (Adm : Admissible B d)
               {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
             → ((s : Y ℐ.⇒ X) → ClosedUnder Adm s)
             → f ≤UC g → Robust P Adm g → Robust P Adm f
uc-preserves P Adm cl le =
  let s , u = ≤UC⇒dummy le in uc-preserves-at P Adm s u (cl s)

-- The adversary-attached form, at `_≤UC_`'s own quantifier order: the order
-- supplies a simulator per adversary, so the conclusion is about the real
-- system with that adversary attached.
uc⁺-preserves : (P : (W : ℐ.Obj) → SaturatedProperty p (T₀ W A)) (Adm : Admissible B d)
                {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} (a : X ℐ.⇒ X′)
              → ((s : Y ℐ.⇒ X′) → ClosedUnder Adm s)
              → f ≤UC g → Robust P Adm g → Robust P Adm (sub a 𝒞.∘ f)
uc⁺-preserves P Adm a cl le =
  let s , u = le a in uc-preserves-at P Adm s u (cl s)

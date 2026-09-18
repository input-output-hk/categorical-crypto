{-# OPTIONS --safe --without-K #-}

-- The quantitative UC setup and its contextual comparison
-- (`docs/quantitative-uc-setup-plan.typ` §§1, 4, 5.1).
--
-- Only the environment presheaf moves, from `Setoids` to `Approx`; forgetting
-- it along `F₀` or `F₊` gives an ordinary `UCSetup`, so the whole qualitative
-- metatheory is INHERITED rather than restated.
--
-- `underlying₀` is also the working tool, not just an instance: its
-- environment equality IS closeness at zero error, so every presheaf law
-- `Abstract2.Action` proves arrives here as an exact quantitative step, and
-- `≈-resp₀` is what splices such a step into a bound at any ε.  That is the
-- whole reason the congruences below preserve their error unchanged; it is a
-- statement about nonexpansive maps and must not be read as a claim about the
-- query-aware theorems, whose errors do change under composition.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Monad.Graded using (GradedKleisliTriple)

open import Level using (Level; suc; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Abstract2.Action as Action

module CategoricalCrypto.UC.Quantitative {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Small E
open import CategoricalCrypto.Approx.Space E

record QUCSetup (o ℓ e o′ ℓ′ e′ c ℓb : Level)
              : Set (suc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)) where
  field
    𝒞 : Category o′ ℓ′ e′
    ℐ : MonoidalCategory o ℓ e
    ℳ : GradedKleisliTriple ℐ 𝒞
    Q : Presheaf 𝒞 (Approx c (es ⊔ ℓe ⊔ ℓb))

module QuantitativeUC {o ℓ e o′ ℓ′ e′ c ℓb : Level}
                      (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb) where

  private module S = QUCSetup S

  open import CategoricalCrypto.Approx.Forget E c ℓb

  underlying₀ underlying₊ : UCSetup o ℓ e o′ ℓ′ e′ c (es ⊔ ℓe ⊔ ℓb)
  underlying₀ = record { 𝒞 = S.𝒞 ; ℐ = S.ℐ ; ℳ = S.ℳ ; ℰ = F₀ ∘F S.Q }
  underlying₊ = record { 𝒞 = S.𝒞 ; ℐ = S.ℐ ; ℳ = S.ℳ ; ℰ = F₊ ∘F S.Q }

  -- The third way to forget (`Approx.Small`), which the all-positive one is
  -- NOT an instance of: here the error is merely EXISTENTIAL, so what the
  -- environment equality of this setup says depends on where the quantifier
  -- sits relative to the contexts (`UC.Quantitative.Bridge.Small`).
  underlyingSmall : {ℓs : Level} → SmallClass ℓs
                  → UCSetup o ℓ e o′ ℓ′ e′ c (es ⊔ ℓe ⊔ ℓs ⊔ ℓb)
  underlyingSmall Sm = record
    { 𝒞 = S.𝒞 ; ℐ = S.ℐ ; ℳ = S.ℳ
    ; ℰ = Collapse.FSmall Sm c (es ⊔ ℓe ⊔ ℓb) ∘F S.Q }

  open Action underlying₀ public
  module A₊ = Action underlying₊

  private
    module Q = Functor S.Q
    module QS (D : 𝒞.Obj) = ApproxSpace (Q.F₀ D)

  private variable
    A B C′ D D′ : 𝒞.Obj
    X Y P : ℐ.Obj
    ε δ : Error

  ------------------------------------------------------------------------
  -- Closeness of environments, and the splice

  infix 4 _≈[_]_

  _≈[_]_ : {D : 𝒞.Obj} → Env D → Error → Env D → Set (es ⊔ ℓe ⊔ ℓb)
  _≈[_]_ {D} x ε y = QS._≈[_]_ D x ε y

  ≈-refl : {x : Env D} → x ≈[ ε₀ ] x
  ≈-refl {D} = QS.≈[]-refl D

  ≈-sym : {x y : Env D} → x ≈[ ε ] y → y ≈[ ε ] x
  ≈-sym {D} = QS.≈[]-sym D

  ≈-trans : {x y z : Env D} → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ⊕ δ ] z
  ≈-trans {D} = QS.≈[]-trans D

  ≈-mono : {x y : Env D} → ε ⊑ δ → x ≈[ ε ] y → x ≈[ δ ] y
  ≈-mono {D} = QS.≈[]-mono D

  ≈-resp₀ : {x x′ y y′ : Env D}
          → x′ ≈[ ε₀ ] x → y ≈[ ε₀ ] y′ → x ≈[ ε ] y → x′ ≈[ ε ] y′
  ≈-resp₀ {D} = resp₀ (Q.F₀ D)

  ------------------------------------------------------------------------
  -- Quantitative contextual agreement

  infix 4 _≈ᵁ[_]_

  _≈ᵁ[_]_ : (f : A 𝒞.⇒ T₀ X B) → Error → (g : A 𝒞.⇒ T₀ X B)
          → Set (o ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  _≈ᵁ[_]_ {X = X} {B = B} f ε g =
    (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B)) → run W f e ≈[ ε ] run W g e

  ctx-refl : {f : A 𝒞.⇒ T₀ X B} → f ≈ᵁ[ ε₀ ] f
  ctx-refl _ _ = ≈-refl

  ctx-sym : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ[ ε ] g → g ≈ᵁ[ ε ] f
  ctx-sym h W e = ≈-sym (h W e)

  ctx-trans : {f g h : A 𝒞.⇒ T₀ X B} → f ≈ᵁ[ ε ] g → g ≈ᵁ[ δ ] h → f ≈ᵁ[ ε ⊕ δ ] h
  ctx-trans h k W e = ≈-trans (h W e) (k W e)

  ctx-mono : {f g : A 𝒞.⇒ T₀ X B} → ε ⊑ δ → f ≈ᵁ[ ε ] g → f ≈ᵁ[ δ ] g
  ctx-mono le h W e = ≈-mono le (h W e)

  -- Pullback along a prefix is nonexpansive, so an ambient hom equality of
  -- either side is spent at zero error.
  run-resp-≈ : {f f′ : A 𝒞.⇒ T₀ X B} → f 𝒞.≈ f′ → (W : ℐ.Obj)
             → (e : Env (T₀ (W ⊗₀ X) B)) → run W f e ≈[ ε₀ ] run W f′ e
  run-resp-≈ eq W = pull-resp-≈ (𝒞.∘-resp-≈ʳ (T-resp-≈ eq))

  ctx-resp : {f f′ g g′ : A 𝒞.⇒ T₀ X B}
           → f 𝒞.≈ f′ → g 𝒞.≈ g′ → f ≈ᵁ[ ε ] g → f′ ≈ᵁ[ ε ] g′
  ctx-resp ef eg h W e =
    ≈-resp₀ (run-resp-≈ (𝒞.Equiv.sym ef) W e) (run-resp-≈ eg W e) (h W e)

  ≈C⇒ctx : {f g : A 𝒞.⇒ T₀ X B} → f 𝒞.≈ g → f ≈ᵁ[ ε₀ ] g
  ≈C⇒ctx eq W e = run-resp-≈ eq W e

  ------------------------------------------------------------------------
  -- Absorption and the two congruences of graded composition

  pull-mono : (u : D 𝒞.⇒ D′) {x y : Env D′} → x ≈[ ε ] y → pull u x ≈[ ε ] pull u y
  pull-mono u = Nonexpansive.preserves (Q.F₁ u)

  -- Absorbing a simulator is the presheaf's action on `sub` (`run-sub`), so it
  -- costs nothing: the bound crosses unchanged.
  ctx-sub : (s : Y ℐ.⇒ X) {f g : A 𝒞.⇒ T₀ Y B}
          → f ≈ᵁ[ ε ] g → (sub s 𝒞.∘ f) ≈ᵁ[ ε ] (sub s 𝒞.∘ g)
  ctx-sub s {f} {g} h W e =
    ≈-resp₀ (run-sub W s f e) (≈-sym (run-sub W s g e)) (h W (regradeEnv W s e))

  -- `∙-decomp` at elements: a prefix of a composite reads the second leg off an
  -- environment the first leg has already been absorbed into.
  extEnv : (W : ℐ.Obj) {X : ℐ.Obj} (h : B 𝒞.⇒ T₀ P C′)
         → Env (T₀ (W ⊗₀ (X ⊗₀ P)) C′) → Env (T₀ (W ⊗₀ X) B)
  extEnv W {X} h = pull (sub α⇒ 𝒞.∘ ext (W ⊗₀ X) h)

  run-ext : (W : ℐ.Obj) (h : B 𝒞.⇒ T₀ P C′) (f : A 𝒞.⇒ T₀ X B)
            (e : Env (T₀ (W ⊗₀ (X ⊗₀ P)) C′))
          → run W (h ∙ f) e ≈[ ε₀ ] run W f (extEnv W h e)
  run-ext W h f e =
    ≈Env-trans (pull-resp-≈ (∙-decomp h f W) e) (pull-∘ _ (prefix W f) e)

  ctx-ext : (h : B 𝒞.⇒ T₀ P C′) {f g : A 𝒞.⇒ T₀ X B}
          → f ≈ᵁ[ ε ] g → (h ∙ f) ≈ᵁ[ ε ] (h ∙ g)
  ctx-ext h {f} {g} k W e =
    ≈-resp₀ (run-ext W h f e) (≈-sym (run-ext W h g e)) (k W (extEnv W h e))

  -- …and in the other argument the absorbed environment is what varies, which
  -- `μT` turns back into a prefix so the hypothesis applies at grade `W ⊗ X`.
  ext-env : (W X : ℐ.Obj) (h : B 𝒞.⇒ T₀ P C′) (e : Env (T₀ (W ⊗₀ (X ⊗₀ P)) C′))
          → extEnv W {X} h e ≈[ ε₀ ] run (W ⊗₀ X) h (pull (sub α⇒) e)
  ext-env W X h e = ≈Env-trans (pull-∘ (sub α⇒) (ext (W ⊗₀ X) h) e)
                               (pull-resp-≈ (𝒞.Equiv.sym (μT h)) _)

  ctx-pre : {h k : B 𝒞.⇒ T₀ P C′} (f : A 𝒞.⇒ T₀ X B)
          → h ≈ᵁ[ ε ] k → (h ∙ f) ≈ᵁ[ ε ] (k ∙ f)
  ctx-pre {P = P} {C′ = C′} {X = X} {h = h} {k = k} f hyp W e =
    ≈-resp₀ (run-ext W h f e) (≈-sym (run-ext W k f e))
      (pull-mono (prefix W f)
        (≈-resp₀ (ext-env W X h e) (≈-sym (ext-env W X k e))
                 (hyp (W ⊗₀ X) (pull (sub α⇒) e))))

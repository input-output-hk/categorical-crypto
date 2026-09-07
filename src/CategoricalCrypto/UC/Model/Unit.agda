{-# OPTIONS --safe --without-K --guardedness #-}

-- The model's two empty objects, and why the choice between them is immaterial.
--
-- `UC.Model.Observation` takes its closures at `𝟘ᵒ = ifaceᵒ unitᴵ` rather than
-- at `𝔾ᵒ`'s monoidal unit `𝟘ᵘ` — the two are the empty interface spelled with
-- two different empty types — and leaves them unidentified.  This module says
-- what that costs, which is nothing, in two halves.
--
--   `AnyEnvironment`  the metatheory is BLIND to the closure object.  `StdUC`
--                     consumes `ℰ` abstractly, so its whole output is available
--                     at an arbitrary environment presheaf over `𝔾ᵒ`; the
--                     closures that `ℰᵒ` happens to quantify over never enter a
--                     statement.  `𝟘ᵘ` does enter, but only as a GRADE — it is
--                     `ℐ.unit`, where `≈ᵁ⇒≈ℰ` spends `λ⇒`/`λ⇐`/`return` — and
--                     the grade position never meets the closure position.
--   `Interconvert`    what an iso `𝟘ᵒ ≅ 𝟘ᵘ` would buy, proved over an abstract
--                     one: the two closure families interconvert and `ℰᵒ`'s
--                     test agreement is the SAME relation either way (`≋⇔≋ᵘ`).
--
-- So no iso is needed anywhere, and it is `Interconvert` that measures the gap:
-- its hypothesis is the only thing the identification adds, and nothing in the
-- cone asks for it.  The iso is nonetheless constructible — from the base's
-- initiality through `pureᴹ` and `GConstructionEmbedding.⌜⌝-≅`, which absorbs
-- the ⊕-trace generically — but not affordably: measured at >150 s and 6.7 GiB
-- resident, over this branch's bar.  `docs/stduc-supersession-plan.md` §1.1
-- carries the construction and the diagnosis.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ-syntax)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ; suc)

open import ProbabilisticLogic.Dp using (Dₚ)

open import CategoricalCrypto.Standard2 using (module StdUC)
open import CategoricalCrypto.UC.Model.Environment using (_≋_)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣; 𝔾ᵒ)

module CategoricalCrypto.UC.Model.Unit where

private module G = MonoidalCategory 𝔾ᵒ

-- The grade unit.  `Abstract2` calls it `ℐ.unit`; it is `𝔾ᵒ`'s empty object,
-- and it is not `𝟘ᵒ`.
𝟘ᵘ : G.Obj
𝟘ᵘ = G.unit

------------------------------------------------------------------------
-- The metatheory does not see the closures

module AnyEnvironment (ℰ : Presheaf ∣𝔾ᵒ∣ (Setoids (suc 0ℓ) (suc 0ℓ))) where

  open StdUC 𝔾ᵒ ℰ

  private variable A B C X Y P Q : Channel

  refl-at : (f : A ⇒ T₀ X B) → f ≤UC f
  refl-at = ≤UC-refl

  dummy-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
           → Σ[ s₀ ∈ Y ⇒ X ] f ≈ᵁ sub s₀ ∘ g → f ≤UC g
  dummy-at = dummy-complete

  trans-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} {h : A ⇒ T₀ P B}
           → f ≤UC g → g ≤UC h → f ≤UC h
  trans-at = ≤UC-trans

  compose-at : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
               {h : B ⇒ T₀ P C} {k : B ⇒ T₀ Q C}
             → f ≤UC g → h ≤UC k → h ∙ f ≤UC k ∙ g
  compose-at = UC-compose

  -- The one metatheorem that spends the unit — as a grade, through `λ⇒`/`λ⇐`
  -- and `return`, with no closure in sight.
  collapse-at : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰ g
  collapse-at = ≈ᵁ⇒≈ℰ

------------------------------------------------------------------------
-- What the identification would buy

module Interconvert (unit-≅ᵒ : Mor._≅_ ∣𝔾ᵒ∣ 𝟘ᵒ 𝟘ᵘ) where

  open G.HomReasoning
  open MR ∣𝔾ᵒ∣ using (cancelʳ)

  private module ι = Mor._≅_ unit-≅ᵒ

  Closureᵘ : G.Obj → Set (suc 0ℓ)
  Closureᵘ X = 𝟘ᵘ G.⇒ X

  at𝟘 : {X : G.Obj} → Closureᵘ X → Closure X
  at𝟘 n = n G.∘ ι.from

  atᵘ : {X : G.Obj} → Closure X → Closureᵘ X
  atᵘ m = m G.∘ ι.to

  at𝟘-atᵘ : {X : G.Obj} (m : Closure X) → at𝟘 (atᵘ m) G.≈ m
  at𝟘-atᵘ _ = cancelʳ ι.isoˡ

  -- The model owns one closed run, at `unitᴵ` (`UC.Machine.⟦_⟧ᴼ`), so the
  -- unit-spelled observation is DEFINED by factoring.  The content is `≋⇔≋ᵘ`.
  Obsᵘ : Closureᵘ Ωᵒ → Dₚ Bool
  Obsᵘ n = Obs (at𝟘 n)

  infix 4 _≋ᵘ_

  _≋ᵘ_ : {X : G.Obj} → Test X → Test X → Set (suc 0ℓ)
  _≋ᵘ_ {X} e e′ = (n : Closureᵘ X) → Obsᵘ (e G.∘ n) ∼ᴼ Obsᵘ (e′ G.∘ n)

  ≋⇒≋ᵘ : {X : G.Obj} {e e′ : Test X} → e ≋ e′ → e ≋ᵘ e′
  ≋⇒≋ᵘ h n = ∼ᴼ-resp (obs-resp G.sym-assoc) (obs-resp G.sym-assoc) (h (at𝟘 n))

  ≋ᵘ⇒≋ : {X : G.Obj} {e e′ : Test X} → e ≋ᵘ e′ → e ≋ e′
  ≋ᵘ⇒≋ {e = e} {e′} h m =
    ∼ᴼ-resp (obs-resp (step e)) (obs-resp (step e′)) (h (atᵘ m))
    where
    step : (t : Test _) → (t G.∘ atᵘ m) G.∘ ι.from G.≈ t G.∘ m
    step t = G.assoc ○ (refl⟩∘⟨ at𝟘-atᵘ m)

  ≋⇔≋ᵘ : {X : G.Obj} {e e′ : Test X} → e ≋ e′ ⇔ e ≋ᵘ e′
  ≋⇔≋ᵘ {e = e} {e′} = mk⇔ {B = e ≋ᵘ e′} ≋⇒≋ᵘ ≋ᵘ⇒≋

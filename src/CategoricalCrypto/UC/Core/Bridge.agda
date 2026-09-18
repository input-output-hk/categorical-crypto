{-# OPTIONS --safe --without-K #-}

-- The core's environment agreement IS the inherited `_≈ᵁ_`, at any monoidal
-- base and observation — hence the inherited order, hence
-- `Abstract2.UC-compose` on anything the core proves.
--
-- The vocabulary is the trap, and this is the one place it is spelled out.  The
-- core's `_≈ℰ_` (`UC.Environment`, here `C._≈ℰ_`, named apart as `_≈ℰᶜ_`)
-- quantifies over an ancilla; StdUC's `_≈ℰ_` is the bare presheaf kernel and
-- does not.  So the two relations sharing that name are NOT the same one: what
-- the core's coincides with is StdUC's `_≈ᵁ_`.
--
-- The two directions spend different things.  Forward needs no rebracketing
-- and is what an ingested bound spends:
--
--     f ≈ℰᶜ g  ─grade-stable→  id ⊗₁ f ≈ℰᶜ id ⊗₁ g  ─congˡ→
--     μ Y X ∘ id ⊗₁ f ≈ℰᶜ μ Y X ∘ id ⊗₁ g  ─at the unit ancilla→  …≈ℰ…
--
-- `grade-stable` is `UC.Environment`'s theorem — the ancilla quantifier
-- absorbing a bypass wire, with no hypothesis under it — which is exactly what
-- `Abstract2.bridge` asks for and cannot get from a BARE kernel: coming back
-- from that one wants `GradeStable` for `ℰᴼ`, which no instance here supplies,
-- the core buying grade stability by putting the ancilla into the relation
-- instead.  The last step is the unit ancilla, where the two wires cancel by
-- the unitor's naturality and its own iso, and the core's relay is the tensor
-- with an identity on the nose, so nothing needs `T₁-⊗` there.
--
-- Back, the prefix `μ Y X ∘ T₁ Y f` that `_≈ᵁ_` carries is `α⇐ ∘ id ⊗₁ f`
-- (`μT₁-α⇐`), so cancelling it against `α⇒` in the test reads the hypothesis
-- at `Y` as the core's experiment at that ancilla.  That cancellation is
-- `shuffle⇒`/`shuffle⇐`, which the model's robustness and quantitative layers
-- consume directly.
--
-- At UNGRADED homs `_≈ᵁ_` says nothing — it is stated at `A ⇒ T₀ X B` — while
-- the core's relation is stated at every codomain.  `_≈ᴳ_` is what it is
-- there, and agrees with `_≈ᵁ_` wherever the latter is stated, so a seam
-- statement can be read in one vocabulary.
--
-- Universal composition is what the two ORDERS agreeing retires: the core's
-- own order could only state it, and `≤UCᶜ⇔≤UC` carries `Abstract2.UC-compose`
-- — already a theorem — across, leaving the core nothing to owe.
--
-- Everything is generic: the whole argument is monoidal laws plus the core's
-- own congruences, so no instance unfolds while it is checked.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Monoidal.CurriedTensor.Properties
  using (T₁-⊗; μ-α⇐; μT₁-α⇐)
import Categories.Morphism.Reasoning as MR

open import Data.Product.Base using (Σ-syntax; _,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Core using (Observation)

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Environment as Env

module CategoricalCrypto.UC.Core.Bridge
  {o ℓ e os ℓs : Level} (M : MonoidalCategory o ℓ e)
  (O : Observation (MonoidalCategory.U M) os ℓs) where

module C = Env M O

open Std2.StdUC M C.ℰᴼ public

open HomReasoning
open MR ∣machines∣ using (cancelInner; cancelˡ)

private variable A B C X Y : Channel

infix 4 _≈ℰᶜ_

_≈ℰᶜ_ : (f g : A ⇒ B) → Set (o ⊔ ℓ ⊔ ℓs)
_≈ℰᶜ_ = C._≈ℰ_

private
  -- The unit ancilla, plugged: the two unitor wires cancel around `id ⊗₁ u`.
  plug : (t : B ⇒ C.Ω) (u : A ⇒ B) (m : C.𝟙 ⇒ A)
       → ((t ∘ unitorˡ.from) ∘ id ⊗₁ u) ∘ (unitorˡ.to ∘ m) ≈ (t ∘ u) ∘ m
  plug t u m = ((assoc ○ (refl⟩∘⟨ unitorˡ-commute-from) ○ sym-assoc) ⟩∘⟨refl)
             ○ cancelInner unitorˡ.isoʳ

-- The core's relation refines the bare kernel: an agreement seen by every
-- ancilla is in particular seen by the trivial one.
≈ℰᶜ⇒≈ℰ : {f g : A ⇒ B} → f ≈ℰᶜ g → f ≈ℰ g
≈ℰᶜ⇒≈ℰ {f = f} {g} h = KE.mk∼ λ {t} m →
  C.∼-cast (plug t f m) (plug t g m) (h unit (t ∘ unitorˡ.from) (unitorˡ.to ∘ m))

≈ℰᶜ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≈ᵁ g
≈ℰᶜ⇒≈ᵁ {f = f} {g} h Y =
  ≈ℰ-trans (≈C⇒≈ℰ (step f))
           (≈ℰ-trans (≈ℰᶜ⇒≈ℰ (C.≈ℰ-congˡ (μ Y _) (C.grade-stable Y h)))
                     (≈ℰ-sym (≈C⇒≈ℰ (step g))))
  where
  step : (u : A ⇒ T₀ X B) → μ Y X ∘ T₁ Y u ≈ μ Y X ∘ id ⊗₁ u
  step u = refl⟩∘⟨ T₁-⊗ M Y u

-- The cancellation the backward direction is, in the two orientations its
-- consumers state their own bracketing at.
shuffle⇒ : (f : A ⇒ T₀ X B) (e : C.Test (Y ⊗₀ X ⊗₀ B)) (m : C.Closure (Y ⊗₀ A))
         → ((e ∘ α⇒) ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ e ∘ id ⊗₁ f ∘ m
shuffle⇒ {Y = Y} f e m =
  ((refl⟩∘⟨ μT₁-α⇐ M Y f) ⟩∘⟨refl) ○ (cancelInner associator.isoʳ ⟩∘⟨refl) ○ assoc

shuffle⇐ : (f : A ⇒ T₀ X B) (e : C.Test ((Y ⊗₀ X) ⊗₀ B)) (m : C.Closure (Y ⊗₀ A))
         → (e ∘ μ Y X ∘ T₁ Y f) ∘ m ≈ (e ∘ α⇐) ∘ id ⊗₁ f ∘ m
shuffle⇐ {Y = Y} f e m =
  ((refl⟩∘⟨ μT₁-α⇐ M Y f) ⟩∘⟨refl) ○ (sym-assoc ⟩∘⟨refl) ○ assoc

≈ᵁ⇒≈ℰᶜ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰᶜ g
≈ᵁ⇒≈ℰᶜ {f = f} {g} u Y E m = C.∼-cast (step f) (step g) (KE.run∼ (u Y) {E ∘ α⇒} m)
  where step = λ x → shuffle⇒ x E m ○ sym-assoc

≈ℰᶜ⇔≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g ⇔ f ≈ᵁ g
≈ℰᶜ⇔≈ᵁ = mk⇔ ≈ℰᶜ⇒≈ᵁ ≈ᵁ⇒≈ℰᶜ

------------------------------------------------------------------------
-- The same identification at ungraded homs

infix 4 _≈ᴳ_

-- The bare kernel read at every ancilla: the largest grade-stable relation
-- under `_≈ℰ_`, and the inherited spelling of the core's relation where
-- `_≈ᵁ_` is not stated.
_≈ᴳ_ : (f g : A ⇒ B) → Set (o ⊔ ℓ ⊔ ℓs)
_≈ᴳ_ f g = (Y : Channel) → T₁ Y f ≈ℰ T₁ Y g

≈ᴳ-refl : {f : A ⇒ B} → f ≈ᴳ f
≈ᴳ-refl _ = ≈ℰ-refl

≈ᴳ-sym : {f g : A ⇒ B} → f ≈ᴳ g → g ≈ᴳ f
≈ᴳ-sym h Y = ≈ℰ-sym (h Y)

≈ᴳ-trans : {f g h : A ⇒ B} → f ≈ᴳ g → g ≈ᴳ h → f ≈ᴳ h
≈ᴳ-trans p q Y = ≈ℰ-trans (p Y) (q Y)

≈C⇒≈ᴳ : {f g : A ⇒ B} → f ≈ g → f ≈ᴳ g
≈C⇒≈ᴳ e _ = ≈C⇒≈ℰ (T-resp-≈ e)

≈ᴳ-congˡ : (k : B ⇒ C) {f g : A ⇒ B} → f ≈ᴳ g → k ∘ f ≈ᴳ k ∘ g
≈ᴳ-congˡ k h Y = ≈ℰ-trans (≈C⇒≈ℰ T-homomorphism)
  (≈ℰ-trans (≈ℰ-cong-post (T₁ Y k) (h Y)) (≈C⇒≈ℰ (⟺ T-homomorphism)))

≈ᴳ-congʳ : (l : C ⇒ A) {f g : A ⇒ B} → f ≈ᴳ g → f ∘ l ≈ᴳ g ∘ l
≈ᴳ-congʳ l h Y = ≈ℰ-trans (≈C⇒≈ℰ T-homomorphism)
  (≈ℰ-trans (≈ℰ-cong-pre (T₁ Y l) (h Y)) (≈C⇒≈ℰ (⟺ T-homomorphism)))

-- Where `_≈ᵁ_` is stated the two coincide: the prefix `μ Y X` it carries is an
-- iso (`μ-α⇐`, `associator.isoʳ`), so composing with it changes nothing.
≈ᴳ⇒≈ᵁ : {f g : A ⇒ T₀ X B} → f ≈ᴳ g → f ≈ᵁ g
≈ᴳ⇒≈ᵁ {X = X} h Y = ≈ℰ-cong-post (μ Y X) (h Y)

≈ᵁ⇒≈ᴳ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ᴳ g
≈ᵁ⇒≈ᴳ {X = X} {f = f} {g} u Y =
  ≈ℰ-trans (≈C⇒≈ℰ (⟺ (cancel f))) (≈ℰ-trans (≈ℰ-cong-post α⇒ (u Y)) (≈C⇒≈ℰ (cancel g)))
  where
  cancel : {A′ B′ : Channel} (x : A′ ⇒ T₀ X B′) → α⇒ ∘ μ Y X ∘ T₁ Y x ≈ T₁ Y x
  cancel _ = cancelˡ (∘-resp-≈ʳ (μ-α⇐ M Y X) ○ associator.isoʳ)

-- …and everywhere it is the core's, which is what licenses reading a seam
-- statement in the inherited vocabulary without weakening it.
private
  -- The core's action is the tensor's own `F₁`; the triple derives its `T₁` and
  -- pays one triangle for the identification.
  reT₁ : (f : A ⇒ B) (e : C.Test (Y ⊗₀ B)) (m : C.Closure (Y ⊗₀ A))
       → (e ∘ T₁ Y f) ∘ m ≈ (e ∘ id ⊗₁ f) ∘ m
  reT₁ {Y = Y} f _ _ = (refl⟩∘⟨ T₁-⊗ M Y f) ⟩∘⟨refl

≈ᴳ⇒≈ℰᶜ : {f g : A ⇒ B} → f ≈ᴳ g → f ≈ℰᶜ g
≈ᴳ⇒≈ℰᶜ {f = f} {g} h Y e m = C.∼-cast (reT₁ f e m) (reT₁ g e m) (KE.run∼ (h Y) {e} m)

≈ℰᶜ⇒≈ᴳ : {f g : A ⇒ B} → f ≈ℰᶜ g → f ≈ᴳ g
≈ℰᶜ⇒≈ᴳ {f = f} {g} h Y = KE.mk∼ λ {e} m →
  C.∼-cast (⟺ (reT₁ f e m)) (⟺ (reT₁ g e m)) (h Y e m)

≈ᴳ⇔≈ℰᶜ : {f g : A ⇒ B} → f ≈ᴳ g ⇔ f ≈ℰᶜ g
≈ᴳ⇔≈ℰᶜ {f = f} {g} = mk⇔ {B = f ≈ℰᶜ g} ≈ᴳ⇒≈ℰᶜ ≈ℰᶜ⇒≈ᴳ

-- `C.≈ℰ-at`, the same shape past the inherited kernel: an agreement read at ONE
-- context, presented uniformly in the process.  Stated away from any machine
-- layer for the reason `UC.Seam.Grounding`'s header gives — there a `∼` between
-- machine COMPOSITES η-expands the observation record — so a seam supplies the
-- three components and the equation, and nothing else.
≈ᴳ-at : (Y : Channel) (Et : C.Test (Y ⊗₀ B)) (m : C.Closure (Y ⊗₀ A))
        (k : A ⇒ B → C.Closure C.Ω) → ((w : A ⇒ B) → (Et ∘ T₁ Y w) ∘ m ≈ k w)
      → {f g : A ⇒ B} → f ≈ᴳ g → C.⟦ k f ⟧ C.∼ C.⟦ k g ⟧
≈ᴳ-at Y Et m k eq {f} {g} r = C.∼-cast (eq f) (eq g) (KE.run∼ (r Y) {Et} m)

------------------------------------------------------------------------
-- …and the two emulation orders agree

infix 4 _≤UCᶜ_

-- The core's own dummy-form order, recorded here as the subject of the
-- equivalence below: the inherited `_≤UC_` carries an adversary quantifier in
-- its statement, and `dummy-complete`/`≤UC⇒dummy` are what read one as the
-- other.  `_≤UC_` is where `UC-compose`, `≤UC-trans` and `dummy-complete` are
-- stated, so a bound the core proves enters the metatheory here.
_≤UCᶜ_ : A ⇒ T₀ X B → A ⇒ T₀ Y B → Set (o ⊔ ℓ ⊔ ℓs)
_≤UCᶜ_ {X = X} {Y = Y} f g = Σ[ s ∈ Y ⇒ X ] f ≈ℰᶜ (sub s ∘ g)

≈ℰᶜ⇒≤UC : {f g : A ⇒ T₀ X B} → f ≈ℰᶜ g → f ≤UC g
≈ℰᶜ⇒≤UC {g = g} h =
  dummy-complete (id , ≈ᵁ-trans (≈ℰᶜ⇒≈ᵁ h) (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ g))))

≤UCᶜ⇒≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g → f ≤UC g
≤UCᶜ⇒≤UC (s , e) = dummy-complete (s , ≈ℰᶜ⇒≈ᵁ e)

≤UC⇒≤UCᶜ : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UC g → f ≤UCᶜ g
≤UC⇒≤UCᶜ p = let s , e = ≤UC⇒dummy p in s , ≈ᵁ⇒≈ℰᶜ e

≤UCᶜ⇔≤UC : {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B} → f ≤UCᶜ g ⇔ f ≤UC g
≤UCᶜ⇔≤UC {f = f} {g} = mk⇔ {B = f ≤UC g} ≤UCᶜ⇒≤UC ≤UC⇒≤UCᶜ

{-# OPTIONS --safe --without-K #-}

-- Qualitative UC preservation: what an emulation carries when nothing
-- numerical is in play.
--
-- `UC.Audit.audit-carry` moves a MASS bound across an emulation and pays for
-- the simulator's queries out of the context's budget.  The same slide works
-- with no arithmetic under it at all, provided the property carried cannot see
-- the difference between observationally equal runs: `SaturatedProperty` is
-- such a property (`saturated` is exactly `_∼_`-invariance), `Robust` says it
-- survives every closing context, and `uc-preserves` is the carry — `sub s`
-- slides off the process and onto the test, so a closing context of the real
-- system is a closing context of the ideal one with the simulator in front.
--
-- Robustness quantifies over ALL closing contexts, and that is what makes the
-- carry premise-free: an invariant property is closed under the absorption
-- automatically, so no `Absorbs` datum is needed.  For a mass-valued property
-- the total class is too coarse — `UC.Audit`'s header records why a bound over
-- every budgeted test is uninhabitable at a trivial grade — and designating a
-- smaller class is what `AuditEvent` is for.  `UC.Asymptotic.uc-preservesᴺ` is
-- the third carry, the one with the probability in it.
--
-- SCOPE.  A generic metatheorem about invariant properties, and no more: it
-- discharges neither a concrete monitor inclusion nor any error-uniformity
-- obligation (`docs/protocol-implementation-review.md` §§1-2, 4) — there is no
-- error here to be uniform in.

open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤; tt)

open import Level using (Level; 0ℓ; _⊔_; suc)

open import CategoricalCrypto.UC.Core using (UCBase)

module CategoricalCrypto.UC.Robust
  {o ℓ e os ℓs} (base : UCBase o ℓ e os ℓs) where

open import CategoricalCrypto.UC.Emulation base

private variable A B′ X Y Z : Obj
                 p : Level

------------------------------------------------------------------------
-- Observation-invariant properties

-- What the core's equivalence cannot see: a predicate on closed observations
-- that `_∼_` may not refute.  `UC.Saturated`'s existential slack is the shape a
-- NUMERICAL statement needs to reach this invariance; here it is the definition.
record SaturatedProperty (p : Level) : Set (os ⊔ ℓs ⊔ suc p) where
  field
    holds     : Obs → Set p
    saturated : {u v : Obs} → u ∼ v → holds u → holds v

open SaturatedProperty public

-- The terminal one: invariance is vacuous, and everything below is robust for
-- it.  What a consumer instantiates to read the API's shape off.
⊤ᴾ : SaturatedProperty 0ℓ
⊤ᴾ = record { holds = λ _ → ⊤ ; saturated = λ _ _ → tt }

-- The nontrivial shape: the run shows a designated verdict.  Invariance is
-- `_∼_`'s own transitivity, so no property-specific argument is spent.
∼[_] : Obs → SaturatedProperty ℓs
∼[ r ] = record { holds = r ∼_ ; saturated = λ h k → ∼-trans k h }

------------------------------------------------------------------------
-- Robustness

-- Under every closing context: the ancilla, test and closure `_≈ℰ_` itself
-- quantifies over, so a robust property is stated at exactly the experiments
-- the environment layer already has.
--
-- The property stays EXPLICIT throughout this section: `Robust 𝔓 f` reduces to
-- a Π type whose body applies `holds 𝔓`, which no use site can invert.
Robust : {A B′ : Obj} (𝔓 : SaturatedProperty p) → A ⇒ B′ → Set (o ⊔ ℓ ⊔ p)
Robust {A = A} {B′} 𝔓 f = (Y : Obj) (Et : Test (Y ⊛ B′)) (m : Closure (Y ⊛ A))
                        → holds 𝔓 (obs (tv₁ Y f Et) m)

-- Invariance read at the contexts rather than at the observations: an
-- environment agreement is a context-by-context `_∼_`, and that is all a
-- saturated property needs.
robust-resp-≈ℰ : (𝔓 : SaturatedProperty p) {f g : A ⇒ B′}
               → f ≈ℰ g → Robust 𝔓 g → Robust 𝔓 f
robust-resp-≈ℰ 𝔓 e rob W Et m = saturated 𝔓 (∼-sym (e W Et m)) (rob W Et m)

-- The simulator slide, with no budget to charge it to: testing `sub s ∘ g`
-- through `Et` is testing `g` through `Et` with the simulator in front of it,
-- which is again a closing context of `g`.
robust-sub : (𝔓 : SaturatedProperty p) {g : A ⇒ Y ⊛ B′} (s : Y ⇒ X)
           → Robust 𝔓 g → Robust 𝔓 (sub s ∘ g)
robust-sub 𝔓 {g} s rob W Et m =
  saturated 𝔓 (⟦⟧-resp-≈ (Equiv.sym slide)) (rob W (Et ∘ T₁ W (sub s)) m)
  where
  slide : (Et ∘ T₁ W (sub s ∘ g)) ∘ m ≈ ((Et ∘ T₁ W (sub s)) ∘ T₁ W g) ∘ m
  slide = ∘-resp-≈ˡ (Equiv.trans (∘-resp-≈ʳ T₁-∘) sym-assoc)

------------------------------------------------------------------------
-- Preservation

-- The carry: a robust invariant property of the ideal system is one of the
-- real system.  The emulation's simulator goes into the test, the ideal
-- robustness is invoked at the extended context, and the emulation's own
-- agreement brings the property back.
uc-preserves : (𝔓 : SaturatedProperty p) {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′}
             → f ≤UC g → Robust 𝔓 g → Robust 𝔓 f
uc-preserves 𝔓 (s , e) rob = robust-resp-≈ℰ 𝔓 e (robust-sub 𝔓 s rob)

-- The dummy-adversary form, at the same cost: the emulation supplies a
-- simulator per adversary, so the conclusion is about the real system with that
-- adversary attached.  `dummy-complete` makes this the weaker statement of the
-- two, not a second theorem.
uc⁺-preserves : (𝔓 : SaturatedProperty p) {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′}
              → f ≤UC⁺ g → Robust 𝔓 g → (a : X ⇒ Z) → Robust 𝔓 (sub a ∘ f)
uc⁺-preserves 𝔓 le rob a =
  let s , e = le a in robust-resp-≈ℰ 𝔓 e (robust-sub 𝔓 s rob)

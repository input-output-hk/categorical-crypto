{-# OPTIONS --safe --without-K --guardedness #-}

-- The intended model: the UC layer over the machine layer, with `Iface`
-- objects.
--
-- `⟦_⟧ᴵ` is a bijection between `Iface` and `𝒢ₚ`'s objects, so presenting the
-- G construction with interfaces as its objects costs one reindexing record and
-- makes `_⊗ᴵ_` — the interface tensor layer 0 already defines — the grading
-- action.  Every object of this layer is an interface; no raw pair of sets, and
-- no `Channel`, appears anywhere.
--
-- The verdict interface is TICKED (`Neg Ωᴵ = ⊤`).  A machine is reactive, so a
-- closed composite at a verdict interface with an empty negative side could
-- never be activated and would observe nothing; the tick is the environment's
-- single activation, and the observation is then layer 1's own closed run at
-- the one-ask strategy.
--
-- The grading's DATA is direct: `T₁ᴵ` and `subᴵ` keep the plugged process's
-- state and only relabel the interface sum, so no coherence morphism and no
-- trace appears in them, and the two ancilla reassociators are stateless wires.
-- The laws are collected in `GradingLawsᴹ` and priced — see its comment.

open import Categories.Category using (Category; _[_,_]; _[_≈_])

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic.Base as PolyUnit
open import Level using (0ℓ; suc)

open import ProbabilisticLogic.Dp using (Dₚ; mapₚ; returnₚ)
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ; runᴹ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Approximate
  using (Approximation; ApproximateObservation; ℚ-errors; module Induced)
open import CategoricalCrypto.UC.Core using (Grading; Observation; UCBase)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Machine where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒢 = Category (𝒢ₚ 0ℓ)

------------------------------------------------------------------------
-- Processes on interfaces

-- A `𝒢ₚ`-hom read at interfaces: `Machine (A⁺ + B⁻) (A⁻ + B⁺)`, a process that
-- answers queries from above and issues queries below.
Proc : Iface → Iface → Set₁
Proc A B = 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]

-- Every object implicit is passed explicitly.  Left to inference, each field
-- asks Agda to invert `Machine (Pos A + Neg B) (Neg A + Pos B)` for the pair
-- `(Pos A , Neg B)`, and `_+_` is not a constructor: the resulting
-- normalization of `𝒢ₚ` — which carries the whole Elgot instance under it —
-- exhausts a 10 GiB heap.
𝒫ᴵ : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝒫ᴵ = record
  { Obj       = Iface
  ; _⇒_       = Proc
  ; _≈_       = λ {A} {B} → 𝒢._≈_ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
  ; id        = λ {A} → 𝒢.id {⟦ A ⟧ᴵ}
  ; _∘_       = λ {A} {B} {C} → 𝒢._∘_ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ}
  ; assoc     = λ {A} {B} {C} {D} → 𝒢.assoc {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} {⟦ D ⟧ᴵ}
  ; sym-assoc = λ {A} {B} {C} {D} → 𝒢.sym-assoc {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} {⟦ D ⟧ᴵ}
  ; identityˡ = λ {A} {B} → 𝒢.identityˡ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
  ; identityʳ = λ {A} {B} → 𝒢.identityʳ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
  ; identity² = λ {A} → 𝒢.identity² {⟦ A ⟧ᴵ}
  ; equiv     = λ {A} {B} → 𝒢.equiv {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
  ; ∘-resp-≈  = λ {A} {B} {C} → 𝒢.∘-resp-≈ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ}
  }

private module 𝒫 = Category 𝒫ᴵ

-- The base category's tensor unit, which is also the state object of every
-- stateless machine.
⊤ᵛ : Set
⊤ᵛ = PolyUnit.⊤ {0ℓ}

-- A stateless forwarder: a positive message travels up, a negative one down.
-- The step is a named function so that a statement about it can be made
-- without projecting one out of a `Proc` (`UC.QueryBound`).
wireStep : {A B : Iface} → (Pos A → Pos B) → (Neg B → Neg A)
         → ⊤ᵛ × (Pos A ⊎ Neg B) → Dₚ (⊤ᵛ × (Neg A ⊎ Pos B))
wireStep up down (s , inj₁ p) = returnₚ (s , inj₂ (up p))
wireStep up down (s , inj₂ n) = returnₚ (s , inj₁ (down n))

wireᴹ : {A B : Iface} → (Pos A → Pos B) → (Neg B → Neg A) → Proc A B
wireᴹ up down = MC.mk MC.Iˢ (wireStep up down)

------------------------------------------------------------------------
-- The observation

Ωᴵ : Iface
Ωᴵ = Bool ⇿ ⊤

⟦_⟧ᴼ : Proc unitᴵ Ωᴵ → Dₚ Bool
⟦ M ⟧ᴼ = runᴹ M (ask tt out)

-- The advantage is a RELATION, not a function: `Dₚ`'s termination mass is a
-- supremum this layer never forms, so an `adv : Obs → Obs → ℚ` would be
-- uninhabited here (`ProbabilisticLogic.Dp.Advantage`'s header).  Rational
-- slack is what survives, and it carries exactly the four laws the abstract
-- error layer asks for.
Approximationᴹ : Approximation (Dₚ Bool) ℚ-errors 0ℓ
Approximationᴹ = record
  { _≈[_]_    = _≈ₚ[_]_
  ; ≈[]-refl  = ≈ₚ[]-refl
  ; ≈[]-sym   = ≈ₚ[]-sym
  ; ≈[]-trans = ≈ₚ[]-trans
  ; ≈[]-mono  = ≈ₚ[]-mono
  }

private
  module I = Induced 𝒫ᴵ Approximationᴹ unitᴵ Ωᴵ ⟦_⟧ᴼ
                     (λ eq → ≈ₚ⇒≈ₚ[0] (runᴹ-resp-≈ᴹ {Ωᴵ} eq (ask tt out)))

-- The qualitative observation, as the core wants it: two closed runs agree when
-- no positive slack separates their verdict masses.
Observationᴹ : Observation 𝒫ᴵ 0ℓ 0ℓ
Observationᴹ = I.observation

ApproximateObservationᴹ : ApproximateObservation Observationᴹ ℚ-errors 0ℓ
ApproximateObservationᴹ = I.approximate

------------------------------------------------------------------------
-- The grading action, as data

private
  ⊎assocˡ : {P Q R : Set} → P ⊎ (Q ⊎ R) → (P ⊎ Q) ⊎ R
  ⊎assocˡ (inj₁ p)        = inj₁ (inj₁ p)
  ⊎assocˡ (inj₂ (inj₁ q)) = inj₁ (inj₂ q)
  ⊎assocˡ (inj₂ (inj₂ r)) = inj₂ r

  ⊎assocʳ : {P Q R : Set} → (P ⊎ Q) ⊎ R → P ⊎ (Q ⊎ R)
  ⊎assocʳ (inj₁ (inj₁ p)) = inj₁ p
  ⊎assocʳ (inj₁ (inj₂ q)) = inj₂ (inj₁ q)
  ⊎assocʳ (inj₂ r)        = inj₂ (inj₂ r)

-- An ancilla interface bypassing a process: the process's own messages go
-- through it, the ancilla's are forwarded, and the state is the process's.
T₁ᴵ : (Y : Iface) {A B : Iface} → Proc A B → Proc (Y ⊗ᴵ A) (Y ⊗ᴵ B)
T₁ᴵ Y {A} {B} f = MC.mk (MC.state f) stepT
  where
  outT : Neg A ⊎ Pos B → (Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)
  outT (inj₁ a) = inj₁ (inj₂ a)
  outT (inj₂ b) = inj₂ (inj₂ b)

  relay : Dₚ (MC.St f × (Neg A ⊎ Pos B))
        → Dₚ (MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)))
  relay = mapₚ λ p → proj₁ p , outT (proj₂ p)

  stepT : MC.St f × ((Pos Y ⊎ Pos A) ⊎ (Neg Y ⊎ Neg B))
        → Dₚ (MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)))
  stepT (s , inj₁ (inj₁ y)) = returnₚ (s , inj₂ (inj₁ y))
  stepT (s , inj₁ (inj₂ a)) = relay (MC.step f (s , inj₁ a))
  stepT (s , inj₂ (inj₁ y)) = returnₚ (s , inj₁ (inj₁ y))
  stepT (s , inj₂ (inj₂ b)) = relay (MC.step f (s , inj₂ b))

-- A simulator acting on the ancilla alone; this time it is the bypassed
-- interface that is forwarded.
subᴵ : {X Y : Iface} → Proc X Y → {A : Iface} → Proc (X ⊗ᴵ A) (Y ⊗ᴵ A)
subᴵ {X} {Y} s {A} = MC.mk (MC.state s) stepS
  where
  outS : Neg X ⊎ Pos Y → (Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)
  outS (inj₁ x) = inj₁ (inj₁ x)
  outS (inj₂ y) = inj₂ (inj₁ y)

  relay : Dₚ (MC.St s × (Neg X ⊎ Pos Y))
        → Dₚ (MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)))
  relay = mapₚ λ p → proj₁ p , outS (proj₂ p)

  stepS : MC.St s × ((Pos X ⊎ Pos A) ⊎ (Neg Y ⊎ Neg A))
        → Dₚ (MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)))
  stepS (t , inj₁ (inj₁ x)) = relay (MC.step s (t , inj₁ x))
  stepS (t , inj₁ (inj₂ a)) = returnₚ (t , inj₂ (inj₂ a))
  stepS (t , inj₂ (inj₁ y)) = relay (MC.step s (t , inj₂ y))
  stepS (t , inj₂ (inj₂ a)) = returnₚ (t , inj₁ (inj₂ a))

a⇒ᴵ : {X Y A : Iface} → Proc (X ⊗ᴵ (Y ⊗ᴵ A)) ((X ⊗ᴵ Y) ⊗ᴵ A)
a⇒ᴵ = wireᴹ ⊎assocˡ ⊎assocʳ

a⇐ᴵ : {X Y A : Iface} → Proc ((X ⊗ᴵ Y) ⊗ᴵ A) (X ⊗ᴵ (Y ⊗ᴵ A))
a⇐ᴵ = wireᴹ ⊎assocʳ ⊎assocˡ

------------------------------------------------------------------------
-- …and its laws, priced

-- Four of the eight are TRACE-FREE: `T₁ᴵ`/`subᴵ` keep the plugged process's
-- state and only relabel the interface, so `T₁-resp-≈`/`sub-resp-≈` are one
-- `_≲_` at the given simulation's own state map, and `T₁-id`/`sub-id` compare
-- two stateless wires (`𝒫.id` is `σᴹ = pureᴹ +-swap`) up to the junctions a
-- `pureᴹ` spends.  The other four each compare a `𝒫ᴵ`-composite, and
-- composition here is the ⊕-trace, so each needs the trace-fusion step M2's
-- task 3 left open — the same gate as `Monoidal (GConstruction C)`'s
-- `homomorphism`.  Stated as a record and inhabited by nothing — no escape
-- hatch, as everywhere in this branch.
record GradingLawsᴹ : Set (suc 0ℓ) where
  field
    T₁-resp-≈  : {Y A B : Iface} {f g : Proc A B}
               → 𝒫ᴵ [ f ≈ g ] → 𝒫ᴵ [ T₁ᴵ Y f ≈ T₁ᴵ Y g ]
    T₁-id      : {Y A : Iface} → 𝒫ᴵ [ T₁ᴵ Y (𝒫.id {A}) ≈ 𝒫.id ]
    T₁-∘       : {Y A B C : Iface} {g : Proc B C} {f : Proc A B}
               → 𝒫ᴵ [ T₁ᴵ Y (g 𝒫.∘ f) ≈ T₁ᴵ Y g 𝒫.∘ T₁ᴵ Y f ]
    sub-resp-≈ : {X Y A : Iface} {s t : Proc X Y}
               → 𝒫ᴵ [ s ≈ t ] → 𝒫ᴵ [ subᴵ s {A} ≈ subᴵ t ]
    sub-id     : {X A : Iface} → 𝒫ᴵ [ subᴵ (𝒫.id {X}) {A} ≈ 𝒫.id ]
    sub-∘      : {X Y Z A : Iface} {t : Proc Y Z} {s : Proc X Y}
               → 𝒫ᴵ [ subᴵ (t 𝒫.∘ s) {A} ≈ subᴵ t 𝒫.∘ subᴵ s ]
    a-isoˡ     : {X Y A : Iface} → 𝒫ᴵ [ a⇐ᴵ {X} {Y} {A} 𝒫.∘ a⇒ᴵ ≈ 𝒫.id ]
    a-nat      : {X Y A B : Iface} {f : Proc A B}
               → 𝒫ᴵ [ a⇒ᴵ 𝒫.∘ T₁ᴵ X (T₁ᴵ Y f) ≈ T₁ᴵ (X ⊗ᴵ Y) f 𝒫.∘ a⇒ᴵ ]

-- `Gradingᴹ : GradingLawsᴹ → Grading 𝒫ᴵ` does NOT assemble, and the reason is
-- not the laws: matching the data above against `Grading`'s field types makes
-- Agda compare `Proc X Y` with `Category._⇒_ 𝒫ᴵ X Y` after whnf-ing both to
-- `Machine (Mealy-Monoidal (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) .⊗₀ …) …`, and the
-- record-eta comparison of those two spellings of the base exhausts a 10 GiB
-- heap — the `GradedKleisli` eta cliff, at a different index.  So the
-- obligation is taken at `Grading 𝒫ᴵ` itself: `GradingLawsᴹ` says what has to
-- be proved, `UCBaseᴹ` says what it buys, and the assembly wants either the
-- one-spelling discipline that cures the cliff or an `opaque` boundary around
-- the base instance.
UCBaseᴹ : Grading 𝒫ᴵ → UCBase (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ
UCBaseᴹ G = record { 𝒞 = 𝒫ᴵ ; grading = G ; observation = Observationᴹ }

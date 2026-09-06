{-# OPTIONS --safe --without-K --guardedness #-}

-- The intended model: the UC layer over the machine layer.
--
-- `⟦_⟧ᴵ` is a bijection between `Iface` and `𝒢ₚ`'s objects, with a definitional
-- retraction `retᴵ`, so a hom of `𝒢ₚ` at any objects IS a `Proc` and either
-- vocabulary reads the other with no coercion.  `𝒫ᴵ` — the reindexing at
-- `Iface` objects — is kept for the statements written in that vocabulary
-- (`UC.QueryBound`, `UC.Seam`, `Protocol.Machine`), but the GRADING is taken on
-- 𝒢's own objects, where it is free; `gradingᴹ` below prices the difference.
-- No `Channel` appears anywhere.
--
-- The verdict interface is TICKED (`Neg Ωᴵ = ⊤`).  A machine is reactive, so a
-- closed composite at a verdict interface with an empty negative side could
-- never be activated and would observe nothing; the tick is the environment's
-- single activation, and the observation is then layer 1's own closed run at
-- the one-ask strategy.
--
-- The relays `T₁ᴵ`/`subᴵ` and the two ancilla reassociators are kept as
-- VOCABULARY: they are direct — the plugged process's state, the interface sum
-- relabelled, no coherence morphism and no trace — which is what makes a query
-- bound about them readable (`UC.QueryBound`).  They are no longer the
-- grading's data; the grading is `gradingᴹ` below, derived on 𝒢's own objects,
-- and `UC.Machine.Dictionary`'s zigzags are the bridge between the two.

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
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ; runᴹ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Approximate
  using (Approximation; ApproximateObservation; ℚ-errors; module Induced)
open import CategoricalCrypto.UC.Core using (Grading; Observation; UCBase)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Machine where

-- Re-exported from the module body, which is where `public` is allowed:
-- `UC.QueryBound`'s `qbᵢ-wire` certificates for `a⇒ᴵ`/`a⇐ᴵ` name the two
-- reassociators, as does `UC.Machine.Grading`.
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ) public

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
-- error layer asks for.  It compares BOTH verdict masses, since divergence
-- weighs 0 under either indicator and the `true`-mass alone would identify a
-- process that answers `false` with one that diverges (proposal §1,
-- `docs/kb/frontier/15-probabilistic-uc-model.typ`).
Approximationᴹ : Approximation (Dₚ Bool) ℚ-errors 0ℓ
Approximationᴹ = record
  { _≈[_]_    = _≈ₚ[_]_
  ; ≈[]-refl  = ≈ₚ[]-refl
  ; ≈[]-sym   = ≈ₚ[]-sym
  ; ≈[]-trans = ≈ₚ[]-trans
  ; ≈[]-mono  = ≈ₚ[]-mono
  }

-- The observation is homed on `𝒢ₚ`, not on `𝒫ᴵ`, because that is where the
-- grading is: `Proc unitᴵ Ωᴵ` IS `𝒢ₚ [ ⟦ unitᴵ ⟧ᴵ , ⟦ Ωᴵ ⟧ᴵ ]`, so `⟦_⟧ᴼ` and
-- its congruence apply verbatim and only the index moves.
private
  module I = Induced (𝒢ₚ 0ℓ) Approximationᴹ ⟦ unitᴵ ⟧ᴵ ⟦ Ωᴵ ⟧ᴵ ⟦_⟧ᴼ
                     (λ eq → ≈ₚ⇒≈ₚ[0] (runᴹ-resp-≈ᴹ {Ωᴵ} eq (ask tt out)))

-- The qualitative observation, as the core wants it: two closed runs agree when
-- no positive slack separates their verdict masses.
Observationᴹ : Observation (𝒢ₚ 0ℓ) 0ℓ 0ℓ
Observationᴹ = I.observation

ApproximateObservationᴹ : ApproximateObservation Observationᴹ ℚ-errors 0ℓ
ApproximateObservationᴹ = I.approximate

------------------------------------------------------------------------
-- The grading action, as data

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

-- `Grading.sub` takes the bypassed interface implicit BEFORE the simulator, so
-- the field value is this reordering; definitionally `subᴵ′ s = subᴵ s`.
-- Giving the field a bare definition rather than a lambda keeps the later
-- fields' expected types free of a beta-redex.
subᴵ′ : {X Y A : Iface} → Proc X Y → Proc (X ⊗ᴵ A) (Y ⊗ᴵ A)
subᴵ′ {A = A} s = subᴵ s {A}

a⇒ᴵ : {X Y A : Iface} → Proc (X ⊗ᴵ (Y ⊗ᴵ A)) ((X ⊗ᴵ Y) ⊗ᴵ A)
a⇒ᴵ = wireᴹ ⊎assocˡ ⊎assocʳ

a⇐ᴵ : {X Y A : Iface} → Proc ((X ⊗ᴵ Y) ⊗ᴵ A) (X ⊗ᴵ (Y ⊗ᴵ A))
a⇐ᴵ = wireᴹ ⊎assocʳ ⊎assocˡ

------------------------------------------------------------------------
-- The grading, and the UC base it buys

-- The grading is the one a monoidal category carries for free
-- (`UC.Core.Standard.gradingᵗ`), read at `𝒢ₚᴹ` — and it is read on 𝒢's OWN
-- objects rather than on `Iface`.  That is measured, not chosen.  `gradingᵗ`
-- PLUGS each `Monoidal` law into a `Grading` field whose type is derived from
-- it, and never writes such a type out; the whole eight-law record costs
-- 363 ms.  Writing any one of those types out instead costs ~470 s at this
-- instance, because a `Monoidal` law is stated with the record's own private
-- `_⊗₀_`/`_⊗₁_` abbreviations, which no consumer can name, so the mismatch is
-- settled by reducing both sides through the ⊕-trace.  Re-presenting the same
-- record on `Iface` objects is the same wall (measured >1500 s), which is why
-- `Iface` stays VOCABULARY — `⟦_⟧ᴵ`, `retᴵ` and the relays below — and is not
-- the grading's object type.  `docs/protocol-rewrite.md` carries the table.
gradingᴹ : Grading (𝒢ₚ 0ℓ)
gradingᴹ = Std.gradingᵗ (𝒢ₚᴹ 0ℓ)

ucBaseᴹ : UCBase (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ
ucBaseᴹ = record { 𝒞 = 𝒢ₚ 0ℓ ; grading = gradingᴹ ; observation = Observationᴹ }

-- `⟦_⟧ᴵ`'s retraction: `Iface` and `𝒢ₚ`'s objects are both eta records, so this
-- is a definitional inverse and a hom of `𝒢ₚ` at any objects is a `Proc`.  It is
-- what lets a statement written in the `Iface` vocabulary be read at the
-- grading's objects without a coercion.
retᴵ : Category.Obj (𝒢ₚ 0ℓ) → Iface
retᴵ X = proj₁ X ⇿ proj₂ X

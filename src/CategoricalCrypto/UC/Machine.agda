{-# OPTIONS --safe --without-K --guardedness #-}

-- The intended model: the UC layer over the machine layer.
--
-- `⟦_⟧ᴵ` is a bijection between `Iface` and `𝒢ₚ`'s objects, with a definitional
-- retraction `retᴵ`, so a hom of `𝒢ₚ` at any objects IS a `Proc` and either
-- vocabulary reads the other with no coercion.  The ancilla action is taken
-- on 𝒢's own objects, where it is free: re-presenting it on `Iface` objects is
-- a measured >1500 s wall (`docs/protocol-rewrite.md`'s "A `Monoidal` law
-- costs ~470 s to RECEIVE and nothing to PLUG").
--
-- The verdict interface is TICKED (`Neg Ωᴵ = ⊤`).  A machine is reactive, so a
-- closed composite at a verdict interface with an empty negative side could
-- never be activated and would observe nothing; the tick is the environment's
-- single activation, and the observation is then layer 1's own closed run at
-- the one-ask strategy.
--
-- The relays `T₁ᴵ`/`subᴵ` and the ancilla reassociators are direct — no
-- coherence morphism, no trace — which keeps a query bound about them readable
-- (`UC.QueryBound`); `UC.Machine.Dictionary` relates them to the tensor's action.

open import Categories.Category

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂) renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Data.Unit.Base
import Data.Unit.Polymorphic.Base as PolyUnit
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Space ℚ-ordered
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Processes on interfaces

-- A `𝒢ₚ`-hom read at interfaces: `Machine (A⁺ + B⁻) (A⁻ + B⁺)`, a process that
-- answers queries from above and issues queries below.  Spelled with `_⊎_`
-- rather than as `𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` (definitionally the same): an
-- implicit inferred from the hom form is `𝒢ₚ`'s object sum, under which sits
-- the δ-unfolded Mealy category record, and every term mentioning it carries
-- that copy (`UC.Machine.Monitor.Agree`: 2.4 → 1.2 GiB residency).
Proc : Iface → Iface → Set₁
Proc A B = MC.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)

-- A consumer passes every object implicit of `𝒫ᴵ` explicitly.  Left to
-- inference, each asks Agda to invert `Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)`
-- for the pair `(Pos A , Neg B)`, and `_⊎_` is not a constructor: the resulting
-- normalization of `𝒢ₚ` — which carries the whole Elgot instance under it —
-- exhausts a 10 GiB heap.
--
-- `FullSubCategory (𝒢ₚ 0ℓ) ⟦_⟧ᴵ` field for field, except that `_⇒_` and `_≈_`
-- are spelled at the interface sums, for the reason given at `Proc`.
𝒫ᴵ : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝒫ᴵ = record
  { Obj       = Iface
  ; _⇒_       = Proc
  ; _≈_       = λ {A} {B} → MS._≈ᴹ_ {Pos A ⊎ Neg B} {Neg A ⊎ Pos B}
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
  where module 𝒢 = Category (𝒢ₚ 0ℓ)

-- A definitional inverse of `⟦_⟧ᴵ`: `Iface` and `𝒢ₚ`'s objects are both eta
-- records.
retᴵ : Category.Obj (𝒢ₚ 0ℓ) → Iface
retᴵ X = proj₁ X ⇿ proj₂ X

-- The base category's tensor unit, which is also the state object of every
-- stateless machine.
⊤ᵛ : Set
⊤ᵛ = PolyUnit.⊤

-- The step is a named function so that a statement about it can be made
-- without projecting one out of a `Proc` (`UC.QueryBound`).
wireStep : {A B : Iface} → (Pos A → Pos B) → (Neg B → Neg A)
         → ⊤ᵛ × (Pos A ⊎ Neg B) → Dₚ (⊤ᵛ × (Neg A ⊎ Pos B))
wireStep up down (s , inj₁ p) = returnₚ (s , inj₂ (up p))
wireStep up down (s , inj₂ n) = returnₚ (s , inj₁ (down n))

wireᴹ : {A B : Iface} → (Pos A → Pos B) → (Neg B → Neg A) → Proc A B
wireᴹ up down = MC.mk MC.Iˢ (wireStep up down)

initˢ : (S : Set) → S → MC.State
initˢ S s = record { obj = S ; point = λ _ → returnₚ s }

------------------------------------------------------------------------
-- The observation

Ωᴵ : Iface
Ωᴵ = Bool ⇿ ⊤

⟦_⟧ᴼ : Proc unitᴵ Ωᴵ → Dₚ Bool
⟦ M ⟧ᴼ = runᴹ M (ask tt out)

-- Compares both verdict masses (`ProbabilisticLogic.Dp.Advantage`'s header).
Approximationᴹ : Approximation (Dₚ Bool) ℚ-ordered 0ℓ
Approximationᴹ = record
  { _≈[_]_    = _≈ₚ[_]_
  ; ≈[]-refl  = ≈ₚ[]-refl
  ; ≈[]-sym   = ≈ₚ[]-sym
  ; ≈[]-trans = ≈ₚ[]-trans
  ; ≈[]-mono  = ≈ₚ[]-mono
  }

spaceᴹ : ApproxSpace 0ℓ 0ℓ
spaceᴹ = record { Carrier = Dₚ Bool ; approx = Approximationᴹ }

-- The readout is homed on `𝒢ₚ`, not on `𝒫ᴵ`, because that is where the
-- grading is; the hom equality is read at slack 0 (`UC.Machine.Run`).
QEvaluationᴹ : QEvaluation (𝒢ₚ 0ℓ) 0ℓ 0ℓ
QEvaluationᴹ = record
  { J = ⟦ unitᴵ ⟧ᴵ ; Ω = ⟦ Ωᴵ ⟧ᴵ ; X = spaceᴹ
  ; eval₀ = record
      { to = ⟦_⟧ᴼ ; cong = λ eq → ≈ₚ⇒≈ₚ[0] (runᴹ-resp-≈ᴹ eq (ask tt out)) }
  }

Evaluationᴹ : Evaluation (𝒢ₚ 0ℓ) 0ℓ 0ℓ
Evaluationᴹ = qual₊ ℚ-refinement QEvaluationᴹ

------------------------------------------------------------------------
-- The ancilla relays, as data

outT : {Nʸ Pʸ N P : Set} → N ⊎ P → (Nʸ ⊎ N) ⊎ (Pʸ ⊎ P)
outT (inj₁ a) = inj₁ (inj₂ a)
outT (inj₂ b) = inj₂ (inj₂ b)

T₁ᴵ : (Y : Iface) {A B : Iface} → Proc A B → Proc (Y ⊗ᴵ A) (Y ⊗ᴵ B)
T₁ᴵ Y {A} {B} f = MC.mk (MC.state f) stepT
  where
  stepT : MC.St f × ((Pos Y ⊎ Pos A) ⊎ (Neg Y ⊎ Neg B))
        → Dₚ (MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)))
  stepT (s , inj₁ (inj₁ y)) = returnₚ (s , inj₂ (inj₁ y))
  stepT (s , inj₁ (inj₂ a)) = mapₚ (map₂ outT) (MC.step f (s , inj₁ a))
  stepT (s , inj₂ (inj₁ y)) = returnₚ (s , inj₁ (inj₁ y))
  stepT (s , inj₂ (inj₂ b)) = mapₚ (map₂ outT) (MC.step f (s , inj₂ b))

subᴵ : {X Y A : Iface} → Proc X Y → Proc (X ⊗ᴵ A) (Y ⊗ᴵ A)
subᴵ {X} {Y} {A} s = MC.mk (MC.state s) stepS
  where
  outS : Neg X ⊎ Pos Y → (Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)
  outS (inj₁ x) = inj₁ (inj₁ x)
  outS (inj₂ y) = inj₂ (inj₁ y)

  stepS : MC.St s × ((Pos X ⊎ Pos A) ⊎ (Neg Y ⊎ Neg A))
        → Dₚ (MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)))
  stepS (t , inj₁ (inj₁ x)) = mapₚ (map₂ outS) (MC.step s (t , inj₁ x))
  stepS (t , inj₁ (inj₂ a)) = returnₚ (t , inj₂ (inj₂ a))
  stepS (t , inj₂ (inj₁ y)) = mapₚ (map₂ outS) (MC.step s (t , inj₂ y))
  stepS (t , inj₂ (inj₂ a)) = returnₚ (t , inj₁ (inj₂ a))

a⇐ᴵ : {X Y A : Iface} → Proc (X ⊗ᴵ (Y ⊗ᴵ A)) ((X ⊗ᴵ Y) ⊗ᴵ A)
a⇐ᴵ = wireᴹ ⊎assocˡ ⊎assocʳ

a⇒ᴵ : {X Y A : Iface} → Proc ((X ⊗ᴵ Y) ⊗ᴵ A) (X ⊗ᴵ (Y ⊗ᴵ A))
a⇒ᴵ = wireᴹ ⊎assocʳ ⊎assocˡ

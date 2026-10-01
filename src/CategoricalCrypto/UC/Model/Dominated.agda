{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Machine.Bridge.ContextDominated` at SEAL objects, and its proof.
--
-- The bridge quantifies its ancilla over `Iface` and `UC.Family._≈ℰ[_]_` over
-- objects of the seal; `UC.Model.Seal.objᵒ` is a section of `ifaceᵒ`, so the
-- two quantifiers agree and `dominatedᵒ` is `dominated` read at `objᵒ X`.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Dominated
open import CategoricalCrypto.UC.Machine.Grading
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Slide
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound using (QB; certified⇒QB; qb-resp-≈; qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws
open import CategoricalCrypto.UC.QueryBound.Object

module CategoricalCrypto.UC.Model.Dominated where

private
  module G = MonoidalCategory 𝔾ᵒ
  module 𝒫 = Category 𝒫ᴵ

open GradedSubCat gradingᵒ

-- The seal's ancilla action, which is what the family layer's is, levelwise
-- (`UC.Family.Famᴹ`).
T₁ᵒ : (X : G.Obj) {A B : G.Obj} → A G.⇒ B → X G.⊗₀ A G.⇒ X G.⊗₀ B
T₁ᵒ X f = G._⊗₁_ (G.id {X}) f

------------------------------------------------------------------------
-- Crossing the seal

opaque
  unfolding 𝔾ᵒ sealᵒ

  -- What a context's test and closure CARRY is a `gradingᵒ` certificate, and
  -- the budget `dominated` charges its strategy is the machine layer's own.
  unqb-testᵒ : {P A B : Iface} {c : ℕ⁺} (X : G.Obj)
               {E : X G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ A) G.⇒ ifaceᵒ B}
             → Image forget c E → QB (value c) (untestᵒ X E)
  unqb-testᵒ {P} {A} {B} X ((_ , q) , e) =
    qb-resp-≈ e (qb-from-image (objᵒ X ⊗ᴵ (P ⊗ᴵ A)) B q)

  unqb-closᵒ : {A B : Iface} {c : ℕ⁺} (X : G.Obj)
               {m : ifaceᵒ A G.⇒ X G.⊗₀ ifaceᵒ B}
             → Image forget c m → QB (value c) (unclosᵒ X m)
  unqb-closᵒ {A} {B} X ((_ , q) , e) = qb-resp-≈ e (qb-from-image A (objᵒ X ⊗ᴵ B) q)

  -- The reading itself: an ancilla context of the seal, observed, IS the
  -- bridge's `ctxRun` at the retracted ancilla.  Composition crosses on the
  -- nose (`unprocᵒ-∘`'s reason), so the whole content is `T₁-⊗₁`.
  ctxRunᵒ : {P A B : Iface} (X : G.Obj)
            (E : X G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ)
            (m : 𝟘ᵒ G.⇒ X G.⊗₀ ifaceᵒ A) (f : Proc A (P ⊗ᴵ B))
          → Obs ((E G.∘ T₁ᵒ X (gradedᵒ f)) G.∘ m)
            ≈ₚ ctxRun (objᵒ X) (untestᵒ X E) (unclosᵒ X m) f
  ctxRunᵒ X E m f =
    runᴹ-resp-≈ᴹ (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (𝒫.Equiv.sym (T₁-⊗₁ f)))) (ask tt out)

------------------------------------------------------------------------
-- …and the statement at seal objects

private
  guard : {c c′ : ℕ⁺} {B : Iface} {P : Strat (Neg B) (Pos B) → Set}
        → ((d : Strat (Neg B) (Pos B)) → asks≤ (value (c · c′)) d → P d)
        → (d : Strat (Neg B) (Pos B)) → asks≤ (value c * (value c′ ⊔ 1)) d → P d
  guard {c} {c′} h d a = h d (subst (λ k → asks≤ k d) (cong (value c *_) (value-positive c′)) a)

-- `UC.Machine.Dominated.dominated` with its ancilla quantified over the
-- seal's objects and its rates read off `gradingᵒ`: the shape
-- `UC.Family._≈ℰ[_]_` presents at one level.  The hole is at the trivial grade
-- and the compared processes are closed, exactly as there.  At a positive
-- closure rate the machine layer's guarded allowance `scale c (positive c′)`
-- is the product of the two rates (`value-positive`).
dominatedᵒ :
    (B : Iface) (X : G.Obj)
    (E : X G.⊗₀ (𝟘ᵒ G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ X G.⊗₀ 𝟘ᵒ)
    {c c′ : ℕ⁺} → Image forget c E → Image forget c′ m
  → (u v : Proc unitᴵ B) (ε δ : ℚ) → 0ℚ ℚ.< δ
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (value (c · c′)) d
     → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
  → Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ u))) G.∘ m)
    ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ v))) G.∘ m)
dominatedᵒ B X E m {c} {c′} qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (ctxRunᵒ X E m (conjᴵ u)))
            (≈ₚ-sym _ _ (ctxRunᵒ X E m (conjᴵ v)))
            (dominated B (objᵒ X) (untestᵒ X E) (unclosᵒ X m)
                       (unqb-testᵒ X qE) (unqb-closᵒ X qm) u v ε δ 0<δ (guard {c} {c′} h))

------------------------------------------------------------------------
-- …and at a nontrivial grade

-- `dominatedᵒ` at a hole that is a real grade rather than `𝟘ᵒ`.
-- so a grade beside it is already inside the statement, and `ctxRunᵒ` crosses
-- the seal at an arbitrary grade.  What is in the way is the unitor `conjᴵ`
-- leaves in front of the process, and `UC.Machine.Slide.ctxRun-conj` cancels
-- it.  That unitor costs the test one activation, and `*-identityʳ` takes the
-- product back to the test's own rate, so the hypothesis is read at
-- `value (c · c′)` exactly as `dominatedᵒ`'s is.
dominatedᵍᵠ : {P B : Iface} (W : G.Obj)
              (E : W G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ W G.⊗₀ 𝟘ᵒ)
              {c c′ : ℕ⁺} → Image forget c E → Image forget c′ m
            → (u v : Proc unitᴵ (P ⊗ᴵ B)) (ε δ : ℚ) → 0ℚ ℚ.< δ
            → ((d : Strat (Neg (P ⊗ᴵ B)) (Pos (P ⊗ᴵ B))) → asks≤ (value (c · c′)) d
               → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
            → Obs ((E G.∘ T₁ᵒ W (gradedᵒ u)) G.∘ m)
              ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ W (gradedᵒ v)) G.∘ m)
dominatedᵍᵠ {P} {B} W E m {c} {c′} qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (open-hole u)) (≈ₚ-sym _ _ (open-hole v))
    (dominated (P ⊗ᴵ B) (objᵒ W) Eᶜ (unclosᵒ W m) qEᶜ (unqb-closᵒ W qm)
               u v ε δ 0<δ (guard {c} {c′} h))
  where
  Eᶜ : Proc (objᵒ W ⊗ᴵ (unitᴵ ⊗ᴵ (P ⊗ᴵ B))) Ωᴵ
  Eᶜ = untestᵒ W E 𝒫.∘ T₁ᴵ (objᵒ W) (λᴵ⇒ {P ⊗ᴵ B})

  qEᶜ : QB (value c) Eᶜ
  qEᶜ = subst (λ k → QB k Eᶜ) (*-identityʳ (value c))
          (qb-∘-category (objᵒ W ⊗ᴵ (unitᴵ ⊗ᴵ (P ⊗ᴵ B))) (objᵒ W ⊗ᴵ (P ⊗ᴵ B)) Ωᴵ
            (untestᵒ W E) (T₁ᴵ (objᵒ W) λᴵ⇒) (unqb-testᵒ W qE)
            (qb-T₁ᴵ (objᵒ W) (unitᴵ ⊗ᴵ (P ⊗ᴵ B)) (P ⊗ᴵ B) λᴵ⇒ qb-λᴵ⇒))

  open-hole : (x : Proc unitᴵ (P ⊗ᴵ B))
            → Obs ((E G.∘ T₁ᵒ W (gradedᵒ x)) G.∘ m)
              ≈ₚ ctxRun (objᵒ W) Eᶜ (unclosᵒ W m) (conjᴵ x)
  open-hole x = ctxRunᵒ W E m x
            ⟨≈⟩ ctxRun-conj (untestᵒ W E) (unclosᵒ W m) x

-- …at EVERY strategy instead of at every strategy of the context's budget,
-- which is the shape an exact run agreement has: the conclusion's error is
-- then independent of the budget, so no allowance arithmetic is spent
-- crossing.
dominatedᵍ : {P B : Iface} (W : G.Obj)
             (E : W G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ W G.⊗₀ 𝟘ᵒ)
             {c c′ : ℕ⁺} → Image forget c E → Image forget c′ m
           → (u v : Proc unitᴵ (P ⊗ᴵ B)) (ε δ : ℚ) → 0ℚ ℚ.< δ
           → ((d : Strat (Neg (P ⊗ᴵ B)) (Pos (P ⊗ᴵ B))) → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
           → Obs ((E G.∘ T₁ᵒ W (gradedᵒ u)) G.∘ m)
             ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ W (gradedᵒ v)) G.∘ m)
dominatedᵍ W E m {c} {c′} qE qm u v ε δ 0<δ h =
  dominatedᵍᵠ W E m {c} {c′} qE qm u v ε δ 0<δ (λ d _ → h d)

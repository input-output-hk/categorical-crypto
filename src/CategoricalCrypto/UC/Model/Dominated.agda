{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Machine.Bridge.ContextDominated` at SEAL objects, and its proof.
--
-- The bridge quantifies its ancilla over `Iface`; `UC.Family._≈ℰ[_]_` — hence
-- `UC.Model.Family`'s — quantifies over objects of the seal, and under the seal
-- `ifaceᵒ` is not known to be onto (`UC.Seam.Grounding`'s header records the
-- same asymmetry, `docs/end-to-end.md`'s continuation spec item 1 the
-- consequence).  It IS onto: `UC.Machine.retᴵ` inverts `⟦_⟧ᴵ` definitionally,
-- so `UC.Model.Seal.objᵒ` is a section and the two quantifiers agree.  Nothing
-- about the domination argument changes — `dominatedᵒ` is `dominated` read at
-- `objᵒ X` — and no statement is restricted to an image.
--
-- What the reading costs is the three coercions below plus one machine
-- equation: the seal's own action `id ⊗₁ _` against the relay `T₁ᴵ` the bridge
-- is written with, which is `UC.Machine.Dictionary.T₁-⊗₁` and nothing else.
-- The coercions are `p = p` under the seal and must be exported from inside it
-- (`UC.Model.Seal`'s third discipline), one per shape: the TYPE of a definition
-- in an `opaque` block is checked with the seal closed, and only its body sees
-- through.
--
-- The ancilla is the only quantifier that has to be general.  The grade, the
-- interfaces and the two compared processes come from the statement being read,
-- which is written at `Iface` — a concrete security theorem names its
-- interface — so nothing is gained by generalizing them and the coercions stay
-- small.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Unit.Base using (tt)

open import ProbabilisticLogic.Dp using (_≈ₚ_; ≈ₚ-sym)
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-resp)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat; asks≤; ask; out)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (conjᴵ; ctxRun)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁)
open import CategoricalCrypto.UC.Machine.Dominated using (dominated)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Object using (qb-to-image; qb-from-image)

module CategoricalCrypto.UC.Model.Dominated where

private
  module G = MonoidalCategory 𝔾ᵒ
  module 𝒫 = Category 𝒫ᴵ

-- The seal's ancilla action, which is what the family layer's is, levelwise
-- (`UC.Family.Famᴹ`).
T₁ᵒ : (X : G.Obj) {A B : G.Obj} → A G.⇒ B → X G.⊗₀ A G.⇒ X G.⊗₀ B
T₁ᵒ X f = G._⊗₁_ (G.id {X}) f

------------------------------------------------------------------------
-- Crossing the seal

opaque
  unfolding 𝔾ᵒ sealᵒ

  -- A query bound on a graded process, as the family layer's hom data asks for
  -- it (`UC.Model.Enrichment.qbᵒ` at the graded spelling of the codomain).
  qb-gradedᵒ : {A P B : Iface} {c : ℕ} {f : Proc A (P ⊗ᴵ B)}
             → QB c f → Budget.QB budgetᵒ c (gradedᵒ f)
  qb-gradedᵒ {A} {P} {B} = qb-to-image A (P ⊗ᴵ B)

  -- …and the two the other way: what a context's test and closure CARRY is a
  -- `budgetᵒ` certificate, and the budget `dominated` charges its strategy is
  -- the machine layer's own.
  unqb-testᵒ : {P A B : Iface} {c : ℕ} (X : G.Obj)
               {E : X G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ A) G.⇒ ifaceᵒ B}
             → Budget.QB budgetᵒ c E → QB c (untestᵒ X E)
  unqb-testᵒ {P} {A} {B} X = qb-from-image (objᵒ X ⊗ᴵ (P ⊗ᴵ A)) B

  unqb-closᵒ : {A B : Iface} {c : ℕ} (X : G.Obj)
               {m : ifaceᵒ A G.⇒ X G.⊗₀ ifaceᵒ B}
             → Budget.QB budgetᵒ c m → QB c (unclosᵒ X m)
  unqb-closᵒ {A} {B} X = qb-from-image A (objᵒ X ⊗ᴵ B)

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

-- `UC.Machine.Bridge.ContextDominated` with its ancilla quantified over the
-- seal's objects and its budgets read off `budgetᵒ`: the shape
-- `UC.Family._≈ℰ[_]_` presents at one level.  The hole is at the trivial grade
-- and the compared processes are closed, exactly as there.
ContextDominatedᵒ : Set₁
ContextDominatedᵒ =
    (B : Iface) (X : G.Obj)
    (E : X G.⊗₀ (𝟘ᵒ G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ X G.⊗₀ 𝟘ᵒ)
    {c c′ : ℕ} → Budget.QB budgetᵒ c E → Budget.QB budgetᵒ c′ m
  → (u v : Proc unitᴵ B) (ε δ : ℚ) → 0ℚ ℚ.< δ
  → ((d : Strat (Neg B) (Pos B)) → asks≤ (ctxBudget c c′) d
     → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
  → Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ u))) G.∘ m)
    ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ X (gradedᵒ (conjᴵ v))) G.∘ m)

dominatedᵒ : ContextDominatedᵒ
dominatedᵒ B X E m qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (ctxRunᵒ X E m (conjᴵ u)))
            (≈ₚ-sym _ _ (ctxRunᵒ X E m (conjᴵ v)))
            (dominated B (objᵒ X) (untestᵒ X E) (unclosᵒ X m)
                       (unqb-testᵒ X qE) (unqb-closᵒ X qm) u v ε δ 0<δ h)

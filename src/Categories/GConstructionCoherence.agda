{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `assoc'-coherence` lemma of the Int/G-construction, proven via the
-- APROP solver toolchain and transported into an arbitrary symmetric
-- monoidal category.
--
-- The free-level proof (`coh`) chains:
--   * `Decomp.lhs-decomp` / `Decomp.rhs-decomp` — free decompositions of
--     the two ~50-morphism sides into three one-box segments each
--     (splitting front-end; small solver leaves only);
--   * `Wiring.segments` — the three segment-level naturality squares,
--     each a single-box solver obligation.
-- The 50-morphism equation is never solved whole.
--
-- `Transport.coherence` interprets the result in any SMC via the free
-- functor; its statement is definitionally GConstruction's
-- `assoc'-coherence` goal.
--------------------------------------------------------------------------------

-- STATUS (2026-06-10): COMPLETE.  The whole chain typechecks in ~2.5 min
-- (obligations ~30 s each) after fixing two call-pattern performance bugs —
-- see docs/smc-solver-performance.md ("the 8-atom wall: RESOLVED"):
--   * forcing must be routed through refl-checked equations (`force!`),
--     never `from-just`/inferred witnesses (slow elaborator path);
--   * instantiated types must be SPELLED as the consuming signature spells
--     them (Translation (APROPSignatureDec.sig gSigDec), not Translation gSig).
module Categories.GConstructionCoherence where

open import Level using (Level)

open import Categories.GConstructionCoherence.Terms
open import Categories.GConstructionCoherence.Wiring using (segments)
open import Categories.GConstructionCoherence.Decomp using (lhs-decomp; rhs-decomp)

-- The free-level coherence theorem.
coh : lhsᵗ ≈Term rhsᵗ
coh = ≈-Term-trans lhs-decomp
        (≈-Term-trans (≈-Term-sym segments) (≈-Term-sym rhs-decomp))

--------------------------------------------------------------------------------
-- Transport into an arbitrary symmetric monoidal category.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
import Categories.APROP.Hypergraph.Solver.Interpret as Interp

private module IM = Interp gSigDec

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ e⁺ e⁻ : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 8 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = a⁺ ; ⟦ 1F ⟧ᵖ₀ = a⁻ ; ⟦ 2F ⟧ᵖ₀ = b⁺ ; ⟦ 3F ⟧ᵖ₀ = b⁻
  ⟦ 4F ⟧ᵖ₀ = d⁺ ; ⟦ 5F ⟧ᵖ₀ = d⁻ ; ⟦ 6F ⟧ᵖ₀ = e⁺ ; ⟦ 7F ⟧ᵖ₀ = e⁻

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGens
    (f₀ : OI.⟦ A⁺ ⊗₀ B⁻ ⟧₀ C.⇒ OI.⟦ A⁻ ⊗₀ B⁺ ⟧₀)
    (g₀ : OI.⟦ B⁺ ⊗₀ D⁻ ⟧₀ C.⇒ OI.⟦ B⁻ ⊗₀ D⁺ ⟧₀)
    (h₀ : OI.⟦ D⁺ ⊗₀ E⁻ ⟧₀ C.⇒ OI.⟦ D⁻ ⊗₀ E⁺ ⟧₀)
    where

    ⟦_⟧ᵖ₁ : ∀ {x y} → GMor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
    ⟦ gf ⟧ᵖ₁ = f₀
    ⟦ gg ⟧ᵖ₁ = g₀
    ⟦ gh ⟧ᵖ₁ = h₀

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    -- The coherence equation in C (the two sides are definitionally the
    -- interpretations of lhsᵗ/rhsᵗ).
    coherence : ⟦ lhsᵗ ⟧₁ C.≈ ⟦ rhsᵗ ⟧₁
    coherence = Functor.F-resp-≈ freeFunctor coh

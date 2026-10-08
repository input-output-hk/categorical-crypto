{-# OPTIONS --safe --without-K #-}

-- Generator interpretations are typed by the object map before the finite
-- signature is fixed.

open import Data.Fin
import Data.Fin.Properties as Fin
open import Data.Nat
open import Data.Product
open import Data.Vec as Vec

open import Categories.APROP
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.Frontend.Core as Core
import Categories.APROP.Hypergraph.Solver.Frontend.Drive as Drive
import Categories.APROP.Hypergraph.Solver.Frontend.Rewrite as Rewrite
open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Solver.Frontend.FinSetup
  {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  {k : ℕ} (objects : Vec C.Obj k) where

open FreeMonoidalHelper Symm (Fin k) public using (ObjTerm)

private
  ⟦v⟧ = fromMC {v = Symm} C.monoidalCategory (λ ⦃ _ ⦄ → C.symmetric)
  ⟦obj⟧ = Vec.lookup objects

open FreeObjInterp Symm (Fin k) ⟦v⟧ ⟦obj⟧ public

module WithGen {n : ℕ}
  (generators : Vec (Σ[ s ∈ ObjTerm ] Σ[ t ∈ ObjTerm ] ⟦ s ⟧₀ C.⇒ ⟦ t ⟧₀) n) where

  private
    arity : Fin n → ObjTerm × ObjTerm
    arity i = let source , target , _ = Vec.lookup generators i in source , target

  open FinSig Fin._≟_ arity public using (dom; cod; gen; genElim; finSig)
  module S = APROP finSig

  private
    ⟦gen⟧ : ∀ {A B} → S.mor A B → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
    ⟦gen⟧ = genElim (λ i → proj₂ (proj₂ (Vec.lookup generators i)))

  open Core.Target finSig C ⟦obj⟧ ⟦gen⟧ public
    using (⟦_⟧₁; freeFunctor; module Tgt; solveH; Rule; module Rule; mkRule)

  module R = Rewrite.Rewrite finSig C ⟦obj⟧ ⟦gen⟧
  module Drv = Drive.Drive finSig C ⟦obj⟧ ⟦gen⟧

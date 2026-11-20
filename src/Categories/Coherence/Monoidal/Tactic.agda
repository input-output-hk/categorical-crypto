------------------------------------------------------------------------
-- A reflection frontend for the monoidal coherence solver.
--
--   solve-mor 𝒞 : proves `f ≈ g` in `MonoidalCategory 𝒞` whenever the
--   backend's decision procedure equates their wire diagrams
--   (coherence + naturality + interchange over opaque generators).

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Tactic where

open import Data.Bool
open import Data.Fin
open import Data.Fin.Reflection
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.QuotedDefinitions
open import Reflection.TCM.Syntax
open import Agda.Builtin.Reflection using (withReduceDefs; withExpandLast)
open import Reflection.Utils.Args
open import Reflection.Utils.Goal
open import Reflection.Utils.Metas using (metaFree)
open import Tactic.Solver.Core
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category
open import Categories.Category.Monoidal
import Categories.Coherence.Monoidal as Coh
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Tactic.Core
open import Categories.FreeMonoidal

private
  atomRef : EncodeEnv → ℕ → Term
  atomRef _ i = con (quote FreeMonoidalHelper.Mor.var)
    (con (quote FinSig.genS) (toTerm (fromℕ i) ⟨∷⟩ []) ⟨∷⟩ [])

  finish : EncodeEnv → Term → Term → List Term → List Term → Term
  finish env lhs rhs vars sig = def (quote Coh.MorSolve.solveMor!)
    ( 3 ⋯⟅∷⟆ EncodeEnv.R↓ env
    ⟨∷⟩ unknown ⟅∷⟆ `vec vars
    ⟨∷⟩ unknown ⟅∷⟆ `vec sig
    ⟨∷⟩ 2 ⋯⟅∷⟆ lhs ⟨∷⟩ rhs ⟨∷⟩ unknown ⟅∷⟆ [])

  morTheory : TwoLevelTheory
  morTheory = Parser.theory "solve-mor" atomRef finish

  splitEquationArgs : Args Term → Maybe (Args Term × Args Term)
  splitEquationArgs (x@(arg (arg-info visible _) _) ∷ y@(arg (arg-info visible _) _) ∷ []) =
    just ([] , x ∷ y ∷ [])
  splitEquationArgs (a ∷ as) = case splitEquationArgs as of λ where
    nothing → nothing
    (just (pre , operands)) → just (a ∷ pre , operands)
  splitEquationArgs [] = nothing

  open Parser using (`≈; _==_)

  -- Appending operands to a projection from a literal record can expose a
  -- different relation or a Pi. A projection from this variable stays neutral.
  neutralRelation : Term → Term → Bool
  neutralRelation (var i []) (def f as) =
    if f == `≈ then (case vArgs as of λ where
      (def u us ∷ []) → if u == quote MonoidalCategory.U then
        (case vArgs us of λ where
          (var j [] ∷ []) → i ≡ᵇ j
          _ → false)
        else false
      _ → false)
    else false
  neutralRelation _ _ = false

  -- `reduce` re-elaborates its arguments. On meta-free goals, expose only the
  -- relation prefix and retain the original operands. Speculation must roll
  -- back before falling back to the ordinary Pi walk and meta-blocking policy.
  exposeEquation : Term → Term → TC (Maybe Term)
  exposeEquation C@(var _ []) ty@(def f as) =
    if ((f == quote Setoid._≈_) ∨ (f == quote _[_≈_])) ∧ metaFree ty then
      (case splitEquationArgs as of λ where
        nothing → pure nothing
        (just (pre , operands)) → runSpeculative
          (catchTC (do
            r ← withExpandLast false (reduce (def f pre))
            case r of λ where
              (def g gs) → if neutralRelation C r ∧ metaFree r
                then pure (just (def g (gs ++ operands)) , true)
                else pure (nothing , false)
              _ → pure (nothing , false))
            (pure (nothing , false))))
    else pure nothing
  exposeEquation _ _ = pure nothing

solve-mor-macro : Term → Term → TC ⊤
solve-mor-macro 𝒞 hole = do
  𝒞' ← checkType 𝒞 (def (quote MonoidalCategory) (3 ⋯⟨∷⟩ []))
  ty ← inferType hole
  equation ← withReduceDefs (false , Parser.blocked) (exposeEquation 𝒞' ty)
  final ← withReduceDefs (false , Parser.blocked) (case equation of λ where
    nothing → underPisOpaque Parser.blocked 1024 ty (solveTwoLevelEquation morTheory 𝒞')
    (just eq) → solveTwoLevelEquation morTheory 𝒞' 0 eq)
  unify hole final

macro
  solve-mor : Term → Term → TC ⊤
  solve-mor = solve-mor-macro

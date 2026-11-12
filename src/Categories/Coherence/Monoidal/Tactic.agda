------------------------------------------------------------------------
-- A reflection frontend for the monoidal coherence solver.
--
--   solve-mor 𝒞 : proves `f ≈ g` in `MonoidalCategory 𝒞` whenever the
--   backend's decision procedure equates their wire diagrams
--   (coherence + naturality + interchange over opaque generators).

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Tactic where

open import Data.Fin
open import Data.Fin.Reflection
open import Data.List
open import Data.Nat
open import Data.Unit
open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.QuotedDefinitions
open import Reflection.TCM.Syntax
open import Tactic.Solver.Core

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

solve-mor-macro : Term → Term → TC ⊤
solve-mor-macro 𝒞 hole = do
  𝒞' ← checkType 𝒞 (def (quote MonoidalCategory) (3 ⋯⟨∷⟩ []))
  solveByTwoLevelTheory (Parser.theory "solve-mor" atomRef finish) 𝒞' hole

macro
  solve-mor : Term → Term → TC ⊤
  solve-mor = solve-mor-macro

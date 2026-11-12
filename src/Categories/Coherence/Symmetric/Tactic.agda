------------------------------------------------------------------------
-- Reflection frontend for symmetric-monoidal coherence over opaque boxes.
-- See Categories.Coherence.Symmetric for the explicit-signature interface.

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Symmetric.Tactic where

open import Data.Bool
open import Data.Fin
import Data.Fin.Properties as Fin
open import Data.Fin.Reflection
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product
open import Data.Unit
import Data.Vec as Vec
open import Function
open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.QuotedDefinitions
open import Reflection.TCM.Syntax
open import Reflection.Utils.Args
open import Reflection.Utils.Reduction
open import Tactic.Solver.Core

import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Symmetric
open import Categories.Coherence.Monoidal.Tactic.Core
import Categories.Coherence.Symmetric as Coh
open import Categories.FreeMonoidal
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism

private
  open Parser

  `η = quote NaturalTransformation.η
  `⇒ = quote NaturalIsomorphism.F⇒G
  `⇐ = quote NaturalIsomorphism.F⇐G
  `braiding = quote Braided.braiding
  `FX≅GX = quote NaturalIsomorphism.FX≅GX
  `braided-iso = quote Symmetric.braided-iso
  `σ = quote FreeMonoidalHelper.Mor.σ

  leaf2 : EncodeEnv → List Term → Term
  leaf2 _ (x ∷ y ∷ []) = con `σ
    (4 ⋯⟅∷⟆ x ⟅∷⟆ y ⟅∷⟆ iArg (con (quote v≤v) []) ∷ [])
  leaf2 _ _ = unknown

  braidLeaf : Term → TC (Maybe TwoLevelOccurrence)
  braidLeaf p = do
    p′ ← whnfIfReducible p
    case p′ of λ where
      (con c as) → if c == `pair then (case takeLast 2 (vArgs as) of λ where
        (just (x Vec.∷ y Vec.∷ Vec.[])) → pure (just (record
          { indices = x ∷ y ∷ []
          ; operands = []
          ; encode = λ env is _ → leaf2 env is }))
        _ → pure nothing) else pure nothing
      _ → pure nothing

  isBraiding : Args Term → TC Bool
  isBraiding as = do
    inner ← innerDef as
    pure (case inner of λ where
      (just (g , _)) → g == `braiding
      _ → false)

  ηOcc : Args Term → TC (Maybe TwoLevelOccurrence)
  ηOcc as = case takeLast 2 (vArgs as) of λ where
    (just (nt Vec.∷ p Vec.∷ Vec.[])) → do
      nt′ ← whnfIfReducible nt
      case nt′ of λ where
        (def g gas) → if g == `⇒ then (do
          yes ← isBraiding gas
          if yes then braidLeaf p else pure nothing) else pure nothing
        _ → pure nothing
    _ → pure nothing

  isoBraid : Bool → Args Term → TC (Maybe TwoLevelOccurrence)
  isoBraid backwards as = do
    inner ← innerDef as
    case inner of λ where
      (just (g , gas)) →
        if g == `braided-iso then
          hiddenIndexLeaf 2 (λ env is → leaf2 env (if backwards then reverse is else is)) gas
        else if (g == `FX≅GX) ∧ not backwards then (do
          yes ← isBraiding gas
          if yes then (case takeLast 1 (hArgs gas) of λ where
            (just (p Vec.∷ Vec.[])) → braidLeaf p
            _ → pure nothing) else pure nothing)
        else pure nothing
      _ → pure nothing

  fromOcc toOcc : Args Term → TC (Maybe TwoLevelOccurrence)
  fromOcc as = do
    nothing ← isoOcc `λ⇒ `ρ⇒ `α⇒ as
      where (just occ) → pure (just occ)
    isoBraid false as
  toOcc as = do
    nothing ← isoOcc `λ⇐ `ρ⇐ `α⇐ as
      where (just occ) → pure (just occ)
    isoBraid true as

  atomRef : EncodeEnv → ℕ → Term
  atomRef _ i = con `var
    (def (quote FinSig.gen)
      (def (quote Fin._≟_) [] ⟨∷⟩ unknown ⟨∷⟩ toTerm (fromℕ i) ⟨∷⟩ []) ⟨∷⟩ [])

  encSig : EncodeEnv → Term → List Term → Term
  encSig _ b (x ∷ y ∷ []) = x `, (y `, b)
  encSig _ _ _ = unknown

  finish : EncodeEnv → Term → Term → List Term → List Term → Term
  finish env lhs rhs vars sig = def (quote Coh.Solver.solveH!)
    (3 ⋯⟅∷⟆ EncodeEnv.R↓ env ⟨∷⟩ 2 ⋯⟅∷⟆ `vec vars ⟨∷⟩ `vec sig
      ⟨∷⟩ 2 ⋯⟅∷⟆ lhs ⟨∷⟩ rhs ⟨∷⟩ unknown ⟅∷⟆ [])

  morTheory : TwoLevelTheory
  morTheory = record (theory "solve-smc" atomRef finish)
    { operators = mkOp `η ηOcc ∷ operators fromOcc toOcc
    ; blockedNames = `⇒ ∷ `⇐ ∷ `braiding ∷ `FX≅GX ∷ `braided-iso ∷ blocked
    ; encodeSig = encSig
    }

solve-smc-macro : Term → Term → TC ⊤
solve-smc-macro Cˢ hole = do
  Cˢ′ ← checkType Cˢ (def (quote SymmetricMonoidalCategory) (3 ⋯⟨∷⟩ []))
  solveByTwoLevelTheory morTheory Cˢ′ hole

macro
  solve-smc : Term → Term → TC ⊤
  solve-smc = solve-smc-macro

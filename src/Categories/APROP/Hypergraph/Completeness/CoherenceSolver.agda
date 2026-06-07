{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Use `Categories.MonoidalCoherence.Solver.solveM` (mechanised Mac Lane
-- coherence: parallel structural morphisms in a free monoidal category are
-- propositionally equal, lifted to the target via the freely-induced
-- functor) to discharge structural-morphism equations.  A thin shim
-- exposing a couple of helpers.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.CoherenceSolver (sig : APROPSignature) where

open APROP sig

open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Categories.Category using (Category)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.MonoidalCoherence using (module Solver)

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Category.Monoidal using (Monoidal)
open Monoidal Monoidal-FreeMonoidal using (associator; unitorˡ; unitorʳ)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- Sanity check: `solveM` instantiated at FreeMonoidal with 3 atoms.

module 3-atoms (a b c : X) where
  vars : Vec ObjTerm 3
  vars = (Var a) ∷ (Var b) ∷ (Var c) ∷ []

  open Solver record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }
              {n = 3} vars
    using (solveM)
    renaming (HomTerm to FreeHomTerm; α⇒ to α⇒'; α⇐ to α⇐';
              λ⇒ to λ⇒'; λ⇐ to λ⇐'; ρ⇒ to ρ⇒'; ρ⇐ to ρ⇐';
              id to id'; _∘_ to _∘'_; _⊗₁_ to _⊗₁'_;
              ObjTerm to FreeObjTerm; unit to unit'; _⊗₀_ to _⊗₀'_;
              Var to Var')
    public

  test-α-iso :
    -- α⇒ ∘ α⇐ ≈ id at (Var a ⊗₀ Var b) ⊗₀ Var c
    α⇒ {A = Var a} {Var b} {Var c} ∘ α⇐ {A = Var a} {Var b} {Var c} ≈Term id
  test-α-iso = solveM
                 (α⇒' {A = Var' zero} {Var' (suc zero)} {Var' (suc (suc zero))}
                    ∘' α⇐')
                 id'

  test-pentagon-instance :
    -- pentagon equation at concrete types
    let X = Var a; Y = Var b; Z = Var c
    in  α⇒ {X} {Y} {Z ⊗₀ X} ∘ α⇒ {X ⊗₀ Y} {Z} {X}
      ≈Term id ⊗₁ α⇒ {Y} {Z} {X} ∘ α⇒ {X} {Y ⊗₀ Z} {X} ∘ α⇒ {X} {Y} {Z} ⊗₁ id
  test-pentagon-instance = solveM
    (α⇒' {A = Var' zero} {Var' (suc zero)} {Var' (suc (suc zero)) ⊗₀' Var' zero}
       ∘' α⇒' {A = Var' zero ⊗₀' Var' (suc zero)} {Var' (suc (suc zero))} {Var' zero})
    (id' ⊗₁' α⇒' {A = Var' (suc zero)} {Var' (suc (suc zero))} {Var' zero}
       ∘' α⇒' {A = Var' zero} {Var' (suc zero) ⊗₀' Var' (suc (suc zero))} {Var' zero}
       ∘' α⇒' {A = Var' zero} {Var' (suc zero)} {Var' (suc (suc zero))} ⊗₁' id')

--------------------------------------------------------------------------------
-- Solver-discharged structural lemmas, generic in the ObjTerm parameters
-- (passed as a Vec at instantiation; `solveM` settles each in one call).

module 2-objs (X Y : ObjTerm) where
  vars : Vec ObjTerm 2
  vars = X ∷ Y ∷ []

  open Solver record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }
              {n = 2} vars
    using (solveM)
    renaming (α⇒ to α⇒'; α⇐ to α⇐';
              λ⇒ to λ⇒'; λ⇐ to λ⇐'; ρ⇒ to ρ⇒'; ρ⇐ to ρ⇐';
              id to id'; _∘_ to _∘'_; _⊗₁_ to _⊗₁'_;
              unit to unit'; _⊗₀_ to _⊗₀'_; Var to Var')
    public

  -- α⇒_{unit, X, Y} ∘ (λ⇐_X ⊗ id_Y) ≈ λ⇐_{X⊗Y}.
  α⇒-λ⇐-collapse
    : α⇒ {unit} {X} {Y} ∘ (λ⇐ {X} ⊗₁ id {Y}) ≈Term λ⇐ {X ⊗₀ Y}
  α⇒-λ⇐-collapse =
    solveM
      (α⇒' {A = unit'} {Var' zero} {Var' (suc zero)} ∘' (λ⇐' ⊗₁' id'))
      (λ⇐' {A = Var' zero ⊗₀' Var' (suc zero)})

module 4-objs (X Y Z W : ObjTerm) where
  vars : Vec ObjTerm 4
  vars = X ∷ Y ∷ Z ∷ W ∷ []

  open Solver record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }
              {n = 4} vars
    using (solveM)
    renaming (α⇒ to α⇒'; α⇐ to α⇐';
              λ⇒ to λ⇒'; λ⇐ to λ⇐'; ρ⇒ to ρ⇒'; ρ⇐ to ρ⇐';
              id to id'; _∘_ to _∘'_; _⊗₁_ to _⊗₁'_;
              unit to unit'; _⊗₀_ to _⊗₀'_; Var to Var')
    public

  private
    X' = Var' zero
    Y' = Var' (suc zero)
    Z' = Var' (suc (suc zero))
    W' = Var' (suc (suc (suc zero)))

  -- Pentagon for α⇒_{X⊗Y, Z, W}.
  pentagon-rewrite
    : α⇒ {X ⊗₀ Y} {Z} {W}
    ≈Term α⇐ {X} {Y} {Z ⊗₀ W}
          ∘ id {X} ⊗₁ α⇒ {Y} {Z} {W}
          ∘ α⇒ {X} {Y ⊗₀ Z} {W}
          ∘ α⇒ {X} {Y} {Z} ⊗₁ id {W}
  pentagon-rewrite =
    solveM
      (α⇒' {A = X' ⊗₀' Y'} {Z'} {W'})
      (α⇐' {A = X'} {Y'} {Z' ⊗₀' W'}
       ∘' id' ⊗₁' α⇒' {A = Y'} {Z'} {W'}
       ∘' α⇒' {A = X'} {Y' ⊗₀' Z'} {W'}
       ∘' α⇒' {A = X'} {Y'} {Z'} ⊗₁' id')

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Worked example: commutative Frobenius algebra signature (per
-- TensorRocq §5). This file only defines the signature and builds a
-- few sample terms -- equational reasoning is deferred to later phases.
--------------------------------------------------------------------------------

module Categories.APROP.Examples.Frobenius where

open import Categories.APROP

-- Single atom `A`. The full signature is over `ObjTerm` built from it.
data Atom : Set where
  A : Atom

open FreeMonoidalHelper Symm Atom using (ObjTerm; unit; _⊗₀_; Var)

a : ObjTerm
a = Var A

-- Generators of a commutative Frobenius algebra on `a`:
-- η : I → a        unit
-- μ : a ⊗ a → a    multiplication
-- ε : a → I        counit
-- δ : a → a ⊗ a    comultiplication
data Gen : ObjTerm → ObjTerm → Set where
  η : Gen unit a
  μ : Gen (a ⊗₀ a) a
  ε : Gen a unit
  δ : Gen a (a ⊗₀ a)

FrobSig : APROPSignature
FrobSig = record { X = Atom ; mor = Gen }

-- `APROP FrobSig` re-exports `ObjTerm, unit, _⊗₀_, Var` via
-- `FreeMonoidal`; they are the same as the ones opened at the top, but
-- Agda still flags the overload. Hide them here.
open APROP FrobSig hiding (ObjTerm; unit; _⊗₀_; Var)

-- Sample APROP terms. These just exercise term-building; axioms and
-- normalisation come in later phases.

-- Left-biased triple multiplication.
μ³ : HomTerm ((a ⊗₀ a) ⊗₀ a) a
μ³ = Agen μ ∘ (Agen μ ⊗₁ id)

-- Right-biased triple multiplication, reassociated.
μ³' : HomTerm ((a ⊗₀ a) ⊗₀ a) a
μ³' = Agen μ ∘ (id ⊗₁ Agen μ) ∘ α⇒

-- Swap the two inputs of the multiplication (uses the braiding σ).
μ-swap : HomTerm (a ⊗₀ a) a
μ-swap = Agen μ ∘ σ

-- "Frobenius snake": δ then μ, with a braid in between.
snake : HomTerm a a
snake = Agen μ ∘ σ ∘ Agen δ

-- Two-legged zigzag using unit and counit.
zigzag : HomTerm a a
zigzag = ρ⇒ ∘ (id ⊗₁ Agen ε) ∘ Agen δ

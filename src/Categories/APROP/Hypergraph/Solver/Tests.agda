{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Smoke tests for `findIso`, threaded through `completeness-full`.
--
-- Each test is of the form
--
--   test : f ≈Term g
--   test = completeness-full (from-just (findIso ⟪ f ⟫ ⟪ g ⟫))
--
-- which compels `findIso` to actually reduce to `just _` at type-check
-- time and routes the resulting hypergraph iso through the inductive
-- `decode-rel-resp-≅ᴴ-full` dispatcher to a syntactic `≈Term` equation.
--
-- `⟪_⟫` is imported from `Translation` (the *pruned* translation).
-- Under pruning, `⟪ id ∘ Agen f ⟫` and `⟪ Agen f ⟫` have matching
-- vertex counts, so `findIso` succeeds on all 18 equation-shaped
-- `_≈Term_` constructors below.
--
-- `completeness-full` is now stated against `Translation.⟪_⟫`, so the
-- two pieces compose directly.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Tests where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (from-just)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

--------------------------------------------------------------------------------
-- Atom alphabet.

X : Set
X = Fin 3

open FreeMonoidalHelper Symm X using (ObjTerm; Var)

private
  -- Shorthand for the three atoms.
  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

--------------------------------------------------------------------------------
-- Generator data type. Three constructors at distinct (dom, cod) — Agda
-- index unification rules out the cross cases automatically, so
-- `_≟-MyMor_` only needs to handle the diagonal.

data MyMor : ObjTerm → ObjTerm → Set where
  f : MyMor a₀ a₁
  g : MyMor a₁ a₂
  h : MyMor a₂ a₀

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
f ≟-MyMor f = yes refl
g ≟-MyMor g = yes refl
h ≟-MyMor h = yes refl

--------------------------------------------------------------------------------
-- Build the signature.

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record
  { sig     = mySig
  ; _≟X_    = _≟F_
  ; _≟-mor_ = _≟-MyMor_
  }

--------------------------------------------------------------------------------
-- Bring in the term language, the solver, and the completeness theorem.

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open import Categories.APROP.Hypergraph.CompletenessFull mySigDec
  using (completeness-full)
open APROP mySig

--------------------------------------------------------------------------------
-- Tests for each equation-shaped `_≈Term_` constructor.

test-idˡ : id ∘ Agen f ≈Term Agen f
test-idˡ = completeness-full (from-just (findIso ⟪ id ∘ Agen f ⟫ ⟪ Agen f ⟫))

test-idʳ : Agen f ∘ id ≈Term Agen f
test-idʳ = completeness-full (from-just (findIso ⟪ Agen f ∘ id ⟫ ⟪ Agen f ⟫))

test-assoc : (Agen h ∘ Agen g) ∘ Agen f ≈Term Agen h ∘ (Agen g ∘ Agen f)
test-assoc = completeness-full
  (from-just (findIso ⟪ (Agen h ∘ Agen g) ∘ Agen f ⟫
                      ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫))

test-≈-refl : Agen f ≈Term Agen f
test-≈-refl = completeness-full (from-just (findIso ⟪ Agen f ⟫ ⟪ Agen f ⟫))

test-id⊗id : id {a₀} ⊗₁ id {a₁} ≈Term id {a₀ ⊗₀ a₁}
test-id⊗id = completeness-full
  (from-just (findIso ⟪ id {a₀} ⊗₁ id {a₁} ⟫ ⟪ id {a₀ ⊗₀ a₁} ⟫))

test-⊗-∘-dist
  : (Agen g ∘ Agen f) ⊗₁ (Agen f ∘ Agen h)
  ≈Term Agen g ⊗₁ Agen f ∘ Agen f ⊗₁ Agen h
test-⊗-∘-dist = completeness-full (from-just (findIso
  ⟪ (Agen g ∘ Agen f) ⊗₁ (Agen f ∘ Agen h) ⟫
  ⟪ Agen g ⊗₁ Agen f ∘ Agen f ⊗₁ Agen h ⟫))

test-λ⇐∘λ⇒ : λ⇐ ∘ λ⇒ {a₀} ≈Term id {unit ⊗₀ a₀}
test-λ⇐∘λ⇒ = completeness-full
  (from-just (findIso ⟪ λ⇐ ∘ λ⇒ {a₀} ⟫ ⟪ id {unit ⊗₀ a₀} ⟫))

test-λ⇒∘λ⇐ : λ⇒ ∘ λ⇐ {a₀} ≈Term id {a₀}
test-λ⇒∘λ⇐ = completeness-full
  (from-just (findIso ⟪ λ⇒ ∘ λ⇐ {a₀} ⟫ ⟪ id {a₀} ⟫))

test-ρ⇐∘ρ⇒ : ρ⇐ ∘ ρ⇒ {a₀} ≈Term id {a₀ ⊗₀ unit}
test-ρ⇐∘ρ⇒ = completeness-full
  (from-just (findIso ⟪ ρ⇐ ∘ ρ⇒ {a₀} ⟫ ⟪ id {a₀ ⊗₀ unit} ⟫))

test-ρ⇒∘ρ⇐ : ρ⇒ ∘ ρ⇐ {a₀} ≈Term id {a₀}
test-ρ⇒∘ρ⇐ = completeness-full
  (from-just (findIso ⟪ ρ⇒ ∘ ρ⇐ {a₀} ⟫ ⟪ id {a₀} ⟫))

test-α⇐∘α⇒ : α⇐ ∘ α⇒ {a₀} {a₁} {a₂} ≈Term id {(a₀ ⊗₀ a₁) ⊗₀ a₂}
test-α⇐∘α⇒ = completeness-full (from-just (findIso
  ⟪ α⇐ ∘ α⇒ {a₀} {a₁} {a₂} ⟫ ⟪ id {(a₀ ⊗₀ a₁) ⊗₀ a₂} ⟫))

test-α⇒∘α⇐ : α⇒ ∘ α⇐ {a₀} {a₁} {a₂} ≈Term id {a₀ ⊗₀ (a₁ ⊗₀ a₂)}
test-α⇒∘α⇐ = completeness-full (from-just (findIso
  ⟪ α⇒ ∘ α⇐ {a₀} {a₁} {a₂} ⟫ ⟪ id {a₀ ⊗₀ (a₁ ⊗₀ a₂)} ⟫))

test-λ⇒∘id⊗f : λ⇒ ∘ (id {unit} ⊗₁ Agen f) ≈Term Agen f ∘ λ⇒
test-λ⇒∘id⊗f = completeness-full (from-just (findIso
  ⟪ λ⇒ ∘ (id {unit} ⊗₁ Agen f) ⟫ ⟪ Agen f ∘ λ⇒ ⟫))

test-ρ⇒∘f⊗id : ρ⇒ ∘ (Agen f ⊗₁ id {unit}) ≈Term Agen f ∘ ρ⇒
test-ρ⇒∘f⊗id = completeness-full (from-just (findIso
  ⟪ ρ⇒ ∘ (Agen f ⊗₁ id {unit}) ⟫ ⟪ Agen f ∘ ρ⇒ ⟫))

test-α-comm
  : α⇒ ∘ ((Agen f ⊗₁ Agen g) ⊗₁ Agen h)
  ≈Term (Agen f ⊗₁ (Agen g ⊗₁ Agen h)) ∘ α⇒
test-α-comm = completeness-full (from-just (findIso
  ⟪ α⇒ ∘ ((Agen f ⊗₁ Agen g) ⊗₁ Agen h) ⟫
  ⟪ (Agen f ⊗₁ (Agen g ⊗₁ Agen h)) ∘ α⇒ ⟫))

test-triangle
  : id {a₀} ⊗₁ λ⇒ {a₁} ∘ α⇒ {a₀} {unit} {a₁}
  ≈Term ρ⇒ {a₀} ⊗₁ id {a₁}
test-triangle = completeness-full (from-just (findIso
  ⟪ id {a₀} ⊗₁ λ⇒ {a₁} ∘ α⇒ {a₀} {unit} {a₁} ⟫
  ⟪ ρ⇒ {a₀} ⊗₁ id {a₁} ⟫))

test-pentagon
  : (id {a₀} ⊗₁ α⇒ {a₁} {a₂} {a₀})
       ∘ α⇒ {a₀} {a₁ ⊗₀ a₂} {a₀}
       ∘ (α⇒ {a₀} {a₁} {a₂} ⊗₁ id {a₀})
  ≈Term α⇒ {a₀} {a₁} {a₂ ⊗₀ a₀}
       ∘ α⇒ {a₀ ⊗₀ a₁} {a₂} {a₀}
test-pentagon = completeness-full (from-just (findIso
  ⟪ (id {a₀} ⊗₁ α⇒ {a₁} {a₂} {a₀})
       ∘ α⇒ {a₀} {a₁ ⊗₀ a₂} {a₀}
       ∘ (α⇒ {a₀} {a₁} {a₂} ⊗₁ id {a₀}) ⟫
  ⟪ α⇒ {a₀} {a₁} {a₂ ⊗₀ a₀}
       ∘ α⇒ {a₀ ⊗₀ a₁} {a₂} {a₀} ⟫))

test-σ∘σ : σ ∘ σ {a₀} {a₁} ≈Term id {a₀ ⊗₀ a₁}
test-σ∘σ = completeness-full
  (from-just (findIso ⟪ σ ∘ σ {a₀} {a₁} ⟫ ⟪ id {a₀ ⊗₀ a₁} ⟫))

test-σ∘[f⊗g] : σ ∘ (Agen f ⊗₁ Agen g) ≈Term (Agen g ⊗₁ Agen f) ∘ σ
test-σ∘[f⊗g] = completeness-full (from-just (findIso
  ⟪ σ ∘ (Agen f ⊗₁ Agen g) ⟫
  ⟪ (Agen g ⊗₁ Agen f) ∘ σ ⟫))

test-hexagon
  : id {a₁} ⊗₁ σ ∘ α⇒ {a₁} {a₀} {a₂} ∘ σ ⊗₁ id {a₂}
  ≈Term α⇒ {a₁} {a₂} {a₀} ∘ σ {a₀} {a₁ ⊗₀ a₂} ∘ α⇒ {a₀} {a₁} {a₂}
test-hexagon = completeness-full (from-just (findIso
  ⟪ id {a₁} ⊗₁ σ ∘ α⇒ {a₁} {a₀} {a₂} ∘ σ ⊗₁ id {a₂} ⟫
  ⟪ α⇒ {a₁} {a₂} {a₀} ∘ σ {a₀} {a₁ ⊗₀ a₂} ∘ α⇒ {a₀} {a₁} {a₂} ⟫))

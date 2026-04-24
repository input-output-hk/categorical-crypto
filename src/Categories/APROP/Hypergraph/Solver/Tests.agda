{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Smoke tests for `findIso`.
--
-- A concrete `APROPSignatureDec` instance with `X = Fin 3` and a custom
-- `MyMor` data type whose constructors all live at distinct `(domain,
-- codomain)` index pairs — this makes `_≟-MyMor_` a one-line case
-- analysis.
--
-- Each test is of the form
--
--   test : ⟪ lhs ⟫ ≅ᴴ ⟪ rhs ⟫
--   test = from-just (findIso ⟪ lhs ⟫ ⟪ rhs ⟫)
--
-- which compels `findIso` to actually reduce to `just _` at type-check
-- time. If the search or verification fails, the program does not
-- type-check.
--
-- We cover every *equation*-shaped constructor of `_≈Term_`. The four
-- inference rules — `∘-resp-≈`, `≈-Term-sym`, `≈-Term-trans`,
-- `⊗-resp-≈` — are skipped because they aren't single equations.
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
-- Bring in the term language and the solver.

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open APROP mySig

--------------------------------------------------------------------------------
-- Tests for each equation-shaped `_≈Term_` constructor.

test-idˡ : ⟪ id ∘ Agen f ⟫ ≅ᴴ ⟪ Agen f ⟫
test-idˡ = from-just (findIso ⟪ id ∘ Agen f ⟫ ⟪ Agen f ⟫)

test-idʳ : ⟪ Agen f ∘ id ⟫ ≅ᴴ ⟪ Agen f ⟫
test-idʳ = from-just (findIso ⟪ Agen f ∘ id ⟫ ⟪ Agen f ⟫)

test-assoc : ⟪ (Agen h ∘ Agen g) ∘ Agen f ⟫ ≅ᴴ ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫
test-assoc = from-just (findIso ⟪ (Agen h ∘ Agen g) ∘ Agen f ⟫
                                ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫)

test-≈-refl : ⟪ Agen f ⟫ ≅ᴴ ⟪ Agen f ⟫
test-≈-refl = from-just (findIso ⟪ Agen f ⟫ ⟪ Agen f ⟫)

test-id⊗id : ⟪ id {a₀} ⊗₁ id {a₁} ⟫ ≅ᴴ ⟪ id {a₀ ⊗₀ a₁} ⟫
test-id⊗id = from-just (findIso ⟪ id {a₀} ⊗₁ id {a₁} ⟫ ⟪ id {a₀ ⊗₀ a₁} ⟫)

test-⊗-∘-dist
  : ⟪ (Agen g ∘ Agen f) ⊗₁ (Agen f ∘ Agen h) ⟫
  ≅ᴴ ⟪ Agen g ⊗₁ Agen f ∘ Agen f ⊗₁ Agen h ⟫
test-⊗-∘-dist = from-just (findIso
  ⟪ (Agen g ∘ Agen f) ⊗₁ (Agen f ∘ Agen h) ⟫
  ⟪ Agen g ⊗₁ Agen f ∘ Agen f ⊗₁ Agen h ⟫)

test-λ⇐∘λ⇒ : ⟪ λ⇐ ∘ λ⇒ {a₀} ⟫ ≅ᴴ ⟪ id {unit ⊗₀ a₀} ⟫
test-λ⇐∘λ⇒ = from-just (findIso ⟪ λ⇐ ∘ λ⇒ {a₀} ⟫ ⟪ id {unit ⊗₀ a₀} ⟫)

test-λ⇒∘λ⇐ : ⟪ λ⇒ ∘ λ⇐ {a₀} ⟫ ≅ᴴ ⟪ id {a₀} ⟫
test-λ⇒∘λ⇐ = from-just (findIso ⟪ λ⇒ ∘ λ⇐ {a₀} ⟫ ⟪ id {a₀} ⟫)

test-ρ⇐∘ρ⇒ : ⟪ ρ⇐ ∘ ρ⇒ {a₀} ⟫ ≅ᴴ ⟪ id {a₀ ⊗₀ unit} ⟫
test-ρ⇐∘ρ⇒ = from-just (findIso ⟪ ρ⇐ ∘ ρ⇒ {a₀} ⟫ ⟪ id {a₀ ⊗₀ unit} ⟫)

test-ρ⇒∘ρ⇐ : ⟪ ρ⇒ ∘ ρ⇐ {a₀} ⟫ ≅ᴴ ⟪ id {a₀} ⟫
test-ρ⇒∘ρ⇐ = from-just (findIso ⟪ ρ⇒ ∘ ρ⇐ {a₀} ⟫ ⟪ id {a₀} ⟫)

test-α⇐∘α⇒
  : ⟪ α⇐ ∘ α⇒ {a₀} {a₁} {a₂} ⟫ ≅ᴴ ⟪ id {(a₀ ⊗₀ a₁) ⊗₀ a₂} ⟫
test-α⇐∘α⇒ = from-just (findIso
  ⟪ α⇐ ∘ α⇒ {a₀} {a₁} {a₂} ⟫ ⟪ id {(a₀ ⊗₀ a₁) ⊗₀ a₂} ⟫)

test-α⇒∘α⇐
  : ⟪ α⇒ ∘ α⇐ {a₀} {a₁} {a₂} ⟫ ≅ᴴ ⟪ id {a₀ ⊗₀ (a₁ ⊗₀ a₂)} ⟫
test-α⇒∘α⇐ = from-just (findIso
  ⟪ α⇒ ∘ α⇐ {a₀} {a₁} {a₂} ⟫ ⟪ id {a₀ ⊗₀ (a₁ ⊗₀ a₂)} ⟫)

test-λ⇒∘id⊗f
  : ⟪ λ⇒ ∘ (id {unit} ⊗₁ Agen f) ⟫ ≅ᴴ ⟪ Agen f ∘ λ⇒ ⟫
test-λ⇒∘id⊗f = from-just (findIso
  ⟪ λ⇒ ∘ (id {unit} ⊗₁ Agen f) ⟫ ⟪ Agen f ∘ λ⇒ ⟫)

test-ρ⇒∘f⊗id
  : ⟪ ρ⇒ ∘ (Agen f ⊗₁ id {unit}) ⟫ ≅ᴴ ⟪ Agen f ∘ ρ⇒ ⟫
test-ρ⇒∘f⊗id = from-just (findIso
  ⟪ ρ⇒ ∘ (Agen f ⊗₁ id {unit}) ⟫ ⟪ Agen f ∘ ρ⇒ ⟫)

test-α-comm
  : ⟪ α⇒ ∘ ((Agen f ⊗₁ Agen g) ⊗₁ Agen h) ⟫
  ≅ᴴ ⟪ (Agen f ⊗₁ (Agen g ⊗₁ Agen h)) ∘ α⇒ ⟫
test-α-comm = from-just (findIso
  ⟪ α⇒ ∘ ((Agen f ⊗₁ Agen g) ⊗₁ Agen h) ⟫
  ⟪ (Agen f ⊗₁ (Agen g ⊗₁ Agen h)) ∘ α⇒ ⟫)

test-triangle
  : ⟪ id {a₀} ⊗₁ λ⇒ {a₁} ∘ α⇒ {a₀} {unit} {a₁} ⟫
  ≅ᴴ ⟪ ρ⇒ {a₀} ⊗₁ id {a₁} ⟫
test-triangle = from-just (findIso
  ⟪ id {a₀} ⊗₁ λ⇒ {a₁} ∘ α⇒ {a₀} {unit} {a₁} ⟫
  ⟪ ρ⇒ {a₀} ⊗₁ id {a₁} ⟫)

test-pentagon
  : ⟪ (id {a₀} ⊗₁ α⇒ {a₁} {a₂} {a₀})
        ∘ α⇒ {a₀} {a₁ ⊗₀ a₂} {a₀}
        ∘ (α⇒ {a₀} {a₁} {a₂} ⊗₁ id {a₀}) ⟫
  ≅ᴴ ⟪ α⇒ {a₀} {a₁} {a₂ ⊗₀ a₀}
        ∘ α⇒ {a₀ ⊗₀ a₁} {a₂} {a₀} ⟫
test-pentagon = from-just (findIso
  ⟪ (id {a₀} ⊗₁ α⇒ {a₁} {a₂} {a₀})
       ∘ α⇒ {a₀} {a₁ ⊗₀ a₂} {a₀}
       ∘ (α⇒ {a₀} {a₁} {a₂} ⊗₁ id {a₀}) ⟫
  ⟪ α⇒ {a₀} {a₁} {a₂ ⊗₀ a₀}
       ∘ α⇒ {a₀ ⊗₀ a₁} {a₂} {a₀} ⟫)

test-σ∘σ : ⟪ σ ∘ σ {a₀} {a₁} ⟫ ≅ᴴ ⟪ id {a₀ ⊗₀ a₁} ⟫
test-σ∘σ = from-just (findIso ⟪ σ ∘ σ {a₀} {a₁} ⟫ ⟪ id {a₀ ⊗₀ a₁} ⟫)

test-σ∘[f⊗g]
  : ⟪ σ ∘ (Agen f ⊗₁ Agen g) ⟫ ≅ᴴ ⟪ (Agen g ⊗₁ Agen f) ∘ σ ⟫
test-σ∘[f⊗g] = from-just (findIso
  ⟪ σ ∘ (Agen f ⊗₁ Agen g) ⟫
  ⟪ (Agen g ⊗₁ Agen f) ∘ σ ⟫)

test-hexagon
  : ⟪ id {a₁} ⊗₁ σ ∘ α⇒ {a₁} {a₀} {a₂} ∘ σ ⊗₁ id {a₂} ⟫
  ≅ᴴ ⟪ α⇒ {a₁} {a₂} {a₀} ∘ σ {a₀} {a₁ ⊗₀ a₂} ∘ α⇒ {a₀} {a₁} {a₂} ⟫
test-hexagon = from-just (findIso
  ⟪ id {a₁} ⊗₁ σ ∘ α⇒ {a₁} {a₀} {a₂} ∘ σ ⊗₁ id {a₂} ⟫
  ⟪ α⇒ {a₁} {a₂} {a₀} ∘ σ {a₀} {a₁ ⊗₀ a₂} ∘ α⇒ {a₀} {a₁} {a₂} ⟫)

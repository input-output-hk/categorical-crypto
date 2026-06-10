{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Free-SMC mirror of the data of `GConstruction.assoc'-coherence`.
--
-- 8 atoms (the polymorphic objects) and 3 generators (the morphism
-- variables f', g', h') over which the coherence equation is stated:
--
--   f' : A⁺ ⊗ B⁻ → A⁻ ⊗ B⁺      g' : B⁺ ⊗ D⁻ → B⁻ ⊗ D⁺
--   h' : D⁺ ⊗ E⁻ → D⁻ ⊗ E⁺
--
-- plus the GConstruction routing isos β/α/γ as generic free terms, and
-- the two sides lhsᵗ/rhsᵗ of the coherence equation, mirroring the
-- definitions in GConstruction.agda verbatim:
--
--   β = α⇐ ∘ id ⊗ σ ∘ α⇒
--   α = α⇒ ∘ σ⊗id ∘ α⇐ ∘ id⊗(σ⊗id) ∘ id⊗α⇐ ∘ α⇒
--   γ = α  ∘ id⊗σ                  (i.e. α's body with a trailing id⊗σ)
--   m₀  = α ∘ h'⊗g' ∘ γ            k₀  = α ∘ g'⊗f' ∘ γ
--   m₀' = β ∘ m₀⊗id ∘ β            q₀  = α⇐ ∘ id⊗k₀ ∘ α⇒
--   lhs = β ∘ (α⊗id ∘ m₀' ∘ (id⊗f' ∘ γ)⊗id) ∘ β
--   rhs = α⊗id ∘ q₀ ∘ (h'⊗id ∘ γ)⊗id
--------------------------------------------------------------------------------

module Categories.GConstructionCoherence.Terms where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

X8 : Set
X8 = Fin 8

open FreeMonoidalHelper Symm X8 public using (ObjTerm; Var; _⊗₀_)

A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : ObjTerm
A⁺ = Var 0F ; A⁻ = Var 1F ; B⁺ = Var 2F ; B⁻ = Var 3F
D⁺ = Var 4F ; D⁻ = Var 5F ; E⁺ = Var 6F ; E⁻ = Var 7F

data GMor : ObjTerm → ObjTerm → Set where
  gf : GMor (A⁺ ⊗₀ B⁻) (A⁻ ⊗₀ B⁺)
  gg : GMor (B⁺ ⊗₀ D⁻) (B⁻ ⊗₀ D⁺)
  gh : GMor (D⁺ ⊗₀ E⁻) (D⁻ ⊗₀ E⁺)

_≟-GMor_ : ∀ {A B} → DecidableEquality (GMor A B)
gf ≟-GMor gf = yes refl
gg ≟-GMor gg = yes refl
gh ≟-GMor gh = yes refl

gSig : APROPSignature
gSig = record { X = X8 ; mor = GMor }

gSigDec : APROPSignatureDec
gSigDec = record { sig = gSig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-GMor_ }

open APROP gSig public
  using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_;
         ≈-Term-refl; ≈-Term-sym; ≈-Term-trans;
         idˡ; idʳ; assoc; ∘-resp-≈; ⊗-resp-≈; ⊗-∘-dist; id⊗id≈id;
         α-comm; σ∘[f⊗g]≈[g⊗f]∘σ; σ∘σ≈id)

f' g' h' : HomTerm _ _
f' = Agen gf
g' = Agen gg
h' = Agen gh

-- The routing isos, generic (mirror GConstruction lines 49/83/87).
βᵗ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
βᵗ = α⇐ ∘ id ⊗₁ σ ∘ α⇒

αᵗ : ∀ {A⁻' B⁺' B⁻' C⁺'}
   → HomTerm ((B⁻' ⊗₀ C⁺') ⊗₀ (A⁻' ⊗₀ B⁺')) ((A⁻' ⊗₀ C⁺') ⊗₀ (B⁻' ⊗₀ B⁺'))
αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γᵗ : ∀ {A⁺' B⁺' B⁻' C⁻'}
   → HomTerm ((A⁺' ⊗₀ C⁻') ⊗₀ (B⁻' ⊗₀ B⁺')) ((B⁺' ⊗₀ C⁻') ⊗₀ (A⁺' ⊗₀ B⁻'))
γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

-- The composites of the coherence equation, at their concrete instances.
m₀ᵗ : HomTerm ((B⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ((B⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺))
m₀ᵗ = αᵗ ∘ h' ⊗₁ g' ∘ γᵗ

k₀ᵗ : HomTerm ((A⁺ ⊗₀ D⁻) ⊗₀ (B⁻ ⊗₀ B⁺)) ((A⁻ ⊗₀ D⁺) ⊗₀ (B⁻ ⊗₀ B⁺))
k₀ᵗ = αᵗ ∘ g' ⊗₁ f' ∘ γᵗ

m₀'ᵗ : HomTerm (((B⁺ ⊗₀ E⁻) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
              (((B⁻ ⊗₀ E⁺) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
m₀'ᵗ = βᵗ ∘ m₀ᵗ ⊗₁ id ∘ βᵗ

q₀ᵗ : HomTerm (((D⁻ ⊗₀ E⁺) ⊗₀ (A⁺ ⊗₀ D⁻)) ⊗₀ (B⁻ ⊗₀ B⁺))
              (((D⁻ ⊗₀ E⁺) ⊗₀ (A⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
q₀ᵗ = α⇐ ∘ id ⊗₁ k₀ᵗ ∘ α⇒

lhsᵗ rhsᵗ : HomTerm (((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
                    (((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
lhsᵗ = βᵗ ∘ (αᵗ ⊗₁ id ∘ m₀'ᵗ ∘ (id ⊗₁ f' ∘ γᵗ) ⊗₁ id) ∘ βᵗ
rhsᵗ = αᵗ ⊗₁ id ∘ q₀ᵗ ∘ (h' ⊗₁ id ∘ γᵗ) ⊗₁ id

--------------------------------------------------------------------------------
-- Three-segment decompositions of both sides (interfaces I₁/I₂ are the
-- lhs's natural stage boundaries; the rhs segments are conjugated onto
-- them by the re-routing isos ρ₁ᵗ/ρ₂ᵗ).
--
--   lhsᵗ ≈ L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ        (free rearrangement: ⊗-∘-dist + interchange + assoc)
--   rhsᵗ ≈ R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ        (free: + floating h' through q₀'s associators)
--
--   ob₀ : ρ₁ᵗ ∘ R₀ᵗ ≈ L₀ᵗ          ob₁ : ρ₂ᵗ ∘ R₁ᵗ ≈ L₁ᵗ ∘ ρ₁ᵗ
--   ob₂ : R₂ᵗ ≈ L₂ᵗ ∘ ρ₂ᵗ          (solver obligations, one box each)

-- lhs segments
L₀ᵗ : HomTerm (((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
              (((B⁺ ⊗₀ E⁻) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
L₀ᵗ = (id ⊗₁ f') ⊗₁ id ∘ γᵗ ⊗₁ id ∘ βᵗ

L₁ᵗ : HomTerm (((B⁺ ⊗₀ E⁻) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
              (((D⁺ ⊗₀ E⁻) ⊗₀ (B⁻ ⊗₀ D⁺)) ⊗₀ (A⁻ ⊗₀ B⁺))
L₁ᵗ = (id ⊗₁ g') ⊗₁ id ∘ γᵗ ⊗₁ id ∘ βᵗ

L₂ᵗ : HomTerm (((D⁺ ⊗₀ E⁻) ⊗₀ (B⁻ ⊗₀ D⁺)) ⊗₀ (A⁻ ⊗₀ B⁺))
              (((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
L₂ᵗ = βᵗ ∘ αᵗ ⊗₁ id ∘ βᵗ ∘ αᵗ ⊗₁ id ∘ (h' ⊗₁ id) ⊗₁ id

-- rhs segments
R₀ᵗ : HomTerm (((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
              ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁺ ⊗₀ D⁻) ⊗₀ (A⁻ ⊗₀ B⁺)))
R₀ᵗ = id ⊗₁ (id ⊗₁ f') ∘ id ⊗₁ γᵗ ∘ α⇒ ∘ γᵗ ⊗₁ id

R₁ᵗ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁺ ⊗₀ D⁻) ⊗₀ (A⁻ ⊗₀ B⁺)))
              ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁻ ⊗₀ D⁺) ⊗₀ (A⁻ ⊗₀ B⁺)))
R₁ᵗ = id ⊗₁ (g' ⊗₁ id)

R₂ᵗ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁻ ⊗₀ D⁺) ⊗₀ (A⁻ ⊗₀ B⁺)))
              (((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
R₂ᵗ = αᵗ ⊗₁ id ∘ (h' ⊗₁ id) ⊗₁ id ∘ α⇐ ∘ id ⊗₁ αᵗ

-- the re-routing isos
ρ₁ᵗ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁺ ⊗₀ D⁻) ⊗₀ (A⁻ ⊗₀ B⁺)))
              (((B⁺ ⊗₀ E⁻) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
ρ₁ᵗ = βᵗ ∘ (id ⊗₁ σ ∘ σ ∘ αᵗ) ⊗₁ id ∘ βᵗ ∘ σ

ρ₂ᵗ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁻ ⊗₀ D⁺) ⊗₀ (A⁻ ⊗₀ B⁺)))
              (((D⁺ ⊗₀ E⁻) ⊗₀ (B⁻ ⊗₀ D⁺)) ⊗₀ (A⁻ ⊗₀ B⁺))
ρ₂ᵗ = α⇐

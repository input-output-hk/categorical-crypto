{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The coherence residue of `Categories.GConstructionLoop.trace-mid`, proven by
-- the APROP solver over a 6-atom signature and transported into an arbitrary
-- SMC.  Both sides of `trace-mid` split into four nested single-wire traces by
-- `vanishing₂`, in the wire orders P,R,Q,S and P,Q,R,S respectively; one
-- `trace-comm` (Fubini) step reconciles them and leaves exactly
--
--   LC :  β ⊗ id ∘ f₃ ∘ β ⊗ id  ≈  g₃
--
-- with `fᵢ`/`gᵢ` the associator-conjugated loop bodies the splits produce and
-- `g = id ⊗ mid ∘ f ∘ id ⊗ mid`.  The bracketing is the one
-- `vanishing₂`/`trace-∘ˡ`/`trace-∘ʳ` produce, so `trace-mid` reads `LC` off
-- without reassociating.
--------------------------------------------------------------------------------

module Categories.GConstructionLoopCoherence where

open import Level

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Categories.APROP
open import Categories.FreeMonoidal

import Categories.APROP.Hypergraph.Solver.Frontend as Interp

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

X6 : Set
X6 = Fin 6

open FreeMonoidalHelper Symm X6 using (ObjTerm; Var; _⊗₀_)

a b p q r s : ObjTerm
a = Var 0F ; b = Var 1F ; p = Var 2F
q = Var 3F ; r = Var 4F ; s = Var 5F

-- the left-hand trace's loop object
L : ObjTerm
L = (p ⊗₀ r) ⊗₀ (q ⊗₀ s)

data Mor : ObjTerm → ObjTerm → Set where
  gf : Mor (a ⊗₀ L) (b ⊗₀ L)

_≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
gf ≟-Mor gf = yes refl

sig : APROPSignature
sig = record { X = X6 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

βᵗ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
βᵗ = α⇐ ∘ id ⊗₁ σ ∘ α⇒

midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

-- The three splits of the left loop `L`, wire order P,R,Q,S.
f₁ᵗ : HomTerm ((a ⊗₀ (p ⊗₀ r)) ⊗₀ (q ⊗₀ s)) ((b ⊗₀ (p ⊗₀ r)) ⊗₀ (q ⊗₀ s))
f₁ᵗ = α⇐ ∘ Agen gf ∘ α⇒

f₂ᵗ : HomTerm (((a ⊗₀ p) ⊗₀ r) ⊗₀ (q ⊗₀ s)) (((b ⊗₀ p) ⊗₀ r) ⊗₀ (q ⊗₀ s))
f₂ᵗ = α⇐ ⊗₁ id ∘ f₁ᵗ ∘ α⇒ ⊗₁ id

f₃ᵗ : HomTerm ((((a ⊗₀ p) ⊗₀ r) ⊗₀ q) ⊗₀ s) ((((b ⊗₀ p) ⊗₀ r) ⊗₀ q) ⊗₀ s)
f₃ᵗ = α⇐ ∘ f₂ᵗ ∘ α⇒

-- The same three splits of the right loop `(p ⊗ q) ⊗ (r ⊗ s)`, order P,Q,R,S.
gᵗ : HomTerm (a ⊗₀ ((p ⊗₀ q) ⊗₀ (r ⊗₀ s))) (b ⊗₀ ((p ⊗₀ q) ⊗₀ (r ⊗₀ s)))
gᵗ = id ⊗₁ midᵗ ∘ Agen gf ∘ id ⊗₁ midᵗ

g₁ᵗ : HomTerm ((a ⊗₀ (p ⊗₀ q)) ⊗₀ (r ⊗₀ s)) ((b ⊗₀ (p ⊗₀ q)) ⊗₀ (r ⊗₀ s))
g₁ᵗ = α⇐ ∘ gᵗ ∘ α⇒

g₂ᵗ : HomTerm (((a ⊗₀ p) ⊗₀ q) ⊗₀ (r ⊗₀ s)) (((b ⊗₀ p) ⊗₀ q) ⊗₀ (r ⊗₀ s))
g₂ᵗ = α⇐ ⊗₁ id ∘ g₁ᵗ ∘ α⇒ ⊗₁ id

g₃ᵗ : HomTerm ((((a ⊗₀ p) ⊗₀ q) ⊗₀ r) ⊗₀ s) ((((b ⊗₀ p) ⊗₀ q) ⊗₀ r) ⊗₀ s)
g₃ᵗ = α⇐ ∘ g₂ᵗ ∘ α⇒

lhs rhs : HomTerm ((((a ⊗₀ p) ⊗₀ q) ⊗₀ r) ⊗₀ s) ((((b ⊗₀ p) ⊗₀ q) ⊗₀ r) ⊗₀ s)
lhs = βᵗ ⊗₁ id ∘ f₃ᵗ ∘ βᵗ ⊗₁ id
rhs = g₃ᵗ

open import Categories.APROP.Hypergraph.Solver.Split sig
  using () renaming (solveTerm!ᵀ to solve!)

coh : lhs ≈Term rhs
coh = solve! lhs rhs refl

private module IM = Interp sig

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A B P Q R S : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 6 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = A ; ⟦ 1F ⟧ᵖ₀ = B ; ⟦ 2F ⟧ᵖ₀ = P
  ⟦ 3F ⟧ᵖ₀ = Q ; ⟦ 4F ⟧ᵖ₀ = R ; ⟦ 5F ⟧ᵖ₀ = S

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGen (f₀ : OI.⟦ a ⊗₀ L ⟧₀ C.⇒ OI.⟦ b ⊗₀ L ⟧₀) where

    ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
    ⟦ gf ⟧ᵖ₁ = f₀

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    LC : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
    LC = Functor.F-resp-≈ freeFunctor coh

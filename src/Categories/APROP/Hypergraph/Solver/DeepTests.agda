{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Go/no-go spike for `deepFoc`: the canonical NON-SYNTACTIC redex.
--
--   s  = (b ⊗ d) ∘ (a ⊗ c)        (two parallel wires, generators interleaved)
--   lᵗ = b ∘ a                     (the top wire's composite)
--
-- By interchange `s = (b∘a) ⊗ (d∘c)` as a diagram, but `b ∘ a` is NOT a
-- subterm of `s` as written: `a` and `b` live in different operands of the
-- outer `∘`.  So term-level focusing fails (negative control), while the
-- hypergraph route — subMatch, hole-carve, decode, focus-the-hole — finds it,
-- and the resulting frame certifies against `⟪ s ⟫` by `findIso` (exactly the
-- obligation `rewriteH!` imposes).  Each `refl` forces full reduction of the
-- pipeline at type-check time.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.DeepTests where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (is-just; from-just)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

X : Set
X = Fin 1

open FreeMonoidalHelper Symm X using (ObjTerm; Var; _⊗₀_)

private
  x : ObjTerm
  x = Var zero

data MyMor : ObjTerm → ObjTerm → Set where
  a b c d : MyMor x x

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
a ≟-MyMor a = yes refl
a ≟-MyMor b = no λ ()
a ≟-MyMor c = no λ ()
a ≟-MyMor d = no λ ()
b ≟-MyMor a = no λ ()
b ≟-MyMor b = yes refl
b ≟-MyMor c = no λ ()
b ≟-MyMor d = no λ ()
c ≟-MyMor a = no λ ()
c ≟-MyMor b = no λ ()
c ≟-MyMor c = yes refl
c ≟-MyMor d = no λ ()
d ≟-MyMor a = no λ ()
d ≟-MyMor b = no λ ()
d ≟-MyMor c = no λ ()
d ≟-MyMor d = yes refl

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record { sig = mySig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-MyMor_ }

open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open import Categories.APROP.Hypergraph.Solver.Carve mySigDec using (focusAt)
open import Categories.APROP.Hypergraph.Solver.Deep mySigDec using (deepFoc)
open APROP mySig hiding (ObjTerm; Var; _⊗₀_)

private
  lᵗ : HomTerm x x
  lᵗ = Agen b ∘ Agen a

  s : HomTerm (x ⊗₀ x) (x ⊗₀ x)
  s = (Agen b ⊗₁ Agen d) ∘ (Agen a ⊗₁ Agen c)

--------------------------------------------------------------------------------
-- Negative control: the redex is NOT a subterm, so syntactic focusing fails.

syntactic-fails : is-just (focusAt s lᵗ) ≡ false
syntactic-fails = refl

--------------------------------------------------------------------------------
-- The hypergraph route finds it …

deep-finds : is-just (deepFoc s lᵗ) ≡ true
deep-finds = refl

-- … and the auto-constructed frame certifies against ⟪ s ⟫ (the exact
-- obligation `rewriteH!` would impose).

private
  foc  = from-just (deepFoc s lᵗ)
  k    = proj₁ foc
  pre  = proj₁ (proj₂ foc)
  post = proj₂ (proj₂ foc)

  frame : HomTerm (x ⊗₀ x) (x ⊗₀ x)
  frame = post ∘ (id {k} ⊗₁ lᵗ) ∘ pre

deep-certifies : is-just (findIso ⟪ s ⟫ ⟪ frame ⟫) ≡ true
deep-certifies = refl

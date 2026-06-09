{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- End-to-end spike for `focusAt`: feed it a term `s` and a redex `lᵗ`, let it
-- auto-construct the frame `(k , pre , post)`, then check the *constructed*
-- frame is hypergraph-iso to `s` — i.e. `findIso ⟪ s ⟫ ⟪ post ∘ (id{k}⊗lᵗ) ∘ pre ⟫`
-- reduces to `just`.  This is exactly the certification `rewriteH!` would run,
-- so a green `refl` means the carve produced a frame `rewriteH!` would accept,
-- with NO hand-written `pre`/`post`.
--
-- Monoid signature: m : a₀ ⊗ a₀ → a₀ , u : unit → a₀ .
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.CarveTests where

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

open FreeMonoidalHelper Symm X using (ObjTerm; Var; unit; _⊗₀_)

private
  a₀ : ObjTerm
  a₀ = Var zero

data MyMor : ObjTerm → ObjTerm → Set where
  m : MyMor (a₀ ⊗₀ a₀) a₀
  u : MyMor unit a₀

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
m ≟-MyMor m = yes refl
u ≟-MyMor u = yes refl

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record { sig = mySig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-MyMor_ }

open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open import Categories.APROP.Hypergraph.Solver.Carve mySigDec using (focusAt)
open APROP mySig hiding (ObjTerm; Var; unit; _⊗₀_)

--------------------------------------------------------------------------------
-- The redex `lᵗ = m ∘ (u ⊗ id)` occurs in the right tensor factor of
-- `s = m ∘ (id ⊗ (m ∘ (u ⊗ id)))` — under one `∘` and inside a right `⊗`.

private
  lᵗ : HomTerm (unit ⊗₀ a₀) a₀
  lᵗ = Agen m ∘ (Agen u ⊗₁ id)

  s : HomTerm (a₀ ⊗₀ (unit ⊗₀ a₀)) a₀
  s = Agen m ∘ (id {a₀} ⊗₁ (Agen m ∘ (Agen u ⊗₁ id)))

  -- `focusAt` succeeds and yields a frame; project its three components.
  foc = from-just (focusAt s lᵗ)
  k    = proj₁ foc
  pre  = proj₁ (proj₂ foc)
  post = proj₂ (proj₂ foc)

  frame : HomTerm (a₀ ⊗₀ (unit ⊗₀ a₀)) a₀
  frame = post ∘ (id {k} ⊗₁ lᵗ) ∘ pre

-- The auto-constructed frame is certifiable: `findIso` finds the iso to `s`.
carve-certifies : is-just (findIso ⟪ s ⟫ ⟪ frame ⟫) ≡ true
carve-certifies = refl

--------------------------------------------------------------------------------
-- Left-`⊗` factor: the redex is the LEFT operand of a tensor, `lᵗ ⊗ id`.
-- `focusAt` routes the parallel `id` wire past it with σ.

private
  sL : HomTerm ((unit ⊗₀ a₀) ⊗₀ a₀) (a₀ ⊗₀ a₀)
  sL = (Agen m ∘ (Agen u ⊗₁ id)) ⊗₁ id {a₀}

  focL  = from-just (focusAt sL lᵗ)
  kL    = proj₁ focL
  preL  = proj₁ (proj₂ focL)
  postL = proj₂ (proj₂ focL)

  frameL : HomTerm ((unit ⊗₀ a₀) ⊗₀ a₀) (a₀ ⊗₀ a₀)
  frameL = postL ∘ (id {kL} ⊗₁ lᵗ) ∘ preL

carve-left-certifies : is-just (findIso ⟪ sL ⟫ ⟪ frameL ⟫) ≡ true
carve-left-certifies = refl

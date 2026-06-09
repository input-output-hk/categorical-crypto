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
open import Categories.APROP.Hypergraph.Solver.Carve mySigDec using (focusAt; focusAtₙ)
open import Data.Nat.Base using (ℕ)
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

--------------------------------------------------------------------------------
-- Occurrence selection: two copies of the redex, side by side.  `focusAtₙ`
-- locates each (index 0 = right factor, index 1 = left factor) and both frames
-- certify.

private
  s2 : HomTerm ((unit ⊗₀ a₀) ⊗₀ (unit ⊗₀ a₀)) (a₀ ⊗₀ a₀)
  s2 = (Agen m ∘ (Agen u ⊗₁ id)) ⊗₁ (Agen m ∘ (Agen u ⊗₁ id))

  foc2-0 = from-just (focusAtₙ s2 lᵗ 0)
  foc2-1 = from-just (focusAtₙ s2 lᵗ 1)

  frame2-0 frame2-1 : HomTerm ((unit ⊗₀ a₀) ⊗₀ (unit ⊗₀ a₀)) (a₀ ⊗₀ a₀)
  frame2-0 = proj₂ (proj₂ foc2-0) ∘ (id {proj₁ foc2-0} ⊗₁ lᵗ) ∘ proj₁ (proj₂ foc2-0)
  frame2-1 = proj₂ (proj₂ foc2-1) ∘ (id {proj₁ foc2-1} ⊗₁ lᵗ) ∘ proj₁ (proj₂ foc2-1)

two-occ-0 : is-just (findIso ⟪ s2 ⟫ ⟪ frame2-0 ⟫) ≡ true
two-occ-0 = refl

two-occ-1 : is-just (findIso ⟪ s2 ⟫ ⟪ frame2-1 ⟫) ≡ true
two-occ-1 = refl

--------------------------------------------------------------------------------
-- Precision probes for the syntactic engine.

-- Exactly the expected number of occurrences are enumerated: in `s2` the
-- redex occurs twice (plus no spurious whole-term/leaf matches).
open import Data.List.Base using (length)
open import Categories.APROP.Hypergraph.Solver.Carve mySigDec using (focusAll)

occurrence-count : length (focusAll s2 lᵗ) ≡ 2
occurrence-count = refl

-- An out-of-range occurrence index is rejected (the `found` obligation of
-- `rewriteAutoₙ!` becomes unsatisfiable).
out-of-range : is-just (focusAtₙ s2 lᵗ 2) ≡ false
out-of-range = refl

-- Boundary case: the redex IS the whole term; the leaf frame (pad `unit`,
-- λ-contexts) certifies.
private
  focW  = from-just (focusAt lᵗ lᵗ)
  frameW : HomTerm (unit ⊗₀ a₀) a₀
  frameW = proj₂ (proj₂ focW) ∘ (id {proj₁ focW} ⊗₁ lᵗ) ∘ proj₁ (proj₂ focW)

whole-term-leaf : is-just (findIso ⟪ lᵗ ⟫ ⟪ frameW ⟫) ≡ true
whole-term-leaf = refl

-- The leaf test is up-to-SMC (it uses `findIso`, not syntactic equality):
-- a subterm written with extra structural noise (`(… ∘ id) ∘ (σ ∘ σ)`) still
-- matches the clean rule LHS — only the *interface objects* `P`, `Q` must
-- coincide literally.
private
  noisy : HomTerm (unit ⊗₀ a₀) a₀
  noisy = (Agen m ∘ (Agen u ⊗₁ id) ∘ id) ∘ (σ ∘ σ)

  focN = from-just (focusAt noisy lᵗ)
  frameN : HomTerm (unit ⊗₀ a₀) a₀
  frameN = proj₂ (proj₂ focN) ∘ (id {proj₁ focN} ⊗₁ lᵗ) ∘ proj₁ (proj₂ focN)

leaf-up-to-smc : is-just (findIso ⟪ noisy ⟫ ⟪ frameN ⟫) ≡ true
leaf-up-to-smc = refl

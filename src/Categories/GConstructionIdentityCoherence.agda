{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The coherence lemmas of GConstruction's identity laws and of its
-- `right-superposing`, proven by the APROP solver over a 5-atom signature
-- with one generator and transported into an arbitrary SMC.
--
-- identityˡ:  trace (α ∘ σ⇒ ⊗ f ∘ γ) ≈ f,  loop B⁻⊗B⁺.  Reduction plan:
--   vanishing₂ splits the loop; then with
--     h     = β ∘ (f ⊗ id) ∘ β          E₂ = (β ⊗ id) ∘ β
--     gcore = (f ⊗ id) ∘ β              (every yank-core is a β-instance)
--   C1L :  α⇐ ∘ body ∘ α⇒  ≈  E₂ ∘ (h ⊗ id)     -- inner loop canonical form
--   C3L :  β ∘ h           ≈  gcore              -- outer loop canonical form
--   and the trace axioms (trace-∘ˡ/ʳ, superposing, yanking) finish.
--
-- identityʳ:  trace (α ∘ f ⊗ σ⇒ ∘ γ) ≈ f,  loop A⁻⊗A⁺.  Mirror, with
--     PR = β ∘ (σ ⊗ id)                 QR = (σ ⊗ id) ∘ β
--     mR = (β ∘ (σ ⊗ id) ∘ β) ∘ (f ⊗ id) ∘ QR   hR = σ ∘ f
--     E₂R = (σ ⊗ id) ∘ β
--   C1R :  α⇐ ∘ body ∘ α⇒  ≈  (mR ⊗ id) ∘ β ∘ (PR ⊗ id)
--   C3R :  mR ∘ PR         ≈  E₂R ∘ (hR ⊗ id)
--   closing with σ∘σ ≈ id in C.
--
-- right-superposing:  trace f ⊗ id ≈ trace (β ∘ (f ⊗ id) ∘ β).  The braiding
-- swap and the trace naturalities leave the two loop bodies differing by
--   RS :  (σ ⊗ id) ∘ (α⇐ ∘ id ⊗ f ∘ α⇒) ∘ (σ ⊗ id)  ≈  β ∘ (f ⊗ id) ∘ β
--   over the same generator, read with its two b-atoms as the loop wire's
--   ends (aliases A'/B'/X⁻/X⁺) and the fifth atom y as the superposed wire.
--------------------------------------------------------------------------------

module Categories.GConstructionIdentityCoherence where

open import Data.Bool.Base using (true)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

X5 : Set
X5 = Fin 5

open FreeMonoidalHelper Symm X5 public using (ObjTerm; Var; _⊗₀_)

a⁺ a⁻ b⁺ b⁻ y : ObjTerm
a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F ; y = Var 4F

-- the same atoms, named for right-superposing's reading of the generator
-- (f : A' ⊗ X⁻ → B' ⊗ X⁺, with X⁻/X⁺ the loop wire and y superposed)
A' B' X⁻ X⁺ Y : ObjTerm
A' = a⁺ ; B' = a⁻ ; X⁻ = b⁻ ; X⁺ = b⁺ ; Y = y

data IMor : ObjTerm → ObjTerm → Set where
  gf : IMor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)

_≟-IMor_ : ∀ {A B} → DecidableEquality (IMor A B)
gf ≟-IMor gf = yes refl

iSig : APROPSignature
iSig = record { X = X5 ; mor = IMor }

iSigDec : APROPSignatureDec
iSigDec = record { sig = iSig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-IMor_ }

open APROP iSig public
  using (HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

f' : HomTerm (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
f' = Agen gf

-- routing isos (as in GConstruction / GConstructionCoherence)
βᵗ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
βᵗ = α⇐ ∘ id ⊗₁ σ ∘ α⇒

αᵗ : ∀ {A⁻' B⁺' B⁻' C⁺'}
   → HomTerm ((B⁻' ⊗₀ C⁺') ⊗₀ (A⁻' ⊗₀ B⁺')) ((A⁻' ⊗₀ C⁺') ⊗₀ (B⁻' ⊗₀ B⁺'))
αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γᵗ : ∀ {A⁺' B⁺' B⁻' C⁻'}
   → HomTerm ((A⁺' ⊗₀ C⁻') ⊗₀ (B⁻' ⊗₀ B⁺')) ((B⁺' ⊗₀ C⁻') ⊗₀ (A⁺' ⊗₀ B⁻'))
γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

--------------------------------------------------------------------------------
-- identityˡ pieces (loop b⁻ ⊗ b⁺)

bodyLᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ (b⁻ ⊗₀ b⁺)) ((a⁻ ⊗₀ b⁺) ⊗₀ (b⁻ ⊗₀ b⁺))
bodyLᵗ = αᵗ ∘ σ ⊗₁ f' ∘ γᵗ

hLᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ b⁻) ((a⁻ ⊗₀ b⁻) ⊗₀ b⁺)
hLᵗ = βᵗ ∘ f' ⊗₁ id ∘ βᵗ

E₂Lᵗ : HomTerm (((a⁻ ⊗₀ b⁻) ⊗₀ b⁺) ⊗₀ b⁺) (((a⁻ ⊗₀ b⁺) ⊗₀ b⁻) ⊗₀ b⁺)
E₂Lᵗ = βᵗ ⊗₁ id ∘ βᵗ

gcoreᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ b⁻) ((a⁻ ⊗₀ b⁺) ⊗₀ b⁻)
gcoreᵗ = f' ⊗₁ id ∘ βᵗ

C1Lᵗ-lhs C1Lᵗ-rhs : HomTerm (((a⁺ ⊗₀ b⁻) ⊗₀ b⁻) ⊗₀ b⁺) (((a⁻ ⊗₀ b⁺) ⊗₀ b⁻) ⊗₀ b⁺)
C1Lᵗ-lhs = α⇐ ∘ bodyLᵗ ∘ α⇒
C1Lᵗ-rhs = E₂Lᵗ ∘ hLᵗ ⊗₁ id

C3Lᵗ-lhs C3Lᵗ-rhs : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ b⁻) ((a⁻ ⊗₀ b⁺) ⊗₀ b⁻)
C3Lᵗ-lhs = βᵗ ∘ hLᵗ
C3Lᵗ-rhs = gcoreᵗ

--------------------------------------------------------------------------------
-- identityʳ pieces (loop a⁻ ⊗ a⁺)

bodyRᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ (a⁻ ⊗₀ a⁺)) ((a⁻ ⊗₀ b⁺) ⊗₀ (a⁻ ⊗₀ a⁺))
bodyRᵗ = αᵗ ∘ f' ⊗₁ σ ∘ γᵗ

PRᵗ : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ((b⁻ ⊗₀ a⁻) ⊗₀ a⁺)
PRᵗ = βᵗ ∘ σ ⊗₁ id

QRᵗ : HomTerm ((b⁻ ⊗₀ a⁻) ⊗₀ a⁺) ((a⁺ ⊗₀ b⁻) ⊗₀ a⁻)
QRᵗ = σ ⊗₁ id ∘ βᵗ

mRᵗ : HomTerm ((b⁻ ⊗₀ a⁻) ⊗₀ a⁺) ((a⁻ ⊗₀ b⁺) ⊗₀ a⁻)
mRᵗ = (βᵗ ∘ σ ⊗₁ id ∘ βᵗ) ∘ f' ⊗₁ id ∘ QRᵗ

hRᵗ : HomTerm (a⁺ ⊗₀ b⁻) (b⁺ ⊗₀ a⁻)
hRᵗ = σ ∘ f'

E₂Rᵗ : HomTerm ((b⁺ ⊗₀ a⁻) ⊗₀ a⁻) ((a⁻ ⊗₀ b⁺) ⊗₀ a⁻)
E₂Rᵗ = σ ⊗₁ id ∘ βᵗ

C1Rᵗ-lhs C1Rᵗ-rhs : HomTerm (((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ⊗₀ a⁺) (((a⁻ ⊗₀ b⁺) ⊗₀ a⁻) ⊗₀ a⁺)
C1Rᵗ-lhs = α⇐ ∘ bodyRᵗ ∘ α⇒
C1Rᵗ-rhs = mRᵗ ⊗₁ id ∘ βᵗ ∘ PRᵗ ⊗₁ id

C3Rᵗ-lhs C3Rᵗ-rhs : HomTerm ((a⁺ ⊗₀ b⁻) ⊗₀ a⁻) ((a⁻ ⊗₀ b⁺) ⊗₀ a⁻)
C3Rᵗ-lhs = mRᵗ ∘ PRᵗ
C3Rᵗ-rhs = E₂Rᵗ ∘ hRᵗ ⊗₁ id

--------------------------------------------------------------------------------
-- right-superposing piece (loop wire X⁻/X⁺, superposed wire Y)

RSᵗ-lhs RSᵗ-rhs : HomTerm ((A' ⊗₀ Y) ⊗₀ X⁻) ((B' ⊗₀ Y) ⊗₀ X⁺)
RSᵗ-lhs = σ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ ⊗₁ id
RSᵗ-rhs = βᵗ ∘ f' ⊗₁ id ∘ βᵗ

--------------------------------------------------------------------------------
-- Solver obligations (call-pattern rules per docs/smc-solver-performance.md)

open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation (APROPSignatureDec.sig iSigDec) using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Match.FindIsoTab iSigDec using (findIsoᵀ)
open import Categories.APROP.Hypergraph.Soundness iSigDec
  using (soundness)

private
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

  iso-C1L : ⟪ C1Lᵗ-lhs ⟫ ≅ᴴ ⟪ C1Lᵗ-rhs ⟫
  iso-C1L = force! (findIsoᵀ ⟪ C1Lᵗ-lhs ⟫ ⟪ C1Lᵗ-rhs ⟫) refl
  iso-C3L : ⟪ C3Lᵗ-lhs ⟫ ≅ᴴ ⟪ C3Lᵗ-rhs ⟫
  iso-C3L = force! (findIsoᵀ ⟪ C3Lᵗ-lhs ⟫ ⟪ C3Lᵗ-rhs ⟫) refl
  iso-C1R : ⟪ C1Rᵗ-lhs ⟫ ≅ᴴ ⟪ C1Rᵗ-rhs ⟫
  iso-C1R = force! (findIsoᵀ ⟪ C1Rᵗ-lhs ⟫ ⟪ C1Rᵗ-rhs ⟫) refl
  iso-C3R : ⟪ C3Rᵗ-lhs ⟫ ≅ᴴ ⟪ C3Rᵗ-rhs ⟫
  iso-C3R = force! (findIsoᵀ ⟪ C3Rᵗ-lhs ⟫ ⟪ C3Rᵗ-rhs ⟫) refl
  iso-RS : ⟪ RSᵗ-lhs ⟫ ≅ᴴ ⟪ RSᵗ-rhs ⟫
  iso-RS = force! (findIsoᵀ ⟪ RSᵗ-lhs ⟫ ⟪ RSᵗ-rhs ⟫) refl

C1Lᵗ : C1Lᵗ-lhs ≈Term C1Lᵗ-rhs
C1Lᵗ = soundness {f = C1Lᵗ-lhs} {g = C1Lᵗ-rhs} iso-C1L
C3Lᵗ : C3Lᵗ-lhs ≈Term C3Lᵗ-rhs
C3Lᵗ = soundness {f = C3Lᵗ-lhs} {g = C3Lᵗ-rhs} iso-C3L
C1Rᵗ : C1Rᵗ-lhs ≈Term C1Rᵗ-rhs
C1Rᵗ = soundness {f = C1Rᵗ-lhs} {g = C1Rᵗ-rhs} iso-C1R
C3Rᵗ : C3Rᵗ-lhs ≈Term C3Rᵗ-rhs
C3Rᵗ = soundness {f = C3Rᵗ-lhs} {g = C3Rᵗ-rhs} iso-C3R
RSᵗ : RSᵗ-lhs ≈Term RSᵗ-rhs
RSᵗ = soundness {f = RSᵗ-lhs} {g = RSᵗ-rhs} iso-RS

--------------------------------------------------------------------------------
-- Transport into an arbitrary SMC.

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
import Categories.APROP.Hypergraph.Solver.Frontend as Interp

private module IM = Interp iSigDec

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (x⁺ x⁻ y⁺ y⁻ : C.Obj)
  where

  -- the atom y does not occur in the identity-law statements
  ⟦_⟧ᵖ₀ : Fin 5 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = x⁺ ; ⟦ 1F ⟧ᵖ₀ = x⁻ ; ⟦ 2F ⟧ᵖ₀ = y⁺ ; ⟦ 3F ⟧ᵖ₀ = y⁻ ; ⟦ 4F ⟧ᵖ₀ = x⁺

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGen (f₀ : OI.⟦ a⁺ ⊗₀ b⁻ ⟧₀ C.⇒ OI.⟦ a⁻ ⊗₀ b⁺ ⟧₀) where

    ⟦_⟧ᵖ₁ : ∀ {x y} → IMor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
    ⟦ gf ⟧ᵖ₁ = f₀

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    C1L : ⟦ C1Lᵗ-lhs ⟧₁ C.≈ ⟦ C1Lᵗ-rhs ⟧₁
    C1L = Functor.F-resp-≈ freeFunctor C1Lᵗ
    C3L : ⟦ C3Lᵗ-lhs ⟧₁ C.≈ ⟦ C3Lᵗ-rhs ⟧₁
    C3L = Functor.F-resp-≈ freeFunctor C3Lᵗ
    C1R : ⟦ C1Rᵗ-lhs ⟧₁ C.≈ ⟦ C1Rᵗ-rhs ⟧₁
    C1R = Functor.F-resp-≈ freeFunctor C1Rᵗ
    C3R : ⟦ C3Rᵗ-lhs ⟧₁ C.≈ ⟦ C3Rᵗ-rhs ⟧₁
    C3R = Functor.F-resp-≈ freeFunctor C3Rᵗ

-- right-superposing's reading: the loop wire's two ends are one object.
module TransportRS {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (a b x u : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 5 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = a ; ⟦ 1F ⟧ᵖ₀ = b ; ⟦ 2F ⟧ᵖ₀ = x ; ⟦ 3F ⟧ᵖ₀ = x ; ⟦ 4F ⟧ᵖ₀ = u

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGen (f₀ : OI.⟦ A' ⊗₀ X⁻ ⟧₀ C.⇒ OI.⟦ B' ⊗₀ X⁺ ⟧₀) where

    ⟦_⟧ᵖ₁ : ∀ {p q} → IMor p q → OI.⟦ p ⟧₀ C.⇒ OI.⟦ q ⟧₀
    ⟦ gf ⟧ᵖ₁ = f₀

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    RS : ⟦ RSᵗ-lhs ⟧₁ C.≈ ⟦ RSᵗ-rhs ⟧₁
    RS = Functor.F-resp-≈ freeFunctor RSᵗ

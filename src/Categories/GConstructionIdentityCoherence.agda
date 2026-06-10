{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The four coherence lemmas of GConstruction's identity laws, proven by the
-- APROP solver over a 4-atom signature and transported into an arbitrary SMC.
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

X4 : Set
X4 = Fin 4

open FreeMonoidalHelper Symm X4 public using (ObjTerm; Var; _⊗₀_)

a⁺ a⁻ b⁺ b⁻ : ObjTerm
a⁺ = Var 0F ; a⁻ = Var 1F ; b⁺ = Var 2F ; b⁻ = Var 3F

data IMor : ObjTerm → ObjTerm → Set where
  gf : IMor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)

_≟-IMor_ : ∀ {A B} → DecidableEquality (IMor A B)
gf ≟-IMor gf = yes refl

iSig : APROPSignature
iSig = record { X = X4 ; mor = IMor }

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
-- Solver obligations (call-pattern rules per docs/smc-solver-performance.md)

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation (APROPSignatureDec.sig iSigDec) using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso iSigDec using (findIso)
open import Categories.APROP.Hypergraph.SoundnessFullWired iSigDec
  using (soundness-full-wired)

private
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

  iso-C1L : ⟪ C1Lᵗ-lhs ⟫ ≅ᴴ ⟪ C1Lᵗ-rhs ⟫
  iso-C1L = force! (findIso ⟪ C1Lᵗ-lhs ⟫ ⟪ C1Lᵗ-rhs ⟫) refl
  iso-C3L : ⟪ C3Lᵗ-lhs ⟫ ≅ᴴ ⟪ C3Lᵗ-rhs ⟫
  iso-C3L = force! (findIso ⟪ C3Lᵗ-lhs ⟫ ⟪ C3Lᵗ-rhs ⟫) refl
  iso-C1R : ⟪ C1Rᵗ-lhs ⟫ ≅ᴴ ⟪ C1Rᵗ-rhs ⟫
  iso-C1R = force! (findIso ⟪ C1Rᵗ-lhs ⟫ ⟪ C1Rᵗ-rhs ⟫) refl
  iso-C3R : ⟪ C3Rᵗ-lhs ⟫ ≅ᴴ ⟪ C3Rᵗ-rhs ⟫
  iso-C3R = force! (findIso ⟪ C3Rᵗ-lhs ⟫ ⟪ C3Rᵗ-rhs ⟫) refl

C1Lᵗ : C1Lᵗ-lhs ≈Term C1Lᵗ-rhs
C1Lᵗ = soundness-full-wired {f = C1Lᵗ-lhs} {g = C1Lᵗ-rhs} iso-C1L
C3Lᵗ : C3Lᵗ-lhs ≈Term C3Lᵗ-rhs
C3Lᵗ = soundness-full-wired {f = C3Lᵗ-lhs} {g = C3Lᵗ-rhs} iso-C3L
C1Rᵗ : C1Rᵗ-lhs ≈Term C1Rᵗ-rhs
C1Rᵗ = soundness-full-wired {f = C1Rᵗ-lhs} {g = C1Rᵗ-rhs} iso-C1R
C3Rᵗ : C3Rᵗ-lhs ≈Term C3Rᵗ-rhs
C3Rᵗ = soundness-full-wired {f = C3Rᵗ-lhs} {g = C3Rᵗ-rhs} iso-C3R

--------------------------------------------------------------------------------
-- Transport into an arbitrary SMC.

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
import Categories.APROP.Hypergraph.Solver.Interpret as Interp

private module IM = Interp iSigDec

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (x⁺ x⁻ y⁺ y⁻ : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 4 → C.Obj
  ⟦ 0F ⟧ᵖ₀ = x⁺ ; ⟦ 1F ⟧ᵖ₀ = x⁻ ; ⟦ 2F ⟧ᵖ₀ = y⁺ ; ⟦ 3F ⟧ᵖ₀ = y⁻

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

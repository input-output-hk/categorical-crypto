{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The loop-body coherence residue of `GConstructionMonoidal.homomorphismᴳ`
-- (see there), over a 12-atom signature.  Solving it whole is out of reach
-- (measured: no answer in 900 s at ~50 boxes a side).  The two sides apply the
-- same four boxes grouped `(f′⊗f) ⊗ (g′⊗g)` vs `(f′⊗g′) ⊗ (f⊗g)`, which are
-- conjugate by `mid`; so `coh` pastes two generator-free solver leaves
-- (`ob-out`, `ob-in`) around `mid`'s naturality (`ob-nat`), bridging
-- re-bracketings with the pure-assoc respelling `stepR!`.
--------------------------------------------------------------------------------

module Categories.GConstructionHomCoherence where

open import Level

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin; suc)
open import Data.Fin.Patterns
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Categories.APROP
open import Categories.FreeMonoidal

import Categories.APROP.Hypergraph.Solver.Frontend as Interp
import Categories.Category.Monoidal.Interchange.Braided as IB
import Categories.Category.Monoidal.Interchange.Symmetric as IS

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

pattern 10F = suc 9F
pattern 11F = suc 10F

open FreeMonoidalHelper Symm (Fin 12) using (ObjTerm; Var; _⊗₀_)

a⁺ a⁻ b⁺ b⁻ d⁺ d⁻ p⁺ p⁻ q⁺ q⁻ r⁺ r⁻ : ObjTerm
a⁺ = Var 0F  ; a⁻ = Var 1F  ; b⁺ = Var 2F  ; b⁻ = Var 3F
d⁺ = Var 4F  ; d⁻ = Var 5F  ; p⁺ = Var 6F  ; p⁻ = Var 7F
q⁺ = Var 8F  ; q⁻ = Var 9F  ; r⁺ = Var 10F ; r⁻ = Var 11F

data Mor : ObjTerm → ObjTerm → Set where
  gf  : Mor (a⁺ ⊗₀ b⁻) (a⁻ ⊗₀ b⁺)
  gf′ : Mor (b⁺ ⊗₀ d⁻) (b⁻ ⊗₀ d⁺)
  gg  : Mor (p⁺ ⊗₀ q⁻) (p⁻ ⊗₀ q⁺)
  gg′ : Mor (q⁺ ⊗₀ r⁻) (q⁻ ⊗₀ r⁺)

_≟-Mor_ : ∀ {A B} → DecidableEquality (Mor A B)
gf  ≟-Mor gf  = yes refl
gf′ ≟-Mor gf′ = yes refl
gg  ≟-Mor gg  = yes refl
gg′ ≟-Mor gg′ = yes refl

sig : APROPSignature
sig = record { X = Fin 12 ; mor = Mor ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-Mor_ }

open APROP sig
  using (FreeMonoidal; Symmetric-Monoidal; HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐;
         _≈Term_)

open import Categories.APROP.Hypergraph.Solver.Split sig
  using () renaming (stepSplitR! to stepR!; solveTerm!ᵀ to solve!)
open import Categories.Morphism.Reasoning FreeMonoidal

open Category.HomReasoning FreeMonoidal

-- Verbatim free twins of `GConstructionTrace`'s `α`, `γ`, `mid`: `HOM` is read
-- off by conversion, and `ob-nat` relies on `midᵗ` being upstream's
-- `swapInner.from`.
αᵗ : ∀ {A⁻ B⁺ B⁻ C⁺} → HomTerm ((B⁻ ⊗₀ C⁺) ⊗₀ (A⁻ ⊗₀ B⁺)) ((A⁻ ⊗₀ C⁺) ⊗₀ (B⁻ ⊗₀ B⁺))
αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γᵗ : ∀ {A⁺ B⁺ B⁻ C⁻} → HomTerm ((A⁺ ⊗₀ C⁻) ⊗₀ (B⁻ ⊗₀ B⁺)) ((B⁺ ⊗₀ C⁻) ⊗₀ (A⁺ ⊗₀ B⁻))
γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

X Y W W′ : ObjTerm
X = b⁻ ⊗₀ b⁺                  ; Y  = q⁻ ⊗₀ q⁺
W = (a⁺ ⊗₀ p⁺) ⊗₀ (d⁻ ⊗₀ r⁻) ; W′ = (a⁻ ⊗₀ p⁻) ⊗₀ (d⁺ ⊗₀ r⁺)

BoxL : HomTerm (((b⁺ ⊗₀ d⁻) ⊗₀ (a⁺ ⊗₀ b⁻)) ⊗₀ ((q⁺ ⊗₀ r⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
               (((b⁻ ⊗₀ d⁺) ⊗₀ (a⁻ ⊗₀ b⁺)) ⊗₀ ((q⁻ ⊗₀ r⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
BoxL = (Agen gf′ ⊗₁ Agen gf) ⊗₁ (Agen gg′ ⊗₁ Agen gg)

BoxR : HomTerm (((b⁺ ⊗₀ d⁻) ⊗₀ (q⁺ ⊗₀ r⁻)) ⊗₀ ((a⁺ ⊗₀ b⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
               (((b⁻ ⊗₀ d⁺) ⊗₀ (q⁻ ⊗₀ r⁺)) ⊗₀ ((a⁻ ⊗₀ b⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
BoxR = (Agen gf′ ⊗₁ Agen gg′) ⊗₁ (Agen gf ⊗₁ Agen gg)

Lout : HomTerm (((b⁻ ⊗₀ d⁺) ⊗₀ (a⁻ ⊗₀ b⁺)) ⊗₀ ((q⁻ ⊗₀ r⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
               (W′ ⊗₀ (X ⊗₀ Y))
Lout = midᵗ ⊗₁ id ∘ midᵗ ∘ αᵗ ⊗₁ αᵗ

Lin : HomTerm (W ⊗₀ (X ⊗₀ Y)) (((b⁺ ⊗₀ d⁻) ⊗₀ (a⁺ ⊗₀ b⁻)) ⊗₀ ((q⁺ ⊗₀ r⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
Lin = γᵗ ⊗₁ γᵗ ∘ midᵗ ∘ midᵗ ⊗₁ id

Rout : HomTerm (((b⁻ ⊗₀ d⁺) ⊗₀ (q⁻ ⊗₀ r⁺)) ⊗₀ ((a⁻ ⊗₀ b⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
               (W′ ⊗₀ (X ⊗₀ Y))
Rout = id ⊗₁ midᵗ ∘ αᵗ ∘ midᵗ ⊗₁ midᵗ

Rin : HomTerm (W ⊗₀ (X ⊗₀ Y)) (((b⁺ ⊗₀ d⁻) ⊗₀ (q⁺ ⊗₀ r⁻)) ⊗₀ ((a⁺ ⊗₀ b⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
Rin = midᵗ ⊗₁ midᵗ ∘ γᵗ ∘ id ⊗₁ midᵗ

-- Spelled exactly as `homomorphismᴳ`'s `residue` step states them.
lhs rhs : HomTerm (W ⊗₀ (X ⊗₀ Y)) (W′ ⊗₀ (X ⊗₀ Y))
lhs = midᵗ ⊗₁ id ∘ (midᵗ ∘ (αᵗ ⊗₁ αᵗ ∘ BoxL ∘ γᵗ ⊗₁ γᵗ) ∘ midᵗ) ∘ midᵗ ⊗₁ id
rhs = id ⊗₁ midᵗ ∘ (αᵗ ∘ (midᵗ ⊗₁ midᵗ ∘ BoxR ∘ midᵗ ⊗₁ midᵗ) ∘ γᵗ) ∘ id ⊗₁ midᵗ

ob-out : Lout ≈Term (Rout ∘ midᵗ)
ob-out = solve! Lout (Rout ∘ midᵗ) refl

ob-in : Lin ≈Term (midᵗ ∘ Rin)
ob-in = solve! Lin (midᵗ ∘ Rin) refl

ob-nat : (midᵗ ∘ BoxL ∘ midᵗ) ≈Term BoxR
ob-nat = pullˡ (IB.swapInner-natural (Symmetric.braided Symmetric-Monoidal))
       ○ cancelʳ (IS.swapInner-commutative Symmetric-Monoidal)

coh : lhs ≈Term rhs
coh = stepR! lhs (Lout ∘ BoxL ∘ Lin) refl
    ○ ob-out ⟩∘⟨ (refl⟩∘⟨ ob-in)
    ○ stepR! ((Rout ∘ midᵗ) ∘ BoxL ∘ midᵗ ∘ Rin) (Rout ∘ (midᵗ ∘ BoxL ∘ midᵗ) ∘ Rin) refl
    ○ refl⟩∘⟨ (ob-nat ⟩∘⟨refl)
    ○ stepR! (Rout ∘ BoxR ∘ Rin) rhs refl

private module IM = Interp sig

module Transport {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : C.Obj)
  where

  ⟦_⟧ᵖ₀ : Fin 12 → C.Obj
  ⟦ 0F ⟧ᵖ₀  = A⁺ ; ⟦ 1F ⟧ᵖ₀  = A⁻ ; ⟦ 2F ⟧ᵖ₀  = B⁺ ; ⟦ 3F ⟧ᵖ₀  = B⁻
  ⟦ 4F ⟧ᵖ₀  = D⁺ ; ⟦ 5F ⟧ᵖ₀  = D⁻ ; ⟦ 6F ⟧ᵖ₀  = P⁺ ; ⟦ 7F ⟧ᵖ₀  = P⁻
  ⟦ 8F ⟧ᵖ₀  = Q⁺ ; ⟦ 9F ⟧ᵖ₀  = Q⁻ ; ⟦ 10F ⟧ᵖ₀ = R⁺ ; ⟦ 11F ⟧ᵖ₀ = R⁻

  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  module WithGens (f₀  : OI.⟦ a⁺ ⊗₀ b⁻ ⟧₀ C.⇒ OI.⟦ a⁻ ⊗₀ b⁺ ⟧₀)
                  (f₀′ : OI.⟦ b⁺ ⊗₀ d⁻ ⟧₀ C.⇒ OI.⟦ b⁻ ⊗₀ d⁺ ⟧₀)
                  (g₀  : OI.⟦ p⁺ ⊗₀ q⁻ ⟧₀ C.⇒ OI.⟦ p⁻ ⊗₀ q⁺ ⟧₀)
                  (g₀′ : OI.⟦ q⁺ ⊗₀ r⁻ ⟧₀ C.⇒ OI.⟦ q⁻ ⊗₀ r⁺ ⟧₀) where

    ⟦_⟧ᵖ₁ : ∀ {x y} → Mor x y → OI.⟦ x ⟧₀ C.⇒ OI.⟦ y ⟧₀
    ⟦ gf ⟧ᵖ₁ = f₀ ; ⟦ gf′ ⟧ᵖ₁ = f₀′ ; ⟦ gg ⟧ᵖ₁ = g₀ ; ⟦ gg′ ⟧ᵖ₁ = g₀′

    open IM.Solver C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

    HOM : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
    HOM = Functor.F-resp-≈ freeFunctor coh

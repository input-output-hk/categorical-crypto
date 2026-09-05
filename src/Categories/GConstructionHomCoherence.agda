{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The coherence residue of the G-construction tensor's homomorphism law, over a
-- 12-atom signature with the four generators the law mentions.
--
-- `(f′ ∘ᴳ f) ⊗₁ᴳ (g′ ∘ᴳ g) ≈ (f′ ⊗₁ᴳ g′) ∘ᴳ (f ⊗₁ᴳ g)` compares two loops: on
-- the left, `⊗-trace-mid` fuses the two composites' loops `b⁻⊗b⁺` and `q⁻⊗q⁺`
-- into one and the tensor's two `mid`s are pushed inside; on the right,
-- `trace-mid` re-brackets the single loop `(b⁻⊗q⁻)⊗(b⁺⊗q⁺)` to the same
-- `(b⁻⊗b⁺)⊗(q⁻⊗q⁺)`.  What is left is one equation between the loop bodies —
-- pure symmetric-monoidal coherence, no trace law in it.
--
-- Solving it whole is out of reach (measured: no answer in 900 s at ~50 boxes a
-- side).  It splits, though, along the ONE place where the two sides really
-- differ: both apply the same four boxes, the left as `(f′⊗f) ⊗ (g′⊗g)` and the
-- right as `(f′⊗g′) ⊗ (f⊗g)`, and those two are conjugate by `mid`.  So
--
--   ob-out : Lᵒᵘᵗ ≈ Rᵒᵘᵗ ∘ mid          (no generators)
--   ob-nat : mid ∘ BoxL ∘ mid ≈ BoxR    (`mid`'s naturality, four one-box legs)
--   ob-in  : Lⁱⁿ ≈ mid ∘ Rⁱⁿ            (no generators)
--
-- paste into `coh` by congruence, with the re-bracketings bridged by the
-- pure-assoc respelling `stepR!` (no solver leaf).
--------------------------------------------------------------------------------

module Categories.GConstructionHomCoherence where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
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
  using (FreeMonoidal; HomTerm; Agen; id; _∘_; _⊗₁_; σ; α⇒; α⇐; _≈Term_)

open import Categories.APROP.Hypergraph.Solver.Split sig
  using () renaming (stepSplitR! to stepR!; solveTerm!ᵀ to solve!)

open Category.HomReasoning FreeMonoidal using (_○_; _⟩∘⟨_; _⟩∘⟨refl; refl⟩∘⟨_)

-- The free twins of `GConstructionTrace`'s wiring.
αᵗ : ∀ {A⁻ B⁺ B⁻ C⁺} →
     HomTerm ((B⁻ ⊗₀ C⁺) ⊗₀ (A⁻ ⊗₀ B⁺)) ((A⁻ ⊗₀ C⁺) ⊗₀ (B⁻ ⊗₀ B⁺))
αᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γᵗ : ∀ {A⁺ B⁺ B⁻ C⁻} →
     HomTerm ((A⁺ ⊗₀ C⁻) ⊗₀ (B⁻ ⊗₀ B⁺)) ((B⁺ ⊗₀ C⁻) ⊗₀ (A⁺ ⊗₀ B⁻))
γᵗ = α⇒ ∘ σ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ

midᵗ : ∀ {P Q R S} → HomTerm ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
midᵗ = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ ⊗₁ id ∘ α⇐) ∘ α⇒

-- The two composites' loops (`X`/`Y` — the fused loop is `X ⊗ Y`) and the
-- tensor's interfaces (`W`/`W′`).
X Y W W′ : ObjTerm
X = b⁻ ⊗₀ b⁺                  ; Y  = q⁻ ⊗₀ q⁺
W = (a⁺ ⊗₀ p⁺) ⊗₀ (d⁻ ⊗₀ r⁻) ; W′ = (a⁻ ⊗₀ p⁻) ⊗₀ (d⁺ ⊗₀ r⁺)

-- The four boxes, grouped the two ways the two sides group them.
BoxL : HomTerm (((b⁺ ⊗₀ d⁻) ⊗₀ (a⁺ ⊗₀ b⁻)) ⊗₀ ((q⁺ ⊗₀ r⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
               (((b⁻ ⊗₀ d⁺) ⊗₀ (a⁻ ⊗₀ b⁺)) ⊗₀ ((q⁻ ⊗₀ r⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
BoxL = (Agen gf′ ⊗₁ Agen gf) ⊗₁ (Agen gg′ ⊗₁ Agen gg)

BoxR : HomTerm (((b⁺ ⊗₀ d⁻) ⊗₀ (q⁺ ⊗₀ r⁻)) ⊗₀ ((a⁺ ⊗₀ b⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
               (((b⁻ ⊗₀ d⁺) ⊗₀ (q⁻ ⊗₀ r⁺)) ⊗₀ ((a⁻ ⊗₀ b⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
BoxR = (Agen gf′ ⊗₁ Agen gg′) ⊗₁ (Agen gf ⊗₁ Agen gg)

-- The wiring around them: left of / right of the boxes on each side.
Lout : HomTerm (((b⁻ ⊗₀ d⁺) ⊗₀ (a⁻ ⊗₀ b⁺)) ⊗₀ ((q⁻ ⊗₀ r⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
               (W′ ⊗₀ (X ⊗₀ Y))
Lout = midᵗ ⊗₁ id ∘ midᵗ ∘ αᵗ ⊗₁ αᵗ

Lin : HomTerm (W ⊗₀ (X ⊗₀ Y))
              (((b⁺ ⊗₀ d⁻) ⊗₀ (a⁺ ⊗₀ b⁻)) ⊗₀ ((q⁺ ⊗₀ r⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
Lin = γᵗ ⊗₁ γᵗ ∘ midᵗ ∘ midᵗ ⊗₁ id

Rout : HomTerm (((b⁻ ⊗₀ d⁺) ⊗₀ (q⁻ ⊗₀ r⁺)) ⊗₀ ((a⁻ ⊗₀ b⁺) ⊗₀ (p⁻ ⊗₀ q⁺)))
               (W′ ⊗₀ (X ⊗₀ Y))
Rout = id ⊗₁ midᵗ ∘ αᵗ ∘ midᵗ ⊗₁ midᵗ

Rin : HomTerm (W ⊗₀ (X ⊗₀ Y))
              (((b⁺ ⊗₀ d⁻) ⊗₀ (q⁺ ⊗₀ r⁻)) ⊗₀ ((a⁺ ⊗₀ b⁻) ⊗₀ (p⁺ ⊗₀ q⁻)))
Rin = midᵗ ⊗₁ midᵗ ∘ γᵗ ∘ id ⊗₁ midᵗ

-- The two sides, spelled as the semantic chain leaves them (the tensor's
-- `mid`s outside, `Φ₁ ⊗ Φ₂` resp. the tensor's two factors expanded by
-- ⊗-∘-distributivity).
lhs rhs : HomTerm (W ⊗₀ (X ⊗₀ Y)) (W′ ⊗₀ (X ⊗₀ Y))
lhs = midᵗ ⊗₁ id ∘ (midᵗ ∘ (αᵗ ⊗₁ αᵗ ∘ BoxL ∘ γᵗ ⊗₁ γᵗ) ∘ midᵗ) ∘ midᵗ ⊗₁ id
rhs = id ⊗₁ midᵗ ∘ (αᵗ ∘ (midᵗ ⊗₁ midᵗ ∘ BoxR ∘ midᵗ ⊗₁ midᵗ) ∘ γᵗ) ∘ id ⊗₁ midᵗ

ob-out : Lout ≈Term (Rout ∘ midᵗ)
ob-out = solve! Lout (Rout ∘ midᵗ) refl

ob-in : Lin ≈Term (midᵗ ∘ Rin)
ob-in = solve! Lin (midᵗ ∘ Rin) refl

ob-nat : (midᵗ ∘ BoxL ∘ midᵗ) ≈Term BoxR
ob-nat = solve! (midᵗ ∘ BoxL ∘ midᵗ) BoxR refl

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

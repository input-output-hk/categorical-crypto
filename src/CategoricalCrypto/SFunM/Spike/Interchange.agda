{-# OPTIONS --safe --without-K #-}

-- SPIKE: what the general `trace-∘` needs.
--
-- Composing machines pairs their states; unrolling them pairs their interfaces.
-- `trace-∘` says the two pairings commute, and its content is the interchange
-- of two actions that touch complementary tensor factors — at `𝒱 = Kleisli M`
-- that interchange IS the monad's commutativity, which is why the elementwise
-- layer needs `Discrete.Commutative` for exactly this lemma and nothing else.
--
-- Everything below is discharged by the repo's symmetric-monoidal solver
-- (`solveMorσ!`).  The three identities it does not decide are the documented
-- `lim-straddle` case (a generator taking one wire from each side of a
-- crossing); see the report for their statements.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Frontend.Sigma
open import Categories.Coherence.Monoidal.Sigma
open import Categories.FreeMonoidal
import Categories.Coherence.Monoidal as Coh

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (_∷_; [])

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Interchange {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Mealy 𝒱

-- The solver front-end wants the `MonoidalCategory` bundle.
𝕄 : MonoidalCategory o ℓ e
𝕄 = record { U = U ; monoidal = monoidal }

------------------------------------------------------------------------
-- Solver terms mirroring the combinators of `Spike.Mealy`
------------------------------------------------------------------------

-- One generator `k : P ⊗ X ⇒ P ⊗ Y`, four object atoms besides.
module OneGen (P Q X Y Z : Obj) (k : P ⊗₀ X ⇒ P ⊗₀ Y) where

  vars = P ∷ Q ∷ X ∷ Y ∷ Z ∷ []
  open Coh.SymAtoms 𝕄 symmetric vars

  private
    p q x y z : ObjTerm
    p = V zero
    q = V (suc zero)
    x = V (suc (suc zero))
    y = V (suc (suc (suc zero)))
    z = V (suc (suc (suc (suc zero))))

  open Coh.SymSolve 𝕄 symmetric vars (((p ⊗ᵒ x , p ⊗ᵒ y) , k) ∷ [])

  private
    k′ = gen zero

    swpT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ w) ((u ⊗ᵒ w) ⊗ᵒ v)
    swpT u v w = S.α⇐ S.∘ S.id S.⊗₁ S.σ {v} {w} S.∘ S.α⇒ {u} {v} {w}

    onLT : (u v s t : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
         → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ s) ((u ⊗ᵒ v) ⊗ᵒ t)
    onLT u v s t h = swpT u t v S.∘ h S.⊗₁ S.id {v} S.∘ swpT u v s

    slot₁T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (s ⊗ᵒ w)) (u ⊗ᵒ (t ⊗ᵒ w))
    slot₁T u s t w h = S.α⇒ {u} {t} {w} S.∘ h S.⊗₁ S.id {w} S.∘ S.α⇐ {u} {s} {w}

    ΩT : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    ΩT u v s w = S.α⇒ {u ⊗ᵒ s} {v} {w} S.∘ swpT u v s S.⊗₁ S.id {w}
           S.∘ S.α⇐ {u ⊗ᵒ v} {s} {w}

    Ω′T : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    Ω′T u v s w = S.α⇐ {u} {s} {v ⊗ᵒ w}
      S.∘ S.id {u} S.⊗₁ (S.α⇒ {s} {v} {w} S.∘ S.σ {v} {s} S.⊗₁ S.id {w} S.∘ S.α⇐ {v} {s} {w})
      S.∘ S.α⇒ {u} {v} {s ⊗ᵒ w}

  -- The left state factor acting on interface slot 1 is an `Ω`-conjugate: this
  -- is the half of the interchange the solver decides.
  slot₁-onL : slot₁ {Z = Z} (onL {Q = Q} k) ≈ Ω ∘ k ⊗₁ id ∘ Ω
  slot₁-onL = solveMorσ! (slot₁T (p ⊗ᵒ q) x y z (onLT p q x y k′))
                         (ΩT p y q z S.∘ k′ S.⊗₁ S.id {q ⊗ᵒ z} S.∘ ΩT p q x z)

  -- `Ω` agrees with upstream's `swapInner` (which braids inside the interface
  -- pair rather than the state pair) and is its own inverse.
  Ω≈Ω′ : Ω {P} {Q} {X} {Z} ≈ α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒
  Ω≈Ω′ = solveMorσ! (ΩT p q x z) (Ω′T p q x z)

  Ω-involutive : Ω {P} {X} {Q} {Z} ∘ Ω {P} {Q} {X} {Z} ≈ id
  Ω-involutive = solveMorσ! (ΩT p x q z S.∘ ΩT p q x z) (S.id {(p ⊗ᵒ q) ⊗ᵒ (x ⊗ᵒ z)})

-- The right state factor's actions commute with both interface slots.
module OneGenʳ (P Q X Y Z : Obj) (k : Q ⊗₀ X ⇒ Q ⊗₀ Y) where

  vars = P ∷ Q ∷ X ∷ Y ∷ Z ∷ []
  open Coh.SymAtoms 𝕄 symmetric vars

  private
    p q x y z : ObjTerm
    p = V zero
    q = V (suc zero)
    x = V (suc (suc zero))
    y = V (suc (suc (suc zero)))
    z = V (suc (suc (suc (suc zero))))

  open Coh.SymSolve 𝕄 symmetric vars (((q ⊗ᵒ x , q ⊗ᵒ y) , k) ∷ [])

  private
    k′ = gen zero

    onRT : (u v s t : ObjTerm) → S.HomTerm (v ⊗ᵒ s) (v ⊗ᵒ t)
         → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ s) ((u ⊗ᵒ v) ⊗ᵒ t)
    onRT u v s t h = S.α⇐ {u} {v} {t} S.∘ S.id {u} S.⊗₁ h S.∘ S.α⇒ {u} {v} {s}

    slot₁T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (s ⊗ᵒ w)) (u ⊗ᵒ (t ⊗ᵒ w))
    slot₁T u s t w h = S.α⇒ {u} {t} {w} S.∘ h S.⊗₁ S.id {w} S.∘ S.α⇐ {u} {s} {w}

    slot₂T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (w ⊗ᵒ s)) (u ⊗ᵒ (w ⊗ᵒ t))
    slot₂T u s t w h = (S.id {u} S.⊗₁ S.σ {t} {w} S.∘ S.α⇒ {u} {t} {w})
                 S.∘ h S.⊗₁ S.id {w} S.∘ (S.α⇐ {u} {s} {w} S.∘ S.id {u} S.⊗₁ S.σ {w} {s})

  slot₁-onR : slot₁ {Z = Z} (onR {P = P} k) ≈ onR (slot₁ k)
  slot₁-onR = solveMorσ! (slot₁T (p ⊗ᵒ q) x y z (onRT p q x y k′))
                         (onRT p q (x ⊗ᵒ z) (y ⊗ᵒ z) (slot₁T q x y z k′))

  slot₂-onR : slot₂ {Z = Z} (onR {P = P} k) ≈ onR (slot₂ k)
  slot₂-onR = solveMorσ! (slot₂T (p ⊗ᵒ q) x y z (onRT p q x y k′))
                         (onRT p q (z ⊗ᵒ x) (z ⊗ᵒ y) (slot₂T q x y z k′))

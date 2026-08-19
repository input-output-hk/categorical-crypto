{-# OPTIONS --safe --without-K #-}

-- SPIKE: `Maybe` on `Setoids` as a *commutative* monad for the cartesian tensor.
--
-- This is the one input to `Categories.Category.Monoidal.Construction.Kleisli`
-- that is not upstream, and the only thing standing between `Setoids` and a
-- symmetric monoidal `Kleisli M` for `Spike.Mealy` to run on.  The strength is
-- `(a , nothing) ↦ nothing`, `(a , just b) ↦ just (a , b)`; it is a setoid map
-- at *general* setoids, so — unlike `Spike.KleisliDiscrete` — nothing here
-- needs the objects to be discrete.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian; Setoids-Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (Commutative; CommutativeMonad)
open import Categories.Monad.Construction.Kleisli using (Kleisli⇒Monad)
open import Categories.Monad.Setoids.Maybe using (Maybe-KleisliTriple)
open import Categories.Monad.Strong using (Strength; StrongMonad)
open import Categories.NaturalTransformation using (ntHelper)
import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric

open import Data.Maybe.Base using (Maybe; just; nothing; map)
import Data.Maybe.Relation.Binary.Pointwise as Pw
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function.Bundles using (Func)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)

module CategoricalCrypto.SFunM.Spike.CommutativeMaybe (ℓ : Level) where

open Setoid using (Carrier)

private variable A A′ B B′ C : Setoid ℓ ℓ

Setoids-Symmetric : Symmetric (Setoids-Monoidal {ℓ} {ℓ})
Setoids-Symmetric = CartesianSymmetric.symmetric (Setoids ℓ ℓ) Setoids-Cartesian

Maybe-Monad : Monad (Setoids ℓ ℓ)
Maybe-Monad = Kleisli⇒Monad (Setoids ℓ ℓ) Maybe-KleisliTriple

------------------------------------------------------------------------
-- The strength

-- Projections rather than a pattern-matching lambda, so that the structural
-- morphisms of `Kleisli-Monoidal` still compute on closed inputs.
σᴹᵇ : Func (A ×ₛ Pw.setoid B) (Pw.setoid (A ×ₛ B))
σᴹᵇ {A} {B} = record { to = λ p → map (proj₁ p ,_) (proj₂ p) ; cong = λ {p} {q} (a≈b , m≈n) → congσ (proj₂ p) (proj₂ q) a≈b m≈n }
  where
  congσ : {a b : Carrier A} (m n : Maybe (Carrier B))
        → Setoid._≈_ A a b → Pw.Pointwise (Setoid._≈_ B) m n
        → Pw.Pointwise (Setoid._≈_ (A ×ₛ B)) (map (a ,_) m) (map (b ,_) n)
  congσ (just _) (just _) a≈b (Pw.just x≈y) = Pw.just (a≈b , x≈y)
  congσ nothing  nothing  _   Pw.nothing    = Pw.nothing

Maybe-Strength : Strength Setoids-Monoidal Maybe-Monad
Maybe-Strength = record
  { strengthen     = ntHelper record
      { η       = λ _ → σᴹᵇ
      ; commute = λ {_} {(A′ , B′)} _ → λ where
          {_ , just _}  → Pw.just (Setoid.refl (A′ ×ₛ B′))
          {_ , nothing} → Pw.nothing
      }
  ; identityˡ      = λ {A} → λ where
      {_ , just _}  → Pw.just (Setoid.refl A)
      {_ , nothing} → Pw.nothing
  ; η-comm         = λ {A} {B} → Pw.just (Setoid.refl (A ×ₛ B))
  ; μ-η-comm       = λ {A} {B} → λ where
      {_ , just (just _)} → Pw.just (Setoid.refl (A ×ₛ B))
      {_ , just nothing}  → Pw.nothing
      {_ , nothing}       → Pw.nothing
  ; strength-assoc = λ {A} {B} {C} → λ where
      {_ , just _}  → Pw.just (Setoid.refl (A ×ₛ (B ×ₛ C)))
      {_ , nothing} → Pw.nothing
  }

Maybe-StrongMonad : StrongMonad (Setoids-Monoidal {ℓ} {ℓ})
Maybe-StrongMonad = record { M = Maybe-Monad ; strength = Maybe-Strength }

------------------------------------------------------------------------
-- Commutativity

-- Both sides send `(just x , just y)` to `just (x , y)` and every other pair to
-- `nothing`; the effect order the law is about is invisible for `Maybe`.
Maybe-Commutative : Commutative (Symmetric.braided Setoids-Symmetric) Maybe-StrongMonad
Maybe-Commutative = record
  { commutes = λ {X} {Y} → λ where
      {just _ , just _}  → Pw.just (Setoid.refl (X ×ₛ Y))
      {just _ , nothing} → Pw.nothing
      {nothing , just _} → Pw.nothing
      {nothing , nothing} → Pw.nothing
  }

Maybe-CommutativeMonad : CommutativeMonad (Symmetric.braided Setoids-Symmetric)
Maybe-CommutativeMonad = record { strongMonad = Maybe-StrongMonad ; commutative = Maybe-Commutative }

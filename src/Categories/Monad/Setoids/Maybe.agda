{-# OPTIONS --safe --without-K #-}

-- `Maybe` as a monad on `Setoids`, up to the element setoid's own equality, and as a
-- commutative monad for the cartesian tensor.

open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Instance.Setoids
open import Categories.Category.Monoidal.Symmetric
open import Categories.Monad
open import Categories.Monad.Commutative
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Discrete
open import Categories.Monad.Strong
open import Categories.NaturalTransformation
import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric
import Categories.Monad.Setoids.Discrete as Discrete

open import Data.Maybe
open import Data.Maybe.Relation.Binary.Pointwise as Pw
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function.Bundles
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module Categories.Monad.Setoids.Maybe where

open Setoid

private
  variable
    ℓ ℓ′ ℓ″ : Level
    S : Setoid ℓ ℓ
    S′ : Setoid ℓ′ ℓ′
    S″ : Setoid ℓ″ ℓ″
    A A′ B B′ C : Setoid ℓ ℓ

  ≈ᴹᵇ : (S : Setoid ℓ ℓ) → Maybe (Carrier S) → Maybe (Carrier S) → Set ℓ
  ≈ᴹᵇ S = Pointwise (Setoid._≈_ S)

  >>=-congᴹᵇ : {x y : Maybe (Carrier S)} {f g : Carrier S → Maybe (Carrier S′)}
             → ≈ᴹᵇ S x y → (∀ {a b} → Setoid._≈_ S a b → ≈ᴹᵇ S′ (f a) (g b))
             → ≈ᴹᵇ S′ (x >>= f) (y >>= g)
  >>=-congᴹᵇ (Pw.just a≈b) f≈g = f≈g a≈b
  >>=-congᴹᵇ Pw.nothing    _   = Pw.nothing

Maybe-KleisliTriple : KleisliTriple (Setoids ℓ ℓ)
Maybe-KleisliTriple = record
  { F₀        = Pw.setoid
  ; unit      = record { to = just ; cong = Pw.just }
  ; extend    = λ {S} {S′} f → record
      { to   = _>>= (f ⟨$⟩_)
      ; cong = λ x≈y → >>=-congᴹᵇ {S = S} {S′ = S′} x≈y (Func.cong f)
      }
  ; identityʳ = λ {_} {S′} → Pw.refl (Setoid.refl S′)
  ; identityˡ = λ {S} → λ where
      {just _}  → Pw.just (Setoid.refl S)
      {nothing} → Pw.nothing
  ; assoc     = λ {S} {S′} {S″} {k} {l} {x} → Setoid.sym (Pw.setoid S″)
      (assocᴹᵇ {k = k} {l = l} x)
  ; sym-assoc = λ {S} {S′} {S″} {k} {l} {x} →
      assocᴹᵇ {k = k} {l = l} x
  ; extend-≈  = λ {S} {S′} {k} {h} k≈h {x} →
      >>=-congᴹᵇ {S = S} {S′ = S′} {y = x}
                 (Pw.refl (Setoid.refl S)) λ a≈b →
        Setoid.trans (Pw.setoid S′) k≈h (Func.cong h a≈b)
  }
  where
  assocᴹᵇ : {k : Func S (Pw.setoid S′)} {l : Func S′ (Pw.setoid S″)}
            (x : Maybe (Carrier S))
          → ≈ᴹᵇ S″ ((x >>= (k ⟨$⟩_)) >>= (l ⟨$⟩_)) (x >>= λ a → (k ⟨$⟩ a) >>= (l ⟨$⟩_))
  assocᴹᵇ {S″ = S″} (just _) = Pw.refl (Setoid.refl S″)
  assocᴹᵇ           nothing  = Pw.nothing

Maybe-DiscreteMonad : DiscreteMonad ℓ
Maybe-DiscreteMonad = record
  { elementwise = Discrete.elementwise Maybe-KleisliTriple
  ; >>=-comm    = λ where
      {x = just _}  {y = just _}  → Pw.refl (Setoid.refl (≡-setoid _))
      {x = just _}  {y = nothing} → Pw.nothing
      {x = nothing} {y = just _}  → Pw.nothing
      {x = nothing} {y = nothing} → Pw.nothing
  }

Setoids-Symmetric : Symmetric (Setoids-Monoidal {ℓ} {ℓ})
Setoids-Symmetric = CartesianSymmetric.symmetric (Setoids _ _) Setoids-Cartesian

Maybe-Monad : Monad (Setoids ℓ ℓ)
Maybe-Monad = Kleisli⇒Monad (Setoids _ _) Maybe-KleisliTriple

-- Projections rather than a pattern-matching lambda: see
-- `Categories.Category.Construction.Kleisli.Discrete._⊗ᵏ_`.
σᴹᵇ : Func (A ×ₛ Pw.setoid B) (Pw.setoid (A ×ₛ B))
σᴹᵇ {A = A} {B = B} = record
  { to   = λ p → map (proj₁ p ,_) (proj₂ p)
  ; cong = λ {p} {q} (a≈b , m≈n) → congσ (proj₂ p) (proj₂ q) a≈b m≈n
  }
  where
  congσ : {a b : Carrier A} (m n : Maybe (Carrier B))
        → Setoid._≈_ A a b → Pointwise (Setoid._≈_ B) m n
        → Pointwise (Setoid._≈_ (A ×ₛ B)) (map (a ,_) m) (map (b ,_) n)
  congσ (just _) (just _) a≈b (Pw.just x≈y) = Pw.just (a≈b , x≈y)
  congσ nothing  nothing  _   Pw.nothing    = Pw.nothing

Maybe-Strength : Strength Setoids-Monoidal (Maybe-Monad {ℓ})
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

Maybe-StrongMonad : StrongMonad (Setoids-Monoidal {ℓ})
Maybe-StrongMonad = record { M = Maybe-Monad ; strength = Maybe-Strength }

Maybe-CommutativeMonad : CommutativeMonad (Symmetric.braided (Setoids-Symmetric {ℓ}))
Maybe-CommutativeMonad = record
  { strongMonad = Maybe-StrongMonad
  ; commutative = record
      { commutes = λ {X} {Y} → λ where
          {just _ , just _}   → Pw.just (Setoid.refl (X ×ₛ Y))
          {just _ , nothing}  → Pw.nothing
          {nothing , just _}  → Pw.nothing
          {nothing , nothing} → Pw.nothing
      }
  }

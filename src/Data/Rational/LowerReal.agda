{-# OPTIONS --safe --without-K #-}

-- Lower reals presented by rational sequences: `Cut x` is the lower real (a rounded,
-- down-closed set of rationals; Coquand–Spitters, *Integrals and valuations*,
-- J. Logic & Analysis 1 (2009), Def. 1) that `x : ℕ → ℚ` presents, `_≲_` is inclusion of
-- cuts and `_≈_` their equality. The exact order `_≼_` is strictly finer than `_≲_`.

import Algebra.Properties.Group as GroupProperties
open import Data.Nat
open import Data.Product
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Function.Bundles
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

module Data.Rational.LowerReal where

open GroupProperties +-0-group

private variable
  x y z : ℕ → ℚ
  δ δ′ p q : ℚ

infix 4 _≼_ _≼[_]_ _≲_ _≈_ _≤ℚ_

-- The lemmas take their sequences explicitly: the relations unfold to a Π, so a
-- sequence is never inferable from the type (a `cum` instance strands the meta).

_≼_ : (ℕ → ℚ) → (ℕ → ℚ) → Set
x ≼ y = (n : ℕ) → Σ[ m ∈ ℕ ] x n ℚ.≤ y m

_≼[_]_ : (ℕ → ℚ) → ℚ → (ℕ → ℚ) → Set
x ≼[ δ ] y = x ≼ (λ m → y m ℚ.+ δ)

≼-refl : (x : ℕ → ℚ) → x ≼ x
≼-refl x n = n , ≤-refl

≼-trans : (x y z : ℕ → ℚ) → x ≼ y → y ≼ z → x ≼ z
≼-trans x y z xy yz n = let m , le = xy n ; i , le′ = yz m in i , ≤-trans le le′

≼-mapʳ : (x y y′ : ℕ → ℚ) → (∀ m → y m ℚ.≤ y′ m) → x ≼ y → x ≼ y′
≼-mapʳ x y y′ f xy n = let m , le = xy n in m , ≤-trans le (f m)

≼-+ʳ : (y y′ : ℕ → ℚ) (δ : ℚ) → y ≼ y′ → (λ m → y m ℚ.+ δ) ≼ (λ m → y′ m ℚ.+ δ)
≼-+ʳ y y′ δ yy n = let m , le = yy n in m , +-monoˡ-≤ δ le

≼⇒≼[0] : (x y : ℕ → ℚ) → x ≼ y → x ≼[ 0ℚ ] y
≼⇒≼[0] x y = ≼-mapʳ x y _ λ m → ≤-reflexive (sym (+-identityʳ (y m)))

≼[]-refl : (x : ℕ → ℚ) → 0ℚ ℚ.≤ δ → x ≼[ δ ] x
≼[]-refl x 0≤δ =
  ≼-mapʳ x x _ (λ m → ≤-trans (≤-reflexive (sym (+-identityʳ (x m)))) (+-monoʳ-≤ (x m) 0≤δ)) (≼-refl x)

≼[]-mono : (x y : ℕ → ℚ) → δ ℚ.≤ δ′ → x ≼[ δ ] y → x ≼[ δ′ ] y
≼[]-mono x y le = ≼-mapʳ x _ _ λ m → +-monoʳ-≤ (y m) le

≼[]-trans : (x y z : ℕ → ℚ) → x ≼[ δ ] y → y ≼[ δ′ ] z → x ≼[ δ ℚ.+ δ′ ] z
≼[]-trans {δ = δ} {δ′ = δ′} x y z p q =
  ≼-mapʳ x _ _ (λ i → ≤-reflexive (trans (+-assoc (z i) δ′ δ) (cong (z i ℚ.+_) (+-comm δ′ δ))))
         (≼-trans x _ _ p (≼-+ʳ y _ δ q))

≼[]-resp : (x x′ y y′ : ℕ → ℚ) → x′ ≼ x → y ≼ y′ → x ≼[ δ ] y → x′ ≼[ δ ] y′
≼[]-resp {δ = δ} x x′ y y′ l r p = ≼-trans x′ x _ l (≼-trans x _ _ p (≼-+ʳ y y′ δ r))

_≲_ : Rel (ℕ → ℚ) 0ℓ
x ≲ y = (δ : ℚ) → 0ℚ ℚ.< δ → x ≼[ δ ] y

≼⇒≲ : (x y : ℕ → ℚ) → x ≼ y → x ≲ y
≼⇒≲ x y h δ δ>0 = ≼[]-mono x y (<⇒≤ δ>0) (≼⇒≼[0] x y h)

_≈_ : Rel (ℕ → ℚ) 0ℓ
x ≈ y = (δ : ℚ) → 0ℚ ℚ.< δ → x ≼[ δ ] y × y ≼[ δ ] x

private
  halves : (δ : ℚ) → ½ ℚ.* δ ℚ.+ ½ ℚ.* δ ≡ δ
  halves δ = subst (_≡ δ) (*-distribʳ-+ δ ½ ½) (*-identityˡ δ)

  half-pos : 0ℚ ℚ.< δ → 0ℚ ℚ.< ½ ℚ.* δ
  half-pos {δ} δ>0 = positive⁻¹ _ ⦃ pos*pos⇒pos ½ δ ⦃ ℚ.positive δ>0 ⦄ ⦄

≈-trans : x ≈ y → y ≈ z → x ≈ z
≈-trans {x} {y} {z} h k δ δ>0 =
  let xy , yx = h (½ ℚ.* δ) (half-pos δ>0) ; yz , zy = k (½ ℚ.* δ) (half-pos δ>0)
  in subst (x ≼[_] z) (halves δ) (≼[]-trans x y z xy yz)
   , subst (z ≼[_] x) (halves δ) (≼[]-trans z y x zy yx)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = λ {x} δ δ>0 → ≼[]-refl x (<⇒≤ δ>0) , ≼[]-refl x (<⇒≤ δ>0)
  ; sym   = λ h δ δ>0 → let xy , yx = h δ δ>0 in yx , xy
  ; trans = ≈-trans }

LowerReal : Setoid 0ℓ 0ℓ
LowerReal = record { Carrier = ℕ → ℚ ; _≈_ = _≈_ ; isEquivalence = ≈-isEquivalence }

≈⇒≲ : (x y : ℕ → ℚ) → x ≈ y → x ≲ y
≈⇒≲ x y h δ δ>0 = proj₁ (h δ δ>0)

_≤ℚ_ : (ℕ → ℚ) → ℚ → Set
x ≤ℚ q = (n : ℕ) → x n ℚ.≤ q

≲-≤ℚ : (x y : ℕ → ℚ) → x ≲ y → y ≤ℚ q → (δ : ℚ) → 0ℚ ℚ.< δ → x ≤ℚ q ℚ.+ δ
≲-≤ℚ x y h le δ δ>0 n = let m , xn≤ = h δ δ>0 n in ≤-trans xn≤ (+-monoˡ-≤ δ (le m))

------------------------------------------------------------------------
-- Cuts
------------------------------------------------------------------------

Cut : (ℕ → ℚ) → Pred ℚ 0ℓ
Cut x q = Σ[ n ∈ ℕ ] q ℚ.< x n

Cut-down : (x : ℕ → ℚ) → p ℚ.≤ q → Cut x q → Cut x p
Cut-down x p≤q (n , q<xn) = n , ≤-<-trans p≤q q<xn

Cut-rounded : (x : ℕ → ℚ) → Cut x q → Σ[ p ∈ ℚ ] q ℚ.< p × Cut x p
Cut-rounded x (n , q<xn) = let p , q<p , p<xn = <-dense q<xn in p , q<p , n , p<xn

≲⇒Cut-⊆ : (x y : ℕ → ℚ) → x ≲ y → Cut x ⊆ Cut y
≲⇒Cut-⊆ x y h (n , q<xn) =
  let r , q<r , r<xn = <-dense q<xn ; δ = x n ℚ.- r
      m , le = h δ (subst (ℚ._< δ) (+-inverseʳ r) (+-monoˡ-< (ℚ.- r) r<xn)) n
      r+δ≡xn = trans (+-comm r δ) (//-rightDividesˡ r (x n))
  in m , <-≤-trans q<r (subst₂ ℚ._≤_ (//-rightDividesʳ δ r) (//-rightDividesʳ δ (y m))
                         (+-monoˡ-≤ (ℚ.- δ) (subst (ℚ._≤ y m ℚ.+ δ) (sym r+δ≡xn) le)))

Cut-⊆⇒≲ : (x y : ℕ → ℚ) → Cut x ⊆ Cut y → x ≲ y
Cut-⊆⇒≲ x y s δ δ>0 n =
  let m , lt = s (n , subst (x n ℚ.- δ ℚ.<_) (+-identityʳ (x n)) (+-monoʳ-< (x n) (neg-antimono-< δ>0)))
  in m , <⇒≤ (subst (ℚ._< y m ℚ.+ δ) (//-rightDividesˡ δ (x n)) (+-monoˡ-< δ lt))

≲⇔Cut-⊆ : (x y : ℕ → ℚ) → x ≲ y ⇔ Cut x ⊆ Cut y
≲⇔Cut-⊆ x y = mk⇔ (≲⇒Cut-⊆ x y) (Cut-⊆⇒≲ x y)

≈⇒Cut-≐ : (x y : ℕ → ℚ) → x ≈ y → Cut x ≐ Cut y
≈⇒Cut-≐ x y h = ≲⇒Cut-⊆ x y (λ δ δ>0 → proj₁ (h δ δ>0)) , ≲⇒Cut-⊆ y x (λ δ δ>0 → proj₂ (h δ δ>0))

Cut-≐⇒≈ : (x y : ℕ → ℚ) → Cut x ≐ Cut y → x ≈ y
Cut-≐⇒≈ x y (s , t) δ δ>0 = Cut-⊆⇒≲ x y s δ δ>0 , Cut-⊆⇒≲ y x t δ δ>0

≈⇔Cut-≐ : (x y : ℕ → ℚ) → x ≈ y ⇔ Cut x ≐ Cut y
≈⇔Cut-≐ x y = mk⇔ (≈⇒Cut-≐ x y) (Cut-≐⇒≈ x y)

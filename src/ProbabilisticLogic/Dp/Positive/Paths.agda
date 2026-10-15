{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Paths where

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive

private variable
  a : Level
  A : Set a

positive-product : {x y : ℚ} → 0ℚ ℚ.< x → 0ℚ ℚ.< y → 0ℚ ℚ.< x ℚ.* y
positive-product {x} {y} px py = positive⁻¹ (x ℚ.* y)
  {{pos*pos⇒pos x {{ℚ.positive px}} y {{ℚ.positive py}}}}

nonpositive-zero : {x : ℚ} → 0ℚ ℚ.≤ x → (0ℚ ℚ.< x → ⊥) → x ≡ 0ℚ
nonpositive-zero nn neg = ≤-antisym (≮⇒≥ neg) nn

product-positive : {x y : ℚ} → 0ℚ ℚ.≤ x → 0ℚ ℚ.≤ y
                 → 0ℚ ℚ.< x ℚ.* y → (0ℚ ℚ.< x) × (0ℚ ℚ.< y)
product-positive {x} {y} nx ny pos with 0ℚ ℚ.<? x | 0ℚ ℚ.<? y
... | yes px | yes py = px , py
... | no neg | _ = ⊥-elim (<-irrefl (sym (trans (cong (ℚ._* y) (nonpositive-zero nx neg)) (*-zeroˡ y))) pos)
... | yes _ | no neg = ⊥-elim (<-irrefl (sym (trans (cong (x ℚ.*_) (nonpositive-zero ny neg)) (*-zeroʳ x))) pos)

sum-positive : {x y : ℚ} → 0ℚ ℚ.≤ x → 0ℚ ℚ.≤ y
             → 0ℚ ℚ.< x ℚ.+ y → (0ℚ ℚ.< x) ⊎ (0ℚ ℚ.< y)
sum-positive {x} {y} nx ny pos with 0ℚ ℚ.<? x | 0ℚ ℚ.<? y
... | yes px | _ = inj₁ px
... | no _ | yes py = inj₂ py
... | no qx | no qy = ⊥-elim (<-irrefl (sym (trans
  (cong₂ ℚ._+_ (nonpositive-zero nx qx) (nonpositive-zero ny qy)) (+-identityʳ 0ℚ))) pos)

node-positive-left : {w v x y : ℚ} → 0ℚ ℚ.< w → 0ℚ ℚ.< x
                   → 0ℚ ℚ.≤ v → 0ℚ ℚ.≤ y → 0ℚ ℚ.< w ℚ.* x ℚ.+ v ℚ.* y
node-positive-left {w} {v} {x} {y} pw px nv ny =
  subst (ℚ._< w ℚ.* x ℚ.+ v ℚ.* y) (+-identityʳ 0ℚ)
    (+-mono-<-≤ (positive-product pw px) (0≤* nv ny))

node-positive-right : {w v x y : ℚ} → 0ℚ ℚ.≤ w → 0ℚ ℚ.≤ x
                    → 0ℚ ℚ.< v → 0ℚ ℚ.< y → 0ℚ ℚ.< w ℚ.* x ℚ.+ v ℚ.* y
node-positive-right {w} {v} {x} {y} nw nx pv py =
  subst (ℚ._< w ℚ.* x ℚ.+ v ℚ.* y) (+-identityʳ 0ℚ)
    (+-mono-≤-< (0≤* nw nx) (positive-product pv py))

mutual
  positive-extract : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → NNF P → 0ℚ ℚ.< cum n d P
                   → ∃ λ x → Positive d x × (0ℚ ℚ.< P x)
  positive-extract zero d P nn pos = ⊥-elim (<-irrefl refl pos)
  positive-extract (suc n) d P nn pos with sum-positive
    (0≤* (wt-nn d true) (leafₚ-nn n (br d true) P nn))
    (0≤* (wt-nn d false) (leafₚ-nn n (br d false) P nn)) pos
  ... | inj₁ p =
    let pw , px = product-positive (wt-nn d true) (leafₚ-nn n (br d true) P nn) p
        x , path , test = leaf-extract n d true P nn px pw
    in x , path , test
  ... | inj₂ p =
    let pw , px = product-positive (wt-nn d false) (leafₚ-nn n (br d false) P nn) p
        x , path , test = leaf-extract n d false P nn px pw
    in x , path , test

  leaf-extract : (n : ℕ) (d : Dₚ A) (c : Bool) (P : A → ℚ) → NNF P
               → 0ℚ ℚ.< leafₚ n (br d c) P → 0ℚ ℚ.< wt d c
               → ∃ λ x → Positive d x × (0ℚ ℚ.< P x)
  leaf-extract n d c P nn px pw with br d c in eq
  ... | inj₁ x = x , hit c pw eq , px
  ... | inj₂ e =
    let x , path , test = positive-extract n e P nn px
    in x , delay c e pw eq path , test

branch-positive : (n : ℕ) (d : Dₚ A) (c : Bool) (P : A → ℚ) → NNF P
                → 0ℚ ℚ.< wt d c → 0ℚ ℚ.< leafₚ n (br d c) P → 0ℚ ℚ.< cum (suc n) d P
branch-positive n d true P nn pw px = node-positive-left pw px (wt-nn d false) (leafₚ-nn n (br d false) P nn)
branch-positive n d false P nn pw px = node-positive-right (wt-nn d true) (leafₚ-nn n (br d true) P nn) pw px

positive-witness : {d : Dₚ A} {x : A} (P : A → ℚ) → NNF P
                 → Positive d x → 0ℚ ℚ.< P x → PositiveTest d P
positive-witness {d = d} P nn (hit c pw eq) px =
  1 , branch-positive 0 d c P nn pw (subst (λ r → 0ℚ ℚ.< leafₚ 0 r P) (sym eq) px)
positive-witness {d = d} P nn (delay c e pw eq path) px =
  let n , pos = positive-witness P nn path px
  in suc n , branch-positive n d c P nn pw (subst (λ r → 0ℚ ℚ.< leafₚ n r P) (sym eq) pos)

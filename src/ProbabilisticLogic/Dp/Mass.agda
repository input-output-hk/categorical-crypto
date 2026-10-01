{-# OPTIONS --safe --without-K --guardedness #-}

-- `ASTotal` is deliberately not `Σ[ n ] mass n d ≡ 1ℚ`: a geometric loop
-- terminates with probability one at no finite budget.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Solver
open import Data.Sum.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import Data.Rational.Properties.Ext
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

module ProbabilisticLogic.Dp.Mass where

private variable
  a b c : Level
  A : Set a
  B : Set b
  C : Set c

------------------------------------------------------------------------
-- The mass, and the two bounds every test obeys

mass : ℕ → Dₚ A → ℚ
mass n d = cum n d (λ _ → 1ℚ)

mutual
  cum-≤1 : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → ((p : A) → P p ℚ.≤ 1ℚ) → cum n d P ℚ.≤ 1ℚ
  cum-≤1 zero    d P le = 0≤1ℚ
  cum-≤1 (suc n) d P le =
    ≤-trans (node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
                       (leafₚ-≤1 n (br d true) P le) (leafₚ-≤1 n (br d false) P le))
            (≤-reflexive (trans (cong₂ ℚ._+_ (*-identityʳ (wt d true)) (*-identityʳ (wt d false)))
                                (wt-1 d)))

  leafₚ-≤1 : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) → ((p : A) → P p ℚ.≤ 1ℚ)
           → leafₚ n x P ℚ.≤ 1ℚ
  leafₚ-≤1 n (inj₁ p)  P le = le p
  leafₚ-≤1 n (inj₂ d′) P le = cum-≤1 n d′ P le

mass-nn : (n : ℕ) (d : Dₚ A) → 0ℚ ℚ.≤ mass n d
mass-nn n d = cum-nn n d _ λ _ → 0≤1ℚ

mass-≤1 : (n : ℕ) (d : Dₚ A) → mass n d ℚ.≤ 1ℚ
mass-≤1 n d = cum-≤1 n d _ λ _ → ≤-refl

verdict-mass : (n : ℕ) (d : Dₚ Bool) → Pr≤[ true ] n d ℚ.+ Pr≤[ false ] n d ≡ mass n d
verdict-mass n d = trans (sym (cum-add n d (indᵇ true) (indᵇ false)))
                         (cum-cong-P n d _ (λ _ → 1ℚ) λ { true → +-identityʳ 1ℚ ; false → +-identityˡ 1ℚ })

------------------------------------------------------------------------
-- A prefix scales what follows it

const-bindA : (n : ℕ) (d : Dₚ A) (e : Dₚ B) (P : B → ℚ) → NNF P
            → cum n (d >>=ₚ λ _ → e) P ℚ.≤ mass n d ℚ.* cum n e P
const-bindA n d e P nn = ≤-trans (>>=ₚ-boundA n d (λ _ → e) P nn)
                                 (≤-reflexive (cum-const n d (cum n e P)))

const-bindB : (n m : ℕ) (d : Dₚ A) (e : Dₚ B) (P : B → ℚ) → NNF P
            → mass n d ℚ.* cum m e P ℚ.≤ cum (n +ℕ m) (d >>=ₚ λ _ → e) P
const-bindB n m d e P nn = ≤-trans (≤-reflexive (sym (cum-const n d (cum m e P))))
                                   (>>=ₚ-boundB n m d (λ _ → e) P nn)

mass-bindˡ : (n : ℕ) (d : Dₚ A) (k : A → Dₚ B) → mass n (d >>=ₚ k) ℚ.≤ mass n d
mass-bindˡ n d k =
  ≤-trans (>>=ₚ-boundA n d k _ λ _ → 0≤1ℚ)
          (cum-mono-P n d (λ p → cum n (k p) (λ _ → 1ℚ)) _ λ p → mass-≤1 n (k p))

cum-bindʳ : (n : ℕ) (d : Dₚ A) (k : A → Dₚ B) (P : B → ℚ) → NNF P → (c : ℚ) → 0ℚ ℚ.≤ c
          → ((p : A) → cum n (k p) P ℚ.≤ c) → cum n (d >>=ₚ k) P ℚ.≤ c
cum-bindʳ n d k P nn c 0≤c le =
  ≤-trans (>>=ₚ-boundA n d k P nn)
  (≤-trans (cum-mono-P n d (λ p → cum n (k p) P) (λ _ → c) le)
  (≤-trans (≤-reflexive (cum-const n d c))
  (≤-trans (*-monoʳ-≤-nonNeg c ⦃ ℚ.nonNegative 0≤c ⦄ (mass-≤1 n d))
           (≤-reflexive (*-identityˡ c)))))

mass-bindʳ : (n : ℕ) (d : Dₚ A) (k : A → Dₚ B) (c : ℚ) → 0ℚ ℚ.≤ c
           → ((p : A) → mass n (k p) ℚ.≤ c) → mass n (d >>=ₚ k) ℚ.≤ c
mass-bindʳ n d k = cum-bindʳ n d k (λ _ → 1ℚ) λ _ → 0≤1ℚ

------------------------------------------------------------------------
-- Domination of the masses alone
--
-- `_≼ᵐ_` compares runs with different value types, which `_≼ₚ_` cannot.

infix 4 _≼ᵐ_

_≼ᵐ_ : {A : Set a} {B : Set b} → Dₚ A → Dₚ B → Set
_≼ᵐ_ = Cofinal (λ _ → 1ℚ) (λ _ → 1ℚ)

≼ₚ⇒≼ᵐ : (d e : Dₚ A) → d ≼ₚ e → d ≼ᵐ e
≼ₚ⇒≼ᵐ d e le = le _ λ _ → 0≤1ℚ

bind-≼ᵐ : (d : Dₚ A) (k : A → Dₚ B) → (d >>=ₚ k) ≼ᵐ d
bind-≼ᵐ d k n = n , mass-bindˡ n d k

mapₚ-≼ᵐ : (d : Dₚ A) (h : A → B) → d ≼ᵐ mapₚ h d
mapₚ-≼ᵐ d h n =
  n +ℕ 1
  , ≤-trans (≤-reflexive (cum-cong-P n d _ (λ p → cum 1 (returnₚ (h p)) (λ _ → 1ℚ))
                                     λ p → sym (returnₚ-cum 0 (h p) (λ _ → 1ℚ))))
            (>>=ₚ-boundB n 1 d _ (λ _ → 1ℚ) λ _ → 0≤1ℚ)

-- The hypothesis is budget-uniform: a per-branch cofinal bound cannot be maxed
-- out over a support the budget does not bound.
bindʳ-≼ᵐ : (d : Dₚ A) (k : A → Dₚ B) (e : Dₚ C)
         → ((p : A) (n : ℕ) → mass n (k p) ℚ.≤ mass n e) → (d >>=ₚ k) ≼ᵐ e
bindʳ-≼ᵐ d k e le n = n , mass-bindʳ n d k (mass n e) (mass-nn n e) λ p → le p n

------------------------------------------------------------------------
-- Termination, exact and almost sure

-- Attained, not cofinal: it pins the scale a domination is read on (`squeeze`).
Total : Dₚ Bool → Set
Total d = Σ[ n ∈ ℕ ] (1ℚ ℚ.≤ Pr≤[ true ] n d ℚ.+ Pr≤[ false ] n d)

total-resp-≼ₚ : (d e : Dₚ Bool) → d ≼ₚ e → Total d → Total e
total-resp-≼ₚ d e le (n , tot) =
  let m₁ , b₁ = le (indᵇ true)  (indᵇ-nn true)  n
      m₂ , b₂ = le (indᵇ false) (indᵇ-nn false) n
  in m₁ ⊔ m₂
   , ≤-trans tot (+-mono-≤ (≤-trans b₁ (Pr≤-mono true  e (m≤m⊔n m₁ m₂)))
                           (≤-trans b₂ (Pr≤-mono false e (m≤n⊔m m₁ m₂))))

ASTotal : Dₚ A → Set
ASTotal d = (ε : ℚ) → 0ℚ ℚ.< ε → Σ[ n ∈ ℕ ] (1ℚ ℚ.- ε ℚ.≤ mass n d)

astotal-≼ᵐ : (d : Dₚ A) (e : Dₚ B) → d ≼ᵐ e → ASTotal d → ASTotal e
astotal-≼ᵐ d e le tot ε ε>0 =
  let n , bd = tot ε ε>0
      m , bd′ = le n
  in m , ≤-trans bd bd′

astotal-returnₚ : (x : A) → ASTotal (returnₚ x)
astotal-returnₚ x ε ε>0 =
  1 , ≤-trans (x-y≤x 1ℚ (<⇒≤ ε>0)) (≤-reflexive (sym (returnₚ-cum 0 x (λ _ → 1ℚ))))

private
  open +-*-Solver

  split : (m x : ℚ) → m ℚ.* x ℚ.+ (1ℚ ℚ.- m) ℚ.* x ≡ x
  split = solve 2 (λ m x → m :* x :+ (con 1ℚ :- m) :* x := x) refl

  1-≤ : (m ε : ℚ) → 1ℚ ℚ.- ε ℚ.≤ m → 1ℚ ℚ.- m ℚ.≤ ε
  1-≤ m ε le = ≤-trans (+-monoʳ-≤ 1ℚ (neg-antimono-≤ le)) (≤-reflexive (1-[1-x] ε))

  scale : (m x ε : ℚ) → m ℚ.≤ 1ℚ → 1ℚ ℚ.- ε ℚ.≤ m → 0ℚ ℚ.≤ x → x ℚ.≤ 1ℚ
        → x ℚ.≤ m ℚ.* x ℚ.+ ε
  scale m x ε m≤1 close 0≤x x≤1 =
    ≤-trans (≤-reflexive (sym (split m x)))
            (+-monoʳ-≤ (m ℚ.* x)
              (≤-trans (*-monoˡ-≤-nonNeg (1ℚ ℚ.- m) ⦃ ℚ.nonNegative (0≤1- m≤1) ⦄ x≤1)
              (≤-trans (≤-reflexive (*-identityʳ (1ℚ ℚ.- m))) (1-≤ m ε close))))

  expand : (ε : ℚ) → 1ℚ ℚ.- (ε ℚ.+ ε) ≡ ((1ℚ ℚ.- ε) ℚ.+ (1ℚ ℚ.- ε)) ℚ.- 1ℚ
  expand = solve 1 (λ ε →
    con 1ℚ :- (ε :+ ε) := ((con 1ℚ :- ε) :+ (con 1ℚ :- ε)) :- con 1ℚ) refl

  collect : (a b : ℚ) → ((a ℚ.+ b) ℚ.- 1ℚ) ℚ.+ ((1ℚ ℚ.- a) ℚ.* (1ℚ ℚ.- b)) ≡ a ℚ.* b
  collect = solve 2 (λ a b →
    ((a :+ b) :- con 1ℚ) :+ ((con 1ℚ :- a) :* (con 1ℚ :- b)) := a :* b) refl

  product : (a b ε : ℚ) → a ℚ.≤ 1ℚ → b ℚ.≤ 1ℚ → 1ℚ ℚ.- ε ℚ.≤ a → 1ℚ ℚ.- ε ℚ.≤ b
          → 1ℚ ℚ.- (ε ℚ.+ ε) ℚ.≤ a ℚ.* b
  product a b ε a≤1 b≤1 ea eb =
    ≤-trans (≤-reflexive (expand ε))
    (≤-trans (+-monoˡ-≤ (ℚ.- 1ℚ) (+-mono-≤ ea eb))
    (≤-trans (p≤p+q ((a ℚ.+ b) ℚ.- 1ℚ) (0≤* (0≤1- a≤1) (0≤1- b≤1)))
             (≤-reflexive (collect a b))))

const-bind-astotal : (d : Dₚ A) (e : Dₚ B) → ASTotal d → ASTotal e
                   → ASTotal (d >>=ₚ λ _ → e)
const-bind-astotal d e td te ε ε>0 =
  let k , bd  = td (½ ℚ.* ε) (0<½* ε>0)
      n , bd′ = te (½ ℚ.* ε) (0<½* ε>0)
  in k +ℕ n
   , ≤-trans (subst (λ c → 1ℚ ℚ.- c ℚ.≤ mass k d ℚ.* mass n e) (½*+½* ε)
                    (product (mass k d) (mass n e) (½ ℚ.* ε)
                             (mass-≤1 k d) (mass-≤1 n e) bd bd′))
             (const-bindB k n d e (λ _ → 1ℚ) λ _ → 0≤1ℚ)

module _ (p : Dₚ A) (e : Dₚ Bool) where

  const-bind-≼ : (ε : ℚ) → 0ℚ ℚ.≤ ε → (p >>=ₚ λ _ → e) ≼ₚ[ ε ] e
  const-bind-≼ ε 0≤ε b n = n , ≤-trans (const-bindA n p e (indᵇ b) (indᵇ-nn b))
    (≤-trans (*-monoʳ-≤-nonNeg (Pr≤[ b ] n e)
                ⦃ ℚ.nonNegative (cum-nn n e (indᵇ b) (indᵇ-nn b)) ⦄ (mass-≤1 n p))
    (≤-trans (≤-reflexive (*-identityˡ (Pr≤[ b ] n e)))
             (p≤p+q (Pr≤[ b ] n e) 0≤ε)))

  const-bind-≽ : ASTotal p → (ε : ℚ) → 0ℚ ℚ.< ε → e ≼ₚ[ ε ] (p >>=ₚ λ _ → e)
  const-bind-≽ tot ε ε>0 b n =
    let k , close = tot ε ε>0
    in k +ℕ n
     , ≤-trans (scale (mass k p) (Pr≤[ b ] n e) ε (mass-≤1 k p) close
                      (cum-nn n e (indᵇ b) (indᵇ-nn b))
                      (cum-≤1 n e (indᵇ b) (indᵇ-≤1 b)))
               (+-monoˡ-≤ ε (const-bindB k n p e (indᵇ b) (indᵇ-nn b)))

  astotal-bind : ASTotal p → (ε : ℚ) → 0ℚ ℚ.< ε → (p >>=ₚ λ _ → e) ≈ₚ[ ε ] e
  astotal-bind tot ε ε>0 = const-bind-≼ ε (<⇒≤ ε>0) , const-bind-≽ tot ε ε>0

------------------------------------------------------------------------
-- The squeeze

private
  shift : (x y c : ℚ) → x ℚ.≤ y ℚ.+ c → x ℚ.- c ℚ.≤ y
  shift x y c le = ≤-trans (+-monoˡ-≤ (ℚ.- c) le) (≤-reflexive (+-−-cancel y c))

  pair : (x₁ x₂ ε : ℚ) → (x₁ ℚ.+ ε) ℚ.+ (x₂ ℚ.+ ε) ≡ (x₁ ℚ.+ x₂) ℚ.+ (ε ℚ.+ ε)
  pair = solve 3 (λ x₁ x₂ ε →
    (x₁ :+ ε) :+ (x₂ :+ ε) := (x₁ :+ x₂) :+ (ε :+ ε)) refl

squeeze : (x z : Dₚ Bool) (p : Dₚ A) (ε : ℚ) → Total x → z ≼ᵐ p → x ≼ₚ[ ε ] z
        → Σ[ m ∈ ℕ ] (1ℚ ℚ.- (ε ℚ.+ ε) ℚ.≤ mass m p)
squeeze x z p ε (n , tot) bnd dom = m′ , shift 1ℚ (mass m′ p) (ε ℚ.+ ε)
  (≤-trans tot
  (≤-trans (+-mono-≤ (proj₂ (dom true n)) (proj₂ (dom false n)))
  (≤-trans (+-mono-≤ (+-monoˡ-≤ ε (Pr≤-mono true z (m≤m⊔n m₁ m₂)))
                     (+-monoˡ-≤ ε (Pr≤-mono false z (m≤n⊔m m₁ m₂))))
  (≤-trans (≤-reflexive (trans (pair (Pr≤[ true ] m z) (Pr≤[ false ] m z) ε)
                               (cong (ℚ._+ (ε ℚ.+ ε)) (verdict-mass m z))))
           (+-monoˡ-≤ (ε ℚ.+ ε) (proj₂ (bnd m)))))))
  where
  m₁ = proj₁ (dom true n)
  m₂ = proj₁ (dom false n)
  m  = m₁ ⊔ m₂
  m′ = proj₁ (bnd m)

squeeze-astotal : (x z : Dₚ Bool) (p : Dₚ A) → Total x → z ≼ᵐ p
                → ((ε : ℚ) → 0ℚ ℚ.< ε → x ≼ₚ[ ε ] z)
                → ASTotal p
squeeze-astotal x z p tot bnd dom ε ε>0 =
  let m , le = squeeze x z p (½ ℚ.* ε) tot bnd (dom (½ ℚ.* ε) (0<½* ε>0))
  in m , subst (λ c → 1ℚ ℚ.- c ℚ.≤ mass m p) (½*+½* ε) le

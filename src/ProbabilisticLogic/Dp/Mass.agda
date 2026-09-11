{-# OPTIONS --safe --without-K --guardedness #-}

-- Termination mass at a budget, and what a lossy prefix does to what follows
-- it.
--
-- `mass n d` is `cum n d` against the constant test `1ℚ`: the mass of `d` that
-- reaches a value within `n` steps.  A prefix contributes exactly that factor
-- to whatever follows it — `d >>=ₚ λ _ → e` observes `e` scaled by `mass d` —
-- and `const-bindA`/`const-bindB` are the two halves of that statement,
-- `cum`-wise and sup-free.  `Dp.Zero` is the `mass ≡ 0ℚ` end of the same
-- scale.
--
-- `ASTotal` is almost-sure termination, and it is deliberately NOT
-- `Σ[ n ] mass n d ≡ 1ℚ`: a geometric loop terminates with probability one and
-- at no finite budget.  It is what an ε-closed comparison consumes
-- (`astotal-bind`), and it is exactly what a two-sided domination against a
-- totally terminating run gives back (`squeeze`) — the upper bound `mass ≤ 1ℚ`
-- is free, so a lower bound on one side of the domination is a lower bound on
-- the prefix's mass.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Solver using (module +-*-Solver)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Data.Rational.Properties.Ext
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
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

-- A test bounded by one is scored by at most one: the node weights sum to one.
mutual
  cum-≤1 : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → ((p : A) → P p ℚ.≤ 1ℚ) → cum n d P ℚ.≤ 1ℚ
  cum-≤1 zero    d P le = 0≤1ℚ
  cum-≤1 (suc n) d P le =
    ≤-trans (node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
                       (leafₚ-≤1 n (br d true) P le) (leafₚ-≤1 n (br d false) P le))
            (≤-reflexive (one (wt d true) (wt d false) (wt-1 d)))
    where
    one : (w₁ w₂ : ℚ) → w₁ ℚ.+ w₂ ≡ 1ℚ → w₁ ℚ.* 1ℚ ℚ.+ w₂ ℚ.* 1ℚ ≡ 1ℚ
    one w₁ w₂ eq = trans (cong₂ ℚ._+_ (*-identityʳ w₁) (*-identityʳ w₂)) eq

  leafₚ-≤1 : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) → ((p : A) → P p ℚ.≤ 1ℚ)
           → leafₚ n x P ℚ.≤ 1ℚ
  leafₚ-≤1 n (inj₁ p)  P le = le p
  leafₚ-≤1 n (inj₂ d′) P le = cum-≤1 n d′ P le

mass-nn : (n : ℕ) (d : Dₚ A) → 0ℚ ℚ.≤ mass n d
mass-nn n d = cum-nn n d _ λ _ → 0≤1ℚ

mass-≤1 : (n : ℕ) (d : Dₚ A) → mass n d ℚ.≤ 1ℚ
mass-≤1 n d = cum-≤1 n d _ λ _ → ≤-refl

mass-mono : {n m : ℕ} → n ≤ℕ m → (d : Dₚ A) → mass n d ℚ.≤ mass m d
mass-mono le d = cum-mono le d _ λ _ → 0≤1ℚ

------------------------------------------------------------------------
-- A constant test, and a sum of two

private
  distr : (w₁ w₂ x₁ x₂ c : ℚ)
        → w₁ ℚ.* (x₁ ℚ.* c) ℚ.+ w₂ ℚ.* (x₂ ℚ.* c) ≡ (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.* c
  distr = solve 5 (λ w₁ w₂ x₁ x₂ c →
    w₁ :* (x₁ :* c) :+ w₂ :* (x₂ :* c) := (w₁ :* x₁ :+ w₂ :* x₂) :* c) refl
    where open +-*-Solver

  regroup : (w₁ w₂ x₁ x₂ y₁ y₂ : ℚ)
          → w₁ ℚ.* (x₁ ℚ.+ y₁) ℚ.+ w₂ ℚ.* (x₂ ℚ.+ y₂)
            ≡ (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.+ (w₁ ℚ.* y₁ ℚ.+ w₂ ℚ.* y₂)
  regroup = solve 6 (λ w₁ w₂ x₁ x₂ y₁ y₂ →
    w₁ :* (x₁ :+ y₁) :+ w₂ :* (x₂ :+ y₂)
      := (w₁ :* x₁ :+ w₂ :* x₂) :+ (w₁ :* y₁ :+ w₂ :* y₂)) refl
    where open +-*-Solver

mutual
  cum-const : (n : ℕ) (d : Dₚ A) (c : ℚ) → cum n d (λ _ → c) ≡ mass n d ℚ.* c
  cum-const zero    d c = sym (*-zeroˡ c)
  cum-const (suc n) d c =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-const n (br d true) c))
                       (cong (wt d false ℚ.*_) (leafₚ-const n (br d false) c)))
          (distr (wt d true) (wt d false)
                 (leafₚ n (br d true) (λ _ → 1ℚ)) (leafₚ n (br d false) (λ _ → 1ℚ)) c)

  leafₚ-const : (n : ℕ) (x : A ⊎ Dₚ A) (c : ℚ)
              → leafₚ n x (λ _ → c) ≡ leafₚ n x (λ _ → 1ℚ) ℚ.* c
  leafₚ-const n (inj₁ p)  c = sym (*-identityˡ c)
  leafₚ-const n (inj₂ d′) c = cum-const n d′ c

mutual
  cum-add : (n : ℕ) (d : Dₚ A) (P Q : A → ℚ)
          → cum n d (λ p → P p ℚ.+ Q p) ≡ cum n d P ℚ.+ cum n d Q
  cum-add zero    d P Q = sym (+-identityʳ 0ℚ)
  cum-add (suc n) d P Q =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-add n (br d true) P Q))
                       (cong (wt d false ℚ.*_) (leafₚ-add n (br d false) P Q)))
          (regroup (wt d true) (wt d false)
                   (leafₚ n (br d true) P) (leafₚ n (br d false) P)
                   (leafₚ n (br d true) Q) (leafₚ n (br d false) Q))

  leafₚ-add : (n : ℕ) (x : A ⊎ Dₚ A) (P Q : A → ℚ)
            → leafₚ n x (λ p → P p ℚ.+ Q p) ≡ leafₚ n x P ℚ.+ leafₚ n x Q
  leafₚ-add n (inj₁ p)  P Q = refl
  leafₚ-add n (inj₂ d′) P Q = cum-add n d′ P Q

indᵇ-≤1 : (b c : Bool) → indᵇ b c ℚ.≤ 1ℚ
indᵇ-≤1 true  true  = ≤-refl
indᵇ-≤1 true  false = 0≤1ℚ
indᵇ-≤1 false true  = 0≤1ℚ
indᵇ-≤1 false false = ≤-refl

-- The two verdict masses ARE the termination mass: the indicators sum to one.
verdict-mass : (n : ℕ) (d : Dₚ Bool) → Pr≤[ true ] n d ℚ.+ Pr≤[ false ] n d ≡ mass n d
verdict-mass n d = trans (sym (cum-add n d (indᵇ true) (indᵇ false)))
                         (cum-cong-P n d _ (λ _ → 1ℚ) ind-sum)
  where
  ind-sum : (c : Bool) → indᵇ true c ℚ.+ indᵇ false c ≡ 1ℚ
  ind-sum true  = +-identityʳ 1ℚ
  ind-sum false = +-identityˡ 1ℚ

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

-- …and a prefix can only lose mass, whatever follows it.
mass-bindˡ : (n : ℕ) (d : Dₚ A) (k : A → Dₚ B) → mass n (d >>=ₚ k) ℚ.≤ mass n d
mass-bindˡ n d k =
  ≤-trans (>>=ₚ-boundA n d k _ λ _ → 0≤1ℚ)
          (cum-mono-P n d (λ p → cum n (k p) (λ _ → 1ℚ)) _ λ p → mass-≤1 n (k p))

-- The same for the continuation: a uniform bound on every branch bounds the
-- whole, the prefix's own mass being at most one.
mass-bindʳ : (n : ℕ) (d : Dₚ A) (k : A → Dₚ B) (c : ℚ) → 0ℚ ℚ.≤ c
           → ((p : A) → mass n (k p) ℚ.≤ c) → mass n (d >>=ₚ k) ℚ.≤ c
mass-bindʳ n d k c 0≤c le =
  ≤-trans (>>=ₚ-boundA n d k _ λ _ → 0≤1ℚ)
  (≤-trans (cum-mono-P n d (λ p → cum n (k p) (λ _ → 1ℚ)) (λ _ → c) le)
  (≤-trans (≤-reflexive (cum-const n d c))
  (≤-trans (*-monoʳ-≤-nonNeg c ⦃ ℚ.nonNegative 0≤c ⦄ (mass-≤1 n d))
           (≤-reflexive (*-identityˡ c)))))

------------------------------------------------------------------------
-- Domination of the masses alone
--
-- What a factor of a composite bounds about the whole: the two sides carry
-- values of different types, so this is coarser than `_≼ₚ_` and crosses
-- everything `_≼ₚ_` cannot.

infix 4 _≼ᵐ_

_≼ᵐ_ : {A : Set a} {B : Set b} → Dₚ A → Dₚ B → Set
d ≼ᵐ e = (n : ℕ) → Σ[ m ∈ ℕ ] (mass n d ℚ.≤ mass m e)

≼ᵐ-refl : (d : Dₚ A) → d ≼ᵐ d
≼ᵐ-refl d n = n , ≤-refl

≼ᵐ-trans : (d : Dₚ A) (e : Dₚ B) (h : Dₚ C) → d ≼ᵐ e → e ≼ᵐ h → d ≼ᵐ h
≼ᵐ-trans d e h de eh n =
  let m , le = de n
      k , le′ = eh m
  in k , ≤-trans le le′

≼ₚ⇒≼ᵐ : (d e : Dₚ A) → d ≼ₚ e → d ≼ᵐ e
≼ₚ⇒≼ᵐ d e le n = le _ (λ _ → 0≤1ℚ) n

bind-≼ᵐ : (d : Dₚ A) (k : A → Dₚ B) → (d >>=ₚ k) ≼ᵐ d
bind-≼ᵐ d k n = n , mass-bindˡ n d k

-- …and the same for the continuation.  The hypothesis is budget-UNIFORM: a
-- per-branch cofinal bound cannot be maxed out over a support the budget does
-- not bound, and the one use (a paired state, `UC.Seam.Grounding.Dead`) has
-- the uniform form on the nose.
bindʳ-≼ᵐ : (d : Dₚ A) (k : A → Dₚ B) (e : Dₚ C)
         → ((p : A) (n : ℕ) → mass n (k p) ℚ.≤ mass n e) → (d >>=ₚ k) ≼ᵐ e
bindʳ-≼ᵐ d k e le n = n , mass-bindʳ n d k (mass n e) (mass-nn n e) λ p → le p n

------------------------------------------------------------------------
-- Termination, exact and almost sure

-- A run that reaches a verdict: the two verdict masses are at one already at
-- a finite budget.  Exact rather than cofinal because that is how the layer
-- delivers it — `Dp.Stable`, hence `PrAgree`, is an ATTAINMENT statement — and
-- exactness is what makes it an anchor: nothing else in a sup-free setting
-- pins the scale a domination is read on.
Total : Dₚ Bool → Set
Total d = Σ[ n ∈ ℕ ] (1ℚ ℚ.≤ Pr≤[ true ] n d ℚ.+ Pr≤[ false ] n d)

total-resp-≼ₚ : (d e : Dₚ Bool) → d ≼ₚ e → Total d → Total e
total-resp-≼ₚ d e le (n , tot) =
  let m₁ , b₁ = le (indᵇ true)  (indᵇ-nn true)  n
      m₂ , b₂ = le (indᵇ false) (indᵇ-nn false) n
  in m₁ ⊔ m₂
   , ≤-trans tot (+-mono-≤ (≤-trans b₁ (Pr≤-mono true  e (m≤m⊔n m₁ m₂)))
                           (≤-trans b₂ (Pr≤-mono false e (m≤n⊔m m₁ m₂))))

total-mass : (d : Dₚ Bool) → Total d → Σ[ n ∈ ℕ ] (1ℚ ℚ.≤ mass n d)
total-mass d (n , tot) = n , ≤-trans tot (≤-reflexive (verdict-mass n d))

ASTotal : Dₚ A → Set
ASTotal d = (ε : ℚ) → 0ℚ ℚ.< ε → Σ[ n ∈ ℕ ] (1ℚ ℚ.- ε ℚ.≤ mass n d)

private
  -- `x` is `m`-weighted plus the remainder, and the remainder is what the
  -- slack pays for.
  split : (m x : ℚ) → m ℚ.* x ℚ.+ (1ℚ ℚ.- m) ℚ.* x ≡ x
  split = solve 2 (λ m x → m :* x :+ (con 1ℚ :- m) :* x := x) refl
    where open +-*-Solver

  co : (ε : ℚ) → 1ℚ ℚ.- (1ℚ ℚ.- ε) ≡ ε
  co = solve 1 (λ ε → con 1ℚ :- (con 1ℚ :- ε) := ε) refl
    where open +-*-Solver

  0≤1- : (m : ℚ) → m ℚ.≤ 1ℚ → 0ℚ ℚ.≤ 1ℚ ℚ.- m
  0≤1- m le = ≤-trans (≤-reflexive (sym (+-inverseʳ m))) (+-monoˡ-≤ (ℚ.- m) le)

  1-≤ : (m ε : ℚ) → 1ℚ ℚ.- ε ℚ.≤ m → 1ℚ ℚ.- m ℚ.≤ ε
  1-≤ m ε le = ≤-trans (+-monoʳ-≤ 1ℚ (neg-antimono-≤ le)) (≤-reflexive (co ε))

  -- `x ≤ m * x + ε`, for a mass `m` within `ε` of one and an `x` in the unit
  -- interval: the remainder `(1 - m) * x` is at most `1 - m`, hence at most ε.
  scale : (m x ε : ℚ) → m ℚ.≤ 1ℚ → 1ℚ ℚ.- ε ℚ.≤ m → 0ℚ ℚ.≤ x → x ℚ.≤ 1ℚ
        → x ℚ.≤ m ℚ.* x ℚ.+ ε
  scale m x ε m≤1 close 0≤x x≤1 =
    ≤-trans (≤-reflexive (sym (split m x)))
            (+-monoʳ-≤ (m ℚ.* x)
              (≤-trans (*-monoˡ-≤-nonNeg (1ℚ ℚ.- m) ⦃ ℚ.nonNegative (0≤1- m m≤1) ⦄ x≤1)
              (≤-trans (≤-reflexive (*-identityʳ (1ℚ ℚ.- m))) (1-≤ m ε close))))

module _ (p : Dₚ A) (e : Dₚ Bool) where

  -- A prefix is never seen to ADD mass, whether or not it terminates.
  const-bind-≼ : (ε : ℚ) → 0ℚ ℚ.≤ ε → (p >>=ₚ λ _ → e) ≼ₚ[ ε ] e
  const-bind-≼ ε 0≤ε b n = n , ≤-trans (const-bindA n p e (indᵇ b) (indᵇ-nn b))
    (≤-trans (*-monoʳ-≤-nonNeg (Pr≤[ b ] n e)
                ⦃ ℚ.nonNegative (cum-nn n e (indᵇ b) (indᵇ-nn b)) ⦄ (mass-≤1 n p))
    (≤-trans (≤-reflexive (*-identityˡ (Pr≤[ b ] n e)))
             (≤-trans (≤-reflexive (sym (+-identityʳ (Pr≤[ b ] n e))))
                      (+-monoʳ-≤ (Pr≤[ b ] n e) 0≤ε))))

  -- …and an almost surely terminating one is not seen to lose any either,
  -- past every positive slack.
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
--
-- A run whose verdict mass reaches one is dominated by an observation whose
-- mass is at most the prefix's: so the prefix's mass reaches one too, up to
-- twice the slack the domination carries.  Both bounds are sup-free, and the
-- upper one (`mass ≤ 1ℚ`) is free — nothing is asked of the right-hand run.

private
  shift : (x y c : ℚ) → x ℚ.≤ y ℚ.+ c → x ℚ.- c ℚ.≤ y
  shift x y c le = ≤-trans (+-monoˡ-≤ (ℚ.- c) le) (≤-reflexive (cancel y c))
    where
    cancel : (y c : ℚ) → (y ℚ.+ c) ℚ.- c ≡ y
    cancel = solve 2 (λ y c → (y :+ c) :- c := y) refl
      where open +-*-Solver

  pair : (x₁ x₂ ε : ℚ) → (x₁ ℚ.+ ε) ℚ.+ (x₂ ℚ.+ ε) ≡ (x₁ ℚ.+ x₂) ℚ.+ (ε ℚ.+ ε)
  pair = solve 3 (λ x₁ x₂ ε →
    (x₁ :+ ε) :+ (x₂ :+ ε) := (x₁ :+ x₂) :+ (ε :+ ε)) refl
    where open +-*-Solver

squeeze : (x z : Dₚ Bool) (p : Dₚ A) (ε : ℚ) → Total x → z ≼ᵐ p
        → x ≼ₚ[ ε ] z
        → Σ[ m ∈ ℕ ] (1ℚ ℚ.- (ε ℚ.+ ε) ℚ.≤ mass m p)
squeeze x z p ε (n , tot) bnd dom = m′ , shift 1ℚ (mass m′ p) (ε ℚ.+ ε) bound
  where
  m₁ = proj₁ (dom true n)
  m₂ = proj₁ (dom false n)
  m  = m₁ ⊔ m₂
  m′ = proj₁ (bnd m)

  bound : 1ℚ ℚ.≤ mass m′ p ℚ.+ (ε ℚ.+ ε)
  bound = ≤-trans tot
    (≤-trans (+-mono-≤ (proj₂ (dom true n)) (proj₂ (dom false n)))
    (≤-trans (+-mono-≤ (+-monoˡ-≤ ε (Pr≤-mono true z (m≤m⊔n m₁ m₂)))
                       (+-monoˡ-≤ ε (Pr≤-mono false z (m≤n⊔m m₁ m₂))))
    (≤-trans (≤-reflexive (trans (pair (Pr≤[ true ] m z) (Pr≤[ false ] m z) ε)
                                 (cong (ℚ._+ (ε ℚ.+ ε)) (verdict-mass m z))))
             (+-monoˡ-≤ (ε ℚ.+ ε) (proj₂ (bnd m))))))

-- …and at every slack, which is `ASTotal` on the nose.
squeeze-astotal : (x z : Dₚ Bool) (p : Dₚ A) → Total x → z ≼ᵐ p
                → ((ε : ℚ) → 0ℚ ℚ.< ε → x ≼ₚ[ ε ] z)
                → ASTotal p
squeeze-astotal x z p tot bnd dom ε ε>0 =
  let m , le = squeeze x z p (½ ℚ.* ε) tot bnd (dom (½ ℚ.* ε) (0<½* ε>0))
  in m , subst (λ c → 1ℚ ℚ.- c ℚ.≤ mass m p) (½*+½* ε) le

-- The case the seam consumes: the dominating observation bounds itself, so a
-- domination by a totally terminating run makes it almost surely terminating.
total-dominated : (x z : Dₚ Bool) → Total x
                → ((ε : ℚ) → 0ℚ ℚ.< ε → x ≼ₚ[ ε ] z) → ASTotal z
total-dominated x z tot = squeeze-astotal x z z tot (≼ᵐ-refl z)

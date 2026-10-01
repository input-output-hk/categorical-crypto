{-# OPTIONS --safe --without-K --guardedness #-}

-- The rational probabilistic delay monad `Dₚ A = ν X. S_ℚ (A ⊎ X)`, with a
-- delay-insensitive equivalence stated entirely in `ℚ` (no lubs, no lower reals).
--
-- A step is a biased coin, not a `Dist-ℚ`: a list-shaped step needs structural
-- recursion inside the corecursion, which `--guardedness` rejects; a finite
-- distribution is a cascade of coins (`Dp.Coin`).
--
-- Divergence is delay: `cum` does not count mass that never lands (`botₚ-cum`), so
-- failure other than divergence composes as `Dₚ ∘ Maybe`.
--
-- `_>>=ₚ_` spends one step at the junction; that step buys the exact `cum`
-- identities the monad laws are proved from.

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤n+m; n≤1+n)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties

open import Data.Rational.LowerReal
open import Data.Rational.Properties.Ext
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

import ProbabilisticLogic.Distribution.Linearity as Linearity

module ProbabilisticLogic.Dp where

private variable
  a b c : Level
  A B C : Set a
  n m j k : ℕ
  P : A → ℚ
  ε δ : ℚ

------------------------------------------------------------------------
-- The carrier

record Dₚ (A : Set a) : Set a where
  coinductive
  field
    wt    : Bool → ℚ
    wt-nn : ∀ c → 0ℚ ℚ.≤ wt c
    wt-1  : wt true ℚ.+ wt false ≡ 1ℚ
    br    : Bool → A ⊎ Dₚ A

open Dₚ public

dirac : A ⊎ Dₚ A → Dₚ A
wt    (dirac x) true  = 1ℚ
wt    (dirac x) false = 0ℚ
wt-nn (dirac x) true  = 0≤1ℚ
wt-nn (dirac x) false = ≤-refl
wt-1  (dirac x)       = +-identityʳ 1ℚ
br    (dirac x) _     = x

returnₚ : A → Dₚ A
returnₚ p = dirac (inj₁ p)

laterₚ : Dₚ A → Dₚ A
laterₚ d = dirac (inj₂ d)

-- Written out rather than as `dirac (inj₂ botₚ)`: the corecursive call may sit
-- under constructors but not under an application.
botₚ : Dₚ A
wt    botₚ true  = 1ℚ
wt    botₚ false = 0ℚ
wt-nn botₚ true  = 0≤1ℚ
wt-nn botₚ false = ≤-refl
wt-1  botₚ       = +-identityʳ 1ℚ
br    botₚ _     = inj₂ botₚ

-- A deterministic step that may refuse.
detₚ : Maybe A → Dₚ A
detₚ (just a) = returnₚ a
detₚ nothing  = botₚ

choiceₚ : (q r : ℚ) → 0ℚ ℚ.≤ q → 0ℚ ℚ.≤ r → q ℚ.+ r ≡ 1ℚ → Dₚ A → Dₚ A → Dₚ A
wt    (choiceₚ q r _  _  _  d e) true  = q
wt    (choiceₚ q r _  _  _  d e) false = r
wt-nn (choiceₚ q r 0q 0r _  d e) true  = 0q
wt-nn (choiceₚ q r 0q 0r _  d e) false = 0r
wt-1  (choiceₚ q r _  _  eq d e)       = eq
br    (choiceₚ q r _  _  _  d e) true  = inj₂ d
br    (choiceₚ q r _  _  _  d e) false = inj₂ e

infixl 1 _>>=ₚ_

mutual
  _>>=ₚ_ : Dₚ A → (A → Dₚ B) → Dₚ B
  wt    (d >>=ₚ f)   = wt d
  wt-nn (d >>=ₚ f)   = wt-nn d
  wt-1  (d >>=ₚ f)   = wt-1 d
  br    (d >>=ₚ f) c = tagₚ (br d c) f

  tagₚ : A ⊎ Dₚ A → (A → Dₚ B) → B ⊎ Dₚ B
  tagₚ (inj₁ p)  f = inj₂ (f p)
  tagₚ (inj₂ d′) f = inj₂ (d′ >>=ₚ f)

mapₚ : (A → B) → Dₚ A → Dₚ B
mapₚ h d = d >>=ₚ (returnₚ ∘′ h)

------------------------------------------------------------------------
-- Depth-`n` cumulative mass against a `ℚ`-valued test
--
-- `cum n d P` is the expectation of `P` over the branches of `d` that reach a
-- value within `n` steps — a rational, being a finite sum.  The lower real
-- `∫ P dd` is its supremum, which is never formed.

mutual
  cum : ℕ → Dₚ A → (A → ℚ) → ℚ
  cum zero    d P = 0ℚ
  cum (suc n) d P =
    wt d true ℚ.* leafₚ n (br d true) P ℚ.+ wt d false ℚ.* leafₚ n (br d false) P

  leafₚ : ℕ → A ⊎ Dₚ A → (A → ℚ) → ℚ
  leafₚ n (inj₁ p)  P = P p
  leafₚ n (inj₂ d′) P = cum n d′ P

-- Non-negative tests: `cum` is monotone in the budget only for these, and the
-- equivalence quantifies over them only.
NNF : {A : Set a} → (A → ℚ) → Set a
NNF {A = A} P = (p : A) → 0ℚ ℚ.≤ P p

------------------------------------------------------------------------
-- The two-term arithmetic every `cum` lemma bottoms out in

node-nn : (w₁ w₂ x₁ x₂ : ℚ) → 0ℚ ℚ.≤ w₁ → 0ℚ ℚ.≤ w₂ → 0ℚ ℚ.≤ x₁ → 0ℚ ℚ.≤ x₂
        → 0ℚ ℚ.≤ w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂
node-nn w₁ w₂ x₁ x₂ n₁ n₂ m₁ m₂ =
  ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ))) (+-mono-≤ (0≤* n₁ m₁) (0≤* n₂ m₂))

node-mono : (w₁ w₂ : ℚ) → 0ℚ ℚ.≤ w₁ → 0ℚ ℚ.≤ w₂ → {x₁ y₁ x₂ y₂ : ℚ}
          → x₁ ℚ.≤ y₁ → x₂ ℚ.≤ y₂
          → w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂ ℚ.≤ w₁ ℚ.* y₁ ℚ.+ w₂ ℚ.* y₂
node-mono w₁ w₂ n₁ n₂ le₁ le₂ =
  +-mono-≤ (*-monoˡ-≤-nonNeg w₁ {{ℚ.nonNegative n₁}} le₁)
           (*-monoˡ-≤-nonNeg w₂ {{ℚ.nonNegative n₂}} le₂)

node-dirac : (x y : ℚ) → 1ℚ ℚ.* x ℚ.+ 0ℚ ℚ.* y ≡ x
node-dirac x y = trans (cong₂ ℚ._+_ (*-identityˡ x) (*-zeroˡ y)) (+-identityʳ x)

node-zero : (w₁ w₂ : ℚ) → w₁ ℚ.* 0ℚ ℚ.+ w₂ ℚ.* 0ℚ ≡ 0ℚ
node-zero w₁ w₂ = trans (cong₂ ℚ._+_ (*-zeroʳ w₁) (*-zeroʳ w₂)) (+-identityʳ 0ℚ)

------------------------------------------------------------------------
-- `cum` is non-negative, and monotone in the budget and in the test

mutual
  cum-nn : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → NNF P → 0ℚ ℚ.≤ cum n d P
  cum-nn zero    d P nn = ≤-refl
  cum-nn (suc n) d P nn =
    node-nn (wt d true) (wt d false) (leafₚ n (br d true) P) (leafₚ n (br d false) P)
            (wt-nn d true) (wt-nn d false)
            (leafₚ-nn n (br d true) P nn) (leafₚ-nn n (br d false) P nn)

  leafₚ-nn : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) → NNF P → 0ℚ ℚ.≤ leafₚ n x P
  leafₚ-nn n (inj₁ p)  P nn = nn p
  leafₚ-nn n (inj₂ d′) P nn = cum-nn n d′ P nn

mutual
  cum-mono : n ≤ℕ m → (d : Dₚ A) (P : A → ℚ) → NNF P → cum n d P ℚ.≤ cum m d P
  cum-mono {m = m} z≤n d P nn = cum-nn m d P nn
  cum-mono (s≤s le) d P nn =
    node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
              (leafₚ-mono le (br d true) P nn) (leafₚ-mono le (br d false) P nn)

  leafₚ-mono : n ≤ℕ m → (x : A ⊎ Dₚ A) (P : A → ℚ) → NNF P → leafₚ n x P ℚ.≤ leafₚ m x P
  leafₚ-mono le (inj₁ p)  P nn = ≤-refl
  leafₚ-mono le (inj₂ d′) P nn = cum-mono le d′ P nn

mutual
  cum-mono-P : (n : ℕ) (d : Dₚ A) (P Q : A → ℚ) → (∀ p → P p ℚ.≤ Q p) → cum n d P ℚ.≤ cum n d Q
  cum-mono-P zero    d P Q le = ≤-refl
  cum-mono-P (suc n) d P Q le =
    node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
              (leafₚ-mono-P n (br d true) P Q le) (leafₚ-mono-P n (br d false) P Q le)

  leafₚ-mono-P : (n : ℕ) (x : A ⊎ Dₚ A) (P Q : A → ℚ) → (∀ p → P p ℚ.≤ Q p)
               → leafₚ n x P ℚ.≤ leafₚ n x Q
  leafₚ-mono-P n (inj₁ p)  P Q le = le p
  leafₚ-mono-P n (inj₂ d′) P Q le = cum-mono-P n d′ P Q le

mutual
  cum-cong-P : (n : ℕ) (d : Dₚ A) (F G : A → ℚ) → (∀ p → F p ≡ G p) → cum n d F ≡ cum n d G
  cum-cong-P zero    d F G eq = refl
  cum-cong-P (suc n) d F G eq =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-cong-P n (br d true) F G eq))
                (cong (wt d false ℚ.*_) (leafₚ-cong-P n (br d false) F G eq))

  leafₚ-cong-P : (n : ℕ) (x : A ⊎ Dₚ A) (F G : A → ℚ) → (∀ p → F p ≡ G p)
               → leafₚ n x F ≡ leafₚ n x G
  leafₚ-cong-P n (inj₁ p)  F G eq = eq p
  leafₚ-cong-P n (inj₂ d′) F G eq = cum-cong-P n d′ F G eq

------------------------------------------------------------------------
-- `cum n d` is `lookup-L` over a finite list, so linear in its test
--
-- `flatten` recurses on the budget, not the tree, so the guardedness of `Dₚ` does
-- not bite; the linear laws are then `Distribution.Linearity`'s.

private module Lin = Linearity (CommutativeRing.commutativeSemiring +-*-commutativeRing)

mutual
  flatten : ℕ → Dₚ A → List (ℚ × A)
  flatten zero    d = []
  flatten (suc n) d =
    Lin.scaleL (wt d true) (flattenL n (br d true)) ++ Lin.scaleL (wt d false) (flattenL n (br d false))

  flattenL : ℕ → A ⊎ Dₚ A → List (ℚ × A)
  flattenL n (inj₁ p)  = (1ℚ , p) ∷ []
  flattenL n (inj₂ d′) = flatten n d′

mutual
  cum-flatten : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → cum n d P ≡ Lin.lookup-L (flatten n d) P
  cum-flatten zero    d P = refl
  cum-flatten (suc n) d P = sym (trans (Lin.lookup-L-++ (Lin.scaleL w₁ l₁) (Lin.scaleL w₂ l₂) P) (cong₂ ℚ._+_
    (trans (Lin.lookup-L-scaleL w₁ l₁ P) (cong (w₁ ℚ.*_) (sym (leafₚ-flatten n (br d true) P))))
    (trans (Lin.lookup-L-scaleL w₂ l₂ P) (cong (w₂ ℚ.*_) (sym (leafₚ-flatten n (br d false) P))))))
    where w₁ = wt d true ; w₂ = wt d false
          l₁ = flattenL n (br d true) ; l₂ = flattenL n (br d false)

  leafₚ-flatten : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) → leafₚ n x P ≡ Lin.lookup-L (flattenL n x) P
  leafₚ-flatten n (inj₁ p)  P = sym (trans (+-identityʳ _) (*-identityˡ (P p)))
  leafₚ-flatten n (inj₂ d′) P = cum-flatten n d′ P

cum-zero : (n : ℕ) (d : Dₚ A) → cum n d (λ _ → 0ℚ) ≡ 0ℚ
cum-zero n d = trans (cum-flatten n d _) (Lin.lookup-L-zero (flatten n d))

cum-add : (n : ℕ) (d : Dₚ A) (P Q : A → ℚ) → cum n d (λ p → P p ℚ.+ Q p) ≡ cum n d P ℚ.+ cum n d Q
cum-add n d P Q = trans (cum-flatten n d _) (trans (Lin.lookup-L-+ (flatten n d) P Q)
  (sym (cong₂ ℚ._+_ (cum-flatten n d P) (cum-flatten n d Q))))

cum-*ₗ : (n : ℕ) (d : Dₚ A) (c : ℚ) (P : A → ℚ) → cum n d (λ p → c ℚ.* P p) ≡ c ℚ.* cum n d P
cum-*ₗ n d c P = trans (cum-flatten n d _) (trans (Lin.lookup-L-*ₗ c (flatten n d) P)
  (cong (c ℚ.*_) (sym (cum-flatten n d P))))

cum-const : (n : ℕ) (d : Dₚ A) (c : ℚ) → cum n d (λ _ → c) ≡ cum n d (λ _ → 1ℚ) ℚ.* c
cum-const n d c = trans (cum-flatten n d _) (trans (Lin.lookup-L-const (flatten n d) c)
  (cong (ℚ._* c) (sym (cum-flatten n d _))))

cum-fubini : {A : Set a} {B : Set b} (n m : ℕ) (d : Dₚ A) (e : Dₚ B) (P : A → B → ℚ)
           → cum n d (λ p → cum m e (P p)) ≡ cum m e (λ q → cum n d (λ p → P p q))
cum-fubini n m d e P =
  trans (cum-flatten n d _) (trans (Lin.lookup-L-cong-P (flatten n d) λ p → cum-flatten m e (P p))
  (trans (Lin.lookup-L-swap (flatten n d) (flatten m e) P)
  (trans (sym (Lin.lookup-L-cong-P (flatten m e) λ q → cum-flatten n d _)) (sym (cum-flatten m e _)))))

------------------------------------------------------------------------
-- Depth-`n` support
--
-- The values `d` can reach within `n` steps — at most `2ⁿ` of them, so a
-- pointwise fact need only hold there for `cum n` to see it.  This is the
-- instrument that makes the bind congruence work: the per-value budget witnesses
-- `f p ≼ₚ g p` supplies can be maxed out over a depth-`n` support (`uniformize`).

mutual
  Supp : ℕ → Dₚ A → (A → Set b) → Set b
  Supp zero    d Φ = ⊤
  Supp (suc n) d Φ = SuppL n (br d true) Φ × SuppL n (br d false) Φ

  SuppL : ℕ → A ⊎ Dₚ A → (A → Set b) → Set b
  SuppL n (inj₁ p)  Φ = Φ p
  SuppL n (inj₂ d′) Φ = Supp n d′ Φ

mutual
  cum-mono-Supp : (n : ℕ) (d : Dₚ A) (P Q : A → ℚ)
                → Supp n d (λ p → P p ℚ.≤ Q p) → cum n d P ℚ.≤ cum n d Q
  cum-mono-Supp zero    d P Q s         = ≤-refl
  cum-mono-Supp (suc n) d P Q (s₁ , s₂) =
    node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
              (leafₚ-mono-Supp n (br d true) P Q s₁) (leafₚ-mono-Supp n (br d false) P Q s₂)

  leafₚ-mono-Supp : (n : ℕ) (x : A ⊎ Dₚ A) (P Q : A → ℚ)
                  → SuppL n x (λ p → P p ℚ.≤ Q p) → leafₚ n x P ℚ.≤ leafₚ n x Q
  leafₚ-mono-Supp n (inj₁ p)  P Q s = s
  leafₚ-mono-Supp n (inj₂ d′) P Q s = cum-mono-Supp n d′ P Q s

mutual
  Supp-mono : (Φ : A → ℕ → Set b) → (∀ p → j ≤ℕ k → Φ p j → Φ p k)
            → j ≤ℕ k → (n : ℕ) (d : Dₚ A)
            → Supp n d (λ p → Φ p j) → Supp n d (λ p → Φ p k)
  Supp-mono Φ up le zero    d s         = tt
  Supp-mono Φ up le (suc n) d (s₁ , s₂) =
    SuppL-mono Φ up le n (br d true) s₁ , SuppL-mono Φ up le n (br d false) s₂

  SuppL-mono : (Φ : A → ℕ → Set b) → (∀ p → j ≤ℕ k → Φ p j → Φ p k)
             → j ≤ℕ k → (n : ℕ) (x : A ⊎ Dₚ A)
             → SuppL n x (λ p → Φ p j) → SuppL n x (λ p → Φ p k)
  SuppL-mono Φ up le n (inj₁ p)  s = up p le s
  SuppL-mono Φ up le n (inj₂ d′) s = Supp-mono Φ up le n d′ s

mutual
  uniformize : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′)
             → (∀ p → Σ[ i ∈ ℕ ] Φ p i)
             → (n : ℕ) (d : Dₚ A) → Σ[ i ∈ ℕ ] Supp n d (λ p → Φ p i)
  uniformize Φ up w zero    d = 0 , tt
  uniformize Φ up w (suc n) d =
    let i₁ , s₁ = uniformizeL Φ up w n (br d true)
        i₂ , s₂ = uniformizeL Φ up w n (br d false)
    in i₁ ⊔ i₂
     , SuppL-mono Φ (λ p → up p) (m≤m⊔n i₁ i₂) n (br d true) s₁
     , SuppL-mono Φ (λ p → up p) (m≤n⊔m i₁ i₂) n (br d false) s₂

  uniformizeL : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′)
              → (∀ p → Σ[ i ∈ ℕ ] Φ p i)
              → (n : ℕ) (x : A ⊎ Dₚ A) → Σ[ i ∈ ℕ ] SuppL n x (λ p → Φ p i)
  uniformizeL Φ up w n (inj₁ p)  = w p
  uniformizeL Φ up w n (inj₂ d′) = uniformize Φ up w n d′

-- `Supp` is not `_≈ₚ_`-stable, so it is computed at the literal terms
-- (`Supp-bot`/`Supp-return`/`Supp-bind`).

Supp-bot : (Φ : A → Set b) (n : ℕ) → Supp n (botₚ {A = A}) Φ
Supp-bot Φ zero    = tt
Supp-bot Φ (suc n) = Supp-bot Φ n , Supp-bot Φ n

Supp-return : (Φ : A → Set b) (p : A) → Φ p → (n : ℕ) → Supp n (returnₚ p) Φ
Supp-return Φ p h zero    = tt
Supp-return Φ p h (suc n) = h , h

-- The continuation's budget is quantified, not inherited: the junction spends a
-- step.
mutual
  Supp-bind : (Φ : B → Set b) (n : ℕ) (d : Dₚ A) (f : A → Dₚ B)
            → Supp n d (λ p → (i : ℕ) → Supp i (f p) Φ) → Supp n (d >>=ₚ f) Φ
  Supp-bind Φ zero    d f sp        = tt
  Supp-bind Φ (suc n) d f (s₁ , s₂) =
    SuppL-bind Φ n (br d true) f s₁ , SuppL-bind Φ n (br d false) f s₂

  SuppL-bind : (Φ : B → Set b) (n : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B)
             → SuppL n x (λ p → (i : ℕ) → Supp i (f p) Φ) → SuppL n (tagₚ x f) Φ
  SuppL-bind Φ n (inj₁ p)  f sp = sp n
  SuppL-bind Φ n (inj₂ d′) f sp = Supp-bind Φ n d′ f sp

mutual
  Supp-map : (Φ Ψ : A → Set b) → (∀ p → Φ p → Ψ p)
           → (n : ℕ) (d : Dₚ A) → Supp n d Φ → Supp n d Ψ
  Supp-map Φ Ψ f zero    d sp        = tt
  Supp-map Φ Ψ f (suc n) d (s₁ , s₂) =
    SuppL-map Φ Ψ f n (br d true) s₁ , SuppL-map Φ Ψ f n (br d false) s₂

  SuppL-map : (Φ Ψ : A → Set b) → (∀ p → Φ p → Ψ p)
            → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x Φ → SuppL n x Ψ
  SuppL-map Φ Ψ f n (inj₁ p)  s = f p s
  SuppL-map Φ Ψ f n (inj₂ d′) s = Supp-map Φ Ψ f n d′ s

mutual
  Supp-all : (Φ : A → Set b) → (∀ p → Φ p) → (n : ℕ) (d : Dₚ A) → Supp n d Φ
  Supp-all Φ w zero    d = tt
  Supp-all Φ w (suc n) d = SuppL-all Φ w n (br d true) , SuppL-all Φ w n (br d false)

  SuppL-all : (Φ : A → Set b) → (∀ p → Φ p) → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x Φ
  SuppL-all Φ w n (inj₁ p)  = w p
  SuppL-all Φ w n (inj₂ d′) = Supp-all Φ w n d′

-- `uniformizeˢ` is `uniformize` with the per-value witness assumed only on the
-- support: an unreachable loop re-entry has no bound at all (`Dp.Settle.Iter`).
mutual
  uniformizeˢ : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′)
              → (n : ℕ) (d : Dₚ A) → Supp n d (λ p → Σ[ i ∈ ℕ ] Φ p i)
              → Σ[ i ∈ ℕ ] Supp n d (λ p → Φ p i)
  uniformizeˢ Φ up zero    d sp        = 0 , tt
  uniformizeˢ Φ up (suc n) d (s₁ , s₂) =
    let i₁ , t₁ = uniformizeLˢ Φ up n (br d true)  s₁
        i₂ , t₂ = uniformizeLˢ Φ up n (br d false) s₂
    in i₁ ⊔ i₂
     , SuppL-mono Φ (λ p → up p) (m≤m⊔n i₁ i₂) n (br d true) t₁
     , SuppL-mono Φ (λ p → up p) (m≤n⊔m i₁ i₂) n (br d false) t₂

  uniformizeLˢ : (Φ : A → ℕ → Set b) → (∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′)
               → (n : ℕ) (x : A ⊎ Dₚ A) → SuppL n x (λ p → Σ[ i ∈ ℕ ] Φ p i)
               → Σ[ i ∈ ℕ ] SuppL n x (λ p → Φ p i)
  uniformizeLˢ Φ up n (inj₁ p)  s = s
  uniformizeLˢ Φ up n (inj₂ d′) s = uniformizeˢ Φ up n d′ s

------------------------------------------------------------------------
-- The equivalence: cofinal domination of the cumulative masses
--
-- `d ≼ₚ d′` says every depth-`n` observation of `d` is matched at SOME depth of
-- `d′`.  For a fixed non-negative test the two `cum` families are monotone, so
-- this says exactly `sup ≤ sup` — with rational witnesses and no supremum.

cumₛ : {A : Set a} → Dₚ A → (A → ℚ) → ℕ → ℚ
cumₛ d P n = cum n d P

-- `Cofinal` is exact rather than `Dom` at `0ℚ`: `+ 0ℚ` does not reduce, so every
-- exact witness would pay a `+-identityʳ`.
Cofinal : {A : Set a} {B : Set b} → (A → ℚ) → (B → ℚ) → Dₚ A → Dₚ B → Set
Cofinal P Q d e = cumₛ d P ≼ cumₛ e Q

Dom : (A → ℚ) → ℚ → Dₚ A → Dₚ A → Set
Dom P ε d e = cumₛ d P ≼[ ε ] cumₛ e P

cofinal-refl : (P : A → ℚ) (d : Dₚ A) → Cofinal P P d d
cofinal-refl P d = ≼-refl (cumₛ d P)

cofinal-trans : {A : Set a} {B : Set b} {C : Set c} {P : A → ℚ} {Q : B → ℚ} {R : C → ℚ}
                (d : Dₚ A) (e : Dₚ B) (h : Dₚ C)
              → Cofinal P Q d e → Cofinal Q R e h → Cofinal P R d h
cofinal-trans {P = P} {Q} {R} d e h = ≼-trans (cumₛ d P) (cumₛ e Q) (cumₛ h R)

cofinal⇒dom : {d e : Dₚ A} → Cofinal P P d e → Dom P 0ℚ d e
cofinal⇒dom {P = P} {d = d} {e = e} = ≼⇒≼[0] (cumₛ d P) (cumₛ e P)

dom-mono : {d e : Dₚ A} → ε ℚ.≤ δ → Dom P ε d e → Dom P δ d e
dom-mono {P = P} {d = d} {e = e} = ≼[]-mono (cumₛ d P) (cumₛ e P)

dom-trans : {d e h : Dₚ A} → Dom P ε d e → Dom P δ e h → Dom P (ε ℚ.+ δ) d h
dom-trans {P = P} {d = d} {e = e} {h = h} = ≼[]-trans (cumₛ d P) (cumₛ e P) (cumₛ h P)

dom-resp : {d d′ e e′ : Dₚ A} → Cofinal P P d′ d → Cofinal P P e e′ → Dom P ε d e → Dom P ε d′ e′
dom-resp {P = P} {d = d} {d′ = d′} {e = e} {e′ = e′} =
  ≼[]-resp (cumₛ d P) (cumₛ d′ P) (cumₛ e P) (cumₛ e′ P)

infix 4 _≼ₚ_ _≈ₚ_

_≼ₚ_ : Dₚ A → Dₚ A → Set _
_≼ₚ_ {A = A} d d′ = (P : A → ℚ) → NNF P → Cofinal P P d d′

_≈ₚ_ : Dₚ A → Dₚ A → Set _
d ≈ₚ d′ = (d ≼ₚ d′) × (d′ ≼ₚ d)

≼ₚ-refl : (d : Dₚ A) → d ≼ₚ d
≼ₚ-refl d P nn = cofinal-refl P d

≼ₚ-trans : (d e h : Dₚ A) → d ≼ₚ e → e ≼ₚ h → d ≼ₚ h
≼ₚ-trans d e h de eh P nn = cofinal-trans d e h (de P nn) (eh P nn)

≈ₚ-refl : (d : Dₚ A) → d ≈ₚ d
≈ₚ-refl d = ≼ₚ-refl d , ≼ₚ-refl d

≈ₚ-sym : (d e : Dₚ A) → d ≈ₚ e → e ≈ₚ d
≈ₚ-sym d e = swap

≈ₚ-trans : (d e h : Dₚ A) → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
≈ₚ-trans d e h (de , ed) (eh , he) = ≼ₚ-trans d e h de eh , ≼ₚ-trans h e d he ed

≈ₚ⇒cofinal : {d e : Dₚ A} (P : A → ℚ) → NNF P → d ≈ₚ e → Cofinal P P d e
≈ₚ⇒cofinal P nn eq = proj₁ eq P nn

exact⇒≈ₚ : (d e : Dₚ A) → (∀ (P : A → ℚ) n → cum n d P ≡ cum n e P) → d ≈ₚ e
exact⇒≈ₚ d e eq =
  (λ P nn n → n , ≤-reflexive (eq P n)) , λ P nn n → n , ≤-reflexive (sym (eq P n))

shift⇒≈ₚ : (d e : Dₚ A) → (∀ (P : A → ℚ) n → cum (suc n) d P ≡ cum n e P) → d ≈ₚ e
shift⇒≈ₚ d e eq =
    (λ where P nn zero    → 0 , ≤-refl
             P nn (suc n) → n , ≤-reflexive (eq P n))
  , λ P nn n → suc n , ≤-reflexive (sym (eq P n))

------------------------------------------------------------------------
-- Delays are invisible; divergence is worth nothing

dirac-cum : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) → cum (suc n) (dirac x) P ≡ leafₚ n x P
dirac-cum n x P = node-dirac (leafₚ n x P) (leafₚ n x P)

laterₚ-cum : (n : ℕ) (d : Dₚ A) (P : A → ℚ) → cum (suc n) (laterₚ d) P ≡ cum n d P
laterₚ-cum n d P = dirac-cum n (inj₂ d) P

laterₚ-≈ₚ : (d : Dₚ A) → laterₚ d ≈ₚ d
laterₚ-≈ₚ d = shift⇒≈ₚ (laterₚ d) d (λ P n → laterₚ-cum n d P)

returnₚ-cum : (n : ℕ) (p : A) (P : A → ℚ) → cum (suc n) (returnₚ p) P ≡ P p
returnₚ-cum n p P = dirac-cum n (inj₁ p) P

botₚ-cum : (n : ℕ) (P : A → ℚ) → cum n (botₚ {A = A}) P ≡ 0ℚ
botₚ-cum zero    P = refl
botₚ-cum (suc n) P = trans (dirac-cum n (inj₂ botₚ) P) (botₚ-cum n P)

-- A junction on a divergence diverges: `botₚ >>=ₚ f` is not a `dirac`, but its
-- weights are, so the same two-term arithmetic settles it.
bot-bind-cum : (n : ℕ) (f : A → Dₚ B) (P : B → ℚ) → cum n (botₚ >>=ₚ f) P ≡ 0ℚ
bot-bind-cum zero    f P = refl
bot-bind-cum (suc n) f P =
  trans (node-dirac (cum n (botₚ >>=ₚ f) P) (cum n (botₚ >>=ₚ f) P)) (bot-bind-cum n f P)

bot-bind-≈ₚ : (f : A → Dₚ B) → (botₚ >>=ₚ f) ≈ₚ botₚ
bot-bind-≈ₚ f = exact⇒≈ₚ (botₚ >>=ₚ f) botₚ λ P n →
  trans (bot-bind-cum n f P) (sym (botₚ-cum n P))

------------------------------------------------------------------------
-- Monad laws, as exact `cum` identities

>>=ₚ-identityˡ-cum : (n : ℕ) (p : A) (f : A → Dₚ B) (P : B → ℚ)
                   → cum (suc n) (returnₚ p >>=ₚ f) P ≡ cum n (f p) P
>>=ₚ-identityˡ-cum n p f P = node-dirac (cum n (f p) P) (cum n (f p) P)

>>=ₚ-identityˡ : (p : A) (f : A → Dₚ B) → (returnₚ p >>=ₚ f) ≈ₚ f p
>>=ₚ-identityˡ p f = shift⇒≈ₚ (returnₚ p >>=ₚ f) (f p) λ P n → >>=ₚ-identityˡ-cum n p f P

leafₚ-tag-zero : (x : A ⊎ Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → leafₚ 0 (tagₚ x f) P ≡ 0ℚ
leafₚ-tag-zero (inj₁ p)  f P = refl
leafₚ-tag-zero (inj₂ d′) f P = refl

cum-1-bind : (d : Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → cum 1 (d >>=ₚ f) P ≡ 0ℚ
cum-1-bind d f P =
  trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-tag-zero (br d true) f P))
                     (cong (wt d false ℚ.*_) (leafₚ-tag-zero (br d false) f P)))
        (node-zero (wt d true) (wt d false))

mutual
  >>=ₚ-identityʳ-cum : (n : ℕ) (d : Dₚ A) (P : A → ℚ)
                     → cum (suc n) (d >>=ₚ returnₚ) P ≡ cum n d P
  >>=ₚ-identityʳ-cum zero    d P = cum-1-bind d returnₚ P
  >>=ₚ-identityʳ-cum (suc n) d P =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-identityʳ n (br d true) P))
                (cong (wt d false ℚ.*_) (leafₚ-identityʳ n (br d false) P))

  leafₚ-identityʳ : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ)
                  → leafₚ (suc n) (tagₚ x returnₚ) P ≡ leafₚ n x P
  leafₚ-identityʳ n (inj₁ p)  P = returnₚ-cum n p P
  leafₚ-identityʳ n (inj₂ d′) P = >>=ₚ-identityʳ-cum n d′ P

>>=ₚ-identityʳ : (d : Dₚ A) → (d >>=ₚ returnₚ) ≈ₚ d
>>=ₚ-identityʳ d = shift⇒≈ₚ (d >>=ₚ returnₚ) d λ P n → >>=ₚ-identityʳ-cum n d P

mutual
  >>=ₚ-assoc-cum : (n : ℕ) (d : Dₚ A) (f : A → Dₚ B) (g : B → Dₚ C) (P : C → ℚ)
                 → cum n ((d >>=ₚ f) >>=ₚ g) P ≡ cum n (d >>=ₚ λ p → f p >>=ₚ g) P
  >>=ₚ-assoc-cum zero    d f g P = refl
  >>=ₚ-assoc-cum (suc n) d f g P =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-assoc n (br d true) f g P))
                (cong (wt d false ℚ.*_) (leafₚ-assoc n (br d false) f g P))

  leafₚ-assoc : (n : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B) (g : B → Dₚ C) (P : C → ℚ)
              → leafₚ n (tagₚ (tagₚ x f) g) P ≡ leafₚ n (tagₚ x (λ p → f p >>=ₚ g)) P
  leafₚ-assoc n (inj₁ p)  f g P = refl
  leafₚ-assoc n (inj₂ d′) f g P = >>=ₚ-assoc-cum n d′ f g P

>>=ₚ-assoc : (d : Dₚ A) (f : A → Dₚ B) (g : B → Dₚ C)
           → ((d >>=ₚ f) >>=ₚ g) ≈ₚ (d >>=ₚ λ p → f p >>=ₚ g)
>>=ₚ-assoc d f g =
  exact⇒≈ₚ ((d >>=ₚ f) >>=ₚ g) (d >>=ₚ λ p → f p >>=ₚ g) λ P n → >>=ₚ-assoc-cum n d f g P

------------------------------------------------------------------------
-- `mapₚ` and `returnₚ` against a test

mutual
  mapₚ-cum : (n : ℕ) (h : A → B) (d : Dₚ A) (P : B → ℚ)
           → cum (suc n) (mapₚ h d) P ≡ cum n d (P ∘′ h)
  mapₚ-cum zero    h d P = cum-1-bind d (returnₚ ∘′ h) P
  mapₚ-cum (suc n) h d P =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-mapₚ n h (br d true) P))
                (cong (wt d false ℚ.*_) (leafₚ-mapₚ n h (br d false) P))

  leafₚ-mapₚ : (n : ℕ) (h : A → B) (x : A ⊎ Dₚ A) (P : B → ℚ)
             → leafₚ (suc n) (tagₚ x (returnₚ ∘′ h)) P ≡ leafₚ n x (P ∘′ h)
  leafₚ-mapₚ n h (inj₁ p)  P = returnₚ-cum n (h p) P
  leafₚ-mapₚ n h (inj₂ d′) P = mapₚ-cum n h d′ P

mapₚ-≤ : (n : ℕ) (h : A → B) (d : Dₚ A) (P : B → ℚ) → NNF P
       → cum n (mapₚ h d) P ℚ.≤ cum n d (P ∘′ h)
mapₚ-≤ zero    h d P nn = ≤-refl
mapₚ-≤ (suc n) h d P nn =
  ≤-trans (≤-reflexive (mapₚ-cum n h d P)) (cum-mono (n≤1+n n) d (P ∘′ h) λ p → nn (h p))

returnₚ-cum-≤ : (n : ℕ) (q : A) (P : A → ℚ) → NNF P → cum n (returnₚ q) P ℚ.≤ P q
returnₚ-cum-≤ zero    q P nn = nn q
returnₚ-cum-≤ (suc n) q P nn = ≤-reflexive (returnₚ-cum n q P)

------------------------------------------------------------------------
-- The bind sandwich
--
-- A bind's depth-`n` mass lies between two `cum`s of its factors; with
-- `uniformize` this is all of `>>=ₚ-cong`.

mutual
  >>=ₚ-boundA : (n : ℕ) (d : Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → NNF P
              → cum n (d >>=ₚ f) P ℚ.≤ cum n d (λ p → cum n (f p) P)
  >>=ₚ-boundA zero    d f P nn = ≤-refl
  >>=ₚ-boundA (suc n) d f P nn =
    node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
              (leafₚ-boundA n (br d true) f P nn) (leafₚ-boundA n (br d false) f P nn)

  leafₚ-boundA : (n : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → NNF P
               → leafₚ n (tagₚ x f) P ℚ.≤ leafₚ n x (λ p → cum (suc n) (f p) P)
  leafₚ-boundA n (inj₁ p)  f P nn = cum-mono (n≤1+n n) (f p) P nn
  leafₚ-boundA n (inj₂ d′) f P nn =
    ≤-trans (>>=ₚ-boundA n d′ f P nn)
            (cum-mono-P n d′ (λ p → cum n (f p) P) (λ p → cum (suc n) (f p) P)
                        λ p → cum-mono (n≤1+n n) (f p) P nn)

mutual
  >>=ₚ-boundB : (n m : ℕ) (d : Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → NNF P
              → cum n d (λ p → cum m (f p) P) ℚ.≤ cum (n +ℕ m) (d >>=ₚ f) P
  >>=ₚ-boundB zero    m d f P nn = cum-nn m (d >>=ₚ f) P nn
  >>=ₚ-boundB (suc n) m d f P nn =
    node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
              (leafₚ-boundB n m (br d true) f P nn) (leafₚ-boundB n m (br d false) f P nn)

  leafₚ-boundB : (n m : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → NNF P
               → leafₚ n x (λ p → cum m (f p) P) ℚ.≤ leafₚ (n +ℕ m) (tagₚ x f) P
  leafₚ-boundB n m (inj₁ p)  f P nn = cum-mono (m≤n+m m n) (f p) P nn
  leafₚ-boundB n m (inj₂ d′) f P nn = >>=ₚ-boundB n m d′ f P nn

------------------------------------------------------------------------
-- The bind congruence

>>=ₚ-congᵖ : (d d′ : Dₚ A) (f g : A → Dₚ B) → d ≼ₚ d′ → (∀ p → f p ≼ₚ g p)
           → (d >>=ₚ f) ≼ₚ (d′ >>=ₚ g)
>>=ₚ-congᵖ d d′ f g dd fg P nn n =
  let i , le  = dd (λ p → cum n (f p) P) (λ p → cum-nn n (f p) P nn) n
      i′ , sp = uniformize (λ p i″ → cum n (f p) P ℚ.≤ cum i″ (g p) P) up wit i d′
  in i +ℕ i′
   , ≤-trans (>>=ₚ-boundA n d f P nn)
     (≤-trans le
     (≤-trans (cum-mono-Supp i d′ (λ p → cum n (f p) P) (λ p → cum i′ (g p) P) sp)
              (>>=ₚ-boundB i i′ d′ g P nn)))
  where
  up : ∀ p {i i′} → i ≤ℕ i′ → cum n (f p) P ℚ.≤ cum i (g p) P → cum n (f p) P ℚ.≤ cum i′ (g p) P
  up p le h = ≤-trans h (cum-mono le (g p) P nn)

  wit : ∀ p → Σ[ i ∈ ℕ ] (cum n (f p) P ℚ.≤ cum i (g p) P)
  wit p = fg p P nn n

>>=ₚ-cong : (d d′ : Dₚ A) (f g : A → Dₚ B) → d ≈ₚ d′ → (∀ p → f p ≈ₚ g p)
          → (d >>=ₚ f) ≈ₚ (d′ >>=ₚ g)
>>=ₚ-cong d d′ f g (dd , d′d) fg =
    >>=ₚ-congᵖ d d′ f g dd (λ p → proj₁ (fg p))
  , >>=ₚ-congᵖ d′ d g f d′d (λ p → proj₂ (fg p))

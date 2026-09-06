{-# OPTIONS --safe --without-K --guardedness #-}

-- The rational probabilistic delay monad `Dₚ A = ν X. S_ℚ (A ⊎ X)`, with a
-- delay-insensitive equivalence stated entirely in `ℚ`: no lubs, no lower reals.
--
-- A step is a BIASED COIN, not a `Dist-ℚ`.  With a list-shaped step the functorial
-- action of a step needs structural recursion over the list, and `--guardedness`
-- rejects every mutual block that mixes such a recursion with a corecursive call.
-- Two branches need no recursion at all, and binary trees of rational coins
-- realise every finite rational distribution up to `_≈ₚ_` below, so nothing is
-- lost.  The invariants (`0 ≤ wt`, `wt true + wt false ≡ 1`) then live INSIDE the
-- coinductive record and `_>>=ₚ_` copies them verbatim: the one thing the checker
-- refuses, a corecursive call under a function application, never arises.
--
-- Divergence is delay, not a `nothing` point.  Mass that never reaches a value is
-- exactly what `cum` does not count, so `botₚ` and the mass a
-- `Dist⊥ = Dist-ℚ ∘ Maybe` step would park on `nothing` are indistinguishable
-- (`botₚ-cum`): `Maybe` is redundant here, and failure apart from divergence
-- composes on the value side as `Dₚ ∘ Maybe`.
--
-- `_>>=ₚ_` spends one step at the junction (`tagₚ (inj₁ p) f = inj₂ (f p)`).  That
-- step is invisible to the equivalence and it is what buys the EXACT `cum`
-- identities the monad laws are proved from — no splicing of distributions, hence
-- no list recursion.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤n+m; n≤1+n)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties as ℚP

open import Data.Rational.Properties.Ext
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

module ProbabilisticLogic.Dp where

private variable
  a b : Level
  A B C : Set a
  n m j k : ℕ

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

------------------------------------------------------------------------
-- The equivalence: cofinal domination of the cumulative masses
--
-- `d ≼ₚ d′` says every depth-`n` observation of `d` is matched at SOME depth of
-- `d′`.  For a fixed non-negative test the two `cum` families are monotone, so
-- this says exactly `sup ≤ sup` — with rational witnesses and no supremum.
--
-- Comparing LIMIT termination masses instead would bring the lower reals back, and
-- the mixed inductive-coinductive `laterˡ`/`laterʳ` weak bisimilarity is out
-- because its transitivity needs sized types, which are not `--safe`.

infix 4 _≼ₚ_ _≈ₚ_

_≼ₚ_ : Dₚ A → Dₚ A → Set _
_≼ₚ_ {A = A} d d′ = (P : A → ℚ) → NNF P → (n : ℕ) → Σ[ m ∈ ℕ ] (cum n d P ℚ.≤ cum m d′ P)

_≈ₚ_ : Dₚ A → Dₚ A → Set _
d ≈ₚ d′ = (d ≼ₚ d′) × (d′ ≼ₚ d)

≼ₚ-refl : (d : Dₚ A) → d ≼ₚ d
≼ₚ-refl d P nn n = n , ≤-refl

≼ₚ-trans : (d e h : Dₚ A) → d ≼ₚ e → e ≼ₚ h → d ≼ₚ h
≼ₚ-trans d e h de eh P nn n =
  let m , le  = de P nn n
      i , le′ = eh P nn m
  in i , ≤-trans le le′

≈ₚ-refl : (d : Dₚ A) → d ≈ₚ d
≈ₚ-refl d = ≼ₚ-refl d , ≼ₚ-refl d

≈ₚ-sym : (d e : Dₚ A) → d ≈ₚ e → e ≈ₚ d
≈ₚ-sym d e = swap

≈ₚ-trans : (d e h : Dₚ A) → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
≈ₚ-trans d e h (de , ed) (eh , he) = ≼ₚ-trans d e h de eh , ≼ₚ-trans h e d he ed

-- Both sides are blind at budget 0, so an exact `cum` identity from budget 1 on
-- suffices; and one up to a one-step shift is the shape every unit law has.
exact⇒≈ₚ : (d e : Dₚ A) → (∀ (P : A → ℚ) n → cum n d P ≡ cum n e P) → d ≈ₚ e
exact⇒≈ₚ d e eq =
  (λ P nn n → n , ≤-reflexive (eq P n)) , λ P nn n → n , ≤-reflexive (sym (eq P n))

exactˢ⇒≈ₚ : (d e : Dₚ A) → (∀ (P : A → ℚ) n → cum (suc n) d P ≡ cum (suc n) e P) → d ≈ₚ e
exactˢ⇒≈ₚ d e eq = exact⇒≈ₚ d e λ where P zero    → refl
                                        P (suc n) → eq P n

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

-- Budget 0 sees nothing of a bind: every branch of `d >>=ₚ f` is an `inj₂`.
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
-- The bind sandwich
--
-- A bind's depth-`n` mass is squeezed between two `cum`s of its two factors.
-- This pair is what turns the continuation's per-value domination witnesses into
-- a domination of the composites, i.e. it is the whole content of `>>=ₚ-cong`.

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

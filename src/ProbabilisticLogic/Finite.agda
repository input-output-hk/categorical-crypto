{-# OPTIONS --safe --without-K #-}

-- A finiteness witness on top of `Abstract`: an explicit association-list
-- presentation of a distribution `P`, certified to reproduce every
-- decidable event probability `P ∙ X`.  This unlocks a computable
-- `expectation` operator with the usual linearity laws — inherited from
-- the generic `Linearity` machinery instantiated at the probability
-- semiring.

open import categorical-crypto.Prelude as P
  hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Class.Decidable
open import Relation.Binary using (Setoid)
open import Relation.Unary using (_≐_)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning; cong₂)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Bool using (if_then_else_)
import Data.List.NonEmpty as NE
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import Data.Integer as ℤ
import Data.Integer.Properties as ℤP
open import Data.Integer using (+_)
open import Data.Integer.GCD using (gcd)
import Data.Rational as ℚ
open import Data.Rational using (ℚ; _/_; 0ℚ; 1ℚ; toℚᵘ)
open import Data.Rational.Properties using
  (toℚᵘ-injective; toℚᵘ-homo-+; ↥-/; ↧-/; ↥ᵘ-toℚᵘ; ↧ᵘ-toℚᵘ; 0/n≡0)
import Data.Rational.Unnormalised as ℚᵘ
open import Data.Rational.Unnormalised using (mkℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import LibExt using (module Arith)
open Arith using (n/n≡1ℚ)

open import ProbabilisticLogic.Abstract

module ProbabilisticLogic.Finite c ℓ (a : Abstract c ℓ) where

open Abstract a

import ProbabilisticLogic.Distribution.Linearity as Linearity
private module Lin = Linearity Probabilityᴿ

private
  module Eq = Setoid setoid

  variable
    Ω Ω₁ Ω₂ : Type

------------------------------------------------------------------------
-- `Probability`-valued indicator function for a decidable predicate.

1[_] : (X : Ω → Type) ⦃ _ : X ⁇¹ ⦄ → Ω → Probability
1[ X ] ω = ifᵈ X ω then 1# else 0#

------------------------------------------------------------------------
-- Finiteness witness.
--
-- A `Finite P` says: `P` admits the assoc-list presentation `entries`,
-- whose weights sum to one, and `P` is observationally (on ALL events,
-- not just decidable ones) the corresponding mixture of Dirac
-- distributions.  The decidable-event indicator form is derived below
-- (`represents-dec`).

record Finite (P : ProbDistr Ω) : Type (sucˡ lzero ⊔ˡ c ⊔ˡ ℓ) where
  field
    entries    : NE.List⁺ (Probability × Ω)
    mass-1     : Lin.mass-L (NE.toList entries) ≈ 1#
    represents : {X : Ω → Type}
               → P ∙ X ≈ kmix pure (NE.toList entries) X

open Finite public

------------------------------------------------------------------------
-- The expectation function.

expectation : ∀ {P : ProbDistr Ω} → Finite P → (Ω → Probability) → Probability
expectation fin f = Lin.lookup-L (NE.toList (entries fin)) f

------------------------------------------------------------------------
-- Linearity lemmas — direct consequences of `Linearity.lookup-L-…`.

expectation-cong-fn : ∀ {P : ProbDistr Ω} (fin : Finite P) {f g : Ω → Probability}
                    → (∀ ω → f ω ≈ g ω)
                    → expectation fin f ≈ expectation fin g
expectation-cong-fn fin = Lin.lookup-L-cong-P (NE.toList (entries fin))

expectation-+ : ∀ {P : ProbDistr Ω} (fin : Finite P) (f g : Ω → Probability)
              → expectation fin (λ ω → f ω + g ω)
              ≈ expectation fin f + expectation fin g
expectation-+ fin = Lin.lookup-L-+ (NE.toList (entries fin))

expectation-*ₗ : ∀ {P : ProbDistr Ω} (fin : Finite P) (k : Probability) (f : Ω → Probability)
               → expectation fin (λ ω → k * f ω) ≈ k * expectation fin f
expectation-*ₗ fin k = Lin.lookup-L-*ₗ k (NE.toList (entries fin))

expectation-zero : ∀ {P : ProbDistr Ω} (fin : Finite P)
                 → expectation fin (λ _ → 0#) ≈ 0#
expectation-zero fin = Lin.lookup-L-zero (NE.toList (entries fin))

-- A constant test function has expectation equal to the constant
-- (since the total mass is 1).
expectation-const : ∀ {P : ProbDistr Ω} (fin : Finite P) (c′ : Probability)
                  → expectation fin (λ _ → c′) ≈ c′
expectation-const fin c′ = begin
  Lin.lookup-L (NE.toList (entries fin)) (λ _ → c′)
    ≈⟨ Lin.lookup-L-const (NE.toList (entries fin)) c′ ⟩
  Lin.mass-L (NE.toList (entries fin)) * c′
    ≈⟨ *-congʳ (mass-1 fin) ⟩
  1# * c′
    ≈⟨ *-identityˡ c′ ⟩
  c′ ∎
  where open ≈-Reasoning setoid

-- Fubini: nested expectations commute over independent witnesses.
expectation-swap : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                   (finP : Finite P) (finQ : Finite Q)
                   (f : Ω₁ → Ω₂ → Probability)
                 → expectation finP (λ a → expectation finQ (f a))
                 ≈ expectation finQ (λ b → expectation finP (λ a → f a b))
expectation-swap finP finQ =
  Lin.lookup-L-swap (NE.toList (entries finP)) (NE.toList (entries finQ))

------------------------------------------------------------------------
-- `kmix` evaluated through `lookup-L`: a mixture is the weighted sum
-- of the per-point event probabilities.

kmix-lookup : (k : Ω₁ → ProbDistr Ω₂) (ls : List (Probability × Ω₁)) {X : Ω₂ → Type}
            → kmix k ls X ≈ Lin.lookup-L ls (λ ω → k ω ∙ X)
kmix-lookup k []             = Eq.refl
kmix-lookup k ((w , ω) ∷ ls) = +-congˡ (kmix-lookup k ls)

------------------------------------------------------------------------
-- Constructors.
--
-- These build a `Finite` witness for the various distribution
-- constructors of `Abstract`.

private
  -- A decidable predicate is equivalent to its `↑·⌊_⌋`-Boolean form.
  -- (Same as `Logic.P-Dec` for events, but at the predicate level.)
  Dec≐ : (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄ → X ≐ ↑ (λ ω → ⌊ ¿ X ω ¿ ⌋)
  Dec≐ X = fromWitness , toWitness

  -- `1# * x + 0# ≈ x` — the "trailing tail of zero, leading factor of one"
  -- simplification that the lookup against a singleton list produces.
  trim : (x : Probability) → 1# * x + 0# ≈ x
  trim x = Eq.trans (+-congʳ (*-identityˡ x)) (+-identityʳ x)

  -- `pure ω ∙ X` reduces to the indicator at `ω`.  Via the empirical
  -- definition of `pure` and `empirical-eq` on the singleton list, with
  -- a case-split on the decidability of `X ω` to interpret the count.
  pure-∙ : (ω : Ω) (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄ → pure ω ∙ X ≈ 1[ X ] ω
  pure-∙ ω X = begin
      pure ω ∙ X
        ≈⟨ ∙-cong (Dec≐ X) ⟩
      empirical (ω NE.∷ []) ∙ (↑ (λ ω' → ⌊ ¿ X ω' ¿ ⌋))
        ≈⟨ empirical-eq ⟩
      fromℚ (+ length (filterᵇ (λ ω' → ⌊ ¿ X ω' ¿ ⌋) (ω ∷ [])) / 1)
        ≈⟨ count-bridge ⟩
      1[ X ] ω ∎
    where
      open ≈-Reasoning setoid

      count-bridge : fromℚ (+ length (filterᵇ (λ ω' → ⌊ ¿ X ω' ¿ ⌋) (ω ∷ [])) / 1)
                   ≈ 1[ X ] ω
      count-bridge with ¿ X ω ¿
      ... | yes _ = fromℚ-1
      ... | no _  = fromℚ-0

pure-Finite : (ω : Ω) → Finite (pure ω)
pure-Finite ω = record
  { entries    = (1# , ω) NE.∷ []
  ; mass-1     = trim 1#
  ; represents = λ {X} → Eq.sym (trim (pure ω ∙ X))
  }

-- The expectation of `pure ω` is the value at `ω` (the abstract
-- analogue of `Dist-ℚ`'s `lookupᴰℚ-return`).
expectation-pure : (ω : Ω) (f : Ω → Probability)
                 → expectation (pure-Finite ω) f ≈ f ω
expectation-pure ω f = trim (f ω)

------------------------------------------------------------------------
-- Bridge between `expectation` and the abstract `_∙_`: on decidable
-- events, the Dirac-mixture representation computes to the lookup of
-- the indicator, so the expectation of `1[ X ]` is the probability of
-- `X`.

private
  kmix-pure-dec : (es : List (Probability × Ω)) (X : Ω → Type) ⦃ _ : X ⁇¹ ⦄
                → kmix pure es X ≈ Lin.lookup-L es 1[ X ]
  kmix-pure-dec []             X = Eq.refl
  kmix-pure-dec ((w , ω) ∷ es) X = +-cong (*-congˡ (pure-∙ ω X)) (kmix-pure-dec es X)

-- The decidable-event form of `represents`.
represents-dec : ∀ {P : ProbDistr Ω} (fin : Finite P)
               → (X : Ω → Type) ⦃ _ : X ⁇¹ ⦄
               → P ∙ X ≈ Lin.lookup-L (NE.toList (entries fin)) 1[ X ]
represents-dec fin X = Eq.trans (represents fin) (kmix-pure-dec (NE.toList (entries fin)) X)

expectation-1[X] : ∀ {P : ProbDistr Ω} (fin : Finite P)
                 → (X : Ω → Type) ⦃ _ : X ⁇¹ ⦄
                 → expectation fin 1[ X ] ≈ P ∙ X
expectation-1[X] fin X = Eq.sym (represents-dec fin X)

------------------------------------------------------------------------
-- `empirical-Finite`: the uniform distribution over a non-empty list.
--
-- The witness assigns weight `fromℚ (1 / n)` to each element (with
-- multiplicity), where `n` is the list length.  The crux is the
-- rational identity that uniform weights over the support sum to the
-- count divided by `n` — i.e. same-denominator fraction addition,
-- which std-lib lacks and we prove via the unnormalised rationals.

private
  -- Same-denominator fraction addition.  Proven by mapping to the
  -- unnormalised rationals (where `_+_` does not renormalise) via the
  -- homomorphism `toℚᵘ`, and a `toℚᵘ (i / n) ≃ᵘ mkℚᵘ i n` bridge.
  module FracArith where
    toℚᵘ-/ : ∀ (i : ℤ.ℤ) (m : ℕ.ℕ) → toℚᵘ (i / suc m) ℚᵘ.≃ mkℚᵘ i m
    toℚᵘ-/ i m = ℚᵘ.*≡* eq
      where
        n = suc m
        g = gcd i (+ n)
        open ≡-Reasoning
        eq : ℚᵘ.↥ (toℚᵘ (i / n)) ℤ.* (+ n) ≡ i ℤ.* ℚᵘ.↧ (toℚᵘ (i / n))
        eq = begin
          ℚᵘ.↥ (toℚᵘ (i / n)) ℤ.* (+ n)
            ≡⟨ cong (ℤ._* (+ n)) (↥ᵘ-toℚᵘ (i / n)) ⟩
          ℚ.↥ (i / n) ℤ.* (+ n)
            ≡⟨ cong (ℚ.↥ (i / n) ℤ.*_) (P.sym (↧-/ i n)) ⟩
          ℚ.↥ (i / n) ℤ.* (ℚ.↧ (i / n) ℤ.* g)
            ≡⟨ P.sym (ℤP.*-assoc (ℚ.↥ (i / n)) (ℚ.↧ (i / n)) g) ⟩
          (ℚ.↥ (i / n) ℤ.* ℚ.↧ (i / n)) ℤ.* g
            ≡⟨ cong (ℤ._* g) (ℤP.*-comm (ℚ.↥ (i / n)) (ℚ.↧ (i / n))) ⟩
          (ℚ.↧ (i / n) ℤ.* ℚ.↥ (i / n)) ℤ.* g
            ≡⟨ ℤP.*-assoc (ℚ.↧ (i / n)) (ℚ.↥ (i / n)) g ⟩
          ℚ.↧ (i / n) ℤ.* (ℚ.↥ (i / n) ℤ.* g)
            ≡⟨ cong (ℚ.↧ (i / n) ℤ.*_) (↥-/ i n) ⟩
          ℚ.↧ (i / n) ℤ.* i
            ≡⟨ ℤP.*-comm (ℚ.↧ (i / n)) i ⟩
          i ℤ.* ℚ.↧ (i / n)
            ≡⟨ cong (i ℤ.*_) (P.sym (↧ᵘ-toℚᵘ (i / n))) ⟩
          i ℤ.* ℚᵘ.↧ (toℚᵘ (i / n)) ∎

    same-denom : ∀ (m c : ℕ.ℕ) → mkℚᵘ (+ 1) m ℚᵘ.+ mkℚᵘ (+ c) m ℚᵘ.≃ mkℚᵘ (+ suc c) m
    same-denom m c = ℚᵘ.*≡* eq
      where
        open ≡-Reasoning
        ℕeq : (1 ℕ.* suc m ℕ.+ c ℕ.* suc m) ℕ.* suc m
            ≡ suc c ℕ.* suc (m ℕ.+ m ℕ.* suc m)
        ℕeq = begin
          (1 ℕ.* suc m ℕ.+ c ℕ.* suc m) ℕ.* suc m
            ≡⟨ cong (λ z → (z ℕ.+ c ℕ.* suc m) ℕ.* suc m) (ℕP.*-identityˡ (suc m)) ⟩
          (suc m ℕ.+ c ℕ.* suc m) ℕ.* suc m
            ≡⟨ ℕP.*-assoc (suc c) (suc m) (suc m) ⟩
          suc c ℕ.* (suc m ℕ.* suc m) ∎
        eq : (+ 1 ℤ.* + suc m ℤ.+ + c ℤ.* + suc m) ℤ.* (+ suc m)
           ≡ (+ suc c) ℤ.* (+ suc (m ℕ.+ m ℕ.* suc m))
        eq = begin
          (+ 1 ℤ.* + suc m ℤ.+ + c ℤ.* + suc m) ℤ.* + suc m
            ≡⟨ cong (ℤ._* + suc m)
                 (cong₂ ℤ._+_ (P.sym (ℤP.pos-* 1 (suc m))) (P.sym (ℤP.pos-* c (suc m)))) ⟩
          (+ (1 ℕ.* suc m) ℤ.+ + (c ℕ.* suc m)) ℤ.* + suc m
            ≡⟨ cong (ℤ._* + suc m) (P.sym (ℤP.pos-+ (1 ℕ.* suc m) (c ℕ.* suc m))) ⟩
          + (1 ℕ.* suc m ℕ.+ c ℕ.* suc m) ℤ.* + suc m
            ≡⟨ P.sym (ℤP.pos-* (1 ℕ.* suc m ℕ.+ c ℕ.* suc m) (suc m)) ⟩
          + ((1 ℕ.* suc m ℕ.+ c ℕ.* suc m) ℕ.* suc m)
            ≡⟨ cong +_ ℕeq ⟩
          + (suc c ℕ.* suc (m ℕ.+ m ℕ.* suc m))
            ≡⟨ ℤP.pos-* (suc c) (suc (m ℕ.+ m ℕ.* suc m)) ⟩
          (+ suc c) ℤ.* + suc (m ℕ.+ m ℕ.* suc m) ∎

    frac-suc : ∀ (m c : ℕ.ℕ) → (+ 1 / suc m) ℚ.+ (+ c / suc m) ≡ + suc c / suc m
    frac-suc m c = toℚᵘ-injective (begin
      toℚᵘ ((+ 1 / suc m) ℚ.+ (+ c / suc m))
        ≈⟨ toℚᵘ-homo-+ (+ 1 / suc m) (+ c / suc m) ⟩
      toℚᵘ (+ 1 / suc m) ℚᵘ.+ toℚᵘ (+ c / suc m)
        ≈⟨ ℚᵘP.+-cong (toℚᵘ-/ (+ 1) m) (toℚᵘ-/ (+ c) m) ⟩
      mkℚᵘ (+ 1) m ℚᵘ.+ mkℚᵘ (+ c) m
        ≈⟨ same-denom m c ⟩
      mkℚᵘ (+ suc c) m
        ≈⟨ ℚᵘP.≃-sym (toℚᵘ-/ (+ suc c) m) ⟩
      toℚᵘ (+ suc c / suc m) ∎)
      where open ℚᵘP.≃-Reasoning

  -- `filterᵇ` with an always-true predicate is the identity.
  filterᵇ-true : (xs : List Ω) → filterᵇ (λ _ → true) xs ≡ xs
  filterᵇ-true []       = P.refl
  filterᵇ-true (x ∷ xs) = cong (x ∷_) (filterᵇ-true xs)

  -- The key lookup computation: the uniform-weight lookup of a
  -- `Bool`-indicator over `xs` equals `(count of true entries) / n`.
  uniform-lookup : (m : ℕ.ℕ) (b : Ω → Bool) (xs : List Ω)
    → Lin.lookup-L (map (λ ω → (fromℚ (+ 1 / suc m) , ω)) xs)
                   (λ ω → if b ω then 1# else 0#)
    ≈ fromℚ (+ length (filterᵇ b xs) / suc m)
  uniform-lookup m b [] =
    Eq.sym (Eq.trans (Eq.reflexive (cong fromℚ (0/n≡0 (suc m)))) fromℚ-0)
  uniform-lookup m b (ω ∷ xs) with b ω
  ... | true  = begin
      fromℚ (+ 1 / suc m) * 1#
        + Lin.lookup-L (map (λ ω → (fromℚ (+ 1 / suc m) , ω)) xs)
                       (λ ω → if b ω then 1# else 0#)
        ≈⟨ +-cong (*-identityʳ _) (uniform-lookup m b xs) ⟩
      fromℚ (+ 1 / suc m) + fromℚ (+ length (filterᵇ b xs) / suc m)
        ≈⟨ Eq.sym (fromℚ-+-homo (+ 1 / suc m) (+ length (filterᵇ b xs) / suc m)) ⟩
      fromℚ ((+ 1 / suc m) ℚ.+ (+ length (filterᵇ b xs) / suc m))
        ≡⟨ cong fromℚ (FracArith.frac-suc m (length (filterᵇ b xs))) ⟩
      fromℚ (+ suc (length (filterᵇ b xs)) / suc m) ∎
    where open ≈-Reasoning setoid
  ... | false = begin
      fromℚ (+ 1 / suc m) * 0#
        + Lin.lookup-L (map (λ ω → (fromℚ (+ 1 / suc m) , ω)) xs)
                       (λ ω → if b ω then 1# else 0#)
        ≈⟨ +-cong (zeroʳ _) (uniform-lookup m b xs) ⟩
      0# + fromℚ (+ length (filterᵇ b xs) / suc m)
        ≈⟨ +-identityˡ _ ⟩
      fromℚ (+ length (filterᵇ b xs) / suc m) ∎
    where open ≈-Reasoning setoid

empirical-Finite : (l : NE.List⁺ Ω) → Finite (empirical l)
empirical-Finite {Ω = Ω} (h NE.∷ t) = record
  { entries    = NE.map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) l
  ; mass-1     = mass-pf
  ; represents = empirical-mix
  }
  where
    l = h NE.∷ t
    m = length t

    open ≈-Reasoning setoid

    mass-pf : Lin.mass-L (NE.toList (NE.map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) l)) ≈ 1#
    mass-pf = begin
      Lin.lookup-L (map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) (NE.toList l)) (λ _ → 1#)
        ≈⟨ uniform-lookup m (λ _ → true) (NE.toList l) ⟩
      fromℚ (+ length (filterᵇ (λ _ → true) (NE.toList l)) / suc m)
        ≡⟨ cong (λ z → fromℚ (+ length z / suc m)) (filterᵇ-true (NE.toList l)) ⟩
      fromℚ (+ length (NE.toList l) / suc m)
        ≡⟨ cong fromℚ (n/n≡1ℚ (suc m)) ⟩
      fromℚ 1ℚ
        ≈⟨ fromℚ-1 ⟩
      1# ∎

------------------------------------------------------------------------
-- `>>=-Finite`: binding a finite distribution against a pointwise-
-- finite kernel.  The witness entries are the weighted concatenation
-- of the kernel witnesses' entries (mirroring `Dist-ℚ`'s `bindᴰ-cons`);
-- the obligations reduce to the generic evaluation lemma `bind-eval`
-- plus the `>>=-mix` marginalisation axiom.

module _ {Ω₁ Ω₂ : Type} {P : ProbDistr Ω₁} {k : Ω₁ → ProbDistr Ω₂}
         (finP : Finite P) (finK : (ω : Ω₁) → Finite (k ω)) where

  private
    kes : Ω₁ → List (Probability × Ω₂)
    kes ω = NE.toList (entries (finK ω))

    sc : Probability → (Probability × Ω₂) → (Probability × Ω₂)
    sc w e = (w * proj₁ e , proj₂ e)

    scale⁺ : Probability → NE.List⁺ (Probability × Ω₂) → NE.List⁺ (Probability × Ω₂)
    scale⁺ w = NE.map (sc w)

    bind-entries : (Probability × Ω₁) → List (Probability × Ω₁)
                 → NE.List⁺ (Probability × Ω₂)
    bind-entries (w , ω) []         = scale⁺ w (entries (finK ω))
    bind-entries (w , ω) (e ∷ rest) = scale⁺ w (entries (finK ω)) NE.⁺++⁺ bind-entries e rest

    -- Scaled lookup: pulling a constant weight out of a scaled entry list.
    lookup-sc : (w : Probability) (xs : List (Probability × Ω₂)) (f : Ω₂ → Probability)
              → Lin.lookup-L (map (sc w) xs) f ≈ w * Lin.lookup-L xs f
    lookup-sc w []             f = Eq.sym (zeroʳ w)
    lookup-sc w ((v , b) ∷ xs) f = begin
      (w * v) * f b + Lin.lookup-L (map (sc w) xs) f
        ≈⟨ +-cong (*-assoc w v (f b)) (lookup-sc w xs f) ⟩
      w * (v * f b) + w * Lin.lookup-L xs f
        ≈⟨ Eq.sym (distribˡ w (v * f b) (Lin.lookup-L xs f)) ⟩
      w * (v * f b + Lin.lookup-L xs f) ∎
      where open ≈-Reasoning setoid

    -- Evaluating any lookup against `bind-entries` gives the outer
    -- weighted sum of inner lookups — the finite Fubini for bind.
    bind-eval : (f : Ω₂ → Probability) (e : Probability × Ω₁) (rest : List (Probability × Ω₁))
              → Lin.lookup-L (NE.toList (bind-entries e rest)) f
              ≈ Lin.lookup-L (e ∷ rest) (λ ω → Lin.lookup-L (kes ω) f)
    bind-eval f (w , ω) [] = begin
      Lin.lookup-L (map (sc w) (kes ω)) f
        ≈⟨ lookup-sc w (kes ω) f ⟩
      w * Lin.lookup-L (kes ω) f
        ≈⟨ Eq.sym (+-identityʳ _) ⟩
      w * Lin.lookup-L (kes ω) f + 0# ∎
      where open ≈-Reasoning setoid
    bind-eval f (w , ω) (e ∷ rest) = begin
      Lin.lookup-L (map (sc w) (kes ω) ++ NE.toList (bind-entries e rest)) f
        ≈⟨ Lin.lookup-L-++ (map (sc w) (kes ω)) (NE.toList (bind-entries e rest)) f ⟩
      Lin.lookup-L (map (sc w) (kes ω)) f + Lin.lookup-L (NE.toList (bind-entries e rest)) f
        ≈⟨ +-cong (lookup-sc w (kes ω) f) (bind-eval f e rest) ⟩
      w * Lin.lookup-L (kes ω) f
        + Lin.lookup-L (e ∷ rest) (λ ω′ → Lin.lookup-L (kes ω′) f) ∎
      where open ≈-Reasoning setoid

    pe  = NE.head (entries finP)
    pes = NE.tail (entries finP)

  >>=-Finite : Finite (P >>= k)
  >>=-Finite = record
    { entries    = bind-entries pe pes
    ; mass-1     = mass-pf
    ; represents = represents-pf
    }
    where
      open ≈-Reasoning setoid

      mass-pf : Lin.mass-L (NE.toList (bind-entries pe pes)) ≈ 1#
      mass-pf = begin
        Lin.mass-L (NE.toList (bind-entries pe pes))
          ≈⟨ bind-eval (λ _ → 1#) pe pes ⟩
        Lin.lookup-L (pe ∷ pes) (λ ω → Lin.mass-L (kes ω))
          ≈⟨ Lin.lookup-L-cong-P (pe ∷ pes) (λ ω → mass-1 (finK ω)) ⟩
        Lin.lookup-L (pe ∷ pes) (λ _ → 1#)
          ≈⟨ mass-1 finP ⟩
        1# ∎

      represents-pf : {X : Ω₂ → Type}
        → (P >>= k) ∙ X ≈ kmix pure (NE.toList (bind-entries pe pes)) X
      represents-pf {X} = begin
        (P >>= k) ∙ X
          ≈⟨ >>=-mix {ls = pe ∷ pes} (represents finP) ⟩
        kmix k (pe ∷ pes) X
          ≈⟨ kmix-lookup k (pe ∷ pes) ⟩
        Lin.lookup-L (pe ∷ pes) (λ ω → k ω ∙ X)
          ≈⟨ Lin.lookup-L-cong-P (pe ∷ pes) (λ ω → Eq.trans (represents (finK ω))
               (kmix-lookup pure (kes ω))) ⟩
        Lin.lookup-L (pe ∷ pes) (λ ω → Lin.lookup-L (kes ω) (λ b → pure b ∙ X))
          ≈⟨ Eq.sym (bind-eval (λ b → pure b ∙ X) pe pes) ⟩
        Lin.lookup-L (NE.toList (bind-entries pe pes)) (λ b → pure b ∙ X)
          ≈⟨ Eq.sym (kmix-lookup pure (NE.toList (bind-entries pe pes))) ⟩
        kmix pure (NE.toList (bind-entries pe pes)) X ∎

  -- The expectation of a bind is the nested expectation — the workhorse
  -- for compositional reasoning (the abstract analogue of `Dist-ℚ`'s
  -- `lookupᴰℚ-bind`).
  expectation->>= : (f : Ω₂ → Probability)
                  → expectation >>=-Finite f
                  ≈ expectation finP (λ ω → expectation (finK ω) f)
  expectation->>= f = bind-eval f pe pes

------------------------------------------------------------------------
-- Functorial map, with its `Finite` witness and expectation rule (the
-- abstract analogues of `Dist-ℚ`'s `Dmap` and `lookupᴰℚ-Dmap`).

Dmap : (Ω₁ → Ω₂) → ProbDistr Ω₁ → ProbDistr Ω₂
Dmap f μ = μ >>= (λ ω → pure (f ω))

Dmap-Finite : {μ : ProbDistr Ω₁} (f : Ω₁ → Ω₂) → Finite μ → Finite (Dmap f μ)
Dmap-Finite f fin = >>=-Finite fin (λ ω → pure-Finite (f ω))

expectation-map : {μ : ProbDistr Ω₁} (f : Ω₁ → Ω₂) (fin : Finite μ)
                  (g : Ω₂ → Probability)
                → expectation (Dmap-Finite f fin) g ≈ expectation fin (λ ω → g (f ω))
expectation-map f fin g = Eq.trans
  (expectation->>= fin (λ ω → pure-Finite (f ω)) g)
  (expectation-cong-fn fin (λ ω → expectation-pure (f ω) g))

{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Class.HasOrder
open import Algebra
open import Algebra.Morphism.Structures using (module SemiringMorphisms)
open import Relation.Binary using (Setoid; IsPreorder)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Unary hiding (⌊_⌋)

import Data.List as L
import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_; 1ℚ)
import Data.Rational.Properties as ℚP
open import Data.Integer using (+_)

open import ProbabilisticLogic.Reasoning

open import LibExt using (module Lists; module Arith; module Predicates;
                          _⊠_; singleton-≐-rect)
open Lists using (_×ᴸ_; ×ᴸ-≐-rect; ∈ˡ-?; ∈ˡ-≐-T-∈?; filterᵇ-self)
open Arith using (n/n≡1ℚ)
open Predicates using (∪-∁-LEM; ∩-∁-partition)

module ProbabilisticLogic.Abstract where

open import Tactic.Solver.Ring using (solve-≈)

private variable Ω Ω₁ Ω₂ : Type

disjoint : (P Q : Ω → Type) → Type
disjoint P Q = ∀ {ω} → P ω → Q ω → ⊥

↑_ : (Ω → Bool) → Ω → Type
↑_ X = T P.∘ X

weighted-K : (l : NE.List⁺ (ℕ × Ω)) ⦃ _ : NonZero (proj₁ (NE.head l)) ⦄ → NE.List⁺ Ω
weighted-K ((suc m , ω) NE.∷ rest) =
  ω NE.∷ (replicate m ω ++ concatMap (λ (n , ω') → replicate n ω') rest)

record AbstractProbability c ℓ : Type (sucˡ (c ⊔ˡ ℓ)) where
  field Probabilityᴿ : CommutativeSemiring c ℓ

  open CommutativeSemiring Probabilityᴿ renaming (Carrier to Probability) public

  field _⁻¹ : (p : Probability) → ¬ p ≈ 0# → Probability
        d : Probability → Probability → Probability
        ⦃ HasPartialOrder-Probability ⦄
          : HasPartialOrder {A = Probability} {_≈_ = _≈_} {ℓ″ = ℓ} {ℓ‴ = ℓ}
        ≤-cong : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p * q ≤ p' * q'
        +-mono-≤ : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p + q ≤ p' + q'
        +-cancelʳ-≤ : ∀ {p q r : Probability} → p + r ≤ q + r → p ≤ q
        fromℚ : ℚ → Probability
        fromℚ-isSemiringHomomorphism
          : SemiringMorphisms.IsSemiringHomomorphism ℚP.+-*-rawSemiring rawSemiring fromℚ

  open SemiringMorphisms ℚP.+-*-rawSemiring rawSemiring
  open IsSemiringHomomorphism fromℚ-isSemiringHomomorphism public
    using (1#-homo)
    renaming (+-homo to fromℚ-+-homo; *-homo to fromℚ-*-homo; 0#-homo to fromℚ-0)

  fromℚ-homomorphism : ∀ {p q} → fromℚ p * fromℚ q ≈ fromℚ (p ℚ.* q)
  fromℚ-homomorphism {p} {q} = Eq.sym (fromℚ-*-homo p q)
    where module Eq = Setoid setoid

  fromℚ-1 : fromℚ (+ 1 / 1) ≈ 1#
  fromℚ-1 = 1#-homo

record AbstractCore c ℓ : Type (sucˡ (c ⊔ˡ ℓ)) where
  field abstractProbability : AbstractProbability c ℓ

  open AbstractProbability abstractProbability public

  field -- we assume discrete probability distributions, which don't need a σ-algebra
        ProbDistr : Type → Type c
        _∙_ : ProbDistr Ω → (Ω → Type) → Probability
        _∣_ : ProbDistr Ω → (X : Ω → Type) → ProbDistr Ω
        P∅≈0 : {P : ProbDistr Ω} → P ∙ ∅ ≈ 0#
        PU≈1 : {P : ProbDistr Ω} → P ∙ U ≈ 1#
        P-distrib-disjoint : ∀ {X Y} {P : ProbDistr Ω} → disjoint X Y → P ∙ X + P ∙ Y ≈ P ∙ (X ∪ Y)
        cond-probability : ∀ {P : ProbDistr Ω} {X Y} → P ∙ X * (P ∣ X) ∙ Y ≈ P ∙ (X ∩ Y)
        prob-monotonous : ∀ {P : ProbDistr Ω} {X Y} → X ⊆ Y → P ∙ X ≤ P ∙ Y
        ∣-cong : ∀ {P : ProbDistr Ω} {X X' Y : Ω → Type}
               → X ≐ X' → (P ∣ X) ∙ Y ≈ (P ∣ X') ∙ Y
        empirical : (l : NE.List⁺ Ω) → ProbDistr Ω
        empirical-eq : ∀ {l} {X : Ω → Bool}
                     → empirical l ∙ (↑ X) ≈ fromℚ (+ length (filterᵇ X (NE.toList l)) / NE.length l)
        cond-empirical : ∀ {l l'} {X : Ω → Bool} {Y : Ω → Type}
                       → filterᵇ X (NE.toList l) ≡ NE.toList l'
                       → (empirical l ∣ (↑ X)) ∙ Y ≈ empirical l' ∙ Y
        _⊗_ : ProbDistr Ω₁ → ProbDistr Ω₂ → ProbDistr (Ω₁ × Ω₂)
        ⊗-rect : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} {X : Ω₁ → Type} {Y : Ω₂ → Type}
               → (P ⊗ Q) ∙ (X ⊠ Y) ≈ P ∙ X * Q ∙ Y
        _>>=_ : ProbDistr Ω₁ → (Ω₁ → ProbDistr Ω₂) → ProbDistr Ω₂
        >>=-cong-l : ∀ {P Q : ProbDistr Ω₁} {f : Ω₁ → ProbDistr Ω₂} {Y : Ω₂ → Type}
                   → (∀ {X : Ω₁ → Type} → P ∙ X ≈ Q ∙ X)
                   → (P >>= f) ∙ Y ≈ (Q >>= f) ∙ Y

  pure : Ω → ProbDistr Ω
  pure ω = empirical (ω NE.∷ [])

  -- Evaluation of a finite `Probability`-weighted mixture of the
  -- kernel `k`'s outputs on an event: `Σᵢ wᵢ · (k ωᵢ) ∙ X`.
  kmix : (Ω₁ → ProbDistr Ω₂) → List (Probability × Ω₁) → (Ω₂ → Type) → Probability
  kmix k []             _ = 0#
  kmix k ((w , ω) ∷ ls) X = w * k ω ∙ X + kmix k ls X

  weighted : (l : NE.List⁺ (ℕ × Ω)) ⦃ _ : NonZero (proj₁ (NE.head l)) ⦄ → ProbDistr Ω
  weighted l = empirical (weighted-K l)

  private variable P : ProbDistr Ω
                   X Y : Ω → Type

  ∙-cong : X ≐ Y → P ∙ X ≈ P ∙ Y
  ∙-cong (X⊆Y , Y⊆X) = ≤-antisym (prob-monotonous X⊆Y) (prob-monotonous Y⊆X)

  0≤PX : 0# ≤ P ∙ X
  0≤PX {P = P} {X} = begin
    0#    ≈⟨ P∅≈0 ⟨
    P ∙ ∅ ≤⟨ prob-monotonous (λ ()) ⟩
    P ∙ X ∎
    where open ≤-Reasoning Probability

  PX≤1 : P ∙ X ≤ 1#
  PX≤1 {P = P} {X} = begin
    P ∙ X ≤⟨ prob-monotonous (λ _ → tt) ⟩
    P ∙ U ≈⟨ PU≈1 ⟩
    1#    ∎
    where open ≤-Reasoning Probability

  module _ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} where
    open ≈-Reasoning setoid
    ⊗-marg₁ : ∀ {X : Ω₁ → Type} → (P ⊗ Q) ∙ (X P.∘ proj₁) ≈ P ∙ X
    ⊗-marg₁ {X} = begin
      (P ⊗ Q) ∙ (X P.∘ proj₁) ≈⟨ ∙-cong ((λ Xa → Xa , tt) , proj₁) ⟩
      (P ⊗ Q) ∙ (X ⊠ U)       ≈⟨ ⊗-rect ⟩
      P ∙ X * Q ∙ U           ≈⟨ *-congˡ PU≈1 ⟩
      P ∙ X * 1#              ≈⟨ *-identityʳ _ ⟩
      P ∙ X                   ∎

    ⊗-marg₂ : ∀ {Y : Ω₂ → Type} → (P ⊗ Q) ∙ (Y P.∘ proj₂) ≈ Q ∙ Y
    ⊗-marg₂ {Y} = begin
      (P ⊗ Q) ∙ (Y P.∘ proj₂) ≈⟨ ∙-cong ((λ Yb → tt , Yb) , proj₂) ⟩
      (P ⊗ Q) ∙ (U ⊠ Y)       ≈⟨ ⊗-rect ⟩
      P ∙ U * Q ∙ Y           ≈⟨ *-congʳ PU≈1 ⟩
      1# * Q ∙ Y              ≈⟨ *-identityˡ _ ⟩
      Q ∙ Y                   ∎

    ⊗-cond-* : ∀ {X : Ω₁ → Type} {Y : Ω₂ → Type}
             → P ∙ X * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂) ≈ P ∙ X * Q ∙ Y
    ⊗-cond-* {X} {Y} = begin
      P ∙ X * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂)
        ≈⟨ *-congʳ ⊗-marg₁ ⟨
      (P ⊗ Q) ∙ (X P.∘ proj₁) * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂)
        ≈⟨ cond-probability ⟩
      (P ⊗ Q) ∙ ((X P.∘ proj₁) ∩ (Y P.∘ proj₂))
        ≈⟨ ⊗-rect ⟩
      P ∙ X * Q ∙ Y ∎

  empirical-⊗-rect : ∀ {l₁ : NE.List⁺ Ω₁} {l₂ : NE.List⁺ Ω₂} {X : Ω₁ → Bool} {Y : Ω₂ → Bool}
    → (empirical l₁ ⊗ empirical l₂) ∙ ((↑ X) ⊠ (↑ Y))
    ≈ fromℚ (+ length (filterᵇ X (NE.toList l₁)) / NE.length l₁)
        * fromℚ (+ length (filterᵇ Y (NE.toList l₂)) / NE.length l₂)
  empirical-⊗-rect {l₁ = l₁} {l₂} {X} {Y} = begin
    (empirical l₁ ⊗ empirical l₂) ∙ ((↑ X) ⊠ (↑ Y))
      ≈⟨ ⊗-rect ⟩
    empirical l₁ ∙ (↑ X) * empirical l₂ ∙ (↑ Y)
      ≈⟨ *-cong empirical-eq empirical-eq ⟩
    fromℚ (+ length (filterᵇ X (NE.toList l₁)) / NE.length l₁)
      * fromℚ (+ length (filterᵇ Y (NE.toList l₂)) / NE.length l₂) ∎
    where open ≈-Reasoning setoid

  ----------------------------------------------------------------------
  -- Complement of a full-mass event has zero mass; restriction to a
  -- full-mass event preserves probabilities.

  private
    module HPo = HasPartialOrder HasPartialOrder-Probability
    module HP  = HasPreorder HPo.hasPreorder

    ≈⇒≤-P : ∀ {x y : Probability} → x ≈ y → x ≤ y
    ≈⇒≤-P = IsPreorder.reflexive HP.≤-isPreorder

    1+p≈1⇒p≤0 : ∀ {p : Probability} → 1# + p ≈ 1# → p ≤ 0#
    1+p≈1⇒p≤0 {p} eq = +-cancelʳ-≤ (≈⇒≤-P (begin
      p + 1#  ≈⟨ solve-≈ Probabilityᴿ ⟩
      1# + p  ≈⟨ eq ⟩
      1#      ≈⟨ solve-≈ Probabilityᴿ ⟩
      0# + 1# ∎))
      where open ≈-Reasoning setoid

  P-∁≈0 : ∀ {P : ProbDistr Ω} {A : Ω → Type} ⦃ A? : A ⁇¹ ⦄
        → P ∙ A ≈ 1# → P ∙ ∁ A ≈ 0#
  P-∁≈0 {P = P} {A} PA≈1 = HPo.≤-antisym P∁A≤0 0≤PX
    where
      module Eq = Setoid setoid
      open ≈-Reasoning setoid

      A∁A-disj : disjoint A (∁ A)
      A∁A-disj Aω ¬Aω = ¬Aω Aω

      PA+P∁A≈1 : P ∙ A + P ∙ ∁ A ≈ 1#
      PA+P∁A≈1 = begin
        P ∙ A + P ∙ ∁ A   ≈⟨ P-distrib-disjoint A∁A-disj ⟩
        P ∙ (A ∪ ∁ A)     ≈⟨ ∙-cong (∪-∁-LEM A) ⟩
        P ∙ U             ≈⟨ PU≈1 ⟩
        1#                 ∎

      1+P∁A≈1 : 1# + P ∙ ∁ A ≈ 1#
      1+P∁A≈1 = Eq.trans (+-congʳ (Eq.sym PA≈1)) PA+P∁A≈1

      P∁A≤0 : P ∙ ∁ A ≤ 0#
      P∁A≤0 = 1+p≈1⇒p≤0 1+P∁A≈1

  P≈0-of-⊆ : ∀ {P : ProbDistr Ω} {X Y : Ω → Type}
           → X ⊆ Y → P ∙ Y ≈ 0# → P ∙ X ≈ 0#
  P≈0-of-⊆ X⊆Y PY≈0 = HPo.≤-antisym
    (HP.≤-trans (prob-monotonous X⊆Y) (≈⇒≤-P PY≈0))
    0≤PX

  mass-restrict : ∀ {P : ProbDistr Ω} {A B : Ω → Type} ⦃ A? : A ⁇¹ ⦄
                → P ∙ A ≈ 1# → P ∙ B ≈ P ∙ (B ∩ A)
  mass-restrict {P = P} {A} {B} PA≈1 = begin
    P ∙ B
      ≈⟨ ∙-cong (∩-∁-partition B A) ⟩
    P ∙ ((B ∩ A) ∪ (B ∩ ∁ A))
      ≈⟨ Eq.sym (P-distrib-disjoint disj) ⟩
    P ∙ (B ∩ A) + P ∙ (B ∩ ∁ A)
      ≈⟨ +-congˡ (P≈0-of-⊆ proj₂ (P-∁≈0 PA≈1)) ⟩
    P ∙ (B ∩ A) + 0#
      ≈⟨ +-identityʳ _ ⟩
    P ∙ (B ∩ A) ∎
    where
      module Eq = Setoid setoid
      open ≈-Reasoning setoid

      disj : disjoint (B ∩ A) (B ∩ ∁ A)
      disj (_ , Aω) (_ , ¬Aω) = ¬Aω Aω

  ----------------------------------------------------------------------
  -- Singleton events and full mass on cartesian product supports.

  -- A singleton in `P ⊗ Q` factors as the product of singletons.
  ⊗-singleton : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} (a : Ω₁) (b : Ω₂)
              → (P ⊗ Q) ∙ ((a , b) ≡_) ≈ P ∙ (a ≡_) * Q ∙ (b ≡_)
  ⊗-singleton a b = Eq.trans (∙-cong (singleton-≐-rect a b)) ⊗-rect
    where module Eq = Setoid setoid

  ⊗-full : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
         → (s₁ : List Ω₁) → P ∙ (_∈ˡ s₁) ≈ 1#
         → (s₂ : List Ω₂) → Q ∙ (_∈ˡ s₂) ≈ 1#
         → (P ⊗ Q) ∙ (_∈ˡ (s₁ ×ᴸ s₂)) ≈ 1#
  ⊗-full {P = P} {Q} s₁ P-full s₂ Q-full = begin
    (P ⊗ Q) ∙ (_∈ˡ (s₁ ×ᴸ s₂))
      ≈⟨ ∙-cong (×ᴸ-≐-rect s₁ s₂) ⟩
    (P ⊗ Q) ∙ ((_∈ˡ s₁) ⊠ (_∈ˡ s₂))
      ≈⟨ ⊗-rect ⟩
    P ∙ (_∈ˡ s₁) * Q ∙ (_∈ˡ s₂)
      ≈⟨ *-cong P-full Q-full ⟩
    1# * 1#
      ≈⟨ *-identityʳ 1# ⟩
    1# ∎
    where open ≈-Reasoning setoid

  ----------------------------------------------------------------------
  -- Lemmas requiring decidable equality on Ω: full-mass for `pure ω`
  -- and `empirical l`.

  module _ {Ω : Type} ⦃ deceq-Ω : DecEq Ω ⦄ where

    open import Data.List.Membership.DecPropositional (DecEq._≟_ deceq-Ω)
      using (_∈?_)

    empirical-full : (l : NE.List⁺ Ω) → empirical l ∙ (_∈ˡ NE.toList l) ≈ 1#
    empirical-full l@(_ NE.∷ _) = begin
      empirical l ∙ (_∈ˡ NE.toList l)
        ≈⟨ ∙-cong ∈ˡ-≐-T-∈? ⟩
      empirical l ∙ (↑ (λ ω → ⌊ ω ∈? NE.toList l ⌋))
        ≈⟨ empirical-eq ⟩
      fromℚ ((+ length (filterᵇ (λ ω → ⌊ ω ∈? NE.toList l ⌋) (NE.toList l))) / NE.length l)
        ≡⟨ cong (λ s → fromℚ ((+ length s) / NE.length l)) (filterᵇ-self (NE.toList l)) ⟩
      fromℚ ((+ NE.length l) / NE.length l)
        ≡⟨ cong fromℚ (n/n≡1ℚ (NE.length l)) ⟩
      fromℚ 1ℚ
        ≈⟨ fromℚ-1 ⟩
      1# ∎
      where open ≈-Reasoning setoid

    pure-full : ∀ (ω : Ω) → pure ω ∙ (_∈ˡ (ω ∷ [])) ≈ 1#
    pure-full ω = empirical-full (ω NE.∷ [])

------------------------------------------------------------------------
-- The full abstract theory: the core operations plus the finite-mixture
-- axioms for `empirical` and `_>>=_`.
--
-- These replace the former `>>=-empirical` axiom, which wrongly
-- identified `empirical l >>= empirical ∘ f` with
-- `empirical (concatMap f l)` — false for varying-width kernels, where
-- concatenation re-normalises uniformly instead of mixing (it forces
-- e.g. 1/2 ≈ 1/3 in the rational model).

record Abstract c ℓ : Type (sucˡ (c ⊔ˡ ℓ)) where
  field core : AbstractCore c ℓ

  open AbstractCore core public

  field
        -- `empirical l` is observationally the uniform mixture of the
        -- Dirac distributions at the points of `l` — on ALL events,
        -- not just decidable ones.
        empirical-mix : ∀ {l : NE.List⁺ Ω} {X : Ω → Type}
          → empirical l ∙ X
          ≈ kmix pure (L.map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) (NE.toList l)) X

        -- Marginalisation: binding a distribution that is
        -- observationally a finite Dirac mixture against a kernel
        -- yields the same-weighted mixture of the kernel's outputs.
        -- This is the defining property of `_>>=_` on finite
        -- distributions.
        >>=-mix : ∀ {ls : List (Probability × Ω₁)} {P : ProbDistr Ω₁}
                    {k : Ω₁ → ProbDistr Ω₂} {Y : Ω₂ → Type}
          → (∀ {X : Ω₁ → Type} → P ∙ X ≈ kmix pure ls X)
          → (P >>= k) ∙ Y ≈ kmix k ls Y

  -- The corrected form of the former `>>=-empirical` axiom: binding an
  -- empirical distribution mixes the kernel outputs uniformly.
  >>=-empirical-mix : ∀ {l : NE.List⁺ Ω₁} {k : Ω₁ → ProbDistr Ω₂} {Y : Ω₂ → Type}
    → (empirical l >>= k) ∙ Y
    ≈ kmix k (L.map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) (NE.toList l)) Y
  >>=-empirical-mix {l = l} =
    >>=-mix {ls = L.map (λ ω → (fromℚ (+ 1 / NE.length l) , ω)) (NE.toList l)} empirical-mix

{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Relation.Binary using (Setoid; IsPreorder)
open import Relation.Unary using (∅; U; _∩_; _∪_; _≐_; ∁)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)

open import ProbabilisticLogic.Abstract

open import Data.List using (cartesianProduct) renaming (map to mapL)
open import Data.List.Membership.Propositional.Properties using
  (∈-cartesianProduct⁺; ∈-cartesianProduct⁻)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP

module ProbabilisticLogic.Expectation c ℓ (a : Abstract c ℓ) where

open Abstract a

open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using () renaming (interchange to +-swap-middle)
open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup
  using () renaming (x∙yz≈y∙xz to *-x∙yz≈y∙xz)

private
  module Eq = Setoid setoid
  module HPo = HasPartialOrder HasPartialOrder-Probability
  module HP  = HasPreorder HPo.hasPreorder

  variable Ω Ω₁ Ω₂ : Type

1[_] : (X : Ω → Type) ⦃ _ : X ⁇¹ ⦄ → Ω → Probability
1[ X ] ω = ifᵈ X ω then 1# else 0#

weight-sum : ProbDistr Ω → (Ω → Probability) → List Ω → Probability
weight-sum P f = foldr (λ ω acc → P ∙ (ω ≡_) * f ω + acc) 0#

------------------------------------------------------------------------
-- The relational notion of expectation:
-- `E[ P , f ]≈ e` says that `f : Ω → Probability` has expected value `e`
-- under `P`.

record E[_,_]≈_ (P : ProbDistr Ω) (f : Ω → Probability) (e : Probability)
  : Type (sucˡ lzero ⊔ˡ c ⊔ˡ ℓ) where
  field support  : List Ω
        distinct : AllPairs _≢_ support
        full     : P ∙ (_∈ˡ support) ≈ 1#
        value    : e ≈ weight-sum P f support

open E[_,_]≈_ public

------------------------------------------------------------------------
-- Lemmas about `weight-sum`.

-- Pointwise-`≈` congruence in the function argument.
weight-sum-cong-f : ∀ {P : ProbDistr Ω} {f g : Ω → Probability}
                  → (∀ ω → f ω ≈ g ω)
                  → ∀ s → weight-sum P f s ≈ weight-sum P g s
weight-sum-cong-f         _   []       = Eq.refl
weight-sum-cong-f {P = P} f≈g (ω ∷ ωs) =
  +-cong (*-congˡ (f≈g ω)) (weight-sum-cong-f f≈g ωs)

-- Linearity in additions: weight-sum is additive in `f`.
weight-sum-+ : ∀ {P : ProbDistr Ω} (f g : Ω → Probability) (s : List Ω)
             → weight-sum P (λ ω → f ω + g ω) s ≈ weight-sum P f s + weight-sum P g s
weight-sum-+         f g []       = Eq.sym (+-identityʳ 0#)
weight-sum-+ {P = P} f g (ω ∷ ωs) = begin
  P ∙ (ω ≡_) * (f ω + g ω) + weight-sum P (λ ω → f ω + g ω) ωs
    ≈⟨ +-cong (distribˡ _ _ _) (weight-sum-+ f g ωs) ⟩
  (P ∙ (ω ≡_) * f ω + P ∙ (ω ≡_) * g ω) +
    (weight-sum P f ωs + weight-sum P g ωs)
    ≈⟨ +-swap-middle _ _ _ _ ⟩
  (P ∙ (ω ≡_) * f ω + weight-sum P f ωs) +
    (P ∙ (ω ≡_) * g ω + weight-sum P g ωs) ∎
  where open ≈-Reasoning setoid

-- Linearity in scalar multiplication: a constant factor pulls out.
weight-sum-*ₗ : ∀ {P : ProbDistr Ω} (k : Probability) (f : Ω → Probability) (s : List Ω)
              → weight-sum P (λ ω → k * f ω) s ≈ k * weight-sum P f s
weight-sum-*ₗ         k f []       = Eq.sym (zeroʳ k)
weight-sum-*ₗ {P = P} k f (ω ∷ ωs) = begin
  P ∙ (ω ≡_) * (k * f ω) + weight-sum P (λ ω → k * f ω) ωs
    ≈⟨ +-cong (*-x∙yz≈y∙xz (P ∙ (ω ≡_)) k (f ω)) (weight-sum-*ₗ k f ωs) ⟩
  k * (P ∙ (ω ≡_) * f ω) + k * weight-sum P f ωs
    ≈⟨ Eq.sym (distribˡ k _ _) ⟩
  k * (P ∙ (ω ≡_) * f ω + weight-sum P f ωs) ∎
  where open ≈-Reasoning setoid

-- The constant-zero function has weighted sum zero.
weight-sum-0 : ∀ {P : ProbDistr Ω} (s : List Ω) → weight-sum P (λ _ → 0#) s ≈ 0#
weight-sum-0         []       = Eq.refl
weight-sum-0 {P = P} (ω ∷ ωs) = begin
  P ∙ (ω ≡_) * 0# + weight-sum P (λ _ → 0#) ωs
    ≈⟨ +-cong (zeroʳ _) (weight-sum-0 ωs) ⟩
  0# + 0# ≈⟨ +-identityʳ 0# ⟩
  0# ∎
  where open ≈-Reasoning setoid

-- Monotonicity in the function argument.
weight-sum-mono-f : ∀ {P : ProbDistr Ω} {f g : Ω → Probability}
                  → (∀ ω → f ω ≤ g ω)
                  → ∀ s → weight-sum P f s ≤ weight-sum P g s
weight-sum-mono-f         _   []       = HP.≤-refl
weight-sum-mono-f {P = P} f≤g (ω ∷ ωs) =
  +-mono-≤ (≤-cong HP.≤-refl (f≤g ω)) (weight-sum-mono-f f≤g ωs)

------------------------------------------------------------------------
-- Lemmas at the relation level.

-- Refit an existing E witness onto a (possibly different) function and
-- value, reusing the original's support.  Most lemmas below are thin
-- wrappers around this — they only differ in the `value` equation.
E-refit : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
        → (E_f : E[ P , f ]≈ e)
        → ∀ {g : Ω → Probability} {e' : Probability}
        → e' ≈ weight-sum P g (E_f .support)
        → E[ P , g ]≈ e'
E-refit E_f val = record
  { support  = E_f .support
  ; distinct = E_f .distinct
  ; full     = E_f .full
  ; value    = val
  }

-- Replacing the value by an `≈`-equal one.
E-resp-≈ : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e e' : Probability}
         → e ≈ e' → E[ P , f ]≈ e → E[ P , f ]≈ e'
E-resp-≈ e≈e' E = E-refit E (Eq.trans (Eq.sym e≈e') (E .value))

-- Replacing `f` by a pointwise-`≈` function.
E-resp-≈-f : ∀ {P : ProbDistr Ω} {f g : Ω → Probability} {e : Probability}
           → (∀ ω → f ω ≈ g ω) → E[ P , f ]≈ e → E[ P , g ]≈ e
E-resp-≈-f f≈g E = E-refit E (Eq.trans (E .value) (weight-sum-cong-f f≈g (E .support)))

-- Reusing the support of an existing witness to obtain an expectation
-- for any other function `g`.
E-rebind : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
         → (E_f : E[ P , f ]≈ e) (g : Ω → Probability)
         → E[ P , g ]≈ weight-sum P g (E_f .support)
E-rebind E_f _ = E-refit E_f Eq.refl

-- The constant-zero function has expected value zero.
E-zero : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
       → E[ P , f ]≈ e → E[ P , (λ _ → 0#) ]≈ 0#
E-zero E_f = E-refit E_f (Eq.sym (weight-sum-0 (E_f .support)))

-- Linearity at the relation level: shares the support of the first witness.
E-+ : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
    → (E_f : E[ P , f ]≈ e) (g : Ω → Probability)
    → E[ P , (λ ω → f ω + g ω) ]≈ (e + weight-sum P g (E_f .support))
E-+ {P = P} {f} {e} E_f g = E-refit E_f (begin
  e + weight-sum P g (E_f .support)
    ≈⟨ +-congʳ (E_f .value) ⟩
  weight-sum P f (E_f .support) + weight-sum P g (E_f .support)
    ≈⟨ Eq.sym (weight-sum-+ f g (E_f .support)) ⟩
  weight-sum P (λ ω → f ω + g ω) (E_f .support) ∎)
  where open ≈-Reasoning setoid

-- Scalar pre-multiplication.
E-*ₗ : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
     → (k : Probability) → E[ P , f ]≈ e → E[ P , (λ ω → k * f ω) ]≈ (k * e)
E-*ₗ {P = P} {f} {e} k E_f = E-refit E_f (begin
  k * e ≈⟨ *-congˡ (E_f .value) ⟩
  k * weight-sum P f (E_f .support)
    ≈⟨ Eq.sym (weight-sum-*ₗ k f (E_f .support)) ⟩
  weight-sum P (λ ω → k * f ω) (E_f .support) ∎)
  where open ≈-Reasoning setoid

-- Building an E witness from a support enumeration.
E-of-support : ∀ {P : ProbDistr Ω} (s : List Ω) → AllPairs _≢_ s
             → P ∙ (_∈ˡ s) ≈ 1# → (f : Ω → Probability)
             → E[ P , f ]≈ weight-sum P f s
E-of-support s d full f = record
  { support = s ; distinct = d ; full = full ; value = Eq.refl }

------------------------------------------------------------------------
-- Cartesian product of lists, the rectangle decomposition of membership,
-- and distinctness preservation — all from std-lib.

-- Infix alias for `cartesianProduct`, matching standard math notation.
infixr 5 _×ᴸ_
_×ᴸ_ : List Ω₁ → List Ω₂ → List (Ω₁ × Ω₂)
_×ᴸ_ = cartesianProduct

-- Cartesian product preserves distinctness (alias for std-lib's
-- `Unique.Propositional.cartesianProduct⁺`).
AllPairs-×ᴸ : ∀ {s₁ : List Ω₁} {s₂ : List Ω₂}
            → AllPairs _≢_ s₁ → AllPairs _≢_ s₂
            → AllPairs _≢_ (s₁ ×ᴸ s₂)
AllPairs-×ᴸ = UniqueP.cartesianProduct⁺

-- Membership in the cartesian product as a rectangle predicate equivalence.
×ᴸ-≐-rect : ∀ (s₁ : List Ω₁) (s₂ : List Ω₂)
          → (_∈ˡ (s₁ ×ᴸ s₂)) ≐ ((_∈ˡ s₁) ⊠ (_∈ˡ s₂))
proj₁ (×ᴸ-≐-rect s₁ s₂) ab∈ = ∈-cartesianProduct⁻ s₁ s₂ ab∈
proj₂ (×ᴸ-≐-rect s₁ s₂) (a∈ , b∈) = ∈-cartesianProduct⁺ a∈ b∈

-- Full mass for the cartesian product of full-mass supports under ⊗.
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

-- Building an E witness for `P ⊗ Q` from supports of P and Q.
E-of-support-⊗ : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
               → (s₁ : List Ω₁) → AllPairs _≢_ s₁ → P ∙ (_∈ˡ s₁) ≈ 1#
               → (s₂ : List Ω₂) → AllPairs _≢_ s₂ → Q ∙ (_∈ˡ s₂) ≈ 1#
               → (f : Ω₁ × Ω₂ → Probability)
               → E[ P ⊗ Q , f ]≈ weight-sum (P ⊗ Q) f (s₁ ×ᴸ s₂)
E-of-support-⊗ s₁ d₁ P-full s₂ d₂ Q-full f =
  E-of-support (s₁ ×ᴸ s₂) (AllPairs-×ᴸ d₁ d₂) (⊗-full s₁ P-full s₂ Q-full) f

------------------------------------------------------------------------
-- Fubini-style decompositions of `weight-sum` over `s₁ ×ᴸ s₂`.

-- `weight-sum` distributes over list concatenation in the support.
weight-sum-++ : ∀ {Ω : Type} {P : ProbDistr Ω} (f : Ω → Probability) (s t : List Ω)
              → weight-sum P f (s ++ t) ≈ weight-sum P f s + weight-sum P f t
weight-sum-++         f []      t = Eq.sym (+-identityˡ _)
weight-sum-++ {P = P} f (ω ∷ s) t = begin
  P ∙ (ω ≡_) * f ω + weight-sum P f (s ++ t)
    ≈⟨ +-congˡ (weight-sum-++ f s t) ⟩
  P ∙ (ω ≡_) * f ω + (weight-sum P f s + weight-sum P f t)
    ≈⟨ Eq.sym (+-assoc _ _ _) ⟩
  P ∙ (ω ≡_) * f ω + weight-sum P f s + weight-sum P f t ∎
  where open ≈-Reasoning setoid

private
  -- The singleton event {= (a, b)} is a rectangle over the components.
  singleton-≐-rect : ∀ {Ω₁ Ω₂ : Type} (a : Ω₁) (b : Ω₂)
                   → ((a , b) ≡_) ≐ ((a ≡_) ⊠ (b ≡_))
  proj₁ (singleton-≐-rect a b) P.refl = P.refl , P.refl
  proj₂ (singleton-≐-rect a b) (P.refl , P.refl) = P.refl

-- A singleton in `P ⊗ Q` factors as the product of singletons.
⊗-singleton : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} (a : Ω₁) (b : Ω₂)
            → (P ⊗ Q) ∙ ((a , b) ≡_) ≈ P ∙ (a ≡_) * Q ∙ (b ≡_)
⊗-singleton {P = P} {Q} a b = Eq.trans (∙-cong (singleton-≐-rect a b)) ⊗-rect

-- `weight-sum` factors out a constant scalar (right multiplication).
weight-sum-*ᵣ : ∀ {Ω : Type} {P : ProbDistr Ω} (f : Ω → Probability) (k : Probability) (s : List Ω)
              → weight-sum P (λ ω → f ω * k) s ≈ weight-sum P f s * k
weight-sum-*ᵣ         f k []       = Eq.sym (Eq.trans (*-comm 0# k) (zeroʳ k))
weight-sum-*ᵣ {P = P} f k (ω ∷ ωs) = begin
  P ∙ (ω ≡_) * (f ω * k) + weight-sum P (λ ω → f ω * k) ωs
    ≈⟨ +-cong (Eq.sym (*-assoc _ _ _)) (weight-sum-*ᵣ f k ωs) ⟩
  P ∙ (ω ≡_) * f ω * k + weight-sum P f ωs * k
    ≈⟨ Eq.sym (distribʳ k _ _) ⟩
  (P ∙ (ω ≡_) * f ω + weight-sum P f ωs) * k ∎
  where open ≈-Reasoning setoid

-- `weight-sum` over `mapL (a ,_) s₂` collapses to a constant times the inner
-- weight-sum (the contribution of the fixed first component a).
weight-sum-mapL : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                  (a : Ω₁) (s₂ : List Ω₂) (f : Ω₁ × Ω₂ → Probability)
                → weight-sum (P ⊗ Q) f (mapL (a ,_) s₂)
                ≈ P ∙ (a ≡_) * weight-sum Q (λ b → f (a , b)) s₂
weight-sum-mapL {P = P} {Q} a [] f = Eq.sym (zeroʳ (P ∙ (a ≡_)))
weight-sum-mapL {P = P} {Q} a (b ∷ bs) f = begin
  (P ⊗ Q) ∙ ((a , b) ≡_) * f (a , b)
    + weight-sum (P ⊗ Q) f (mapL (a ,_) bs)
    ≈⟨ +-cong (*-congʳ (⊗-singleton a b)) (weight-sum-mapL a bs f) ⟩
  P ∙ (a ≡_) * Q ∙ (b ≡_) * f (a , b)
    + P ∙ (a ≡_) * weight-sum Q (λ b' → f (a , b')) bs
    ≈⟨ +-congʳ (*-assoc _ _ _) ⟩
  P ∙ (a ≡_) * (Q ∙ (b ≡_) * f (a , b))
    + P ∙ (a ≡_) * weight-sum Q (λ b' → f (a , b')) bs
    ≈⟨ Eq.sym (distribˡ (P ∙ (a ≡_)) _ _) ⟩
  P ∙ (a ≡_)
    * (Q ∙ (b ≡_) * f (a , b)
       + weight-sum Q (λ b' → f (a , b')) bs) ∎
  where open ≈-Reasoning setoid

-- Fubini-style: weight-sum over `s₁ ×ᴸ s₂` factors as a sum over s₁ of the
-- inner weight-sums weighted by P ∙ (a ≡_).
weight-sum-×ᴸ : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                (s₁ : List Ω₁) (s₂ : List Ω₂) (f : Ω₁ × Ω₂ → Probability)
              → weight-sum (P ⊗ Q) f (s₁ ×ᴸ s₂)
              ≈ weight-sum P (λ a → weight-sum Q (λ b → f (a , b)) s₂) s₁
weight-sum-×ᴸ         []       s₂ f = Eq.refl
weight-sum-×ᴸ {P = P} {Q} (a ∷ as) s₂ f = begin
  weight-sum (P ⊗ Q) f (mapL (a ,_) s₂ ++ (as ×ᴸ s₂))
    ≈⟨ weight-sum-++ f (mapL (a ,_) s₂) (as ×ᴸ s₂) ⟩
  weight-sum (P ⊗ Q) f (mapL (a ,_) s₂) + weight-sum (P ⊗ Q) f (as ×ᴸ s₂)
    ≈⟨ +-cong (weight-sum-mapL a s₂ f) (weight-sum-×ᴸ as s₂ f) ⟩
  P ∙ (a ≡_) * weight-sum Q (λ b → f (a , b)) s₂
    + weight-sum P (λ a' → weight-sum Q (λ b → f (a' , b)) s₂) as ∎
  where open ≈-Reasoning setoid

-- For a distinct support s, summing the singletons P ∙ (ω ≡_) over s
-- gives P ∙ (_∈ˡ s).
weight-sum-1#-distinct : ∀ {Ω : Type} {P : ProbDistr Ω}
                         (s : List Ω) → AllPairs _≢_ s
                       → weight-sum P (λ _ → 1#) s ≈ P ∙ (_∈ˡ s)
weight-sum-1#-distinct {P = P} [] _ = begin
  0#                ≈⟨ Eq.sym P∅≈0 ⟩
  P ∙ ∅              ≈⟨ ∙-cong ((λ ()) , λ ()) ⟩
  P ∙ (_∈ˡ [])      ∎
  where open ≈-Reasoning setoid
weight-sum-1#-distinct {P = P} (ω ∷ ωs) (ω∉ωs ∷ d-rest) = begin
  P ∙ (ω ≡_) * 1# + weight-sum P (λ _ → 1#) ωs
    ≈⟨ +-cong (*-identityʳ _) (weight-sum-1#-distinct ωs d-rest) ⟩
  P ∙ (ω ≡_) + P ∙ (_∈ˡ ωs)
    ≈⟨ P-distrib-disjoint disj ⟩
  P ∙ ((ω ≡_) ∪ (_∈ˡ ωs))
    ≈⟨ ∙-cong cons-equiv ⟩
  P ∙ (_∈ˡ (ω ∷ ωs)) ∎
  where
    open ≈-Reasoning setoid
    disj : disjoint (ω ≡_) (_∈ˡ ωs)
    disj P.refl ω∈ωs = All.lookup ω∉ωs ω∈ωs P.refl
    cons-equiv : ((ω ≡_) ∪ (_∈ˡ ωs)) ≐ (_∈ˡ (ω ∷ ωs))
    proj₁ cons-equiv (inj₁ ω≡ω') = here (P.sym ω≡ω')
    proj₁ cons-equiv (inj₂ ω'∈ωs) = there ω'∈ωs
    proj₂ cons-equiv (here ω'≡ω) = inj₁ (P.sym ω'≡ω)
    proj₂ cons-equiv (there ω'∈ωs) = inj₂ ω'∈ωs

-- Fubini for the second projection: weight-sum (P ⊗ Q) (f ∘ proj₂) over a
-- product support reduces to weight-sum Q f over the second support.
weight-sum-proj₂ : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                   (s₁ : List Ω₁) → AllPairs _≢_ s₁ → P ∙ (_∈ˡ s₁) ≈ 1#
                 → (s₂ : List Ω₂) (f : Ω₂ → Probability)
                 → weight-sum (P ⊗ Q) (f P.∘ proj₂) (s₁ ×ᴸ s₂)
                 ≈ weight-sum Q f s₂
weight-sum-proj₂ {P = P} {Q} s₁ d₁ P-full s₂ f = begin
  weight-sum (P ⊗ Q) (f P.∘ proj₂) (s₁ ×ᴸ s₂)
    ≈⟨ weight-sum-×ᴸ s₁ s₂ (f P.∘ proj₂) ⟩
  weight-sum P (λ a → weight-sum Q f s₂) s₁
    ≈⟨ weight-sum-cong-f (λ _ → Eq.sym (*-identityˡ _)) s₁ ⟩
  weight-sum P (λ _ → 1# * weight-sum Q f s₂) s₁
    ≈⟨ weight-sum-*ᵣ (λ _ → 1#) (weight-sum Q f s₂) s₁ ⟩
  weight-sum P (λ _ → 1#) s₁ * weight-sum Q f s₂
    ≈⟨ *-congʳ (Eq.trans (weight-sum-1#-distinct s₁ d₁) P-full) ⟩
  1# * weight-sum Q f s₂
    ≈⟨ *-identityˡ _ ⟩
  weight-sum Q f s₂ ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Helpers about probability events.

private
  ≈⇒≤-P : ∀ {x y : Probability} → x ≈ y → x ≤ y
  ≈⇒≤-P = IsPreorder.reflexive HP.≤-isPreorder

  -- Cancellation: 1# + p ≈ 1# implies p ≤ 0#.
  1+p≈1⇒p≤0 : ∀ {p : Probability} → 1# + p ≈ 1# → p ≤ 0#
  1+p≈1⇒p≤0 {p} eq = +-cancelʳ-≤ (≈⇒≤-P p+1≈0+1)
    where
      open ≈-Reasoning setoid
      p+1≈0+1 : p + 1# ≈ 0# + 1#
      p+1≈0+1 = begin
        p + 1#  ≈⟨ +-comm p 1# ⟩
        1# + p  ≈⟨ eq ⟩
        1#      ≈⟨ Eq.sym (+-identityˡ 1#) ⟩
        0# + 1# ∎

-- Complement of a full-mass event has zero mass.  Requires decidability
-- of the event (so we have law-of-excluded-middle on it).
P-∁≈0 : ∀ {P : ProbDistr Ω} {A : Ω → Type} ⦃ A? : A ⁇¹ ⦄
      → P ∙ A ≈ 1# → P ∙ ∁ A ≈ 0#
P-∁≈0 {P = P} {A} PA≈1 = HPo.≤-antisym P∁A≤0 0≤PX
  where
    open ≈-Reasoning setoid

    A∁A-disj : disjoint A (∁ A)
    A∁A-disj Aω ¬Aω = ¬Aω Aω

    A∪∁A≐U : (A ∪ ∁ A) ≐ U
    proj₁ A∪∁A≐U _ = tt
    proj₂ A∪∁A≐U {ω} _ with ¿ A ω ¿
    ... | yes Aω = inj₁ Aω
    ... | no ¬Aω = inj₂ ¬Aω

    PA+P∁A≈1 : P ∙ A + P ∙ ∁ A ≈ 1#
    PA+P∁A≈1 = begin
      P ∙ A + P ∙ ∁ A   ≈⟨ P-distrib-disjoint A∁A-disj ⟩
      P ∙ (A ∪ ∁ A)     ≈⟨ ∙-cong A∪∁A≐U ⟩
      P ∙ U             ≈⟨ PU≈1 ⟩
      1#                 ∎

    1+P∁A≈1 : 1# + P ∙ ∁ A ≈ 1#
    1+P∁A≈1 = Eq.trans (+-congʳ (Eq.sym PA≈1)) PA+P∁A≈1

    P∁A≤0 : P ∙ ∁ A ≤ 0#
    P∁A≤0 = 1+p≈1⇒p≤0 1+P∁A≈1

-- Mass restriction: P(B) coincides with P(B ∩ A) when A is full-mass.
mass-restrict : ∀ {P : ProbDistr Ω} {A B : Ω → Type} ⦃ A? : A ⁇¹ ⦄
              → P ∙ A ≈ 1# → P ∙ B ≈ P ∙ (B ∩ A)
mass-restrict {P = P} {A} {B} PA≈1 = begin
  P ∙ B
    ≈⟨ ∙-cong B≐BA∪B∁A ⟩
  P ∙ ((B ∩ A) ∪ (B ∩ ∁ A))
    ≈⟨ Eq.sym (P-distrib-disjoint disj) ⟩
  P ∙ (B ∩ A) + P ∙ (B ∩ ∁ A)
    ≈⟨ +-congˡ P-B∩∁A≈0 ⟩
  P ∙ (B ∩ A) + 0#
    ≈⟨ +-identityʳ _ ⟩
  P ∙ (B ∩ A) ∎
  where
    open ≈-Reasoning setoid

    B≐BA∪B∁A : B ≐ (B ∩ A) ∪ (B ∩ ∁ A)
    proj₁ B≐BA∪B∁A {ω} Bω with ¿ A ω ¿
    ... | yes Aω = inj₁ (Bω , Aω)
    ... | no ¬Aω = inj₂ (Bω , ¬Aω)
    proj₂ B≐BA∪B∁A (inj₁ (Bω , _)) = Bω
    proj₂ B≐BA∪B∁A (inj₂ (Bω , _)) = Bω

    disj : disjoint (B ∩ A) (B ∩ ∁ A)
    disj (_ , Aω) (_ , ¬Aω) = ¬Aω Aω

    P-B∩∁A≈0 : P ∙ (B ∩ ∁ A) ≈ 0#
    P-B∩∁A≈0 = HPo.≤-antisym
                  (HP.≤-trans (prob-monotonous proj₂) (≈⇒≤-P (P-∁≈0 PA≈1)))
                  0≤PX

------------------------------------------------------------------------
-- The indicator function summed over a distinct support equals the
-- probability of the event restricted to that support.
weight-sum-1[X] : ∀ {P : ProbDistr Ω} (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄
                → ∀ s → AllPairs _≢_ s
                → weight-sum P 1[ X ] s ≈ P ∙ (X ∩ (_∈ˡ s))
weight-sum-1[X] {P = P} X [] [] = begin
  0#                              ≈⟨ Eq.sym P∅≈0 ⟩
  P ∙ ∅                            ≈⟨ ∙-cong ((λ ()) , λ where (_ , ())) ⟩
  P ∙ (X ∩ (_∈ˡ []))               ∎
  where open ≈-Reasoning setoid
weight-sum-1[X] {P = P} X (ω ∷ ωs) (ω∉ωs ∷ rest-distinct) = begin
  P ∙ (ω ≡_) * 1[ X ] ω + weight-sum P 1[ X ] ωs
    ≈⟨ +-cong head-eq (weight-sum-1[X] X ωs rest-distinct) ⟩
  P ∙ (λ ω' → X ω' × ω ≡ ω') + P ∙ (X ∩ (_∈ˡ ωs))
    ≈⟨ P-distrib-disjoint head-tail-disj ⟩
  P ∙ ((λ ω' → X ω' × ω ≡ ω') ∪ (X ∩ (_∈ˡ ωs)))
    ≈⟨ ∙-cong cons-equiv ⟩
  P ∙ (X ∩ (_∈ˡ (ω ∷ ωs))) ∎
  where
    open ≈-Reasoning setoid

    head-eq : P ∙ (ω ≡_) * 1[ X ] ω ≈ P ∙ (λ ω' → X ω' × ω ≡ ω')
    head-eq with ¿ X ω ¿
    ... | yes Xω = begin
        P ∙ (ω ≡_) * 1#
          ≈⟨ *-identityʳ _ ⟩
        P ∙ (ω ≡_)
          ≈⟨ ∙-cong ((λ ω≡ω' → subst X ω≡ω' Xω , ω≡ω') , proj₂) ⟩
        P ∙ (λ ω' → X ω' × ω ≡ ω') ∎
    ... | no ¬Xω = begin
        P ∙ (ω ≡_) * 0#
          ≈⟨ zeroʳ _ ⟩
        0#
          ≈⟨ Eq.sym P∅≈0 ⟩
        P ∙ ∅
          ≈⟨ ∙-cong ((λ ()) , λ where
                       (Xω' , ω≡ω') → ⊥-elim (¬Xω (subst X (P.sym ω≡ω') Xω'))) ⟩
        P ∙ (λ ω' → X ω' × ω ≡ ω') ∎

    head-tail-disj : disjoint (λ ω' → X ω' × ω ≡ ω') (X ∩ (_∈ˡ ωs))
    head-tail-disj {ω'} (_ , ω≡ω') (_ , ω'∈ωs) =
      All.lookup ω∉ωs (subst (_∈ˡ ωs) (P.sym ω≡ω') ω'∈ωs) P.refl

    cons-equiv : ((λ ω' → X ω' × ω ≡ ω') ∪ (X ∩ (_∈ˡ ωs)))
               ≐ (X ∩ (_∈ˡ (ω ∷ ωs)))
    proj₁ cons-equiv (inj₁ (Xω' , ω≡ω')) = Xω' , here (P.sym ω≡ω')
    proj₁ cons-equiv (inj₂ (Xω' , ω'∈ωs)) = Xω' , there ω'∈ωs
    proj₂ cons-equiv (Xω' , here ω'≡ω) = inj₁ (Xω' , P.sym ω'≡ω)
    proj₂ cons-equiv (Xω' , there ω'∈ωs) = inj₂ (Xω' , ω'∈ωs)

------------------------------------------------------------------------
-- Lemmas requiring decidable equality on Ω.

module _ {Ω : Type} ⦃ deceq-Ω : DecEq Ω ⦄ where

  open import Data.List.Membership.DecPropositional (DecEq._≟_ deceq-Ω) using (_∈?_)

  -- List membership is decidable when Ω has decidable equality.
  instance
    ∈ˡ-? : ∀ {s : List Ω} → (_∈ˡ s) ⁇¹
    ∈ˡ-? {s} = ⁇¹ (_∈? s)

  -- Indicator rule: the expected value of an indicator equals the event's
  -- probability.  Reuses the support of any provided E witness.
  -- TODO: this really shouldn't have the `E_f` argument
  E-indicator : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
              → (E_f : E[ P , f ]≈ e)
              → (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄
              → E[ P , 1[ X ] ]≈ (P ∙ X)
  E-indicator {P = P} {f} {e} E_f X = E-refit E_f (begin
    P ∙ X
      ≈⟨ mass-restrict ⦃ ∈ˡ-? ⦄ (E_f .full) ⟩
    P ∙ (X ∩ (_∈ˡ E_f .support))
      ≈⟨ Eq.sym (weight-sum-1[X] X (E_f .support) (E_f .distinct)) ⟩
    weight-sum P 1[ X ] (E_f .support) ∎)
    where open ≈-Reasoning setoid

  ------------------------------------------------------------------------
  -- Expected value of `pure ω`.

  private
    import Data.List.NonEmpty as NE
    open import Data.List.Properties using (filter-all)
    open import Data.Rational using (_/_; 1ℚ)
    open import Data.Integer using (+_)
    open import Relation.Nullary.Decidable using (T?)
    open import LibExt using (module Arith)
    open Arith using (n/n≡1ℚ)

    -- `_∈ˡ s` and the lifted Bool predicate `↑ (λ ω' → ⌊ ω' ∈? s ⌋)` are
    -- pointwise logically equivalent.
    ∈ˡ≐↑∈?  : ∀ {s : List Ω} → (_∈ˡ s) ≐ (↑ (λ ω' → ⌊ ω' ∈? s ⌋))
    proj₁ ∈ˡ≐↑∈? ω∈s = fromWitness ω∈s
    proj₂ ∈ˡ≐↑∈? {ω} ↑ω = toWitness {a? = ω ∈? _} ↑ω

    -- `filterᵇ (λ ω' → ⌊ ω' ∈? s ⌋) s ≡ s`: filtering by self-membership
    -- keeps every element.
    filterᵇ-self : (s : List Ω) → filterᵇ (λ ω' → ⌊ ω' ∈? s ⌋) s ≡ s
    filterᵇ-self s = filter-all (T? P.∘ (λ ω' → ⌊ ω' ∈? s ⌋))
                                (All.tabulate fromWitness)

  -- For pure ω, "ω' ∈ [ω]" has full probability mass.
  pure-full : ∀ (ω : Ω) → pure ω ∙ (_∈ˡ (ω ∷ [])) ≈ 1#
  pure-full ω = begin
    pure ω ∙ (_∈ˡ (ω ∷ []))
      ≈⟨ ∙-cong ∈ˡ≐↑∈? ⟩
    pure ω ∙ (↑ (λ ω' → ⌊ ω' ∈? (ω ∷ []) ⌋))
      ≈⟨ empirical-eq ⟩
    fromℚ ((+ length (filterᵇ (λ ω' → ⌊ ω' ∈? (ω ∷ []) ⌋) (ω ∷ []))) / 1)
      ≡⟨ cong (λ s → fromℚ ((+ length s) / 1)) (filterᵇ-self (ω ∷ [])) ⟩
    fromℚ ((+ 1) / 1)
      ≈⟨ fromℚ-1 ⟩
    1# ∎
    where open ≈-Reasoning setoid

  -- The expected value of `f` under `pure ω` is `f ω`.
  E-pure : (ω : Ω) (f : Ω → Probability) → E[ pure ω , f ]≈ f ω
  E-pure ω f = record
    { support  = ω ∷ []
    ; distinct = All.[] ∷ []
    ; full     = pure-full ω
    ; value    = begin
        f ω
          ≈⟨ Eq.sym (+-identityʳ _) ⟩
        f ω + 0#
          ≈⟨ +-congʳ (Eq.sym (*-identityˡ _)) ⟩
        1# * f ω + 0#
          ≈⟨ +-congʳ (*-congʳ (Eq.sym pω-self)) ⟩
        pure ω ∙ (ω ≡_) * f ω + 0# ∎
    }
    where
      open ≈-Reasoning setoid

      -- (ω ≡_) and (_∈ˡ [ω]) define the same event up to symmetry of ≡.
      ω≡-↔-∈[ω] : (ω ≡_) ≐ (_∈ˡ (ω ∷ []))
      proj₁ ω≡-↔-∈[ω] ω≡ω' = here (P.sym ω≡ω')
      proj₂ ω≡-↔-∈[ω] (here ω'≡ω) = P.sym ω'≡ω

      pω-self : pure ω ∙ (ω ≡_) ≈ 1#
      pω-self = Eq.trans (∙-cong ω≡-↔-∈[ω]) (pure-full ω)

  ------------------------------------------------------------------------
  -- Expected value of `empirical l` for a list with distinct elements.

  -- For a non-empty list `l` whose elements are pairwise distinct, the
  -- mass of `_∈ˡ NE.toList l` is 1.
  empirical-full : (l : NE.List⁺ Ω) → empirical l ∙ (_∈ˡ NE.toList l) ≈ 1#
  empirical-full l@(_ NE.∷ tail) = begin
    empirical l ∙ (_∈ˡ NE.toList l)
      ≈⟨ ∙-cong ∈ˡ≐↑∈? ⟩
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

  -- The expected value of `f` under `empirical l` for a distinct-element
  -- list `l` is the weight-sum over `NE.toList l`.  This is the canonical
  -- "structural" empirical witness — converting it into a closed-form
  -- arithmetic expression `(Σ f) * fromℚ (1 / n)` requires further work.
  E-empirical-distinct : (l : NE.List⁺ Ω) → AllPairs _≢_ (NE.toList l)
                       → (f : Ω → Probability)
                       → E[ empirical l , f ]≈ weight-sum (empirical l) f (NE.toList l)
  E-empirical-distinct l l-distinct f =
    E-of-support (NE.toList l) l-distinct (empirical-full l) f

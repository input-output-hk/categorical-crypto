{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P
  hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans; zeroˡ)

open import Class.Decidable
open import Relation.Binary using (Setoid)
open import Relation.Unary using (∅; U; _∩_; _∪_; _≐_; ∁)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (∈-resp-↭)

open import ProbabilisticLogic.Abstract

open import Data.List using (filter) renaming (map to mapL)
open import Data.List.Membership.Propositional.Properties using
  (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-filter⁺; ∈-filter⁻)
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsP
open import Relation.Nullary.Decidable using (¬?)

open import LibExt using (module Lists; module Predicates)
open Lists using (_×ᴸ_; Unique-×ᴸ; partition-↭; ∈-cons-≐; ∈ˡ-?)
open import Relation.Unary.Properties using (≐-sym)

module ProbabilisticLogic.Expectation c ℓ (a : Abstract c ℓ) where

open Abstract a

open import Tactic.Solver.Ring using (solve-≈)

private
  module Eq = Setoid setoid

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
  field support     : List Ω
        distinct    : Unique support
        off-support : ∀ {ω} → ω ∉ˡ support → P ∙ (ω ≡_) * f ω ≈ 0#
        value       : e ≈ weight-sum P f support

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
weight-sum-+ {P = P} f g (ω ∷ ωs) = Eq.trans
  (+-congˡ (weight-sum-+ f g ωs))
  (solve-≈ Probabilityᴿ)

-- Linearity in scalar multiplication: a constant factor pulls out.
weight-sum-*ₗ : ∀ {P : ProbDistr Ω} (k : Probability) (f : Ω → Probability) (s : List Ω)
              → weight-sum P (λ ω → k * f ω) s ≈ k * weight-sum P f s
weight-sum-*ₗ         k f []       = Eq.sym (zeroʳ k)
weight-sum-*ₗ {P = P} k f (ω ∷ ωs) = Eq.trans
  (+-congˡ (weight-sum-*ₗ k f ωs))
  (solve-≈ Probabilityᴿ)

-- The constant-zero function has weighted sum zero.
weight-sum-0 : ∀ {P : ProbDistr Ω} (s : List Ω) → weight-sum P (λ _ → 0#) s ≈ 0#
weight-sum-0         []       = Eq.refl
weight-sum-0 {P = P} (ω ∷ ωs) = begin
  P ∙ (ω ≡_) * 0# + weight-sum P (λ _ → 0#) ωs
    ≈⟨ +-cong (zeroʳ _) (weight-sum-0 ωs) ⟩
  0# + 0# ≈⟨ +-identityʳ 0# ⟩
  0# ∎
  where open ≈-Reasoning setoid

-- `weight-sum` distributes over list concatenation in the support.
weight-sum-++ : ∀ {P : ProbDistr Ω} (f : Ω → Probability) (s t : List Ω)
              → weight-sum P f (s ++ t) ≈ weight-sum P f s + weight-sum P f t
weight-sum-++         f []      t = Eq.sym (+-identityˡ _)
weight-sum-++ {P = P} f (ω ∷ s) t = Eq.trans
  (+-congˡ (weight-sum-++ f s t))
  (solve-≈ Probabilityᴿ)

-- A `cons in the middle` rearrangement: an element `a` placed between
-- two list segments contributes the same `P ∙ (a ≡_) * f a` whether we
-- evaluate the sum in-order or pull `a` to the front.
weight-sum-cons-middle : ∀ {P : ProbDistr Ω} {a : Ω}
                         (xs : List Ω) {ys : List Ω}
                         (f : Ω → Probability)
                       → weight-sum P f (xs ++ a ∷ ys)
                       ≈ P ∙ (a ≡_) * f a + weight-sum P f (xs ++ ys)
weight-sum-cons-middle {P = P} {a} xs {ys} f = Eq.trans
  (weight-sum-++ f xs (a ∷ ys))
  (Eq.trans
    (solve-≈ Probabilityᴿ)
    (+-congˡ (Eq.sym (weight-sum-++ f xs ys))))

-- `weight-sum` is invariant under permutation of the support.  Each
-- constructor case is a single ring rearrangement on the head, so the
-- ring solver closes the algebra immediately.
weight-sum-↭ : ∀ {P : ProbDistr Ω} (f : Ω → Probability) {s t : List Ω}
             → s ↭ t → weight-sum P f s ≈ weight-sum P f t
weight-sum-↭         f Perm.refl                    = Eq.refl
weight-sum-↭         f (Perm.prep _ p)              = +-congˡ (weight-sum-↭ f p)
weight-sum-↭ {P = P} f (Perm.swap ω₁ ω₂ p) = Eq.trans
  (+-congˡ (+-congˡ (weight-sum-↭ f p)))
  (solve-≈ Probabilityᴿ)
weight-sum-↭         f (Perm.trans p q)             =
  Eq.trans (weight-sum-↭ f p) (weight-sum-↭ f q)

-- A `weight-sum` over a support whose every weighted contribution
-- vanishes is itself zero.
weight-sum-vanish : ∀ {P : ProbDistr Ω} {f : Ω → Probability} (s : List Ω)
                  → (∀ {ω} → ω ∈ˡ s → P ∙ (ω ≡_) * f ω ≈ 0#)
                  → weight-sum P f s ≈ 0#
weight-sum-vanish         []       _      = Eq.refl
weight-sum-vanish {P = P} {f} (ω ∷ ωs) vanish = Eq.trans
  (+-cong (vanish (here P.refl)) (weight-sum-vanish ωs (vanish ∘ there)))
  (+-identityʳ 0#)

-- "Support enlargement by vanishing elements": if `t` covers `s`, both
-- distinct, and the elements of `t \ s` have vanishing weighted
-- contribution, then ws over `t` equals ws over `s`.  Realised by
-- permuting `t` to `s ++ extras` (via `partition-↭`) and dropping the
-- extras with `weight-sum-vanish`.
weight-sum-extend-vanish : ∀ {P : ProbDistr Ω} (t s : List Ω)
                         → Unique t → Unique s
                         → (∀ {ω} → ω ∈ˡ s → ω ∈ˡ t)
                         → (f : Ω → Probability)
                         → (∀ {ω} → ω ∈ˡ t → ω ∉ˡ s → P ∙ (ω ≡_) * f ω ≈ 0#)
                         → weight-sum P f t ≈ weight-sum P f s
weight-sum-extend-vanish {P = P} t s t-d s-d s⊆t f vanish
  with extras , t↭ , _ , extras∉s ← partition-↭ t s t-d s-d s⊆t = begin
    weight-sum P f t                              ≈⟨ weight-sum-↭ f t↭ ⟩
    weight-sum P f (s ++ extras)                  ≈⟨ weight-sum-++ f s extras ⟩
    weight-sum P f s + weight-sum P f extras      ≈⟨ +-congˡ extras-sum-0 ⟩
    weight-sum P f s + 0#                         ≈⟨ +-identityʳ _ ⟩
    weight-sum P f s ∎
  where
    open ≈-Reasoning setoid
    extras-sum-0 : weight-sum P f extras ≈ 0#
    extras-sum-0 = weight-sum-vanish extras
      (λ ω∈ex → vanish (∈-resp-↭ (Perm.↭-sym t↭) (∈-++⁺ʳ s ω∈ex))
                       (extras∉s ω∈ex))

------------------------------------------------------------------------
-- Lemmas at the relation level.

-- Replacing the value by an `≈`-equal one.
E-resp-≈ : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e e' : Probability}
         → e ≈ e' → E[ P , f ]≈ e → E[ P , f ]≈ e'
E-resp-≈ e≈e' E = record
  { support     = E .support
  ; distinct    = E .distinct
  ; off-support = E .off-support
  ; value       = Eq.trans (Eq.sym e≈e') (E .value)
  }

-- Replacing `f` by a pointwise-`≈` function.
E-resp-≈-f : ∀ {P : ProbDistr Ω} {f g : Ω → Probability} {e : Probability}
           → (∀ ω → f ω ≈ g ω) → E[ P , f ]≈ e → E[ P , g ]≈ e
E-resp-≈-f {P = P} {f} {g} f≈g E = record
  { support     = E .support
  ; distinct    = E .distinct
  ; off-support = λ {ω} ω∉ → Eq.trans (*-congˡ (Eq.sym (f≈g ω))) (E .off-support ω∉)
  ; value       = Eq.trans (E .value) (weight-sum-cong-f f≈g (E .support))
  }

-- The constant-zero function has expected value zero, on the empty support.
E-zero : ∀ {P : ProbDistr Ω} → E[ P , (λ _ → 0#) ]≈ 0#
E-zero = record
  { support     = []
  ; distinct    = []
  ; off-support = λ _ → zeroʳ _
  ; value       = Eq.refl
  }

-- Scalar pre-multiplication.
E-*ₗ : ∀ {P : ProbDistr Ω} {f : Ω → Probability} {e : Probability}
     → (k : Probability) → E[ P , f ]≈ e → E[ P , (λ ω → k * f ω) ]≈ (k * e)
E-*ₗ {P = P} {f} {e} k E_f = record
  { support     = E_f .support
  ; distinct    = E_f .distinct
  ; off-support = λ {ω} ω∉ → Eq.trans
        (solve-≈ Probabilityᴿ)
        (Eq.trans (*-congˡ (E_f .off-support ω∉)) (zeroʳ k))
  ; value = Eq.trans (*-congˡ (E_f .value))
                     (Eq.sym (weight-sum-*ₗ k f (E_f .support)))
  }

-- Building an E witness directly from a support and an `off-support`
-- proof for the function `f`.
E-of-support : ∀ {P : ProbDistr Ω} (s : List Ω) → Unique s
             → (f : Ω → Probability)
             → (∀ {ω} → ω ∉ˡ s → P ∙ (ω ≡_) * f ω ≈ 0#)
             → E[ P , f ]≈ weight-sum P f s
E-of-support s d f off = record
  { support = s ; distinct = d ; off-support = off ; value = Eq.refl }

------------------------------------------------------------------------
-- Fubini-style decompositions of `weight-sum` over `s₁ ×ᴸ s₂`.

-- `weight-sum` factors out a constant scalar (right multiplication).
weight-sum-*ᵣ : ∀ {P : ProbDistr Ω} (f : Ω → Probability) (k : Probability) (s : List Ω)
              → weight-sum P (λ ω → f ω * k) s ≈ weight-sum P f s * k
weight-sum-*ᵣ         f k []       = Eq.sym (zeroˡ k)
weight-sum-*ᵣ {P = P} f k (ω ∷ ωs) = Eq.trans
  (+-congˡ (weight-sum-*ᵣ f k ωs))
  (solve-≈ Probabilityᴿ)

-- `weight-sum` over `mapL (a ,_) s₂` collapses to a constant times the inner
-- weight-sum (the contribution of the fixed first component a).
weight-sum-mapL : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                  (a : Ω₁) (s₂ : List Ω₂) (f : Ω₁ × Ω₂ → Probability)
                → weight-sum (P ⊗ Q) f (mapL (a ,_) s₂)
                ≈ P ∙ (a ≡_) * weight-sum Q (λ b → f (a , b)) s₂
weight-sum-mapL {P = P} {Q} a [] f = Eq.sym (zeroʳ (P ∙ (a ≡_)))
weight-sum-mapL {P = P} {Q} a (b ∷ bs) f = Eq.trans
  (+-cong (*-congʳ (⊗-singleton a b)) (weight-sum-mapL a bs f))
  (solve-≈ Probabilityᴿ)

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
weight-sum-1#-distinct : ∀ {P : ProbDistr Ω}
                         (s : List Ω) → Unique s
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
    ≈⟨ ∙-cong (≐-sym (∈-cons-≐ ω ωs)) ⟩
  P ∙ (_∈ˡ (ω ∷ ωs)) ∎
  where
    open ≈-Reasoning setoid
    disj : disjoint (ω ≡_) (_∈ˡ ωs)
    disj P.refl ω∈ωs = All.lookup ω∉ωs ω∈ωs P.refl

-- Fubini for the second projection: weight-sum (P ⊗ Q) (f ∘ proj₂) over a
-- product support reduces to weight-sum Q f over the second support.
weight-sum-proj₂ : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂}
                   (s₁ : List Ω₁) → Unique s₁ → P ∙ (_∈ˡ s₁) ≈ 1#
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
-- The indicator function summed over a distinct support equals the
-- probability of the event restricted to that support.
weight-sum-1[X] : ∀ {P : ProbDistr Ω} (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄
                → ∀ s → Unique s
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

  -- For a support that carries full P-mass, every singleton off the
  -- support has zero P-mass, hence zero weighted contribution.  This is
  -- the bridge from "support has full P-mass" to "off-support contributes
  -- zero" — the field condition of the `E[ … ]≈ _` record.
  off-support-of-full-mass :
    ∀ {P : ProbDistr Ω} {s : List Ω}
    → P ∙ (_∈ˡ s) ≈ 1#
    → (f : Ω → Probability) → ∀ {ω} → ω ∉ˡ s → P ∙ (ω ≡_) * f ω ≈ 0#
  off-support-of-full-mass full f ω∉ =
    Eq.trans (*-congʳ (P≈0-of-⊆ (λ where P.refl → ω∉) (P-∁≈0 ⦃ ∈ˡ-? ⦄ full)))
             (zeroˡ _)

  -- Indicator rule: the expected value of an indicator over a full-mass
  -- support equals the event's probability.
  E-indicator : ∀ {P : ProbDistr Ω}
              → (s : List Ω) → Unique s → P ∙ (_∈ˡ s) ≈ 1#
              → (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄
              → E[ P , 1[ X ] ]≈ (P ∙ X)
  E-indicator {P = P} s d full X =
    E-resp-≈ ws-1[X]≈P∙X (E-of-support s d 1[ X ] (off-support-of-full-mass full 1[ X ]))
    where
      open ≈-Reasoning setoid
      ws-1[X]≈P∙X : weight-sum P 1[ X ] s ≈ P ∙ X
      ws-1[X]≈P∙X = begin
        weight-sum P 1[ X ] s              ≈⟨ weight-sum-1[X] X s d ⟩
        P ∙ (X ∩ (_∈ˡ s))                  ≈⟨ Eq.sym (mass-restrict ⦃ ∈ˡ-? ⦄ full) ⟩
        P ∙ X ∎

  ------------------------------------------------------------------------
  -- Two-witness linearity: if `f` and `g` each have an expected value, so
  -- does their pointwise sum.  Decidable equality on `Ω` is what lets us
  -- build a distinct combined support.
  E-+ : ∀ {P : ProbDistr Ω} {f g : Ω → Probability} {ef eg : Probability}
      → E[ P , f ]≈ ef → E[ P , g ]≈ eg
      → E[ P , (λ ω → f ω + g ω) ]≈ (ef + eg)
  E-+ {P = P} {f} {g} {ef} {eg} Ef Eg = record
    { support     = sf ++ extras
    ; distinct    = s-d
    ; off-support = off-fg
    ; value       = value-eq
    }
    where
      open ≈-Reasoning setoid

      sf = Ef .support
      sg = Eg .support

      ¬∈sf? : (y : Ω) → Dec (y ∉ˡ sf)
      ¬∈sf? y = ¬? (y ∈? sf)

      extras : List Ω
      extras = filter ¬∈sf? sg

      extras-d : Unique extras
      extras-d = AllPairsP.filter⁺ ¬∈sf? (Eg .distinct)

      extras-∉sf : ∀ {x} → x ∈ˡ extras → x ∉ˡ sf
      extras-∉sf x∈ = proj₂ (∈-filter⁻ ¬∈sf? {xs = sg} x∈)

      ∉sf→sg→extras : ∀ {x} → x ∉ˡ sf → x ∈ˡ sg → x ∈ˡ extras
      ∉sf→sg→extras x∉sf x∈sg = ∈-filter⁺ ¬∈sf? {xs = sg} x∈sg x∉sf

      s-d : Unique (sf ++ extras)
      s-d = AllPairsP.++⁺ (Ef .distinct) extras-d cross
        where
          cross : All (λ x → All (x ≢_) extras) sf
          cross = All.tabulate (λ {x} x∈sf →
                    All.tabulate (λ {y} y∈extras x≡y →
                      extras-∉sf y∈extras (subst (_∈ˡ sf) x≡y x∈sf)))

      off-fg : ∀ {ω} → ω ∉ˡ (sf ++ extras) → P ∙ (ω ≡_) * (f ω + g ω) ≈ 0#
      off-fg {ω} ω∉ = begin
        P ∙ (ω ≡_) * (f ω + g ω)
          ≈⟨ distribˡ _ _ _ ⟩
        P ∙ (ω ≡_) * f ω + P ∙ (ω ≡_) * g ω
          ≈⟨ +-cong (Ef .off-support ω∉sf) (Eg .off-support ω∉sg) ⟩
        0# + 0#
          ≈⟨ +-identityʳ _ ⟩
        0# ∎
        where
          ω∉sf : ω ∉ˡ sf
          ω∉sf ω∈sf = ω∉ (∈-++⁺ˡ ω∈sf)
          ω∉sg : ω ∉ˡ sg
          ω∉sg ω∈sg with ω ∈? sf
          ... | yes ω∈sf  = ω∉sf ω∈sf
          ... | no  ω∉sf' = ω∉ (∈-++⁺ʳ sf (∉sf→sg→extras ω∉sf' ω∈sg))

      sg⊆combined : ∀ {ω} → ω ∈ˡ sg → ω ∈ˡ (sf ++ extras)
      sg⊆combined {ω} ω∈sg with ω ∈? sf
      ... | yes ω∈sf  = ∈-++⁺ˡ ω∈sf
      ... | no  ω∉sf' = ∈-++⁺ʳ sf (∉sf→sg→extras ω∉sf' ω∈sg)

      ws-f-eq : weight-sum P f sf ≈ weight-sum P f (sf ++ extras)
      ws-f-eq = Eq.sym (weight-sum-extend-vanish (sf ++ extras) sf s-d
                        (Ef .distinct) ∈-++⁺ˡ f (λ _ → Ef .off-support))

      ws-g-eq : weight-sum P g sg ≈ weight-sum P g (sf ++ extras)
      ws-g-eq = Eq.sym (weight-sum-extend-vanish (sf ++ extras) sg s-d
                        (Eg .distinct) sg⊆combined g (λ _ → Eg .off-support))

      value-eq : ef + eg ≈ weight-sum P (λ ω → f ω + g ω) (sf ++ extras)
      value-eq = begin
        ef + eg
          ≈⟨ +-cong (Ef .value) (Eg .value) ⟩
        weight-sum P f sf + weight-sum P g sg
          ≈⟨ +-cong ws-f-eq ws-g-eq ⟩
        weight-sum P f (sf ++ extras) + weight-sum P g (sf ++ extras)
          ≈⟨ Eq.sym (weight-sum-+ f g (sf ++ extras)) ⟩
        weight-sum P (λ ω → f ω + g ω) (sf ++ extras) ∎

  ------------------------------------------------------------------------
  -- Expected value of `pure ω`: just the value at ω.

  E-pure : (ω : Ω) (f : Ω → Probability) → E[ pure ω , f ]≈ f ω
  E-pure ω f = record
    { support     = ω ∷ []
    ; distinct    = All.[] ∷ []
    ; off-support = off-support-of-full-mass (pure-full ω) f
    ; value       = begin
        f ω
          ≈⟨ solve-≈ Probabilityᴿ ⟩
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
  -- The canonical "structural" empirical witness — converting into a
  -- closed-form arithmetic expression `(Σ f) * fromℚ (1 / n)` is further
  -- work.

  E-empirical-distinct : (l : NE.List⁺ Ω) → Unique (NE.toList l)
                       → (f : Ω → Probability)
                       → E[ empirical l , f ]≈ weight-sum (empirical l) f (NE.toList l)
  E-empirical-distinct l l-distinct f =
    E-of-support (NE.toList l) l-distinct f
                 (off-support-of-full-mass (empirical-full l) f)

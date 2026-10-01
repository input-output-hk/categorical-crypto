{-# OPTIONS --safe --without-K --guardedness #-}

-- What the potential in `QBᵢ` means on a run: on every activation word the
-- certificate produces a run whose output word carries at most `c` downward
-- outputs per activation from above, and which erases to the machine's own
-- behaviour.  The bound travels INSIDE `Dₚ` — a distribution admits no
-- inspection of an output — so it lives in the type of a refined run rather
-- than as a predicate on an observed list.
--
-- It is `UC.QueryBound.Exact`'s ledger over `_≤_`: the potential `Φ` is the
-- ledger, a downward output is what a step spends, `c` per activation from
-- above is what it is paid (`costᶜ`), and `QBᵢ`'s refined answers are exactly
-- the ledger's steps (`qbᵢ⇒ledger`).  The FINAL potential stays in the
-- run-level invariant because that is the form that recurses; it is dropped
-- once, at the end.
--
-- `CountBound` is a record, not a Σ: `weight` is not injective, so a
-- transparent pair strands `w` on a `weight _ ? ≟ weight _ w` constraint at
-- every use.

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Exact

module CategoricalCrypto.UC.QueryBound.Counting where

module _ {A B : Iface} (S : Set) (point : Dₚ S)
         (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
         where

  record CountBound (c : ℕ) : Set where
    field
      runs   : (w : List (Pos A ⊎ Neg B))
             → Dₚ (Σ[ os ∈ List (Neg A ⊎ Pos B) ] weight downward os ≤ c * weight fromAbove w)
      erases : (w : List (Pos A ⊎ Neg B))
             → mapₚ proj₁ (runs w) ≈ₚ behᵍ S point step w

costᶜ : {P Q : Set} → ℕ → P ⊎ Q → ℕ
costᶜ c (inj₁ _) = 0
costᶜ c (inj₂ _) = c

weight-costᶜ : {P Q : Set} (c : ℕ) (w : List (P ⊎ Q))
             → weight (costᶜ c) w ≡ c * weight fromAbove w
weight-costᶜ c []           = sym (*-zeroʳ c)
weight-costᶜ c (inj₁ _ ∷ w) = weight-costᶜ c w
weight-costᶜ c (inj₂ _ ∷ w) =
  trans (cong (c +_) (weight-costᶜ c w)) (sym (*-suc c (weight fromAbove w)))

module Budget = Ledgerᴿ _≤_ ≤-reflexive ≤-trans +-monoʳ-≤ +-monoˡ-≤

qbᵢ⇒ledger : {A B : Iface} (S : Set) (point : Dₚ S)
             (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B))) (c : ℕ)
           → QBᵢ S point step c → Budget.QEᵢ S point step downward (costᶜ c)
qbᵢ⇒ledger {A} {B} S point step c q = record
  { Λ = Φ ; pointᴱ = pointᵍ ; coh₀ = coh₀
  ; stepᴱ = λ where
      s (inj₁ a) → mapₚ (λ y → proj₁ (ansᴱ y) , ≤-trans (proj₂ (ansᴱ y)) (m≤m+n (Φ s) 0))
                        (onLᵍ s a)
      s (inj₂ b) → mapₚ ansᴱ (onRᵍ s b)
  ; cohᴱ = λ where
      s (inj₁ a) → map-fuse (onLᵍ s a) _ proj₁ forget agree ⟨≈⟩ cohL s a
      s (inj₂ b) → map-fuse (onRᵍ s b) ansᴱ proj₁ forget agree ⟨≈⟩ cohR s b
  }
  where
  open QBᵢ q

  ansᴱ : {r : ℕ} → Ans Φ (Neg A) (Pos B) r
       → Σ[ p ∈ S × (Neg A ⊎ Pos B) ] downward (proj₂ p) + Φ (proj₁ p) ≤ r
  ansᴱ (inj₁ ((s′ , lt) , a′)) = (s′ , inj₁ a′) , lt
  ansᴱ (inj₂ ((s′ , le) , b′)) = (s′ , inj₂ b′) , le

  agree : {r : ℕ} (y : Ans Φ (Neg A) (Pos B) r) → proj₁ (ansᴱ y) ≡ forget y
  agree (inj₁ _) = refl
  agree (inj₂ _) = refl

------------------------------------------------------------------------
-- The counting theorem

qbᵢ⇒count : {A B : Iface} (S : Set) (point : Dₚ S)
            (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B))) (c : ℕ)
          → QBᵢ S point step c → CountBound S point step c
qbᵢ⇒count {A} {B} S point step c q = record
  { runs   = λ w → mapₚ (drop w) (L.exactᴱ qe w)
  ; erases = λ w → map-map (L.exactᴱ qe w) (drop w) proj₁ ⟨≈⟩ L.exactᴱ-erases qe w
  }
  where
  module L = Budget S point step downward (costᶜ c)
  qe = qbᵢ⇒ledger S point step c q

  drop : (w : List (Pos A ⊎ Neg B))
       → Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] L.Balanced (L.QEᵢ.Λ qe) (weight (costᶜ c) w) p
       → Σ[ os ∈ List (Neg A ⊎ Pos B) ] weight downward os ≤ c * weight fromAbove w
  drop w ((s , os) , le) =
    os , m+n≤o⇒m≤o (weight downward os) (≤-trans le (≤-reflexive (weight-costᶜ c w)))

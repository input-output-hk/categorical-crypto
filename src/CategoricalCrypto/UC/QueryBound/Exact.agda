{-# OPTIONS --safe --without-K --guardedness #-}

-- Exact output counts: what a query BOUND cannot say.
--
-- `UC.QueryBound.QBᵢ` is an amortised UPPER bound — "at most `c` completed
-- activations below per activation from above" — and `UC.QueryBound.Counting`
-- turns it into `#downward ≤ c · #upward`.  A statement that a process
-- *performs* a query is the other side of that: it needs the count itself, not
-- a ceiling on it.
--
-- `QEᵢ` is the exact form, and the generalization it needs is small.  `δ`
-- weights the OUTPUTS that are being counted — `δ = 1` on downward outputs
-- counts queries, `δ = 1` on one query CONSTRUCTOR counts queries of that kind
-- — and `cost` weights the input letters that pay for them.  `Λ` is the ledger:
-- the weight still owed at a state.  The potential of an upper bound is
-- replaced by an EQUATION per step, and the run-level conclusion is an equation
-- too:
--
--     weight δ (outputs) + Λ (final state) ≡ weight cost (input word).
--
-- The residual `Λ` is the honest part of the statement — a run interrupted
-- mid-transaction owes the rest — and vanishes exactly when the run comes back
-- to a settled state.  Divergent branches carry no mass, so an off-protocol
-- word constrains nothing, which is why the statement needs no admissibility
-- side condition.
--
-- `QEᵢ` is `QBᵢ`'s exact twin, over the same state/point/step parameters and
-- concluding about the same `behᵍ`.  The ledger is stated over any relation
-- between what a run spends and what it was paid that is reflexive,
-- transitive and `+`-monotone (`Ledgerᴿ`): `Ledger` is it at `_≡_`, and
-- `UC.QueryBound.Counting` reads `QBᵢ` as it at `_≤_`.

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base
open import Data.Nat.ListAction
open import Data.Nat.Properties
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.QueryBound.Exact where

weight : {X : Set} → (X → ℕ) → List X → ℕ
weight w xs = sum (map w xs)

module Ledgerᴿ (_∼_ : ℕ → ℕ → Set)
               (∼-reflexive : {m n : ℕ} → m ≡ n → m ∼ n)
               (∼-trans : {l m n : ℕ} → l ∼ m → m ∼ n → l ∼ n)
               (∼-monoʳ : (k : ℕ) {m n : ℕ} → m ∼ n → (k + m) ∼ (k + n))
               (∼-monoˡ : (k : ℕ) {m n : ℕ} → m ∼ n → (m + k) ∼ (n + k))
               {A B : Iface} (S : Set) (point : Dₚ S)
               (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
               (δ : Neg A ⊎ Pos B → ℕ) (cost : Pos A ⊎ Neg B → ℕ)
               where

  record QEᵢ : Set where
    field
      Λ      : S → ℕ
      pointᴱ : Dₚ (Σ[ s ∈ S ] Λ s ∼ 0)
      coh₀   : mapₚ proj₁ pointᴱ ≈ₚ point
      stepᴱ  : (s : S) (x : Pos A ⊎ Neg B)
             → Dₚ (Σ[ p ∈ S × (Neg A ⊎ Pos B) ] (δ (proj₂ p) + Λ (proj₁ p)) ∼ (Λ s + cost x))
      cohᴱ   : (s : S) (x : Pos A ⊎ Neg B) → mapₚ proj₁ (stepᴱ s x) ≈ₚ step (s , x)

  Balanced : (Λ : S → ℕ) → ℕ → S × List (Neg A ⊎ Pos B) → Set
  Balanced Λ c p = (weight δ (proj₂ p) + Λ (proj₁ p)) ∼ c

  module _ (q : QEᵢ) where
    open QEᵢ q

    private
      cons : (o : Neg A ⊎ Pos B) {c : ℕ}
           → Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ c p
           → S × List (Neg A ⊎ Pos B)
      cons o r = proj₁ (proj₁ r) , o ∷ proj₂ (proj₁ r)

    runᴱ : (s : S) (w : List (Pos A ⊎ Neg B))
         → Dₚ (Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ (Λ s + weight cost w) p)
    runᴱ s []      = returnₚ ((s , []) , ∼-reflexive (sym (+-identityʳ (Λ s))))
    runᴱ s (x ∷ w) = stepᴱ s x >>=ₚ λ r →
      mapₚ (λ z → cons (proj₂ (proj₁ r)) z , chain r z) (runᴱ (proj₁ (proj₁ r)) w)
      where
      chain : (r : Σ[ p ∈ S × (Neg A ⊎ Pos B) ] (δ (proj₂ p) + Λ (proj₁ p)) ∼ (Λ s + cost x))
              (z : Σ[ p ∈ S × List (Neg A ⊎ Pos B) ]
                     Balanced Λ (Λ (proj₁ (proj₁ r)) + weight cost w) p)
            → Balanced Λ (Λ s + weight cost (x ∷ w)) (cons (proj₂ (proj₁ r)) z)
      chain r z =
        ∼-trans (∼-reflexive (+-assoc (δ o) (weight δ os) (Λ s″)))
          (∼-trans (∼-monoʳ (δ o) (proj₂ z))
            (∼-trans (∼-reflexive (sym (+-assoc (δ o) (Λ s′) (weight cost w))))
              (∼-trans (∼-monoˡ (weight cost w) (proj₂ r))
                (∼-reflexive (+-assoc (Λ s) (cost x) (weight cost w))))))
        where
        o  = proj₂ (proj₁ r)
        s′ = proj₁ (proj₁ r)
        s″ = proj₁ (proj₁ z)
        os = proj₂ (proj₁ z)

    runᴱ-erases : (s : S) (w : List (Pos A ⊎ Neg B))
                → mapₚ (λ z → proj₂ (proj₁ z)) (runᴱ s w) ≈ₚ traceᵍ S point step s w
    runᴱ-erases s []      = >>=ₚ-identityˡ _ _
    runᴱ-erases s (x ∷ w) =
        >>=ₚ-assoc (stepᴱ s x) _ _
      ⟨≈⟩ bindᶠ (λ r → map-map (runᴱ (proj₁ (proj₁ r)) w) _ _
                 ⟨≈⟩ ≈sym (map-map (runᴱ (proj₁ (proj₁ r)) w) _ _)
                 ⟨≈⟩ map-arg _ (runᴱ-erases (proj₁ (proj₁ r)) w))
      ⟨≈⟩ ≈sym ( bindˣ (≈sym (cohᴱ s x))
               ⟨≈⟩ >>=ₚ-assoc (stepᴱ s x) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ (proj₁ r) _))

    exactᴱ : (w : List (Pos A ⊎ Neg B))
           → Dₚ (Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ (weight cost w) p)
    exactᴱ w = pointᴱ >>=ₚ λ r →
      mapₚ (λ z → proj₁ z , ∼-trans (proj₂ z) (∼-monoˡ (weight cost w) (proj₂ r)))
           (runᴱ (proj₁ r) w)

    exactᴱ-erases : (w : List (Pos A ⊎ Neg B))
                  → mapₚ (λ z → proj₂ (proj₁ z)) (exactᴱ w) ≈ₚ behᵍ S point step w
    exactᴱ-erases w =
        >>=ₚ-assoc pointᴱ _ _
      ⟨≈⟩ bindᶠ (λ r → map-map (runᴱ (proj₁ r) w) _ _ ⟨≈⟩ runᴱ-erases (proj₁ r) w)
      ⟨≈⟩ ≈sym ( bindˣ (≈sym (coh₀))
               ⟨≈⟩ >>=ₚ-assoc pointᴱ _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ (proj₁ r) _))

module Ledger = Ledgerᴿ _≡_ (λ e → e) trans (λ k → cong (k +_)) (λ k → cong (_+ k))

open Ledger public

------------------------------------------------------------------------
-- Inhabitation

downward : {Q R : Set} → Q ⊎ R → ℕ
downward (inj₁ _) = 1
downward (inj₂ _) = 0

fromAbove : {P Q : Set} → P ⊎ Q → ℕ
fromAbove (inj₁ _) = 0
fromAbove (inj₂ _) = 1

-- `UC.QueryBound.qbᵢ-wire`'s bound read as an equation: where `QEᵢ` is seen
-- not to be vacuous.
qeᵢ-wire : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
         → QEᵢ ⊤ᵛ (returnₚ tt) (wireStep up down) downward fromAbove
qeᵢ-wire up down = record
  { Λ      = λ _ → 0
  ; pointᴱ = returnₚ (tt , refl)
  ; coh₀   = >>=ₚ-identityˡ (tt , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ  = λ where
      s (inj₁ p) → returnₚ ((s , inj₂ (up p))   , refl)
      s (inj₂ n) → returnₚ ((s , inj₁ (down n)) , refl)
  ; cohᴱ   = λ where
      s (inj₁ p) → >>=ₚ-identityˡ ((s , inj₂ (up p))   , refl) (returnₚ ∘′ proj₁)
      s (inj₂ n) → >>=ₚ-identityˡ ((s , inj₁ (down n)) , refl) (returnₚ ∘′ proj₁)
  }

------------------------------------------------------------------------
-- An exact count is a bound

-- A ledger over downward outputs whose letters from below cost nothing and
-- whose letters from above cost at most `c` is a `c`-bounded certificate with
-- the ledger as its potential.
exact⇒certified : {A B : Iface} {S : Set} {point : Dₚ S}
                  {step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B))}
                  {cost : Pos A ⊎ Neg B → ℕ} {c : ℕ}
                → QEᵢ S point step downward cost
                → ((a : Pos A) → cost (inj₁ a) ≡ 0) → ((b : Neg B) → cost (inj₂ b) ≤ c)
                → QBᵢ S point step c
exact⇒certified {A} {B} {S} {point} {step} {cost} {c} q free le = record
  { Φ      = Λ
  ; pointᵍ = mapₚ (λ r → proj₁ r , ≤-reflexive (proj₂ r)) pointᴱ
  ; coh₀   = map-map pointᴱ _ proj₁ ⟨≈⟩ coh₀
  ; onLᵍ   = λ s a → mapₚ (tag λ e → ≤-reflexive (trans e (trans (cong (Λ s +_) (free a))
                                                                (+-identityʳ (Λ s)))))
                          (stepᴱ s (inj₁ a))
  ; onRᵍ   = λ s b → mapₚ (tag λ e → ≤-trans (≤-reflexive e) (+-monoʳ-≤ (Λ s) (le b)))
                          (stepᴱ s (inj₂ b))
  ; cohL   = λ s a → map-fuse (stepᴱ s (inj₁ a)) _ forget proj₁ forget-tag ⟨≈⟩ cohᴱ s (inj₁ a)
  ; cohR   = λ s b → map-fuse (stepᴱ s (inj₂ b)) _ forget proj₁ forget-tag ⟨≈⟩ cohᴱ s (inj₂ b)
  }
  where
  open QEᵢ S point step downward cost q

  tag : {r t : ℕ} → ({s′ : S} {m : ℕ} → m + Λ s′ ≡ t → m + Λ s′ ≤ r)
      → Σ[ p ∈ S × (Neg A ⊎ Pos B) ] (downward (proj₂ p) + Λ (proj₁ p) ≡ t)
      → Ans Λ (Neg A) (Pos B) r
  tag h ((s′ , inj₁ x) , e) = inj₁ ((s′ , h e) , x)
  tag h ((s′ , inj₂ y) , e) = inj₂ ((s′ , h e) , y)

  forget-tag : {r t : ℕ} {h : {s′ : S} {m : ℕ} → m + Λ s′ ≡ t → m + Λ s′ ≤ r}
               (p : Σ[ p ∈ S × (Neg A ⊎ Pos B) ] (downward (proj₂ p) + Λ (proj₁ p) ≡ t))
             → forget (tag h p) ≡ proj₁ p
  forget-tag ((_ , inj₁ _) , _) = refl
  forget-tag ((_ , inj₂ _) , _) = refl

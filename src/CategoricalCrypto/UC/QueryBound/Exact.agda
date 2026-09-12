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
-- `qeᵢ-wire` is the inhabitation: a stateless relay emits exactly one downward
-- output per activation from above and none otherwise.
--
-- This is enrichment, in `UC.Budget`'s sense and no more: `QEᵢ` is `QBᵢ`'s
-- twin, over the same three parameters (a state, a point, a step — the
-- measured spelling `UC.QueryBound`'s header explains) and concluding about
-- the same `behᵍ`.  It is not a field of `UCSetup`, nothing is stated over it,
-- and it introduces no notion of simulator, context or experiment: a simulator
-- remains a grade morphism acting through `sub`
-- (`docs/uc-presheaf-preservation-plan.md` §1, decisions 3 and 5).

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; sym; trans; module ≡-Reasoning)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (wireStep; ⊤ᵛ)
open import CategoricalCrypto.UC.QueryBound using (behᵍ; traceᵍ)

module CategoricalCrypto.UC.QueryBound.Exact where

-- The weight of a word: `sum ∘ map`, spelled so that it reduces on a cons.
weight : {X : Set} → (X → ℕ) → List X → ℕ
weight w xs = sum (map w xs)

module Ledger {A B : Iface} (S : Set) (point : Dₚ S)
              (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
              (δ : Neg A ⊎ Pos B → ℕ) (cost : Pos A ⊎ Neg B → ℕ)
              where

  record QEᵢ : Set where
    field
      Λ      : S → ℕ
      pointᴱ : Dₚ (Σ[ s ∈ S ] Λ s ≡ 0)
      coh₀   : mapₚ proj₁ pointᴱ ≈ₚ point
      stepᴱ  : (s : S) (x : Pos A ⊎ Neg B)
             → Dₚ (Σ[ p ∈ S × (Neg A ⊎ Pos B) ] Λ s + cost x ≡ δ (proj₂ p) + Λ (proj₁ p))
      cohᴱ   : (s : S) (x : Pos A ⊎ Neg B) → mapₚ proj₁ (stepᴱ s x) ≈ₚ step (s , x)

  -- The ledger equation, at a run: the counted outputs plus what the final
  -- state still owes are what the word paid for.
  Balanced : (Λ : S → ℕ) → ℕ → S × List (Neg A ⊎ Pos B) → Set
  Balanced Λ c p = weight δ (proj₂ p) + Λ (proj₁ p) ≡ c

  module _ (q : QEᵢ) where
    open QEᵢ q

    private
      cons : (o : Neg A ⊎ Pos B) {c : ℕ}
           → Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ c p
           → S × List (Neg A ⊎ Pos B)
      cons o r = proj₁ (proj₁ r) , o ∷ proj₂ (proj₁ r)

    -- The refined run.  The `Dₚ`-level recursion is the trace's own; only the
    -- witness is new, and it is the ledger chain below.
    runᴱ : (s : S) (w : List (Pos A ⊎ Neg B))
         → Dₚ (Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ (Λ s + weight cost w) p)
    runᴱ s []      = returnₚ ((s , []) , sym (+-identityʳ (Λ s)))
    runᴱ s (x ∷ w) = stepᴱ s x >>=ₚ λ r →
      mapₚ (λ z → cons (proj₂ (proj₁ r)) z , chain r z) (runᴱ (proj₁ (proj₁ r)) w)
      where
      chain : (r : Σ[ p ∈ S × (Neg A ⊎ Pos B) ] Λ s + cost x ≡ δ (proj₂ p) + Λ (proj₁ p))
              (z : Σ[ p ∈ S × List (Neg A ⊎ Pos B) ]
                     Balanced Λ (Λ (proj₁ (proj₁ r)) + weight cost w) p)
            → Balanced Λ (Λ s + weight cost (x ∷ w)) (cons (proj₂ (proj₁ r)) z)
      chain r z = begin
        (δ o + weight δ os) + Λ s″     ≡⟨ +-assoc (δ o) (weight δ os) (Λ s″) ⟩
        δ o + (weight δ os + Λ s″)     ≡⟨ cong (δ o +_) (proj₂ z) ⟩
        δ o + (Λ s′ + weight cost w)   ≡⟨ +-assoc (δ o) (Λ s′) (weight cost w) ⟨
        (δ o + Λ s′) + weight cost w   ≡⟨ cong (_+ weight cost w) (proj₂ r) ⟨
        (Λ s + cost x) + weight cost w ≡⟨ +-assoc (Λ s) (cost x) (weight cost w) ⟩
        Λ s + (cost x + weight cost w) ∎
        where
        open ≡-Reasoning
        o  = proj₂ (proj₁ r)
        s′ = proj₁ (proj₁ r)
        s″ = proj₁ (proj₁ z)
        os = proj₂ (proj₁ z)

    -- …and it IS the run: forget the witness and the refinement is the trace.
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

    -- The closed form: the initial ledger is zero, so the word alone pays.
    exactᴱ : (w : List (Pos A ⊎ Neg B))
           → Dₚ (Σ[ p ∈ S × List (Neg A ⊎ Pos B) ] Balanced Λ (weight cost w) p)
    exactᴱ w = pointᴱ >>=ₚ λ r →
      mapₚ (λ z → proj₁ z , trans (proj₂ z) (cong (_+ weight cost w) (proj₂ r)))
           (runᴱ (proj₁ r) w)

    exactᴱ-erases : (w : List (Pos A ⊎ Neg B))
                  → mapₚ (λ z → proj₂ (proj₁ z)) (exactᴱ w) ≈ₚ behᵍ S point step w
    exactᴱ-erases w =
        >>=ₚ-assoc pointᴱ _ _
      ⟨≈⟩ bindᶠ (λ r → map-map (runᴱ (proj₁ r) w) _ _ ⟨≈⟩ runᴱ-erases (proj₁ r) w)
      ⟨≈⟩ ≈sym ( bindˣ (≈sym (coh₀))
               ⟨≈⟩ >>=ₚ-assoc pointᴱ _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ (proj₁ r) _))

open Ledger public

------------------------------------------------------------------------
-- Inhabitation

-- The two weightings a plain query count uses: one per output that travels
-- DOWN, one per activation that arrives from ABOVE.
downward : {Q R : Set} → Q ⊎ R → ℕ
downward (inj₁ _) = 1
downward (inj₂ _) = 0

fromAbove : {P Q : Set} → P ⊎ Q → ℕ
fromAbove (inj₁ _) = 0
fromAbove (inj₂ _) = 1

-- A stateless relay emits exactly one downward output per activation from
-- above and none per answer from below.  This is `UC.QueryBound.qbᵢ-wire`'s
-- bound read as an equation, and it is where the notion is seen not to be
-- vacuous.
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

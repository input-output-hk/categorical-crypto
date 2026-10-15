{-# OPTIONS --safe --without-K --guardedness #-}

-- SPEC ⊑ IMPL: implementation steps are simulated by the specification,
-- and enabled labels coincide, including τ and termination. This is strong
-- ready simulation (Bloom, Istrail, Meyer, JACM 42(1), 1995, pp. 232–268),
-- not completeness for failures/divergences or contextual equivalence.
module CategoricalCrypto.CSP.ReadyRefinement (E B R : Set) where

open import Data.List.Base
open import Data.Product.Base
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.Process E B R

private variable
  p q r t : Tree
  l : Label
  xs : List Visible

Enabled : Tree → Label → Set
Enabled p l = Σ Tree (λ q → p ─[ l ]→ q)

infix 4 _⊑_
record _⊑_ (spec impl : Tree) : Set where
  coinductive
  field
    match : ∀ {l t} → impl ─[ l ]→ t → Σ Tree (λ s → spec ─[ l ]→ s × s ⊑ t)
    ready : ∀ {l} → Enabled spec l → Enabled impl l

reflexive : p ⊑ p
_⊑_.match reflexive step = _ , step , reflexive
_⊑_.ready reflexive enabled = enabled

transitive : p ⊑ q → q ⊑ r → p ⊑ r
_⊑_.match (transitive {p = p} {q = q} first second) {l = l} {t = t} step = continue (_⊑_.match second step)
  where
  continue : Σ Tree (λ s → q ─[ l ]→ s × s ⊑ t)
    → Σ Tree (λ s → p ─[ l ]→ s × s ⊑ t)
  continue (s , move , next) = finish (_⊑_.match first move)
    where
    finish : Σ Tree (λ u → p ─[ l ]→ u × u ⊑ s) → Σ Tree (λ u → p ─[ l ]→ u × u ⊑ t)
    finish (u , move′ , next′) = u , move′ , transitive next′ next
_⊑_.ready (transitive first second) enabled = _⊑_.ready second (_⊑_.ready first enabled)

execute : p ⊑ q → Executes q xs t → Σ Tree (λ s → Executes p xs s × s ⊑ t)
execute ref done = _ , done , ref
execute ref (silent-step step rest) = continue (_⊑_.match ref step)
  where
  continue : Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _) → Σ Tree (λ s → Executes _ _ s × s ⊑ _)
  continue (s , move , next) = finish (execute next rest)
    where
    finish : Σ Tree (λ u → Executes s _ u × u ⊑ _) → Σ Tree (λ u → Executes _ _ u × u ⊑ _)
    finish (u , path , end) = u , silent-step move path , end
execute ref (visible-step step rest) = continue (_⊑_.match ref step)
  where
  continue : Σ Tree (λ s → _ ─[ visible _ ]→ s × s ⊑ _) → Σ Tree (λ s → Executes _ _ s × s ⊑ _)
  continue (s , move , next) = finish (execute next rest)
    where
    finish : Σ Tree (λ u → Executes s _ u × u ⊑ _) → Σ Tree (λ u → Executes _ _ u × u ⊑ _)
    finish (u , path , end) = u , visible-step move path , end

traces : p ⊑ q → Trace q xs → Trace p xs
traces ref (t , path) = proj₁ (execute ref path) , proj₁ (proj₂ (execute ref path))

stable : p ⊑ q → Stable q → Stable p
stable ref (noτ , no√) =
  (λ t step → rejectτ (_⊑_.ready ref (t , step))) ,
  (λ r t step → reject√ r (_⊑_.ready ref (t , step)))
  where
  rejectτ : Enabled _ τ → _
  rejectτ (t , step) = noτ t step
  reject√ : ∀ r → Enabled _ (visible (√ r)) → _
  reject√ r (t , step) = no√ r t step

refuses : ∀ {refusal} → p ⊑ q → Refuses q refusal → Refuses p refusal
refuses ref (st , absent) = stable ref st , λ e member t step → reject e member (_⊑_.ready ref (t , step))
  where
  reject : ∀ e → _ → Enabled _ (visible e) → _
  reject e member (t , step) = absent e member t step

failures : ∀ {refusal} → p ⊑ q → Failure q xs refusal → Failure p xs refusal
failures ref (t , path , refusal) = finish (execute ref path)
  where
  finish : Σ Tree (λ s → Executes _ _ s × s ⊑ t) → Failure _ _ _
  finish (s , path′ , next) = s , path′ , refuses next refusal

mutual
  diverges : p ⊑ q → Diverges q → Diverges p
  diverges ref d = divergence-tail (_⊑_.match ref (Diverges.step d)) (Diverges.rest d)

  divergence-tail : Σ Tree (λ s → p ─[ τ ]→ s × s ⊑ q) → Diverges q → Diverges p
  Diverges.next (divergence-tail (s , move , next) d) = s
  Diverges.step (divergence-tail (s , move , next) d) = move
  Diverges.rest (divergence-tail (s , move , next) d) = diverges next d

divergences : p ⊑ q → Divergence q xs → Divergence p xs
divergences ref (t , path , divergence) = finish (execute ref path)
  where
  finish : Σ Tree (λ s → Executes _ _ s × s ⊑ t) → Divergence _ _
  finish (s , path′ , next) = s , path′ , diverges next divergence

silent-prefix-diverges : Executes p [] q → Diverges q → Diverges p
silent-prefix-diverges done d = d
Diverges.next (silent-prefix-diverges (silent-step {q = q} move rest) d) = q
Diverges.step (silent-prefix-diverges (silent-step move rest) d) = move
Diverges.rest (silent-prefix-diverges (silent-step move rest) d) = silent-prefix-diverges rest d

record RawAgreement (p q : Tree) : Set₁ where
  field
    trace-agreement : ∀ xs → (Trace p xs → Trace q xs) × (Trace q xs → Trace p xs)
    failure-agreement : ∀ xs refusal → (Failure p xs refusal → Failure q xs refusal) × (Failure q xs refusal → Failure p xs refusal)
    divergence-agreement : ∀ xs → (Divergence p xs → Divergence q xs) × (Divergence q xs → Divergence p xs)

mutual-agreement : p ⊑ q → q ⊑ p → RawAgreement p q
mutual-agreement forward backward = record
  { trace-agreement = λ _ → traces backward , traces forward
  ; failure-agreement = λ _ _ → failures backward , failures forward
  ; divergence-agreement = λ _ → divergences backward , divergences forward }

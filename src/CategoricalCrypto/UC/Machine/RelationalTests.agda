{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.UC.Machine.RelationalTests where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD

open import Data.Bool.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
import Data.Rational.Properties as ℚP
open import Data.Rational.Properties.Ext using (1≰½)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles using (Equivalence)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Relational

import CategoricalCrypto.Machines.Trace as Trace

private
  module G = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module Tr = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

open MD.MonoidalDistributive (distₚ 0ℓ) using (_+₁_)

tracked erased : (X : Set) → MC.Machine X X
tracked X = MC.mk (initˢ Bool false) λ { (b , x) → returnₚ (not b , x) }
erased X = MC.mk (initˢ ⊤ tt) λ { (_ , x) → returnₚ (tt , x) }

forget : ∀ X → tracked X S.≲ erased X
forget X = simFn (λ _ → tt) (λ _ → >>=ₚ-identityˡ false _) λ { (b , x) → >>=ₚ-identityˡ (not b , x) _ }

functional : ∀ X → tracked X S.≲ erased X
functional X = Equivalence.from RS.≲⇔≲[id] (Equivalence.to RS.≲⇔≲[id] (forget X))

graph : ∀ X → RS.RelSim V.id V.id V.id V.id (tracked X) (erased X)
graph X = RS.≲⇒relsim (forget X)

behaviour : tracked Bool ≈ᴿ erased Bool
behaviour = relsim⇒≈ᴿ (graph Bool)

-- The right interface flips the visible bit while forgetting the hidden bit.
flipped-span : RS.RelSim V.id (K.pureᵏ not) V.id (K.pureᵏ not) (tracked Bool) (erased Bool)
flipped-span = record
  { apex = tracked Bool
  ; left = RS.≲⇒≲[id] S.≲-refl
  ; right = simFn[] (λ _ → tt) not not
      (λ _ → >>=ₚ-identityˡ false _)
      (λ { (b , x) → >>=ₚ-identityˡ (not b , x) _ }) }

flipped-output-pure : KP.IsPure (K.pureᵏ not)
flipped-output-pure = RS.output-pure (RS.right flipped-span)

random-tracked : MC.Machine Bool Bool
random-tracked = MC.mk (record { obj = Bool ; point = λ _ → coinₚ uniform-Bool })
  λ { (b , x) → returnₚ (not b , x) }

-- The apex samples once; the right leg complements that same sample.
coin-flipped-span : RS.RelSim V.id (K.pureᵏ not) V.id (K.pureᵏ not) random-tracked random-tracked
coin-flipped-span = record
  { apex = random-tracked
  ; left = RS.≲⇒≲[id] S.≲-refl
  ; right = simFn[] not not not
      (λ _ → coin-not uniform-Bool uniform-balanced returnₚ ⟨≈⟩ >>=ₚ-identityʳ (coinₚ uniform-Bool))
      (λ { (true , x) → >>=ₚ-identityˡ (false , x) _
         ; (false , x) → >>=ₚ-identityˡ (true , x) _ }) }

faircoin-map : Bool → Dₚ Bool
faircoin-map _ = coinₚ uniform-Bool

private
  coin-cap : (b : Bool) (n : ℕ) → cum n (coinₚ uniform-Bool) (indᵇ b) ℚ.≤ ½
  coin-cap b zero = toWitness {a? = 0ℚ ℚ.≤? ½} _
  coin-cap b (suc zero) = toWitness {a? = 0ℚ ℚ.≤? ½} _
  coin-cap true (suc (suc n)) = ℚP.≤-reflexive (coinₚ-cum uniform-Bool n (indᵇ true))
  coin-cap false (suc (suc n)) = ℚP.≤-reflexive (coinₚ-cum uniform-Bool n (indᵇ false))

  coin-not-dirac : (b : Bool) → ¬ (coinₚ uniform-Bool ≈ₚ returnₚ b)
  coin-not-dirac b eq =
    let n , le = proj₂ eq (indᵇ b) (indᵇ-nn b) 1
    in 1≰½ (ℚP.≤-trans (ℚP.≤-trans (ℚP.≤-reflexive (sym (return-one b))) le) (coin-cap b n))
    where
    return-one : (b : Bool) → cum 1 (returnₚ b) (indᵇ b) ≡ 1ℚ
    return-one true = returnₚ-cum 0 true (indᵇ true)
    return-one false = returnₚ-cum 0 false (indᵇ false)

faircoin-not-pure : ¬ KP.IsPure faircoin-map
faircoin-not-pure p = coin-not-dirac (KP.fn p false) (KP.is-fn p false)

-- The stochastic square commutes; a square alone does not certify marginals
-- under deterministic projections.
faircoin-square :
  (V._∘_ (V.id V.⊗₁ faircoin-map) (MC.step (MC.idᴹ {Bool})))
  V.≈ (V._∘_ (MC.step (MC.idᴹ {Bool})) (V.id V.⊗₁ faircoin-map))
faircoin-square = V.HomReasoning._○_ V.identityʳ (V.Equiv.sym V.identityˡ)

faircoin-simulation-excluded : ¬ (MC.idᴹ {Bool} RS.≲[ faircoin-map ∣ faircoin-map ] MC.idᴹ {Bool})
faircoin-simulation-excluded s = faircoin-not-pure (RS.output-pure s)

faircoin-span-excluded : ¬ (RS.RelSim V.id V.id faircoin-map V.id (MC.idᴹ {Bool}) (MC.idᴹ {Bool}))
faircoin-span-excluded r = faircoin-not-pure (RS.output-pure (RS.left r))

faircoin-input-span-excluded : ¬ (RS.RelSim faircoin-map V.id V.id V.id (MC.idᴹ {Bool}) (MC.idᴹ {Bool}))
faircoin-input-span-excluded r = faircoin-not-pure (RS.input-pure (RS.left r))

summed : RS.RelSim (V.id +₁ V.id) (V.id +₁ V.id) (V.id +₁ V.id) (V.id +₁ V.id)
           (T._⊗ᵉ_ (tracked Bool) (tracked Bool)) (T._⊗ᵉ_ (erased Bool) (erased Bool))
summed = RS.⊗ᵉ-relsim (graph Bool) (graph Bool)

private
  sum-id : (V.id +₁ V.id) V.≈ (V.id {Bool ⊎ Bool})
  sum-id (inj₁ x) = >>=ₚ-identityˡ x _
  sum-id (inj₂ x) = >>=ₚ-identityˡ x _

feedback : RS.RelSim V.id V.id V.id V.id
             (Tr.traceᴹ Bool Bool Bool (tracked (Bool ⊎ Bool)))
             (Tr.traceᴹ Bool Bool Bool (erased (Bool ⊎ Bool)))
feedback = RS.trace-relsim (KP.structural (λ x → x)) (KP.structural (λ x → x))
  (KP.structural (λ x → x)) (KP.structural (λ x → x))
  (KP.structural (λ x → x)) (KP.structural (λ x → x)) record
  { apex = RS.apex (graph (Bool ⊎ Bool))
  ; left = RS.≲[]-resp-≈ (V.Equiv.sym sum-id) (V.Equiv.sym sum-id) (RS.left (graph (Bool ⊎ Bool)))
  ; right = RS.≲[]-resp-≈ (V.Equiv.sym sum-id) (V.Equiv.sym sum-id) (RS.right (graph (Bool ⊎ Bool))) }

feedback-behaviour : Tr.traceᴹ Bool Bool Bool (tracked (Bool ⊎ Bool)) ≈ᴿ Tr.traceᴹ Bool Bool Bool (erased (Bool ⊎ Bool))
feedback-behaviour = relsim⇒≈ᴿ feedback

private
  μ = idᵐ {Bool , Bool}

G-compose : HSim μ μ
              (G._∘_ {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
              (G._∘_ {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
G-compose = HSim-∘ (HSim-id μ) (HSim-id μ)

G-tensor : HSim (μ ⊗ᵐ μ) (μ ⊗ᵐ μ)
             (G._⊗₁_ {Bool , Bool} {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
             (G._⊗₁_ {Bool , Bool} {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
G-tensor = HSim-⊗ (HSim-id μ) (HSim-id μ)

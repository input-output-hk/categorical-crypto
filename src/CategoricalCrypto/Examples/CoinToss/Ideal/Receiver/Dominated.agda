{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Model.Dominated.dominatedᵒ` at a NONTRIVIAL grade.
--
-- The model's domination compares two CLOSED processes inflated to the
-- trivial grade by `UC.Machine.Bridge.conjᴵ`, and every quantitative
-- statement above it that carries a grade is EXACT and reads
-- `UC.Asymptotic.Contextual.≈C⇒≈ctx` instead.  A hop that is approximate AND
-- graded — the corrupted-receiver hop is the first — has nothing to read.
--
-- The grade is not the obstacle.  `UC.Machine.Dominated.dominated`'s honest
-- interface is arbitrary, so a grade sitting beside it is already inside the
-- statement, and `UC.Model.Dominated.ctxRunᵒ` crosses the seal at an
-- arbitrary grade.  What is in the way is the unitor `conjᴵ` leaves in front
-- of the process, and `λᴵ⇒` cancels it: three wire absorptions and one
-- `⊗₁`-functoriality step.
--
-- This belongs beside `dominatedᵒ` in `UC.Model.Dominated`, and is here only
-- because that module was not this branch's to edit (`QUALITY-REVIEW.md`).
-- Nothing in it mentions the coin toss.
--
-- One deliberate difference from `ContextDominatedᵒ`: the strategy hypothesis
-- is at EVERY strategy rather than at every strategy of the context's
-- budget.  That is the shape an exact run agreement has, and it makes the
-- conclusion's error independent of the budget, so no allowance arithmetic
-- is spent crossing.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (tt)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-resp)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ; ⟦_⟧ᴵ)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; T₁ᴵ; wireᴹ; Ωᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (conjᴵ; ctxRun; λᴵ⇐)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁)
open import CategoricalCrypto.UC.Machine.Dominated using (dominated)
open import CategoricalCrypto.UC.Machine.Grading using (qb-T₁ᴳ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Machine.Wire using (sandwichᴹ; sandwich-∘; wire-∘ᴹ)
open import CategoricalCrypto.UC.Model.Dominated using (T₁ᵒ; ctxRunᵒ; unqb-closᵒ; unqb-testᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; gradedᵒ; ifaceᵒ; objᵒ; unclosᵒ; untestᵒ)
open import CategoricalCrypto.UC.QueryBound using (QB; certified⇒QB; qb-resp-≈; qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Dominated where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module 𝔾  = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Cancelling the hole wire

-- `UC.Machine.Bridge.λᴵ⇐`'s retraction, which that module has no use for.
λᴵ⇒ : {B : Iface} → Proc (unitᴵ ⊗ᴵ B) B
λᴵ⇒ = wireᴹ [ ⊥-elim , id ] inj₂

-- A renaming by two identities is no renaming.
sandwich-id : {X Y : Set} (f : Machine X Y) (i : X → X) (o : Y → Y)
            → ((z : X) → i z ≡ z) → ((w : Y) → o w ≡ w)
            → sandwichᴹ f i o ≈ᴹ f
sandwich-id f i o ei eo = ≲⇒≈ᴹ (mk-cong pt)
  where
  pt : (p : _) → _
  pt (s , z) = ≡⇒≈ₚ (cong (λ w → mapₚ (λ q → proj₁ q , o (proj₂ q)) (step f (s , w))) (ei z))
           ⟨≈⟩ map-eq (step f (s , z)) _ (λ q → q)
                      (λ q → cong (proj₁ q ,_) (eo (proj₂ q)))
           ⟨≈⟩ >>=ₚ-identityʳ (step f (s , z))

-- The two wires absorb into one renaming, and that renaming is the identity.
unit-cancel : {B : Iface} (x : Proc unitᴵ B) → 𝒫._≈_ {unitᴵ} {B} (λᴵ⇒ 𝒫.∘ conjᴵ x) x
unit-cancel {B} x =
     𝒫.∘-resp-≈ʳ (wire-∘ᴹ inj₂ [ ⊥-elim , id ] x)
  ○ᴹ wire-∘ᴹ [ ⊥-elim , id ] inj₂ (sandwichᴹ x i₁ o₁)
  ○ᴹ sandwich-∘ x i₁ o₁ i₂ o₂
  ○ᴹ sandwich-id x (λ z → i₁ (i₂ z)) (λ y → o₂ (o₁ y))
       (λ where (inj₁ ())
                (inj₂ _) → refl)
       (λ where (inj₁ ())
                (inj₂ _) → refl)
  where
  i₁ : Pos unitᴵ ⊎ Neg (unitᴵ ⊗ᴵ B) → Pos unitᴵ ⊎ Neg B
  i₁ = Sum.map (λ a → a) [ ⊥-elim , id ]

  o₁ : Neg unitᴵ ⊎ Pos B → Neg unitᴵ ⊎ Pos (unitᴵ ⊗ᴵ B)
  o₁ = Sum.map (λ a → a) inj₂

  i₂ : Pos unitᴵ ⊎ Neg B → Pos unitᴵ ⊎ Neg (unitᴵ ⊗ᴵ B)
  i₂ = Sum.map (λ a → a) inj₂

  o₂ : Neg unitᴵ ⊎ Pos (unitᴵ ⊗ᴵ B) → Neg unitᴵ ⊎ Pos B
  o₂ = Sum.map (λ a → a) [ ⊥-elim , id ]

-- …so relaying it past an ancilla is no relay either.
T₁-conj : {Y B : Iface} (x : Proc unitᴵ B)
        → 𝒫._≈_ {Y ⊗ᴵ unitᴵ} {Y ⊗ᴵ B} (T₁ᴵ Y x) (T₁ᴵ Y (λᴵ⇒ {B}) 𝒫.∘ T₁ᴵ Y (conjᴵ x))
T₁-conj {Y} {B} x =
     T₁-⊗₁ {Y} {unitᴵ} {B} x
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ Y ⟧ᴵ , ⟦ unitᴵ ⟧ᴵ)} {(⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ)}
       {(𝒫.id {Y} , x)} {(𝒫.id {Y} 𝒫.∘ 𝒫.id {Y} , λᴵ⇒ 𝒫.∘ conjᴵ x)}
       (𝒫.Equiv.sym 𝒫.identity² , 𝒫.Equiv.sym (unit-cancel x))
  ○ᴹ 𝔾.⊗.homomorphism
  ○ᴹ 𝒫.Equiv.sym (𝒫.∘-resp-≈ (T₁-⊗₁ {Y} (λᴵ⇒ {B})) (T₁-⊗₁ {Y} (conjᴵ x)))

-- …hence the bridge's observation is unchanged by opening the hole.
ctxRun-conj : {B Y : Iface} (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
              (x : Proc unitᴵ B)
            → ctxRun Y E m x ≈ₚ ctxRun Y (E 𝒫.∘ T₁ᴵ Y (λᴵ⇒ {B})) m (conjᴵ x)
ctxRun-conj {B} {Y} E m x =
  runᴹ-resp-≈ᴹ {Ωᴵ}
    (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (T₁-conj x) ○ᴹ 𝒫.sym-assoc)) (ask tt out)

------------------------------------------------------------------------
-- …and the domination it buys

dominatedᵍ : {P B : Iface} (W : G.Obj)
             (E : W G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ B) G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ W G.⊗₀ 𝟘ᵒ)
             {c c′ : ℕ} → Budget.QB budgetᵒ c E → Budget.QB budgetᵒ c′ m
           → (u v : Proc unitᴵ (P ⊗ᴵ B)) (ε δ : ℚ) → 0ℚ ℚ.< δ
           → ((d : Strat (Neg (P ⊗ᴵ B)) (Pos (P ⊗ᴵ B))) → runᴹ u d ≈ₚ[ ε ] runᴹ v d)
           → Obs ((E G.∘ T₁ᵒ W (gradedᵒ u)) G.∘ m)
             ≈ₚ[ ε ℚ.+ δ ] Obs ((E G.∘ T₁ᵒ W (gradedᵒ v)) G.∘ m)
dominatedᵍ {P} {B} W E m qE qm u v ε δ 0<δ h =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (open-hole u)) (≈ₚ-sym _ _ (open-hole v))
    (dominated (P ⊗ᴵ B) (objᵒ W) Eᶜ (unclosᵒ W m) qEᶜ (unqb-closᵒ W qm)
               u v ε δ 0<δ (λ d _ → h d))
  where
  Eᶜ : Proc (objᵒ W ⊗ᴵ (unitᴵ ⊗ᴵ (P ⊗ᴵ B))) Ωᴵ
  Eᶜ = untestᵒ W E 𝒫.∘ T₁ᴵ (objᵒ W) (λᴵ⇒ {P ⊗ᴵ B})

  qEᶜ : QB _ Eᶜ
  qEᶜ = qb-∘-category (objᵒ W ⊗ᴵ (unitᴵ ⊗ᴵ (P ⊗ᴵ B))) (objᵒ W ⊗ᴵ (P ⊗ᴵ B)) Ωᴵ
          (untestᵒ W E) (T₁ᴵ (objᵒ W) λᴵ⇒) (unqb-testᵒ W qE)
          (qb-resp-≈ (𝒫.Equiv.sym (T₁-⊗₁ {objᵒ W} (λᴵ⇒ {P ⊗ᴵ B})))
            (qb-T₁ᴳ (objᵒ W) (unitᴵ ⊗ᴵ (P ⊗ᴵ B)) (P ⊗ᴵ B) λᴵ⇒
              (certified⇒QB (qbᵢ-wire [ ⊥-elim , id ] inj₂))))

  open-hole : (x : Proc unitᴵ (P ⊗ᴵ B))
            → Obs ((E G.∘ T₁ᵒ W (gradedᵒ x)) G.∘ m)
              ≈ₚ ctxRun (objᵒ W) Eᶜ (unclosᵒ W m) (conjᴵ x)
  open-hole x = ctxRunᵒ W E m x
            ⟨≈⟩ ctxRun-conj (untestᵒ W E) (unclosᵒ W m) x

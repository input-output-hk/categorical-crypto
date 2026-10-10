{-# OPTIONS --safe --without-K --guardedness #-}

-- A compiled relabelling is its wire after the monitor (`docs/uc-setup-ssp.md`
-- §4.3): `morphism (toProtocol ⌜ f ⌝)` checks a reply's channel against its
-- open call and is `botₚ` off protocol, which is exactly what the compiled
-- identity `morphism (toProtocol wireᵖ)` does before a stateless relabelling
-- renames.  At `Protᴹ`'s unitors and associator this relates their compiled
-- images to `𝒲ᴹ`'s structural wires.
--
-- `UC.Machine.Wire.wire-∘ᴹ` absorbs the wire, so no trace is unrolled.  The
-- two waiting states store different continuations, equal only pointwise, so
-- without funext neither side simulates the other: both are simulated out of a
-- machine whose state is the open call's channel, if any (the technique of
-- `Protocol.Machine.Resp`).

open import Categories.Category

open import Class.DecEq
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Protocol as Flat

module CategoricalCrypto.UC.Bracket.Relabel where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

private variable A B C : Iface

------------------------------------------------------------------------
-- A compiled relabelling

module _ (f : A ⇒ᴵ B) (up : Σ (Ch B) (R B) → Σ (Ch A) (R A)) (down : Σ (Ch A) (Q A) → Σ (Ch B) (Q B))
         (up-ok : ∀ c r → up (ch f c , r) ≡ (c , re f r))
         (down-ok : ∀ c q → down (c , q) ≡ (ch f c , qu f q)) where

  private
    relabel : Flat.Protocol (flat B) (flat A)
    relabel = toProtocol ⦃ Ch-dec B ⦄ ⌜ f ⌝

    monitor : Flat.Protocol (flat B) (flat B)
    monitor = toProtocol ⦃ Ch-dec B ⦄ (wireᵖ {B})

    Out : Set
    Out = Maybe (Ch A) × (Σ (Ch B) (Q B) ⊎ Σ (Ch A) (R A))

    answerʳ : {c′ : Ch B} (c : Ch A) → Dec (c′ ≡ ch f c) → R B c′ → Dₚ Out
    answerʳ c (yes refl) r = returnₚ (nothing , inj₂ (c , re f r))
    answerʳ c (no _)     _ = botₚ

    stepʳ : Maybe (Ch A) × (Σ (Ch B) (R B) ⊎ Σ (Ch A) (Q A)) → Dₚ Out
    stepʳ (nothing , inj₂ (c , q))  = returnₚ (just c , inj₁ (ch f c , qu f q))
    stepʳ (just c  , inj₁ (c′ , r)) = answerʳ c (_≟_ ⦃ Ch-dec B ⦄ c′ (ch f c)) r
    stepʳ (nothing , inj₁ _)        = botₚ
    stepʳ (just _  , inj₂ _)        = botₚ

    machineʳ : Proc (flat B) (flat A)
    machineʳ = MC.mk (initˢ (Maybe (Ch A)) nothing) stepʳ

    π : Maybe (Ch A) → MSt relabel
    π nothing  = idle tt
    π (just c) = wait λ x → reply {A = B} ⦃ Ch-dec B ⦄ (_≟_ ⦃ Ch-dec B ⦄ (proj₁ x) (ch f c)) (proj₂ x)
                                  λ r → Flat.ret (tt , c , re f r)

    π′ : Maybe (Ch A) → MSt monitor
    π′ nothing  = idle tt
    π′ (just c) = wait λ x → reply {A = B} ⦃ Ch-dec B ⦄ (_≟_ ⦃ Ch-dec B ⦄ (proj₁ x) (ch f c)) (proj₂ x)
                                   λ r → Flat.ret (tt , ch f c , r)

    answer-π : {c′ : Ch B} (c : Ch A) (d : Dec (c′ ≡ ch f c)) (r : R B c′)
             → (answerʳ c d r >>=ₚ Pw.padϕ π)
               ≈ₚ drive relabel (reply {A = B} ⦃ Ch-dec B ⦄ d r λ r → Flat.ret (tt , c , re f r))
    answer-π c (yes refl) r = >>=ₚ-identityˡ (nothing , inj₂ (c , re f r)) (Pw.padϕ π)
    answer-π c (no _)     _ = bot-bind-≈ₚ (Pw.padϕ π)

    answer-π′ : {c′ : Ch B} (c : Ch A) (d : Dec (c′ ≡ ch f c)) (r : R B c′)
              → (answerʳ c d r >>=ₚ Pw.padϕ π′)
                ≈ₚ mapₚ (λ q → proj₁ q , Sum.map (λ a → a) up (proj₂ q))
                        (drive monitor (reply {A = B} ⦃ Ch-dec B ⦄ d r λ r → Flat.ret (tt , ch f c , r)))
    answer-π′ c (yes refl) r =
      >>=ₚ-identityˡ (nothing , inj₂ (c , re f r)) (Pw.padϕ π′)
      ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (idle tt , inj₂ (ch f c , r)) _ ⟨≈⟩ ret≡ (cong (λ y → idle tt , inj₂ y) (up-ok c r)))
    answer-π′ c (no _)     _ = bot-bind-≈ₚ (Pw.padϕ π′) ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

    π-sim : machineʳ S.≲ morphism relabel
    π-sim = Pw.simFn π (λ _ → >>=ₚ-identityˡ nothing _) λ where
      (nothing , inj₂ (c , q))  → >>=ₚ-identityˡ (just c , inj₁ (ch f c , qu f q)) (Pw.padϕ π)
      (just c  , inj₁ (c′ , r)) → answer-π c (_≟_ ⦃ Ch-dec B ⦄ c′ (ch f c)) r
      (nothing , inj₁ _)        → bot-bind-≈ₚ (Pw.padϕ π)
      (just _  , inj₂ _)        → bot-bind-≈ₚ (Pw.padϕ π)

    π′-sim : machineʳ S.≲ sandwichᴹ (morphism monitor) (Sum.map (λ a → a) down) (Sum.map (λ a → a) up)
    π′-sim = Pw.simFn π′ (λ _ → >>=ₚ-identityˡ nothing _) λ where
      (nothing , inj₂ (c , q))  →
        >>=ₚ-identityˡ (just c , inj₁ (ch f c , qu f q)) (Pw.padϕ π′)
        ⟨≈⟩ ≈sym ( ≡⇒≈ₚ (cong (λ n → mapₚ (λ q → proj₁ q , Sum.map (λ a → a) up (proj₂ q))
                                           (stepᴹ monitor (idle tt , inj₂ n)))
                              (down-ok c q))
                 ⟨≈⟩ >>=ₚ-identityˡ (π′ (just c) , inj₁ (ch f c , qu f q)) _)
      (just c  , inj₁ (c′ , r)) → answer-π′ c (_≟_ ⦃ Ch-dec B ⦄ c′ (ch f c)) r
      (nothing , inj₁ _)        → bot-bind-≈ₚ (Pw.padϕ π′) ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)
      (just _  , inj₂ _)        → bot-bind-≈ₚ (Pw.padϕ π′) ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

  relabel≈ : 𝒫._≈_ {flat B} {flat A} (morphism (toProtocol ⦃ Ch-dec B ⦄ ⌜ f ⌝))
               (𝒫._∘_ {flat B} {flat B} {flat A} (wireᴹ up down) (morphism (toProtocol ⦃ Ch-dec B ⦄ (wireᵖ {B}))))
  relabel≈ = S.≲⇒≈ᴹ˘ π-sim S.○ᴹ S.≲⇒≈ᴹ π′-sim
         S.○ᴹ S.⟺ᴹ (wire-∘ᴹ {flat B} {flat B} {flat A} up down (morphism monitor))

------------------------------------------------------------------------
-- At the structural maps of `Protᴹ`

λ-relabel : 𝒫._≈_ {flat (unitᴵ ⊗ᴵ A)} {flat A} (morphism (toProtocol ⦃ Ch-dec (unitᴵ ⊗ᴵ A) ⦄ ⌜ ι₂ {B = A} {A = unitᴵ} ⌝))
              (𝒫._∘_ {flat (unitᴵ ⊗ᴵ A)} {flat (unitᴵ ⊗ᴵ A)} {flat A} (λʷ {A})
                (morphism (toProtocol ⦃ Ch-dec (unitᴵ ⊗ᴵ A) ⦄ (wireᵖ {unitᴵ ⊗ᴵ A}))))
λ-relabel {A} = relabel≈ (ι₂ {B = A} {A = unitᴵ}) dropΣˡ addΣˡ (λ _ _ → refl) (λ _ _ → refl)

ρ-relabel : 𝒫._≈_ {flat (A ⊗ᴵ unitᴵ)} {flat A} (morphism (toProtocol ⦃ Ch-dec (A ⊗ᴵ unitᴵ) ⦄ ⌜ ι₁ {A = A} {B = unitᴵ} ⌝))
              (𝒫._∘_ {flat (A ⊗ᴵ unitᴵ)} {flat (A ⊗ᴵ unitᴵ)} {flat A} (ρʷ {A})
                (morphism (toProtocol ⦃ Ch-dec (A ⊗ᴵ unitᴵ) ⦄ (wireᵖ {A ⊗ᴵ unitᴵ}))))
ρ-relabel {A} = relabel≈ (ι₁ {A = A} {B = unitᴵ}) dropΣʳ addΣʳ (λ _ _ → refl) (λ _ _ → refl)

α-relabel : 𝒫._≈_ {flat ((A ⊗ᴵ B) ⊗ᴵ C)} {flat (A ⊗ᴵ (B ⊗ᴵ C))}
              (morphism (toProtocol ⦃ Ch-dec ((A ⊗ᴵ B) ⊗ᴵ C) ⦄ ⌜ αᴵ⁻¹ {A} {B} {C} ⌝))
              (𝒫._∘_ {flat ((A ⊗ᴵ B) ⊗ᴵ C)} {flat ((A ⊗ᴵ B) ⊗ᴵ C)} {flat (A ⊗ᴵ (B ⊗ᴵ C))} (αʷ {A} {B} {C})
                (morphism (toProtocol ⦃ Ch-dec ((A ⊗ᴵ B) ⊗ᴵ C) ⦄ (wireᵖ {(A ⊗ᴵ B) ⊗ᴵ C}))))
α-relabel {A} {B} {C} = relabel≈ (αᴵ⁻¹ {A} {B} {C}) assocΣʳ assocΣˡ
  (λ where (inj₁ _) _ → refl ; (inj₂ (inj₁ _)) _ → refl ; (inj₂ (inj₂ _)) _ → refl)
  (λ where (inj₁ _) _ → refl ; (inj₂ (inj₁ _)) _ → refl ; (inj₂ (inj₂ _)) _ → refl)

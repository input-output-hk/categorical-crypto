{-# OPTIONS --safe --without-K --guardedness #-}

-- The family UC premise on protocol images, with its error KEPT: `_≈ᶠᴺ_`.
--
-- `≤UC[]⇒≤UCᴺ` is where a FIXED-DATA quantitative bound
-- (`UC.Quantitative.Family._≤UC[_,_]_`) reaches the canonical negligible
-- order: the route stops at `_≈ℰⁿ_`, which still carries the one global
-- schedule, and is read in `ucSetupᴺ`'s own kernel (the `_≈ᵁ_` of
-- `UC.Family.Negligible.Setup.Canonicalᴺ` is `_≈ℰᴺ_`), spending no
-- `absorb-negl`.
--
-- What the canonical order then STATES is weaker than what the bound gives:
-- a certified simulator family plus a negligible witness chosen inside the
-- contextual quantification (`≈ℰⁿ⇒≈ℰᴺ` specializes the one schedule to each
-- context's allowance).  It does not expose that schedule, and nothing
-- recovers a global one from it — so a caller that needs the number keeps the
-- `_≤UC[_,_]_` data rather than reconstructing it from the corollary.

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Audit.Context

import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Model.Family.Emulation where

private module Cᴺ = Canonicalᴺ

open GradedSubCat gradingᵒ

Systems : (ℕ → Iface) → Set₁
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

private variable B : ℕ → Iface
                 R I : Systems B

------------------------------------------------------------------------
-- The images and the ε-approximate family agreement

gradedᶠ : (B : ℕ → Iface) → Obj^ω
gradedᶠ B = Δ Gr.𝟘ᴳ ⊛ω ifaceᶠ B

imgᶠ : (B : ℕ → Iface) (R : Systems B) (n : ℕ) → 𝟘ᵒ ⇒ gradedᶠ B n
imgᶠ B R n = Gr.closedᵒ (morphism (R n))

infix 4 _≈ᶠ[_]_

_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁
_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I

infix 4 _≈ᶠᴺ_

-- Symmetric and simulator-free; the simulator-bearing relation is
-- `UC.Quantitative.Family._≤UC^ωᵉ_`.
_≈ᶠᴺ_ : Systems B → Systems B → Set₁
R ≈ᶠᴺ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I

------------------------------------------------------------------------
-- The witness form, and the `_≈ℰⁿ_` tier it lands in

-- `ε` is EXPLICIT here and in `≈ᶠ-runs`, for `UC.Approximate.GradedBound-+[_]`'s
-- reason.  An implication, not an identification: `_≈ℰ[_]_` quantifies over
-- levelwise FAMILIES of contexts carrying one polynomial, where the contextual
-- relation quantifies each level's context separately.
≈ctxᴬ⇒≈ℰ[] : {A X B : Obj^ω} (ε : ℕ → ℕ → ℚ) (f g : A ⇒^ω (X ⊛ω B))
           → sim f ≈ctxᴬ[ ε ] sim g → _≈ℰ[_]_ {A} {X ⊛ω B} f ε g
≈ctxᴬ⇒≈ℰ[] _ _ _ h Y Et m _ cE n =
  h n (Y n) ⌊ hom Et n ⌋ ⌊ hom m n ⌋ (cE n) (hom m n , Equiv.refl)

module _ {A X Y B : Obj^ω} (s : Certified Y X) (ε : ℕ → ℕ → ℚ)
         (neg : NegligibleBound ε) (f : A ⇒^ω (X ⊛ω B)) (g : A ⇒^ω (Y ⊛ω B))
         (e : sim f ≤UC[ s , ε ] sim g) where

  ≤UC[]⇒≈ℰⁿ : _≈ℰⁿ_ {A} {X ⊛ω B} f (Cᴺ.sub s Cᴺ.∘ g)
  ≤UC[]⇒≈ℰⁿ = ε , carried-negligible {ε = ε} neg
            , ≈ctxᴬ⇒≈ℰ[] ε f (Cᴺ.sub s Cᴺ.∘ g) (≈ctx⇒≈ctxᴬ ε e)

  ≤UC[]⇒≤UCᴺ : f Cᴺ.≤UC g
  ≤UC[]⇒≤UCᴺ = Cᴺ.dummy-complete {f = f} {g} (s , ≈ℰⁿ⇒≈ℰᴺ f (Cᴺ.sub s Cᴺ.∘ g) ≤UC[]⇒≈ℰⁿ)

-- Read at `UC.Seam.Audit.Context`'s context — the embedded strategy behind the
-- two unitors, at its own ask-depth, with a unitor closure at `1⁺` (hence
-- `*-identityʳ`) — the premise's `ε` lands on the DIRECT runs.
≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I
        → (n : ℕ) (q : ℕ⁺) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (value q) d
        → runᴹ (morphism (R n)) d ≈ₚ[ ε n (value q) ] runᴹ (morphism (I n)) d
≈ᶠ-runs ε h n q d a =
  subst (λ k → _ ≈ₚ[ ε n k ] _) (*-identityʳ (value q))
        (≈ₚ[]-resp (audit-run _ d _) (audit-run _ d _)
                   (h n Gr.𝟘ᴳ (auditTest _ d) auditClose {q} {1⁺}
                      ((auditTest _ d , audit-qb _ d q a) , Equiv.refl)
                      ((auditClose , pred-λ⇐) , Equiv.refl)))

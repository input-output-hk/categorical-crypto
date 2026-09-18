{-# OPTIONS --safe --without-K --guardedness #-}

-- The qualitative carry at the intended instance, and the API's acceptance
-- tests.
--
-- The carry is the CANONICAL one: `UC.Robust` at `UC.Model.Setup`, whose
-- premise is the inherited `_≤UC_` directly — `≤UC⇒dummy` supplies the
-- simulator, so the detour through the core's order has left this proof
-- (`UC.Model.Bridge.≤UC⇒≤UCᶜ` stays; it is the seam's own two-way
-- identification of the orders, whose gate is importer migration, not this one
-- call).  What connects it to the observation-scoped statements is `propᵒ`,
-- the adapter turning an observation-invariant predicate into a saturated
-- predicate on tests, and `UC.Model.Reading`'s bracketing shuffle.
--
-- `UC.Robust.Observation` keeps its own scope and is not derived: it is stated
-- at an arbitrary `UCBase`, where there is no graded Kleisli triple.  Its names
-- are re-exported here unchanged; the canonical API is reached through `Gen`.
--
-- SCOPE: see `UC.Robust`'s header.  Nothing here bounds a probability, so
-- nothing here discharges the monitor-inclusion or error-uniformity obligations
-- of `docs/protocol-implementation-review.md` §§1-2.

open import Data.Unit.Base using (tt)

open import Level using (Level; 0ℓ; _⊔_; suc)

open import CategoricalCrypto.Iface using (Iface)
open import CategoricalCrypto.UC.Model.Pin using (relayᵒ)
open import CategoricalCrypto.UC.Model.Reading using (shuffle⇒; shuffle⇐)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Environment as Env
import CategoricalCrypto.UC.Robust.Observation as RobO
import CategoricalCrypto.UC.Robust.Selected as Sel

module CategoricalCrypto.UC.Robust.Model where

open import CategoricalCrypto.UC.Environment baseᵗ using (Obs)

open HomReasoning

-- The canonical preservation, at this setup.  Its `SaturatedProperty` and
-- `Robust` stay qualified: the names below are the observation-scoped ones,
-- and they are different statements.
module Gen = Sel StdSetup

private
  module Core = Env baseᵗ
  module R = RobO baseᵗ

open R public
  using ( SaturatedProperty; holds; saturated; ⊤ᴾ; ∼[_]; Robust; robust-resp-≈ℰ
        ; robust-sub )

private variable A B X Y : Channel
                 p : Level

------------------------------------------------------------------------
-- The observation-predicate adapter

-- A test holds an observation-invariant predicate when every closure of it
-- shows one.  Saturation is the test setoid's own equality, evaluated at each
-- closure — no property-specific argument is spent, which is what makes the
-- adapter available for every `SaturatedProperty` at once.  It is NOT part of
-- the theorem for all UC setups: a setup need not have a closed run at all.
propᵒ : SaturatedProperty p → (D : Channel) → Gen.SaturatedProperty (suc 0ℓ ⊔ p) D
propᵒ 𝔓 D = record
  { holds     = λ t → (m : Core.Closure D) → holds 𝔓 Core.⟦ t ∘ m ⟧
  ; saturated = λ eq h m → saturated 𝔓 (eq m) (h m) }

-- …and the two bracketings of a closing context, which is all that separates
-- the observation-scoped `Robust` from the canonical one at this setup.
robust⇒robustᵍ : (𝔓 : SaturatedProperty p) {f : A ⇒ T₀ X B}
               → Robust 𝔓 f → Gen.Robust (λ W → propᵒ 𝔓 (T₀ W A)) Gen.⊤ᴬ f
robust⇒robustᵍ 𝔓 {f = f} rob W e _ m =
  saturated 𝔓 (Core.⟦⟧-resp-≈ (assoc ○ ⟺ (shuffle⇐ f e m))) (rob W (e ∘ α⇐) m)

robustᵍ⇒robust : (𝔓 : SaturatedProperty p) {f : A ⇒ T₀ X B}
               → Gen.Robust (λ W → propᵒ 𝔓 (T₀ W A)) Gen.⊤ᴬ f → Robust 𝔓 f
robustᵍ⇒robust 𝔓 {f = f} rob W Et m =
  saturated 𝔓 (Core.⟦⟧-resp-≈ (shuffle⇒ f Et m ○ sym-assoc)) (rob W (Et ∘ α⇒) tt m)

------------------------------------------------------------------------
-- Preservation at the model

uc-preservesᵒ : (𝔓 : SaturatedProperty p) {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
              → f ≤UC g → Robust 𝔓 g → Robust 𝔓 f
uc-preservesᵒ {A = A} 𝔓 le rob = robustᵍ⇒robust 𝔓
  (Gen.uc-preserves (λ W → propᵒ 𝔓 (T₀ W A)) Gen.⊤ᴬ (λ _ _ _ _ → tt) le
    (robust⇒robustᵍ 𝔓 rob))

⊤-robust : (f : A ⇒ B) → Robust ⊤ᴾ f
⊤-robust _ _ _ _ = tt

-- If no closing context tells the ideal system apart from a designated
-- verdict, none tells the real one apart either.
verdict-preservedᵒ : (r : Obs) {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
                   → f ≤UC g → Robust ∼[ r ] g → Robust ∼[ r ] f
verdict-preservedᵒ r = uc-preservesᵒ ∼[ r ]

------------------------------------------------------------------------
-- A selected environment class, at a concrete simulator

-- The acceptance test the top class cannot give: a nontrivial `Adm`
-- (`UC.Robust.Selected.Factors`), a simulator that is a real machine — the
-- relay of `UC.Model.Pin`, which exposes its own caller interface as its grade
-- — and the preservation applied at that explicit witness rather than at an
-- all-simulators closure.
relay-selectedᵒ : (𝔄 : Iface) (r : Obs) (V : Channel)
                → Gen.Robust (λ W → propᵒ ∼[ r ] (T₀ W (ifaceᵒ 𝔄))) (Gen.Factors V)
                             (relayᵒ 𝔄)
                → Gen.Robust (λ W → propᵒ ∼[ r ] (T₀ W (ifaceᵒ 𝔄))) (Gen.Factors V)
                             (sub (relayᵒ 𝔄) ∘ relayᵒ 𝔄)
relay-selectedᵒ 𝔄 r V =
  Gen.uc-preserves-factors (λ W → propᵒ ∼[ r ] (T₀ W (ifaceᵒ 𝔄))) V (relayᵒ 𝔄) ≈ᵁ-refl

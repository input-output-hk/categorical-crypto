{-# OPTIONS --safe --without-K --guardedness #-}

-- Two of `UC.Seam.Grounding`'s statements are FALSE at the intended model.
--
-- The mechanism is `UC.Seam.Grounding.Dead`: a process whose initial state
-- diverges observes nothing in any context.  Two consequences.
--
--   `UnitGrade`  is false at EVERY trivial grade.  Take the simulator to be
--                such a process: `sub s ∘ (ι ∘ v)` then observes nothing, so a
--                `u` that observes nothing emulates every `v`, while `Agreeˢ`
--                still compares the two runs.  `_≤UC_`'s simulator quantifier
--                admits a divergent simulator and nothing downstream excludes
--                it.
--   `SubBlind`   says every scalar `𝟘 ⇒ 𝟘` acts as the identity, and is false
--                for the same reason.  `no-trivial-grade` shows it is not
--                merely unproved: together with `IotaBlind` — a theorem at the
--                unit grade (`UC.Seam.Grounded.iotaBlind`) — it identifies all
--                closed processes.
--
-- The separation is layer 1's own: `Adequacy` turns both context runs into
-- direct runs, and `Pr≤` tells a divergent process from one that answers.
--
-- A repair is therefore a restriction on the simulator, not a proof: `_≤UC_`'s
-- `Σ[ s ] …` has to be cut down to the non-degenerate `s` (a termination-mass
-- side condition on `point`, or a subcategory of machines with a pure point).
-- Both change a statement, so both are the maintainer's call.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (Bool; true)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
  using (+-identityˡ; ≤-reflexive; ≤-trans; _<?_; _≤?_)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (Pr≤[_]; indᵇ-nn)
open import ProbabilisticLogic.Dp.Zero

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒫ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ; ⟦_⟧ᴼ; ⊤ᵛ; ucBaseᴹ)
open import CategoricalCrypto.UC.Seam using (Agreeˢ; ctxRunˢ)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ; iotaBlind; stratIsEnv)
open import CategoricalCrypto.UC.Seam.Grounding using (module TrivialGrade)
open import CategoricalCrypto.UC.Seam.Grounding.Dead

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounding.Refuted where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝔾  = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E  = Em ucBaseᴹ

open E using (_≈ℰ_; ≈ℰ-sym; ≈ℰ-trans)

------------------------------------------------------------------------
-- A closed process that does observe something

private
  v₁ : Proc unitᴵ Ωᴵ
  v₁ = MC.mk (record { obj = ⊤ᵛ ; point = λ _ → returnₚ ttᵛ
                     ; discard = λ _ → returnₚ ttᵛ })
             λ _ → returnₚ (ttᵛ , inj₂ true)

  v₁-run : ⟦ v₁ ⟧ᴼ ≈ₚ returnₚ true
  v₁-run = ≈ₚ-trans _ _ _ (>>=ₚ-identityˡ ttᵛ _)
                          (>>=ₚ-identityˡ (ttᵛ , inj₂ true) _)

  -- Read off by projection, never by `with`: the goal mentions `⟦ v₁ ⟧ᴼ`, and
  -- abstracting a scrutinee out of it normalizes the machine run.  Measured at
  -- ≥94 s against 8 s for the same module without the abstraction.
  v₁-mass : Σ[ m ∈ ℕ ] (1ℚ ℚ.≤ Pr≤[ true ] m ⟦ v₁ ⟧ᴼ)
  v₁-mass = proj₁ reads
          , ≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
                    (proj₂ reads)
    where reads = proj₂ v₁-run (indᵇ true) (indᵇ-nn true) 1

deadᴼ : Proc unitᴵ Ωᴵ
deadᴼ = deadᴹ ⟦ unitᴵ ⟧ᴵ ⟦ Ωᴵ ⟧ᴵ

private
  0<½ : 0ℚ ℚ.< ½
  0<½ = toWitness {a? = 0ℚ <? ½} _

  1≰½ : ¬ (1ℚ ℚ.≤ ½)
  1≰½ = toWitnessFalse {a? = 1ℚ ≤? ½} _

  -- Layer 1's own comparison separates a dead process from `v₁`: `Adequacy`
  -- turns both context runs into direct runs, and the direct run of a dead
  -- process carries no mass at all.
  no-agree : ¬ Agreeˢ Ωᴵ deadᴼ v₁
  no-agree ag = 1≰½ (≤-trans (proj₂ v₁-mass)
                       (≤-trans (proj₂ reach)
                         (≤-trans (proj₂ split) (≤-reflexive zsum))))
    where
    d = ask tt out

    reach = proj₂ (adequacy Ωᴵ v₁ d) (indᵇ true) (indᵇ-nn true) (proj₁ v₁-mass)
    split = proj₂ (ag d ½ 0<½) true (proj₁ reach)

    zeroᵈ : Zero (ctxRunˢ Ωᴵ d deadᴼ)
    zeroᵈ = zero-resp-≈ₚ (≈ₚ-sym _ _ (adequacy Ωᴵ deadᴼ d))
                         (dead-run Ωᴵ deadᴼ (dead-deadᴹ ⟦ unitᴵ ⟧ᴵ ⟦ Ωᴵ ⟧ᴵ) d)

    zsum = trans (cong (ℚ._+ ½) (zeroᵈ (indᵇ true) (indᵇ-nn true) (proj₁ split)))
                 (+-identityˡ ½)

------------------------------------------------------------------------
-- The refutations

-- Every object implicit is passed, for the reason `Grounding.Dead`'s header
-- gives: the terms below are `𝒢ₚ`-composites, and an inferred object at one of
-- them is a `Machine (A⁺ + B⁻) (A⁻ + B⁺)` inversion.
module _ (𝟘 : Iface) (ι : (B : Iface) → Proc B (𝟘 ⊗ᴵ B)) where

  private
    module T = TrivialGrade 𝟘 ι

    𝕀 = ⟦ unitᴵ ⟧ᴵ
    𝕆 = ⟦ Ωᴵ ⟧ᴵ
    𝔽 = ⟦ 𝟘 ⊗ᴵ Ωᴵ ⟧ᴵ

    s₀ : Proc 𝟘 𝟘
    s₀ = deadᴹ ⟦ 𝟘 ⟧ᴵ ⟦ 𝟘 ⟧ᴵ

    subs₀ : 𝒢ₚ 0ℓ [ 𝔽 , 𝔽 ]
    subs₀ = E.sub {⟦ 𝟘 ⟧ᴵ} {⟦ 𝟘 ⟧ᴵ} {𝕆} s₀

    plug : (w : Proc unitᴵ Ωᴵ) → 𝒢ₚ 0ℓ [ 𝕀 , 𝔽 ]
    plug w = 𝔾._∘_ {𝕀} {𝕆} {𝔽} (ι Ωᴵ) w

    simplug : (w : Proc unitᴵ Ωᴵ) → 𝒢ₚ 0ℓ [ 𝕀 , 𝔽 ]
    simplug w = 𝔾._∘_ {𝕀} {𝔽} {𝔽} subs₀ (plug w)

    dead-ι : (w : Proc unitᴵ Ωᴵ) → Dead 𝕀 𝕆 w → Dead 𝕀 𝔽 (plug w)
    dead-ι w = dead-∘ʳ 𝕀 𝕆 𝔽 (ι Ωᴵ) w

    dead-sim : (w : Proc unitᴵ Ωᴵ) → Dead 𝕀 𝔽 (simplug w)
    dead-sim w = dead-∘ˡ 𝕀 𝔽 𝔽 subs₀ (plug w)
                         (dead-sub ⟦ 𝟘 ⟧ᴵ ⟦ 𝟘 ⟧ᴵ 𝕆 s₀ (dead-deadᴹ ⟦ 𝟘 ⟧ᴵ ⟦ 𝟘 ⟧ᴵ))

  -- A divergent simulator makes an emulation at the trivial grade hold between
  -- processes layer 1 tells apart, so the collapse to a direct agreement fails.
  no-unit-grade : ¬ T.UnitGrade
  no-unit-grade ug = no-agree (ug Ωᴵ deadᴼ v₁
    (s₀ , dead-≈ℰ 𝕀 𝔽 (plug deadᴼ) (simplug v₁)
            (dead-ι deadᴼ (dead-deadᴹ 𝕀 𝕆)) (dead-sim v₁)))

  -- …and with `IotaBlind` the same simulator identifies all closed processes.
  no-trivial-grade : T.SubBlind → T.IotaBlind → ⊥
  no-trivial-grade sb ib = no-agree (stratIsEnv Ωᴵ deadᴼ v₁ (ib Ωᴵ deadᴼ v₁ ι-agree))
    where
    ι-agree : _≈ℰ_ {𝕀} {𝔽} (plug deadᴼ) (plug v₁)
    ι-agree = ≈ℰ-trans {𝕀} {𝔽} (≈ℰ-sym {𝕀} {𝔽} (sb Ωᴵ s₀ deadᴼ))
                (≈ℰ-trans {𝕀} {𝔽}
                  (dead-≈ℰ 𝕀 𝔽 (simplug deadᴼ) (simplug v₁)
                               (dead-sim deadᴼ) (dead-sim v₁))
                  (sb Ωᴵ s₀ v₁))

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

unitGrade-refuted : ¬ TG.UnitGrade
unitGrade-refuted = no-unit-grade 𝟘ᴳ ιᴳ

subBlind-refuted : ¬ TG.SubBlind
subBlind-refuted sb = no-trivial-grade 𝟘ᴳ ιᴳ sb iotaBlind

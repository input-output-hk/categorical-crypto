{-# OPTIONS --safe --without-K --guardedness #-}

-- The qualitative carry at the intended instance, and the API's acceptance
-- test.
--
-- `UC.Robust` is generic in the base.  The base here is the sealed model
-- (`UC.Model.Bridge.ucBaseᵒ`) and the premise is the INHERITED `_≤UC_` of
-- `UC.Model.Setup`, read into the core's by `UC.Model.Bridge.≤UC⇒≤UCᶜ` — the
-- same one step `UC.Seam.Audit` takes for the budgeted carry.  No second UC
-- metatheory appears: the bridge, then the generic theorem.
--
-- The two acceptance statements are the degenerate and the nontrivial ends of
-- the API: `⊤ᴾ` is robust for every machine with no premise at all, and `∼[_]`
-- is carried at a designated verdict.
--
-- SCOPE: see `UC.Robust`'s header.  Nothing here bounds a probability, so
-- nothing here discharges the monitor-inclusion or error-uniformity obligations
-- of `docs/protocol-implementation-review.md` §§1-2.

open import Data.Unit.Base using (tt)

open import Level using (Level)

open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ; ≤UC⇒≤UCᶜ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Robust as Rob

module CategoricalCrypto.UC.Robust.Model where

open import CategoricalCrypto.UC.Emulation ucBaseᵒ using (Obs)

private module R = Rob ucBaseᵒ

open R public
  using ( SaturatedProperty; holds; saturated; ⊤ᴾ; ∼[_]; Robust; robust-resp-≈ℰ
        ; robust-sub; uc-preserves; uc⁺-preserves )

private variable A B X Y : Channel
                 p : Level

uc-preservesᵒ : (𝔓 : SaturatedProperty p) {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
              → f ≤UC g → Robust 𝔓 g → Robust 𝔓 f
uc-preservesᵒ 𝔓 le = R.uc-preserves 𝔓 (≤UC⇒≤UCᶜ le)

⊤-robust : (f : A ⇒ B) → Robust ⊤ᴾ f
⊤-robust _ _ _ _ = tt

-- If no closing context tells the ideal system apart from a designated
-- verdict, none tells the real one apart either.
verdict-preservedᵒ : (r : Obs) {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
                   → f ≤UC g → Robust ∼[ r ] g → Robust ∼[ r ] f
verdict-preservedᵒ r = uc-preservesᵒ ∼[ r ]

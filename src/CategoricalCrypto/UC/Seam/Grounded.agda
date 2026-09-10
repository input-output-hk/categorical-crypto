{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Grounding`'s statements, discharged at the trivial grade.
--
-- The grade is 𝒢's OWN monoidal unit read back as an interface
-- (`retᴵ 𝔾.unit`), not `unitᴵ`.  The two are the empty interface spelled with
-- two different empty types — `Data.Empty.⊥` against the base's initial object
-- — and `UC.Model.Unit` prices the iso between them at over the perf bar.  At
-- `retᴵ 𝔾.unit` no iso is needed: `T₁ ⟦ retᴵ 𝔾.unit ⟧ᴵ w` IS `id ⊗₁ w` at the
-- unit, so the unitor's naturality and its own iso — two fields of the monoidal
-- record, hence free — are all that is spent.  Nothing here reduces a machine.
--
-- `StratIsEnv` is what `UC.Seam.Grounding`'s header measures at 2400 s and an
-- 8 GiB heap and calls blocked.  That measurement was taken with the grade at
-- `unitᴵ`, where the missing unitor left the equation to the ⊕-trace.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Morphism.Reasoning as MR

open import Data.Unit.Base using (tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ[]-resp)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ; ⟦_⟧ᴼ; retᴵ; ucBaseᴹ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Seam using (ctxRunˢ; strategyEnv)
open import CategoricalCrypto.UC.Seam.Grounding

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounded where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E = Em ucBaseᴹ

open 𝔾.HomReasoning
open E using (≈ℰ-at; ≈ℰ-congˡ; ≈ℰ-trans; ≈⇒≈ℰ; T₁; _∘_; _≈_)
open MR (𝒢ₚ 0ℓ) using (cancelˡ; cancelʳ)

------------------------------------------------------------------------
-- The trivial grade

𝟘ᴳ : Iface
𝟘ᴳ = retᴵ 𝔾.unit

ιᴳ : (B : Iface) → Proc B (𝟘ᴳ ⊗ᴵ B)
ιᴳ B = 𝔾.unitorˡ.to

module TG = TrivialGrade 𝟘ᴳ ιᴳ

iotaBlind : TG.IotaBlind
iotaBlind B u v h =
  ≈ℰ-trans (≈⇒≈ℰ (⟺ (cancel u)))
           (≈ℰ-trans (≈ℰ-congˡ 𝔾.unitorˡ.from h) (≈⇒≈ℰ (cancel v)))
  where
  cancel : (w : Proc unitᴵ B) → (𝔾.unitorˡ.from ∘ (ιᴳ B ∘ w)) ≈ w
  cancel w = cancelˡ 𝔾.unitorˡ.isoʳ

------------------------------------------------------------------------
-- The degenerate ancilla

-- The plugging law both `EnvAsCtx` and `StratIsEnv` are: at the unit ancilla
-- the two wires cancel, by the unitor's naturality and its own iso.
plug-λ : {B : Iface} (t : Proc B Ωᴵ) (w : Proc unitᴵ B)
       → (((t ∘ 𝔾.unitorˡ.from) ∘ T₁ ⟦ 𝟘ᴳ ⟧ᴵ w) ∘ 𝔾.unitorˡ.to) ≈ (t ∘ w)
plug-λ t w = (𝔾.assoc ○ (refl⟩∘⟨ 𝔾.unitorˡ-commute-from) ○ 𝔾.sym-assoc) ⟩∘⟨refl
           ○ cancelʳ 𝔾.unitorˡ.isoʳ

envAsCtx : EnvAsCtx
envAsCtx B d = record
  { anc   = 𝟘ᴳ
  ; test  = strategyEnv B d ∘ 𝔾.unitorˡ.from
  ; close = 𝔾.unitorˡ.to
  ; plugs = toEnvPlugs λ w → toProc≈ (plug-λ (strategyEnv B d) w)
  }

------------------------------------------------------------------------
-- The grounding

-- `plugˢ` is `𝒢`'s composite with the G-record's projection already performed;
-- `Machines.Collapse` supplies both halves of that reading.
plug-run : (B : Iface) (d : Strat (Neg B) (Pos B)) (w : Proc unitᴵ B)
         → ctxRunˢ B d w ≈ₚ ⟦ (strategyEnv B d ∘ w) ⟧ᴼ
plug-run B d w = runᴹ-resp-≈ᴹ (Col.S.⟺ᴹ (Col.collapseᵀ (strategyEnv B d) w)
                               Col.S.○ᴹ Col.compose-raw≈∘ᴳ (strategyEnv B d) w)
                              (ask tt out)

stratIsEnv : StratIsEnv
stratIsEnv B u v h d ε ε>0 =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (plug-run B d u)) (≈ₚ-sym _ _ (plug-run B d v))
            (≈ℰ-at 𝔾.unit (strategyEnv B d ∘ 𝔾.unitorˡ.from) 𝔾.unitorˡ.to
                   (strategyEnv B d ∘_) (plug-λ (strategyEnv B d)) h ε ε>0)

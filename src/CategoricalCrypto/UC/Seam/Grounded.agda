{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Grounding`'s statements, discharged at the trivial grade.
--
-- The grade is the sealed bundle's OWN monoidal unit, not `unitᴵ`.  The two are
-- the empty interface spelled with two different empty types — `Data.Empty.⊥`
-- against the base's initial object — and `UC.Model.Unit` prices the iso
-- between them at over the perf bar.  At `unit` no iso is needed: `T₁ unit w`
-- is `id ⊗₁ w` there (`CurriedTensor.Properties.T₁-⊗`), so the unitor's
-- naturality and its own iso — two fields of the monoidal record, hence free —
-- are all that is spent.  Nothing here reduces a machine.
--
-- `plug-run` is the one place a sealed composite has to be read back as the
-- machine composite it is, and `UC.Model.Seal.unprocᵒ-∘` is what reads it.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗)
import Categories.Morphism.Reasoning as MR

open import Data.Unit.Base using (tt)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ[]-resp)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Model.Bridge
  using (≈ᴳ-at; ≈ᴳ-congˡ; ≈ᴳ-trans; ≈C⇒≈ᴳ; ≈ᵁ⇒≈ᴳ; unit-gradeᵁ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ; procᵒ; unprocᵒ-∘)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (ctxRunˢ; strategyEnv)
open import CategoricalCrypto.UC.Seam.Grounding

import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.UC.Seam.Grounded where

open HomReasoning
open MR ∣machines∣ using (cancelˡ; cancelʳ)

------------------------------------------------------------------------
-- The trivial grade

𝟘ᴳ : Channel
𝟘ᴳ = unit

ιᴳ : (B : Iface) → ifaceᵒ B ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
ιᴳ _ = unitorˡ.to

module TG = TrivialGrade 𝟘ᴳ ιᴳ

iotaBlind : TG.IotaBlind
iotaBlind B u v h =
  ≈ᴳ-trans (≈C⇒≈ᴳ (⟺ (cancel (procᵒ u))))
           (≈ᴳ-trans (≈ᴳ-congˡ unitorˡ.from (≈ᵁ⇒≈ᴳ h)) (≈C⇒≈ᴳ (cancel (procᵒ v))))
  where
  cancel : (w : 𝟘ᵒ ⇒ ifaceᵒ B) → unitorˡ.from ∘ (ιᴳ B ∘ w) ≈ w
  cancel _ = cancelˡ unitorˡ.isoʳ

------------------------------------------------------------------------
-- The degenerate ancilla

-- The plugging law both `EnvAsCtx` and `StratIsEnv` are: at the unit ancilla
-- the two wires cancel, by the unitor's naturality and its own iso.
plug-λ : {B : Iface} (t : ifaceᵒ B ⇒ Ωᵒ) (w : 𝟘ᵒ ⇒ ifaceᵒ B)
       → ((t ∘ unitorˡ.from) ∘ T₁ 𝟘ᴳ w) ∘ unitorˡ.to ≈ t ∘ w
plug-λ t w = ((refl⟩∘⟨ T₁-⊗ 𝔾ᵒ 𝟘ᴳ w) ⟩∘⟨refl)
           ○ (assoc ○ (refl⟩∘⟨ unitorˡ-commute-from) ○ sym-assoc) ⟩∘⟨refl
           ○ cancelʳ unitorˡ.isoʳ

envAsCtx : EnvAsCtx
envAsCtx B d = record
  { anc   = 𝟘ᴳ
  ; test  = procᵒ (strategyEnv B d) ∘ unitorˡ.from
  ; close = unitorˡ.to
  ; plugs = toEnvPlugs λ w → toProc≈ (plug-λ (procᵒ (strategyEnv B d)) w)
  }

------------------------------------------------------------------------
-- The grounding

-- `plugˢ` is `𝒢`'s composite with the G-record's projection already performed;
-- `Machines.Collapse` supplies both halves of that reading, and `unprocᵒ-∘`
-- crosses the seal.
plug-run : (B : Iface) (d : Strat (Neg B) (Pos B)) (w : Proc unitᴵ B)
         → ctxRunˢ B d w ≈ₚ Obs (procᵒ (strategyEnv B d) ∘ procᵒ w)
plug-run B d w =
  runᴹ-resp-≈ᴹ ((Col.S.⟺ᴹ (Col.collapseᵀ e w) Col.S.○ᴹ Col.compose-raw≈∘ᴳ e w)
                Col.S.○ᴹ Col.S.⟺ᴹ (unprocᵒ-∘ e w))
               (ask tt out)
  where e = strategyEnv B d

stratIsEnv : StratIsEnv
stratIsEnv B u v h d ε ε>0 =
  ≈ₚ[]-resp (≈ₚ-sym _ _ (plug-run B d u)) (≈ₚ-sym _ _ (plug-run B d v))
            (≈ᴳ-at 𝟘ᴳ (procᵒ (strategyEnv B d) ∘ unitorˡ.from) unitorˡ.to
                   (procᵒ (strategyEnv B d) ∘_) (plug-λ (procᵒ (strategyEnv B d)))
                   h ε ε>0)

-- …and with that the collapse at the trivial grade rests on `SubBlind` and on
-- nothing else.  Which is where it should rest: `SubBlind` is FALSE as stated
-- — `_≤UC_` quantifies its simulator over a divergent `s` too, and
-- `UC.Seam.Grounding.Dead` is the mechanized half of why — so this is what
-- localizes the defect, rather than a use of it.
unitGrade : TG.SubBlind → TG.UnitGrade
unitGrade blind B u v e =
  stratIsEnv B u v (unit-gradeᵁ (λ s → blind B s v) (iotaBlind B u v) e)

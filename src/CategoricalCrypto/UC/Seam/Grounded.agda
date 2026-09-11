{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Grounding`'s statements at the trivial grade: `IotaBlind`,
-- `EnvAsCtx` and `StratIsEnv` discharged, `UnitGrade` reduced to `SubBlind`,
-- and `SubBlind`'s hypothesis shown to say what it is meant to say.
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

open import Data.Bool.Base using (true)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Unit.Base using (tt)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (_≼ₚ[_]_; ≈ₚ[]-resp)
open import ProbabilisticLogic.Dp.Mass
  using (ASTotal; Total; astotal-≼ᵐ; total-dominated; total-resp-≼ₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Model.Bridge
  using (≈ᴳ-at; ≈ᴳ-congˡ; ≈ᴳ-trans; ≈C⇒≈ᴳ; ≈ᵁ⇒≈ᴳ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp; ∼ᴼ-resp)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ; procᵒ; unprocᵒ-∘)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (ctxRunˢ; runˢ; strategyEnv)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Grounding
open import CategoricalCrypto.UC.Seam.Grounding.Dead
  using (Massedᵒ; massedᵒ-∘ˡ; massedᵒ-∘ʳ; massedᵒ-obs; massedᵒ-point; massedᵒ-sub; pointᵒ)

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
plug-λ : {X : Channel} (t : X ⇒ Ωᵒ) (w : 𝟘ᵒ ⇒ X)
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

------------------------------------------------------------------------
-- The collapse at the trivial grade

-- `_≤UC_` quantifies its simulator over a DIVERGENT `s` as well, so blindness
-- is not free: `UC.Seam.Grounding.Dead` shows a never-starting simulator makes
-- the ideal invisible, and a process observing nothing emulates everything.
-- What rules that out is not a restriction on the simulator but the real
-- process's own totality, and the step that turns the one into the other is
-- the squeeze below.
--
-- Read at one embedded strategy the emulation is a two-sided ε-domination
-- between `u`'s run and the simulated ideal's observation.  `u`'s run carries
-- verdict mass one EXACTLY (`TotalRun`, a finite budget), the observation
-- carries at most one for free, and `Dp.Mass.total-dominated` squeezes: the
-- observation's mass is within ε of one, at every ε.  That is `SimTotal` — the
-- simulator's initialization terminates almost surely — which is all
-- `SubBlind` asks.
--
-- `TotalRun v` is not consumed here.  It is part of the statement because the
-- consumer's pair is symmetric and `Protocol.Machine.Total` discharges both by
-- name; the asymmetry is real (only the REAL side anchors the scale).
unitGrade : TG.SubBlind → TG.UnitGrade
unitGrade blind B u v tu _ e =
  stratIsEnv B u v (iotaBlind B u v (≈ᵁ-trans em (blind B s v simTotal)))
  where
  s : 𝟘ᴳ ⇒ 𝟘ᴳ
  s = proj₁ (e id)

  em : ιᴳ B ∘ procᵒ u ≈ᵁ sub s ∘ (ιᴳ B ∘ procᵒ v)
  em = ≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ (ιᴳ B ∘ procᵒ u)))) (proj₂ (e id))

  simTotal : TG.SimTotal B s v
  simTotal d t factor = total-dominated (ctxRunˢ B d u) _ total near
    where
    -- `Adequacy` moves `u`'s totality onto the observation the strategy makes.
    total : Total (ctxRunˢ B d u)
    total = total-resp-≼ₚ (runˢ B u d) (ctxRunˢ B d u) (proj₂ (adequacy B u d)) (tu d)

    read : ctxRunˢ B d u ≈ₚ Obs (t ∘ (ιᴳ B ∘ procᵒ u))
    read = ≈ₚ-trans _ _ _ (plug-run B d u)
                          (obs-resp (⟺ (sym-assoc ○ (fromProc≈ factor ⟩∘⟨refl))))

    near : (ε : ℚ) → 0ℚ ℚ.< ε
         → ctxRunˢ B d u ≼ₚ[ ε ] Obs (t ∘ (sub s ∘ (ιᴳ B ∘ procᵒ v)))
    near ε ε>0 = proj₁ (∼ᴼ-resp (≈ₚ-sym _ _ read) (≈ₚ-refl _)
      (≈ᴳ-at 𝟘ᴳ (t ∘ unitorˡ.from) unitorˡ.to (t ∘_) (plug-λ t) (≈ᵁ⇒≈ᴳ em)) ε ε>0)

------------------------------------------------------------------------
-- The residue

-- `SubBlind` itself is not discharged.  What is landed is that its hypothesis
-- says what it is meant to say: `SimTotal` is exactly "the simulator's own
-- initialization terminates almost surely", because a trivial-grade scalar
-- reaches a closed observation only through that initialization
-- (`Grounding.Dead`'s propagation, read back from the observation's mass to
-- the point's).
--
-- What remains is the converse traffic, at the machine layer and not in the
-- ε-arithmetic: `Dp.Mass.astotal-bind` already says an almost surely
-- terminating PREFIX is invisible to an ε-closed comparison; what is missing
-- is that a scalar buried in a `𝒢`-trace nest IS such a prefix of the
-- composite's run.  A plain simulation cannot say it — `Machines.Sim`'s
-- generator equates the two points exactly — so the step wants a lax one,
-- with its own congruence through `∘ᴹ`, `⊗ᵉ` and the trace.
simTotal⇒point : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (v : Proc unitᴵ B)
               → TG.SimTotal B s v → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
simTotal⇒point B s v st =
  astotal-≼ᵐ _ _ (massedᵒ-obs u _ massed)
                 (st (out true) t (toProc≈ (cancelʳ unitorˡ.isoʳ)))
  where
  t : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
  t = procᵒ (strategyEnv B (out true)) ∘ unitorˡ.from

  u : 𝟘ᵒ ⇒ Ωᵒ
  u = t ∘ (sub s ∘ (ιᴳ B ∘ procᵒ v))

  massed : Massedᵒ 𝟘ᵒ Ωᵒ u (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
  massed = massedᵒ-∘ʳ _ _ _ t _ _
             (massedᵒ-∘ˡ _ _ _ (sub s) (ιᴳ B ∘ procᵒ v) _
               (massedᵒ-sub 𝟘ᴳ 𝟘ᴳ (ifaceᵒ B) s _ (massedᵒ-point 𝟘ᴳ 𝟘ᴳ s)))

{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Seam.Grounding`'s statements at the trivial grade, all discharged:
-- `IotaBlind`, `EnvAsCtx`, `StratIsEnv`, `SubBlind`, and with them `UnitGrade`.
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
open import CategoricalCrypto.UC.Machine using (Proc; ⊤ᵛ)
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
open import CategoricalCrypto.UC.Seam.Grounding.Prefix
open import CategoricalCrypto.UC.Seam.Slide using (slide⊗)

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

-- A closed protocol image, as the UC layer sees it: this is the shape
-- `UC.Asymptotic._≤UC^ω_` compares, and everything downstream of the collapse
-- is stated at it.
closedᵒ : {B : Iface} → Proc unitᴵ B → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
closedᵒ {B} w = ιᴳ B ∘ procᵒ w

-- …and an OPEN one, whose domain is the port the component below it answers on
-- (`UC.Factor`, where the two are the factors of a closed two-stage system).
stageᵒ : {A B : Iface} → Proc A B → ifaceᵒ A ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
stageᵒ {B = B} g = ιᴳ B ∘ procᵒ g

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
-- the two wires cancel, by the unitor's naturality and its own iso.  Nothing
-- in it looks at the plugged morphism's domain, so it is stated at any — which
-- is what `UC.Seam.Audit.Context.plug-runᵍ` needs, where the process below the
-- ancilla is OPEN and its resource is plugged after the fact.
plug-λ : {D X : Channel} (t : X ⇒ Ωᵒ) (w : D ⇒ X)
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
            (≈ᴳ-at 𝟘ᴳ (envᵒ ∘ unitorˡ.from) unitorˡ.to (envᵒ ∘_) (plug-λ envᵒ)
                   h ε ε>0)
  where envᵒ = procᵒ (strategyEnv B d)

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
emSimTotal : (B : Iface) (u v : Proc unitᴵ B) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) → TotalRun B u
           → closedᵒ u ≈ᵁ sub s ∘ closedᵒ v → TG.SimTotal B s v
emSimTotal B u v s tu em d t factor = total-dominated (ctxRunˢ B d u) _ total near
  where
  -- `Adequacy` moves `u`'s totality onto the observation the strategy makes.
  total : Total (ctxRunˢ B d u)
  total = total-resp-≼ₚ (runˢ B u d) (ctxRunˢ B d u) (proj₂ (adequacy B u d)) (tu d)

  read : ctxRunˢ B d u ≈ₚ Obs (t ∘ closedᵒ u)
  read = ≈ₚ-trans _ _ _ (plug-run B d u)
                        (obs-resp (⟺ (sym-assoc ○ (fromProc≈ factor ⟩∘⟨refl))))

  near : (ε : ℚ) → 0ℚ ℚ.< ε
       → ctxRunˢ B d u ≼ₚ[ ε ] Obs (t ∘ (sub s ∘ closedᵒ v))
  near ε ε>0 = proj₁ (∼ᴼ-resp (≈ₚ-sym _ _ read) (≈ₚ-refl _)
    (≈ᴳ-at 𝟘ᴳ (t ∘ unitorˡ.from) unitorˡ.to (t ∘_) (plug-λ t) (≈ᵁ⇒≈ᴳ em)) ε ε>0)

-- The collapse itself, stopping one step short of `Agreeˢ`: the simulator is
-- removed and what is left is the direct `≈ᵁ` agreement, which is an
-- ε-QUANTIFIED CONTEXTUAL statement.  `stratIsEnv ∘ iotaBlind` is the last
-- step; the asymptotic family premise stops here instead and keeps the ε
-- (`UC.Asymptotic.Family.uc-≈ᶠ[_]`).
subBlind⇒emul : TG.SubBlind → (B : Iface) (u v : Proc unitᴵ B) → TotalRun B u
              → closedᵒ u ≤UC closedᵒ v → closedᵒ u ≈ᵁ closedᵒ v
subBlind⇒emul blind B u v tu e = ≈ᵁ-trans em (blind B s v (emSimTotal B u v s tu em))
  where
  s : 𝟘ᴳ ⇒ 𝟘ᴳ
  s = proj₁ (e id)

  em : closedᵒ u ≈ᵁ sub s ∘ closedᵒ v
  em = ≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ (closedᵒ u)))) (proj₂ (e id))

subBlind⇒unitGrade : TG.SubBlind → TG.UnitGrade
subBlind⇒unitGrade blind B u v tu _ e =
  stratIsEnv B u v (iotaBlind B u v (subBlind⇒emul blind B u v tu e))

------------------------------------------------------------------------
-- Blindness

-- `SimTotal` says what it is meant to say: "the simulator's own initialization
-- terminates almost surely", because a trivial-grade scalar reaches a closed
-- observation only through that initialization (`Grounding.Dead`'s
-- propagation, read back from the observation's mass to the point's).
simTotal⇒point : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (v : Proc unitᴵ B)
               → TG.SimTotal B s v → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
simTotal⇒point B s v st =
  astotal-≼ᵐ _ _ (massedᵒ-obs u _ massed)
                 (st (out true) t (toProc≈ (cancelʳ unitorˡ.isoʳ)))
  where
  t : T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ
  t = procᵒ (strategyEnv B (out true)) ∘ unitorˡ.from

  u : 𝟘ᵒ ⇒ Ωᵒ
  u = t ∘ (sub s ∘ closedᵒ v)

  massed : Massedᵒ 𝟘ᵒ Ωᵒ u (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
  massed = massedᵒ-∘ʳ _ _ _ t _ _
             (massedᵒ-∘ˡ _ _ _ (sub s) (closedᵒ v) _
               (massedᵒ-sub 𝟘ᴳ 𝟘ᴳ (ifaceᵒ B) s _ (massedᵒ-point 𝟘ᴳ 𝟘ᴳ s)))

-- …hence the simulator's initialization is almost surely total off the REAL
-- side's totality alone, which is the hypothesis the budgeted route's
-- prefix-tolerant extraction asks for (`UC.Asymptotic.Audit.uc-audit-boundedᵖ`).
simAstotal : (B : Iface) (u v : Proc unitᴵ B) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) → TotalRun B u
           → closedᵒ u ≈ᵁ sub s ∘ closedᵒ v → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
simAstotal B u v s tu em = simTotal⇒point B s v (emSimTotal B u v s tu em)

-- The whole of what a trivial-grade simulator contributes to a context: its
-- own initialization, in front of whatever that context observes.  A
-- trivial-grade scalar carries no message, so it is the identity except for
-- that point (`Grounding.Prefix.scalar-blindᵒ`), and `sub` and the ancilla keep
-- it a prefix.  The experiment is read in the ∀-ancilla/test/closure form
-- `_≈ℰᶜ_`, where the simulator is the single factor `id ⊗₁ sub s` between the
-- test and everything below it — `k` being that everything, which is why
-- nothing about the process it acts on is asked for here.
subPrefixedˢ : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (Y : Channel)
               (t : Y ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ) (k : 𝟘ᵒ ⇒ Y ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B))
             → Prefixedᵒ 𝟘ᵒ Ωᵒ (t ∘ id ⊗₁ sub s ∘ k) (t ∘ k) (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
subPrefixedˢ B s Y t k =
  prefixedᵒ-resp-≈ 𝟘ᵒ Ωᵒ _ _ _ _ σ Equiv.refl (refl⟩∘⟨ identityˡ)
    (prefixedᵒ-∘ˡ 𝟘ᵒ (Y ⊗₀ Bᵍ) Ωᵒ t _ _ σ
      (prefixedᵒ-∘ʳ 𝟘ᵒ (Y ⊗₀ Bᵍ) (Y ⊗₀ Bᵍ) k (id ⊗₁ sub s) id σ ancilla))
  where
  σ : Dₚ ⊤ᵛ
  σ = pointᵒ 𝟘ᴳ 𝟘ᴳ s

  Bᵍ : Channel
  Bᵍ = T₀ 𝟘ᴳ (ifaceᵒ B)

  -- The simulator acts on the grade alone, which is where it is blind.
  blindˢ : Prefixedᵒ Bᵍ Bᵍ (sub s) id σ
  blindˢ = prefixedᵒ-resp-≈ Bᵍ Bᵍ (sub s) (sub s) (sub id) id σ
             Equiv.refl sub-identity
             (prefixedᵒ-sub 𝟘ᴳ 𝟘ᴳ (ifaceᵒ B) s id σ (scalar-blindᵒ s))

  ancilla : Prefixedᵒ (Y ⊗₀ Bᵍ) (Y ⊗₀ Bᵍ) (id ⊗₁ sub s) id σ
  ancilla = prefixedᵒ-resp-≈ (Y ⊗₀ Bᵍ) (Y ⊗₀ Bᵍ)
              (id ⊗₁ sub s) (id ⊗₁ sub s) (id ⊗₁ id) id σ
              Equiv.refl ⊗.identity
              (prefixedᵒ-⊗ʳ Y Y Bᵍ Bᵍ id (sub s) id σ blindˢ)

-- …read where the simulator sits on the PROCESS rather than on the context,
-- which is the factorization `SubBlind` compares.
subPrefixed : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (v : Proc unitᴵ B) (Y : Channel)
              (t : Y ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ) (m : 𝟘ᵒ ⇒ Y ⊗₀ 𝟘ᵒ)
            → Prefixedᵒ 𝟘ᵒ Ωᵒ (t ∘ id ⊗₁ (sub s ∘ closedᵒ v) ∘ m)
                              (t ∘ id ⊗₁ closedᵒ v ∘ m) (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
subPrefixed B s v Y t m = prefixedᵒ-resp-≈ 𝟘ᵒ Ωᵒ _ _ _ _ (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
  (refl⟩∘⟨ (sym-assoc ○ (⟺ split ⟩∘⟨refl))) Equiv.refl
  (subPrefixedˢ B s Y t (id ⊗₁ wire ∘ m))
  where
  wire : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
  wire = closedᵒ v

  split = slide⊗ Y (sub s) wire

-- …and an initialization that terminates almost surely is invisible:
-- `Dp.Mass.astotal-bind` removes it from the observation.
subBlind : TG.SubBlind
subBlind B s v st = ≈ℰᶜ⇒≈ᵁ λ Y t m →
  ∼ᴼ-resp (obs-resp sym-assoc) (obs-resp sym-assoc)
          (prefixedᵒ-obs _ _ _ (simTotal⇒point B s v st) (subPrefixed B s v Y t m))

-- …so the unit-grade specialization is a closed theorem.
unitGrade : TG.UnitGrade
unitGrade = subBlind⇒unitGrade subBlind

-- …and so is the step before it, which is the one the asymptotic family premise
-- consumes: no `Agreeˢ`, and the ε still quantified rather than spent.
emulAgreeᵁ : (B : Iface) (u v : Proc unitᴵ B) → TotalRun B u
           → closedᵒ u ≤UC closedᵒ v → closedᵒ u ≈ᵁ closedᵒ v
emulAgreeᵁ = subBlind⇒emul subBlind

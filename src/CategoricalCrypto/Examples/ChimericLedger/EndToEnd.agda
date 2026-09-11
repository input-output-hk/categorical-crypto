{-# OPTIONS --safe --without-K --guardedness #-}

-- The end-to-end asymptotic UC-to-POV theorem for the chimeric ledger.
--
-- `ledger-uc-to-pov` starts at the PROVED ideal birthday bound
-- (`ChimericLedger.Birthday.target`, read through the designated monitor by
-- `ChimericLedger.Trajectory`) and a genuine UC-emulation premise between the
-- real and ideal machine FAMILIES, and concludes a real-side bound on the
-- state trajectory — preservation of value — modulo negligible slack at every
-- polynomial allowance.  `ledger-pov-negligible` reads the same conclusion as
-- one number: at every polynomial allowance the real failure probability is
-- negligible, the birthday bound and the slack together.
--
-- What the theorem assumes, and nothing else:
--
--   `SerInj`        the birthday theorem's own injective-serialization
--                   hypothesis, per level (`Tx` depends on the hash width, so
--                   a single `ser` cannot be typed)
--   `R ≤UC^ω …`     the emulation, in the INHERITED preorder — a simulator per
--                   dummy adversary — never a direct `Agreeˢ`
--   `TotalRun`      on the real side; the ideal side's is proved
--                   (`ChimericLedger.Total`).  Not decoration: with the real
--                   side divergent every ideal is emulated, by a simulator
--                   that never starts
--   `TruthfulAudit` the real implementation's audit answers report its own
--                   state.  UC identifies no internal trajectory, so this is
--                   irreducibly about the implementation; for a ledger image
--                   it is `Trajectory.monitor-complete` and `ideal-truthful`
--                   supplies it
--
-- The costs are explicit and both appear in the conclusion: the audit
-- instrumentation doubles the allowance (`asks≤-audited`), and the slack is
-- `2⁻ⁿ`, negligible and positive (a carry off an ε-quantified agreement has no
-- zero instance to take).
--
-- `ledger-audit-carry` is the GRADED route beside it, where the simulator's
-- own query cost is charged (`simCost`), and it stops at an `AuditBound`.
-- `ledger-uc-to-pov-simCost` is that cost reaching a PROBABILITY: the premise
-- is a BUDGETED emulation and the allowance the birthday bound is read at is
-- `simCost (q + q) (cs n)`, the audit instrumentation's doubling composed with
-- the simulator's own rescaling.  It goes through `UC.Seam.Audit.Prefix`'s
-- prefix-tolerant class rather than through the trivial-grade collapse, which
-- is what `docs/end-to-end.md`'s closed obstruction owed.
--
-- The two are not ordered, and which way is worth saying: a budgeted emulation
-- IS an emulation (`UC.Audit.≤UC[]⇒≤UC` then `UC.Model.Bridge.≤UCᶜ⇒≤UC`), so
-- `ledger-uc-to-pov` applies wherever the budgeted theorem does and gives the
-- SHARPER bound — at the trivial grade the simulator costs the ideal side
-- nothing.  What the budgeted statement adds is not a better number but the
-- accounting: it is the route that survives a simulator whose queries have to
-- be paid for, and it is the example's witness that the prefix extraction
-- composes end to end.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-+; poly-const; poly-⊔)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2)
open import ProbabilisticLogic.Dp using (_≈ₚ_; ≈ₚ-refl; ≈ₚ-sym; ≈ₚ-trans)
open import ProbabilisticLogic.Dp.Advantage using (_≼ₚ[_]_)
open import ProbabilisticLogic.Dp.Mass
  using (ASTotal; Total; total-dominated; total-resp-≼ₚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface using (Iface; Neg; Pos; unitᴵ)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-+)
open import CategoricalCrypto.UC.Approximate.Decay
  using (0<inv-pow-2; negligible-slack)
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Asymptotic.Audit
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Model.Bridge using (≈ᴳ-at; ≈ℰᶜ⇒≈ᵁ; ≈ᵁ⇒≈ᴳ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; obs-resp; ∼ᴼ-resp)
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
  using (_≈negl_; Bad; SaturatedBoundedᴺ; SaturatedHitᴺ; Systems)
open import CategoricalCrypto.UC.Seam.Audit
  using (AuditBound; absorb; emulate; sim; simCost)
open import CategoricalCrypto.UC.Seam using (Agreeˢ; ctxRunˢ; runˢ)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Grounded
  using (plug-λ; plug-run; simTotal⇒point; 𝟘ᴳ; ιᴳ)
open import CategoricalCrypto.UC.Seam.Grounding using (fromProc≈; module TrivialGrade)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)

import CategoricalCrypto.Examples.ChimericLedger.Audit as Aud

module CategoricalCrypto.Examples.ChimericLedger.EndToEnd
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

open HomReasoning

module Ad (n : ℕ) = Aud n (ser n)

private
  module TG = TrivialGrade 𝟘ᴳ ιᴳ

  Strats : (n : ℕ) → Set
  Strats n = Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))

-- The slack the carries spend: `2⁻ⁿ`, positive at every level and negligible.
ν : ℕ → ℚ
ν = inv-pow-2

νNegligible : Negligible ν
νNegligible = negligible-slack λ _ → ≤-refl

------------------------------------------------------------------------
-- The theorem

-- For every polynomial allowance `p` there is a negligible `νₚ` such that no
-- strategy of budget `p n` moves the real system's total value away from
-- genesis with probability above `εbirthday` at the audit-adjusted allowance
-- plus `νₚ n`.
ledger-uc-to-pov :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
ledger-uc-to-pov a V si R badR tR em truthful =
  saturatedHitᴺ-from-monitor {ε = εᴸ} {P = R} {Bad = badR} {bad = monitorᴸ a V}
    (λ _ q → q ℕ.+ q) (auditedᴸ a V) (λ _ Pp → poly-+ Pp Pp) (auditedᴸ-asks a V)
    truthful real
  where
  agree : (n : ℕ) → Agreeˢ (LedgerIf^ω n) (morphism (R n)) (morphism (Ideal a V n))
  agree = uc-agree {R = R} {I = Ideal a V} tR (idealTotal a V) em

  near : R ≈negl Ideal a V
  near = uc-≈negl {ν = ν} {R = R} {I = Ideal a V} 0<inv-pow-2 νNegligible agree

  ideal : SaturatedBoundedᴺ (Ideal a V) (monitorᴸ a V) εᴸ
  ideal = boundedᴺ {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V} (ideal-bounded a V si)

  real : SaturatedBoundedᴺ R (monitorᴸ a V) εᴸ
  real = uc-preservesᴺ {R = R} {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V}
           (monitorᴸ-preserving a V) near ideal

-- …read as one number: the real system's preservation-of-value failure is
-- negligible in the security parameter at every polynomial allowance.
ledger-pov-negligible :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
ledger-pov-negligible a V si R badR tR em truthful p Pp =
  let νₚ , neg , bnd = ledger-uc-to-pov a V si R badR tR em truthful p Pp
  in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
   , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
   , bnd

-- The same ideal bound crossing a BUDGETED emulation: the real side reads the
-- absorbed event class and the simulator's own queries are charged there.
ledger-audit-carry :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (cs : ℕ → ℕ)
    (em : R ≤UC^ω[ cs ] Ideal a V) (n : ℕ)
  → AuditBound (ιᴳ (LedgerIf^ω n) ∘ procᵒ (morphism (R n)))
      (absorb (sim (em n)) (cs n) (Ad.auditEvent n inputConsuming (gen a V n)))
      (λ q → εᴸ n (simCost q (cs n)) ℚ.+ ν n)
ledger-audit-carry a V si R cs em =
  uc-audit-carry {ε = εᴸ} {ν = ν} em (monitorᴸ a V)
    (λ n → Ad.audit-target n (h₀ n) (si n) a V) 0<inv-pow-2

------------------------------------------------------------------------
-- The budgeted route

-- What the prefix-tolerant extraction asks of the simulator's initialization,
-- off the REAL family's own totality: `emSimTotal` is the `simTotal` block of
-- `UC.Seam.Grounded.subBlind⇒unitGrade` verbatim, which that proof keeps in a
-- `where` and so cannot be reused, and `simAstotal` is `simTotal⇒point` on top
-- of it.  BOTH BELONG IN `UC.Seam.Grounded` (rule 27) and sit here only
-- because this branch's edit scope is `Examples/ChimericLedger/`; the
-- relocation is filed in `QUALITY-REVIEW.md`.  The budgeted emulation's own
-- relation is the core's `_≈ℰ_`, which at a graded codomain IS `_≈ᵁ_`.
private
  emSimTotal : (B : Iface) (u v : Proc unitᴵ B) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) → TotalRun B u
             → ιᴳ B ∘ procᵒ u ≈ᵁ sub s ∘ (ιᴳ B ∘ procᵒ v) → TG.SimTotal B s v
  emSimTotal B u v s tu em d t factor = total-dominated (ctxRunˢ B d u) _ total near
    where
    total : Total (ctxRunˢ B d u)
    total = total-resp-≼ₚ (runˢ B u d) (ctxRunˢ B d u) (proj₂ (adequacy B u d)) (tu d)

    read : ctxRunˢ B d u ≈ₚ Obs (t ∘ (ιᴳ B ∘ procᵒ u))
    read = ≈ₚ-trans _ _ _ (plug-run B d u)
                          (obs-resp (⟺ (sym-assoc ○ (fromProc≈ factor ⟩∘⟨refl))))

    near : (ε : ℚ) → 0ℚ ℚ.< ε
         → ctxRunˢ B d u ≼ₚ[ ε ] Obs (t ∘ (sub s ∘ (ιᴳ B ∘ procᵒ v)))
    near ε ε>0 = proj₁ (∼ᴼ-resp (≈ₚ-sym _ _ read) (≈ₚ-refl _)
      (≈ᴳ-at 𝟘ᴳ (t ∘ unitorˡ.from) unitorˡ.to (t ∘_) (plug-λ t) (≈ᵁ⇒≈ᴳ em)) ε ε>0)

  simAstotal : (R I : Systems LedgerIf^ω) (cs : ℕ → ℕ)
             → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
             → (em : R ≤UC^ω[ cs ] I) (n : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim (em n)))
  simAstotal R I cs tR em n =
    simTotal⇒point (LedgerIf^ω n) (sim (em n)) (morphism (I n))
      (emSimTotal (LedgerIf^ω n) (morphism (R n)) (morphism (I n)) (sim (em n))
                  (tR n) (≈ℰᶜ⇒≈ᵁ (emulate (em n))))

-- `ledger-uc-to-pov` off a BUDGETED emulation: the same trajectory
-- conclusion, the birthday bound read at the allowance the audit
-- instrumentation and the simulator together cost, plus the carry's slack.
-- The premise list is the pointwise theorem's with `_≤UC^ω_` replaced by
-- `_≤UC^ω[ cs ]_`; nothing is added.
ledger-uc-to-pov-simCost :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R) (cs : ℕ → ℕ)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω[ cs ] Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (simCost (q ℕ.+ q) (cs n)) ℚ.+ ν n)
ledger-uc-to-pov-simCost a V si R badR cs tR em truthful =
  saturatedHitᴺ-from-monitor {ε = εᶜ} {P = R} {Bad = badR} {bad = monitorᴸ a V}
    (λ _ q → q ℕ.+ q) (auditedᴸ a V) (λ _ Pp → poly-+ Pp Pp) (auditedᴸ-asks a V)
    truthful real
  where
  εᶜ : ℕ → ℕ → ℚ
  εᶜ n q = εᴸ n (simCost q (cs n)) ℚ.+ ν n

  real : SaturatedBoundedᴺ R (monitorᴸ a V) εᶜ
  real = boundedᴺ {I = R} {ε = εᶜ} {bad = monitorᴸ a V}
           (uc-audit-boundedᵖ {ε = εᴸ} {ν = ν} em (monitorᴸ a V)
                              (simAstotal R (Ideal a V) cs tR em)
                              (monitorᴸ-preserving a V) (ideal-bounded a V si)
                              0<inv-pow-2)

-- …read as one number, as `ledger-pov-negligible` reads the pointwise theorem.
-- The simulator's budget has to be polynomial for that number to be
-- negligible, and that is the only hypothesis this corollary adds: a
-- superpolynomial simulator magnifies the allowance out of the birthday
-- bound's negligible range.
ledger-pov-simCost-negligible :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
    (cs : ℕ → ℕ) → Poly cs
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω[ cs ] Ideal a V
  → TruthfulAudit a V R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
ledger-pov-simCost-negligible a V si R badR cs Pcs tR em truthful p Pp =
  let νₚ , neg , bnd = ledger-uc-to-pov-simCost a V si R badR cs tR em truthful p Pp
  in (λ n → (εᴸ n (simCost (p n ℕ.+ p n) (cs n)) ℚ.+ ν n) ℚ.+ νₚ n)
   , Negligible-+
       (Negligible-+
         (εᴸ-negligible (λ n → simCost (p n ℕ.+ p n) (cs n))
                        (poly-* (poly-+ Pp Pp) (poly-⊔ Pcs (poly-const 1))))
         νNegligible)
       neg
   , bnd

{-# OPTIONS --safe --without-K --guardedness #-}

-- The ledger's properties carried across a UC emulation, as three distinct
-- results (`docs/end-to-end.md` §6):
--   `preserves-value-transfer`  observable audit safety (`PreservesValue`):
--     assumes `SerInj` and an emulation; bounds a discrepant audit ANSWER;
--   `ledger-uc-to-state`  state-event safety (`StateSafe`) for a supplied
--     test `badR`: also assumes `TruthfulAudit`, at a doubled allowance.  At
--     the ledger's own `badTotal` it is conservation of the internal total,
--     and there `TruthfulAudit` is a theorem (`ledger-conserves-value-from-hash`);
--   `ideal-spends-genesis`  responsiveness: assumes nothing, and neither
--     safety result implies it (`Mute`).
-- `Liar` pins what the first does not say; the replay attack refutes
-- `PreservesValue` for the chimeric family.

open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Bool.Base
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl) renaming (+-identityʳ to +-identityʳᴺ)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties using (+-identityʳ; positive⁻¹; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine.StateEvent.Adequacy
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Family.Emulation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound renaming (QB to QBᴹ)
open import CategoricalCrypto.UC.Quantitative.EventLift
open import CategoricalCrypto.UC.Seam.Grounded

import CategoricalCrypto.Examples.ChimericLedger.Replay as Replay

module CategoricalCrypto.Examples.ChimericLedger.Transfer
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Property ser
open Compose

------------------------------------------------------------------------
-- Claim 1: observable audit safety
------------------------------------------------------------------------

-- The ideal bound is read at the context's own cap `p n`, the comparison at
-- `p n + 1` only because `≈ᶠ-runs` takes a positive cap; neither is read at a
-- certificate of the compiled test: the flag is an internal port of the
-- monitored process, so what a strategy extracted from it spends on the
-- ledger is the honest allowance alone (`docs/event-bounds-in-setup.md` §B).
-- No schedule monotonicity is spent.
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R
preserves-value-transfer a V R si (ε , neg , h) p Pp =
    (λ n → ε n (p n ℕ.+ 1))
  , neg (λ n → p n ℕ.+ 1) (poly-+ Pp (poly-const 1))
  , λ n → hitsᴸ (genesisTotal V) R n (p n) λ d ad →
      upper-≈[] (≈ᶠ-runs ε h n (p n ℕ.+ 1 , m≤n+m 1 (p n))
                         (auditWatch (genesisTotal V) n d)
                         (asks≤-watch _ false d (asks≤-mono (m≤m+n (p n) 1) d ad)))
                (upper-run (Ideal a V n) (auditWatch (genesisTotal V) n d)
                           (ideal-bounded a V si n (p n) d ad))

-- The UC layer sees only the CLOSED system, in which the hash is invisible;
-- `ledger-factor` re-reads it as `ledgerᵒ ∙ hashᵒ hash` through the exposed
-- port `hashPortᵒ`.  It gives no nontrivial simulator
-- (`docs/ledger-factoring.md`).

HashIf^ω : ℕ → Iface
HashIf^ω = AtLevel.HashIf

hashPortᵒ : ℕ → Channel
hashPortᵒ n = ifaceᵒ (HashIf^ω n)

oracle^ω : Systems HashIf^ω
oracle^ω = AtLevel.oracle

hashᵒ : Systems HashIf^ω → (n : ℕ) → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (hashPortᵒ n)
hashᵒ hash n = closedᵒ (morphism (hash n))

ledgerᵒ : (n : ℕ) (vr : Variant) (s : Ledger.LState n)
        → hashPortᵒ n ⇒ T₀ 𝟘ᴳ (ifaceᵒ (LedgerIf^ω n))
ledgerᵒ n vr s = stageᵒ (morphism (AtLevel.ledger n vr s))

ledger-factor : (hash : Systems HashIf^ω) (vr : Variant) (n : ℕ) (s : Ledger.LState n)
              → closedᵒ (morphism (AtLevel.Sysᴴ n (hash n) vr s))
                ≈ sub λ⇒ ∘ (ledgerᵒ n vr s ∙ hashᵒ hash n)
ledger-factor hash vr n s = factorᵖ (AtLevel.ledger n vr s) (hash n)

Realᴴ : Systems HashIf^ω → Variant → ((n : ℕ) → Ledger.LState n) → Systems LedgerIf^ω
Realᴴ hash vr s n = AtLevel.Sysᴴ n (hash n) vr (s n)

-- What the lift costs the premise's schedule: the ledger goes into the test at
-- its own rate `1`, then the unit regrading goes in at rate `1` as well, so the
-- allowance is substituted twice and both substitutions are EXACT.
εᴴ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᴴ ε n q = ε n (scale (scale q 1⁺) 1⁺)

εᴴ-negligible : (ε : ℕ → ℕ → ℚ) → NegligibleBound ε → NegligibleBound (εᴴ ε)
εᴴ-negligible ε neg =
  NegligibleBound-scale (λ _ → 1⁺) poly⁺-1 (λ n q → ε n (scale q 1⁺))
    (NegligibleBound-scale (λ _ → 1⁺) poly⁺-1 ε neg)

open GradedSubCat gradingᵒ renaming (forget to forgetᴳ)
open HomReasoning

module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n) where

  private
    ledgerᶠ : Homᶠ (ifaceᶠ HashIf^ω) (Δ 𝟘ᴳ) (ifaceᶠ LedgerIf^ω)
    ledgerᶠ n = ledgerᵒ n vr (s n)

    ledgerᶠ-qb : (n : ℕ) → Image forgetᴳ 1⁺ (ledgerᶠ n)
    ledgerᶠ-qb n =
      imageᵒ (pred-sub ≤-refl (pred-∘ pred-λ⇐ (qbᵒ {r = 1⁺}
        (qb-oneCall (AtLevel.ledger n vr (s n)) (AtLevel.ledgerCall n vr) λ _ _ → refl))))

    factorᴿ : (hash : Systems HashIf^ω) (n : ℕ)
            → subᶠ (λ⇒ᶜ (Δ 𝟘ᴳ)) (ledgerᶠ ∙ᶠ imgᶠ HashIf^ω hash) n
              ≈ imgᶠ LedgerIf^ω (Realᴴ hash vr s) n
    factorᴿ hash n = ⟺ (ledger-factor hash vr n (s n))

  -- With one upper stage there is no simulator to compose, hence none to
  -- forget afterwards (`docs/ledger-lift-eps.md` §§1, 5).
  hash-liftᵇ : (hash : Systems HashIf^ω) (ε : ℕ → ℕ → ℚ) → hash ≈ᶠ[ ε ] oracle^ω
             → Realᴴ hash vr s ≈ᶠ[ εᴴ ε ] Realᴴ oracle^ω vr s
  hash-liftᵇ hash ε h =
    ≈ctx⇒≈ctxᴬ (εᴴ ε)
      (≈ctx-resp (εᴴ ε) (factorᴿ hash) (factorᴿ oracle^ω)
        (≈ctx-sub (λ⇒ᶜ (Δ 𝟘ᴳ)) (λ n q → ε n (scale q 1⁺))
          (≈ctx-ext ledgerᶠ (λ _ → 1⁺) ledgerᶠ-qb ε (≈ctxᴬ⇒≈ctx ε h))))

  hash-liftⁿ : (hash : Systems HashIf^ω) → hash ≈ᶠᴺ oracle^ω
             → Realᴴ hash vr s ≈ᶠᴺ Realᴴ oracle^ω vr s
  hash-liftⁿ hash (ε , neg , h) = εᴴ ε , εᴴ-negligible ε neg , hash-liftᵇ hash ε h

ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≈ᶠᴺ oracle^ω
  → PreservesValue (genesisTotal V) (Realᴴ hash inputConsuming (genesisAt a V))
ledger-preserves-value-from-hash a V hash si hp =
  preserves-value-transfer a V (Realᴴ hash inputConsuming (genesisAt a V)) si
    (hash-liftⁿ inputConsuming (genesisAt a V) hash hp)

------------------------------------------------------------------------
-- Claim 2: state-event safety
------------------------------------------------------------------------

-- UC identifies no internal state, so a state event comes back only through
-- `TruthfulAudit` (a theorem for the ideal ledger, `ideal-truthful`; part of
-- the statement otherwise).

module _ (a V : ℕ) where

  ledger-uc-to-state :
      SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
    → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR
    → StateSafe R badR (λ n q → εᴸ n (q ℕ.+ q))
  ledger-uc-to-state si R badR em =
    preservesValue⇒stateSafe (genesisTotal V) R badR {εᴸ} (preserves-value-transfer a V R si em)

  ledger-uc-to-pov-family :
      SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
    → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR → BoundedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
  ledger-uc-to-pov-family si R badR em truthful =
    stateᴺ⇒hitᴺ R badR (λ n → idleTest (R n) (badR n)) (λ _ _ → refl) (λ n q → εᴸ n (q ℕ.+ q))
      (ledger-uc-to-state si R badR em truthful)

  ledger-pov-family-negligible :
      SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
    → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR
    → (p : ℕ → ℕ) → Poly p
    → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
      × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
         → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
  ledger-pov-family-negligible si R badR em truthful p Pp =
    let νₚ , neg , bnd = ledger-uc-to-pov-family si R badR em truthful p Pp
    in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
     , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
     , bnd

ledger-conserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≈ᶠᴺ oracle^ω
  → StateSafe (Realᴴ hash inputConsuming (genesisAt a V))
              (λ n → Watched.badTotal n (genesisAt a V n)) (λ n q → εᴸ n (q ℕ.+ q))
ledger-conserves-value-from-hash a V hash si hp =
  preservesValue⇒stateSafe (genesisTotal V) (Realᴴ hash inputConsuming (genesisAt a V))
    (λ n → Watched.badTotal n (genesisAt a V n)) {εᴸ}
    (ledger-preserves-value-from-hash a V hash si hp)
    λ n → Watched.auditWatch-complete n (hash n) inputConsuming (genesisAt a V n)

------------------------------------------------------------------------
-- Claim 3: the genesis is live
------------------------------------------------------------------------

module Live (a V n : ℕ) = Replay.Genesis n (ser n) (h₀ n) a V

ideal-spends-genesis : (a V n : ℕ)
  → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ
  × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))
ideal-spends-genesis a V n = Live.genesis-live a V n , Live.genesis-moves a V n

------------------------------------------------------------------------
-- What claims 1 and 2 do not say
------------------------------------------------------------------------

-- Diverges at every query: satisfies claim 1 at zero slack yet never
-- accepts, so neither safety claim implies responsiveness.
Mute : Systems LedgerIf^ω
Mute n = record { St = ⊤ ; init = tt ; step = λ _ _ → dead }

-- Always bad, never says so: satisfies claim 1 while its trajectory event has
-- probability one; the gap is exactly `TruthfulAudit`.
Liar : Systems LedgerIf^ω
Liar n = record { St = ⊤ ; init = tt ; step = λ _ _ → ret (tt , AtLevel.ok false) }

always-bad : (n : ℕ) → St (Liar n) → Bool
always-bad _ _ = true

module _ (a V : ℕ) where

  private
    never-reports : (P : Systems LedgerIf^ω)
                  → ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                     → Pr (P n) (auditWatch (genesisTotal V) n d) ≡ 0ℚ)
                  → PreservesValue (genesisTotal V) P
    never-reports P zero-pr p Pp = (λ _ → 0ℚ) , Negligible-0 , λ n →
      hitsᴸ (genesisTotal V) P n (p n) λ d _ → upper-run (P n) (auditWatch (genesisTotal V) n d)
        (subst (ℚ._≤ εᴸ n (p n) ℚ.+ 0ℚ) (sym (zero-pr n d))
               (subst (0ℚ ℚ.≤_) (sym (+-identityʳ (εᴸ n (p n)))) (0≤εᴸ n (p n))))

  mute-silent : (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
              → Pr (Mute n) (auditWatch (genesisTotal V) n d) ≡ 0ℚ
  mute-silent _ (out _)   = lookupᴰℚ-return (just false) mb
  mute-silent n (ask q k) =
    trans (>>=ᴹ-identityˡ nothing (kmaybe λ st → runFrom (Mute n) (proj₁ st)
             (Watched.auditWatchFrom n (genesisTotal V)
               (Watched.reportsLoss n (genesisTotal V) q (proj₂ st)) (k (proj₂ st)))) mb)
          (lookupᴰℚ-return nothing mb)
  mute-silent n (coin μ k) =
    trans (E-bind μ (λ b → runObs (Mute n) (auditWatch (genesisTotal V) n (k b))) mb)
          (trans (lookupᴰℚ-cong-P (entries μ) (λ b → mute-silent n (k b))) (E-const μ 0ℚ))

  mute-preserves-value : PreservesValue (genesisTotal V) Mute
  mute-preserves-value = never-reports Mute mute-silent

  mute-never-accepts : (n : ℕ) → Pr (Mute n) (Live.spend a V n) ≡ 0ℚ
  mute-never-accepts n =
    trans (>>=ᴹ-identityˡ nothing
             (kmaybe λ st → runFrom (Mute n) (proj₁ st) (out (AtLevel.accepted n (proj₂ st)))) mb)
          (lookupᴰℚ-return nothing mb)

  liar-quiet : (n : ℕ) (acc : Bool) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
             → Pr₁⊥ (runFrom (Liar n) tt (Watched.auditWatchFrom n (genesisTotal V) acc d))
               ≡ bool→ℚ acc
  liar-quiet _ acc (out _)   = lookupᴰℚ-return (just acc) mb
  liar-quiet n acc (ask q k) =
    trans (>>=⊥-identityˡ (tt , ok false) (λ st → runFrom (Liar n) (proj₁ st)
             (Watched.auditWatchFrom n (genesisTotal V)
               (acc ∨ Watched.reportsLoss n (genesisTotal V) q (proj₂ st)) (k (proj₂ st)))) mb)
          (trans (cong (λ b → Pr₁⊥ (runFrom (Liar n) tt
                                     (Watched.auditWatchFrom n (genesisTotal V) b (k (ok false)))))
                       (quiet q))
                 (liar-quiet n acc (k (ok false))))
    where
    open AtLevel n

    quiet : (q′ : Query) → acc ∨ Watched.reportsLoss n (genesisTotal V) q′ (ok false) ≡ acc
    quiet (submit _) = ∨-identityʳ acc
    quiet audit      = ∨-identityʳ acc
  liar-quiet n acc (coin μ k) =
    trans (E-bind μ (λ b → runFrom (Liar n) tt
                             (Watched.auditWatchFrom n (genesisTotal V) acc (k b))) mb)
          (trans (lookupᴰℚ-cong-P (entries μ) (λ b → liar-quiet n acc (k b)))
                 (E-const μ (bool→ℚ acc)))

  liar-preserves-value : PreservesValue (genesisTotal V) Liar
  liar-preserves-value = never-reports Liar λ n → liar-quiet n false

  liar-not-truthful : ¬ TruthfulAudit (genesisTotal V) Liar always-bad
  liar-not-truthful tr =
    1≰0 (subst₂ ℚ._≤_ (lookupᴰℚ-return (just true) mb) (lookupᴰℚ-return (just false) mb) (tr 0 (out false)))

------------------------------------------------------------------------
-- The replay attack at family level
------------------------------------------------------------------------

-- `preservesValue⇒saturated` hands the attack's strategy back a bound
-- `ε n 3 + ν n`, eventually below `½` for any negligible schedule `ε`, against
-- probability one.
-- `Chimericᶠ` starts account-funded rather than at `Ideal`'s UTxO genesis,
-- which never funds an account (`System.ledger-keeps-accts-[]`); only the
-- watch is shared, via `funded-total`.  Whether the chimeric variant preserves
-- value at the UTxO genesis is left open (`docs/end-to-end.md` §2).

module At (V n : ℕ) = Replay.Attack n (ser n) V

Chimericᶠ : (V : ℕ) → Systems LedgerIf^ω
Chimericᶠ V n = AtLevel.Sys n chimeric (At.s₀ V n)

module _ (V : ℕ) where

  funded-total : (n : ℕ) → genesisTotal (suc (suc V)) ≡ Ledger.total n (At.s₀ V n)
  funded-total _ = cong (λ z → suc (suc z)) (+-identityʳᴺ (V ℕ.+ 0))

  chimeric-loses-value^ω : (n : ℕ)
    → Pr (Chimericᶠ V n) (auditWatch (genesisTotal (suc (suc V))) n (At.replay V n)) ≡ 1ℚ
  chimeric-loses-value^ω n =
    At.chimeric-loses-value V n (genesisTotal (suc (suc V))) (funded-total n)

  chimeric-not-preserving : (ε : ℕ → ℕ → ℚ) → NegligibleBound ε
    → ¬ Hitsᴺ (λ n → morphism (Chimericᶠ V n)) (auditMonitorᶠ (genesisTotal (suc (suc V)))) ε
  chimeric-not-preserving ε negε pv =
    let ν , neg , bnd = preservesValue⇒saturated (genesisTotal (suc (suc V))) (Chimericᶠ V) {ε} pv
                          (λ _ → 3) (poly-const 3)
        N , small     = →0-+ (Negligible⇒→0 (negε (λ _ → 3) (poly-const 3)))
                             (Negligible⇒→0 neg) ½ (positive⁻¹ ½)
    in 1≰½ (≤-trans (≤-reflexive (sym (chimeric-loses-value^ω N)))
                    (≤-trans (bnd N (At.replay V N) (At.replay-asks V N)) (small N ≤-refl)))

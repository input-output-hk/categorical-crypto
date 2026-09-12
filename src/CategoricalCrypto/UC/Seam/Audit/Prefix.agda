{-# OPTIONS --safe --without-K --guardedness #-}

-- The widened class is closed under the context compositions `Absorbs`
-- performs, and with that the unit-grade budgeted route reaches a probability.
--
-- `absorb-watchedᵖ` is the closure, and `docs/prefix-tolerant-audit-plan.md`
-- put its risk on whether a prefix survives those compositions.  It does, with
-- nothing up to `≈ₚ` anywhere: absorbing a trivial-grade simulator prepends the
-- simulator's own initialization to what the context observes
-- (`UC.Seam.Grounded.subPrefixedˢ`), and two prefixes in sequence are one by
-- the monad's associativity on the nose (`Dp.Mass.const-bind-astotal` for the
-- termination, the two halves of the slack).  So the SYNTACTIC prefix shape of
-- `watchedᵖ` suffices and the plan's fallbacks are unused.
--
-- `ctx-absorb` is `docs/protocol-implementation-review.md` §2's inclusion
-- obligation: the extraction context with the simulator absorbed into it is a
-- permitted context of the PULLBACK class `absorb s cs (watchedᵖ I bad)` — the
-- class `UC.Audit.audit-carry` delivers on the real side — at the budget the
-- absorption adjusts to.  It is a statement about the IDEAL process while the
-- bound carried is about the real one, which is why `absorb-absorbs` (a closure
-- and nothing more) is not a substitute for it.
--
-- `uc-audit-bounded` composes the two with the carry, which is the gap
-- `docs/end-to-end.md`'s "Obstruction" section records, closed at the unit
-- grade.  Only there: the simulator is a trivial-grade scalar, so
-- `subPrefixedˢ` may call its whole contribution an initialization, and prefix
-- congruence propagates a supplied prefix witness rather than manufacturing one
-- (review §3).
--
-- The `ASTotal` hypothesis is the one the trivial-grade collapse already
-- spends: `UC.Seam.Grounded.simTotal⇒point` supplies it from `TG.SimTotal`,
-- which `subBlind⇒unitGrade` in turn reads off the REAL side's totality.

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Dp using (Dₚ; _>>=ₚ_; _≈ₚ_; >>=ₚ-assoc)
open import ProbabilisticLogic.Dp.Mass using (ASTotal; const-bind-astotal)
open import ProbabilisticLogic.Dp.Reasoning using (_⟨≈⟩_; bindᶠ; ≈sym)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mono)
open import CategoricalCrypto.UC.Machine using (⊤ᵛ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Audit
  using ( _≤UC[_]_; sim; simCost; q≤simCost; AuditBound; Absorbs; absorb
        ; absorb-absorbs; audit-carry; module TrivialGrade )
open import CategoricalCrypto.UC.Seam.Audit.Bounded using (boundedIsAuditᵖ; ctx-watched)
open import CategoricalCrypto.UC.Seam.Audit.Context using (auditClose; auditTest; extract)
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; 𝟘ᴳ; ιᴳ; subPrefixedˢ)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)
open import CategoricalCrypto.UC.Seam.Grounding.Prefix
  using (Prefixedᵒ; prefixedᵒ-bind; prefixedᵒ-resp-≈)

module CategoricalCrypto.UC.Seam.Audit.Prefix where

open HomReasoning

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

-- Closure under the absorption: the simulator's initialization goes in front of
-- the prefix the context already carried, and the two are one prefix.
absorb-watchedᵖ : (B : Iface) (P : Protocol unitᴵ B)
                  (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
                  (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (cs : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
                → Absorbs s cs (TG.watchedᵖ P bad) (TG.watchedᵖ P bad)
absorb-watchedᵖ B P bad s cs tot W Et m q (d , p , a , tp , near) =
    d , (σ >>=ₚ λ _ → p) , asks≤-mono (q≤simCost q cs) d a
  , const-bind-astotal σ p tot tp , step₁ ⟨≈⟩ step₂ ⟨≈⟩ step₃
  where
  σ : Dₚ ⊤ᵛ
  σ = pointᵒ 𝟘ᴳ 𝟘ᴳ s

  f₀ : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
  f₀ = closedᵒ (morphism P)

  run : Dₚ Bool
  run = runᴹ (morphism P) (bad d)

  -- The absorbed simulator sits between the test and the process below it.
  pre : Prefixedᵒ 𝟘ᵒ Ωᵒ (((Et ∘ id ⊗₁ sub s) ∘ id ⊗₁ f₀) ∘ m) ((Et ∘ id ⊗₁ f₀) ∘ m) σ
  pre = prefixedᵒ-resp-≈ 𝟘ᵒ Ωᵒ _ _ _ _ σ
          ((refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (sym-assoc ⟩∘⟨refl)) sym-assoc
          (subPrefixedˢ B s W Et (id ⊗₁ f₀ ∘ m))

  step₁ : Obs (((Et ∘ id ⊗₁ sub s) ∘ id ⊗₁ f₀) ∘ m)
            ≈ₚ (σ >>=ₚ λ _ → Obs ((Et ∘ id ⊗₁ f₀) ∘ m))
  step₁ = prefixedᵒ-bind _ _ σ pre

  step₂ : (σ >>=ₚ λ _ → Obs ((Et ∘ id ⊗₁ f₀) ∘ m))
            ≈ₚ (σ >>=ₚ λ _ → (p >>=ₚ λ _ → run))
  step₂ = bindᶠ (λ _ → near)

  step₃ : (σ >>=ₚ λ _ → (p >>=ₚ λ _ → run)) ≈ₚ ((σ >>=ₚ λ _ → p) >>=ₚ λ _ → run)
  step₃ = ≈sym (>>=ₚ-assoc σ (λ _ → p) (λ _ → run))

-- Review §2's inclusion: the extraction context IS a permitted context of the
-- carried class, at the adjusted budget.
ctx-absorb : (B : Iface) (I : Protocol unitᴵ B)
             (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
             (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (cs : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
           → (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
           → absorb s cs (TG.watchedᵖ I bad) 𝟘ᴳ (auditTest B (bad d)) auditClose (q ℕ.* 1)
ctx-absorb B I bad s cs tot q d a =
  absorb-watchedᵖ B I bad s cs tot 𝟘ᴳ (auditTest B (bad d)) auditClose (q ℕ.* 1)
    (TG.watched⇒watchedᵖ I bad 𝟘ᴳ (auditTest B (bad d)) auditClose (q ℕ.* 1)
      (ctx-watched I bad q d a))

-- …so a real-side bound at the carried class is layer 1's own `Bounded`, the
-- membership PROVED rather than presumed.
auditIsBoundedᴬ : (B : Iface) (R I : Protocol unitᴵ B)
                  (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
                  (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (cs : ℕ) (ε : ℕ → ℚ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ s)
                → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                → AuditBound (closedᵒ (morphism R)) (absorb s cs (TG.watchedᵖ I bad)) ε
                → Bounded R bad ε
auditIsBoundedᴬ B R I bad s cs ε tot bad-asks =
  extract R bad ε {𝔈 = absorb s cs (TG.watchedᵖ I bad)} bad-asks
          (ctx-absorb B I bad s cs tot)

-- The unit-grade budgeted route, end to end: the ideal bound supplied at the
-- widened class, carried across a budgeted emulation at `simCost`, extracted
-- back to a probability.
uc-audit-bounded : (B : Iface) (R I : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) {cs : ℕ}
                   (em : closedᵒ (morphism R) ≤UC[ cs ] closedᵒ (morphism I))
                   (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
                 → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim em))
                 → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                 → Bounded I bad ε
                 → Bounded R bad (λ q → ε (simCost q cs) ℚ.+ ν)
uc-audit-bounded B R I bad {cs} em ε ν ν>0 tot bad-asks bi =
  auditIsBoundedᴬ B R I bad (sim em) cs _ tot bad-asks
    (audit-carry _ _ em {𝔉 = TG.watchedᵖ I bad}
                 (absorb-absorbs {s = sim em} {cs} {TG.watchedᵖ I bad}) ε ν ν>0
                 (boundedIsAuditᵖ I bad ε bi))

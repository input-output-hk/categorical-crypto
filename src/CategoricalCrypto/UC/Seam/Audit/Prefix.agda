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
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-monoˡ-≤; ≤-refl; ≤-trans)

open import ProbabilisticLogic.Dp using (Dₚ; _>>=ₚ_; _≈ₚ_; >>=ₚ-assoc; ≼ₚ-refl)
open import ProbabilisticLogic.Dp.Advantage using (_≼ₚ[_]_; ≼ₚ[]-resp)
open import ProbabilisticLogic.Dp.Mass using (ASTotal; const-bind-astotal; const-bind-≼)
open import ProbabilisticLogic.Dp.Reasoning using (_⟨≈⟩_; bindᶠ; ≈sym)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mono)
open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Machine using (⊤ᵛ)
open import CategoricalCrypto.UC.Model.Bridge using (_≈ℰᶜ_; ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (massᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Audit
  using ( _≤UC[_]_; emulate; sim; simCost; q≤simCost; AuditBound; Absorbs; absorb
        ; absorb-absorbs; audit-carry; module TrivialGrade )
open import CategoricalCrypto.UC.Seam.Audit.Bounded
  using (boundedIsAuditᵖ; ctx-watched; supply)
open import CategoricalCrypto.UC.Seam.Audit.Context
  using (audit-run; auditClose; auditTest; extract; extract-bounded)
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; 𝟘ᴳ; ιᴳ; subPrefixedˢ)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)
open import CategoricalCrypto.UC.Seam.Grounding.Prefix
  using (Prefixedᵒ; prefixedᵒ-bind; prefixedᵒ-resp-≈)
open import CategoricalCrypto.UC.Seam.Slide using (slide⊗)

module CategoricalCrypto.UC.Seam.Audit.Prefix where

open import CategoricalCrypto.UC.Emulation ucBaseᵒ using (obs; tv₁)

open HomReasoning
open Mass massᵒ using (dominate)

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

-- What a trivial-grade simulator absorbed into a context contributes to what
-- that context observes: its own initialization, in front of it and nothing
-- else.  `subPrefixedˢ` is the statement and `prefixedᵒ-bind` reads it off the
-- observation, exactly — which is what lets both routes below start here.
prefix-absorbᵒ : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (W : Channel)
                 (Et : W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ) {D : Channel}
                 (g : D ⇒ W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B)) (m : 𝟘ᵒ ⇒ D)
               → Obs (((Et ∘ id ⊗₁ sub s) ∘ g) ∘ m)
                 ≈ₚ (pointᵒ 𝟘ᴳ 𝟘ᴳ s >>=ₚ λ _ → Obs ((Et ∘ g) ∘ m))
prefix-absorbᵒ B s W Et g m = prefixedᵒ-bind _ _ _
  (prefixedᵒ-resp-≈ 𝟘ᵒ Ωᵒ _ _ _ _ _
     ((refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (sym-assoc ⟩∘⟨refl)) sym-assoc
     (subPrefixedˢ B s W Et (g ∘ m)))

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

  step₁ : Obs (((Et ∘ id ⊗₁ sub s) ∘ id ⊗₁ f₀) ∘ m)
            ≈ₚ (σ >>=ₚ λ _ → Obs ((Et ∘ id ⊗₁ f₀) ∘ m))
  step₁ = prefix-absorbᵒ B s W Et (id ⊗₁ f₀) m

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

------------------------------------------------------------------------
-- The same endpoint, with no event class on the route

-- Review §4.3's application consequence, stated directly: a trivial-grade
-- simulator standing in front of the extraction context contributes only its
-- own initialization (`prefix-absorbᵒ`), and an initialization is never seen to
-- ADD mass — so what the simulator-fronted context observes is dominated, with
-- no slack, by the ideal monitored run itself.
--
-- The `ASTotal` the class route spends is not spent here.  It is what the
-- two-sided `≈ₚ[ ε ]` of `prefixedᵒ-obs` needs, and this is the one-sided half;
-- `uc-audit-bounded′` keeps the premise because the theorem it reproves has it.
sim-prefixedᵖ : (B : Iface) (I : Protocol unitᴵ B) (e : Strat (Neg B) (Pos B))
                (s : 𝟘ᴳ ⇒ 𝟘ᴳ)
              → obs (tv₁ 𝟘ᴳ (sub s ∘ closedᵒ (morphism I)) (auditTest B e)) auditClose
                ≼ₚ[ 0ℚ ] runᴹ (morphism I) e
sim-prefixedᵖ B I e s =
  ≼ₚ[]-resp (proj₁ chain) (≼ₚ-refl _) (const-bind-≼ (pointᵒ 𝟘ᴳ 𝟘ᴳ s) run 0ℚ ≤-refl)
  where
  f₀ : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
  f₀ = closedᵒ (morphism I)

  run : Dₚ Bool
  run = runᴹ (morphism I) e

  -- The simulator leaves the process and becomes one wire in front of the test.
  slide : (auditTest B e ∘ id ⊗₁ (sub s ∘ f₀)) ∘ auditClose
        ≈ ((auditTest B e ∘ id ⊗₁ sub s) ∘ id ⊗₁ f₀) ∘ auditClose
  slide = ((refl⟩∘⟨ slide⊗ 𝟘ᴳ (sub s) f₀) ○ sym-assoc) ⟩∘⟨refl

  chain : obs (tv₁ 𝟘ᴳ (sub s ∘ f₀) (auditTest B e)) auditClose
            ≈ₚ (pointᵒ 𝟘ᴳ 𝟘ᴳ s >>=ₚ λ _ → run)
  chain = obs-resp slide
      ⟨≈⟩ prefix-absorbᵒ B s 𝟘ᴳ (auditTest B e) (id ⊗₁ f₀) auditClose
      ⟨≈⟩ bindᶠ (λ _ → audit-run B e (morphism I))

-- What that route actually consumes: one emulation witness, one allowance
-- inflation, and the ideal bound.  No query certificate and no budget law — an
-- environment agreement holds at EVERY test, so nothing here pays for the
-- simulator's queries; `Bounded`'s own quantifier is where the allowance moves.
bounded-carry : (B : Iface) (R I : Protocol unitᴵ B)
                (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
                (s : 𝟘ᴳ ⇒ 𝟘ᴳ) → closedᵒ (morphism R) ≈ℰᶜ (sub s ∘ closedᵒ (morphism I))
              → (p : ℕ → ℕ) → ((q : ℕ) → q ℕ.≤ p q)
              → (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
              → Bounded I bad ε → Bounded R bad (λ q → ε (p q) ℚ.+ ν)
bounded-carry B R I bad s em p q≤p ε ν ν>0 bi =
  extract-bounded R bad (λ q → ε (p q) ℚ.+ ν) λ q d a n →
    let k , le = dominate (em 𝟘ᴳ (auditTest B (bad d)) auditClose) ν ν>0 n
    in ≤-trans le (+-monoˡ-≤ ν
         (supply I bad ε (p q) d (asks≤-mono (q≤p q) d a) bi _
                 (sim-prefixedᵖ B I (bad d) s) k))

-- `uc-audit-bounded` again, hypotheses and conclusion verbatim, by that route:
-- the membership records, the absorption and the pullback class are gone, and
-- what is left is the emulation's own domination, the mass bound above, and
-- `UC.Seam.Audit.Context.extract-obs`.  `simCost` remains the allowance the
-- bound is read at — the uncharged one is a DIFFERENT statement, an arbitrary
-- `ε` being monotone in no direction.
uc-audit-bounded′ : (B : Iface) (R I : Protocol unitᴵ B)
                    (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) {cs : ℕ}
                    (em : closedᵒ (morphism R) ≤UC[ cs ] closedᵒ (morphism I))
                    (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
                  → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim em))
                  → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                  → Bounded I bad ε
                  → Bounded R bad (λ q → ε (simCost q cs) ℚ.+ ν)
uc-audit-bounded′ B R I bad {cs} em ε ν ν>0 _ _ =
  bounded-carry B R I bad (sim em) (emulate em)
                (λ q → simCost q cs) (λ q → q≤simCost q cs) ε ν ν>0

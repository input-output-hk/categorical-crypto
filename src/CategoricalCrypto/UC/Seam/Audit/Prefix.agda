{-# OPTIONS --safe --without-K --guardedness #-}

-- The unit-grade budgeted route to a probability, with no event class on it.
--
-- `docs/end-to-end.md`'s "Obstruction" section records the gap this closes, and
-- only the unit grade closes it: the simulator is a trivial-grade scalar, so
-- `UC.Seam.Grounded.subPrefixedˢ` may call its whole contribution an
-- initialization.
--
-- `prefix-absorbᵒ` is what an absorbed trivial-grade simulator contributes to
-- what a context observes — its own initialization, in front of it and nothing
-- else.  `sim-prefixed` reads that one-sidedly (an initialization is never seen
-- to ADD mass), `bounded-carry` spends it against the emulation's own
-- domination, and `uc-audit-bounded` is the endpoint at the allowance `simCost`.
--
-- `uc-audit-bounded`'s `ASTotal` hypothesis and the monitor's budget law are
-- part of its interface and are NOT consumed: the former is what the two-sided
-- `≈ₚ[ ε ]` of `prefixedᵒ-obs` needs and this is the one-sided half, and
-- `Bounded I bad ε` charges `ε` at the budget of `d`, never of `bad d`.  The
-- honest premise list is `bounded-carry`'s.

import Categories.Category.Monoidal.Reasoning as MonR

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-monoˡ-≤; ≤-refl; ≤-trans)

open import ProbabilisticLogic.Dp using (Dₚ; _>>=ₚ_; _≈ₚ_; ≼ₚ-refl)
open import ProbabilisticLogic.Dp.Advantage using (_≼ₚ[_]_; ≼ₚ[]-resp)
open import ProbabilisticLogic.Dp.Mass using (ASTotal; const-bind-≼)
open import ProbabilisticLogic.Dp.Reasoning using (_⟨≈⟩_; bindᶠ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mono)
open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Model.Enrichment using (massᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ; obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Audit
  using (_≤UC[_]_; emulate; sim; simCost; q≤simCost)
open import CategoricalCrypto.UC.Seam.Audit.Bounded using (supply)
open import CategoricalCrypto.UC.Seam.Audit.Context
  using (audit-run; auditClose; auditTest; extract-bounded)
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; 𝟘ᴳ; subPrefixedˢ)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)
open import CategoricalCrypto.UC.Seam.Grounding.Prefix
  using (prefixedᵒ-bind; prefixedᵒ-resp-≈)

module CategoricalCrypto.UC.Seam.Audit.Prefix where

open C using (obs; tv₁)

open MonR monoidal
open Mass massᵒ using (dominate)

-- What a trivial-grade simulator absorbed into a context contributes to what
-- that context observes: its own initialization, in front of it and nothing
-- else.  `subPrefixedˢ` is the statement and `prefixedᵒ-bind` reads it off the
-- observation, exactly.
prefix-absorbᵒ : (B : Iface) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (W : Channel)
                 (Et : W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B) ⇒ Ωᵒ) {D : Channel}
                 (g : D ⇒ W ⊗₀ T₀ 𝟘ᴳ (ifaceᵒ B)) (m : 𝟘ᵒ ⇒ D)
               → Obs (((Et ∘ id ⊗₁ sub s) ∘ g) ∘ m)
                 ≈ₚ (pointᵒ 𝟘ᴳ 𝟘ᴳ s >>=ₚ λ _ → Obs ((Et ∘ g) ∘ m))
prefix-absorbᵒ B s W Et g m = prefixedᵒ-bind _ _ _
  (prefixedᵒ-resp-≈ 𝟘ᵒ Ωᵒ _ _ _ _ _
     ((refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (sym-assoc ⟩∘⟨refl)) sym-assoc
     (subPrefixedˢ B s W Et (g ∘ m)))

-- Review §4.3's application consequence, stated directly: a trivial-grade
-- simulator standing in front of the extraction context contributes only its
-- own initialization (`prefix-absorbᵒ`), and an initialization is never seen to
-- ADD mass — so what the simulator-fronted context observes is dominated, with
-- no slack, by the ideal monitored run itself.
sim-prefixed : (B : Iface) (I : Protocol unitᴵ B) (e : Strat (Neg B) (Pos B))
               (s : 𝟘ᴳ ⇒ 𝟘ᴳ)
             → obs (tv₁ 𝟘ᴳ (sub s ∘ closedᵒ (morphism I)) (auditTest B e)) auditClose
               ≼ₚ[ 0ℚ ] runᴹ (morphism I) e
sim-prefixed B I e s =
  ≼ₚ[]-resp (proj₁ chain) (≼ₚ-refl _) (const-bind-≼ (pointᵒ 𝟘ᴳ 𝟘ᴳ s) run 0ℚ ≤-refl)
  where
  f₀ : 𝟘ᵒ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
  f₀ = closedᵒ (morphism I)

  run : Dₚ Bool
  run = runᴹ (morphism I) e

  -- The simulator leaves the process and becomes one wire in front of the test.
  slide : (auditTest B e ∘ id ⊗₁ (sub s ∘ f₀)) ∘ auditClose
        ≈ ((auditTest B e ∘ id ⊗₁ sub s) ∘ id ⊗₁ f₀) ∘ auditClose
  slide = ((refl⟩∘⟨ split₂ʳ) ○ sym-assoc) ⟩∘⟨refl

  chain : obs (tv₁ 𝟘ᴳ (sub s ∘ f₀) (auditTest B e)) auditClose
            ≈ₚ (pointᵒ 𝟘ᴳ 𝟘ᴳ s >>=ₚ λ _ → run)
  chain = obs-resp slide
      ⟨≈⟩ prefix-absorbᵒ B s 𝟘ᴳ (auditTest B e) (id ⊗₁ f₀) auditClose
      ⟨≈⟩ bindᶠ (λ _ → audit-run B e (morphism I))

-- What the route actually consumes: one emulation witness, one allowance
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
                 (sim-prefixed B I (bad d) s) k))

-- The unit-grade budgeted route, end to end: the ideal bound carried across a
-- budgeted emulation and read back as layer 1's own probability.  `simCost` is
-- the allowance the bound is read at — the uncharged reading is a DIFFERENT
-- statement, an arbitrary `ε` being monotone in no direction.
uc-audit-bounded : (B : Iface) (R I : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) {cs : ℕ}
                   (em : closedᵒ (morphism R) ≤UC[ cs ] closedᵒ (morphism I))
                   (ε : ℕ → ℚ) (ν : ℚ) → 0ℚ ℚ.< ν
                 → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim em))
                 → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                 → Bounded I bad ε
                 → Bounded R bad (λ q → ε (simCost q cs) ℚ.+ ν)
uc-audit-bounded B R I bad {cs} em ε ν ν>0 _ _ =
  bounded-carry B R I bad (sim em) (emulate em)
                (λ q → simCost q cs) (λ q → q≤simCost q cs) ε ν ν>0

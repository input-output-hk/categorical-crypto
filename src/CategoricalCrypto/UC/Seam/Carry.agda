{-# OPTIONS --safe --without-K --guardedness #-}

-- The seam's corollary: `Adequacy` and `PrAgree` inhabit `AgreeToAdv`, and both
-- are theorems (`UC.Seam.Adequacy`, `Protocol.Machine.Agree`), so `agreeToAdv`
-- and the POV carry below are closed terms.
--
-- `adv-at`/`adv-from-runs` are the same arithmetic with the error KEPT rather
-- than spent at one value, which is what a premise whose slack must stay
-- negligible asks for (`UC.Family`'s header; `UC.Saturated._≈negl_` is the
-- layer-1 relation it feeds).  `agree-to-adv` is `adv-from-runs` at a constant
-- slack.
--
-- It is a module of its own because `UC.Seam` pays the machine-layer
-- conversions once, in its interface, and the arithmetic here re-derives none
-- of them: past `run-agree`, which is one `≈ₚ[]-resp`, everything is about `Dₚ`
-- masses and ℚ, and the two processes are opaque carriers.

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (m≤n+m)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist.Advantage using (advᵇ⊥)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage


open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy

module CategoricalCrypto.UC.Seam.Carry where

-- Adequacy transports environment agreement onto the direct runs: the step the
-- refuted reflection direction was meant to supply.
run-agree : Adequacy → (B : Iface) (u v : Proc unitᴵ B) → Agreeˢ B u v
          → (d : Strat (Neg B) (Pos B)) (ε : ℚ) → 0ℚ ℚ.< ε
          → runˢ B u d ≈ₚ[ ε ] runˢ B v d
run-agree ad B u v ag d ε ε>0 = ≈ₚ[]-resp (ad B u d) (ad B v d) (ag d ε ε>0)

private
  -- `x ≤ y + ε`, as a bound on the difference.
  shift : (x y ε : ℚ) → x ℚ.≤ y ℚ.+ ε → x ℚ.- y ℚ.≤ ε
  shift x y ε le = begin
    x ℚ.- y          ≤⟨ +-monoˡ-≤ (ℚ.- y) le ⟩
    (y ℚ.+ ε) ℚ.- y  ≡⟨ cong (ℚ._- y) (+-comm y ε) ⟩
    (ε ℚ.+ y) ℚ.- y  ≡⟨ +-−-cancel ε y ⟩
    ε                ∎
    where open ≤-Reasoning

  -- What `PrAgree` says about one side, as a property of the mass alone: the
  -- verdict-`b` probability is read off at every budget past some witness.
  Reads : Bool → Dₚ Bool → ℚ → Set
  Reads b x u = Σ[ n ∈ ℕ ] ((m : ℕ) → Pr≤[ b ] (n ℕ.+ m) x ≡ u)

  -- Both sides being read off, an ε-domination of masses bounds the values:
  -- `Pr≤[ b ]` is monotone, so the budget the domination hands back can always
  -- be raised to one that computes the right-hand value.
  one-sided : (b : Bool) (x y : Dₚ Bool) (u v ε : ℚ)
            → Reads b x u → Reads b y v → x ≼ₚ[ ε ] y → u ℚ.≤ v ℚ.+ ε
  one-sided b x y u v ε (nx , hx) (ny , hy) le =
    let m , bd = le b (nx ℕ.+ 0) in begin
    u                            ≡⟨ sym (hx 0) ⟩
    Pr≤[ b ] (nx ℕ.+ 0) x        ≤⟨ bd ⟩
    Pr≤[ b ] m y ℚ.+ ε           ≤⟨ +-monoˡ-≤ ε (Pr≤-mono b y (m≤n+m m ny)) ⟩
    Pr≤[ b ] (ny ℕ.+ m) y ℚ.+ ε  ≡⟨ cong (ℚ._+ ε) (hy m) ⟩
    v ℚ.+ ε                      ∎
    where open ≤-Reasoning

-- Closeness of the two machine runs at ONE slack is layer 1's advantage bound
-- at that slack, at either verdict.  `prAgree` reads each verdict probability
-- off a budget the domination reaches, and `∣∣≤` closes the bound.
adv-at : {B : Iface} (P Q : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B)) (ε : ℚ)
       → runᴹ (morphism P) d ≈ₚ[ ε ] runᴹ (morphism Q) d
       → (b : Bool) → advᵇ⊥ b (run P d) (run Q d) ℚ.≤ ε
adv-at {B} P Q d ε (le , el) b =
  ∣∣≤ (shift (Prᵇ P b d) (Prᵇ Q b d) ε
             (one-sided b x y (Prᵇ P b d) (Prᵇ Q b d) ε (prAgree b P d) (prAgree b Q d) le))
      (subst (ℚ._≤ ε) (neg-sub (Prᵇ Q b d) (Prᵇ P b d))
             (shift (Prᵇ Q b d) (Prᵇ P b d) ε
                    (one-sided b y x (Prᵇ Q b d) (Prᵇ P b d) ε
                               (prAgree b Q d) (prAgree b P d) el)))
  where
  x = runᴹ (morphism P) d
  y = runᴹ (morphism Q) d

-- …and the packaged form, at a budget-indexed slack: this is `_≈adv[_]_`, whose
-- negligibly graded family is `UC.Saturated._≈negl_`.
adv-from-runs : {B : Iface} (P Q : Protocol unitᴵ B) (δ : ℕ → ℚ)
              → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
                 → runᴹ (morphism P) d ≈ₚ[ δ q ] runᴹ (morphism Q) d)
              → P ≈adv[ δ ] Q
adv-from-runs P Q δ h b q d a = adv-at P Q d (δ q) (h q d a) b

-- …so the ε-quantified form is the constant-slack instance.  The `PrAgree`
-- hypothesis goes unused — `adv-at` spends the closed `prAgree` instead — and
-- is kept because `UC.Seam`'s two named obligations are the interface this
-- module answers.
agree-to-adv : Adequacy → PrAgree → AgreeToAdv
agree-to-adv ad _ {B} P Q ag ε ε>0 =
  adv-from-runs P Q (λ _ → ε)
    (λ _ d _ → run-agree ad B (morphism P) (morphism Q) ag d ε ε>0)

------------------------------------------------------------------------
-- Both hypotheses discharged

agreeToAdv : AgreeToAdv
agreeToAdv = agree-to-adv adequacy prAgree

povCarry : {B : Iface} (P Q : Protocol unitᴵ B)
         → Agreeˢ B (morphism P) (morphism Q)
         → {bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)} {ε : ℕ → ℚ}
         → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
         → (δ : ℚ) → 0ℚ ℚ.< δ
         → Bounded Q bad ε → Bounded P bad (λ q → ε q ℚ.+ δ)
povCarry = pov-carry agreeToAdv

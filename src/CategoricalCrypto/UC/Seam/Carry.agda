{-# OPTIONS --safe --without-K --guardedness #-}

-- The seam's corollary: `Adequacy` and `PrAgree` inhabit `AgreeToAdv`, so the
-- POV carry rests on those two statements and nothing else.
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

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage


open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Seam

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
  -- verdict probability is read off at every budget past some witness.
  Reads : Dₚ Bool → ℚ → Set
  Reads x a = Σ[ n ∈ ℕ ] ((m : ℕ) → Pr≤ (n ℕ.+ m) x ≡ a)

  -- Both sides being read off, an ε-domination of masses bounds the values:
  -- `Pr≤` is monotone, so the budget the domination hands back can always be
  -- raised to one that computes the right-hand value.
  one-sided : (x y : Dₚ Bool) (a b ε : ℚ)
            → Reads x a → Reads y b → x ≼ₚ[ ε ] y → a ℚ.≤ b ℚ.+ ε
  one-sided x y a b ε (nx , hx) (ny , hy) le =
    let m , bd = le (nx ℕ.+ 0) in begin
    a                       ≡⟨ sym (hx 0) ⟩
    Pr≤ (nx ℕ.+ 0) x        ≤⟨ bd ⟩
    Pr≤ m y ℚ.+ ε           ≤⟨ +-monoˡ-≤ ε (Pr≤-mono y (m≤n+m m ny)) ⟩
    Pr≤ (ny ℕ.+ m) y ℚ.+ ε  ≡⟨ cong (ℚ._+ ε) (hy m) ⟩
    b ℚ.+ ε                 ∎
    where open ≤-Reasoning

agree-to-adv : Adequacy → PrAgree → AgreeToAdv
agree-to-adv ad pa {B} P Q ag ε ε>0 _ d _ =
  let le , el = run-agree ad B (morphism P) (morphism Q) ag d ε ε>0
      x = runˢ B (morphism P) d
      y = runˢ B (morphism Q) d
  in ∣∣≤ (shift (Pr P d) (Pr Q d) ε
               (one-sided x y (Pr P d) (Pr Q d) ε (pa P d) (pa Q d) le))
         (subst (ℚ._≤ ε) (neg-sub (Pr Q d) (Pr P d))
                (shift (Pr Q d) (Pr P d) ε
                       (one-sided y x (Pr Q d) (Pr P d) ε (pa Q d) (pa P d) el)))

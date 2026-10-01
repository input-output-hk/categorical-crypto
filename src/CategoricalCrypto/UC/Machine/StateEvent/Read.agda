{-# OPTIONS --safe --without-K --guardedness #-}

-- Reading a state event in an ordinary experiment: the experiment `E , m` at
-- `B` is run against `M ▷ P`, and `UC.Machine.Monitor.flagReadᴹ` above the test
-- waits for its verdict, discards it and answers the flag.  No state is
-- projected out of a composite; the flag is an interface message.
--
-- The completed-run convention is `flagReadᴹ`'s: a test that diverges leaves
-- the reader waiting, so a flag raised before a divergence is not reported.
-- At an embedded strategy the reading is `flagStrat`
-- (`UC.Machine.StateEvent.Agree`); at a protocol image it is
-- `Protocol.Observe.PrHit` (`UC.Machine.StateEvent.Adequacy`).

open import Categories.Category using (Category)

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base

import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.StateEvent

module CategoricalCrypto.UC.Machine.StateEvent.Read where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The reading

stateRead : {A B : Iface} (Y : Iface) (M : Proc A B) → StateTest M
          → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ A) → Dₚ Bool
stateRead {B = B} Y M P = readRun Y (M ▷ P) (flagReader B)

-- The strategy-level closing experiment: play `d`, ignore its verdict, ask
-- the flag.  An answer off the protocol scores `false`.
flagStrat : {Q R : Set} → Strat Q R → Strat (Q ⊎ ⊤) (R ⊎ Bool)
flagStrat (out _)    = ask (inj₂ tt) [ (λ _ → out false) , out ]
flagStrat (ask q k)  = ask (inj₁ q) [ flagStrat ∘ k , (λ _ → out false) ]
flagStrat (coin μ k) = coin μ (flagStrat ∘ k)

-- The flag costs one ask.
asks≤-flag : {Q R : Set} (n : ℕ) (d : Strat Q R) → asks≤ n d → asks≤ (suc n) (flagStrat d)
asks≤-flag n       (out _)    _ = λ { (inj₁ _) → tt ; (inj₂ _) → tt }
asks≤-flag (suc n) (ask _ k)  h = λ { (inj₁ r) → asks≤-flag n (k r) (h r) ; (inj₂ _) → tt }
asks≤-flag n       (coin _ k) h = λ b → asks≤-flag n (k b) (h b)

------------------------------------------------------------------------
-- The bound, as an instance of `UC.Machine.EventBounds`

StateBoundedAt : {A B : Iface} → ℕ → ℚ → (M : Proc A B) → StateTest M → Set₁
StateBoundedAt {B = B} q r M P = BoundedAt q r (M ▷ P) (flagReader B)

module _ {A B : ℕ → Iface} (M : (n : ℕ) → Proc (A n) (B n))
         (P : (n : ℕ) → StateTest (M n)) where

  StateBoundedᶠ : (ℕ → ℕ → ℚ) → Set₁
  StateBoundedᶠ = Boundedᶠ (λ n → M n ▷ P n) (λ n → flagReader (B n))

  StateBoundedᴺ : (ℕ → ℕ → ℚ) → Set₁
  StateBoundedᴺ = Boundedᴺ (λ n → M n ▷ P n) (λ n → flagReader (B n))

------------------------------------------------------------------------
-- Invariance

module _ {A B : Iface} (Y : Iface) where

  stateRead-resp-≈ᵉ : {x y : Annotated A B} → x ≈ᵉ y
                    → (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ A))
                    → stateRead Y (proj₁ x) (proj₂ x) E m ≈ₚ stateRead Y (proj₁ y) (proj₂ y) E m
  stateRead-resp-≈ᵉ e = readRun-resp-≈ Y (▷-≈ e) (flagReader B)

  stateRead-resp-env : (M : Proc A B) (P : StateTest M)
                       {E E′ : Proc (Y ⊗ᴵ B) Ωᴵ} {m m′ : Proc unitᴵ (Y ⊗ᴵ A)}
                     → 𝒫._≈_ E E′ → 𝒫._≈_ m m′
                     → stateRead Y M P E m ≈ₚ stateRead Y M P E′ m′
  stateRead-resp-env M P eE em =
    runᴹ-resp-≈ᴹ
      (𝒫.∘-resp-≈ (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (𝒫.∘-resp-≈ˡ (sub-resp-≈ eE)))) em)
      (ask tt out)

stateBounded-resp-≈ᵉ : {A B : Iface} {q : ℕ} {r : ℚ} {x y : Annotated A B} → x ≈ᵉ y
                     → StateBoundedAt q r (proj₁ x) (proj₂ x)
                     → StateBoundedAt q r (proj₁ y) (proj₂ y)
stateBounded-resp-≈ᵉ {x = x} {y} e h Y E m qE qm le =
  upper-≈ (stateRead-resp-≈ᵉ Y (EqC.symmetric EventSim e) E m) (h Y E m qE qm le)

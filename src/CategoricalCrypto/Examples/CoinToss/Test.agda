{-# OPTIONS --safe --without-K --guardedness #-}

-- Acceptance instance for the composed statement: the attack the composition
-- is about, and the ceiling it runs into.
--
-- `bias` is a corrupted committer that waits for the honest share and then
-- opens to a DIFFERENT bit — it commits to `H(true ∷ r)` and opens at the
-- share `s`, which forces P2's output to `s xor s`, i.e. constantly `false`.
-- In the ideal-`F_com` world that opening is refused whenever `s ≢ true`, so
-- the whole of the attack's advantage sits inside the commitment's own
-- extraction bound, and `Compose.composed-ε` says the composition carries that
-- bound UNRESCALED: `(q² + 2q)·2⁻ᵏ`, evaluated below at `k = q = 3`.
--
-- `bias-round` is the witness that the word the trace statement quantifies
-- over is inhabited by a live run — `Examples.HashForward.UC.sim-round`'s role
-- here, and the same chain.
--
-- The SECOND hop adds nothing to that ceiling (`ideal-bound`), and its two
-- live rounds say what it rests on: the ideal coin leaks its bit before it
-- delivers it, and the joint simulator publishes exactly the share that makes
-- the hybrid's `b₁ xor share` land on that bit.

open import Data.Bool.Base using (Bool; true; _xor_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using () renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Data.Vec.Base using (Vec) renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound using (behᵍ; traceᵍ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.CoinToss.Test where

open import CategoricalCrypto.Examples.CoinToss 3
open import CategoricalCrypto.Examples.CoinToss.Compose using (composed-ε; εᶜᵗ)
open import CategoricalCrypto.Examples.CoinToss.Hiding 3
open import CategoricalCrypto.Examples.CoinToss.Ideal 3
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose using (ideal-ε; εᶜⁱ)
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver 3
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose using (ideal-εʳ; εᶜʳ)
open import CategoricalCrypto.Examples.ROCommitment 3
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic using (εᶜ)
open import CategoricalCrypto.Examples.ROCommitment.Extraction 3 using (Dig; Pt)
open import CategoricalCrypto.Examples.ROCommitment.Hiding 3
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic using (εᵗ)

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- The ceiling

-- `(3² + 2·3)·2⁻³`, and it is the COMMITMENT's schedule at the same allowance:
-- the coin-toss stage costs the test one activation and no more.
attack-bound : εᶜᵗ εᶜ 3 3 ≡ fromℕ 15 *ℚ inv-pow-2 3
attack-bound = composed-ε 3 3

-- …and the same ceiling for the whole statement: the hop to the ideal coin is
-- exact, so it contributes `0ℚ`.
ideal-bound : εᶜⁱ εᶜ 3 3 ≡ fromℕ 15 *ℚ inv-pow-2 3
ideal-bound = ideal-ε 3 3

-- At the corrupted RECEIVER the second hop is not exact — the two worlds
-- sample at different activations — and what it adds is the one positive
-- slack that carrying a run agreement into a context costs.
ideal-boundʳ : εᶜʳ εᵗ 3 3 ≡ fromℕ 9 *ℚ inv-pow-2 3 +ℚ inv-pow-2 3
ideal-boundʳ = ideal-εʳ 3 3

------------------------------------------------------------------------
-- The ideal coin, and the simulator that lands the toss on it

-- `sampleᵏ` draws the bit and hands it over; only then does `deliverᵏ` release
-- it to the honest party.  That order is what makes Blum's protocol
-- simulatable at all (`Examples.CoinToss.Ideal`).
coin-round : (c : Bool)
           → traceᵍ {unitᴵ} {Lkᴵᶜ ⊗ᴵ Honᴵᶜ} FSt (returnₚ freshᵏ) coinStep (heldᵏ c)
               (inj₂ (inj₁ deliverᵏ) ∷ [])
             ≈ₚ returnₚ (inj₂ (inj₂ (tossedᶜ c)) ∷ [])
coin-round c = >>=ₚ-identityˡ (doneᵏ , inj₂ (inj₂ (tossedᶜ c))) _
           ⟨≈⟩ >>=ₚ-identityˡ [] _

-- The joint simulator's round: told `commitˢ b₁` it buys the coin, told the
-- coin `c` it publishes `shareᴬ (b₁ xor c)` — the share that forces the
-- hybrid's output `b₁ xor share` to be `c` — and told `openˢ` it delivers.
sim-round : (b₁ c : Bool)
          → behᵍ {Lkᴵᶜ} {Lkᴵ ⊗ᴵ Advᴵᶜ} JSt (returnₚ (preʲ [])) jStep
              (inj₂ (inj₁ (commitˢ b₁)) ∷ inj₁ (coinᵏ c) ∷ inj₂ (inj₁ openˢ) ∷ [])
            ≈ₚ returnₚ ( inj₁ sampleᵏ
                       ∷ inj₂ (inj₂ (shareᴬ (b₁ xor c)))
                       ∷ inj₁ deliverᵏ ∷ [] )
sim-round b₁ c =
    >>=ₚ-identityˡ (preʲ []) _
  ⟨≈⟩ >>=ₚ-identityˡ (askʲ [] b₁ , inj₁ sampleᵏ) _
  ⟨≈⟩ map-arg _ afterCoin
  ⟨≈⟩ >>=ₚ-identityˡ _ _
  where
  afterOpen : traceᵍ {Lkᴵᶜ} {Lkᴵ ⊗ᴵ Advᴵᶜ} JSt (returnₚ (preʲ [])) jStep (midʲ [])
                (inj₂ (inj₁ openˢ) ∷ [])
              ≈ₚ returnₚ (inj₁ deliverᵏ ∷ [])
  afterOpen = >>=ₚ-identityˡ (endʲ [] , inj₁ deliverᵏ) _ ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterCoin : traceᵍ {Lkᴵᶜ} {Lkᴵ ⊗ᴵ Advᴵᶜ} JSt (returnₚ (preʲ [])) jStep (askʲ [] b₁)
                (inj₁ (coinᵏ c) ∷ inj₂ (inj₁ openˢ) ∷ [])
              ≈ₚ returnₚ (inj₂ (inj₂ (shareᴬ (b₁ xor c))) ∷ inj₁ deliverᵏ ∷ [])
  afterCoin = >>=ₚ-identityˡ (midʲ [] , inj₂ (inj₂ (shareᴬ (b₁ xor c)))) _
            ⟨≈⟩ map-arg _ afterOpen ⟨≈⟩ >>=ₚ-identityˡ _ _

------------------------------------------------------------------------
-- …and at the other corruption

-- `Fcoinʰ` releases the bit only after the simulator has bought it, exactly
-- as `Fcoin` does; what it leaks first is that the honest committer started.
coin-roundʰ : (c : Bool)
            → traceᵍ {unitᴵ} {Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ} FStʰ (returnₚ freshᵏʰ) coinStepʰ (heldᵏʰ c)
                (inj₂ (inj₂ getᶜ) ∷ [])
              ≈ₚ returnₚ (inj₂ (inj₂ (tossedᶜʰ c)) ∷ [])
coin-roundʰ c = >>=ₚ-identityˡ (doneᵏʰ , inj₂ (inj₂ (tossedᶜʰ c))) _
            ⟨≈⟩ >>=ₚ-identityˡ [] _

-- The joint simulator's round: it publishes the receipt, buys the coin at the
-- corrupted receiver's share `b₂`, and reports `bitᶠ (c xor b₂)` — the bit
-- that makes the hybrid's `b₁ xor b₂` the coin's own `c`.
sim-roundʰ : (b₂ c : Bool)
           → behᵍ {Lkᴵᶜʰ} {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ} JStʰ (returnₚ (preʲʰ [])) jStepʰ
               (inj₁ startᵏʰ ∷ inj₂ (inj₂ (shareᴬʰ b₂)) ∷ inj₁ (coinᵏʰ c) ∷ [])
             ≈ₚ returnₚ ( inj₂ (inj₁ rcptᶠ) ∷ inj₁ sampleᵏʰ
                        ∷ inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [] )
sim-roundʰ b₂ c =
    >>=ₚ-identityˡ (preʲʰ []) _
  ⟨≈⟩ >>=ₚ-identityˡ (midʲʰ [] , inj₂ (inj₁ rcptᶠ)) _
  ⟨≈⟩ map-arg _ afterStart
  ⟨≈⟩ >>=ₚ-identityˡ _ _
  where
  afterCoin : traceᵍ {Lkᴵᶜʰ} {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ} JStʰ (returnₚ (preʲʰ [])) jStepʰ
                (askʲʰ [] b₂) (inj₁ (coinᵏʰ c) ∷ [])
              ≈ₚ returnₚ (inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [])
  afterCoin = >>=ₚ-identityˡ (endʲʰ [] , inj₂ (inj₁ (bitᶠ (c xor b₂)))) _
            ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterStart : traceᵍ {Lkᴵᶜʰ} {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ} JStʰ (returnₚ (preʲʰ [])) jStepʰ (midʲʰ [])
                 (inj₂ (inj₂ (shareᴬʰ b₂)) ∷ inj₁ (coinᵏʰ c) ∷ [])
               ≈ₚ returnₚ (inj₁ sampleᵏʰ ∷ inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [])
  afterStart = >>=ₚ-identityˡ (askʲʰ [] b₂ , inj₁ sampleᵏʰ) _
             ⟨≈⟩ map-arg _ afterCoin ⟨≈⟩ >>=ₚ-identityˡ _ _

------------------------------------------------------------------------
-- The attack

-- A corrupted committer has to be woken by something: it hears the
-- commitment's answers and the honest share on its own two ports and speaks
-- first, so its codomain carries exactly one letter and no answer.
Startᴵ : Iface
Startᴵ = ⊥ ⇿ ⊤

data BSt : Set where
  asleepᵇ : BSt
  askedᵇ  : BSt
  heldᵇ   : Dig → BSt
  doneᵇ   : BSt

module _ (r : Vec Bool 3) where

  biasStep : BSt × (Pos (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Neg Startᴵ)
           → Dₚ (BSt × (Neg (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Pos Startᴵ))
  biasStep (s , inj₂ tt)                     = case s of λ where
    asleepᵇ → returnₚ (askedᵇ , inj₁ (inj₁ (queryᴬ (true ∷ᵛ r))))
    _       → botₚ
  biasStep (s , inj₁ (inj₁ (ansᴬ d)))        = case s of λ where
    askedᵇ → returnₚ (heldᵇ d , inj₁ (inj₁ (commitᴬ d)))
    _      → botₚ
  biasStep (s , inj₁ (inj₂ (shareᴬ b₂)))     = case s of λ where
    (heldᵇ _) → returnₚ (doneᵇ , inj₁ (inj₁ (openᴬ b₂ r)))
    _         → botₚ

  stateᵇ : State
  stateᵇ = record { obj = BSt ; point = λ _ → returnₚ asleepᵇ ; discard = λ _ → returnₚ ttᵛ }

  bias : Proc (Advᴵ ⊗ᴵ Advᴵᶜ) Startᴵ
  bias = mk stateᵇ biasStep

  -- One live round: woken, it queries `true ∷ r`; answered `d`, it commits to
  -- `d`; told the share `b₂`, it opens at `b₂` — a bit it did not commit to
  -- unless `b₂ ≡ true`, which is exactly the extraction bound's bad event.
  round : Dig → Bool → List (Pos (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Neg Startᴵ)
  round d b₂ = inj₂ tt ∷ inj₁ (inj₁ (ansᴬ d)) ∷ inj₁ (inj₂ (shareᴬ b₂)) ∷ []

  bias-round : (d : Dig) (b₂ : Bool)
             → behᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep (round d b₂)
               ≈ₚ returnₚ ( inj₁ (inj₁ (queryᴬ (true ∷ᵛ r)))
                          ∷ inj₁ (inj₁ (commitᴬ d))
                          ∷ inj₁ (inj₁ (openᴬ b₂ r)) ∷ [] )
  bias-round d b₂ =
      >>=ₚ-identityˡ asleepᵇ _
    ⟨≈⟩ >>=ₚ-identityˡ (askedᵇ , inj₁ (inj₁ (queryᴬ (true ∷ᵛ r)))) _
    ⟨≈⟩ map-arg _ afterAns
    ⟨≈⟩ >>=ₚ-identityˡ _ _
    where
    afterOpen : traceᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep (heldᵇ d)
                  (inj₁ (inj₂ (shareᴬ b₂)) ∷ [])
                ≈ₚ returnₚ (inj₁ (inj₁ (openᴬ b₂ r)) ∷ [])
    afterOpen = >>=ₚ-identityˡ (doneᵇ , inj₁ (inj₁ (openᴬ b₂ r))) _
              ⟨≈⟩ >>=ₚ-identityˡ [] _

    afterAns : traceᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep askedᵇ
                 (inj₁ (inj₁ (ansᴬ d)) ∷ inj₁ (inj₂ (shareᴬ b₂)) ∷ [])
               ≈ₚ returnₚ (inj₁ (inj₁ (commitᴬ d)) ∷ inj₁ (inj₁ (openᴬ b₂ r)) ∷ [])
    afterAns = >>=ₚ-identityˡ (heldᵇ d , inj₁ (inj₁ (commitᴬ d))) _
             ⟨≈⟩ map-arg _ afterOpen ⟨≈⟩ >>=ₚ-identityˡ _ _

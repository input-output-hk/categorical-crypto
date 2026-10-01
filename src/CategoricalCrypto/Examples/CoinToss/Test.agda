{-# OPTIONS --safe --without-K --guardedness #-}

-- Acceptance instances for the composed statements: their schedules where they
-- bite, and one live round of each ideal coin and joint simulator, read
-- through `UC.QueryBound.behᴾ` at the processes the theorems name.
--
-- The schedules are pinned at security parameter 5 and three queries; at the
-- machines' own `k = 3` all three are at least 1 (15/8, 15/8 and 5/4), so a
-- pin there would test the arithmetic only.

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.List.Base
open import Data.Product.Base
open import Data.Rational using (_/_)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.CoinToss.Test where

open import CategoricalCrypto.Examples.CoinToss 3
open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Hiding 3
open import CategoricalCrypto.Examples.CoinToss.Ideal 3
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver 3
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose
open import CategoricalCrypto.Examples.ROCommitment 3
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding 3
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic

------------------------------------------------------------------------
-- The schedules

attack-bound : εᶜᵗ εᶜ 5 3 ≡ + 15 / 32
attack-bound = refl

ideal-bound : εᶜⁱ εᶜ 5 3 ≡ + 15 / 32
ideal-bound = refl

ideal-boundʳ : εᶜʳ εᵗ 5 3 ≡ + 5 / 16
ideal-boundʳ = refl

------------------------------------------------------------------------
-- The ideal coin, and the simulator that lands the toss on it

coin-round : behᴾ Fcoin (inj₂ (inj₁ sampleᵏ) ∷ inj₂ (inj₁ deliverᵏ) ∷ [])
             ≈ₚ (coinₚ uniform-Bool >>=ₚ λ c →
                   returnₚ (inj₂ (inj₁ (coinᵏ c)) ∷ inj₂ (inj₂ (tossedᶜ c)) ∷ []))
coin-round =
      >>=ₚ-identityˡ freshᵏ _
  ⟨≈⟩ >>=ₚ-assoc (coinₚ uniform-Bool) _ _
  ⟨≈⟩ bindᶠ λ c → >>=ₚ-identityˡ (heldᵏ c , inj₂ (inj₁ (coinᵏ c))) _
              ⟨≈⟩ map-arg _ (>>=ₚ-identityˡ (doneᵏ , inj₂ (inj₂ (tossedᶜ c))) _
                             ⟨≈⟩ >>=ₚ-identityˡ [] _)
              ⟨≈⟩ >>=ₚ-identityˡ _ _

sim-round : (b₁ c : Bool)
          → behᴾ simJ
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
  afterOpen : traceᵍ JSt (returnₚ (preʲ [])) jStep (midʲ [])
                (inj₂ (inj₁ openˢ) ∷ [])
              ≈ₚ returnₚ (inj₁ deliverᵏ ∷ [])
  afterOpen = >>=ₚ-identityˡ (endʲ [] , inj₁ deliverᵏ) _ ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterCoin : traceᵍ JSt (returnₚ (preʲ [])) jStep (askʲ [] b₁)
                (inj₁ (coinᵏ c) ∷ inj₂ (inj₁ openˢ) ∷ [])
              ≈ₚ returnₚ (inj₂ (inj₂ (shareᴬ (b₁ xor c))) ∷ inj₁ deliverᵏ ∷ [])
  afterCoin = >>=ₚ-identityˡ (midʲ [] , inj₂ (inj₂ (shareᴬ (b₁ xor c)))) _
            ⟨≈⟩ map-arg _ afterOpen ⟨≈⟩ >>=ₚ-identityˡ _ _

------------------------------------------------------------------------
-- …and at the other corruption

coin-roundʰ : behᴾ Fcoinʰ (inj₂ (inj₂ goᶜ) ∷ inj₂ (inj₁ sampleᵏʰ) ∷ inj₂ (inj₂ getᶜ) ∷ [])
              ≈ₚ (coinₚ uniform-Bool >>=ₚ λ c →
                    returnₚ (inj₂ (inj₁ startᵏʰ) ∷ inj₂ (inj₁ (coinᵏʰ c))
                             ∷ inj₂ (inj₂ (tossedᶜʰ c)) ∷ []))
coin-roundʰ =
      >>=ₚ-identityˡ freshᵏʰ _
  ⟨≈⟩ >>=ₚ-identityˡ (waitᵏʰ , inj₂ (inj₁ startᵏʰ)) _
  ⟨≈⟩ map-arg _ afterGo
  ⟨≈⟩ map-bind (coinₚ uniform-Bool) _ (inj₂ (inj₁ startᵏʰ) ∷_)
  ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)
  where
  afterGo : traceᵍ FStʰ (returnₚ freshᵏʰ) coinStepʰ waitᵏʰ
              (inj₂ (inj₁ sampleᵏʰ) ∷ inj₂ (inj₂ getᶜ) ∷ [])
            ≈ₚ (coinₚ uniform-Bool >>=ₚ λ c →
                  returnₚ (inj₂ (inj₁ (coinᵏʰ c)) ∷ inj₂ (inj₂ (tossedᶜʰ c)) ∷ []))
  afterGo =
        >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ λ c → >>=ₚ-identityˡ (heldᵏʰ c , inj₂ (inj₁ (coinᵏʰ c))) _
                ⟨≈⟩ map-arg _ (>>=ₚ-identityˡ (doneᵏʰ , inj₂ (inj₂ (tossedᶜʰ c))) _
                               ⟨≈⟩ >>=ₚ-identityˡ [] _)
                ⟨≈⟩ >>=ₚ-identityˡ _ _

sim-roundʰ : (b₂ c : Bool)
           → behᴾ simJʰ
               (inj₁ startᵏʰ ∷ inj₂ (inj₂ (shareᴬʰ b₂)) ∷ inj₁ (coinᵏʰ c) ∷ [])
             ≈ₚ returnₚ ( inj₂ (inj₁ rcptᶠ) ∷ inj₁ sampleᵏʰ
                        ∷ inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [] )
sim-roundʰ b₂ c =
    >>=ₚ-identityˡ (preʲʰ []) _
  ⟨≈⟩ >>=ₚ-identityˡ (midʲʰ [] , inj₂ (inj₁ rcptᶠ)) _
  ⟨≈⟩ map-arg _ afterStart
  ⟨≈⟩ >>=ₚ-identityˡ _ _
  where
  afterCoin : traceᵍ JStʰ (returnₚ (preʲʰ [])) jStepʰ
                (askʲʰ [] b₂) (inj₁ (coinᵏʰ c) ∷ [])
              ≈ₚ returnₚ (inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [])
  afterCoin = >>=ₚ-identityˡ (endʲʰ [] , inj₂ (inj₁ (bitᶠ (c xor b₂)))) _
            ⟨≈⟩ >>=ₚ-identityˡ [] _

  afterStart : traceᵍ JStʰ (returnₚ (preʲʰ [])) jStepʰ (midʲʰ [])
                 (inj₂ (inj₂ (shareᴬʰ b₂)) ∷ inj₁ (coinᵏʰ c) ∷ [])
               ≈ₚ returnₚ (inj₁ sampleᵏʰ ∷ inj₂ (inj₁ (bitᶠ (c xor b₂))) ∷ [])
  afterStart = >>=ₚ-identityˡ (askʲʰ [] b₂ , inj₁ sampleᵏʰ) _
             ⟨≈⟩ map-arg _ afterCoin ⟨≈⟩ >>=ₚ-identityˡ _ _

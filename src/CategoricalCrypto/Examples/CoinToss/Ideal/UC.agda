{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop at the UC model: the joint simulator's query certificate, and
-- `Examples.CoinToss.Ideal.Machine.coin-machine` read across the seal through
-- `UC.Graded`'s coercions for a composed system: `ext-graded` for the stage on
-- top, `graded₂-∘` for the resource under it, `sub-graded₂` for the simulator.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Base using (_∘′_)
open import Level

open import Categories.Category
open import Categories.LocallyGraded.SubCategory

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Graded
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

open import CategoricalCrypto.Machines.Base

module CategoricalCrypto.Examples.CoinToss.Ideal.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.CoinToss.Ideal k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Machine k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open GradedSubCat gradingᵒ using (Pred)
open HomReasoning

private module M = Category (𝒢ₚ 0ℓ)

simJCert : Certified 1 simJ
simJCert = qbᵢ-upward _ _ _ onL cohL
  where
  Aᵍ : ℕ → Set
  Aᵍ = Ans (λ _ → 0) (Neg Lkᴵᶜ) (Pos (Lkᴵ ⊗ᴵ Advᴵᶜ))

  onL : (s : JSt) (a : Pos Lkᴵᶜ) → Dₚ (Aᵍ 0)
  onL (preʲ _)    (coinᵏ _) = botₚ
  onL (askʲ t b₁) (coinᵏ c) = returnₚ (inj₂ ((midʲ t , z≤n) , inj₂ (shareᴬ (b₁ xor c))))
  onL _ _                   = botₚ

  cohL : (s : JSt) (a : Pos Lkᴵᶜ) → mapₚ forget (onL s a) ≈ₚ jStep (s , inj₁ a)
  cohL (preʲ _)   (coinᵏ _) = bot-bind-≈ₚ _
  cohL (askʲ _ _) (coinᵏ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (midʲ _)   (coinᵏ _) = bot-bind-≈ₚ _
  cohL (endʲ _)   (coinᵏ _) = bot-bind-≈ₚ _

simJQB : Pred 1⁺ (gradedᵒ simJ)
simJQB = qb-gradedᵒ (certified⇒QB simJCert)

coin-hop : (ext (ifaceᵒ Lkᴵ) (gradedᵒ toss) ∘ gradedᵒ ideal) ∘ procᵒ resource
           ≈ sub (gradedᵒ simJ) ∘ gradedᵒ Fcoin
coin-hop =
       ∘-resp-≈ˡ (ext-graded toss ideal)
  ○    graded₂-∘ (M._∘_ a⇐ᴵ (M._∘_ (T₁ᴵ Lkᴵ toss) ideal)) resource
  ○    ≈ᴹ⇒≈ᵍ₂ coin-machine
  ○    Equiv.sym (sub-graded₂ simJ Fcoin)

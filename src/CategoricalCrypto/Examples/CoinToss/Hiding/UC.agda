{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver coin-toss stage at the UC model, with the certificate
-- `UC-composeᵉ` demands: each activation from above buys exactly one downward
-- message (`commitᴱ`/`openᴱ`) and nothing is owed afterwards, so it is
-- `Certified 1` at potential 0.  The honest committer's is
-- `Examples.ROCommitment.Hiding.UC.comCert`.

open import Categories.LocallyGraded.SubCategory

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Base

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.CoinToss.Hiding.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open GradedSubCat gradingᵒ using (Pred)

tossʰᵒ : ifaceᵒ Honᴵʰ ⇒ T₀ (ifaceᵒ Advᴵᶜʰ) (ifaceᵒ Honᴵᶜʰ)
tossʰᵒ = gradedᵒ tossʰ

------------------------------------------------------------------------
-- One drive of `F_com` per activation from above

tossʰCert : Certified 1 tossʰ
tossʰCert = qbᵢ-upward _ _ _ onL cohL
  where
  onL : (s : QSt) (a : Pos Honᴵʰ) → Dₚ (Ans (λ _ → 0) (Neg Honᴵʰ) (Pos (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)) 0)
  onL (comᵗ _)    nakᴱ = returnₚ (inj₂ ((doneᵗ , z≤n) , inj₂ abortedᶜʰ))
  onL (openᵗ _ _) nakᴱ = returnₚ (inj₂ ((doneᵗ , z≤n) , inj₂ abortedᶜʰ))
  onL _ _              = botₚ

  cohL : (s : QSt) (a : Pos Honᴵʰ) → mapₚ forget (onL s a) ≈ₚ τStep (s , inj₁ a)
  cohL (comᵗ _)    nakᴱ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (openᵗ _ _) nakᴱ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL freshᵗ      nakᴱ = bot-bind-≈ₚ _
  cohL doneᵗ       nakᴱ = bot-bind-≈ₚ _

tossʰQB : Pred 1⁺ tossʰᵒ
tossʰQB = qb-gradedᵒ (certified⇒QB tossʰCert)

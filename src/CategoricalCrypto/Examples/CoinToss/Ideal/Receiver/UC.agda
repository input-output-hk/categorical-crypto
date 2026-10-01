{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver hop at the UC model: the joint simulator's query
-- certificate, and the two sides of `Receiver.Machine.coin-runʰ` read as
-- graded homs.  Both are also regraded (`UC.Graded.regrade`) from
-- `ifaceᵒ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)` to `ifaceᵒ Lkᴵʰ ⊗₀ ifaceᵒ Advᴵᶜʰ`: `dominatedᵍ`
-- is stated at the first shape and `_∙ᶠ_` produces the second.

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
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Graded
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Machine k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open GradedSubCat gradingᵒ using (Pred)
open HomReasoning

private module M = Category (𝒢ₚ 0ℓ)

------------------------------------------------------------------------
-- The joint simulator spends one call per activation

simJʰCert : Certified 1 simJʰ
simJʰCert = qbᵢ-upward _ _ _ onL cohL
  where
  Aᵍ : ℕ → Set
  Aᵍ = Ans (λ _ → 0) (Neg Lkᴵᶜʰ) (Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))

  onL : (s : JStʰ) (a : Pos Lkᴵᶜʰ) → Dₚ (Aᵍ 0)
  onL (preʲʰ t)    startᵏʰ    = returnₚ (inj₂ ((midʲʰ t , z≤n) , inj₁ rcptᶠ))
  onL (preʲʰ _)    (coinᵏʰ _) = botₚ
  onL (midʲʰ _)    startᵏʰ    = botₚ
  onL (midʲʰ _)    (coinᵏʰ _) = botₚ
  onL (askʲʰ _ _)  startᵏʰ    = botₚ
  onL (askʲʰ t b₂) (coinᵏʰ c) =
    returnₚ (inj₂ ((endʲʰ t , z≤n) , inj₁ (bitᶠ (c xor b₂))))
  onL _ _                     = botₚ

  cohL : (s : JStʰ) (a : Pos Lkᴵᶜʰ) → mapₚ forget (onL s a) ≈ₚ jStepʰ (s , inj₁ a)
  cohL (preʲʰ _)   startᵏʰ    = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (preʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _
  cohL (midʲʰ _)   startᵏʰ    = bot-bind-≈ₚ _
  cohL (midʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _
  cohL (askʲʰ _ _) startᵏʰ    = bot-bind-≈ₚ _
  cohL (askʲʰ _ _) (coinᵏʰ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (endʲʰ _)   startᵏʰ    = bot-bind-≈ₚ _
  cohL (endʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _

simJʰQB : Pred 1⁺ (gradedᵒ simJʰ)
simJʰQB = qb-gradedᵒ (certified⇒QB simJʰCert)

flatʰ : ifaceᵒ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ) ⇒ ifaceᵒ Lkᴵʰ ⊗₀ ifaceᵒ Advᴵᶜʰ
flatʰ = flatᵍ

flatʰQB : Pred 1⁺ flatʰ
flatʰQB = qb-gradedᵒ qb-idᴹ

------------------------------------------------------------------------
-- The two sides, regraded

hyb-flatʰ : sub flatʰ ∘ gradedᵒ hybridᴹʰ
            ≈ (ext (ifaceᵒ Lkᴵʰ) (gradedᵒ tossʰ) ∘ gradedᵒ idealʰ) ∘ procᵒ resource
hyb-flatʰ =
       regrade hybridᴹʰ
  ○ Equiv.sym ( ∘-resp-≈ˡ (ext-graded tossʰ idealʰ)
              ○ graded₂-∘ (M._∘_ a⇐ᴵ (M._∘_ (T₁ᴵ Lkᴵʰ tossʰ) idealʰ)) resource )

idl-flatʰ : sub flatʰ ∘ gradedᵒ idealᴹʰ ≈ sub (gradedᵒ simJʰ) ∘ gradedᵒ Fcoinʰ
idl-flatʰ = regrade idealᴹʰ ○ Equiv.sym (sub-graded₂ simJʰ Fcoinʰ)

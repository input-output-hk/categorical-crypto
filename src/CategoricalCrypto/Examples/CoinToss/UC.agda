{-# OPTIONS --safe --without-K --guardedness #-}

-- The coin-toss stage at the UC model, and its query certificate for
-- `UC.Quantitative.Family.≤UC[]-compose`: the stage makes no downward call at all
-- (`tossCert`; see `Examples.CoinToss`); the receiver's is
-- `Examples.ROCommitment.UC.recvCert`.  The grading's rates are positive, so the
-- stage enters it at `1⁺`.

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.CoinToss.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k

open GradedSubCat gradingᵒ using (Pred)

tossᵒ : ifaceᵒ Honᴵ ⇒ T₀ (ifaceᵒ Advᴵᶜ) (ifaceᵒ Honᴵᶜ)
tossᵒ = gradedᵒ toss

tossCert : Certified 0 toss
tossCert = qbᵢ-noDown _ _ _ λ ()

tossQB : Pred 1⁺ tossᵒ
tossQB = qb-gradedᵒ (qb-mono z≤n (certified⇒QB tossCert))

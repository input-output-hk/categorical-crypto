{-# OPTIONS --safe --without-K --guardedness #-}

-- What the ledger costs its hash: one call per activation, hence `QB 1`.
--
-- `submit` hashes once and `audit` answers purely, so `System.ledger`'s step is
-- `fromCall` of the `Call` below on the nose — which is exactly the hypothesis
-- of `UC.QueryBound.qb-oneCall`, where the certificate is built and where the
-- reason it cannot be read off `Protocol.Machine.MSt` is recorded.

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.ChimericLedger.QueryBound where

module _ (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

  open Ledger ℓ
  open Step ser
  open import CategoricalCrypto.Examples.ChimericLedger.System ℓ ser

  ledgerCall : (vr : Variant) → LState → Query → Call (Neg HashIf) (Pos HashIf) (LState × Answer)
  ledgerCall vr s (submit tx) =
    reCall (fzero ,_) proj₂ (mapCall (λ sb → proj₁ sb , ok (proj₂ sb)) (applyTx vr s tx))
  ledgerCall _  s audit       = pureᶜ (s , totalIs (total s))

  qb-ledger : (vr : Variant) (s₀ : LState) → QB 1 (morphism (ledger vr s₀))
  qb-ledger vr s₀ = qb-oneCall (ledger vr s₀) (ledgerCall vr) factors
    where
    factors : (s : LState) (q : Query) → step (ledger vr s₀) s q ≡ fromCall (ledgerCall vr s q)
    factors _ (submit _) = refl
    factors _ audit      = refl

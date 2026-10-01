{-# OPTIONS --safe --without-K #-}

-- One-shot oracle calls: a computation that either answers outright or asks its
-- oracle ONCE and continues with the reply — the shape a protocol step has when
-- written as ordinary Agda (`CategoricalCrypto.Protocol.fromCall` embeds it).

open import Data.Product.Base
open import Data.Sum.Base

module CategoricalCrypto.OracleCall where

private variable Q Q′ R R′ A B : Set

Call : (Q R A : Set) → Set
Call Q R A = A ⊎ (Q × (R → A))

pureᶜ : A → Call Q R A
pureᶜ = inj₁

callᶜ : Q → (R → A) → Call Q R A
callᶜ q k = inj₂ (q , k)

runCall : (Q → R) → Call Q R A → A
runCall _ (inj₁ a)       = a
runCall o (inj₂ (q , k)) = k (o q)

mapCall : (A → B) → Call Q R A → Call Q R B
mapCall f (inj₁ a)       = inj₁ (f a)
mapCall f (inj₂ (q , k)) = inj₂ (q , λ r → f (k r))

-- Re-index the oracle's channel: tag the query, untag the reply.  This is what
-- puts a bitstring-keyed call onto a party-indexed random-oracle interface.
reCall : (Q → Q′) → (R′ → R) → Call Q R A → Call Q′ R′ A
reCall _ _ (inj₁ a)       = inj₁ a
reCall f g (inj₂ (q , k)) = inj₂ (f q , λ r → k (g r))

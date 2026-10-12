{-# OPTIONS --safe --without-K --guardedness #-}

-- Environment-selected, one-send symmetric channel.  The fixed-public-message
-- example remains in CategoricalCrypto.Symbolic.Example.SecureChannel.
module CategoricalCrypto.Symbolic.Example.SecureChannel.Interactive where

open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol public
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Security public
  using (smt≈simulated; smt≤ideal)
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Ideal public
  using (simulated≈ideal-simulator)
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Negative public
  using (leaky≉simulated; leaky≉real)
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Tests public
  using (accepts-arbitrary-environment-plaintext; delivers-arbitrary-selected-plaintext;
         arbitrary-delivery-trace; drop-trace; no-post-delivery-activation)

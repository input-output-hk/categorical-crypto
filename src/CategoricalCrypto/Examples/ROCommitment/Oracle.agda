{-# OPTIONS --safe --without-K #-}

-- The lazily sampled oracle the two closed `F_com` games run on.
--
-- A tabulated point is answered from the table; a fresh one draws a uniform
-- digest and keeps it.  The two games hold that table inside different states,
-- so the kernel takes the embedding `g` of the post-table into the game's own
-- state: `fetchT id` is the bare table `Hiding.Game` reads, `fetchT (_, m)` the
-- table-plus-ancilla `Game` does.  Taking `g` rather than mapping the result
-- afterwards is what keeps the kernel REDUCING under the games' `E-bind`
-- rewrites — a `Dmap` in front of it would not.

open import Data.List.Base using (_∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Vec)

module CategoricalCrypto.Examples.ROCommitment.Oracle (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k

fetchT : {A : Set} → (Tbl → A) → Tbl → Pt → Dist-ℚ (A × Dig)
fetchT g t x with lookupPt t x
... | just d  = return-ℚ (g t , d)
... | nothing = uniform-Vec k >>=ᴹ λ h → return-ℚ (g ((x , h) ∷ t) , h)

{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Computed pins: at 1-bit hashes the whole system — the lazily sampled
-- compression oracle, the protocol composition, the chaining, the ℚ
-- arithmetic — runs by `refl`.
--
-- The pins are chosen so that nothing here is vacuous.  At ONE block the real
-- and ideal worlds are literally the same experiment and `bound 1` is `0ℚ`:
-- the bound is TIGHT there, and a pin says so.  At TWO blocks the chaining is
-- visible — two messages sharing their second block collide whenever their
-- first chaining values do, which at a 1-bit hash is half the time — so the
-- real world's collision probability is 3/4 against the ideal's 1/2.  That
-- ¼ gap is the reason `bound` grows with the block count, and it is pinned
-- against the bound itself.
--
-- Warm single-module typecheck: ~6 s (measured 2026-09-10, `+RTS -M3G -H1G`).
--------------------------------------------------------------------------------

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Fin.Base using (zero)
open import Data.Integer.Base using () renaming (+_ to +ℤ_)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Rational using (0ℚ; 1ℚ; _/_) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_; head)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Examples.MerkleDamgard
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.MerkleDamgard.Pin where

------------------------------------------------------------------------
-- One block: the two worlds are the same experiment

module OneBlock where

  open MD 1 1 (false ∷ []) public

  -- Hash one message and report the single output bit.
  hash : Vec Bool 1 → Strat (Neg Generalᴵ) (Pos Generalᴵ)
  hash m = ask (zero , m) λ a → out (head (proj₂ a))

  hash-asks : (m : Vec Bool 1) → asks≤ 1 (hash m)
  hash-asks _ _ = tt

  -- A fresh message hashes to a uniform bit, in both worlds.
  real-uniform : Pr Sys (hash (false ∷ [])) ≡ +ℤ 1 / 2
  real-uniform = refl

  ideal-uniform : Pr general (hash (false ∷ [])) ≡ +ℤ 1 / 2
  ideal-uniform = refl

  -- Ask the same message twice: both worlds answer consistently.
  twice : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  twice = ask (zero , false ∷ []) λ a →
          ask (zero , false ∷ []) λ b →
          out (not (head (proj₂ a) xor head (proj₂ b)))

  real-consistent : Pr Sys twice ≡ 1ℚ
  real-consistent = refl

  ideal-consistent : Pr general twice ≡ 1ℚ
  ideal-consistent = refl

  -- `bound 1` is `0ℚ` at one block, and the advantage really is zero: the
  -- theorem is tight here rather than vacuously satisfied.
  bound-1 : bound 1 ≡ 0ℚ
  bound-1 = refl

  tight : ∣ Pr general (hash (false ∷ [])) -ℚ Pr Sys (hash (false ∷ [])) ∣ℚ ≡ 0ℚ
  tight = refl

------------------------------------------------------------------------
-- Two blocks: the chaining is observable

module TwoBlocks where

  open MD 1 2 (false ∷ []) public

  -- Two messages differing only in their FIRST block.  Their second
  -- compression calls carry the same block at the same index, so they hit the
  -- same table entry exactly when the first calls returned the same chaining
  -- value — at a 1-bit hash, half the time.
  collide : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  collide = ask (zero , false ∷ false ∷ []) λ a →
            ask (zero , true  ∷ false ∷ []) λ b →
            out (not (head (proj₂ a) xor head (proj₂ b)))

  collide-asks : asks≤ 2 collide
  collide-asks _ _ = tt

  -- ½ (first chaining values agree) + ½·½ (they do not, fresh coincidence).
  real-collides : Pr Sys collide ≡ +ℤ 3 / 4
  real-collides = refl

  -- The variable-length oracle answers two distinct messages independently.
  ideal-collides : Pr general collide ≡ +ℤ 1 / 2
  ideal-collides = refl

  -- The gap the chaining costs, and the bound that pays for it.
  gap : ∣ Pr general collide -ℚ Pr Sys collide ∣ℚ ≡ +ℤ 1 / 4
  gap = refl

  bound-2 : bound 2 ≡ +ℤ 3 / 1
  bound-2 = refl

  -- Both queries repeated: every compression call is a table hit the second
  -- time round, so the two worlds agree with probability 1.
  replay : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  replay = ask (zero , true ∷ false ∷ []) λ a →
           ask (zero , true ∷ false ∷ []) λ b →
           out (not (head (proj₂ a) xor head (proj₂ b)))

  real-replay : Pr Sys replay ≡ 1ℚ
  real-replay = refl

  ideal-replay : Pr general replay ≡ 1ℚ
  ideal-replay = refl


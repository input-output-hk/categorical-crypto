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
-- ¼ gap is the reason `bound` grows with the block count.  The two-block
-- bound itself is pinned too, but `bound 2 ≡ 3 > 1`, so the theorem is
-- vacuous at those parameters and that pin exercises the arithmetic only.
--------------------------------------------------------------------------------

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.Integer.Base using () renaming (+_ to +ℤ_)
open import Data.Product.Base
open import Data.Rational renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist.Advantage

open import CategoricalCrypto.Examples.MerkleDamgard
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.MerkleDamgard.Pin where

------------------------------------------------------------------------
-- One block: the two worlds are the same experiment

module OneBlock where

  open MD 1 1 (false ∷ []) public

  hash : Vec Bool 1 → Strat (Neg Generalᴵ) (Pos Generalᴵ)
  hash m = ask (zero , m) λ a → out (head (proj₂ a))

  hash-asks : (m : Vec Bool 1) → asks≤ 1 (hash m)
  hash-asks _ _ = tt

  real-uniform : Pr Sys (hash (false ∷ [])) ≡ +ℤ 1 / 2
  real-uniform = refl

  ideal-uniform : Pr general (hash (false ∷ [])) ≡ +ℤ 1 / 2
  ideal-uniform = refl

  twice : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  twice = ask (zero , false ∷ []) λ a →
          ask (zero , false ∷ []) λ b →
          out (not (head (proj₂ a) xor head (proj₂ b)))

  real-consistent : Pr Sys twice ≡ 1ℚ
  real-consistent = refl

  ideal-consistent : Pr general twice ≡ 1ℚ
  ideal-consistent = refl

  bound-1 : bound 1 ≡ 0ℚ
  bound-1 = refl

  tight : ∣ Pr general (hash (false ∷ [])) -ℚ Pr Sys (hash (false ∷ [])) ∣ℚ ≡ 0ℚ
  tight = refl

  hash-bounded : advᵇ⊥ false (runObs general (hash (false ∷ [])))
                             (runObs Sys (hash (false ∷ []))) ≤ℚ bound 1
  hash-bounded = indistinguishable false 1 (hash (false ∷ [])) (hash-asks (false ∷ []))

------------------------------------------------------------------------
-- Two blocks: the chaining is observable

module TwoBlocks where

  open MD 1 2 (false ∷ []) public

  collide : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  collide = ask (zero , false ∷ false ∷ []) λ a →
            ask (zero , true  ∷ false ∷ []) λ b →
            out (not (head (proj₂ a) xor head (proj₂ b)))

  collide-asks : asks≤ 2 collide
  collide-asks _ _ = tt

  -- ½ (first chaining values agree) + ½·½ (they do not, fresh coincidence).
  real-collides : Pr Sys collide ≡ +ℤ 3 / 4
  real-collides = refl

  ideal-collides : Pr general collide ≡ +ℤ 1 / 2
  ideal-collides = refl

  gap : ∣ Pr general collide -ℚ Pr Sys collide ∣ℚ ≡ +ℤ 1 / 4
  gap = refl

  bound-2 : bound 2 ≡ +ℤ 3 / 1
  bound-2 = refl

  collide-bounded : advᵇ⊥ true (runObs general collide) (runObs Sys collide) ≤ℚ bound 2
  collide-bounded = indistinguishable true 2 collide collide-asks

  replay : Strat (Neg Generalᴵ) (Pos Generalᴵ)
  replay = ask (zero , true ∷ false ∷ []) λ a →
           ask (zero , true ∷ false ∷ []) λ b →
           out (not (head (proj₂ a) xor head (proj₂ b)))

  real-replay : Pr Sys replay ≡ 1ℚ
  real-replay = refl

  ideal-replay : Pr general replay ≡ 1ℚ
  ideal-replay = refl


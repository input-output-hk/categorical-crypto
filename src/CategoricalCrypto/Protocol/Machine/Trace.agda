{-# OPTIONS --safe --without-K --guardedness #-}

-- `Protocol.Machine.Raw`'s hypothesis discharged at a TRACED machine, which is
-- the shape every composite of the G construction has.
--
-- `Machines.Trace.traceStep` is `solve ∘ k ∘ id ⊗₁ i₁`: the letter goes in on
-- the external summand, the body acts, and `solve` either lets the emission out
-- or feeds it back round `iterₚ`.  Each of those three is a junction
-- `Dp.Settle` already closes — the two wirings are pure, so `Settles-ret⋆`
-- takes them one step at a time — except the loop, which is
-- `Dp.Settle.Iter.Settles-iter` and needs its round-trip bound.
--
-- Everything here is built at the literal `traceStep` term.  It has to be:
-- `Settles` carries a syntactic `Halts`, `_≈ₚ_` is equality of suprema, and a
-- supremum can be approached without being reached — so no `Settles` fact rides
-- `Dp.Reasoning`'s rearrangements, `Machines.Pointwise`'s calculus or
-- `Machines.Sim`'s `_≈ᴹ_`.  What makes that affordable is that the trace's step
-- IS the bind chain below, definitionally (`Protocol.Machine.Compose`'s
-- `trace-pt`/`solve-pt` start their `≈ₚ` chains at exactly these terms).

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Kleisli.Discrete as KD

open import Data.Nat.Base using (ℕ; suc; _<_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Settle.Iter

open import CategoricalCrypto.Machines.Base

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Protocol.Machine.Trace where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})

module _ (S : MC.State) (A B X : Set)
         (k  : MC.obj S × (A ⊎ X) → Dₚ (MC.obj S × (B ⊎ X)))
         (Kk : MC.obj S × (A ⊎ X) → Dist⊥ (MC.obj S × (B ⊎ X)))
         (kS : (z : MC.obj S × (A ⊎ X)) → Σ[ i ∈ ℕ ] Settles i (k z) (Kk z))
  where

  -- `id ⊗₁ pureᵏ h` at a point is three `returnₚ`s and nothing else.
  private
    ⊗S : {Y Z : Set} (h : Y → Z) (m : MC.obj S) (y : Y)
       → Σ[ i ∈ ℕ ] Settles i ((V.id V.⊗₁ K.pureᵏ h) (m , y)) (return⊥ (m , h y))
    ⊗S h m y = Settles-ret⋆ m _ (return⊥ (m , h y))
                 (Settles-ret⋆ (h y) _ (return⊥ (m , h y)) (1 , Settles-return (m , h y)))

    -- One pass of the loop: the same junction, then the body.
    lbS : (w : MC.obj S × X)
        → Σ[ i ∈ ℕ ] Settles i (MT.loopBody S A B X k w) (Kk (proj₁ w , inj₂ (proj₂ w)))
    lbS (m , x) =
      let i , s = ⊗S inj₂ m x
          j , t = Settles-bind⋆ i _ k (return⊥ (m , inj₂ x)) Kk s kS
      in j , Settles-resp (return⊥ (m , inj₂ x) >>=⊥ Kk) (Kk (m , inj₂ x))
                          (λ Q → >>=⊥-identityˡ (m , inj₂ x) Kk (maybeℚ Q)) t

  module I = Loop (MT.loopBody S A B X k) (λ w → Kk (proj₁ w , inj₂ (proj₂ w))) lbS
  open I using (loopK; exitK)

  -- The round-trip bound, at a rank the whole state space respects: for these
  -- machines it is the number of messages the upper factor has still to bounce
  -- off the lower one, and `f` is its maximum plus one.
  module _ (rank : MC.obj S × X → ℕ) (rk : I.Ranked rank)
           (f : ℕ) (rb : (w : MC.obj S × X) → rank w < f) where

    private
      solveS : (r : MC.obj S × (B ⊎ X))
             → Σ[ i ∈ ℕ ] Settles i (MT.solve S A B X k r) (exitK f r)
      solveS (m , inj₁ b) =
        Settles-ret⋆ (inj₁ (m , b)) _ (return⊥ (m , b)) (1 , Settles-return (m , b))
      solveS (m , inj₂ x) =
        Settles-ret⋆ (inj₂ (m , x)) _ (loopK f (m , x))
                     (I.Settles-iter rank rk f (m , x) (rb (m , x)))

    -- The kernel a traced step settles on: the body's, then the loop's exit.
    Ktrace : MC.obj S × A → Dist⊥ (MC.obj S × B)
    Ktrace z = Kk (proj₁ z , inj₁ (proj₂ z)) >>=⊥ exitK f

    trace-settles : (z : MC.obj S × A)
                  → Σ[ i ∈ ℕ ] Settles i (MT.traceStep S A B X k z) (Ktrace z)
    trace-settles (m , a) =
      let i , s = ⊗S inj₁ m a
          j , t = Settles-bind⋆ i _ k (return⊥ (m , inj₁ a)) Kk s kS
          l , v = Settles-bind⋆ j _ (MT.solve S A B X k)
                                (return⊥ (m , inj₁ a) >>=⊥ Kk) (exitK f) t solveS
      in l , Settles-resp ((return⊥ (m , inj₁ a) >>=⊥ Kk) >>=⊥ exitK f)
                          (Ktrace (m , a)) value v
      where
      value : (Q : MC.obj S × B → ℚ)
            → E⊥ ((return⊥ (m , inj₁ a) >>=⊥ Kk) >>=⊥ exitK f) Q ≡ E⊥ (Ktrace (m , a)) Q
      value Q = >>=⊥-congʳ (exitK f) (return⊥ (m , inj₁ a) >>=⊥ Kk) (Kk (m , inj₁ a))
                           (>>=⊥-identityˡ (m , inj₁ a) Kk) (maybeℚ Q)

{-# OPTIONS --safe --without-K #-}

-- Boundary tests distinguish positive-probability activation outcomes from
-- zero-weight leaves and the abort sink; reachability is not tree membership.

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
import Data.Rational as ℚ
import Data.Rational.Properties as ℚₚ
import Data.Rational.Properties.Ext as ℚₑ
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
import CategoricalCrypto.Protocol.Reachability

module CategoricalCrypto.Protocol.ReachabilityTests where

module RandomCounter where
  private
    next : Bool → ℕ → ℕ
    next false n = suc n
    next true  n = suc (suc n)

  P : Protocol unitᴵ (Bool ⇿ ⊤)
  P = record
    { St = ℕ × Bool
    ; init = 0 , false
    ; step = λ (n , flag) _ → coin uniform-Bool λ b → ret ((next b n , flag) , b)
    }

  module R = CategoricalCrypto.Protocol.Reachability P
  open R

  initial : Reachable (0 , false)
  initial = start

  false-branch : Reachable (1 , false)
  false-branch = advance {q = tt} initial (Any.here (0<inv-pow-2 1 , refl))

  true-branch : Reachable (2 , false)
  true-branch = advance {q = tt} initial (Any.there (Any.here (0<inv-pow-2 1 , refl)))

  two-activations : Reachable (3 , false)
  two-activations = advance {q = tt} false-branch
    (Any.there (Any.here (0<inv-pow-2 1 , refl)))

  FlagClear : St P → Set
  FlagClear s = proj₂ s ≡ false

  flag-preserved : Preserved⊥ FlagClear (kernel P)
  flag-preserved (n , flag) tt clear = evalC-support (step P (n , flag) tt) (λ _ → clear)

  reachable-flag-clear : ∀ {s} → Reachable s → FlagClear s
  reachable-flag-clear = reachable-invariant flag-preserved refl

  flagged-state-unreachable : ∀ n → ¬ Reachable (n , true)
  flagged-state-unreachable n reached with reachable-flag-clear reached
  ... | ()

module ZeroBranch where
  -- The forbidden target occurs in the representation, but has weight zero.
  biased : Dist-ℚ Bool
  biased = mk-Dist ((ℚ.1ℚ , false) NE.∷ (ℚ.0ℚ , true) ∷ []) refl
    (ℚₑ.0≤1ℚ All.∷ ℚₚ.≤-refl All.∷ All.[])

  P : Protocol unitᴵ (⊤ ⇿ ⊤)
  P = record
    { St = Bool
    ; init = false
    ; step = λ _ _ → coin biased λ b → ret (b , tt)
    }

  module R = CategoricalCrypto.Protocol.Reachability P
  open R

  zero-weight-no-successor : ∀ s → ¬ InSupport (just (true , tt)) (kernel P s tt)
  zero-weight-no-successor s (Any.here (_ , ()))
  zero-weight-no-successor s (Any.there (Any.here (positive , _))) = ℚₚ.<-irrefl refl positive
  zero-weight-no-successor s (Any.there (Any.there ()))

  zero-weight-unreachable : ¬ Reachable true
  zero-weight-unreachable (advance {s = s} reached member) = zero-weight-no-successor s member

module Abort where
  P : Protocol unitᴵ (⊤ ⇿ ⊤)
  P = record { St = ℕ ; init = 0 ; step = λ _ _ → dead }

  module R = CategoricalCrypto.Protocol.Reachability P
  open R

  abort-no-successor : ∀ s t → ¬ InSupport (just (t , tt)) (kernel P s tt)
  abort-no-successor s t member with support-return member
  ... | ()

  only-initial : ∀ {s} → Reachable s → s ≡ 0
  only-initial start = refl
  only-initial (advance {s = s} {t = t} reached member) = ⊥-elim (abort-no-successor s t member)

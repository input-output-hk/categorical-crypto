{-# OPTIONS --safe --without-K --guardedness #-}

-- Machines read at interfaces (`Proc`), and the closed run of one against a
-- strategy (`runᴹ`).  A closed machine is a `Proc unitᴵ B`: both polarities of
-- `unitᴵ` are empty, and the initial state is `point`, which at a Kleisli base
-- is itself effectful.

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Machines.Run where

private variable B : Iface

-- A `𝒢ₚ`-hom read at interfaces: `Machine (A⁺ + B⁻) (A⁻ + B⁺)`, a process that
-- answers queries from above and issues queries below.  Spelled with `_⊎_`
-- rather than as `𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]` (definitionally the same): an
-- implicit inferred from the hom form is `𝒢ₚ`'s object sum, under which sits
-- the δ-unfolded Mealy category record, and every term mentioning it carries
-- that copy (`UC.Machine.Monitor.flag-agree`: 2.4 → 1.2 GiB residency).
Proc : Iface → Iface → Set₁
Proc A B = MC.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)

module _ (M : Proc unitᴵ B) where

  -- Named rather than `where`-local so that a lemma about a run can quantify
  -- over it (`Machines.Run.Sim.resume-ϕ`).
  resumeᴹ : (MC.St M → Pos B → Dₚ Bool) → MC.St M × (⊥ ⊎ Pos B) → Dₚ Bool
  resumeᴹ c (_  , inj₁ a) = ⊥-elim a
  resumeᴹ c (m′ , inj₂ r) = c m′ r

  runᴹFrom : MC.St M → Strat (Neg B) (Pos B) → Dₚ Bool
  runᴹFrom m (out b)    = returnₚ b
  runᴹFrom m (coin μ k) = coinₚ μ >>=ₚ λ b → runᴹFrom m (k b)
  runᴹFrom m (ask q k)  =
    MC.step M (m , inj₂ q) >>=ₚ resumeᴹ λ m′ r → runᴹFrom m′ (k r)

  runᴹ : Strat (Neg B) (Pos B) → Dₚ Bool
  runᴹ d = MC.point (MC.state M) tt >>=ₚ λ m → runᴹFrom m d

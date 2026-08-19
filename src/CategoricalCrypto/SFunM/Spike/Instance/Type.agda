{-# OPTIONS --safe --without-K #-}

-- SPIKE: the general Mealy layer instantiated at `Klᴹ` for the possibility
-- monad, and the certificate that it recovers the elementwise layer.
--
-- The pins below say that at this instance the general layer's kernel is
-- *literally* `CategoricalCrypto.SFunM`'s: `Machine.step` has type
-- `SFunType A B S`, and `pow` is the n-fold `×`.  The one real divergence is the
-- state's packaging: `Machine` carries a `point : ⊤ → M S` and a
-- `discard : S → M ⊤` where `SFunᵉ` carries a pure `init : S`.

open import categorical-crypto.Prelude hiding (_>>=_; return)

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Monad.Setoids.Discrete as Discrete

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Spike.KleisliDiscrete as KD
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
open import ProbabilisticLogic.Distribution.Possibility

module CategoricalCrypto.SFunM.Spike.Instance.Type where

open Discrete (𝒫-KleisliTriple {0ℓ})
open KD (𝒫-KleisliTriple {0ℓ}) 𝒫-commutative
open Mealy Klᴹ-SymmetricMonoidal
open SymmetricMonoidalCategory Klᴹ-SymmetricMonoidal using (_⊗₀_; _⇒_)
open SFun (𝒫-KleisliTriple {0ℓ}) using (SFunType; SFunᵉ; mkᵉ)
open Machine
open State

private variable A B S Msg : Type

------------------------------------------------------------------------
-- The kernel

-- The type of `Machine.step`, unfolded.  At the discrete setoids the possibility
-- monad is `List` on the nose, so the general layer's kernel at `Klᴹ` is the
-- elementwise layer's kernel on TYPES — see `Examples.Possibilistic.kernel-on-Types`.
kernel-on-Types : (S ⊗₀ A ⇒ S ⊗₀ B) ≡ (S × A → List (S × B))
kernel-on-Types = refl

-- Same fact stated so that it is `Machine.step` itself being ascribed the
-- elementwise kernel type.
stepᵏ : (f : Machine A B) → SFunType A B (St f)
stepᵏ = step

-- `pow` is the n-fold `×` ending in the unit, `⊤ᵏ = Lift 0ℓ ⊤`.
pow-suc : (n : ℕ) → pow (suc n) A ≡ (A × pow n A)
pow-suc _ = refl

pow-on-Types : pow 2 A ≡ (A × A × ⊤ᵏ)
pow-on-Types = refl

------------------------------------------------------------------------
-- The state's packaging

-- Here the general layer really does diverge from `SFunᵉ`: an initial state is a
-- *morphism* out of the unit, so a set of states rather than a single one, and
-- the final state is dropped by a morphism into the unit rather than by
-- projection.  Neither is forced: `⊤ᵏ` is neither initial nor terminal in `Klᴹ`
-- (`A → M ⊤ᵏ` is `A → List (Lift ⊤)`), so `Mealy.agda`'s remark that the discard
-- is unique holds at `Setoids`, not here.
pointᵏ : (T : State) → ⊤ᵏ → M (obj T)
pointᵏ = point

discardᵏ : (T : State) → obj T → M ⊤ᵏ
discardᵏ = discard

fromSFunᵉ : SFunᵉ A B → Machine A B
fromSFunᵉ f = record
  { state = record { obj = F.State ; point = pureᵏ (const F.init) ; discard = pureᵏ (const (lift tt)) }
  ; step  = F.fun
  }
  where module F = SFunᵉ f

-- The reverse direction is not a function: `point` is a set of initial states,
-- so one of them has to be supplied.
toSFunᵉ : (f : Machine A B) → obj (state f) → SFunᵉ A B
toSFunᵉ f s = mkᵉ s (step f)

------------------------------------------------------------------------
-- An example machine

-- `Examples.Possibilistic.Cut`, written directly in the general layer: the
-- adversary decides once and for all whether messages are forwarded
-- (state = `just true`) or dropped (state = `just false`).
Cutᴹ : Machine (Maybe Msg) (Maybe Msg)
Cutᴹ = record
  { state = record { obj = Maybe Bool ; point = pureᵏ (const nothing) ; discard = pureᵏ (const (lift tt)) }
  ; step  = λ where
      (nothing    , m) → (just true , m) ∷ (just false , nothing) ∷ []
      (just true  , m) → return (just true , m)
      (just false , _) → return (just false , nothing)
  }

-- The general `eval` still computes on closed inputs: every structural shuffle
-- (`swp`, `tuck`, `slot₁`, `slot₂`, the unitors) is a `return` of a function, so
-- two rounds of `Cutᴹ` reduce to a literal two-element list.
eval-Cutᴹ : {m₁ m₂ : Msg} → eval Cutᴹ 2 (just m₁ , just m₂ , lift tt)
          ≡ ((just m₁ , just m₂ , lift tt) ∷ (nothing , nothing , lift tt) ∷ [])
eval-Cutᴹ = refl

-- …hence also up to `_≈ᴹ_`, which at the possibility monad is list set equality.
eval-Cutᴹ-set : {m₁ m₂ : Msg} → eval Cutᴹ 2 (just m₁ , just m₂ , lift tt)
              ≈ᴹ ((just m₁ , just m₂ , lift tt) ∷ (nothing , nothing , lift tt) ∷ [])
eval-Cutᴹ-set = ≈ᴹ.reflexive eval-Cutᴹ

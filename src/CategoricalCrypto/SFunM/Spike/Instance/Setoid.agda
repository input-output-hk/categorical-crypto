{-# OPTIONS --safe --without-K #-}

-- SPIKE: the general Mealy layer at the *full* Kleisli category of a `Setoids`
-- monad — objects are arbitrary setoids and a machine kernel is a setoid map
-- into `Maybe`.  Unlike `Spike.Instance.Type`, which runs on the hand-rolled
-- `Spike.KleisliDiscrete`, the symmetric monoidal structure here is entirely
-- upstream: `Setoids-Monoidal` + `Cartesian.SymmetricMonoidal` for the base and
-- `Monoidal.Construction.Kleisli{,.Symmetric}` for the bridge, fed the
-- `CommutativeMonad` of `Spike.CommutativeMaybe`.
--
-- The pins say what the general layer unfolds to here.  Two things are new
-- relative to the elementwise `SFunᵉ`: the initial state is a Kleisli map out of
-- the unit, so it may *fail*; and the discrete setoids are not closed under the
-- tensor on the nose (`≡-setoid S ×ₛ ≡-setoid A` carries `Pointwise _≡_ _≡_`,
-- not `_≡_`), which is what `kernelᶠ` bridges.

open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Construction.Kleisli using (Kleisli-Monoidal)
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric using (Kleisli-Symmetric)
open import Categories.Monad.Setoids.Maybe using (Maybe-KleisliTriple)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as Pw
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_; ≡×≡⇒≡)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (0ℓ) renaming (suc to lsuc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

import CategoricalCrypto.SFunM.Kleisli as SFun
open import CategoricalCrypto.SFunM.Spike.CommutativeMaybe 0ℓ
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Instance.Setoid where

𝒱 : SymmetricMonoidalCategory (lsuc 0ℓ) 0ℓ 0ℓ
𝒱 = record
  { U         = Kleisli Maybe-Monad
  ; monoidal  = Kleisli-Monoidal Setoids-Symmetric Maybe-CommutativeMonad
  ; symmetric = Kleisli-Symmetric Setoids-Symmetric Maybe-CommutativeMonad
  }

open Mealy 𝒱
open Machine
open State
open SymmetricMonoidalCategory 𝒱 using (Obj; _⇒_; _⊗₀_; unit)
open SFun Maybe-KleisliTriple using (SFunType; SFunᵉ)

private variable A B S Msg : Set

------------------------------------------------------------------------
-- The kernel

-- A Kleisli hom is a setoid map into `Maybe`, and the tensor is `_×ₛ_`, so a
-- `Machine`'s kernel is a setoid map `S ×ₛ A ⟶ Maybe (S ×ₛ B)`.
kernel-on-Setoids : {S A B : Obj} → (S ⊗₀ A ⇒ S ⊗₀ B) ≡ Func (S ×ₛ A) (Pw.setoid (S ×ₛ B))
kernel-on-Setoids = refl

-- Same fact, with `Machine.step` itself ascribed the unfolded type.
stepᶠ : {A B : Obj} (f : Machine A B) → Func (St f ×ₛ A) (Pw.setoid (St f ×ₛ B))
stepᶠ = step

-- The elementwise layer's kernel is the same thing at the *discrete* setoids,
-- stripped of the `cong`: `SFunM`'s `M` is `Maybe` on the nose.
kernel-on-Types : SFunType A B S ≡ (S × A → Maybe (S × B))
kernel-on-Types = refl

-- …but the discrete setoids are not closed under the tensor, so an elementwise
-- kernel is not a `Machine.step`: this is the bridge, and `≡×≡⇒≡` is its only
-- content.
kernelᶠ : (S × A → Maybe (S × B)) → ≡-setoid S ⊗₀ ≡-setoid A ⇒ ≡-setoid S ⊗₀ ≡-setoid B
kernelᶠ {S = S} {A = A} {B = B} k = record { to = k ; cong = λ p≈q → congᶠ (≡×≡⇒≡ p≈q) }
  where
  congᶠ : {p q : S × A} → p ≡ q
        → Setoid._≈_ (Pw.setoid (≡-setoid S ×ₛ ≡-setoid B)) (k p) (k q)
  congᶠ refl = Pw.refl (refl , refl)

------------------------------------------------------------------------
-- Tensor powers

pow-zero : {A : Obj} → pow 0 A ≡ unit
pow-zero = refl

pow-suc : {A : Obj} (n : ℕ) → pow (suc n) A ≡ (A ×ₛ pow n A)
pow-suc _ = refl

-- `unit` is the one-point setoid `SingletonSetoid`, whose carrier is the
-- polymorphic `⊤`; so the carrier of a tensor power is an `n`-tuple.
pow-carrier : {A : Obj} → Setoid.Carrier (pow 2 A) ≡ (Setoid.Carrier A × Setoid.Carrier A × ⊤)
pow-carrier = refl

------------------------------------------------------------------------
-- The state's packaging

-- A `point` is a Kleisli map out of the unit — a *possibly failing* initial
-- state, where `SFunᵉ` has a pure `init : State`.
pointᶠ : (T : State) → Func unit (Pw.setoid (obj T))
pointᶠ = point

-- A `discard` is data, and at general setoids it is not unique either: `unit` is
-- terminal in `Setoids` but not in `Kleisli Maybe-Monad`, where `T ⇒ unit` is
-- `T → Maybe ⊤`.  `SFunᵉ` has no such field.
discardᶠ : (T : State) → Func (obj T) (Pw.setoid unit)
discardᶠ = discard

pureᵖ : (s : S) → unit ⇒ ≡-setoid S
pureᵖ s = record { to = const (just s) ; cong = λ _ → Pw.just refl }

dropᵈ : {T : Obj} → T ⇒ unit
dropᵈ = record { to = const (just tt) ; cong = λ _ → Pw.just tt }

fromSFunᵉ : SFunᵉ A B → Machine (≡-setoid A) (≡-setoid B)
fromSFunᵉ f = record
  { state = record { obj = ≡-setoid F.State ; point = pureᵖ F.init ; discard = dropᵈ }
  ; step  = kernelᶠ F.fun
  }
  where module F = SFunᵉ f

-- The reverse direction is not a function, and for two independent reasons: the
-- state object of a `Machine` need not be discrete, and even when it is, `point`
-- is a `Maybe`-valued map, so it need not name an initial state at all.
--
-- Nor do the two hom equalities line up: `_≈ᵉ_` here is
-- `∀ n → eval f n ≈ eval g n` at the tensor powers, where the elementwise one is
-- `∀ xs → eval f xs ≈ᴹ eval g xs` over `List A`.  Relating them needs an
-- iso `pow n (≡-setoid A) ≅ ≡-setoid (Vec A n)` in `Kleisli Maybe-Monad` plus a
-- `Vec`/`List` reindexing of `trace`; that is left open here.

------------------------------------------------------------------------
-- An example machine

-- A partial cut: the first round commits to forwarding (state `just true`) or to
-- dropping (state `just false`) according to whether it carries a message, and
-- every later round honours that commitment — the dropping branch by *failing*,
-- which is the structure `Examples.Possibilistic.Cut` cannot express (there the
-- adversary's choice is nondeterminism, here it is the input).
Cutᴹ : Machine (≡-setoid (Maybe Msg)) (≡-setoid (Maybe Msg))
Cutᴹ = record
  { state = record { obj = ≡-setoid (Maybe Bool) ; point = pureᵖ nothing ; discard = dropᵈ }
  ; step  = kernelᶠ λ where
      (nothing    , just m)  → just (just true , just m)
      (nothing    , nothing) → just (just false , nothing)
      (just true  , m)       → just (just true , m)
      (just false , _)       → nothing
  }

-- The general `eval` still computes on closed inputs: `Kleisli` composition goes
-- through `μ ∘ F₁ f` rather than `extend f`, but the two agree on a literal
-- `Maybe`, and every structural morphism of `Kleisli-Monoidal` is a `just` of a
-- function.
eval-Cutᴹ-forward : {m₁ m₂ : Msg}
  → eval Cutᴹ 2 ⟨$⟩ (just m₁ , just m₂ , tt) ≡ just (just m₁ , just m₂ , tt)
eval-Cutᴹ-forward = refl

-- The non-trivial fact: an idle first round commits the machine to dropping, and
-- the commitment then kills the whole run.
eval-Cutᴹ-fail : {m : Msg} → eval Cutᴹ 2 ⟨$⟩ (nothing , just m , tt) ≡ nothing
eval-Cutᴹ-fail = refl

-- Two cuts in series are one cut, at this input: the shape `_∘ᴹ_` needs — the
-- paired state, `onL`/`onR` and hence `swp` — computes here too.
eval-Cutᴹ-∘ : {m₁ m₂ : Msg}
  → eval (Cutᴹ ∘ᴹ Cutᴹ) 2 ⟨$⟩ (just m₁ , just m₂ , tt)
  ≡ eval Cutᴹ 2 ⟨$⟩ (just m₁ , just m₂ , tt)
eval-Cutᴹ-∘ = refl

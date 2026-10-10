{-# OPTIONS --safe --without-K --guardedness #-}

-- A simulation is invisible to a run.
--
-- `Machines.Sim`'s generator carries a PURE state map, so the simulating
-- machine's step differs from the simulated one's only in a state factor the
-- run discards.  Hence a run against a strategy — a closed observation among
-- them, being a run at the closed alphabet (`runᴹ≈runˢ`) — is a function of
-- the machine category's own hom equality, which is what makes the UC layer's
-- `⟦⟧-resp-≈` a theorem rather than a field, and the only place where the
-- machine layer's equality has to be reconciled with `Dₚ`'s.

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level
open import Relation.Binary.Structures
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (fnStep; padϕ)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy

import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Run where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module P = KDP (Dₚ-DiscreteMonad {0ℓ})
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable X Y : Set

------------------------------------------------------------------------
-- A run against a strategy, at any alphabet (maurer2002 Def 9)

module _ (M : MC.Machine X Y) where

  resumeˢ : (MC.St M → Y → Dₚ Bool) → MC.St M × Y → Dₚ Bool
  resumeˢ c (m′ , y) = c m′ y

  runFromˢ : MC.St M → Strat X Y → Dₚ Bool
  runFromˢ m (out b)    = returnₚ b
  runFromˢ m (coin μ k) = coinₚ μ >>=ₚ λ b → runFromˢ m (k b)
  runFromˢ m (ask x k)  = MC.step M (m , x) >>=ₚ resumeˢ λ m′ y → runFromˢ m′ (k y)

  runˢ : Strat X Y → Dₚ Bool
  runˢ d = MC.point (MC.state M) tt >>=ₚ λ m → runFromˢ m d

------------------------------------------------------------------------
-- The induction, over a state map and its step law

-- A state map and the law relating the two steps through it is ALL the
-- induction on the strategy tree spends, so it is parameterized by that pair
-- rather than by a simulation.
module _ {f g : MC.Machine X Y} (ϕ : MC.St f → MC.St g)
         (step-law : (p : MC.St f × X)
                   → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p))
         where

  runFromˢ-ϕ : (m : MC.St f) (d : Strat X Y) → runFromˢ f m d ≈ₚ runFromˢ g (ϕ m) d
  runFromˢ-ϕ m (out b)    = ≈refl
  runFromˢ-ϕ m (coin μ k) = bindᶠ (λ b → runFromˢ-ϕ m (k b))
  runFromˢ-ϕ m (ask x k)  =
      bindᶠ {l = λ p → resumeˢ g contᵍ (ϕ (proj₁ p) , proj₂ p)}
            (λ p → runFromˢ-ϕ (proj₁ p) (k (proj₂ p)))
    ⟨≈⟩ ≈sym (bindᶠ (λ p → >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p) (resumeˢ g contᵍ)))
    ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.step f (m , x)) (padϕ ϕ) (resumeˢ g contᵍ))
    ⟨≈⟩ bindˣ (step-law (m , x))
    where
    contᵍ : MC.St g → Y → Dₚ Bool
    contᵍ m′ y = runFromˢ g m′ (k y)

------------------------------------------------------------------------
-- A closed run is a run at the closed alphabet

closeˢ : {B : Iface} → Strat (Neg B) (Pos B) → Strat (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)
closeˢ = mapStrat inj₂ [ ⊥-elim , id ]

module _ {B : Iface} (M : Closed B) where

  runᴹFrom≈runFromˢ : (m : MC.St M) (d : Strat (Neg B) (Pos B))
                    → runᴹFrom M m d ≈ₚ runFromˢ M m (closeˢ d)
  runᴹFrom≈runFromˢ m (out b)    = ≈refl
  runᴹFrom≈runFromˢ m (coin μ k) = bindᶠ (λ b → runᴹFrom≈runFromˢ m (k b))
  runᴹFrom≈runFromˢ m (ask q k)  = bindᶠ λ where
    (_  , inj₁ ())
    (m′ , inj₂ r) → runᴹFrom≈runFromˢ m′ (k r)

  runᴹ≈runˢ : (d : Strat (Neg B) (Pos B)) → runᴹ M d ≈ₚ runˢ M (closeˢ d)
  runᴹ≈runˢ d = bindᶠ (λ m → runᴹFrom≈runFromˢ m d)

module _ {B : Iface} {f g : Closed B} (ϕ : MC.St f → MC.St g)
         (step-law : (p : MC.St f × (⊥ ⊎ Neg B))
                   → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p))
         where

  runFrom-ϕ : (m : MC.St f) (d : Strat (Neg B) (Pos B))
            → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ m) d
  runFrom-ϕ m d = runᴹFrom≈runFromˢ f m d ⟨≈⟩ runFromˢ-ϕ ϕ step-law m (closeˢ d)
              ⟨≈⟩ ≈sym (runᴹFrom≈runFromˢ g (ϕ m) d)

------------------------------------------------------------------------
-- What a simulation supplies

module _ {f g : MC.Machine X Y} (sim : f S.≲ g) where

  ϕ : MC.St f → MC.St g
  ϕ = P.fn (S.θ-pure sim)

  step-sim : (p : MC.St f × X)
           → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
  step-sim = fnStep (S.θ-pure sim) (S.θ-step sim)

  point-sim : mapₚ ϕ (MC.point (MC.state f) tt) ≈ₚ MC.point (MC.state g) tt
  point-sim = bindᶠ (λ s → ≈sym (P.is-fn (S.θ-pure sim) s)) ⟨≈⟩ S.θ-point sim tt

  runˢ-sim : (d : Strat X Y) → runˢ f d ≈ₚ runˢ g d
  runˢ-sim d = bindᶠ (λ m → runFromˢ-ϕ ϕ step-sim m d)
         ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state f) tt) ϕ (λ m → runFromˢ g m d))
         ⟨≈⟩ bindˣ point-sim

module _ {X Y : Set} where

  private
    Runs : MC.Machine X Y → MC.Machine X Y → Set
    Runs f g = (d : Strat X Y) → runˢ f d ≈ₚ runˢ g d

    Runs-isEquivalence : IsEquivalence Runs
    Runs-isEquivalence = record
      { refl  = λ _ → ≈refl
      ; sym   = λ h d → ≈sym (h d)
      ; trans = λ h k d → h d ⟨≈⟩ k d
      }

  runˢ-resp-≈ᴹ : {f g : MC.Machine X Y} → f S.≈ᴹ g → (d : Strat X Y) → runˢ f d ≈ₚ runˢ g d
  runˢ-resp-≈ᴹ = EqC.fold Runs-isEquivalence runˢ-sim

------------------------------------------------------------------------
-- …hence a whole closed run is invisible to it

module _ {B : Iface} {f g : Closed B} (sim : f S.≲ g) where

  runFrom-sim : (m : MC.St f) (d : Strat (Neg B) (Pos B))
              → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ sim m) d
  runFrom-sim = runFrom-ϕ (ϕ sim) (step-sim sim)

  run-sim : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
  run-sim d = runᴹ≈runˢ f d ⟨≈⟩ runˢ-sim sim (closeˢ d) ⟨≈⟩ ≈sym (runᴹ≈runˢ g d)

-- Opaque: it is the readouts' `cong` (`UC.Machine`, `UC.Model.Observation`),
-- which importers' conversions unfold; transparent, `UC.Graded.≤UC[]ᵍ` ran past
-- 30 min (RS plan §6, step 2).
opaque
  runᴹ-resp-≈ᴹ : {B : Iface} {f g : Closed B} → f S.≈ᴹ g
               → (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
  runᴹ-resp-≈ᴹ {f = f} {g} e d =
    runᴹ≈runˢ f d ⟨≈⟩ runˢ-resp-≈ᴹ e (closeˢ d) ⟨≈⟩ ≈sym (runᴹ≈runˢ g d)

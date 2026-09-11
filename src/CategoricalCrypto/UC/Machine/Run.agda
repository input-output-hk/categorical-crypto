{-# OPTIONS --safe --without-K --guardedness #-}

-- A simulation is invisible to a closed run.
--
-- `Machines.Sim`'s generator carries a PURE state map, so the simulating
-- machine's step differs from the simulated one's only in a state factor the
-- run discards.  Hence a closed observation is a function of the machine
-- category's own hom equality, which is what makes the UC layer's
-- `⟦⟧-resp-≈` a theorem rather than a field, and the only place where the
-- machine layer's equality has to be reconciled with `Dₚ`'s.

open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.Structures
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy

import Categories.Category.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Run where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module P = KDP (Dₚ-DiscreteMonad {0ℓ})
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

-- A closed machine at an interface: nothing can be asked of its domain side.
Closed : Iface → Set₁
Closed B = MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)

padϕ : {Sf Sg Z : Set} → (Sf → Sg) → Sf × Z → Dₚ (Sg × Z)
padϕ ϕ p = returnₚ (ϕ (proj₁ p) , proj₂ p)

------------------------------------------------------------------------
-- The induction, over a state map and its step law

-- A state map and the law relating the two steps through it is ALL the
-- induction on the strategy tree spends, so it is parameterized by that pair
-- rather than by a simulation.  `Run.Lax` supplies the same pair from a lax
-- simulation and differs only at the point, which is why it shares this.
module _ {B : Iface} {f g : Closed B} (ϕ : MC.St f → MC.St g)
         (step-law : (p : MC.St f × (⊥ ⊎ Neg B))
                   → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p))
         where

  private
    contᵍ : (Pos B → Strat (Neg B) (Pos B)) → MC.St g → Pos B → Dₚ Bool
    contᵍ k m′ r = runᴹFrom g m′ (k r)

    resume-ϕ : {cᶠ : MC.St f → Pos B → Dₚ Bool} {cᵍ : MC.St g → Pos B → Dₚ Bool}
             → ((m′ : MC.St f) (r : Pos B) → cᶠ m′ r ≈ₚ cᵍ (ϕ m′) r)
             → (p : MC.St f × (⊥ ⊎ Pos B))
             → resumeᴹ f cᶠ p ≈ₚ resumeᴹ g cᵍ (ϕ (proj₁ p) , proj₂ p)
    resume-ϕ h (_  , inj₁ a) = ⊥-elim a
    resume-ϕ h (m′ , inj₂ r) = h m′ r

  runFrom-ϕ : (m : MC.St f) (d : Strat (Neg B) (Pos B))
            → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ m) d
  runFrom-ϕ m (out b)    = ≈refl
  runFrom-ϕ m (coin μ k) = bindᶠ (λ b → runFrom-ϕ m (k b))
  runFrom-ϕ m (ask q k)  =
      bindᶠ (resume-ϕ {cᵍ = contᵍ k} (λ m′ r → runFrom-ϕ m′ (k r)))
    ⟨≈⟩ ≈sym (bindᶠ (λ p → >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p)
                                          (resumeᴹ g (contᵍ k))))
    ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.step f (m , inj₂ q)) (padϕ ϕ) (resumeᴹ g (contᵍ k)))
    ⟨≈⟩ bindˣ (step-law (m , inj₂ q))

------------------------------------------------------------------------
-- What a simulation supplies

module _ {X Y : Set} {f g : MC.Machine X Y} (sim : f S.≲ g) where

  ϕ : MC.St f → MC.St g
  ϕ = P.fn (S.θ-pure sim)

  private
    pad : {Z : Set} → MC.St f × Z → Dₚ (MC.St g × Z)
    pad = S.θ sim V.⊗₁ V.id

    pad-fn : {Z : Set} (p : MC.St f × Z) → pad p ≈ₚ padϕ ϕ p
    pad-fn (s , z) = bindˣ (P.is-fn (S.θ-pure sim) s)
               ⟨≈⟩ >>=ₚ-identityˡ (ϕ s) _
               ⟨≈⟩ >>=ₚ-identityˡ z _

  step-sim : (p : MC.St f × X)
           → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
  step-sim p = bindᶠ (λ q → ≈sym (pad-fn q))
         ⟨≈⟩ S.θ-step sim p
         ⟨≈⟩ bindˣ (pad-fn p)
         ⟨≈⟩ >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p) (MC.step g)

  point-sim : mapₚ ϕ (MC.point (MC.state f) tt) ≈ₚ MC.point (MC.state g) tt
  point-sim = bindᶠ (λ s → ≈sym (P.is-fn (S.θ-pure sim) s)) ⟨≈⟩ S.θ-point sim tt

------------------------------------------------------------------------
-- …hence a whole closed run is invisible to it

module _ {B : Iface} {f g : Closed B} (sim : f S.≲ g) where

  runFrom-sim : (m : MC.St f) (d : Strat (Neg B) (Pos B))
              → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ sim m) d
  runFrom-sim = runFrom-ϕ (ϕ sim) (step-sim sim)

  run-sim : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
  run-sim d = bindᶠ (λ m → runFrom-sim m d)
        ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state f) tt) (ϕ sim) (λ m → runᴹFrom g m d))
        ⟨≈⟩ bindˣ (point-sim sim)

module _ {B : Iface} where

  private
    Runs : Closed B → Closed B → Set
    Runs f g = (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d

    Runs-isEquivalence : IsEquivalence Runs
    Runs-isEquivalence = record
      { refl  = λ _ → ≈refl
      ; sym   = λ h d → ≈sym (h d)
      ; trans = λ h k d → h d ⟨≈⟩ k d
      }

  runᴹ-resp-≈ᴹ : {f g : Closed B} → f S.≈ᴹ g
               → (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
  runᴹ-resp-≈ᴹ = EqC.fold Runs-isEquivalence run-sim

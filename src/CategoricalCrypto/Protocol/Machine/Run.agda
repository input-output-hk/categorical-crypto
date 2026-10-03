{-# OPTIONS --safe --without-K --guardedness #-}

-- A simulation is invisible to a closed run.
--
-- `Machines.Sim`'s generator carries a PURE state map, so the simulating
-- machine's step differs from the simulated one's only in a state factor the
-- run discards.  Hence a closed observation is a function of the machine
-- category's own hom equality, which is what makes the UC layer's
-- `UC.Model.Observation.obs-resp` a theorem rather than a field, and the only place where the
-- machine layer's equality has to be reconciled with `Dₚ`'s.

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
open import CategoricalCrypto.Machines.Pointwise using (padϕ; ϕ; step-sim; point-sim; module S)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy


module CategoricalCrypto.Protocol.Machine.Run where

------------------------------------------------------------------------
-- The induction, over a state map and its step law

-- A state map and the law relating the two steps through it is ALL the
-- induction on the strategy tree spends, so it is parameterized by that pair
-- rather than by a simulation.
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
-- …hence a whole closed run is invisible to it

module _ {B : Iface} {f g : Closed B} (sim : f S.≲ g) where

  run-sim : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
  run-sim d = bindᶠ (λ m → runFrom-ϕ (ϕ sim) (step-sim sim) m d)
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

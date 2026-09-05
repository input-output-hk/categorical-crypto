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
open import Function.Base
open import Level
open import Relation.Binary.Structures
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp

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

------------------------------------------------------------------------
-- `Dₚ` shorthands: the library's lemmas take their subjects explicitly, and a
-- transparent chain would strand them as metas.

private
  variable A′ B′ C′ : Set

  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ A′} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  ≈refl : {d : Dₚ A′} → d ≈ₚ d
  ≈refl {d = d} = ≈ₚ-refl d

  ≈sym : {d e : Dₚ A′} → d ≈ₚ e → e ≈ₚ d
  ≈sym {d = d} {e} = ≈ₚ-sym d e

  bindᶠ : {d : Dₚ A′} {k l : A′ → Dₚ B′}
        → ((a : A′) → k a ≈ₚ l a) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l ≈refl h

  bindˣ : {d e : Dₚ A′} {k : A′ → Dₚ B′} → d ≈ₚ e → (d >>=ₚ k) ≈ₚ (e >>=ₚ k)
  bindˣ {d = d} {e} {k} h = >>=ₚ-cong d e k k h λ _ → ≈refl

  bind-map : (d : Dₚ A′) (h : A′ → B′) (k : B′ → Dₚ C′)
           → (mapₚ h d >>=ₚ k) ≈ₚ (d >>=ₚ (k ∘′ h))
  bind-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) k
             ⟨≈⟩ bindᶠ (λ a → >>=ₚ-identityˡ (h a) k)

------------------------------------------------------------------------
-- What a simulation does to one step

module _ {X Y : Set} {f g : MC.Machine X Y} (sim : f S.≲ g) where

  ϕ : MC.St f → MC.St g
  ϕ = P.fn (S.θ-pure sim)

  padϕ : {Z : Set} → MC.St f × Z → Dₚ (MC.St g × Z)
  padϕ p = returnₚ (ϕ (proj₁ p) , proj₂ p)

  private
    pad : {Z : Set} → MC.St f × Z → Dₚ (MC.St g × Z)
    pad = S.θ sim V.⊗₁ V.id

    pad-fn : {Z : Set} (p : MC.St f × Z) → pad p ≈ₚ padϕ p
    pad-fn (s , z) = bindˣ (P.is-fn (S.θ-pure sim) s)
               ⟨≈⟩ >>=ₚ-identityˡ (ϕ s) _
               ⟨≈⟩ >>=ₚ-identityˡ z _

  step-sim : (p : MC.St f × X)
           → (MC.step f p >>=ₚ padϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
  step-sim p = bindᶠ (λ q → ≈sym (pad-fn q))
         ⟨≈⟩ S.θ-step sim p
         ⟨≈⟩ bindˣ (pad-fn p)
         ⟨≈⟩ >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p) (MC.step g)

  point-sim : mapₚ ϕ (MC.point (MC.state f) tt) ≈ₚ MC.point (MC.state g) tt
  point-sim = bindᶠ (λ s → ≈sym (P.is-fn (S.θ-pure sim) s)) ⟨≈⟩ S.θ-point sim tt

------------------------------------------------------------------------
-- …and to a whole closed run

module _ {B : Iface} {f g : Closed B} (sim : f S.≲ g) where

  private
    contᵍ : (Pos B → Strat (Neg B) (Pos B)) → MC.St g → Pos B → Dₚ Bool
    contᵍ k m′ r = runᴹFrom g m′ (k r)

  resume-sim : {cᶠ : MC.St f → Pos B → Dₚ Bool} {cᵍ : MC.St g → Pos B → Dₚ Bool}
             → ((m′ : MC.St f) (r : Pos B) → cᶠ m′ r ≈ₚ cᵍ (ϕ sim m′) r)
             → (p : MC.St f × (⊥ ⊎ Pos B))
             → resumeᴹ f cᶠ p ≈ₚ resumeᴹ g cᵍ (ϕ sim (proj₁ p) , proj₂ p)
  resume-sim h (_  , inj₁ a) = ⊥-elim a
  resume-sim h (m′ , inj₂ r) = h m′ r

  runFrom-sim : (m : MC.St f) (d : Strat (Neg B) (Pos B))
              → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ sim m) d
  runFrom-sim m (out b)    = ≈refl
  runFrom-sim m (coin μ k) = bindᶠ (λ b → runFrom-sim m (k b))
  runFrom-sim m (ask q k)  =
      bindᶠ (resume-sim {cᵍ = contᵍ k} (λ m′ r → runFrom-sim m′ (k r)))
    ⟨≈⟩ ≈sym (bindᶠ (λ p → >>=ₚ-identityˡ (ϕ sim (proj₁ p) , proj₂ p)
                                          (resumeᴹ g (contᵍ k))))
    ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.step f (m , inj₂ q)) (padϕ sim) (resumeᴹ g (contᵍ k)))
    ⟨≈⟩ bindˣ (step-sim sim (m , inj₂ q))

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

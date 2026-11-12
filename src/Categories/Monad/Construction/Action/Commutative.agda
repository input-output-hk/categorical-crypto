{-# OPTIONS --safe --without-K #-}

-- If W is a commutative monoid, W ⊗- is a commutative monad

open import Categories.Category.Core
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
open import Categories.Object.Monoid

module Categories.Monad.Construction.Action.Commutative
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

import Categories.Category.Monoidal.Braided.Properties as BP
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties S
import Categories.Category.Monoidal.Utilities as MU
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative
import Categories.Monad.Commutative.Properties as CP
open import Categories.Monad.Construction.Action
import Categories.Monad.Construction.Action.Commutative.Coherence as Coherence
open import Categories.Monad.Strong
import Categories.Monad.Strong.Properties as SP
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Object.CommutativeMonoid
open import Data.Product

open Category C
open Monoidal M
open Symmetric S using (braided)
open BP.Shorthands (Symmetric.braided S)
open MU.Shorthands M

private variable A B : Obj

module _ (W : Monoid M) where
  open Monoid W using (Carrier)
  open Coherence.Wiring S Carrier

  private
    module T = Monad (ActionM M W)
    module Laws = Coherence.Laws S W

  actionStrength : Strength M (ActionM M W)
  actionStrength = record
    { strengthen = ntHelper record
      { η       = λ _ → strength-map
      ; commute = λ (f , g) → Laws.natural f g
      }
    ; identityˡ     = Laws.strength-unit _
    ; η-comm        = Laws.strength-η _ _
    ; μ-η-comm      = Laws.strength-μ _ _
    ; strength-assoc = Laws.strength-assoc _ _ _
    }

  actionStrongMonad : StrongMonad M
  actionStrongMonad = record { M = ActionM M W; strength = actionStrength }

  actionRightStrength : RightStrength M (ActionM M W)
  actionRightStrength = SP.Strength⇒RightStrength braided actionStrength

  private
    module Left = SP.Left.Shorthands actionStrength
    module Right = SP.Right.Shorthands actionRightStrength

  right-strength-normal : Right.τ {A} {B} ≈ associator.from
  right-strength-normal {A} {B} =
    ∘-resp-≈ˡ (⊗-resp-≈ʳ braiding-selfInverse) ○ Laws.right-strength A B

  left-fubini-normal : (T.μ.η (A ⊗₀ B) ∘ T.F.₁ Right.τ) ∘ Left.σ
    ≈ ((Monoid.μ W ∘ σ⇒) ⊗₁ id) ∘ effect-permute
  left-fubini-normal {A} {B} =
    ∘-resp-≈ˡ (∘-resp-≈ʳ (T.F.F-resp-≈ right-strength-normal)) ○ Laws.left-normal A B

  right-fubini-normal : (T.μ.η (A ⊗₀ B) ∘ T.F.₁ Left.σ) ∘ Right.τ ≈ Monoid.μ W ⊗₁ id ∘ effect-permute
  right-fubini-normal {A} {B} = ∘-resp-≈ʳ right-strength-normal ○ Laws.right-normal A B

module _ (W : CommutativeMonoid braided) where
  open CommutativeMonoid W using (Carrier; monoid; μ) renaming (commutative to μ-comm)
  open Coherence.Wiring S Carrier

  actionCommutativeMonad : CommutativeMonad braided
  actionCommutativeMonad = record
    { strongMonad = actionStrongMonad monoid
    ; commutative = record
      { commutes = left-fubini-normal monoid ○ ∘-resp-≈ˡ (⊗-resp-≈ˡ μ-comm)
        ○ Equiv.sym (right-fubini-normal monoid) }
    }

  ψ-normal : CP.CommutativeProperties.ψ braided actionCommutativeMonad {A} {B}
    ≈ μ ⊗₁ id ∘ effect-permute
  ψ-normal = left-fubini-normal monoid ○ ∘-resp-≈ˡ (⊗-resp-≈ˡ μ-comm)

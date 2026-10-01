{-# OPTIONS --safe --without-K #-}

-- The machine layer as a traced symmetric monoidal category, and the
-- G construction over it with its monoidal structure.  `Traced.Ext`'s `β`
-- reduces to `Machines.Trace.Fubini.βᴹ`.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Traced
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Traced.Ext as TE
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.GConstructionMonoidal

open import Level

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as Congruence
import CategoricalCrypto.Machines.Trace.Fubini as Fubini
import CategoricalCrypto.Machines.Trace.Vanishing as Vanishing

module CategoricalCrypto.Machines.G
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open Bundle 𝒱 dist 𝒫
open Congruence 𝒱 dist 𝒫 E
open Fubini 𝒱 dist 𝒫 E
open MCat 𝒱 𝒫
open Sim 𝒱 𝒫
open Trace 𝒱 dist 𝒫 E
open Vanishing 𝒱 dist 𝒫 E

------------------------------------------------------------------------
-- Naturality

-- The `⊗ᵉ idᴹ` on the right-hand side adds a trivial state factor, so the two
-- sides differ by `ρ⇒` on the state and by which of the two state factors
-- `iter` runs at.  `traceStep-onR`/`traceStep-onL` reconcile the second and a
-- simulation the first.  Not in `Machines.Trace`: in one file with it, the
-- identical proof term measured 397 s warm against 7 s + 7 s apart.
module _ where
  open SymmetricMonoidalCategory 𝒱
  open Core 𝒱
  open Equiv
  open Frame 𝒱
  open MD.MonoidalDistributive dist
  open MonoidalUtilities.Shorthands monoidal
  open PureSub 𝒫
  open Tensor 𝒱 dist 𝒫

  open import Categories.Category.Monoidal.Reasoning monoidal
  open import Categories.Morphism.Reasoning U

  private variable A B P : Obj

  private
    id⊗id-comm : {t : P ⊗₀ A ⇒ P ⊗₀ B} → id ⊗₁ id ∘ t ≈ t ∘ id ⊗₁ id
    id⊗id-comm = elimˡ ⊗.identity ○ ⟺ (elimʳ ⊗.identity)

  opaque
    unfolding _∘ᴹ_

    trace-∘ˡ : {A B C X : Obj} (g : Machine B C) (f : Machine (A + X) (B + X))
             → (g ∘ᴹ traceᴹ A B X f) ≈ᴹ traceᴹ A C X ((g ⊗ᵉ idᴹ) ∘ᴹ f)
    trace-∘ˡ {A} {B} {C} {X} g f =
      ≲⇒≈ᴹ˘ (≲-trans (mk-cong (traceStep-cong S′ A C X
                                 ((onL-tstep ○ tstep-cong refl (onL-cong onR-id ○ onL-id)) ⟩∘⟨refl)
                               ○ ⟺ (traceStep-∘ˡ S′ A B C X (onR (step f)) (onL (onL (step g))))
                               ○ (refl⟩∘⟨ traceStep-onR (state g ⊛ Iˢ) (state f) A B X (step f))))
                     (sim (ρ⇒ ⊗₁ id) (pure-⊗₁ pure-ρ⇒ pure-id)
                          (⊛-point₂ (state g ⊛ Iˢ) (state g) (state f) (state f)
                                    (ρ-point (state g)) identityˡ)
                          (pullˡ (onL-sim onL-collapseʳ) ○ assoc
                           ○ (refl⟩∘⟨ onR-sim id⊗id-comm) ○ sym-assoc)))
      where
        S′ : State
        S′ = (state g ⊛ Iˢ) ⊛ state f

    trace-∘ʳ : {A B C X : Obj} (f : Machine (A + X) (B + X)) (h : Machine C A)
             → (traceᴹ A B X f ∘ᴹ h) ≈ᴹ traceᴹ C B X (f ∘ᴹ (h ⊗ᵉ idᴹ))
    trace-∘ʳ {A} {B} {C} {X} f h =
      ≲⇒≈ᴹ˘ (≲-trans (mk-cong reduce)
                     (sim (id ⊗₁ ρ⇒) (pure-⊗₁ pure-id pure-ρ⇒)
                          (⊛-point₂ (state f) (state f) (state h ⊛ Iˢ) (state h)
                                    identityˡ (ρ-point (state h)))
                          (pullˡ (onL-sim id⊗id-comm) ○ assoc
                           ○ (refl⟩∘⟨ onR-sim onL-collapseʳ) ○ sym-assoc)))
      where
        S″ : State
        S″ = state f ⊛ (state h ⊛ Iˢ)

        n : obj S″ ⊗₀ C ⇒ obj S″ ⊗₀ A
        n  = onR (onL (step h))

        -- Named, unlike `trace-∘ˡ`'s: inlined, this module's warm check goes from 15 s to 160 s.
        reduce : traceStep S″ C B X (step (f ∘ᴹ (h ⊗ᵉ idᴹ)))
               ≈ onL (traceStep (state f) A B X (step f)) ∘ n
        reduce = traceStep-cong S″ C B X
                   (refl⟩∘⟨ (onR-tstep ○ tstep-cong refl (onR-cong onR-id ○ onR-id)))
               ○ ⟺ (traceStep-∘ʳ S″ A B C X (onL (step f)) n)
               ○ (traceStep-onL (state f) (state h ⊛ Iˢ) A B X (step f) ⟩∘⟨refl)

------------------------------------------------------------------------
-- Superposing

-- An interface summand `P` the traced machine never sees.  Both sides run at
-- `Iˢ ⊛ state f`, so once the two `pureᴹ` re-bracketings are absorbed into the
-- step the law is a single step equation.  Its content is `exit-relabel`: the
-- superposed loop exits into `(P + B) + X` where the plain one exits into
-- `B + X`, and relabelling an exit branch is `iter-out`.
module _ where
  open SymmetricMonoidalCategory 𝒱
  open Core 𝒱
  open Equiv
  open Frame 𝒱
  open Iteration.Elgot E
  open MD.MonoidalDistributive dist
  open CE U cocartesian
  open MDP 𝒱 dist
  open Tensor 𝒱 dist 𝒫

  open import Categories.Category.Monoidal.Reasoning monoidal
  open import Categories.Morphism.Reasoning U

  super-step : (V : State) (P A B X : Obj) (g : obj V ⊗₀ (A + X) ⇒ obj V ⊗₀ (B + X))
             → traceStep V (P + A) (P + B) X (id ⊗₁ α+⇐ ∘ (tstep id g ∘ id ⊗₁ α+⇒))
             ≈ tstep id (traceStep V A B X g)
  super-step V P A B X g = δ-unique
    ((assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ)))
      ○ (refl⟩∘⟨ ( assoc ○ (refl⟩∘⟨ assoc)
                 ○ (refl⟩∘⟨ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇒-i₁i₁))))
                 ○ (refl⟩∘⟨ (tstep-i₁ ○ identityʳ))
                 ○ parallel refl α+⇐-i₁))
      ○ pullˡ (solve-i₁ V (P + A) (P + B) X k′) ○ identityˡ)
     ○ ⟺ (tstep-i₁ ○ identityʳ))
    ((assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ)))
      ○ (refl⟩∘⟨ enter₂ α+⇒-i₁i₂)
      ○ pullˡ exit-relabel ○ assoc)
     ○ ⟺ tstep-i₂)
    where
      k′ : obj V ⊗₀ ((P + A) + X) ⇒ obj V ⊗₀ ((P + B) + X)
      k′ = id ⊗₁ α+⇐ ∘ (tstep id g ∘ id ⊗₁ α+⇒)

      enter₂ : {W : Obj} {j : W ⇒ (P + A) + X} {j′ : W ⇒ A + X} → α+⇒ ∘ j ≈ i₂ ∘ j′
             → k′ ∘ id ⊗₁ j ≈ id ⊗₁ (i₂ +₁ id) ∘ (g ∘ id ⊗₁ j′)
      enter₂ e = assoc ○ (refl⟩∘⟨ assoc)
               ○ (refl⟩∘⟨ (refl⟩∘⟨ parallel refl e))
               ○ (refl⟩∘⟨ pullˡ tstep-i₂) ○ (refl⟩∘⟨ assoc)
               ○ pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇐-i₂))

      exit-relabel : solve V (P + A) (P + B) X k′ ∘ id ⊗₁ (i₂ +₁ id) ≈ id ⊗₁ i₂ ∘ solve V A B X g
      exit-relabel = δ-unique
        ((assoc ○ (refl⟩∘⟨ parallel refl +₁∘i₁)
          ○ pullˡ (solve-i₁ V (P + A) (P + B) X k′) ○ identityˡ)
         ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₁ V A B X g) ○ identityʳ))
        ((assoc ○ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ (+₁∘i₂ ○ identityʳ))))
          ○ solve-i₂ V (P + A) (P + B) X k′
          ○ iter-cong (enter₂ α+⇒-i₂
                       ○ (⟺ (tstep-cong refl (⟺ ⊗.identity) ○ tstep-str i₂ id) ⟩∘⟨refl))
          ○ ⟺ (iter-out (id ⊗₁ i₂)))
         ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₂ V A B X g)))

  superposing : {A B P X : Obj} (f : Machine (A + X) (B + X))
              → traceᴹ (P + A) (P + B) X (α⇐ᴹ ∘ᴹ (idᴹ ⊗ᵉ f) ∘ᴹ α⇒ᴹ)
              ≈ᴹ (idᴹ ⊗ᵉ traceᴹ A B X f)
  superposing {A} {B} {P} {X} f =
    ≲⇒≈ᴹ (≲-trans (trace-resp-≲ (≲-trans (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ α+⇒ M))
                                         (pure-∘ˡ α+⇐ (mk V k))))
                  (mk-cong (traceStep-cong V (P + A) (P + B) X
                              (refl⟩∘⟨ (tstep-cong onL-id refl ⟩∘⟨refl))
                            ○ super-step V P A B X (onR (step f))
                            ○ tstep-cong (⟺ onL-id) (traceStep-onR Iˢ (state f) A B X (step f)))))
    where
      M = idᴹ ⊗ᵉ f
      V = state M

      k : obj V ⊗₀ ((P + A) + X) ⇒ obj V ⊗₀ (P + (B + X))
      k = step M ∘ id ⊗₁ α+⇒

------------------------------------------------------------------------
-- The traced category and its G construction

Mealy-Traced : Traced Mealy-Monoidal
Mealy-Traced = record
  { symmetric   = Mealy-Symmetric
  ; trace       = λ {X} {A} {B} → traceᴹ A B X
  ; vanishing₁  = ≲⇒≈ᴹ (vanishing₁ᴹ _)
  ; vanishing₂  = vanishing₂ _
  ; superposing = superposing _
  ; yanking     = ≲⇒≈ᴹ yankingᴹ
  }

Mealy-TraceLaws : TE.Laws Mealy-Traced
Mealy-TraceLaws = record
  { trace-resp-≈ = trace-resp-≈ᴹ
  ; trace-∘ˡ     = trace-∘ˡ _ _
  ; trace-∘ʳ     = trace-∘ʳ _ _
  ; trace-comm   = trace-comm _
  }

-- States and processes over the machine layer, monoidal.  One application, and
-- consumers project from it: writing the category and its monoidal structure as
-- two separate `GConstruction*` applications instead makes Agda compare two
-- `GConstruction` record values field by field, which does not fit in 8 GB.
Mealy-Gᴹ : MonoidalCategory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Gᴹ = GConstructionMonoidalCategory Mealy-Category Mealy-Monoidal Mealy-Traced Mealy-TraceLaws

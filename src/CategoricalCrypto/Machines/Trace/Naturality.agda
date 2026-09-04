{-# OPTIONS --safe --without-K #-}

-- The ⊕-trace's two naturality laws, for arbitrary machines.
--
-- The `⊗ᵉ idᴹ` on the right-hand side adds a trivial state factor, so the two
-- sides differ by `ρ⇒` on the state and by which of the two state factors
-- `iter` runs at.  `traceStep-onR`/`traceStep-onL` reconcile the second and a
-- simulation the first.
--
-- Split off `CategoricalCrypto.Machines.Trace` for typecheck cost, and the
-- split is the whole speedup: measured warm, the two apart were 7 s + 7 s where
-- together in one file they were 397 s, for an identical proof term.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Machines.Trace.Naturality
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MD.MonoidalDistributive dist
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B P : Obj

private
  id⊗id-comm : {t : P ⊗₀ A ⇒ P ⊗₀ B} → id {P} ⊗₁ id ∘ t ≈ t ∘ id ⊗₁ id
  id⊗id-comm = elimˡ ⊗.identity ○ ⟺ (elimʳ ⊗.identity)

trace-∘ˡ : {A B C X : Obj} (g : Machine B C) (f : Machine (A + X) (B + X))
         → (g ∘ᴹ traceᴹ A B X f) ≈ᴹ traceᴹ A C X ((g ⊗ᵉ idᴹ {X}) ∘ᴹ f)
trace-∘ˡ {A} {B} {C} {X} g f =
  ≲⇒≈ᴹ˘ (≲-trans (mk-cong reduce) (sim (ρ⇒ ⊗₁ id) (pure-⊗₁ pure-ρ⇒ pure-id) d-ok p-ok s-ok))
  where
    S′ = (state g ⊛ Iˢ) ⊛ state f
    m  = onL {Q = obj (state f)} (onL {Q = unit} (step g))

    reduce : traceStep S′ A C X (step ((g ⊗ᵉ idᴹ {X}) ∘ᴹ f))
           ≈ m ∘ onR (traceStep (state f) A B X (step f))
    reduce = traceStep-cong S′ A C X
               ((onL-tstep ○ tstep-cong refl (onL-cong onR-id ○ onL-id)) ⟩∘⟨refl)
           ○ ⟺ (traceStep-∘ˡ S′ A B C X (onR (step f)) m)
           ○ (refl⟩∘⟨ traceStep-onR (state g ⊛ Iˢ) (state f) A B X (step f))

    d-ok = ⊛-discard (state g ⊛ Iˢ) (state g) (state f) (ρ-discard (state g))
    p-ok = ⊛-point (state g ⊛ Iˢ) (state g) (state f) (ρ-point (state g))

    s-ok : (ρ⇒ ⊗₁ id) ⊗₁ id ∘ (m ∘ onR (traceStep (state f) A B X (step f)))
         ≈ (onL (step g) ∘ onR (traceStep (state f) A B X (step f)))
           ∘ (ρ⇒ ⊗₁ id) ⊗₁ id
    s-ok = pullˡ (onL-sim onL-collapseʳ) ○ assoc
         ○ (refl⟩∘⟨ onR-sim id⊗id-comm) ○ sym-assoc

trace-∘ʳ : {A B C X : Obj} (f : Machine (A + X) (B + X)) (h : Machine C A)
         → (traceᴹ A B X f ∘ᴹ h) ≈ᴹ traceᴹ C B X (f ∘ᴹ (h ⊗ᵉ idᴹ {X}))
trace-∘ʳ {A} {B} {C} {X} f h =
  ≲⇒≈ᴹ˘ (≲-trans (mk-cong reduce) (sim (id ⊗₁ ρ⇒) (pure-⊗₁ pure-id pure-ρ⇒) d-ok p-ok s-ok))
  where
    S″ = state f ⊛ (state h ⊛ Iˢ)
    n  = onR {P = obj (state f)} (onL {Q = unit} (step h))

    reduce : traceStep S″ C B X (step (f ∘ᴹ (h ⊗ᵉ idᴹ {X})))
           ≈ onL (traceStep (state f) A B X (step f)) ∘ n
    reduce = traceStep-cong S″ C B X
               (refl⟩∘⟨ (onR-tstep ○ tstep-cong refl (onR-cong onR-id ○ onR-id)))
           ○ ⟺ (traceStep-∘ʳ S″ A B C X (onL (step f)) n)
           ○ (traceStep-onL (state f) (state h ⊛ Iˢ) A B X (step f) ⟩∘⟨refl)

    d-ok = ⊛-discardʳ (state f) (state h ⊛ Iˢ) (state h) (ρ-discard (state h))
    p-ok = ⊛-pointʳ (state f) (state h ⊛ Iˢ) (state h) (ρ-point (state h))

    s-ok : (id ⊗₁ ρ⇒) ⊗₁ id ∘ (onL (traceStep (state f) A B X (step f)) ∘ n)
         ≈ (onL (traceStep (state f) A B X (step f)) ∘ onR (step h))
           ∘ (id ⊗₁ ρ⇒) ⊗₁ id
    s-ok = pullˡ (onL-sim id⊗id-comm) ○ assoc
         ○ (refl⟩∘⟨ onR-sim onL-collapseʳ) ○ sym-assoc

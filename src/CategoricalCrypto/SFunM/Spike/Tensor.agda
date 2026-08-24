{-# OPTIONS --safe --without-K #-}

-- SPIKE: the interface tensor of the machine layer, over a distributive base.
--
-- `Spike.Mealy`'s `⊗` pairs STATES; the tensor here pairs INTERFACES, and is
-- `CategoricalCrypto.SFunM.Monoidal`'s `_⊗ᵉ_` written point-free: a paired state
-- acts on a sum interface by distributing (`δ⇐`), copairing the two one-sided
-- actions, and reassembling (`δ⇒`).  Three levers carry the layer:
--   * a map out of a distributed sum is its two components (`δ-unique`), so the
--     ⊕-side equations are branch goals, not coherence chains;
--   * `pureᴹ` is a functor from the base and monoidal (`⊗ᵉ-pureᴹ`), so every
--     structural morphism and all of its coherence comes from `+-monoidal`;
--   * `sim` is the point-free `≈ᵉ-sim`, and `collapseˡ`/`collapseʳ` its two
--     instances for the trivial state a pure machine contributes.
--
-- What is missing (`⊗ᵉ-homomorphism` and `assoc-commute`, hence the bundles) is
-- missing for a state-side reason, not a ⊕-side one: each needs the action of one
-- factor of a re-bracketed state tree to be recognized as the action of the same
-- factor of another — `Spike.SlotFrame`'s `σ-onR`/`σ-onL` pair is that statement
-- for the state braiding, and its `onL-sim`/`onR-sim` for a state map on each
-- factor.
--
-- `⊗ᵉ-resp-≈ᵉ` needed more, and that is `Spike.Distributor`: the elementwise
-- `⊗idᵏ-trace` splits a *word* over `A ⊎ C` into its two subwords, which binary
-- distributivity does not hand over.  `run-⊗id`/`eval-⊗id` are that split, and
-- `Spike.SlotFrame` holds the reshuffles it needs across the step, as it does
-- every other coherence obligation this file glues together.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Cocartesian as Cocart
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)

import CategoricalCrypto.SFunM.Spike.Distributor as Distributor
import CategoricalCrypto.SFunM.Spike.Interchange as Interchange
import CategoricalCrypto.SFunM.Spike.Laws as Laws
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD
import CategoricalCrypto.SFunM.Spike.SlotFrame as SlotFrame

module CategoricalCrypto.SFunM.Spike.Tensor {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Distributor 𝒱 dist
open Equiv
open Interchange 𝒱
open Laws 𝒱
open MD.MonoidalDistributive dist
open Mealy 𝒱
open SlotFrame 𝒱
open Machine
open State

open import Categories.Category.Monoidal.Properties monoidal using (coherence₃)
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D P Q X Y Z : Obj

------------------------------------------------------------------------
-- Machines with a named state
------------------------------------------------------------------------

mk : (S : State) → obj S ⊗₀ A ⇒ obj S ⊗₀ B → Machine A B
mk S k = record { state = S ; step = k }

run-cong : {S : State} {k k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
         → k ≈ k′ → (n : ℕ) → run (mk S k) n ≈ run (mk S k′) n
run-cong e zero    = refl
run-cong e (suc n) = slot₂ᵍ-cong (run-cong e n) ⟩∘⟨ slot₁ᵍ-cong e

mk-cong : {S : State} {k k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B} → k ≈ k′ → mk S k ≈ᵉ mk S k′
mk-cong e n = cl-cong (run-cong e n)

------------------------------------------------------------------------
-- Simulation: the point-free `≈ᵉ-sim`
------------------------------------------------------------------------

run-sim : {S T : State} {k : obj S ⊗₀ A ⇒ obj S ⊗₀ B} {k′ : obj T ⊗₀ A ⇒ obj T ⊗₀ B}
          (u : obj S ⇒ obj T) → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
        → (n : ℕ) → u ⊗₁ id ∘ run (mk S k) n ≈ run (mk T k′) n ∘ u ⊗₁ id
run-sim u e zero    = identityʳ ○ ⟺ identityˡ
run-sim u e (suc n) =
    pullˡ (slot₂-sim (run-sim u e n)) ○ assoc ○ (refl⟩∘⟨ slot₁-sim e) ○ sym-assoc

-- Machines whose states are related by a map respecting point, discard and step
-- have the same traces.
sim : {S T : State} {k : obj S ⊗₀ A ⇒ obj S ⊗₀ B} {k′ : obj T ⊗₀ A ⇒ obj T ⊗₀ B}
      (u : obj S ⇒ obj T)
    → discard T ∘ u ≈ discard S → u ∘ point S ≈ point T
    → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
    → mk S k ≈ᵉ mk T k′
sim u ed ep e n = cl-sim u ed ep (run-sim u e n)

------------------------------------------------------------------------
-- Pure machines
------------------------------------------------------------------------

-- The `n`-fold `⊗₁`, playing the role of `List`'s `map` in the elementwise layer.
powmap : (n : ℕ) → A ⇒ B → pow n A ⇒ pow n B
powmap zero    f = id
powmap (suc n) f = f ⊗₁ powmap n f

powmap-id : (n : ℕ) → powmap n (id {A}) ≈ id
powmap-id zero    = refl
powmap-id (suc n) = (refl⟩⊗⟨ powmap-id n) ○ ⊗.identity

powmap-∘ : (g : B ⇒ C) (f : A ⇒ B) (n : ℕ) → powmap n (g ∘ f) ≈ powmap n g ∘ powmap n f
powmap-∘ g f zero    = ⟺ identity²
powmap-∘ g f (suc n) = (refl⟩⊗⟨ powmap-∘ g f n) ○ ⊗.homomorphism

powmap-cong : {f g : A ⇒ B} → f ≈ g → (n : ℕ) → powmap n f ≈ powmap n g
powmap-cong e zero    = refl
powmap-cong e (suc n) = e ⟩⊗⟨ powmap-cong e n

run-str : {S : State} (h : A ⇒ B) (n : ℕ) → run (mk S (id ⊗₁ h)) n ≈ id ⊗₁ powmap n h
run-str h zero    = ⟺ ⊗.identity
run-str {S = S} h (suc n) = begin
  slot₂ (run (mk S (id ⊗₁ h)) n) ∘ slot₁ (id ⊗₁ h)
    ≈⟨ slot₂ᵍ-cong (run-str h n) ⟩∘⟨ slot₁-str h ⟩
  slot₂ (id ⊗₁ powmap n h) ∘ id ⊗₁ (h ⊗₁ id)
    ≈⟨ slot₂-str (powmap n h) ⟩∘⟨refl ○ merge₂ʳ ⟩
  id ⊗₁ (id ⊗₁ powmap n h ∘ h ⊗₁ id)
    ≈˘⟨ refl⟩⊗⟨ serialize₂₁ ⟩
  id ⊗₁ (h ⊗₁ powmap n h)  ∎

-- Any state that points and discards to the identity is invisible to a step
-- that ignores it.
eval-str : {S : State} → discard S ∘ point S ≈ id → (h : A ⇒ B) (n : ℕ)
         → eval (mk S (id ⊗₁ h)) n ≈ powmap n h
eval-str {S = S} c h n = begin
  λ⇒ ∘ (d ⊗₁ id ∘ (run (mk S (id ⊗₁ h)) n ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ run-str h n ⟩∘⟨refl ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (id ⊗₁ powmap n h ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (pad-transport d (powmap n h))) ⟩
  λ⇒ ∘ ((id ⊗₁ powmap n h ∘ d ⊗₁ id) ∘ (p ⊗₁ id ∘ λ⇐))
    ≈⟨ pullˡ (pullˡ unitorˡ-commute-from) ○ assoc ○ assoc ⟩
  powmap n h ∘ (λ⇒ ∘ (d ⊗₁ id ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ c ⟩⊗⟨refl ○ ⊗.identity) ⟩
  powmap n h ∘ (λ⇒ ∘ (id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ identityˡ ○ unitorˡ.isoʳ) ⟩
  powmap n h ∘ id
    ≈⟨ identityʳ ⟩
  powmap n h  ∎
  where
    d = discard S
    p = point S

pureᴹ : A ⇒ B → Machine A B
pureᴹ f = mk Iˢ (id ⊗₁ f)

eval-pureᴹ : (h : A ⇒ B) (n : ℕ) → eval (pureᴹ h) n ≈ powmap n h
eval-pureᴹ = eval-str identity²

pureᴹ-cong : {f g : A ⇒ B} → f ≈ g → pureᴹ f ≈ᵉ pureᴹ g
pureᴹ-cong {f = f} {g} eq n = eval-pureᴹ f n ○ powmap-cong eq n ○ ⟺ (eval-pureᴹ g n)

pureᴹ-id : pureᴹ (id {A}) ≈ᵉ idᴹ
pureᴹ-id n = eval-pureᴹ id n ○ powmap-id n ○ ⟺ (eval-id n)

pureᴹ-∘ : (g : B ⇒ C) (f : A ⇒ B) → pureᴹ (g ∘ f) ≈ᵉ (pureᴹ g ∘ᴹ pureᴹ f)
pureᴹ-∘ g f n = eval-pureᴹ (g ∘ f) n ○ powmap-∘ g f n
              ○ ⟺ (eval-pureᴹ g n ⟩∘⟨ eval-pureᴹ f n) ○ ⟺ (eval-∘ (pureᴹ g) (pureᴹ f) n)

------------------------------------------------------------------------
-- The interface tensor
------------------------------------------------------------------------

private
  -- `[ id , id ] : ⊥ + ⊥ ⇒ ⊥` is an iso, its inverse `i₁`, because maps out of
  -- the initial object are unique.
  ⊥+⊥-isoˡ : i₁ ∘ [ id {⊥} , id ] ≈ id
  ⊥+⊥-isoˡ = ⟺ (+-unique (pullʳ inject₁ ○ identityʳ)
                         (pullʳ inject₂ ○ identityʳ ○ ¡-unique₂ i₁ i₂)) ○ +-η

  ψ : (X ⊗₀ ⊥) + (X ⊗₀ ⊥) ⇒ X ⊗₀ ⊥
  ψ = id ⊗₁ [ id , id ] ∘ δ⇒

  ψ⁻ : X ⊗₀ ⊥ ⇒ (X ⊗₀ ⊥) + (X ⊗₀ ⊥)
  ψ⁻ = δ⇐ ∘ id ⊗₁ i₁

  ψ-isoˡ : ψ⁻ {X} ∘ ψ ≈ id
  ψ-isoˡ = center (merge₂ʳ ○ refl⟩⊗⟨ ⊥+⊥-isoˡ ○ ⊗.identity)
         ○ (refl⟩∘⟨ identityˡ) ○ distributeˡ.isoˡ

  ψ-i₁ : ψ {X} ∘ i₁ ≈ id
  ψ-i₁ = pullʳ inject₁ ○ merge₂ʳ ○ (refl⟩⊗⟨ inject₁) ○ ⊗.identity

  ψ-i₂ : ψ {X} ∘ i₂ ≈ id
  ψ-i₂ = pullʳ inject₂ ○ merge₂ʳ ○ (refl⟩⊗⟨ inject₂) ○ ⊗.identity

-- Binary distributivity already makes `X ⊗₀ ⊥` initial: the injections of
-- `(X ⊗₀ ⊥) + (X ⊗₀ ⊥)` agree, hence so do any two maps out of `X ⊗₀ ⊥`.
⊥-unique : {u v : X ⊗₀ ⊥ ⇒ Y} → u ≈ v
⊥-unique = ⟺ inject₁ ○ (refl⟩∘⟨ i-collapse) ○ inject₂
  where
    i-collapse : i₁ {X ⊗₀ ⊥} {X ⊗₀ ⊥} ≈ i₂
    i-collapse = insertˡ ψ-isoˡ ○ (refl⟩∘⟨ ψ-i₁) ○ identityʳ
               ○ ⟺ (insertˡ ψ-isoˡ ○ (refl⟩∘⟨ ψ-i₂) ○ identityʳ)

-- The two clauses of `SFunM.Monoidal`'s `_⊗ᵏ_` as the two components of a
-- copairing: expose the sum, act on the matching side, reassemble.
tstep : (X ⊗₀ A ⇒ X ⊗₀ B) → (X ⊗₀ C ⇒ X ⊗₀ D) → X ⊗₀ (A + C) ⇒ X ⊗₀ (B + D)
tstep k l = δ⇒ ∘ (k +₁ l) ∘ δ⇐

infixr 10 _⊗ᵉ_

_⊗ᵉ_ : Machine A B → Machine C D → Machine (A + C) (B + D)
f ⊗ᵉ g = mk (state f ⊛ state g) (tstep (onL (step f)) (onR (step g)))

tstep-cong : {k k′ : X ⊗₀ A ⇒ X ⊗₀ B} {l l′ : X ⊗₀ C ⇒ X ⊗₀ D}
           → k ≈ k′ → l ≈ l′ → tstep k l ≈ tstep k′ l′
tstep-cong e₁ e₂ = refl⟩∘⟨ +₁-cong₂ e₁ e₂ ⟩∘⟨refl

tstep-i₁ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ C ⇒ X ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₁ ≈ id ⊗₁ i₁ ∘ k
tstep-i₁ = assoc ○ (refl⟩∘⟨ (pullʳ δ⇐-i₁ ○ +₁∘i₁)) ○ pullˡ inject₁

tstep-i₂ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ C ⇒ X ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₂ ≈ id ⊗₁ i₂ ∘ l
tstep-i₂ = assoc ○ (refl⟩∘⟨ (pullʳ δ⇐-i₂ ○ +₁∘i₂)) ○ pullˡ inject₂

-- A tensor of steps that ignore the state is the state-ignoring step of the sum:
-- the distributor is natural in both summands.
tstep-str : (h : A ⇒ B) (k : C ⇒ D) → tstep (id {X} ⊗₁ h) (id ⊗₁ k) ≈ id ⊗₁ (h +₁ k)
tstep-str h k = δ-unique (tstep-i₁ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₁))
                         (tstep-i₂ ○ merge₂ʳ ○ ⟺ (merge₂ʳ ○ refl⟩⊗⟨ +₁∘i₂))

IˢIˢ-closed : discard (Iˢ ⊛ Iˢ) ∘ point (Iˢ ⊛ Iˢ) ≈ id
IˢIˢ-closed = (elimʳ ⊗.identity ⟩∘⟨ elimˡ ⊗.identity) ○ unitorˡ.isoʳ

+₁-id : id {A} +₁ id {B} ≈ id
+₁-id = ⟺ (+-unique (+₁∘i₁ ○ identityʳ) (+₁∘i₂ ○ identityʳ)) ○ +-η

-- The analogue of `statelessᵉ-⊗`: `pureᴹ` is monoidal, which is what carries
-- every coherence law of the interface tensor.
⊗ᵉ-pureᴹ : (h : A ⇒ B) (k : C ⇒ D) → (pureᴹ h ⊗ᵉ pureᴹ k) ≈ᵉ pureᴹ (h +₁ k)
⊗ᵉ-pureᴹ h k n = mk-cong (tstep-cong (onL-str h) (onRᵍ-id⊗ k) ○ tstep-str h k) n
               ○ eval-str IˢIˢ-closed (h +₁ k) n ○ ⟺ (eval-pureᴹ (h +₁ k) n)

⊗ᵉ-identity : (idᴹ {A} ⊗ᵉ idᴹ {B}) ≈ᵉ idᴹ
⊗ᵉ-identity n =
    mk-cong (tstep-cong (onL-id ○ ⟺ ⊗.identity) (onR-id ○ ⟺ ⊗.identity)
             ○ tstep-str id id) n
  ○ eval-str IˢIˢ-closed (id +₁ id) n
  ○ powmap-cong +₁-id n ○ powmap-id n ○ ⟺ (eval-id n)

------------------------------------------------------------------------
-- Collapsing a trivial state factor
------------------------------------------------------------------------

collapseˡ : {S : State} {k : (unit ⊗₀ obj S) ⊗₀ A ⇒ (unit ⊗₀ obj S) ⊗₀ B}
            {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → λ⇒ ⊗₁ id ∘ k ≈ k′ ∘ λ⇒ ⊗₁ id → mk (Iˢ ⊛ S) k ≈ᵉ mk S k′
collapseˡ = sim λ⇒ (⟺ unitorˡ-commute-from)
                   (pullˡ unitorˡ-commute-from ○ cancelʳ unitorˡ.isoʳ)

collapseʳ : {S : State} {k : (obj S ⊗₀ unit) ⊗₀ A ⇒ (obj S ⊗₀ unit) ⊗₀ B}
            {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → ρ⇒ ⊗₁ id ∘ k ≈ k′ ∘ ρ⇒ ⊗₁ id → mk (S ⊛ Iˢ) k ≈ᵉ mk S k′
collapseʳ = sim ρ⇒ (⟺ unitorʳ-commute-from ○ (⟺ coherence₃) ⟩∘⟨refl)
                   (pullˡ unitorʳ-commute-from
                    ○ cancelʳ ((⟺ coherence₃) ⟩∘⟨refl ○ unitorˡ.isoʳ))

-- Composing with a pure machine only pre- or post-composes the step.
pure-∘ˡ : (h : B ⇒ C) (M : Machine A B) → (pureᴹ h ∘ᴹ M) ≈ᵉ mk (state M) (id ⊗₁ h ∘ step M)
pure-∘ˡ h M = collapseˡ ((refl⟩∘⟨ onL-str h ⟩∘⟨refl) ○ pullˡ (⟺ (pad-transport λ⇒ h))
                         ○ assoc ○ (refl⟩∘⟨ onR-collapseˡ) ○ sym-assoc)

pure-∘ʳ : (h : A ⇒ B) (M : Machine B C) → (M ∘ᴹ pureᴹ h) ≈ᵉ mk (state M) (step M ∘ id ⊗₁ h)
pure-∘ʳ h M = collapseʳ ((refl⟩∘⟨ refl⟩∘⟨ onRᵍ-id⊗ h) ○ pullˡ onL-collapseʳ ○ assoc
                         ○ (refl⟩∘⟨ ⟺ (pad-transport ρ⇒ h)) ○ sym-assoc)

------------------------------------------------------------------------
-- The structural morphisms
------------------------------------------------------------------------

private
  module ⊕ = Cocart.CocartesianMonoidal U cocartesian
  module ⊕Sym = Symmetric (Cocart.CocartesianSymmetricMonoidal.+-symmetric U cocartesian)
  module ⊕Br = Braided ⊕Sym.braided
  module ℳ = Category Mealy-Category

open ℳ.HomReasoning using ()
  renaming (_○_ to _○ᴹ_; ⟺ to ⟺ᴹ; _⟩∘⟨_ to _⟩∘ᴹ⟨_; refl⟩∘⟨_ to reflᴹ⟩∘ᴹ⟨_
           ; _⟩∘⟨refl to _⟩∘ᴹ⟨reflᴹ)

λ⇒ᴹ : Machine (⊥ + A) A
λ⇒ᴹ = pureᴹ ⊕.unitorˡ.from

λ⇐ᴹ : Machine A (⊥ + A)
λ⇐ᴹ = pureᴹ ⊕.unitorˡ.to

ρ⇒ᴹ : Machine (A + ⊥) A
ρ⇒ᴹ = pureᴹ ⊕.unitorʳ.from

ρ⇐ᴹ : Machine A (A + ⊥)
ρ⇐ᴹ = pureᴹ ⊕.unitorʳ.to

α⇒ᴹ : Machine ((A + B) + C) (A + (B + C))
α⇒ᴹ = pureᴹ ⊕.associator.from

α⇐ᴹ : Machine (A + (B + C)) ((A + B) + C)
α⇐ᴹ = pureᴹ ⊕.associator.to

σᴹ : Machine (A + B) (B + A)
σᴹ = pureᴹ +-swap

-- `idᴹ` and `pureᴹ id` differ only in their step, so they are interchangeable
-- under `_⊗ᵉ_` without a congruence for it.
⊗ᵉ-idᴹˡ : (M : Machine C D) → (idᴹ {A} ⊗ᵉ M) ≈ᵉ (pureᴹ id ⊗ᵉ M)
⊗ᵉ-idᴹˡ M = mk-cong (tstep-cong (onL-cong (⟺ ⊗.identity)) refl)

⊗ᵉ-idᴹʳ : (M : Machine A B) → (M ⊗ᵉ idᴹ {C}) ≈ᵉ (M ⊗ᵉ pureᴹ id)
⊗ᵉ-idᴹʳ M = mk-cong (tstep-cong refl (onR-cong (⟺ ⊗.identity)))

------------------------------------------------------------------------
-- Coherence: every law is its base instance conjugated by `pureᴹ`
------------------------------------------------------------------------

pure-iso : {h : A ⇒ B} {h⁻ : B ⇒ A} → h⁻ ∘ h ≈ id → (pureᴹ h⁻ ∘ᴹ pureᴹ h) ≈ᵉ idᴹ
pure-iso e = ⟺ᴹ (pureᴹ-∘ _ _) ○ᴹ pureᴹ-cong e ○ᴹ pureᴹ-id

λᴹ-isoˡ : (λ⇐ᴹ ∘ᴹ λ⇒ᴹ {A}) ≈ᵉ idᴹ
λᴹ-isoˡ = pure-iso ⊕.unitorˡ.isoˡ

λᴹ-isoʳ : (λ⇒ᴹ ∘ᴹ λ⇐ᴹ {A}) ≈ᵉ idᴹ
λᴹ-isoʳ = pure-iso ⊕.unitorˡ.isoʳ

ρᴹ-isoˡ : (ρ⇐ᴹ ∘ᴹ ρ⇒ᴹ {A}) ≈ᵉ idᴹ
ρᴹ-isoˡ = pure-iso ⊕.unitorʳ.isoˡ

ρᴹ-isoʳ : (ρ⇒ᴹ ∘ᴹ ρ⇐ᴹ {A}) ≈ᵉ idᴹ
ρᴹ-isoʳ = pure-iso ⊕.unitorʳ.isoʳ

αᴹ-isoˡ : (α⇐ᴹ ∘ᴹ α⇒ᴹ {A} {B} {C}) ≈ᵉ idᴹ
αᴹ-isoˡ = pure-iso ⊕.associator.isoˡ

αᴹ-isoʳ : (α⇒ᴹ ∘ᴹ α⇐ᴹ {A} {B} {C}) ≈ᵉ idᴹ
αᴹ-isoʳ = pure-iso ⊕.associator.isoʳ

σᴹ-involutive : (σᴹ ∘ᴹ σᴹ {A} {B}) ≈ᵉ idᴹ
σᴹ-involutive = pure-iso +-swap∘swap

triangleᴹ : ((idᴹ {A} ⊗ᵉ λ⇒ᴹ {B}) ∘ᴹ α⇒ᴹ) ≈ᵉ (ρ⇒ᴹ ⊗ᵉ idᴹ)
triangleᴹ = (⊗ᵉ-idᴹˡ λ⇒ᴹ ○ᴹ ⊗ᵉ-pureᴹ id ⊕.unitorˡ.from) ⟩∘ᴹ⟨reflᴹ
          ○ᴹ ⟺ᴹ (pureᴹ-∘ _ _) ○ᴹ pureᴹ-cong ⊕.triangle
          ○ᴹ ⟺ᴹ (⊗ᵉ-idᴹʳ ρ⇒ᴹ ○ᴹ ⊗ᵉ-pureᴹ ⊕.unitorʳ.from id)

pentagonᴹ : ((idᴹ ⊗ᵉ α⇒ᴹ {B} {C} {D}) ∘ᴹ (α⇒ᴹ ∘ᴹ (α⇒ᴹ {A} ⊗ᵉ idᴹ))) ≈ᵉ (α⇒ᴹ ∘ᴹ α⇒ᴹ)
pentagonᴹ = (⊗ᵉ-idᴹˡ α⇒ᴹ ○ᴹ ⊗ᵉ-pureᴹ id ⊕.associator.from)
              ⟩∘ᴹ⟨ (reflᴹ⟩∘ᴹ⟨ (⊗ᵉ-idᴹʳ α⇒ᴹ ○ᴹ ⊗ᵉ-pureᴹ ⊕.associator.from id))
          ○ᴹ (reflᴹ⟩∘ᴹ⟨ ⟺ᴹ (pureᴹ-∘ _ _)) ○ᴹ ⟺ᴹ (pureᴹ-∘ _ _)
          ○ᴹ pureᴹ-cong ⊕.pentagon ○ᴹ pureᴹ-∘ _ _

hexagonᴹ : ((idᴹ ⊗ᵉ σᴹ {A} {C}) ∘ᴹ (α⇒ᴹ ∘ᴹ (σᴹ {A} {B} ⊗ᵉ idᴹ))) ≈ᵉ (α⇒ᴹ ∘ᴹ (σᴹ ∘ᴹ α⇒ᴹ))
hexagonᴹ = (⊗ᵉ-idᴹˡ σᴹ ○ᴹ ⊗ᵉ-pureᴹ id +-swap)
             ⟩∘ᴹ⟨ (reflᴹ⟩∘ᴹ⟨ (⊗ᵉ-idᴹʳ σᴹ ○ᴹ ⊗ᵉ-pureᴹ +-swap id))
         ○ᴹ (reflᴹ⟩∘ᴹ⟨ ⟺ᴹ (pureᴹ-∘ _ _)) ○ᴹ ⟺ᴹ (pureᴹ-∘ _ _)
         ○ᴹ pureᴹ-cong hexagon⊕ ○ᴹ pureᴹ-∘ _ _ ○ᴹ (reflᴹ⟩∘ᴹ⟨ pureᴹ-∘ _ _)
  where hexagon⊕ = ⊕Br.hexagon₁

------------------------------------------------------------------------
-- `tstep` is functorial, and the state-side actions distribute over it
------------------------------------------------------------------------

tstep-∘ : {k₂ : X ⊗₀ B ⇒ X ⊗₀ C} {l₂ : X ⊗₀ D ⇒ X ⊗₀ Z}
          {k₁ : X ⊗₀ A ⇒ X ⊗₀ B} {l₁ : X ⊗₀ Y ⇒ X ⊗₀ D}
        → tstep k₂ l₂ ∘ tstep k₁ l₁ ≈ tstep (k₂ ∘ k₁) (l₂ ∘ l₁)
tstep-∘ {k₂ = k₂} {l₂} {k₁} {l₁} = begin
  (δ⇒ ∘ ((k₂ +₁ l₂) ∘ δ⇐)) ∘ (δ⇒ ∘ ((k₁ +₁ l₁) ∘ δ⇐))
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  δ⇒ ∘ ((k₂ +₁ l₂) ∘ (δ⇐ ∘ (δ⇒ ∘ ((k₁ +₁ l₁) ∘ δ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ distributeˡ.isoˡ ⟩
  δ⇒ ∘ ((k₂ +₁ l₂) ∘ ((k₁ +₁ l₁) ∘ δ⇐))
    ≈⟨ refl⟩∘⟨ pullˡ +₁∘+₁ ⟩
  δ⇒ ∘ (((k₂ ∘ k₁) +₁ (l₂ ∘ l₁)) ∘ δ⇐)  ∎

-- Both state-side actions carry a square that is natural in the interface
-- (`onL-branch`/`onR-branch`), hence both distribute over the tensor of steps.
onL-tstep : {k : P ⊗₀ A ⇒ P ⊗₀ B} {l : P ⊗₀ C ⇒ P ⊗₀ D}
          → onL {Q = Q} (tstep k l) ≈ tstep (onL k) (onL l)
onL-tstep = δ-unique (onL-branch tstep-i₁ ○ ⟺ tstep-i₁)
                     (onL-branch tstep-i₂ ○ ⟺ tstep-i₂)

onR-tstep : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {l : Q ⊗₀ C ⇒ Q ⊗₀ D}
          → onR {P = P} (tstep k l) ≈ tstep (onR k) (onR l)
onR-tstep = δ-unique (onR-branch tstep-i₁ ○ ⟺ tstep-i₁)
                     (onR-branch tstep-i₂ ○ ⟺ tstep-i₂)

------------------------------------------------------------------------
-- Unitor naturality
------------------------------------------------------------------------

-- Cutting the empty summand: the other branch cannot fire, because `X ⊗₀ ⊥` is
-- initial (`⊥-unique`).
private
  ρ-i₁ : ∀ {W} → id {X} ⊗₁ ⊕.unitorʳ.from {W} ∘ id ⊗₁ i₁ ≈ id
  ρ-i₁ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorʳ.isoʳ) ○ ⊗.identity

  λ-i₂ : ∀ {W} → id {X} ⊗₁ ⊕.unitorˡ.from {W} ∘ id ⊗₁ i₂ ≈ id
  λ-i₂ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorˡ.isoʳ) ○ ⊗.identity

tstep-ρ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥}
        → id ⊗₁ ⊕.unitorʳ.from ∘ tstep k l ≈ k ∘ id ⊗₁ ⊕.unitorʳ.from
tstep-ρ = δ-unique (pullʳ tstep-i₁ ○ pullˡ ρ-i₁ ○ identityˡ
                    ○ ⟺ (pullʳ ρ-i₁ ○ identityʳ)) ⊥-unique

tstep-λ : {k : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥} {l : X ⊗₀ A ⇒ X ⊗₀ B}
        → id ⊗₁ ⊕.unitorˡ.from ∘ tstep k l ≈ l ∘ id ⊗₁ ⊕.unitorˡ.from
tstep-λ = δ-unique ⊥-unique
                   (pullʳ tstep-i₂ ○ pullˡ λ-i₂ ○ identityˡ
                    ○ ⟺ (pullʳ λ-i₂ ○ identityʳ))

unitorˡ-commuteᴹ : {f : Machine A B} → (λ⇒ᴹ ∘ᴹ (idᴹ {⊥} ⊗ᵉ f)) ≈ᵉ (f ∘ᴹ λ⇒ᴹ)
unitorˡ-commuteᴹ {f = f} =
    pure-∘ˡ ⊕.unitorˡ.from (idᴹ ⊗ᵉ f)
  ○ᴹ collapseˡ ((refl⟩∘⟨ tstep-λ) ○ pullˡ onR-collapseˡ ○ assoc
                ○ (refl⟩∘⟨ ⟺ (pad-transport λ⇒ ⊕.unitorˡ.from)) ○ sym-assoc)
  ○ᴹ ⟺ᴹ (pure-∘ʳ ⊕.unitorˡ.from f)

unitorʳ-commuteᴹ : {f : Machine A B} → (ρ⇒ᴹ ∘ᴹ (f ⊗ᵉ idᴹ {⊥})) ≈ᵉ (f ∘ᴹ ρ⇒ᴹ)
unitorʳ-commuteᴹ {f = f} =
    pure-∘ˡ ⊕.unitorʳ.from (f ⊗ᵉ idᴹ)
  ○ᴹ collapseʳ ((refl⟩∘⟨ tstep-ρ) ○ pullˡ onL-collapseʳ ○ assoc
                ○ (refl⟩∘⟨ ⟺ (pad-transport ρ⇒ ⊕.unitorʳ.from)) ○ sym-assoc)
  ○ᴹ ⟺ᴹ (pure-∘ʳ ⊕.unitorʳ.from f)

------------------------------------------------------------------------
-- Interchange
------------------------------------------------------------------------

-- A state map that conjugates both arms conjugates the tensor: the interface
-- tensor is compatible with state simulations.
tstep-sim : {X′ : Obj} {v : X ⇒ X′} {k : X ⊗₀ A ⇒ X ⊗₀ B} {k′ : X′ ⊗₀ A ⇒ X′ ⊗₀ B}
            {l : X ⊗₀ C ⇒ X ⊗₀ D} {l′ : X′ ⊗₀ C ⇒ X′ ⊗₀ D}
          → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id → v ⊗₁ id ∘ l ≈ l′ ∘ v ⊗₁ id
          → v ⊗₁ id ∘ tstep k l ≈ tstep k′ l′ ∘ v ⊗₁ id
tstep-sim {v = v} e₁ e₂ = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (⟺ (pad-transport v i₁)) ○ assoc ○ (refl⟩∘⟨ e₁)
   ○ ⟺ (pullʳ (⟺ (pad-transport v i₁)) ○ pullˡ tstep-i₁ ○ assoc))
  (pullʳ tstep-i₂ ○ pullˡ (⟺ (pad-transport v i₂)) ○ assoc ○ (refl⟩∘⟨ e₂)
   ○ ⟺ (pullʳ (⟺ (pad-transport v i₂)) ○ pullˡ tstep-i₂ ○ assoc))

------------------------------------------------------------------------
-- Braiding naturality
------------------------------------------------------------------------

-- Swapping the interface summands swaps the two arms.
tstep-swap : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ C ⇒ X ⊗₀ D}
           → id ⊗₁ +-swap ∘ tstep k l ≈ tstep l k ∘ id ⊗₁ +-swap
tstep-swap = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ inject₁)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ inject₁) ○ tstep-i₂))
  (pullʳ tstep-i₂ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ inject₂)
   ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ inject₂) ○ tstep-i₁))

braiding-commuteᴹ : {f : Machine A B} {g : Machine C D}
                  → (σᴹ ∘ᴹ (f ⊗ᵉ g)) ≈ᵉ ((g ⊗ᵉ f) ∘ᴹ σᴹ)
braiding-commuteᴹ {f = f} {g} =
    pure-∘ˡ +-swap (f ⊗ᵉ g)
  ○ᴹ sim σ⇒ discard-σ point-σ
         (pullˡ (⟺ (pad-transport σ⇒ +-swap)) ○ assoc
          ○ (refl⟩∘⟨ tstep-sim σ-onL σ-onR) ○ sym-assoc ○ (tstep-swap ⟩∘⟨refl))
  ○ᴹ ⟺ᴹ (pure-∘ʳ +-swap (g ⊗ᵉ f))
  where
    discard-σ : discard (state g ⊛ state f) ∘ σ⇒ ≈ discard (state f ⊛ state g)
    discard-σ = pullʳ (⟺ (braiding.⇒.commute _)) ○ pullˡ (refl⟩∘⟨ σ-unit ○ identityʳ)

    point-σ : σ⇒ ∘ point (state f ⊛ state g) ≈ point (state g ⊛ state f)
    point-σ = pullˡ (braiding.⇒.commute _) ○ assoc
            ○ (refl⟩∘⟨ (σ-unit ⟩∘⟨refl ○ identityˡ))

------------------------------------------------------------------------
-- Splitting a word: the interface tensor's congruence
------------------------------------------------------------------------

-- Tensoring with the identity, with the trivial state factor collapsed away, so
-- that the word induction below sees no `onL`/`onR` at all.
⊗idᵉ-collapse : (f : Machine A B) → (f ⊗ᵉ idᴹ {C}) ≈ᵉ mk (state f) (tstep (step f) id)
⊗idᵉ-collapse f =
  collapseʳ (tstep-sim onL-collapseʳ ((refl⟩∘⟨ onR-id) ○ identityʳ ○ ⟺ identityˡ))

private
  -- Peeling the head letter off a word: the head goes through the matching
  -- branch of the step, the tail through the induction hypothesis.
  peel : {S A′ B′ N N′ W W′ : Obj}
         {T : S ⊗₀ (A + C) ⇒ S ⊗₀ (B + D)} {R : S ⊗₀ N ⇒ S ⊗₀ N′}
         {Rt : S ⊗₀ W ⇒ S ⊗₀ W′} {j : W ⇒ N} {j′ : W′ ⇒ N′}
         {b : A′ ⇒ A + C} {b′ : B′ ⇒ B + D} {kb : S ⊗₀ A′ ⇒ S ⊗₀ B′}
       → T ∘ id ⊗₁ b ≈ id ⊗₁ b′ ∘ kb
       → R ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ Rt
       → (slot₂ᵍ R ∘ slot₁ᵍ T) ∘ id ⊗₁ (b ⊗₁ j)
       ≈ id ⊗₁ (b′ ⊗₁ j′) ∘ (slot₂ᵍ Rt ∘ slot₁ᵍ kb)
  peel {T = T} {R} {Rt} {j} {j′} {b} {b′} {kb} eT eR = begin
    (slot₂ᵍ R ∘ slot₁ᵍ T) ∘ id ⊗₁ (b ⊗₁ j)
      ≈⟨ refl⟩∘⟨ pair-slots b j ⟩
    (slot₂ᵍ R ∘ slot₁ᵍ T) ∘ (slot₁ᵍ (id ⊗₁ b) ∘ slot₂ᵍ (id ⊗₁ j))
      ≈⟨ assoc ○ (refl⟩∘⟨ sym-assoc) ⟩
    slot₂ᵍ R ∘ ((slot₁ᵍ T ∘ slot₁ᵍ (id ⊗₁ b)) ∘ slot₂ᵍ (id ⊗₁ j))
      ≈⟨ refl⟩∘⟨ (⟺ slot₁ᵍ-∘ ○ slot₁ᵍ-cong eT ○ slot₁ᵍ-∘) ⟩∘⟨refl ⟩
    slot₂ᵍ R ∘ ((slot₁ᵍ (id ⊗₁ b′) ∘ slot₁ᵍ kb) ∘ slot₂ᵍ (id ⊗₁ j))
      ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ slots-comm) ○ sym-assoc) ⟩
    slot₂ᵍ R ∘ ((slot₁ᵍ (id ⊗₁ b′) ∘ slot₂ᵍ (id ⊗₁ j)) ∘ slot₁ᵍ kb)
      ≈˘⟨ refl⟩∘⟨ pair-slots b′ j ⟩∘⟨refl ⟩
    slot₂ᵍ R ∘ (id ⊗₁ (b′ ⊗₁ j) ∘ slot₁ᵍ kb)
      ≈⟨ pullˡ tail ⟩
    (id ⊗₁ (b′ ⊗₁ j′) ∘ slot₂ᵍ Rt) ∘ slot₁ᵍ kb
      ≈⟨ assoc ⟩
    id ⊗₁ (b′ ⊗₁ j′) ∘ (slot₂ᵍ Rt ∘ slot₁ᵍ kb)  ∎
    where
      slots-comm : slot₁ᵍ kb ∘ slot₂ᵍ (id ⊗₁ j) ≈ slot₂ᵍ (id ⊗₁ j) ∘ slot₁ᵍ kb
      slots-comm = (refl⟩∘⟨ slot₂-str j) ○ slot₁-pad j ○ (⟺ (slot₂-str j) ⟩∘⟨refl)

      tail : slot₂ᵍ R ∘ id ⊗₁ (b′ ⊗₁ j) ≈ id ⊗₁ (b′ ⊗₁ j′) ∘ slot₂ᵍ Rt
      tail = (refl⟩∘⟨ ((refl⟩⊗⟨ serialize₁₂) ○ split₂ʳ)) ○ pullˡ (slot₂-pad b′) ○ assoc
           ○ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ (slot₂-str j)) ○ ⟺ slot₂ᵍ-∘ ○ slot₂ᵍ-cong eR
                       ○ slot₂ᵍ-∘ ○ (slot₂-str j′ ⟩∘⟨refl)))
           ○ sym-assoc ○ ((merge₂ʳ ○ (refl⟩⊗⟨ (⟺ serialize₁₂))) ⟩∘⟨refl)

-- The point-free `⊗idᵏ-trace`: unrolling `f ⊗ᵉ idᴹ` along a word runs `f` on the
-- word's `A`-letters and carries the `C`-letters along.  `Split`'s two indices
-- are exactly the elementwise `lefts`/`rights` of the word.
run-⊗id : (f : Machine A B) {n k m : ℕ} (w : Split n k m)
        → run (mk (state f) (tstep (step f) (id {St f ⊗₀ C}))) n ∘ id ⊗₁ ι {A} {C} w
        ≈ id ⊗₁ ι {B} {C} w ∘ slot₁ (run f k)
run-⊗id f []       = identityˡ ○ ⟺ (elimʳ slot₁-id)
run-⊗id f (a∷ w) =
    (refl⟩∘⟨ split₂ʳ) ○ sym-assoc ○ (peel tstep-i₁ (run-⊗id f w) ⟩∘⟨refl) ○ assoc
  ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ slot₁-α) ○ sym-assoc ○ (slot-α ⟩∘⟨refl) ○ assoc
              ○ (refl⟩∘⟨ ⟺ slot₁ᵍ-∘)))
  ○ sym-assoc ○ (⟺ split₂ʳ ⟩∘⟨refl)
run-⊗id f (c∷ w) =
    (refl⟩∘⟨ split₂ʳ) ○ sym-assoc ○ (peel tstep-i₂ (run-⊗id f w) ⟩∘⟨refl) ○ assoc
  ○ (refl⟩∘⟨ ((elimʳ slot₁-id ⟩∘⟨refl) ○ slot-σ))
  ○ sym-assoc ○ (⟺ split₂ʳ ⟩∘⟨refl)

-- The closed form: `eval (f ⊗ᵉ idᴹ) n` is `eval f` on the word's `A`-subword,
-- with the `C`-subword passed through.  This is the elementwise `⊗idᵉ-resp`'s
-- `fillˡ xs <$>ᴹ eval f (lefts xs)`, read as a diagram.
eval-⊗id : (f : Machine A B) {n k m : ℕ} (w : Split n k m)
         → eval (f ⊗ᵉ idᴹ {C}) n ∘ ι w ≈ ι w ∘ (eval f k ⊗₁ id)
eval-⊗id f {n} w = (⊗idᵉ-collapse f n ⟩∘⟨refl) ○ ⟺ cl-∘ʳ ○ cl-cong (run-⊗id f {n} w)
                 ○ cl-∘ˡ ○ (refl⟩∘⟨ cl-slot₁)

⊗idᵉ-resp : {f g : Machine A B} → f ≈ᵉ g → (f ⊗ᵉ idᴹ {C}) ≈ᵉ (g ⊗ᵉ idᴹ)
⊗idᵉ-resp {A} {B} {C} {f} {g} e n = pow-unique′ {A} {C} n λ {k} {m} w →
  eval-⊗id f {n} w ○ (refl⟩∘⟨ (e k ⟩⊗⟨refl)) ○ ⟺ (eval-⊗id g {n} w)

------------------------------------------------------------------------
-- Splitting the tensor, and the congruence
------------------------------------------------------------------------

-- The tensor is the composite of its two one-sided halves: the elementwise
-- `⊗-split`, and the only place a *state* interchange is needed.
⊗-split : (f : Machine A B) (g : Machine C D)
        → (f ⊗ᵉ g) ≈ᵉ ((f ⊗ᵉ idᴹ {D}) ∘ᴹ (idᴹ {A} ⊗ᵉ g))
⊗-split {A} {B} {C} {D} f g = ⟺ᴹ (sim (ρ⇒ ⊗₁ λ⇒) dsc-u pt-u step-u)
  where
    dsc-u : discard (state f ⊛ state g) ∘ (ρ⇒ ⊗₁ λ⇒)
          ≈ discard ((state f ⊛ Iˢ) ⊛ (Iˢ ⊛ state g))
    dsc-u = assoc ○ (refl⟩∘⟨ ⟺ ⊗.homomorphism)
          ○ (refl⟩∘⟨ (⟺ ((coherence₃ ⟩∘⟨refl) ○ unitorʳ-commute-from)
                      ⟩⊗⟨ ⟺ unitorˡ-commute-from))

    pt-u : (ρ⇒ ⊗₁ λ⇒) ∘ point ((state f ⊛ Iˢ) ⊛ (Iˢ ⊛ state g))
         ≈ point (state f ⊛ state g)
    pt-u = sym-assoc ○ ((⟺ ⊗.homomorphism) ⟩∘⟨refl)
         ○ ((  (pullˡ unitorʳ-commute-from ○ assoc
                ○ (refl⟩∘⟨ ((⟺ coherence₃ ⟩∘⟨refl) ○ unitorˡ.isoʳ)) ○ identityʳ)
            ⟩⊗⟨ (pullˡ unitorˡ-commute-from ○ assoc
                 ○ (refl⟩∘⟨ unitorˡ.isoʳ) ○ identityʳ)) ⟩∘⟨refl)

    step-u : (ρ⇒ ⊗₁ λ⇒) ⊗₁ id ∘ (onL (step (f ⊗ᵉ idᴹ {D})) ∘ onR (step (idᴹ {A} ⊗ᵉ g)))
           ≈ step (f ⊗ᵉ g) ∘ (ρ⇒ ⊗₁ λ⇒) ⊗₁ id
    step-u = (refl⟩∘⟨ ((onL-tstep ⟩∘⟨ onR-tstep) ○ tstep-∘
                       ○ tstep-cong (elimʳ (onR-cong onL-id ○ onR-id))
                                    (elimˡ (onL-cong onR-id ○ onL-id))))
           ○ tstep-sim (onL-sim onL-collapseʳ) (onR-sim onR-collapseˡ)

private
  -- Tensoring on the left is tensoring on the right, conjugated by the braiding.
  braid-conj : (M : Machine A B) (N : Machine C D)
             → (M ⊗ᵉ N) ≈ᵉ (σᴹ ∘ᴹ ((N ⊗ᵉ M) ∘ᴹ σᴹ))
  braid-conj M N = ⟺ᴹ identityˡ-∘ᴹ ○ᴹ (⟺ᴹ σᴹ-involutive ⟩∘ᴹ⟨reflᴹ)
                 ○ᴹ assoc-∘ᴹ ○ᴹ (reflᴹ⟩∘ᴹ⟨ braiding-commuteᴹ)

id⊗ᵉ-resp : {g h : Machine C D} → g ≈ᵉ h → (idᴹ {A} ⊗ᵉ g) ≈ᵉ (idᴹ ⊗ᵉ h)
id⊗ᵉ-resp {g = g} {h} e = braid-conj idᴹ g
                        ○ᴹ (reflᴹ⟩∘ᴹ⟨ (⊗idᵉ-resp e ⟩∘ᴹ⟨reflᴹ))
                        ○ᴹ ⟺ᴹ (braid-conj idᴹ h)

⊗ᵉ-resp-≈ᵉ : {f h : Machine A B} {g i : Machine C D}
           → f ≈ᵉ h → g ≈ᵉ i → (f ⊗ᵉ g) ≈ᵉ (h ⊗ᵉ i)
⊗ᵉ-resp-≈ᵉ {f = f} {h} {g} {i} e₁ e₂ =
  ⊗-split f g ○ᴹ (⊗idᵉ-resp e₁ ⟩∘ᴹ⟨ id⊗ᵉ-resp e₂) ○ᴹ ⟺ᴹ (⊗-split h i)

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
-- What is missing (`⊗ᵉ-homomorphism`, `assoc-commute`, `⊗ᵉ-resp-≈ᵉ`, hence the
-- bundles) is missing for a state-side reason, not a ⊕-side one: each needs the
-- action of one factor of a re-bracketed state tree to be recognized as the
-- action of the same factor of another — the `σ-onR`/`σ-onL` pair below is that
-- statement for the state braiding, and it is the one the braiding square
-- needed.  `⊗ᵉ-resp-≈ᵉ` needs more: the elementwise `⊗idᵏ-trace` splits a
-- *word* over `A ⊎ C` into its two subwords, i.e. the iterated distributor
-- `pow n (A + C) ≅ Σ`, which binary distributivity does not hand over.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Cocartesian as Cocart
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)

import CategoricalCrypto.SFunM.Spike.Interchange as Interchange
import CategoricalCrypto.SFunM.Spike.Laws as Laws
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD

module CategoricalCrypto.SFunM.Spike.Tensor {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv
open Interchange 𝒱
open Laws 𝒱
open MD.MonoidalDistributive dist
open Mealy 𝒱
open Machine
open State

open import Categories.Category.Monoidal.Properties monoidal using (coherence₁; coherence₃)
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open BraidedProps braided using (braiding-coherence)

private variable A B C D P Q R X Y Z : Obj

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

-- A state map conjugating the steps passes through both interface slots…
slot₁-sim : {u : P ⇒ R} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
          → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
          → u ⊗₁ id {Y ⊗₀ Z} ∘ slot₁ k ≈ slot₁ k′ ∘ u ⊗₁ id
slot₁-sim {u = u} {k} {k′} e = begin
  u ⊗₁ id ∘ (α⇒ ∘ (k ⊗₁ id ∘ α⇐))            ≈⟨ pullˡ pad-α⇒ ⟩
  (α⇒ ∘ (u ⊗₁ id) ⊗₁ id) ∘ (k ⊗₁ id ∘ α⇐)    ≈⟨ center merge₁ˡ ⟩
  α⇒ ∘ ((u ⊗₁ id ∘ k) ⊗₁ id ∘ α⇐)            ≈⟨ refl⟩∘⟨ (e ⟩⊗⟨refl ○ split₁ˡ) ⟩∘⟨refl ⟩
  α⇒ ∘ ((k′ ⊗₁ id ∘ (u ⊗₁ id) ⊗₁ id) ∘ α⇐)   ≈⟨ refl⟩∘⟨ pullʳ (⟺ pad-α⇐) ⟩
  α⇒ ∘ (k′ ⊗₁ id ∘ (α⇐ ∘ u ⊗₁ id))           ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇒ ∘ (k′ ⊗₁ id ∘ α⇐)) ∘ u ⊗₁ id           ∎
  where
    pad-α⇒ : u ⊗₁ id {Y ⊗₀ Z} ∘ α⇒ ≈ α⇒ ∘ (u ⊗₁ id {Y}) ⊗₁ id {Z}
    pad-α⇒ = (refl⟩⊗⟨ (⟺ ⊗.identity)) ⟩∘⟨refl ○ ⟺ assoc-commute-from

    pad-α⇐ : α⇐ ∘ u ⊗₁ id {X ⊗₀ Z} ≈ (u ⊗₁ id {X}) ⊗₁ id {Z} ∘ α⇐
    pad-α⇐ = (refl⟩∘⟨ (refl⟩⊗⟨ (⟺ ⊗.identity))) ○ assoc-commute-to

-- …the second one being the first conjugated by an interface braiding.
slot₂-sim : {u : P ⇒ R} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
          → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
          → u ⊗₁ id {Z ⊗₀ Y} ∘ slot₂ k ≈ slot₂ k′ ∘ u ⊗₁ id
slot₂-sim {u = u} {k} {k′} e = begin
  u ⊗₁ id ∘ slot₂ k                            ≈⟨ refl⟩∘⟨ slot₂-slot₁ ⟩
  u ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ (slot₁ k ∘ id ⊗₁ σ⇒))  ≈⟨ pullˡ (⟺ (pad-transport u σ⇒)) ⟩
  (id ⊗₁ σ⇒ ∘ u ⊗₁ id) ∘ (slot₁ k ∘ id ⊗₁ σ⇒)  ≈⟨ center (slot₁-sim e) ⟩
  id ⊗₁ σ⇒ ∘ ((slot₁ k′ ∘ u ⊗₁ id) ∘ id ⊗₁ σ⇒) ≈⟨ refl⟩∘⟨ pullʳ (⟺ (pad-transport u σ⇒)) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ k′ ∘ (id ⊗₁ σ⇒ ∘ u ⊗₁ id)) ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (id ⊗₁ σ⇒ ∘ (slot₁ k′ ∘ id ⊗₁ σ⇒)) ∘ u ⊗₁ id ≈˘⟨ slot₂-slot₁ ⟩∘⟨refl ⟩
  slot₂ k′ ∘ u ⊗₁ id                           ∎

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
sim {S = S} {T} {k} {k′} u ed ep e n = begin
  λ⇒ ∘ (discard S ⊗₁ id ∘ (Rn ∘ (point S ⊗₁ id ∘ λ⇐)))
    ≈˘⟨ refl⟩∘⟨ ed ⟩⊗⟨refl ⟩∘⟨refl ⟩
  λ⇒ ∘ ((discard T ∘ u) ⊗₁ id ∘ (Rn ∘ (point S ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ○ (refl⟩∘⟨ assoc) ⟩
  λ⇒ ∘ (discard T ⊗₁ id ∘ (u ⊗₁ id ∘ (Rn ∘ (point S ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (run-sim u e n) ⟩
  λ⇒ ∘ (discard T ⊗₁ id ∘ ((Rn′ ∘ u ⊗₁ id) ∘ (point S ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (discard T ⊗₁ id ∘ (Rn′ ∘ (u ⊗₁ id ∘ (point S ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ ep ⟩⊗⟨refl) ⟩
  λ⇒ ∘ (discard T ⊗₁ id ∘ (Rn′ ∘ (point T ⊗₁ id ∘ λ⇐)))  ∎
  where
    Rn  = run (mk S k) n
    Rn′ = run (mk T k′) n

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

-- A step that ignores the state slots into both interface slots as itself.
slot₁-str : (h : X ⇒ Y) → slot₁ {P} (id ⊗₁ h) ≈ id ⊗₁ (h ⊗₁ id {Z})
slot₁-str h = pullˡ assoc-commute-from ○ cancelʳ associator.isoʳ

slot₂-str : (h : X ⇒ Y) → slot₂ {P} (id ⊗₁ h) ≈ id ⊗₁ (id {Z} ⊗₁ h)
slot₂-str h = slot₂-slot₁ ○ (refl⟩∘⟨ slot₁-str h ⟩∘⟨refl)
            ○ (refl⟩∘⟨ merge₂ʳ) ○ merge₂ʳ ○ refl⟩⊗⟨ (⟺ (pad-braid _ h))

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

-- Two maps out of a distributed sum agree as soon as their branches do: this is
-- the lever that replaces the ⊕-side coherence chains.
δ-unique : {u v : X ⊗₀ (A + B) ⇒ Y}
         → u ∘ id ⊗₁ i₁ ≈ v ∘ id ⊗₁ i₁ → u ∘ id ⊗₁ i₂ ≈ v ∘ id ⊗₁ i₂ → u ≈ v
δ-unique e₁ e₂ = insertʳ distributeˡ.isoʳ
               ○ (∘-distribˡ-[] ○ []-cong₂ e₁ e₂ ○ ⟺ ∘-distribˡ-[]) ⟩∘⟨refl
               ○ cancelʳ distributeˡ.isoʳ

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

δ⇐-i₁ : δ⇐ ∘ id {X} ⊗₁ i₁ ≈ i₁ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₁ = (refl⟩∘⟨ ⟺ inject₁) ○ cancelˡ distributeˡ.isoˡ

δ⇐-i₂ : δ⇐ ∘ id {X} ⊗₁ i₂ ≈ i₂ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₂ = (refl⟩∘⟨ ⟺ inject₂) ○ cancelˡ distributeˡ.isoˡ

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

-- A trivial left state factor sees an `onR` action as the action itself…
onR-collapseˡ : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → λ⇒ ⊗₁ id ∘ onR k ≈ k ∘ λ⇒ ⊗₁ id
onR-collapseˡ {k = k} = begin
  λ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))   ≈˘⟨ coherence₁ ⟩∘⟨refl ⟩
  (λ⇒ ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))  ≈⟨ cancelInner associator.isoʳ ⟩
  λ⇒ ∘ (id ⊗₁ k ∘ α⇒)                ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  k ∘ (λ⇒ ∘ α⇒)                      ≈⟨ refl⟩∘⟨ coherence₁ ⟩
  k ∘ λ⇒ ⊗₁ id                       ∎

-- …and a trivial right one an `onL` action, which is `discard-onL` at `id`.
onL-collapseʳ : {k : P ⊗₀ A ⇒ P ⊗₀ B} → ρ⇒ ⊗₁ id ∘ onL k ≈ k ∘ ρ⇒ ⊗₁ id
onL-collapseʳ {P = P} =
    ((⟺ dsc-id) ⟩⊗⟨refl ⟩∘⟨refl) ○ discard-onL ○ (refl⟩∘⟨ dsc-id ⟩⊗⟨refl)
  where
    dsc-id : dsc (id {unit}) ≈ ρ⇒ {P}
    dsc-id = elimʳ ⊗.identity

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

-- `swp` is natural in the interface factor it moves out, too — the mirror of
-- `Interchange`'s `swp-natural`, obtained from it by involutivity.
swp-natural′ : (g : X ⇒ Y) → swp {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ swp
swp-natural′ g = begin
  swp ∘ (id ⊗₁ g) ⊗₁ id                ≈⟨ refl⟩∘⟨ insertʳ swp-swp ⟩
  swp ∘ (((id ⊗₁ g) ⊗₁ id ∘ swp) ∘ swp) ≈˘⟨ refl⟩∘⟨ swp-natural g ⟩∘⟨refl ⟩
  swp ∘ ((swp ∘ id ⊗₁ g) ∘ swp)        ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ (swp ∘ (id ⊗₁ g ∘ swp))        ≈⟨ cancelˡ swp-swp ⟩
  id ⊗₁ g ∘ swp                        ∎

-- Both state-side actions carry a square that is natural in the interface…
onL-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onL {Q = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onL k
onL-branch {k = k} {t} {j} {j′} e = begin
  (swp ∘ (t ⊗₁ id ∘ swp)) ∘ id ⊗₁ j        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  swp ∘ (t ⊗₁ id ∘ (swp ∘ id ⊗₁ j))        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swp-natural j ⟩
  swp ∘ (t ⊗₁ id ∘ ((id ⊗₁ j) ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ e ⟩⊗⟨refl ○ split₁ˡ) ⟩
  swp ∘ (((id ⊗₁ j′) ⊗₁ id ∘ k ⊗₁ id) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ○ pullˡ (swp-natural′ j′) ○ assoc ⟩
  id ⊗₁ j′ ∘ (swp ∘ (k ⊗₁ id ∘ swp))       ∎

onR-branch : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {t : Q ⊗₀ X ⇒ Q ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onR {P = P} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onR k
onR-branch {k = k} {t} {j} {j′} e = begin
  (α⇐ ∘ (id ⊗₁ t ∘ α⇒)) ∘ id ⊗₁ j          ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇐ ∘ (id ⊗₁ t ∘ (α⇒ ∘ id ⊗₁ j))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ⟩
  α⇐ ∘ (id ⊗₁ t ∘ (id ⊗₁ (id ⊗₁ j) ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ e ○ split₂ʳ) ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ j′) ∘ id ⊗₁ k) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc
       ○ pullˡ (assoc-commute-to ○ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ○ assoc ⟩
  id ⊗₁ j′ ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))         ∎

-- …hence both distribute over the tensor of steps.
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

private
  σ⊗-inv : σ⇒ {P} {Q} ⊗₁ id {A} ∘ σ⇒ {Q} {P} ⊗₁ id ≈ id
  σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

-- The state-side arm: braiding the state pair swaps which factor acts.  The
-- braiding crosses `k`\'s whole block, so `unbraid` puts the padding on one side
-- and the two residual obligations are the block hexagon (`σ-splitˡ`/`σ-splitʳ`).
σ-onR : {k : Q ⊗₀ A ⇒ Q ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onR {P = P} k ≈ onL {Q = P} k ∘ σ⇒ ⊗₁ id {A}
σ-onR {k = k} = begin
  σ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))              ≈⟨ sym-assoc ⟩
  (σ⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ k ∘ α⇒)              ≈⟨ unbraid k ⟩
  ((σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇒) ∘ (k ⊗₁ id ∘ (σ⇒ ∘ α⇒))
    ≈⟨ out ⟩∘⟨ (refl⟩∘⟨ inn) ⟩
  swp ∘ (k ⊗₁ id ∘ (swp ∘ σ⇒ ⊗₁ id))            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  swp ∘ ((k ⊗₁ id ∘ swp) ∘ σ⇒ ⊗₁ id)            ≈⟨ sym-assoc ⟩
  (swp ∘ (k ⊗₁ id ∘ swp)) ∘ σ⇒ ⊗₁ id            ∎
  where
    out : (σ⇒ {P} {Q} ⊗₁ id {B} ∘ α⇐) ∘ σ⇒ ≈ swp
    out = (refl⟩∘⟨ σ-splitʳ) ○ cancelInner associator.isoˡ
        ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

    inn : σ⇒ {P} {Q ⊗₀ A} ∘ α⇒ ≈ swp ∘ σ⇒ ⊗₁ id
    inn = (σ-splitˡ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ
        ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc

-- …and the mirror arm follows by conjugating with the braiding.
σ-onL : {k : P ⊗₀ A ⇒ P ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onL {Q = Q} k ≈ onR {P = Q} k ∘ σ⇒ ⊗₁ id {A}
σ-onL {k = k} = begin
  σ⇒ ⊗₁ id ∘ onL k                        ≈˘⟨ refl⟩∘⟨ cancelʳ σ⊗-inv ⟩
  σ⇒ ⊗₁ id ∘ ((onL k ∘ σ⇒ ⊗₁ id) ∘ σ⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ σ-onR ⟩∘⟨refl ⟩
  σ⇒ ⊗₁ id ∘ ((σ⇒ ⊗₁ id ∘ onR k) ∘ σ⇒ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  σ⇒ ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ (onR k ∘ σ⇒ ⊗₁ id))
    ≈⟨ cancelˡ σ⊗-inv ⟩
  onR k ∘ σ⇒ ⊗₁ id                        ∎

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

private
  -- The braiding is trivial on the unit, so it leaves a paired point and a
  -- paired discard alone.
  σ-unit : σ⇒ {unit} {unit} ≈ id
  σ-unit = insertˡ unitorˡ.isoˡ ○ (refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃))
         ○ unitorˡ.isoˡ

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

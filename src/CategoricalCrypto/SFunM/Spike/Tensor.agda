{-# OPTIONS --safe --without-K #-}

-- SPIKE: the interface tensor of the machine layer, over a distributive base.
--
-- `Spike.Mealy`'s `⊗` pairs STATES; the tensor here pairs INTERFACES, and is
-- `CategoricalCrypto.SFunM.Monoidal`'s `_⊗ᵉ_` written point-free: a paired state
-- acts on a sum interface by distributing (`δ⇐`), copairing the two one-sided
-- actions, and reassembling (`δ⇒`).  Two levers carry the layer:
--   * a map out of a distributed sum is its two components (`δ-unique`), so the
--     ⊕-side equations split into branch goals instead of coherence chains;
--   * `sim` is the point-free `≈ᵉ-sim`, and `pureᴹ` a functor from the base, so
--     the structural morphisms and their coherence come from `+-monoidal`.

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

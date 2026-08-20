{-# OPTIONS --safe --without-K #-}

-- SPIKE: reshuffling the interface around an action on slot 1.
--
-- The interface tensor's congruence has to recognize "the step acts on the
-- `A`-subword of a mixed word" as "the step acts on slot 1", and the two differ
-- by a reshuffle that carries the untouched letters past the step.  Every such
-- goal is an equality of two `frame k i o` — `k` in slot 1, the rest of the
-- interface reshuffled on both sides — and `frame-pad` slides the untouched
-- factor from one side of the frame to the other, which is `Interchange`'s
-- `repad` lifted through `id ⊗₁ _`.  What is left is generator-free: `rot-in`
-- and `rot-out`, one hexagon each.
--
-- This is the point-free price of the elementwise `lefts`/`fillˡ` recursion, and
-- it is the only genuinely braided content in the congruence: `slot-α` merges
-- two paddings, `slot-σ` moves one letter out of the way.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Product using (_,_)

import CategoricalCrypto.SFunM.Spike.Interchange as Interchange
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.SlotFrame {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv
open Interchange 𝒱
open Mealy 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open MonoidalUtilities monoidal using (pentagon-inv)

private variable A B C P Q R S X Y Z : Obj

------------------------------------------------------------------------
-- Reassociating a slot's padding
------------------------------------------------------------------------

σ⊗-inv : σ⇒ {P} {Q} ⊗₁ id {A} ∘ σ⇒ {Q} {P} ⊗₁ id ≈ id
σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

private
  -- The pentagon, read as "a padding may be split or merged".
  pent⇒ : α⇒ ∘ (α⇒ {X} {Y} {Z} ⊗₁ id {S}) ≈ id ⊗₁ α⇐ ∘ (α⇒ ∘ α⇒)
  pent⇒ = insertˡ (pad-inv associator.isoˡ) ○ (refl⟩∘⟨ pentagon)

  pent⇐ : α⇒ ∘ (α⇐ {X} {Y} {Z} ⊗₁ id {S} ∘ α⇐) ≈ α⇐ ∘ id ⊗₁ α⇒
  pent⇐ = (refl⟩∘⟨ (insertʳ (pad-inv associator.isoˡ) ○ (pentagon-inv ⟩∘⟨refl)))
        ○ sym-assoc ○ (cancelˡ associator.isoʳ ⟩∘⟨refl)

-- Slot 1 is natural in the factor it leaves alone.
slot₁-pad : (h : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y}
          → slot₁ᵍ {Z = S} k ∘ id ⊗₁ (id ⊗₁ h) ≈ id ⊗₁ (id ⊗₁ h) ∘ slot₁ᵍ {Z = Z} k
slot₁-pad h {k} = begin
  (α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ (id ⊗₁ h)
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇒ ∘ (k ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (id ⊗₁ h)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc-commute-to ○ ((⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl)) ⟩
  α⇒ ∘ (k ⊗₁ id ∘ (id ⊗₁ h ∘ α⇐))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (pad-transport k h)) ⟩
  α⇒ ∘ ((id ⊗₁ h ∘ k ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ (id ⊗₁ h ∘ (k ⊗₁ id ∘ α⇐))
    ≈⟨ pullˡ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ○ assoc ⟩
  id ⊗₁ (id ⊗₁ h) ∘ (α⇒ ∘ (k ⊗₁ id ∘ α⇐))  ∎

-- Slot 2 is natural in its untouched factor, which is slot 1's braided.
slot₂-pad : (h : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y}
          → slot₂ᵍ {Z = S} k ∘ id ⊗₁ (h ⊗₁ id) ≈ id ⊗₁ (h ⊗₁ id) ∘ slot₂ᵍ {Z = Z} k
slot₂-pad h {k} = begin
  slot₂ᵍ k ∘ id ⊗₁ (h ⊗₁ id)
    ≈⟨ slot₂-slot₁ ⟩∘⟨refl ⟩
  (id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒)) ∘ id ⊗₁ (h ⊗₁ id)
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ (id ⊗₁ σ⇒ ∘ id ⊗₁ (h ⊗₁ id)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (h , id)) ○ split₂ʳ) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ (id ⊗₁ (id ⊗₁ h) ∘ id ⊗₁ σ⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (slot₁-pad h) ⟩
  id ⊗₁ σ⇒ ∘ ((id ⊗₁ (id ⊗₁ h) ∘ slot₁ᵍ k) ∘ id ⊗₁ σ⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ σ⇒ ∘ (id ⊗₁ (id ⊗₁ h) ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒))
    ≈⟨ pullˡ (merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (id , h)) ○ split₂ʳ) ○ assoc ⟩
  id ⊗₁ (h ⊗₁ id) ∘ (id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒))
    ≈˘⟨ refl⟩∘⟨ slot₂-slot₁ ⟩
  id ⊗₁ (h ⊗₁ id) ∘ slot₂ᵍ k  ∎

-- A step that ignores the state slots into either interface slot as itself.
slot₁-str : (h : X ⇒ Y) → slot₁ᵍ {Z = Z} (id {P} ⊗₁ h) ≈ id ⊗₁ (h ⊗₁ id)
slot₁-str h = pullˡ assoc-commute-from ○ cancelʳ associator.isoʳ

slot₂-str : (h : X ⇒ Y) → slot₂ᵍ {Z = Z} (id {P} ⊗₁ h) ≈ id ⊗₁ (id ⊗₁ h)
slot₂-str h = slot₂-slot₁ ○ (refl⟩∘⟨ slot₁-str h ⟩∘⟨refl)
            ○ (refl⟩∘⟨ merge₂ʳ) ○ merge₂ʳ ○ refl⟩⊗⟨ (⟺ (pad-braid _ h))

------------------------------------------------------------------------
-- The frame
------------------------------------------------------------------------

-- `k` acting on slot 1, with the rest of the interface reshuffled on both
-- sides.  Every goal the word split raises is an equality of two of these.
frame : (P ⊗₀ X ⇒ R ⊗₀ Y) → (A ⇒ X ⊗₀ Z) → (Y ⊗₀ Z ⇒ B) → P ⊗₀ A ⇒ R ⊗₀ B
frame k i o = id ⊗₁ o ∘ (slot₁ᵍ k ∘ id ⊗₁ i)

frame-cong : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i i′ : A ⇒ X ⊗₀ Z} {o o′ : Y ⊗₀ Z ⇒ B}
           → i ≈ i′ → o ≈ o′ → frame k i o ≈ frame k i′ o′
frame-cong ei eo = (refl⟩⊗⟨ eo) ⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ei))

frame-∘ʳ : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ Z ⇒ B} {j : C ⇒ A}
         → frame k i o ∘ id ⊗₁ j ≈ frame k (i ∘ j) o
frame-∘ʳ = assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ merge₂ʳ)

frame-∘ˡ : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ Z ⇒ B} {j : B ⇒ C}
         → id ⊗₁ j ∘ frame k i o ≈ frame k i (j ∘ o)
frame-∘ˡ = pullˡ merge₂ʳ

-- Sliding the untouched factor from one side of the frame to the other.
frame-pad : (s : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ S ⇒ B}
          → frame k (id ⊗₁ s ∘ i) o ≈ frame k i (o ∘ id ⊗₁ s)
frame-pad s = (refl⟩∘⟨ refl⟩∘⟨ split₂ʳ) ○ (refl⟩∘⟨ pullˡ (slot₁-pad s))
            ○ (refl⟩∘⟨ assoc) ○ pullˡ merge₂ʳ

------------------------------------------------------------------------
-- Two nested slots, as frames
------------------------------------------------------------------------

slot₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y} → slot₁ᵍ {Z = Z} k ≈ frame k id id
slot₁-frame = ⟺ (elimˡ ⊗.identity ○ elimʳ ⊗.identity)

slot₁₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₁ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ≈ frame k α⇒ α⇐
slot₁₁-frame {k = k} = begin
  α⇒ ∘ ((α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ⊗₁ id ∘ α⇐)
    ≈⟨ refl⟩∘⟨ (split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)) ⟩∘⟨refl ⟩
  α⇒ ∘ ((α⇒ ⊗₁ id ∘ ((k ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id)) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc)) ⟩
  α⇒ ∘ (α⇒ ⊗₁ id ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐)))
    ≈⟨ pullˡ pent⇒ ⟩
  (id ⊗₁ α⇐ ∘ (α⇒ ∘ α⇒)) ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐))
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (α⇒ ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ (pad-α⇒ k)) ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ ((k ⊗₁ id ∘ α⇒) ∘ (α⇐ ⊗₁ id ∘ α⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (k ⊗₁ id ∘ (α⇒ ∘ (α⇐ ⊗₁ id ∘ α⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pent⇐ ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (k ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ α⇒)))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc) ○ (refl⟩∘⟨ sym-assoc) ⟩
  id ⊗₁ α⇐ ∘ ((α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ α⇒)  ∎

slot₂₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ≈ frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐)
slot₂₁-frame = slot₂-slot₁ ○ (refl⟩∘⟨ slot₁₁-frame ⟩∘⟨refl)
             ○ (refl⟩∘⟨ frame-∘ʳ) ○ frame-∘ˡ

slot₁₂-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₁ᵍ {Z = Z} (slot₂ᵍ {Z = S} k)
             ≈ frame k (α⇒ ∘ σ⇒ ⊗₁ id) (σ⇒ ⊗₁ id ∘ α⇐)
slot₁₂-frame = slot₁ᵍ-cong slot₂-slot₁ ○ (slot₁ᵍ-∘ ○ (refl⟩∘⟨ slot₁ᵍ-∘))
             ○ (slot₁-str σ⇒ ⟩∘⟨ (slot₁₁-frame ⟩∘⟨ slot₁-str σ⇒))
             ○ (refl⟩∘⟨ frame-∘ʳ) ○ frame-∘ˡ

------------------------------------------------------------------------
-- The generator-free residue: one hexagon each way
------------------------------------------------------------------------

-- Rotating a factor out of a pair, and back in.
rot-in : ∀ {X S Z : Obj} → α⇒ {X} {Z} {S} ∘ (σ⇒ {S} {X ⊗₀ Z} ∘ α⇒ {S} {X} {Z})
       ≈ id ⊗₁ σ⇒ ∘ (α⇒ {X} {S} {Z} ∘ σ⇒ {S} {X} ⊗₁ id {Z})
rot-in = (refl⟩∘⟨ (σ-splitˡ ⟩∘⟨refl)) ○ (refl⟩∘⟨ cancelʳ associator.isoˡ)
       ○ cancelˡ associator.isoʳ

rot-out : ∀ {Y S Z : Obj} → σ⇒ {Y ⊗₀ Z} {S} ∘ α⇐ {Y} {Z} {S}
        ≈ (α⇒ {S} {Y} {Z} ∘ (σ⇒ {Y} {S} ⊗₁ id {Z} ∘ α⇐ {Y} {S} {Z}))
          ∘ id ⊗₁ σ⇒ {Z} {S}
rot-out = (σ-splitʳ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ cancelʳ associator.isoʳ) ○ sym-assoc

private
  -- The rotation absorbs the braiding it was built from.
  swap-in : ∀ {X S Z : Obj} → (α⇒ {X} {Z} {S} ∘ σ⇒ {S} {X ⊗₀ Z}) ∘ swapˡ {X} {S} {Z}
          ≈ id ⊗₁ σ⇒ {S} {Z}
  swap-in = assoc ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (rot-in ⟩∘⟨refl)
          ○ assoc ○ (refl⟩∘⟨ (cancelInner σ⊗-inv ○ associator.isoʳ)) ○ identityʳ

------------------------------------------------------------------------
-- The two arms the word split needs
------------------------------------------------------------------------

-- Merging the paddings of two nested slots…
slot-α : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
       → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ∘ id ⊗₁ α⇒
       ≈ id ⊗₁ α⇒ ∘ slot₁ᵍ {Z = Z} (slot₂ᵍ {Z = S} k)
slot-α {X = X} {Y = Y} {S = S} {Z = Z} {k = k} = begin
  slot₂ᵍ (slot₁ᵍ k) ∘ id ⊗₁ α⇒
    ≈⟨ slot₂₁-frame ⟩∘⟨refl ⟩
  frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐) ∘ id ⊗₁ α⇒
    ≈⟨ frame-∘ʳ ⟩
  frame k ((α⇒ ∘ σ⇒) ∘ α⇒) (σ⇒ ∘ α⇐)
    ≈⟨ frame-cong (assoc ○ rot-in {X} {S} {Z}) (rot-out {Y} {S} {Z}) ⟩
  frame k (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id)) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-pad (σ⇒ {S} {Z}) ⟩
  frame k (α⇒ ∘ σ⇒ ⊗₁ id) ((swapˡ ∘ id ⊗₁ σ⇒) ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-cong refl (cancelʳ (pad-inv (commutative {Z} {S}))) ⟩
  frame k (α⇒ ∘ σ⇒ ⊗₁ id) swapˡ
    ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ α⇒ ∘ frame k (α⇒ ∘ σ⇒ ⊗₁ id) (σ⇒ ⊗₁ id ∘ α⇐)
    ≈˘⟨ refl⟩∘⟨ slot₁₂-frame ⟩
  id ⊗₁ α⇒ ∘ slot₁ᵍ (slot₂ᵍ k)  ∎

-- …and moving one letter of the padding out of the way.
slot-σ : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
       → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ∘ id ⊗₁ swapˡ
       ≈ id ⊗₁ swapˡ ∘ slot₁ᵍ {Z = S ⊗₀ Z} k
slot-σ {X = X} {Y = Y} {S = S} {Z = Z} {k = k} = begin
  slot₂ᵍ (slot₁ᵍ k) ∘ id ⊗₁ swapˡ
    ≈⟨ slot₂₁-frame ⟩∘⟨refl ⟩
  frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐) ∘ id ⊗₁ swapˡ
    ≈⟨ frame-∘ʳ ⟩
  frame k ((α⇒ ∘ σ⇒) ∘ swapˡ) (σ⇒ ∘ α⇐)
    ≈⟨ frame-cong (swap-in {X} {S} {Z}) (rot-out {Y} {S} {Z}) ⟩
  frame k (id ⊗₁ σ⇒) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈˘⟨ frame-cong identityʳ refl ⟩
  frame k (id ⊗₁ σ⇒ ∘ id) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-pad (σ⇒ {S} {Z}) ⟩
  frame k id ((swapˡ ∘ id ⊗₁ σ⇒) ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-cong refl (cancelʳ (pad-inv (commutative {Z} {S}))) ⟩
  frame k id swapˡ
    ≈˘⟨ frame-cong refl identityʳ ⟩
  frame k id (swapˡ ∘ id)
    ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ swapˡ ∘ frame k id id
    ≈˘⟨ refl⟩∘⟨ slot₁-frame ⟩
  id ⊗₁ swapˡ ∘ slot₁ᵍ k  ∎

-- Splitting one padding into two.
slot₁-α : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
        → slot₁ᵍ {Z = Z ⊗₀ S} k ∘ id ⊗₁ α⇒
        ≈ id ⊗₁ α⇒ ∘ slot₁ᵍ {Z = S} (slot₁ᵍ {Z = Z} k)
slot₁-α {k = k} = begin
  slot₁ᵍ k ∘ id ⊗₁ α⇒                       ≈⟨ slot₁-frame ⟩∘⟨refl ⟩
  frame k id id ∘ id ⊗₁ α⇒                  ≈⟨ frame-∘ʳ ⟩
  frame k (id ∘ α⇒) id                      ≈⟨ frame-cong identityˡ refl ⟩
  frame k α⇒ id                              ≈˘⟨ frame-cong refl associator.isoʳ ⟩
  frame k α⇒ (α⇒ ∘ α⇐)                       ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ α⇒ ∘ frame k α⇒ α⇐                   ≈˘⟨ refl⟩∘⟨ slot₁₁-frame ⟩
  id ⊗₁ α⇒ ∘ slot₁ᵍ (slot₁ᵍ k)  ∎

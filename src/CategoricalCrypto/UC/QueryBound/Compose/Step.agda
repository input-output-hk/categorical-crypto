{-# OPTIONS --safe --without-K --guardedness #-}

-- The composite's step, computed: `Unfolding` discharged for the real `𝒫ᴵ`
-- composite, and `qb-∘` with it.
--
-- A `𝒢`-composite is `traceᴹ (α ∘ᴹ (g ⊗ᵉ f) ∘ᴹ γ)`, and `α`/`γ` are towers of
-- `pureᴹ`s: collapsing them first (`α-pure`, `γ-pure`) replaces the two `∘ᴹ`
-- towers by ONE machine whose state is `state g ⊛ state f` and whose step pre-
-- and post-composes the wire.  Only then does anything become elementwise —
-- chased at a point from the start, the composite spends a delay junction per
-- structural morphism of `α`, `γ`, the two towers and `iter`
-- (`Protocol.Machine.Pin`).
--
-- `Pt k h` is "`k` is `returnₚ ∘ h`, up to the junctions a point-free composite
-- spends".  The coproduct's structural morphisms are built by dualizing the
-- cartesian ones, so their functions are read off the injection equations of
-- `Cocartesian.Ext` rather than by reduction; the tensor's are `pureᵏ` on the
-- nose.  `Hα`/`Hγ` then come out as the routing `UC.QueryBound.Compose`'s
-- header describes: `γ` feeds `f` the external `Pos A` and the loop's `Neg B`,
-- and `g` the external `Neg C` and the loop's `Pos B`; `α` sends `f`'s `Neg A`
-- and `g`'s `Pos C` out of the composite and the other two back onto the loop.
--
-- The certificate now uses `Collapse.kᴳ` directly and reuses `collapseᵀ` rather
-- than rebuilding the wire collapse as `Bd≈`.  The target names the same raw
-- G-composition before it is packed into the Category record; congruence is
-- isolated in `Collapse.Congruence`.  Measured cost: 12 s with dependencies
-- cached, or 96 s including that congruence rebuild, down from 721 s.

open import Categories.Category using (Category; _[_≈_])
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.GConstructionTrace as GT

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap; assocʳ′; assocˡ′)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂) renaming (map to ⊎map; swap to ⊎swap)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (_∘′_; case_of_; id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Elgot using (padₛ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (𝒱ₚ; distₚ; 𝒫ₚ; Elgotₚ; Remainingₚ; Tracedₚ; module Elgotᵏ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; ⊎assocˡ; ⊎assocʳ)
open import CategoricalCrypto.UC.QueryBound using (Certified; QB; qb-resp-≈)
open import CategoricalCrypto.UC.QueryBound.Compose using (module Compose)

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Collapse.Congruence as ColCong
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.UC.QueryBound.Compose.Step where

private
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module VD = MD.MonoidalDistributive (distₚ 0ℓ)
  module VE = CE V.U VD.cocartesian
  module VS = BraidedProps.Shorthands V.braided
  module VW = MonoidalUtilities.Shorthands V.monoidal
  module EK = Elgotᵏ 0ℓ

module MB = Bundle (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
module MK = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open MK using (∘ᴹ-resp-≈ᴹ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
open Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
open Trace.Remaining (Remainingₚ 0ℓ) using (trace-resp-≈ᴹ)

private
  module W = GT MK.Mealy-Category MB.Mealy-Monoidal (Tracedₚ 0ℓ)

------------------------------------------------------------------------
-- `Dₚ` shorthands: the library's lemmas take their subjects explicitly, and a
-- transparent chain would strand them as metas (as in `UC.Machine.Run`).

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

  map-map : (d : Dₚ A′) (h : A′ → B′) (k : B′ → C′)
          → mapₚ k (mapₚ h d) ≈ₚ mapₚ (k ∘′ h) d
  map-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) (returnₚ ∘′ k)
            ⟨≈⟩ bindᶠ (λ a → >>=ₚ-identityˡ (h a) (returnₚ ∘′ k))

  return-≡ : {x y : A′} → x ≡ y → returnₚ x ≈ₚ returnₚ y
  return-≡ refl = ≈refl

------------------------------------------------------------------------
-- Pure base morphisms, at a point

private
  -- `k` is `returnₚ ∘ h`, up to junctions.
  Pt : {X Y : Set} → (X → Dₚ Y) → (X → Y) → Set
  Pt {X} k h = (x : X) → k x ≈ₚ returnₚ (h x)

  pt-id : {X : Set} → Pt (V.id {X}) id
  pt-id _ = ≈refl

  pt-∘ : {X Y Z : Set} {k : Y → Dₚ Z} {h : Y → Z} {l : X → Dₚ Y} {m : X → Y}
       → Pt k h → Pt l m → Pt (k V.∘ l) (λ x → h (m x))
  pt-∘ {k = k} {m = m} pk pl x = bindˣ (pl x) ⟨≈⟩ >>=ₚ-identityˡ (m x) k ⟨≈⟩ pk (m x)

  pt-pre : {X Y Z : Set} {l : X → Dₚ Y} {m : X → Y} → Pt l m
         → (k : Y → Dₚ Z) (x : X) → (k V.∘ l) x ≈ₚ k (m x)
  pt-pre {m = m} pl k x = bindˣ (pl x) ⟨≈⟩ >>=ₚ-identityˡ (m x) k

  pt-⊗ : {S T X Y : Set} {k : S → Dₚ T} {h : S → T} {l : X → Dₚ Y} {m : X → Y}
       → Pt k h → Pt l m → Pt (k V.⊗₁ l) (λ p → h (proj₁ p) , m (proj₂ p))
  pt-⊗ {h = h} {l = l} {m} pk pl p =
        bindˣ (pk (proj₁ p))
    ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p)) (λ b → l (proj₂ p) >>=ₚ λ d → returnₚ (b , d))
    ⟨≈⟩ bindˣ (pl (proj₂ p))
    ⟨≈⟩ >>=ₚ-identityˡ (m (proj₂ p)) (λ d → returnₚ (h (proj₁ p) , d))

  pt-≗ : {X Y : Set} {k : X → Dₚ Y} {h m : X → Y}
       → ((x : X) → h x ≡ m x) → Pt k h → Pt k m
  pt-≗ e p x = p x ⟨≈⟩ return-≡ (e x)

  -- The tensor's structural morphisms are `pureᵏ` on the nose…
  pt-α⇒ : {X Y Z : Set} → Pt (VW.α⇒ {X} {Y} {Z}) assocʳ′
  pt-α⇒ _ = ≈refl

  pt-α⇐ : {X Y Z : Set} → Pt (VW.α⇐ {X} {Y} {Z}) assocˡ′
  pt-α⇐ _ = ≈refl

  pt-σ : {X Y : Set} → Pt (VS.σ⇒ {X} {Y}) swap
  pt-σ _ = ≈refl

  pt-i₁ : {X Y : Set} → Pt (VD.i₁ {X} {Y}) inj₁
  pt-i₁ _ = ≈refl

  pt-i₂ : {X Y : Set} → Pt (VD.i₂ {X} {Y}) inj₂
  pt-i₂ _ = ≈refl

  -- …while the coproduct's are dualized copairings, read off the injections.
  pt-+₁ : {X Y Z W : Set} {k : X → Dₚ Y} {h : X → Y} {l : Z → Dₚ W} {m : Z → W}
        → Pt k h → Pt l m → Pt (k VD.+₁ l) (⊎map h m)
  pt-+₁ {k = k} {l = l} pk pl (inj₁ x) =
        ≈sym (pt-pre pt-i₁ (k VD.+₁ l) x) ⟨≈⟩ VD.+₁∘i₁ x ⟨≈⟩ pt-∘ pt-i₁ pk x
  pt-+₁ {k = k} {l = l} pk pl (inj₂ z) =
        ≈sym (pt-pre pt-i₂ (k VD.+₁ l) z) ⟨≈⟩ VD.+₁∘i₂ z ⟨≈⟩ pt-∘ pt-i₂ pl z

  pt-α+⇒ : {X Y Z : Set} → Pt (VE.α+⇒ {X} {Y} {Z}) ⊎assocʳ
  pt-α+⇒ (inj₁ (inj₁ x)) =
    ≈sym (pt-pre (pt-∘ pt-i₁ pt-i₁) VE.α+⇒ x) ⟨≈⟩ VE.α+⇒-i₁i₁ x
  pt-α+⇒ (inj₁ (inj₂ y)) =
        ≈sym (pt-pre (pt-∘ pt-i₁ pt-i₂) VE.α+⇒ y) ⟨≈⟩ VE.α+⇒-i₁i₂ y
    ⟨≈⟩ pt-∘ pt-i₂ pt-i₁ y
  pt-α+⇒ (inj₂ z) =
    ≈sym (pt-pre pt-i₂ VE.α+⇒ z) ⟨≈⟩ VE.α+⇒-i₂ z ⟨≈⟩ pt-∘ pt-i₂ pt-i₂ z

  pt-α+⇐ : {X Y Z : Set} → Pt (VE.α+⇐ {X} {Y} {Z}) ⊎assocˡ
  pt-α+⇐ (inj₁ x) =
    ≈sym (pt-pre pt-i₁ VE.α+⇐ x) ⟨≈⟩ VE.α+⇐-i₁ x ⟨≈⟩ pt-∘ pt-i₁ pt-i₁ x
  pt-α+⇐ (inj₂ (inj₁ y)) =
        ≈sym (pt-pre (pt-∘ pt-i₂ pt-i₁) VE.α+⇐ y) ⟨≈⟩ VE.α+⇐-i₂i₁ y
    ⟨≈⟩ pt-∘ pt-i₁ pt-i₂ y
  pt-α+⇐ (inj₂ (inj₂ z)) =
    ≈sym (pt-pre (pt-∘ pt-i₂ pt-i₂) VE.α+⇐ z) ⟨≈⟩ VE.α+⇐-i₂i₂ z

  pt-+-swap : {X Y : Set} → Pt (VD.+-swap {X} {Y}) ⊎swap
  pt-+-swap (inj₁ x) = ≈sym (pt-pre pt-i₁ VD.+-swap x) ⟨≈⟩ VE.+-swap-i₁ x
  pt-+-swap (inj₂ y) = ≈sym (pt-pre pt-i₂ VD.+-swap y) ⟨≈⟩ VE.+-swap-i₂ y

------------------------------------------------------------------------
-- The two state-side actions, at a point

private
  Hswp : {P Q R : Set} → (P × Q) × R → (P × R) × Q
  Hswp ((p , q) , r) = (p , r) , q

  pt-swp : {P Q R : Set} → Pt (swp {P} {Q} {R}) Hswp
  pt-swp = pt-≗ (λ _ → refl) (pt-∘ pt-α⇐ (pt-∘ (pt-⊗ pt-id pt-σ) pt-α⇒))

  -- `Elgotᵏ.onR-padₛ`'s mirror; `onL` conjugates by `swp` instead of `α`.
  onLₑ : {P Q X Y : Set} (k : P × X → Dₚ (P × Y)) (q : Q) (p : P) (x : X)
       → onL k ((p , q) , x) ≈ₚ mapₚ (λ r → (proj₁ r , q) , proj₂ r) (k (p , x))
  onLₑ k q p x =
        bindˣ (bindˣ (pt-swp ((p , q) , x)))
    ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ((p , x) , q) (k V.⊗₁ V.id))
    ⟨≈⟩ bindˣ (bindᶠ (λ b → >>=ₚ-identityˡ q (λ d → returnₚ (b , d))))
    ⟨≈⟩ bind-map (k (p , x)) (_, q) swp
    ⟨≈⟩ bindᶠ (λ r → pt-swp (r , q))

  tstepₑ₁ : {P Q X Y Z W : Set} (k : P × X → Dₚ (Q × Y)) (l : P × Z → Dₚ (Q × W))
            (p : P) (x : X)
          → tstep k l (p , inj₁ x) ≈ₚ mapₚ (λ r → proj₁ r , inj₁ (proj₂ r)) (k (p , x))
  tstepₑ₁ k l p x =
        ≈sym (pt-pre (pt-⊗ pt-id pt-i₁) (tstep k l) (p , x))
    ⟨≈⟩ tstep-i₁ {k = k} {l = l} (p , x)
    ⟨≈⟩ bindᶠ (pt-⊗ pt-id pt-i₁)

  tstepₑ₂ : {P Q X Y Z W : Set} (k : P × X → Dₚ (Q × Y)) (l : P × Z → Dₚ (Q × W))
            (p : P) (z : Z)
          → tstep k l (p , inj₂ z) ≈ₚ mapₚ (λ r → proj₁ r , inj₂ (proj₂ r)) (l (p , z))
  tstepₑ₂ k l p z =
        ≈sym (pt-pre (pt-⊗ pt-id pt-i₂) (tstep k l) (p , z))
    ⟨≈⟩ tstep-i₂ {k = k} {l = l} (p , z)
    ⟨≈⟩ bindᶠ (pt-⊗ pt-id pt-i₂)

------------------------------------------------------------------------
-- Collapsing a tower of pure machines

-- Each combinator's shape is read off the composite it collapses, so the base
-- morphism it produces is fixed by the goal and needs no argument.
private
  ∘ᴹ-pureᴹ : {X Y Z : Set} {h : Y V.⇒ Z} {k : X V.⇒ Y}
             {N : Machine Y Z} {M : Machine X Y}
           → N ≈ᴹ pureᴹ h → M ≈ᴹ pureᴹ k → (N ∘ᴹ M) ≈ᴹ pureᴹ (h V.∘ k)
  ∘ᴹ-pureᴹ {h = h} {k} e₁ e₂ = ∘ᴹ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ h k)

  ⊗ᵉ-pureʳ : {X Y Z : Set} {u : X V.⇒ Y} {M : Machine X Y} → M ≈ᴹ pureᴹ u
           → (M ⊗ᵉ idᴹ {Z}) ≈ᴹ pureᴹ (u VD.+₁ V.id)
  ⊗ᵉ-pureʳ {u = u} e = ⊗ᵉ-resp-≈ᴹ e reflᴹ
                   ○ᴹ ≲⇒≈ᴹ˘ (⊗ᵉ-resp-≲ ≲-refl pureᴹ-id) ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ u V.id)

  ⊗ᵉ-pureˡ : {X Y Z : Set} {v : X V.⇒ Y} {M : Machine X Y} → M ≈ᴹ pureᴹ v
           → (idᴹ {Z} ⊗ᵉ M) ≈ᴹ pureᴹ (V.id VD.+₁ v)
  ⊗ᵉ-pureˡ {v = v} e = ⊗ᵉ-resp-≈ᴹ reflᴹ e
                   ○ᴹ ≲⇒≈ᴹ˘ (⊗ᵉ-resp-≲ pureᴹ-id ≲-refl) ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ V.id v)

------------------------------------------------------------------------
-- The two wires of a `𝒢`-composite

module _ (A B C : Iface) where

  module _ (g : Proc B C) (f : Proc A B) where

    private
      Sg = St g
      Sf = St f

      Sᶜ : Col.MC.State
      Sᶜ = Col.Sᴳ g f

      stepg = step g
      stepf = step f

      bodyStep : (Sg × Sf) × ((Pos A ⊎ Neg C) ⊎ (Neg B ⊎ Pos B))
               → Dₚ ((Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
      bodyStep = Col.kᴳ g f

      Bd : Col.MC.Machine ((Pos A ⊎ Neg C) ⊎ (Neg B ⊎ Pos B))
                          ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
      Bd = Col.MC.mk Sᶜ bodyStep

      Nᶜ : Proc A C
      Nᶜ = Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
             (Col.MC.mk (Col.Sᴳ g f) (Col.kᴳ g f))

      pointᶜ = point Sᶜ tt
      stepᶜ  = step Nᶜ

      solveᶜ = solve Sᶜ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) bodyStep

      module CP = Compose {A} {B} {C} Sg Sf (point (state g) tt) (point (state f) tt)
                          pointᶜ stepg stepf stepᶜ solveᶜ

      ----------------------------------------------------------------
      -- The two factors' steps, inside the composite's

      padF : Sg → Sf × (Neg A ⊎ Pos B) → (Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
      padF sg r = (sg , proj₁ r) , Col.outᶠ (proj₂ r)

      padG : Sf → Sg × (Neg B ⊎ Pos C) → (Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
      padG sf r = (proj₁ r , sf) , Col.outᵍ (proj₂ r)

      bodyF : (sg : Sg) (sf : Sf) (v : Pos A ⊎ Neg B)
            → bodyStep ((sg , sf) , (case v of λ where
                (inj₁ a) → inj₁ (inj₁ a)
                (inj₂ b) → inj₂ (inj₁ b)))
            ≈ₚ mapₚ (padF sg) (stepf (sf , v))
      bodyF sg sf (inj₁ a) = ≈refl
      bodyF sg sf (inj₂ b) = ≈refl

      bodyG : (sg : Sg) (sf : Sf) (u : Pos B ⊎ Neg C)
            → bodyStep ((sg , sf) , (case u of λ where
                (inj₁ b) → inj₂ (inj₂ b)
                (inj₂ n) → inj₁ (inj₂ n)))
            ≈ₚ mapₚ (padG sf) (stepg (sg , u))
      bodyG sg sf (inj₁ b) = ≈refl
      bodyG sg sf (inj₂ n) = ≈refl

      ----------------------------------------------------------------
      -- …and the solved loop the walk consumes

      resumeF-pad : (sg : Sg) (r : Sf × (Neg A ⊎ Pos B))
                  → CP.resumeF sg r ≈ₚ solveᶜ (padF sg r)
      resumeF-pad sg (sf , inj₁ n) = ≈refl
      resumeF-pad sg (sf , inj₂ q) = ≈refl

      resumeG-pad : (sf : Sf) (r : Sg × (Neg B ⊎ Pos C))
                  → CP.resumeG sf r ≈ₚ solveᶜ (padG sf r)
      resumeG-pad sf (sg , inj₁ b) = ≈refl
      resumeG-pad sf (sg , inj₂ p) = ≈refl

      -- One external step feeds its input in on the `A` summand…
      step-in : (s : Sg × Sf) (z : Pos A ⊎ Neg C)
              → stepᶜ (s , z) ≈ₚ (bodyStep (s , inj₁ z) >>=ₚ solveᶜ)
      step-in s z = bindˣ (pt-pre (pt-⊗ pt-id pt-i₁) bodyStep (s , z))

      -- …the dispatch exits on the `B` summand…
      solve-outᶜ : (s : Sg × Sf) (o : Neg A ⊎ Pos C) → solveᶜ (s , inj₁ o) ≈ₚ returnₚ (s , o)
      solve-outᶜ s o =
            ≈sym (pt-pre (pt-⊗ pt-id pt-i₁) solveᶜ (s , o))
        ⟨≈⟩ solve-i₁ Sᶜ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) bodyStep (s , o)

      -- …and re-enters the body on the loop wire.
      solve-loopᶜ : (s : Sg × Sf) (y : Neg B ⊎ Pos B)
                  → solveᶜ (s , inj₂ y) ≈ₚ (bodyStep (s , inj₂ y) >>=ₚ solveᶜ)
      solve-loopᶜ s y =
            ≈sym (pt-pre (pt-⊗ pt-id pt-i₂) solveᶜ (s , y))
        ⟨≈⟩ solve-i₂ Sᶜ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) bodyStep (s , y)
        ⟨≈⟩ solve-loop Sᶜ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) bodyStep (s , y)
        ⟨≈⟩ bindˣ (pt-pre (pt-⊗ pt-id pt-i₂) bodyStep (s , y))

      resumedF : (sg : Sg) (sf : Sf) (v : Pos A ⊎ Neg B)
               → (mapₚ (padF sg) (stepf (sf , v)) >>=ₚ solveᶜ)
               ≈ₚ (stepf (sf , v) >>=ₚ CP.resumeF sg)
      resumedF sg sf v = bind-map (stepf (sf , v)) (padF sg) solveᶜ
                     ⟨≈⟩ bindᶠ (λ r → ≈sym (resumeF-pad sg r))

      resumedG : (sg : Sg) (sf : Sf) (u : Pos B ⊎ Neg C)
               → (mapₚ (padG sf) (stepg (sg , u)) >>=ₚ solveᶜ)
               ≈ₚ (stepg (sg , u) >>=ₚ CP.resumeG sf)
      resumedG sg sf u = bind-map (stepg (sg , u)) (padG sf) solveᶜ
                     ⟨≈⟩ bindᶠ (λ r → ≈sym (resumeG-pad sf r))

      unfoldᶜ : CP.Unfolding
      unfoldᶜ = record
        { point-eq  = >>=ₚ-identityˡ (tt , tt) (point (state g) V.⊗₁ point (state f))
        ; step-L    = λ sg sf a →
              step-in (sg , sf) (inj₁ a)
          ⟨≈⟩ bindˣ (bodyF sg sf (inj₁ a))
          ⟨≈⟩ resumedF sg sf (inj₁ a)
        ; step-R    = λ sg sf n →
              step-in (sg , sf) (inj₂ n)
          ⟨≈⟩ bindˣ (bodyG sg sf (inj₂ n))
          ⟨≈⟩ resumedG sg sf (inj₂ n)
        ; solve-out = solve-outᶜ
        ; solve-B⁻  = λ sg sf b →
              solve-loopᶜ (sg , sf) (inj₁ b)
          ⟨≈⟩ bindˣ (bodyF sg sf (inj₂ b))
          ⟨≈⟩ resumedF sg sf (inj₂ b)
        ; solve-B⁺  = λ sg sf q →
              solve-loopᶜ (sg , sf) (inj₂ q)
          ⟨≈⟩ bindˣ (bodyG sg sf (inj₁ q))
          ⟨≈⟩ resumedG sg sf (inj₁ q)
        }

      eqᶜ : Nᶜ Col.S.≈ᴹ
              Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
                (Col.W.α Col.MC.∘ᴹ ((g Col.T.⊗ᵉ f) Col.MC.∘ᴹ Col.W.γ))
      eqᶜ = Col.S.⟺ᴹ
        (Col.collapseᵀ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} g f)

    qbᵢ-∘ : {c c′ : ℕ} → Certified {B} {C} c g → Certified {A} {B} c′ f
          → QB {A} {C} (c ℕ.* c′)
              (Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
                (Col.W.α Col.MC.∘ᴹ ((g Col.T.⊗ᵉ f) Col.MC.∘ᴹ Col.W.γ)))
    qbᵢ-∘ qg qf = Nᶜ , CP.qbᵢ-∘ᵍ unfoldᶜ qg qf , eqᶜ

qb-∘ : (A B C : Iface) {c c′ : ℕ} (g : Proc B C) (f : Proc A B)
     → QB {B} {C} c g → QB {A} {B} c′ f
     → QB {A} {C} (c ℕ.* c′)
         (Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
           (Col.W.α Col.MC.∘ᴹ ((g Col.T.⊗ᵉ f) Col.MC.∘ᴹ Col.W.γ)) )
qb-∘ A B C g f (Ng , cg , eg) (Nf , cf , ef) =
  qb-resp-≈ {A} {C}
    (ColCong.compose-resp-≈ᴹ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} eg ef)
    (qbᵢ-∘ A B C Ng Nf cg cf)

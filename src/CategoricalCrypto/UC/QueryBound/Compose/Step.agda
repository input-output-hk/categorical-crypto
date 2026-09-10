{-# OPTIONS --safe --without-K --guardedness #-}

-- The composite's step, computed: `Unfolding` discharged for the real `𝒫ᴵ`
-- composite, and `qb-∘` with it.
--
-- The certificate now uses `Collapse.kᴳ` directly and reuses `collapseᵀ` rather
-- than rebuilding the wire collapse as `Bd≈`.  The target names the same raw
-- G-composition before it is packed into the Category record; congruence is
-- paid by the hom-level closure in `Compose.Laws`, not by this concrete step.
-- Measured warm cost: 10.1 s, down from 12.2 s; rebuilding this module no
-- longer rebuilds the 94 s congruence module.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Distributive as MD

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (_∘′_; case_of_; id)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (𝒱ₚ; distₚ; 𝒫ₚ; Elgotₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound using (Certified; QB)
open import CategoricalCrypto.UC.QueryBound.Compose using (module Compose)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.UC.QueryBound.Compose.Step where

private
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module VD = MD.MonoidalDistributive (distₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

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

------------------------------------------------------------------------
-- Pure base morphisms, at a point

private
  -- `k` is `returnₚ ∘ h`, up to junctions.
  Pt : {X Y : Set} → (X → Dₚ Y) → (X → Y) → Set
  Pt {X} k h = (x : X) → k x ≈ₚ returnₚ (h x)

  pt-id : {X : Set} → Pt (V.id {X}) id
  pt-id _ = ≈refl

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

  pt-i₁ : {X Y : Set} → Pt (VD.i₁ {X} {Y}) inj₁
  pt-i₁ _ = ≈refl

  pt-i₂ : {X Y : Set} → Pt (VD.i₂ {X} {Y}) inj₂
  pt-i₂ _ = ≈refl

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

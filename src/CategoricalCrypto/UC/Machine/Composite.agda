{-# OPTIONS --safe --without-K --guardedness #-}

-- A `𝒢ₚ`-composite of two processes as one product-state machine, and the six
-- equations that read its step off.
--
-- `Unfolding` is the whole interface to the composite's step.  A `𝒢ₚ`-composite
-- is a ⊕-trace whose loop wire is the intermediate interface in both
-- directions, so its step solves that loop within one external step; the six
-- equations say what the solved loop does in each of its positions, and nothing
-- downstream unfolds a trace or an iteration.  Everything is stated over
-- state/point/step PARAMETERS for the reason noted above
-- `UC.QueryBound.Certificate`.
--
-- `Nᶜ`/`unfoldᶜ`/`eq-∘ᶜ` discharge it for the real `𝒫ᴵ` composite, beside
-- `Machines.Collapse`'s `kᴳ`: the target names the same raw G-composition
-- before it is packed into the Category record.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.UC.Machine.Composite where

------------------------------------------------------------------------
-- The composite's step, as a reader sees it

module Unfold {A B C : Iface} (Sg Sf : Set)
              (pointg : Dₚ Sg) (pointf : Dₚ Sf) (pointᶜ : Dₚ (Sg × Sf))
              (stepg : Sg × (Pos B ⊎ Neg C) → Dₚ (Sg × (Neg B ⊎ Pos C)))
              (stepf : Sf × (Pos A ⊎ Neg B) → Dₚ (Sf × (Neg A ⊎ Pos B)))
              (stepᶜ : (Sg × Sf) × (Pos A ⊎ Neg C) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C)))
              (solveᶜ : (Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
                      → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C)))
              where

  -- Once the token leaves `f` (resp. `g`), an output on the composite's own
  -- interface exits and one on `B` crosses the loop wire to the other factor.
  resumeF : Sg → Sf × (Neg A ⊎ Pos B) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C))
  resumeF sg (sf , inj₁ a) = solveᶜ ((sg , sf) , inj₁ (inj₁ a))
  resumeF sg (sf , inj₂ b) = solveᶜ ((sg , sf) , inj₂ (inj₂ b))

  resumeG : Sf → Sg × (Neg B ⊎ Pos C) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C))
  resumeG sf (sg , inj₁ b) = solveᶜ ((sg , sf) , inj₂ (inj₁ b))
  resumeG sf (sg , inj₂ p) = solveᶜ ((sg , sf) , inj₁ (inj₂ p))

  record Unfolding : Set where
    field
      point-eq  : pointᶜ ≈ₚ (pointg >>=ₚ λ sg → mapₚ (sg ,_) pointf)
      step-L    : (sg : Sg) (sf : Sf) (a : Pos A)
                → stepᶜ ((sg , sf) , inj₁ a) ≈ₚ (stepf (sf , inj₁ a) >>=ₚ resumeF sg)
      step-R    : (sg : Sg) (sf : Sf) (n : Neg C)
                → stepᶜ ((sg , sf) , inj₂ n) ≈ₚ (stepg (sg , inj₂ n) >>=ₚ resumeG sf)
      solve-out : (s : Sg × Sf) (o : Neg A ⊎ Pos C)
                → solveᶜ (s , inj₁ o) ≈ₚ returnₚ (s , o)
      solve-B⁻  : (sg : Sg) (sf : Sf) (b : Neg B)
                → solveᶜ ((sg , sf) , inj₂ (inj₁ b))
                ≈ₚ (stepf (sf , inj₂ b) >>=ₚ resumeF sg)
      solve-B⁺  : (sg : Sg) (sf : Sf) (b : Pos B)
                → solveᶜ ((sg , sf) , inj₂ (inj₂ b))
                ≈ₚ (stepg (sg , inj₁ b) >>=ₚ resumeG sf)

  -- One external step of the composite, at the shapes a consumer reading it
  -- off needs: `g` refuses, `g` calls `f`, and `f` answers `g`, which exits.
  module Walk (u : Unfolding) where
    open Unfolding u

    R-bot : (sg : Sg) (sf : Sf) (n : Neg C) → stepg (sg , inj₂ n) ≈ₚ botₚ
          → stepᶜ ((sg , sf) , inj₂ n) ≈ₚ botₚ
    R-bot sg sf n eq = step-R sg sf n ⟨≈⟩ bindˣ eq ⟨≈⟩ bot-bind-≈ₚ _

    R-down : (sg : Sg) (sf : Sf) (n : Neg C) (sg′ : Sg) (b : Neg B)
           → stepg (sg , inj₂ n) ≈ₚ returnₚ (sg′ , inj₁ b)
           → {D : Dₚ (Sf × (Neg A ⊎ Pos B))} → stepf (sf , inj₂ b) ≈ₚ D
           → stepᶜ ((sg , sf) , inj₂ n) ≈ₚ (D >>=ₚ resumeF sg′)
    R-down sg sf n sg′ b eq eqf =
      step-R sg sf n ⟨≈⟩ bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ b) (resumeG sf)
      ⟨≈⟩ solve-B⁻ sg′ sf b ⟨≈⟩ bindˣ eqf

    F-up : (sg : Sg) (sf : Sf) (b : Pos B) (sg′ : Sg) (p : Pos C)
         → stepg (sg , inj₁ b) ≈ₚ returnₚ (sg′ , inj₂ p)
         → resumeF sg (sf , inj₂ b) ≈ₚ returnₚ ((sg′ , sf) , inj₂ p)
    F-up sg sf b sg′ p eq =
      solve-B⁺ sg sf b ⟨≈⟩ bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ p) (resumeG sf)
      ⟨≈⟩ solve-out (sg′ , sf) (inj₂ p)

private
  module 𝒫  = Category 𝒫ᴵ

open MC

------------------------------------------------------------------------
-- The two wires of a `𝒢`-composite

module _ (A B C : Iface) where

  module _ (g : Proc B C) (f : Proc A B) where

    Sg = St g
    Sf = St f

    Sᶜ : State
    Sᶜ = Col.Sᴳ g f

    stepg = step g
    stepf = step f

    bodyStep : (Sg × Sf) × ((Pos A ⊎ Neg C) ⊎ (Neg B ⊎ Pos B))
             → Dₚ ((Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
    bodyStep = Col.kᴳ g f

    private module L = Pw.Loop (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) Sᶜ bodyStep

    Nᶜ : Proc A C
    Nᶜ = L.tracedᴹ

    pointᶜ = point Sᶜ tt
    stepᶜ  = step Nᶜ

    solveᶜ = contᵢ L.body

    module CP = Unfold {A} {B} {C} Sg Sf (point (state g) tt) (point (state f) tt)
                        pointᶜ stepg stepf stepᶜ solveᶜ

    private
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
              L.step-red (sg , sf) (inj₁ a)
          ⟨≈⟩ bindˣ (bodyF sg sf (inj₁ a))
          ⟨≈⟩ resumedF sg sf (inj₁ a)
        ; step-R    = λ sg sf n →
              L.step-red (sg , sf) (inj₂ n)
          ⟨≈⟩ bindˣ (bodyG sg sf (inj₂ n))
          ⟨≈⟩ resumedG sg sf (inj₂ n)
        ; solve-out = λ _ _ → ≈refl
        ; solve-B⁻  = λ sg sf b →
              iterₚ-fix L.body ((sg , sf) , inj₁ b)
          ⟨≈⟩ bindˣ (bodyF sg sf (inj₂ b))
          ⟨≈⟩ resumedF sg sf (inj₂ b)
        ; solve-B⁺  = λ sg sf q →
              iterₚ-fix L.body ((sg , sf) , inj₂ q)
          ⟨≈⟩ bindˣ (bodyG sg sf (inj₁ q))
          ⟨≈⟩ resumedG sg sf (inj₁ q)
        }

    eqᶜ : Nᶜ MS.≈ᴹ
            MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
              (Col.W.α ∘ᴹ ((g T.⊗ᵉ f) ∘ᴹ Col.W.γ))
    eqᶜ = MS.⟺ᴹ (Col.collapseᵀ {Pos A} {Neg A} {Pos B} {Neg B} g f)

    eq-∘ᶜ : Nᶜ MS.≈ᴹ (𝒫._∘_ {A} {B} g f)
    eq-∘ᶜ = eqᶜ MS.○ᴹ Col.compose-raw≈∘ᴳ g f

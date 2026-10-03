{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The wiring and trace algebra the G construction runs on: the
-- loop-body wiring `α`, `γ` of a G-composite, `mid` for its monoidal
-- structure, and the consequences of `TE.Laws` its laws need;
-- `right-superposing` and `⊗-trace-mid` each spend one solver coherence step
-- (`RS` in `Categories.GConstructionIdentityCoherence`, `TM` in
-- `Categories.GConstructionTraceCoherence`).
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE

module Categories.GConstructionTrace
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Interchange.Braided as IB
import Categories.Category.Monoidal.Interchange.Symmetric as IS
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionIdentityCoherence as GCohId
import Categories.GConstructionTraceCoherence as TCoh

open Category C
open Traced Traced
open U.Shorthands Monoidal
open import Categories.Category.Monoidal.Reasoning Monoidal
  using (serialize₁₂; refl⟩⊗⟨_; ⊗-distrib-over-∘; _⟩⊗⟨_)
open import Categories.Morphism.Reasoning C using (introˡ; pullʳ; elimʳ; switch-fromtoʳ; cancelʳ)
open BProps.Shorthands braided

open HomReasoning

open TE Traced public using (β)

Cˢ : SymmetricMonoidalCategory a b c
Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = symmetric }

α : ∀ {A⁻ B⁺ B⁻ C⁺ : Obj} → (B⁻ ⊗₀ C⁺) ⊗₀ (A⁻ ⊗₀ B⁺) ⇒ (A⁻ ⊗₀ C⁺) ⊗₀ (B⁻ ⊗₀ B⁺)
α = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id) ∘ id ⊗₁ α⇐ ∘ α⇒

γ : ∀ {A⁺ B⁺ B⁻ C⁻ : Obj} → (A⁺ ⊗₀ C⁻) ⊗₀ (B⁻ ⊗₀ B⁺) ⇒ (B⁺ ⊗₀ C⁻) ⊗₀ (A⁺ ⊗₀ B⁻)
γ = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (σ⇒ ⊗₁ id)
  ∘ id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ σ⇒

-- The middle-four interchange, the only structural morphism the
-- G-construction's tensor of morphisms needs.  It is upstream's
-- `Interchange.Braided.swapInner.from`, spelled out so that the
-- conversion checker meets the composite directly; the involution, the
-- naturality and the braiding law below are upstream's, read at that
-- spelling.
mid : ∀ {P Q R S : Obj} → (P ⊗₀ Q) ⊗₀ (R ⊗₀ S) ⇒ (P ⊗₀ R) ⊗₀ (Q ⊗₀ S)
mid = α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒

mid-involutive : ∀ {P Q R S : Obj} → mid {P} {Q} {R} {S} ∘ mid ≈ id
mid-involutive = IS.swapInner-commutative symmetric

mid-natural : ∀ {P P′ Q Q′ R R′ S S′ : Obj}
                {f : P ⇒ P′} {g : Q ⇒ Q′} {h : R ⇒ R′} {k : S ⇒ S′} →
              mid ∘ (f ⊗₁ g) ⊗₁ (h ⊗₁ k)
              ≈ (f ⊗₁ h) ⊗₁ (g ⊗₁ k) ∘ mid
mid-natural = IB.swapInner-natural braided

mid-σ : ∀ {P Q R S : Obj} → mid ∘ σ⇒ ⊗₁ σ⇒ ≈ σ⇒ ∘ mid {P} {R} {Q} {S}
mid-σ = switch-fromtoʳ (IS.swapInner-iso symmetric) (assoc ○ IB.swapInner-braiding braided)

-- The unitor and associator squares of `f ⊗₁ᴳ g = mid ∘ f ⊗ g ∘ mid`
-- (`GConstructionMonoidal`, after `absorbˡ`/`absorbʳ`).  `⊗` is strong monoidal
-- with `⊗-homo = swapInner` (upstream `Categories.Functor.Monoidal.Tensor`), and
-- these are its `swapInner-unitˡ`/`-unitʳ`/`-assoc` read through the conjugation.
module _ where
  open import Categories.Category.Construction.Core C
  open import Categories.Category.Monoidal.Properties Monoidal
  open import Categories.Category.Monoidal.Reasoning Monoidal using (_⟩⊗⟨refl)
  open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
  open import Categories.Category.Monoidal.Utilities Monoidal using (_⊗ᵢ_)
  open import Categories.Morphism C
  open import Categories.Morphism.IsoEquiv C
  open import Categories.Morphism.Reasoning C hiding (introˡ; pullʳ; elimʳ; switch-fromtoʳ; cancelʳ)
  open import Categories.Tactic.Category
  open Kelly's
  open Shorthands

  private
    variable O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : Obj

    -- Bracketings, generic so that `solve` meets variables, not the composites.
    unit-shape : {d : O₀ ⇒ O₁} {q₃ : O₁ ⇒ O₂} {q₂ : O₂ ⇒ O₃} {q₁ : O₃ ⇒ O₄} {s : O₄ ⇒ O₅}
                 {p₃ : O₅ ⇒ O₆} {p₂ : O₆ ⇒ O₇} {p₁ : O₇ ⇒ O₈} {a : O₈ ⇒ O₉}
               → a ∘ ((p₁ ∘ p₂ ∘ p₃) ∘ s ∘ q₁ ∘ q₂ ∘ q₃) ∘ d ≈ (a ∘ p₁) ∘ p₂ ∘ (p₃ ∘ s ∘ q₁) ∘ q₂ ∘ (q₃ ∘ d)
    unit-shape = solve C

    assoc-shape : {d : O₀ ⇒ O₁} {b′ : O₁ ⇒ O₂} {c′ : O₂ ⇒ O₃} {x : O₃ ⇒ O₄} {c : O₄ ⇒ O₅}
                  {b : O₅ ⇒ O₆} {a : O₆ ⇒ O₇}
                → a ∘ (b ∘ (c ∘ x ∘ c′) ∘ b′) ∘ d ≈ (a ∘ b ∘ c) ∘ x ∘ (c′ ∘ b′ ∘ d)
    assoc-shape = solve C

    mid-shape : {v : O₀ ⇒ O₁} {w : O₁ ⇒ O₂} {z : O₂ ⇒ O₃} {y : O₃ ⇒ O₄} {x : O₄ ⇒ O₅}
              → x ∘ (y ∘ z ∘ w) ∘ v ≈ (x ∘ y) ∘ z ∘ (w ∘ v)
    mid-shape = solve C

    mid-λ : ∀ {X Y} → mid {unit} {unit} {X} {Y} ≈ λ⇐ ⊗₁ λ⇐ ∘ λ⇒ ∘ λ⇒ ⊗₁ id
    mid-λ = switch-fromtoʳ (≅.sym (unitorˡ ⊗ᵢ idᵢ))
              (switch-fromtoˡ (unitorˡ ⊗ᵢ unitorˡ) (IB.swapInner-unitˡ braided)) ○ assoc

    mid-λ′ : ∀ {X Y} → mid {unit} {X} {unit} {Y} ≈ λ⇐ ⊗₁ id ∘ λ⇐ ∘ λ⇒ ⊗₁ λ⇒
    mid-λ′ {X} {Y} = ⟺ (elimʳ inv) ○ cancelˡ mid-involutive
      where inv : mid {unit} {unit} {X} {Y} ∘ λ⇐ ⊗₁ id ∘ λ⇐ ∘ λ⇒ ⊗₁ λ⇒ ≈ id
            inv = pullˡ (switch-fromtoˡ (unitorˡ ⊗ᵢ unitorˡ) (IB.swapInner-unitˡ braided))
                  ○ assoc ○ refl⟩∘⟨ cancelˡ unitorˡ.isoʳ ○ (⟺ ⊗-distrib-over-∘ ○ (unitorˡ.isoˡ ⟩⊗⟨ unitorˡ.isoˡ) ○ ⊗.identity)

    mid-ρ : ∀ {X Y} → mid {X} {Y} {unit} {unit} ≈ ρ⇐ ⊗₁ ρ⇐ ∘ ρ⇒ ∘ id ⊗₁ λ⇒
    mid-ρ = switch-fromtoʳ (≅.sym (idᵢ ⊗ᵢ unitorˡ))
              (switch-fromtoˡ (unitorʳ ⊗ᵢ unitorʳ) (IB.swapInner-unitʳ braided)) ○ assoc

    mid-ρ′ : ∀ {X Y} → mid {X} {unit} {Y} {unit} ≈ id ⊗₁ λ⇐ ∘ ρ⇐ ∘ ρ⇒ ⊗₁ ρ⇒
    mid-ρ′ {X} {Y} = ⟺ (elimʳ inv) ○ cancelˡ mid-involutive
      where inv : mid {X} {Y} {unit} {unit} ∘ id ⊗₁ λ⇐ ∘ ρ⇐ ∘ ρ⇒ ⊗₁ ρ⇒ ≈ id
            inv = pullˡ (switch-fromtoˡ (unitorʳ ⊗ᵢ unitorʳ) (IB.swapInner-unitʳ braided))
                  ○ assoc ○ refl⟩∘⟨ cancelˡ unitorʳ.isoʳ ○ (⟺ ⊗-distrib-over-∘ ○ (unitorʳ.isoˡ ⟩⊗⟨ unitorʳ.isoˡ) ○ ⊗.identity)

  mid-unitˡ : ∀ {A⁺ A⁻ B⁺ B⁻} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
              id ⊗₁ λ⇒ ∘ (mid ∘ σ⇒ ⊗₁ f ∘ mid) ∘ id ⊗₁ λ⇐ ≈ λ⇐ ⊗₁ id ∘ f ∘ λ⇒ ⊗₁ id
  mid-unitˡ {f = f} = begin
    id ⊗₁ λ⇒ ∘ (mid ∘ σ⇒ ⊗₁ f ∘ mid) ∘ id ⊗₁ λ⇐
      ≈⟨ refl⟩∘⟨ (mid-λ ⟩∘⟨ (σ-unit ⟩⊗⟨refl) ⟩∘⟨ mid-λ′) ⟩∘⟨refl ⟩
    id ⊗₁ λ⇒ ∘ ((λ⇐ ⊗₁ λ⇐ ∘ λ⇒ ∘ λ⇒ ⊗₁ id) ∘ id ⊗₁ f ∘ λ⇐ ⊗₁ id ∘ λ⇐ ∘ λ⇒ ⊗₁ λ⇒) ∘ id ⊗₁ λ⇐
      ≈⟨ unit-shape ⟩
    (id ⊗₁ λ⇒ ∘ λ⇐ ⊗₁ λ⇐) ∘ λ⇒ ∘ (λ⇒ ⊗₁ id ∘ id ⊗₁ f ∘ λ⇐ ⊗₁ id) ∘ λ⇐ ∘ (λ⇒ ⊗₁ λ⇒ ∘ id ⊗₁ λ⇐)
      ≈⟨ (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ unitorˡ.isoʳ))
         ⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⟺ ⊗-distrib-over-∘) ○ ⟺ ⊗-distrib-over-∘
                     ○ ((elim-center Equiv.refl ○ unitorˡ.isoʳ) ⟩⊗⟨ (identityˡ ○ identityʳ)))
         ⟩∘⟨ refl⟩∘⟨ (⟺ ⊗-distrib-over-∘ ○ (identityʳ ⟩⊗⟨ unitorˡ.isoʳ)) ⟩
    λ⇐ ⊗₁ id ∘ λ⇒ ∘ id ⊗₁ f ∘ λ⇐ ∘ λ⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ (pullˡ unitorˡ-commute-from ○ assoc ○ refl⟩∘⟨ cancelˡ unitorˡ.isoʳ) ⟩
    λ⇐ ⊗₁ id ∘ f ∘ λ⇒ ⊗₁ id ∎

  mid-unitʳ : ∀ {A⁺ A⁻ B⁺ B⁻} {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
              id ⊗₁ ρ⇒ ∘ (mid ∘ f ⊗₁ σ⇒ ∘ mid) ∘ id ⊗₁ ρ⇐ ≈ ρ⇐ ⊗₁ id ∘ f ∘ ρ⇒ ⊗₁ id
  mid-unitʳ {f = f} = begin
    id ⊗₁ ρ⇒ ∘ (mid ∘ f ⊗₁ σ⇒ ∘ mid) ∘ id ⊗₁ ρ⇐
      ≈⟨ refl⟩∘⟨ (mid-ρ ⟩∘⟨ (refl⟩⊗⟨ σ-unit) ⟩∘⟨ mid-ρ′) ⟩∘⟨refl ⟩
    id ⊗₁ ρ⇒ ∘ ((ρ⇐ ⊗₁ ρ⇐ ∘ ρ⇒ ∘ id ⊗₁ λ⇒) ∘ f ⊗₁ id ∘ id ⊗₁ λ⇐ ∘ ρ⇐ ∘ ρ⇒ ⊗₁ ρ⇒) ∘ id ⊗₁ ρ⇐
      ≈⟨ unit-shape ⟩
    (id ⊗₁ ρ⇒ ∘ ρ⇐ ⊗₁ ρ⇐) ∘ ρ⇒ ∘ (id ⊗₁ λ⇒ ∘ f ⊗₁ id ∘ id ⊗₁ λ⇐) ∘ ρ⇐ ∘ (ρ⇒ ⊗₁ ρ⇒ ∘ id ⊗₁ ρ⇐)
      ≈⟨ (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ unitorʳ.isoʳ))
         ⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⟺ ⊗-distrib-over-∘) ○ ⟺ ⊗-distrib-over-∘
                     ○ ((identityˡ ○ identityʳ) ⟩⊗⟨ (elim-center Equiv.refl ○ unitorˡ.isoʳ)))
         ⟩∘⟨ refl⟩∘⟨ (⟺ ⊗-distrib-over-∘ ○ (identityʳ ⟩⊗⟨ unitorʳ.isoʳ)) ⟩
    ρ⇐ ⊗₁ id ∘ ρ⇒ ∘ f ⊗₁ id ∘ ρ⇐ ∘ ρ⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ (pullˡ unitorʳ-commute-from ○ assoc ○ refl⟩∘⟨ cancelˡ unitorʳ.isoʳ) ⟩
    ρ⇐ ⊗₁ id ∘ f ∘ ρ⇒ ⊗₁ id ∎

  mid-assoc : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻}
                {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} {g : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} {h : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} →
              id ⊗₁ α⇒ ∘ (mid ∘ (mid ∘ f ⊗₁ g ∘ mid) ⊗₁ h ∘ mid) ∘ id ⊗₁ α⇐
              ≈ α⇐ ⊗₁ id ∘ (mid ∘ f ⊗₁ (mid ∘ g ⊗₁ h ∘ mid) ∘ mid) ∘ α⇒ ⊗₁ id
  mid-assoc {f = f} {g} {h} = begin
    id ⊗₁ α⇒ ∘ (mid ∘ (mid ∘ f ⊗₁ g ∘ mid) ⊗₁ h ∘ mid) ∘ id ⊗₁ α⇐
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ conj ⟩∘⟨refl) ⟩∘⟨refl ⟩
    id ⊗₁ α⇒ ∘ (mid ∘ (mid ⊗₁ id ∘ (f ⊗₁ g) ⊗₁ h ∘ mid ⊗₁ id) ∘ mid) ∘ id ⊗₁ α⇐
      ≈⟨ assoc-shape ⟩
    (id ⊗₁ α⇒ ∘ mid ∘ mid ⊗₁ id) ∘ (f ⊗₁ g) ⊗₁ h ∘ (mid ⊗₁ id ∘ mid ∘ id ⊗₁ α⇐)
      ≈⟨ refl⟩∘⟨ switch-fromtoˡ associator assoc-commute-from ⟩∘⟨refl ⟩
    (id ⊗₁ α⇒ ∘ mid ∘ mid ⊗₁ id) ∘ (α⇐ ∘ F ∘ α⇒) ∘ (mid ⊗₁ id ∘ mid ∘ id ⊗₁ α⇐)
      ≈⟨ mid-shape ⟩
    ((id ⊗₁ α⇒ ∘ mid ∘ mid ⊗₁ id) ∘ α⇐) ∘ F ∘ (α⇒ ∘ mid ⊗₁ id ∘ mid ∘ id ⊗₁ α⇐)
      ≈⟨ out ⟩∘⟨ refl⟩∘⟨ inp ⟩
    (α⇐ ⊗₁ id ∘ mid ∘ id ⊗₁ mid) ∘ F ∘ (id ⊗₁ mid ∘ mid ∘ α⇒ ⊗₁ id)
      ≈˘⟨ assoc-shape ⟩
    α⇐ ⊗₁ id ∘ (mid ∘ (id ⊗₁ mid ∘ F ∘ id ⊗₁ mid) ∘ mid) ∘ α⇒ ⊗₁ id
      ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ conj′ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    α⇐ ⊗₁ id ∘ (mid ∘ f ⊗₁ (mid ∘ g ⊗₁ h ∘ mid) ∘ mid) ∘ α⇒ ⊗₁ id ∎
    where
    F = f ⊗₁ g ⊗₁ h
    Sw = IS.swapInner-iso symmetric
    conj  = (refl⟩⊗⟨ ⟺ (identityˡ ○ identityʳ)) ○ ⊗-distrib-over-∘ ○ (refl⟩∘⟨ ⊗-distrib-over-∘)
    conj′ = (⟺ (identityˡ ○ identityʳ) ⟩⊗⟨refl) ○ ⊗-distrib-over-∘ ○ (refl⟩∘⟨ ⊗-distrib-over-∘)
    out = ((((⟺ (associator.isoˡ ⟩⊗⟨ identityˡ) ○ ⊗-distrib-over-∘) ⟩∘⟨refl)
            ○ assoc ○ (refl⟩∘⟨ IB.swapInner-assoc braided)) ⟩∘⟨refl)
        ○ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ (assoc ○ elimʳ associator.isoʳ))
    inp = (refl⟩∘⟨ (sym-assoc ○ (refl⟩∘⟨ (⟺ (associator.isoˡ ⟩⊗⟨ identityʳ) ○ ⊗-distrib-over-∘)) ○ sym-assoc
                   ○ (to-unique (_≅_.iso ((associator ⊗ᵢ associator) ∘ᵢ Sw ∘ᵢ (Sw ⊗ᵢ idᵢ)))
                                (_≅_.iso (Sw ∘ᵢ (idᵢ ⊗ᵢ Sw) ∘ᵢ associator))
                                (IB.swapInner-assoc braided) ⟩∘⟨refl)
                   ○ assoc ○ assoc))
        ○ cancelˡ associator.isoʳ

module WithTrace (L : TE.Laws Traced) where

  open TE.Laws L

  trace-βyank : ∀ {Y X : Obj} → trace (β {Y} {X} {X}) ≈ id
  trace-βyank = superposing ○ (refl⟩⊗⟨ yanking) ○ ⊗.identity

  trace-gyank : ∀ {Y X B' : Obj} {g : Y ⊗₀ X ⇒ B'} →
                trace (g ⊗₁ id ∘ β {Y} {X} {X}) ≈ g
  trace-gyank = ⟺ trace-∘ˡ ○ elimʳ trace-βyank

  -- Right superposing, the mirror of `Traced.superposing`.
  right-superposing : ∀ {X Y A' B'} {f' : A' ⊗₀ X ⇒ B' ⊗₀ X} →
    trace f' ⊗₁ id {Y} ≈ trace (β ∘ f' ⊗₁ id ∘ β)
  right-superposing {X} {Y} {A'} {B'} {f'} = begin
    trace f' ⊗₁ id
      ≈⟨ introˡ commutative ○ pullʳ (braiding.⇒.commute _) ⟩
    σ⇒ ∘ id ⊗₁ trace f' ∘ σ⇒
      ≈⟨ refl⟩∘⟨ Equiv.sym superposing ⟩∘⟨refl ⟩
    σ⇒ ∘ trace (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒
      ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
    σ⇒ ∘ trace ((α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒ ⊗₁ id)
      ≈⟨ trace-∘ˡ ⟩
    trace (σ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f' ∘ α⇒) ∘ σ⇒ ⊗₁ id)
      ≈⟨ trace-resp-≈ (GCohId.Transport.WithGen.RS Cˢ A' B' X X Y f') ⟩
    trace (β ∘ f' ⊗₁ id ∘ β)
    ∎

  ⊗-trace : ∀ {X Y A A' B B' : Obj}
              {u : A ⊗₀ X ⇒ B ⊗₀ X} {v : A' ⊗₀ Y ⇒ B' ⊗₀ Y} →
            trace u ⊗₁ trace v ≈
            trace (trace ((β ∘ u ⊗₁ id ∘ β) ⊗₁ id ∘ β
                              ∘ (α⇐ ∘ id ⊗₁ v ∘ α⇒) ⊗₁ id ∘ β))
  ⊗-trace {X} {Y} {A} {A'} {B} {B'} {u} {v} = begin
    trace u ⊗₁ trace v
      ≈⟨ serialize₁₂ ⟩
    trace u ⊗₁ id ∘ id ⊗₁ trace v
      ≈⟨ right-superposing ⟩∘⟨ Equiv.sym superposing ⟩
    trace body₁ ∘ trace body₂
      ≈⟨ trace-∘ʳ ⟩
    trace (body₁ ∘ trace body₂ ⊗₁ id)
      ≈⟨ trace-resp-≈ (refl⟩∘⟨ right-superposing) ⟩
    trace (body₁ ∘ trace (β ∘ body₂ ⊗₁ id ∘ β))
      ≈⟨ trace-resp-≈ trace-∘ˡ ⟩
    trace (trace (body₁ ⊗₁ id ∘ β ∘ body₂ ⊗₁ id ∘ β))
    ∎
    where body₁ = β ∘ u ⊗₁ id {B'} ∘ β
          body₂ = α⇐ ∘ id {A} ⊗₁ v ∘ α⇒

  -- The traced category's own "trace is monoidal", with no G-construction
  -- wiring in it: `TM` identifies `⊗-trace`'s β-conjugated body with
  -- `mid ∘ u ⊗ v ∘ mid`, so `vanishing₂` merges the loops.
  ⊗-trace-mid : ∀ {X Y A A' B B' : Obj}
                  {u : A ⊗₀ X ⇒ B ⊗₀ X} {v : A' ⊗₀ Y ⇒ B' ⊗₀ Y} →
                trace u ⊗₁ trace v ≈ trace (mid ∘ u ⊗₁ v ∘ mid)
  ⊗-trace-mid {X} {Y} {A} {A'} {B} {B'} {u} {v} =
    ⊗-trace
    ○ trace-resp-≈ (trace-resp-≈ (TCoh.Transport.WithGens.TM Cˢ A A' B B' X Y u v))
    ○ vanishing₂

  -- Re-bracketing the loop object along `mid`: slide, then `mid`'s involution.
  trace-mid : ∀ {A B P Q R S : Obj}
                {f : A ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S)) ⇒ B ⊗₀ ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))} →
              trace f ≈ trace (id ⊗₁ mid {P} {R} {Q} {S} ∘ f ∘ id ⊗₁ mid {P} {Q} {R} {S})
  trace-mid = ⟺ (TE.trace-slide Traced L ○ trace-resp-≈ (cancelʳ
    (⟺ ⊗-distrib-over-∘ ○ (identityˡ ⟩⊗⟨ mid-involutive) ○ ⊗.identity)))

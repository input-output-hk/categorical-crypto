{-# OPTIONS --safe --without-K #-}
module Categories.GConstruction where

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Traced

open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Categories.Category.Monoidal.Braided.Properties

import Categories.Category.Monoidal.Utilities as U

import Categories.GConstructionCoherence as GCoh
import Categories.GConstructionIdentityCoherence as GCohId

module _ {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    module C where
      open Category C public
      open Traced Traced public
      open U Monoidal public using (module Shorthands)
      open import Categories.Category.Monoidal.Reasoning Monoidal public
        using (serialize₁₂; serialize₂₁; _⟩⊗⟨_; refl⟩⊗⟨_)
      open import Categories.Morphism.Reasoning C public
        using (introˡ; pullʳ; pullˡ; pushˡ; elimˡ; elimʳ; cancelˡ)
      open Shorthands public
      module BP = Categories.Category.Monoidal.Braided.Properties braided
      open BP.Shorthands public

    -- the bundle the transported coherence lemmas are instantiated at
    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

  -- Trace properties needed for the G-construction, taken as HYPOTHESES — the
  -- `module _` below makes all four parameters the caller discharges:
  --   trace-resp-≈ : congruence (trace is a setoid morphism)
  --   trace-∘ˡ / ∘ʳ : left / right naturality      trace-comm : Fubini
  -- They are not derivable here.  agda-categories' `Traced` declares `trace` as
  -- a bare field with only `vanishing₁/₂`, `superposing` and `yanking` — no
  -- congruence and no naturality — although its own header cites a *natural*
  -- family.  So the standard (Joyal-Street-Verity) laws it omits are assumed.
  -- β swaps the last two factors: (A ⊗ Y) ⊗ X → (A ⊗ X) ⊗ Y
  private
    β : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (P C.⊗₀ R) C.⊗₀ Q
    β = C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

  module _ (trace-resp-≈ : ∀ {X A B} {f g : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                           f C.≈ g → C.trace f C.≈ C.trace g)
           (trace-∘ˡ : ∀ {X A B B'} {g : B C.⇒ B'} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                       g C.∘ C.trace f C.≈ C.trace (g C.⊗₁ C.id C.∘ f))
           (trace-∘ʳ : ∀ {X A A' B} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} {h : A' C.⇒ A} →
                       C.trace f C.∘ h C.≈ C.trace (f C.∘ h C.⊗₁ C.id))
           -- Fubini: exchange the order of two nested traces (via β)
           (trace-comm : ∀ {X Y A B} {f : (A C.⊗₀ X) C.⊗₀ Y C.⇒ (B C.⊗₀ X) C.⊗₀ Y} →
                         C.trace (C.trace f) C.≈ C.trace (C.trace (β C.∘ f C.∘ β)))
           where

    GConstruction : Category a b c
    GConstruction = categoryHelper record
      { Obj = C.Obj × C.Obj
      ; _⇒_ = λ where (A⁺ , A⁻) (B⁺ , B⁻) → A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺
      ; _≈_ = C._≈_
      ; id = C.σ⇒
      ; _∘_ = λ f g → C.trace (α C.∘ f C.⊗₁ g C.∘ γ)
      ; assoc = assoc'
      ; identityˡ = identityˡ'
      ; identityʳ = identityʳ'
      ; equiv = C.equiv
      ; ∘-resp-≈ = λ p q → trace-resp-≈ (refl⟩∘⟨ ((p C.⟩⊗⟨ q) ⟩∘⟨refl))
      }
      where
        open C.HomReasoning

        -- Coherence isomorphisms for the G-construction composition
        α : ∀ {A⁻ B⁺ B⁻ C⁺ : C.Obj} →
            (B⁻ C.⊗₀ C⁺) C.⊗₀ (A⁻ C.⊗₀ B⁺) C.⇒ (A⁻ C.⊗₀ C⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
        α = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id) C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒

        γ : ∀ {A⁺ B⁺ B⁻ C⁻ : C.Obj} →
            (A⁺ C.⊗₀ C⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) C.⇒ (B⁺ C.⊗₀ C⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)
        γ = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id)
          C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒ C.∘ C.id C.⊗₁ C.σ⇒

        -- Identity laws.
        -- Strategy: split the two-wire loop with vanishing₂, rewrite each
        -- one-wire loop body into a framed yanking canonical form (the SMC
        -- coherence steps are solver lemmas in GConstructionIdentityCoherence),
        -- then collapse with trace-∘ˡ/∘ʳ + superposing + yanking.

        -- trace of the yanking core: β at Q = R = X swaps the loop wire with
        -- a parallel copy of itself, so its trace is the identity.
        trace-βyank : ∀ {Y X : C.Obj} → C.trace (β {Y} {X} {X}) C.≈ C.id
        trace-βyank =
          C.superposing ○ (C.refl⟩⊗⟨ C.yanking) ○ C.⊗.identity

        -- framed yanking: a loop whose body is a yanking core followed by
        -- loop-independent processing g collapses to g.
        trace-gyank : ∀ {Y X B' : C.Obj} {g : Y C.⊗₀ X C.⇒ B'} →
                      C.trace (g C.⊗₁ C.id C.∘ β {Y} {X} {X}) C.≈ g
        trace-gyank = ⟺ trace-∘ˡ ○ C.elimʳ trace-βyank

        -- identityˡ: id ∘G f ≈ f, i.e. trace(α ∘ σ⇒ ⊗₁ f ∘ γ) ≈ f
        identityˡ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.≈ f
        identityˡ' {A} {B} {f} =
          ⟺ (C.vanishing₂ {X = proj₂ B} {Y = proj₁ B})
          ○ trace-resp-≈ (trace-resp-≈ ICW.C1L ○ ⟺ trace-∘ʳ
                          ○ (trace-gyank ⟩∘⟨refl) ○ ICW.C3L)
          ○ trace-gyank
          where
            module ICW = GCohId.Transport.WithGen Cˢ
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

        -- identityʳ: f ∘G id ≈ f, i.e. trace(α ∘ f ⊗₁ σ⇒ ∘ γ) ≈ f
        identityʳ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.≈ f
        identityʳ' {A} {B} {f} =
          ⟺ (C.vanishing₂ {X = proj₂ A} {Y = proj₁ A})
          ○ trace-resp-≈ (trace-resp-≈ ICW.C1R ○ ⟺ trace-∘ˡ
                          ○ (refl⟩∘⟨ (⟺ trace-∘ʳ ○ C.elimˡ trace-βyank))
                          ○ ICW.C3R)
          ○ ⟺ trace-∘ʳ ○ (trace-gyank ⟩∘⟨refl)
          ○ C.cancelˡ C.commutative
          where
            module ICW = GCohId.Transport.WithGen Cˢ
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

        -- Right superposing: trace(f) ⊗₁ id ≈ trace(β ∘ f ⊗₁ id ∘ β)
        right-superposing : ∀ {X Y A' B'} {f' : A' C.⊗₀ X C.⇒ B' C.⊗₀ X} →
          C.trace f' C.⊗₁ C.id {Y} C.≈ C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
        right-superposing {X} {Y} {A'} {B'} {f'} = begin
          C.trace f' C.⊗₁ C.id
            -- braiding: a ⊗₁ b ≈ σ⇒ ∘ (b ⊗₁ a) ∘ σ⇒ (from braiding naturality)
            ≈⟨ braiding-swap ⟩
          C.σ⇒ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
            -- superposing⁻¹: id ⊗₁ trace(f') → trace(α⇐ ∘ id ⊗₁ f' ∘ α⇒)
            ≈⟨ refl⟩∘⟨ C.Equiv.sym C.superposing ⟩∘⟨refl ⟩
          C.σ⇒ C.∘ C.trace (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒
            -- right naturality: trace(X) ∘ σ⇒ → trace(X ∘ (σ⇒ ⊗₁ id))
            ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
          C.σ⇒ C.∘ C.trace ((C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
            -- left naturality: σ⇒ ∘ trace(X) → trace((σ⇒ ⊗₁ id) ∘ X)
            ≈⟨ trace-∘ˡ ⟩
          C.trace (C.σ⇒ C.⊗₁ C.id C.∘ (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
            -- coherence: the transported free-level solver result
            ≈⟨ trace-resp-≈ coherence ⟩
          C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
          ∎
          where -- introduce σ⇒ ∘ σ⇒ ≈ id on the left, then braiding naturality
                braiding-swap : C.trace f' C.⊗₁ C.id C.≈
                  C.σ⇒ {Y} {B'} C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
                braiding-swap = C.introˡ C.commutative
                              ○ C.pullʳ (C.braiding.⇒.commute _)

                coherence = GCohId.Transport.WithGen.RS Cˢ A' B' X X Y f'

        -- Associativity
        assoc' : ∀ {A B D E : C.Obj × C.Obj}
                   {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B}
                   {g : proj₁ B C.⊗₀ proj₂ D C.⇒ proj₂ B C.⊗₀ proj₁ D}
                   {h : proj₁ D C.⊗₀ proj₂ E C.⇒ proj₂ D C.⊗₀ proj₁ E} →
                   C.trace (α C.∘ C.trace (α C.∘ h C.⊗₁ g C.∘ γ) C.⊗₁ f C.∘ γ) C.≈
                   C.trace (α C.∘ h C.⊗₁ C.trace (α C.∘ g C.⊗₁ f C.∘ γ) C.∘ γ)
        assoc' {_ , _} {B⁺ , B⁻} {D⁺ , D⁻} {E⁺ , E⁻} {f} {g} {h} = begin
          -- LHS: trace_B(α ∘ trace_D(m) ⊗₁ f ∘ γ)
          C.trace (α C.∘ C.trace m C.⊗₁ f C.∘ γ)
            -- 1-2. serialize + reassociate: trace(m) ⊗₁ f ∘ γ
            --      → (trace(m) ⊗₁ id) ∘ ((id ⊗₁ f) ∘ γ)
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.pushˡ C.serialize₁₂) ⟩
          C.trace (α C.∘ C.trace m C.⊗₁ C.id C.∘ C.id C.⊗₁ f C.∘ γ)
            -- 3. right-superposing: trace_D(m) ⊗₁ id → trace_D(β ∘ m ⊗₁ id ∘ β)
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ right-superposing ⟩∘⟨refl) ⟩
          C.trace (α C.∘ C.trace m' C.∘ C.id C.⊗₁ f C.∘ γ)
            -- 4. right naturality: push (id ⊗₁ f ∘ γ) into trace_D
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ trace-∘ʳ) ⟩
          C.trace (α C.∘ C.trace (m' C.∘ (C.id C.⊗₁ f C.∘ γ) C.⊗₁ C.id))
            -- 5. left naturality: push α into trace_D
            ≈⟨ trace-resp-≈ trace-∘ˡ ⟩
          C.trace (C.trace (α C.⊗₁ C.id C.∘ m' C.∘ (C.id C.⊗₁ f C.∘ γ) C.⊗₁ C.id))
            -- 6a. exchange trace order via Fubini: trace_B(trace_D(f)) ≈ trace_D(trace_B(β∘f∘β))
            ≈⟨ trace-comm ⟩
          C.trace (C.trace (β C.∘ (α C.⊗₁ C.id C.∘ m' C.∘ (C.id C.⊗₁ f C.∘ γ) C.⊗₁ C.id) C.∘ β))
            -- 6b. coherence: β ∘ Φ_L ∘ β ≈ Φ_R
            --     Both sides apply the same permutation to h ⊗₁ g ⊗₁ f
            --     with the traced variables. Pure monoidal coherence.
            ≈⟨ trace-resp-≈ (trace-resp-≈ (assoc'-coherence f g h)) ⟩
          C.trace (C.trace (α C.⊗₁ C.id C.∘ q C.∘ (h C.⊗₁ C.id C.∘ γ) C.⊗₁ C.id))
            -- 7. left naturality⁻¹: extract α from trace_B
            ≈˘⟨ trace-resp-≈ trace-∘ˡ ⟩
          C.trace (α C.∘ C.trace (q C.∘ (h C.⊗₁ C.id C.∘ γ) C.⊗₁ C.id))
            -- 8. right naturality⁻¹: extract (h ⊗₁ id ∘ γ) from trace_B
            ≈˘⟨ trace-resp-≈ (refl⟩∘⟨ trace-∘ʳ) ⟩
          C.trace (α C.∘ C.trace q C.∘ h C.⊗₁ C.id C.∘ γ)
            -- 9. superposing: trace_B(q) ≈ id ⊗₁ trace_B(k)
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.superposing ⟩∘⟨refl) ⟩
          C.trace (α C.∘ C.id C.⊗₁ C.trace k C.∘ h C.⊗₁ C.id C.∘ γ)
            -- 10-11. reassociate + serialize⁻¹:
            --        (id ⊗₁ trace(k)) ∘ ((h ⊗₁ id) ∘ γ) → (h ⊗₁ trace(k)) ∘ γ
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.pullˡ (⟺ C.serialize₂₁)) ⟩
          C.trace (α C.∘ h C.⊗₁ C.trace k C.∘ γ)
          ∎
          where
            m = α C.∘ h C.⊗₁ g C.∘ γ
            k = α C.∘ g C.⊗₁ f C.∘ γ
            m' = β C.∘ m C.⊗₁ C.id C.∘ β
            q = C.α⇐ C.∘ C.id C.⊗₁ k C.∘ C.α⇒

            -- The main coherence proof
            assoc'-coherence :
              ∀ {A⁺ A⁻' B⁺' B⁻' D⁺' D⁻' E⁺' E⁻'}
              (f' : A⁺ C.⊗₀ B⁻' C.⇒ A⁻' C.⊗₀ B⁺')
              (g' : B⁺' C.⊗₀ D⁻' C.⇒ B⁻' C.⊗₀ D⁺')
              (h' : D⁺' C.⊗₀ E⁻' C.⇒ D⁻' C.⊗₀ E⁺') →
              let m₀ = α C.∘ h' C.⊗₁ g' C.∘ γ
                  k₀ = α C.∘ g' C.⊗₁ f' C.∘ γ
                  m₀' = β C.∘ m₀ C.⊗₁ C.id C.∘ β
                  q₀ = C.α⇐ C.∘ C.id C.⊗₁ k₀ C.∘ C.α⇒
              in β C.∘ (α C.⊗₁ C.id C.∘ m₀' C.∘ (C.id C.⊗₁ f' C.∘ γ) C.⊗₁ C.id) C.∘ β
                 C.≈
                 α C.⊗₁ C.id C.∘ q₀ C.∘ (h' C.⊗₁ C.id C.∘ γ) C.⊗₁ C.id
            -- The main coherence equation: pure monoidal coherence showing that
            -- the two rearrangements of h ⊗₁ g ⊗₁ f (with trace variables)
            -- are equal. Both sides represent the same string diagram.
            -- Discharged by the transported free-level solver result
            -- (GConstructionCoherence.Transport.WithGens.coherence).
            assoc'-coherence {A⁺} {A⁻'} {B⁺'} {B⁻'} {D⁺'} {D⁻'} {E⁺'} {E⁻'} f' g' h' =
              GCoh.Transport.WithGens.coherence Cˢ
                A⁺ A⁻' B⁺' B⁻' D⁺' D⁻' E⁺' E⁻'
                f' g' h'


{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The G construction: the category of states-and-processes over a
-- traced symmetric monoidal category.  The flagship application of the
-- coherence solver — the associativity and identity obligations are
-- solver-discharged in `GConstructionCoherence` and
-- `GConstructionIdentityCoherence`; the loop wiring and the trace
-- algebra live in `GConstructionTrace`, and the monoidal structure in
-- `GConstructionMonoidal`.
------------------------------------------------------------------------

module Categories.GConstruction where

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE

open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Categories.Category.Monoidal.Braided.Properties as BProps

import Categories.Category.Monoidal.Utilities as U

import Categories.GConstructionCoherence as GCoh
import Categories.GConstructionIdentityCoherence as GCohId
import Categories.GConstructionTrace as GT

module _ {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    module C where
      open Category C public
      open Traced Traced public
      open U.Shorthands Monoidal public
      open import Categories.Category.Monoidal.Reasoning Monoidal public
        using (serialize₁₂; serialize₂₁; _⟩⊗⟨_)
      open import Categories.Morphism.Reasoning C public
        using (pullˡ; pushˡ; elimˡ; cancelˡ)
      open BProps.Shorthands braided public

    -- the bundle the transported coherence lemmas are instantiated at
    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

    module W = GT C Monoidal Traced

  open W using (α; β; γ)

  _⇒ᴳ_ : C.Obj × C.Obj → C.Obj × C.Obj → Set b
  (A⁺ , A⁻) ⇒ᴳ (B⁺ , B⁻) = A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺

  opaque
    composeᴳ : ∀ {A B D} → B ⇒ᴳ D → A ⇒ᴳ B → A ⇒ᴳ D
    composeᴳ f g = C.trace (α C.∘ f C.⊗₁ g C.∘ γ)

  opaque
    unfolding composeᴳ

    composeᴳ-raw : ∀ {A B D} {f : B ⇒ᴳ D} {g : A ⇒ᴳ B} →
                   composeᴳ f g C.≈ C.trace (α C.∘ f C.⊗₁ g C.∘ γ)
    composeᴳ-raw = C.Equiv.refl

  -- The trace laws `Traced` omits are a hypothesis: see `Traced.Ext`.
  module _ (L : TE.Laws Traced) where

    open TE.Laws L

    GConstruction : Category a b c
    GConstruction = categoryHelper record
      { Obj = C.Obj × C.Obj
      ; _⇒_ = _⇒ᴳ_
      ; _≈_ = C._≈_
      ; id = C.σ⇒
      ; _∘_ = composeᴳ
      ; assoc = assoc'
      ; identityˡ = identityˡ'
      ; identityʳ = identityʳ'
      ; equiv = C.equiv
      ; ∘-resp-≈ = compose-resp-≈
      }
      where
        open C.HomReasoning
        open W.WithTrace L

        -- Identity laws.
        -- Strategy: split the two-wire loop with vanishing₂, rewrite each
        -- one-wire loop body into a framed yanking canonical form (the SMC
        -- coherence steps are solver lemmas in GConstructionIdentityCoherence),
        -- then collapse with trace-∘ˡ/∘ʳ + superposing + yanking.

        -- identityˡ: id ∘G f ≈ f, i.e. trace(α ∘ σ⇒ ⊗₁ f ∘ γ) ≈ f
        identityˡ-raw : ∀ {A B : C.Obj × C.Obj}
                          {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                        C.trace (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.≈ f
        identityˡ-raw {A} {B} {f} =
          ⟺ (C.vanishing₂ {X = proj₂ B} {Y = proj₁ B})
          ○ trace-resp-≈ (trace-resp-≈ ICW.C1L ○ ⟺ trace-∘ʳ
                          ○ (trace-gyank ⟩∘⟨refl) ○ ICW.C3L)
          ○ trace-gyank
          where
            module ICW = GCohId.Transport.WithGen Cˢ
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

        -- identityʳ: f ∘G id ≈ f, i.e. trace(α ∘ f ⊗₁ σ⇒ ∘ γ) ≈ f
        identityʳ-raw : ∀ {A B : C.Obj × C.Obj}
                          {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                        C.trace (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.≈ f
        identityʳ-raw {A} {B} {f} =
          ⟺ (C.vanishing₂ {X = proj₂ A} {Y = proj₁ A})
          ○ trace-resp-≈ (trace-resp-≈ ICW.C1R ○ ⟺ trace-∘ˡ
                          ○ (refl⟩∘⟨ (⟺ trace-∘ʳ ○ C.elimˡ trace-βyank))
                          ○ ICW.C3R)
          ○ ⟺ trace-∘ʳ ○ (trace-gyank ⟩∘⟨refl)
          ○ C.cancelˡ C.commutative
          where
            module ICW = GCohId.Transport.WithGen Cˢ
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) (proj₁ A) f

        -- Associativity
        assoc-raw : ∀ {A B D E : C.Obj × C.Obj}
                      {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B}
                      {g : proj₁ B C.⊗₀ proj₂ D C.⇒ proj₂ B C.⊗₀ proj₁ D}
                      {h : proj₁ D C.⊗₀ proj₂ E C.⇒ proj₂ D C.⊗₀ proj₁ E} →
                      C.trace (α C.∘ C.trace (α C.∘ h C.⊗₁ g C.∘ γ) C.⊗₁ f C.∘ γ) C.≈
                      C.trace (α C.∘ h C.⊗₁ C.trace (α C.∘ g C.⊗₁ f C.∘ γ) C.∘ γ)
        assoc-raw {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} {E⁺ , E⁻} {f} {g} {h} = begin
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
            ≈⟨ trace-resp-≈ (trace-resp-≈ assoc'-coherence) ⟩
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

            -- The main coherence equation: pure monoidal coherence — both
            -- sides are the same rearrangement of h ⊗₁ g ⊗₁ f with the
            -- traced variables, i.e. the same string diagram.  Discharged
            -- by the transported free-level solver result.  (Stated at the
            -- ONE instantiation it has: the enclosing `where`'s own `m'`
            -- and `q`.)
            assoc'-coherence :
              β C.∘ (α C.⊗₁ C.id C.∘ m' C.∘ (C.id C.⊗₁ f C.∘ γ) C.⊗₁ C.id) C.∘ β
              C.≈ α C.⊗₁ C.id C.∘ q C.∘ (h C.⊗₁ C.id C.∘ γ) C.⊗₁ C.id
            assoc'-coherence =
              GCoh.Transport.WithGens.coherence Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ f g h

        opaque
          unfolding composeᴳ

          compose-resp-≈ : ∀ {A B D} {f h : B ⇒ᴳ D} {g i : A ⇒ᴳ B}
                         → f C.≈ h → g C.≈ i → composeᴳ f g C.≈ composeᴳ h i
          compose-resp-≈ p q = trace-resp-≈ (refl⟩∘⟨ ((p C.⟩⊗⟨ q) ⟩∘⟨refl))

          identityˡ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ C.σ⇒ f C.≈ f
          identityˡ' = identityˡ-raw

          identityʳ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ f C.σ⇒ C.≈ f
          identityʳ' = identityʳ-raw

          assoc' : ∀ {A B D E} {f : A ⇒ᴳ B} {g : B ⇒ᴳ D} {h : D ⇒ᴳ E}
                 → composeᴳ (composeᴳ h g) f C.≈ composeᴳ h (composeᴳ g f)
          assoc' = assoc-raw

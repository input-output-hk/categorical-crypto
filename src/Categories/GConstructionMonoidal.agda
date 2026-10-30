{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The monoidal structure of the G construction: objects tensor
-- polarity-wise with unit `(I,I)`, and `f ⊗₁ᴳ g = mid ∘ f ⊗ g ∘ mid`
-- uses no trace.  Every structural morphism is an embedding
-- `⌜ u , v ⌝`, so `⌜⌝-⊗`, `⌜⌝-∘` and `absorbˡ`/`absorbʳ` reduce each
-- coherence law to a base-level one (`GConstructionTrace.mid-unitˡ/ʳ/-assoc`);
-- only `homomorphismᴳ` meets the trace.
------------------------------------------------------------------------

module Categories.GConstructionMonoidal where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
open import Categories.GConstruction
open import Categories.GConstructionEmbedding

open import Data.Product

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionHomCoherence as HCoh
import Categories.GConstructionTrace as GT

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  open Category C
  open Traced T
  open U M using (triangle-inv; pentagon-inv)
  open U.Shorthands M
  open import Categories.Category.Monoidal.Reasoning M
    using (⊗-distrib-over-∘; _⟩⊗⟨_)
  open import Categories.Morphism.Reasoning C using (pullˡ; pullʳ; cancelʳ)
  open BProps.Shorthands braided

  private
    module E₀ = Embed C M T
    module W = GT C M T

  open HomReasoning
  open E₀
  open W

  _⊗₀ᴳ_ : Obj × Obj → Obj × Obj → Obj × Obj
  (A⁺ , A⁻) ⊗₀ᴳ (B⁺ , B⁻) = A⁺ ⊗₀ B⁺ , A⁻ ⊗₀ B⁻

  unitᴳ : Obj × Obj
  unitᴳ = unit , unit

  opaque
    infixr 10 _⊗₁ᴳ_
    _⊗₁ᴳ_ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj} →
            A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺ → D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺ →
            (A⁺ ⊗₀ D⁺) ⊗₀ (B⁻ ⊗₀ E⁻) ⇒ (A⁻ ⊗₀ D⁻) ⊗₀ (B⁺ ⊗₀ E⁺)
    f ⊗₁ᴳ g = mid ∘ f ⊗₁ g ∘ mid

  opaque
    unfolding _⊗₁ᴳ_

    ⊗₁ᴳ-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj}
                   {f f' : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                   {g g' : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} →
                 f ≈ f' → g ≈ g' → f ⊗₁ᴳ g ≈ f' ⊗₁ᴳ g'
    ⊗₁ᴳ-resp-≈ e₁ e₂ = refl⟩∘⟨ ((e₁ ⟩⊗⟨ e₂) ⟩∘⟨refl)

    ⌜⌝-⊗ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj}
             {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} →
           ⌜ u , v ⌝ ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ u ⊗₁ p , v ⊗₁ q ⌝
    ⌜⌝-⊗ = refl⟩∘⟨ (⊗-distrib-over-∘ ⟩∘⟨refl)
         ○ pullˡ (pullˡ mid-σ)
         ○ (pullʳ mid-natural ⟩∘⟨refl)
         ○ assoc
         ○ refl⟩∘⟨ cancelʳ mid-involutive

  module _ (L : TE.Laws T) where

    open TE.Laws L

    private
      G' : Category a b c
      G' = GConstruction C M T L
      module G = Category G'

    open E₀.WithTrace L
    open W.WithTrace L

    ⌜⌝-⊗ˡ : ∀ {A⁺ A⁻ D⁺ D⁻ E⁺ E⁻ : Obj} {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} →
            G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ id ⊗₁ p , id ⊗₁ q ⌝
    ⌜⌝-⊗ˡ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) Equiv.refl ○ ⌜⌝-⊗

    ⌜⌝-⊗ʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} →
            ⌜ u , v ⌝ ⊗₁ᴳ G.id {D⁺ , D⁻} ≈ ⌜ u ⊗₁ id , v ⊗₁ id ⌝
    ⌜⌝-⊗ʳ = ⊗₁ᴳ-resp-≈ Equiv.refl (⟺ ⌜⌝-id) ○ ⌜⌝-⊗

    identityᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} → G.id {A⁺ , A⁻} ⊗₁ᴳ G.id {B⁺ , B⁻} ≈ G.id
    identityᴳ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) (⟺ ⌜⌝-id)
              ○ ⌜⌝-⊗
              ○ ⌜⌝-resp-≈ ⊗.identity ⊗.identity
              ○ ⌜⌝-id

    opaque
      unfolding _⊗₁ᴳ_

      homomorphismᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : Obj}
                        {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                        {f′ : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺}
                        {g : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺}
                        {g′ : Q⁺ ⊗₀ R⁻ ⇒ Q⁻ ⊗₀ R⁺} →
                      G._∘_ {A⁺ , A⁻} {B⁺ , B⁻} f′ f
                        ⊗₁ᴳ G._∘_ {P⁺ , P⁻} g′ g
                        ≈ G._∘_ {A⁺ ⊗₀ P⁺ , A⁻ ⊗₀ P⁻}
                                  {B⁺ ⊗₀ Q⁺ , B⁻ ⊗₀ Q⁻}

                                  (f′ ⊗₁ᴳ g′) (f ⊗₁ᴳ g)
      homomorphismᴳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {P⁺} {P⁻} {Q⁺} {Q⁻} {R⁺} {R⁻}
                    {f} {f′} {g} {g′} =
        ⊗₁ᴳ-resp-≈ (composeᴳ-raw C M T) (composeᴳ-raw C M T) ○ (begin
        mid ∘ (trace Φ₁ ⊗₁ trace Φ₂) ∘ mid
          ≈⟨ refl⟩∘⟨ (⊗-trace-mid ⟩∘⟨refl) ⟩
        mid ∘ trace (mid ∘ Φ₁ ⊗₁ Φ₂ ∘ mid) ∘ mid
          ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
        mid ∘ trace ((mid ∘ Φ₁ ⊗₁ Φ₂ ∘ mid) ∘ mid ⊗₁ id)
          ≈⟨ trace-∘ˡ ⟩
        trace (mid ⊗₁ id ∘ (mid ∘ Φ₁ ⊗₁ Φ₂ ∘ mid) ∘ mid ⊗₁ id)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ ((refl⟩∘⟨ (⊗-expand ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        trace (mid ⊗₁ id
                 ∘ (mid ∘ (α ⊗₁ α ∘ BoxL ∘ γ ⊗₁ γ) ∘ mid) ∘ mid ⊗₁ id)
          ≈⟨ trace-resp-≈ residue ⟩
        trace (id ⊗₁ mid
                 ∘ (α ∘ (mid ⊗₁ mid ∘ BoxR ∘ mid ⊗₁ mid) ∘ γ) ∘ id ⊗₁ mid)
          ≈˘⟨ trace-resp-≈ (refl⟩∘⟨ ((refl⟩∘⟨ (⊗-expand ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        trace (id ⊗₁ mid ∘ Ψ ∘ id ⊗₁ mid)
          ≈˘⟨ trace-mid ⟩
        trace Ψ ∎) ○ ⟺ (composeᴳ-raw C M T)
        where
          Φ₁ : (A⁺ ⊗₀ D⁻) ⊗₀ (B⁻ ⊗₀ B⁺) ⇒ (A⁻ ⊗₀ D⁺) ⊗₀ (B⁻ ⊗₀ B⁺)
          Φ₁ = α ∘ f′ ⊗₁ f ∘ γ

          Φ₂ : (P⁺ ⊗₀ R⁻) ⊗₀ (Q⁻ ⊗₀ Q⁺) ⇒ (P⁻ ⊗₀ R⁺) ⊗₀ (Q⁻ ⊗₀ Q⁺)
          Φ₂ = α ∘ g′ ⊗₁ g ∘ γ

          Ψ : ((A⁺ ⊗₀ P⁺) ⊗₀ (D⁻ ⊗₀ R⁻))
                ⊗₀ ((B⁻ ⊗₀ Q⁻) ⊗₀ (B⁺ ⊗₀ Q⁺)) ⇒
              ((A⁻ ⊗₀ P⁻) ⊗₀ (D⁺ ⊗₀ R⁺))
                ⊗₀ ((B⁻ ⊗₀ Q⁻) ⊗₀ (B⁺ ⊗₀ Q⁺))
          Ψ = α ∘ (f′ ⊗₁ᴳ g′) ⊗₁ (f ⊗₁ᴳ g) ∘ γ

          BoxL : (((B⁺ ⊗₀ D⁻) ⊗₀ (A⁺ ⊗₀ B⁻)) ⊗₀
                    ((Q⁺ ⊗₀ R⁻) ⊗₀ (P⁺ ⊗₀ Q⁻))) ⇒
                 (((B⁻ ⊗₀ D⁺) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀
                    ((Q⁻ ⊗₀ R⁺) ⊗₀ (P⁻ ⊗₀ Q⁺)))
          BoxL = (f′ ⊗₁ f) ⊗₁ (g′ ⊗₁ g)

          BoxR : (((B⁺ ⊗₀ D⁻) ⊗₀ (Q⁺ ⊗₀ R⁻)) ⊗₀
                    ((A⁺ ⊗₀ B⁻) ⊗₀ (P⁺ ⊗₀ Q⁻))) ⇒
                 (((B⁻ ⊗₀ D⁺) ⊗₀ (Q⁻ ⊗₀ R⁺)) ⊗₀
                    ((A⁻ ⊗₀ B⁺) ⊗₀ (P⁻ ⊗₀ Q⁺)))
          BoxR = (f′ ⊗₁ g′) ⊗₁ (f ⊗₁ g)

          ⊗-expand : ∀ {V₀ V V′ V″ U₀ U U′ U″ : Obj}
                       {u₂ : V′ ⇒ V″} {u₁ : V ⇒ V′} {u₀ : V₀ ⇒ V}
                       {v₂ : U′ ⇒ U″} {v₁ : U ⇒ U′} {v₀ : U₀ ⇒ U} →
                     (u₂ ∘ u₁ ∘ u₀) ⊗₁ (v₂ ∘ v₁ ∘ v₀)
                       ≈ u₂ ⊗₁ v₂ ∘ u₁ ⊗₁ v₁ ∘ u₀ ⊗₁ v₀
          ⊗-expand = ⊗-distrib-over-∘ ○ (refl⟩∘⟨ ⊗-distrib-over-∘)

          residue : mid ⊗₁ id
                      ∘ (mid ∘ (α ⊗₁ α ∘ BoxL ∘ γ ⊗₁ γ) ∘ mid)
                      ∘ mid ⊗₁ id
                    ≈ id ⊗₁ mid
                      ∘ (α ∘ (mid ⊗₁ mid ∘ BoxR ∘ mid ⊗₁ mid) ∘ γ)
                      ∘ id ⊗₁ mid
          residue = HCoh.Transport.WithGens.HOM Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻
                      f f′ g g′

    opaque
      unfolding _⊗₁ᴳ_ composeᴳ

      triangleᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} →
                  G._∘_ (G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ λ⇒ , λ⇐ ⌝) ⌜ α⇒ , α⇐ ⌝
                    ≈ ⌜ ρ⇒ , ρ⇐ ⌝ ⊗₁ᴳ G.id {B⁺ , B⁻}
      triangleᴳ = G.∘-resp-≈ˡ ⌜⌝-⊗ˡ ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ triangle triangle-inv ○ ⟺ ⌜⌝-⊗ʳ

      pentagonᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : Obj} →
                  G._∘_ (G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ α⇒ {B⁺} {D⁺} , α⇐ {B⁻} {D⁻} ⌝)
                        (G._∘_ ⌜ α⇒ , α⇐ ⌝
                               (⌜ α⇒ , α⇐ ⌝ ⊗₁ᴳ G.id {E⁺ , E⁻}))
                    ≈ G._∘_ ⌜ α⇒ {A⁺} , α⇐ ⌝
                              ⌜ α⇒ , α⇐ ⌝
      pentagonᴳ = G.∘-resp-≈ ⌜⌝-⊗ˡ (G.∘-resp-≈ʳ ⌜⌝-⊗ʳ ○ ⌜⌝-∘)
                ○ ⌜⌝-∘
                ○ ⌜⌝-resp-≈ pentagon pentagon-inv
                ○ ⟺ ⌜⌝-∘

      unitorˡ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj}
                           {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                         G._∘_ ⌜ λ⇒ , λ⇐ ⌝ (G.id ⊗₁ᴳ f)
                           ≈ G._∘_ f ⌜ λ⇒ , λ⇐ ⌝
      unitorˡ-commuteᴳ = absorbˡ ○ mid-unitˡ ○ ⟺ absorbʳ

      unitorʳ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj}
                           {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                         G._∘_ ⌜ ρ⇒ , ρ⇐ ⌝ (f ⊗₁ᴳ G.id)
                           ≈ G._∘_ f ⌜ ρ⇒ , ρ⇐ ⌝
      unitorʳ-commuteᴳ = absorbˡ ○ mid-unitʳ ○ ⟺ absorbʳ

      assoc-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : Obj}
                         {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺}
                         {g : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺}
                         {h : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} →
                       G._∘_ ⌜ α⇒ , α⇐ ⌝ ((f ⊗₁ᴳ g) ⊗₁ᴳ h)
                         ≈ G._∘_ (f ⊗₁ᴳ (g ⊗₁ᴳ h)) ⌜ α⇒ , α⇐ ⌝
      assoc-commuteᴳ = absorbˡ ○ mid-assoc ○ ⟺ absorbʳ

    GConstructionMonoidal : Monoidal G'
    GConstructionMonoidal = monoidalHelper G' record
      { ⊗ = record
        { F₀ = λ (X , Y) → X ⊗₀ᴳ Y
        ; F₁ = λ (u , v) → u ⊗₁ᴳ v
        ; identity = identityᴳ
        ; homomorphism = homomorphismᴳ
        ; F-resp-≈ = λ (p , q) → ⊗₁ᴳ-resp-≈ p q
        }
      ; unit = unitᴳ
      ; unitorˡ = unitorˡᴳ
      ; unitorʳ = unitorʳᴳ
      ; associator = associatorᴳ
      ; unitorˡ-commute = unitorˡ-commuteᴳ
      ; unitorʳ-commute = unitorʳ-commuteᴳ
      ; assoc-commute = assoc-commuteᴳ
      ; triangle = triangleᴳ
      ; pentagon = pentagonᴳ
      }

    -- The bundle, and the entry point an instance should use.  Asking instead
    -- for `Monoidal <the category spelled a second time>` makes Agda compare
    -- two `GConstruction` record values field by field, and those fields are
    -- solver witnesses — measured at the machine layer: >8 GB.  Projected from
    -- ONE application, every field is syntactically shared.
    GConstructionMonoidalCategory : MonoidalCategory a b c
    GConstructionMonoidalCategory = record { U = G' ; monoidal = GConstructionMonoidal }

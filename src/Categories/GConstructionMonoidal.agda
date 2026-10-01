{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The monoidal structure of the G construction: objects tensor
-- polarity-wise with unit `(I,I)`, and `f ⊗₁ᴳ g = mid ∘ f ⊗ g ∘ mid`
-- uses no trace.  Every structural morphism is an embedding
-- `⌜ u , v ⌝`, so `⌜⌝-⊗`, `⌜⌝-∘` and `absorbˡ`/`absorbʳ` reduce each
-- coherence law to a base-level one (`GConstructionTrace.mid-unitˡ/ʳ/-assoc`);
-- only `homomorphismᴳ` meets the trace (see there).
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
import Categories.GConstructionLoop as GL
import Categories.GConstructionTrace as GT

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  private
    module C where
      open Category C public
      open Traced T public
      open U M public using (triangle-inv; pentagon-inv)
      open U.Shorthands M public
      open import Categories.Category.Monoidal.Reasoning M public
        using (⊗-distrib-over-∘; _⟩⊗⟨_)
      open import Categories.Morphism.Reasoning C public using (pullˡ; pullʳ; cancelʳ)
      open BProps.Shorthands braided public

    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = M ; symmetric = C.symmetric }

    module E₀ = Embed C M T
    module W = GT C M T

  open C.HomReasoning
  open E₀
  open W

  _⊗₀ᴳ_ : C.Obj × C.Obj → C.Obj × C.Obj → C.Obj × C.Obj
  (A⁺ , A⁻) ⊗₀ᴳ (B⁺ , B⁻) = A⁺ C.⊗₀ B⁺ , A⁻ C.⊗₀ B⁻

  unitᴳ : C.Obj × C.Obj
  unitᴳ = C.unit , C.unit

  opaque
    infixr 10 _⊗₁ᴳ_
    _⊗₁ᴳ_ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj} →
            A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺ → D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺ →
            (A⁺ C.⊗₀ D⁺) C.⊗₀ (B⁻ C.⊗₀ E⁻) C.⇒ (A⁻ C.⊗₀ D⁻) C.⊗₀ (B⁺ C.⊗₀ E⁺)
    f ⊗₁ᴳ g = mid C.∘ f C.⊗₁ g C.∘ mid

  opaque
    unfolding _⊗₁ᴳ_

    ⊗₁ᴳ-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj}
                   {f f' : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺}
                   {g g' : D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺} →
                 f C.≈ f' → g C.≈ g' → f ⊗₁ᴳ g C.≈ f' ⊗₁ᴳ g'
    ⊗₁ᴳ-resp-≈ e₁ e₂ = refl⟩∘⟨ ((e₁ C.⟩⊗⟨ e₂) ⟩∘⟨refl)

    ⌜⌝-⊗ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj}
             {u : A⁺ C.⇒ B⁺} {v : B⁻ C.⇒ A⁻} {p : D⁺ C.⇒ E⁺} {q : E⁻ C.⇒ D⁻} →
           ⌜ u , v ⌝ ⊗₁ᴳ ⌜ p , q ⌝ C.≈ ⌜ u C.⊗₁ p , v C.⊗₁ q ⌝
    ⌜⌝-⊗ = refl⟩∘⟨ (C.⊗-distrib-over-∘ ⟩∘⟨refl)
         ○ C.pullˡ (C.pullˡ mid-σ)
         ○ (C.pullʳ mid-natural ⟩∘⟨refl)
         ○ C.assoc
         ○ refl⟩∘⟨ C.cancelʳ mid-involutive

  module _ (L : TE.Laws T) where

    open TE.Laws L

    private
      G' : Category a b c
      G' = GConstruction C M T L
      module G = Category G'

    open E₀.WithTrace L
    open GL.WithTrace C M T L
    open W.WithTrace L

    ⌜⌝-⊗ˡ : ∀ {A⁺ A⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj} {p : D⁺ C.⇒ E⁺} {q : E⁻ C.⇒ D⁻} →
            G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ p , q ⌝ C.≈ ⌜ C.id C.⊗₁ p , C.id C.⊗₁ q ⌝
    ⌜⌝-⊗ˡ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) C.Equiv.refl ○ ⌜⌝-⊗

    ⌜⌝-⊗ʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} {u : A⁺ C.⇒ B⁺} {v : B⁻ C.⇒ A⁻} →
            ⌜ u , v ⌝ ⊗₁ᴳ G.id {D⁺ , D⁻} C.≈ ⌜ u C.⊗₁ C.id , v C.⊗₁ C.id ⌝
    ⌜⌝-⊗ʳ = ⊗₁ᴳ-resp-≈ C.Equiv.refl (⟺ ⌜⌝-id) ○ ⌜⌝-⊗

    identityᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → G.id {A⁺ , A⁻} ⊗₁ᴳ G.id {B⁺ , B⁻} C.≈ G.id
    identityᴳ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) (⟺ ⌜⌝-id)
              ○ ⌜⌝-⊗
              ○ ⌜⌝-resp-≈ C.⊗.identity C.⊗.identity
              ○ ⌜⌝-id

    -- The two composites' loops `B⁻⊗B⁺` and `Q⁻⊗Q⁺` fuse into their tensor
    -- (`⊗-trace-mid`), and the tensor's own loop `(B⁻⊗Q⁻)⊗(B⁺⊗Q⁺)`
    -- re-brackets to it (`trace-mid`); what remains is the loop-body
    -- coherence `GConstructionHomCoherence.HOM`.
    opaque
      unfolding _⊗₁ᴳ_

      homomorphismᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : C.Obj}
                        {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺}
                        {f′ : B⁺ C.⊗₀ D⁻ C.⇒ B⁻ C.⊗₀ D⁺}
                        {g : P⁺ C.⊗₀ Q⁻ C.⇒ P⁻ C.⊗₀ Q⁺}
                        {g′ : Q⁺ C.⊗₀ R⁻ C.⇒ Q⁻ C.⊗₀ R⁺} →
                      G._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} f′ f
                        ⊗₁ᴳ G._∘_ {P⁺ , P⁻} {Q⁺ , Q⁻} {R⁺ , R⁻} g′ g
                        C.≈ G._∘_ {A⁺ C.⊗₀ P⁺ , A⁻ C.⊗₀ P⁻}
                                  {B⁺ C.⊗₀ Q⁺ , B⁻ C.⊗₀ Q⁻}
                                  {D⁺ C.⊗₀ R⁺ , D⁻ C.⊗₀ R⁻}
                                  (f′ ⊗₁ᴳ g′) (f ⊗₁ᴳ g)
      homomorphismᴳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {P⁺} {P⁻} {Q⁺} {Q⁻} {R⁺} {R⁻}
                    {f} {f′} {g} {g′} =
        ⊗₁ᴳ-resp-≈ (composeᴳ-raw C M T) (composeᴳ-raw C M T) ○ (begin
        mid C.∘ (C.trace Φ₁ C.⊗₁ C.trace Φ₂) C.∘ mid
          ≈⟨ refl⟩∘⟨ (⊗-trace-mid ⟩∘⟨refl) ⟩
        mid C.∘ C.trace (mid C.∘ Φ₁ C.⊗₁ Φ₂ C.∘ mid) C.∘ mid
          ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
        mid C.∘ C.trace ((mid C.∘ Φ₁ C.⊗₁ Φ₂ C.∘ mid) C.∘ mid C.⊗₁ C.id)
          ≈⟨ trace-∘ˡ ⟩
        C.trace (mid C.⊗₁ C.id C.∘ (mid C.∘ Φ₁ C.⊗₁ Φ₂ C.∘ mid) C.∘ mid C.⊗₁ C.id)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ ((refl⟩∘⟨ (⊗-expand ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        C.trace (mid C.⊗₁ C.id
                 C.∘ (mid C.∘ (α C.⊗₁ α C.∘ BoxL C.∘ γ C.⊗₁ γ) C.∘ mid) C.∘ mid C.⊗₁ C.id)
          ≈⟨ trace-resp-≈ residue ⟩
        C.trace (C.id C.⊗₁ mid
                 C.∘ (α C.∘ (mid C.⊗₁ mid C.∘ BoxR C.∘ mid C.⊗₁ mid) C.∘ γ) C.∘ C.id C.⊗₁ mid)
          ≈˘⟨ trace-resp-≈ (refl⟩∘⟨ ((refl⟩∘⟨ (⊗-expand ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        C.trace (C.id C.⊗₁ mid C.∘ Ψ C.∘ C.id C.⊗₁ mid)
          ≈˘⟨ trace-mid ⟩
        C.trace Ψ ∎) ○ ⟺ (composeᴳ-raw C M T)
        where
          Φ₁ : (A⁺ C.⊗₀ D⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) C.⇒ (A⁻ C.⊗₀ D⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
          Φ₁ = α C.∘ f′ C.⊗₁ f C.∘ γ

          Φ₂ : (P⁺ C.⊗₀ R⁻) C.⊗₀ (Q⁻ C.⊗₀ Q⁺) C.⇒ (P⁻ C.⊗₀ R⁺) C.⊗₀ (Q⁻ C.⊗₀ Q⁺)
          Φ₂ = α C.∘ g′ C.⊗₁ g C.∘ γ

          Ψ : ((A⁺ C.⊗₀ P⁺) C.⊗₀ (D⁻ C.⊗₀ R⁻))
                C.⊗₀ ((B⁻ C.⊗₀ Q⁻) C.⊗₀ (B⁺ C.⊗₀ Q⁺)) C.⇒
              ((A⁻ C.⊗₀ P⁻) C.⊗₀ (D⁺ C.⊗₀ R⁺))
                C.⊗₀ ((B⁻ C.⊗₀ Q⁻) C.⊗₀ (B⁺ C.⊗₀ Q⁺))
          Ψ = α C.∘ (f′ ⊗₁ᴳ g′) C.⊗₁ (f ⊗₁ᴳ g) C.∘ γ

          BoxL : (((B⁺ C.⊗₀ D⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)) C.⊗₀
                    ((Q⁺ C.⊗₀ R⁻) C.⊗₀ (P⁺ C.⊗₀ Q⁻))) C.⇒
                 (((B⁻ C.⊗₀ D⁺) C.⊗₀ (A⁻ C.⊗₀ B⁺)) C.⊗₀
                    ((Q⁻ C.⊗₀ R⁺) C.⊗₀ (P⁻ C.⊗₀ Q⁺)))
          BoxL = (f′ C.⊗₁ f) C.⊗₁ (g′ C.⊗₁ g)

          BoxR : (((B⁺ C.⊗₀ D⁻) C.⊗₀ (Q⁺ C.⊗₀ R⁻)) C.⊗₀
                    ((A⁺ C.⊗₀ B⁻) C.⊗₀ (P⁺ C.⊗₀ Q⁻))) C.⇒
                 (((B⁻ C.⊗₀ D⁺) C.⊗₀ (Q⁻ C.⊗₀ R⁺)) C.⊗₀
                    ((A⁻ C.⊗₀ B⁺) C.⊗₀ (P⁻ C.⊗₀ Q⁺)))
          BoxR = (f′ C.⊗₁ g′) C.⊗₁ (f C.⊗₁ g)

          ⊗-expand : ∀ {V₀ V V′ V″ U₀ U U′ U″ : C.Obj}
                       {u₂ : V′ C.⇒ V″} {u₁ : V C.⇒ V′} {u₀ : V₀ C.⇒ V}
                       {v₂ : U′ C.⇒ U″} {v₁ : U C.⇒ U′} {v₀ : U₀ C.⇒ U} →
                     (u₂ C.∘ u₁ C.∘ u₀) C.⊗₁ (v₂ C.∘ v₁ C.∘ v₀)
                       C.≈ u₂ C.⊗₁ v₂ C.∘ u₁ C.⊗₁ v₁ C.∘ u₀ C.⊗₁ v₀
          ⊗-expand = C.⊗-distrib-over-∘ ○ (refl⟩∘⟨ C.⊗-distrib-over-∘)

          residue : mid C.⊗₁ C.id
                      C.∘ (mid C.∘ (α C.⊗₁ α C.∘ BoxL C.∘ γ C.⊗₁ γ) C.∘ mid)
                      C.∘ mid C.⊗₁ C.id
                    C.≈ C.id C.⊗₁ mid
                      C.∘ (α C.∘ (mid C.⊗₁ mid C.∘ BoxR C.∘ mid C.⊗₁ mid) C.∘ γ)
                      C.∘ C.id C.⊗₁ mid
          residue = HCoh.Transport.WithGens.HOM Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻
                      f f′ g g′

    opaque
      unfolding _⊗₁ᴳ_ composeᴳ

      triangleᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} →
                  G._∘_ (G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ C.λ⇒ , C.λ⇐ ⌝) ⌜ C.α⇒ , C.α⇐ ⌝
                    C.≈ ⌜ C.ρ⇒ , C.ρ⇐ ⌝ ⊗₁ᴳ G.id {B⁺ , B⁻}
      triangleᴳ = G.∘-resp-≈ˡ ⌜⌝-⊗ˡ ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ C.triangle C.triangle-inv ○ ⟺ ⌜⌝-⊗ʳ

      pentagonᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj} →
                  G._∘_ (G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ C.α⇒ {B⁺} {D⁺} {E⁺} , C.α⇐ {B⁻} {D⁻} {E⁻} ⌝)
                        (G._∘_ ⌜ C.α⇒ , C.α⇐ ⌝
                               (⌜ C.α⇒ , C.α⇐ ⌝ ⊗₁ᴳ G.id {E⁺ , E⁻}))
                    C.≈ G._∘_ ⌜ C.α⇒ {A⁺} {B⁺} {D⁺ C.⊗₀ E⁺} , C.α⇐ ⌝
                              ⌜ C.α⇒ {A⁺ C.⊗₀ B⁺} {D⁺} {E⁺} , C.α⇐ ⌝
      pentagonᴳ = G.∘-resp-≈ (⌜⌝-⊗ˡ {p = C.α⇒}) (G.∘-resp-≈ʳ ⌜⌝-⊗ʳ ○ ⌜⌝-∘)
                ○ ⌜⌝-∘
                ○ ⌜⌝-resp-≈ C.pentagon C.pentagon-inv
                ○ ⟺ ⌜⌝-∘

      unitorˡ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj}
                           {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺} →
                         G._∘_ ⌜ C.λ⇒ , C.λ⇐ ⌝ (G.id {unitᴳ} ⊗₁ᴳ f)
                           C.≈ G._∘_ f ⌜ C.λ⇒ , C.λ⇐ ⌝
      unitorˡ-commuteᴳ = absorbˡ ○ mid-unitˡ ○ ⟺ absorbʳ

      unitorʳ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj}
                           {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺} →
                         G._∘_ ⌜ C.ρ⇒ , C.ρ⇐ ⌝ (f ⊗₁ᴳ G.id {unitᴳ})
                           C.≈ G._∘_ f ⌜ C.ρ⇒ , C.ρ⇐ ⌝
      unitorʳ-commuteᴳ = absorbˡ ○ mid-unitʳ ○ ⟺ absorbʳ

      assoc-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : C.Obj}
                         {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺}
                         {g : D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺}
                         {h : P⁺ C.⊗₀ Q⁻ C.⇒ P⁻ C.⊗₀ Q⁺} →
                       G._∘_ ⌜ C.α⇒ , C.α⇐ ⌝ ((f ⊗₁ᴳ g) ⊗₁ᴳ h)
                         C.≈ G._∘_ (f ⊗₁ᴳ (g ⊗₁ᴳ h)) ⌜ C.α⇒ , C.α⇐ ⌝
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

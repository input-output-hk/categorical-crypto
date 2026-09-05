{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The monoidal structure of the G construction.  Objects tensor
-- polarity-wise, `(A⁺,A⁻) ⊗ (B⁺,B⁻) = (A⁺ ⊗ B⁺ , A⁻ ⊗ B⁻)` with unit
-- `(I,I)`, and morphisms tensor by conjugating the base tensor with the
-- middle-four interchange
--
--   mid : (P ⊗ Q) ⊗ (R ⊗ S) ⇒ (P ⊗ R) ⊗ (Q ⊗ S)
--
-- so `f ⊗₁ᴳ g = mid ∘ f ⊗₁ g ∘ mid` uses NO trace.  Every structural
-- morphism is an embedding `⌜ u , v ⌝`, so `⌜⌝-⊗` (embedding is
-- monoidal) plus `⌜⌝-∘` and `absorbˡ`/`absorbʳ` transport each base
-- coherence law; the base-level residues are solved in
-- `Categories.GConstructionTensorCoherence`.
------------------------------------------------------------------------

module Categories.GConstructionMonoidal where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Traced
open import Categories.GConstruction
open import Categories.GConstructionEmbedding

open import Data.Product using (_×_; _,_)

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionTensorCoherence as TCoh

module _ {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    module C where
      open Category C public
      open Traced Traced public
      open U Monoidal public using (triangle-inv; pentagon-inv)
      open U.Shorthands Monoidal public
      open import Categories.Category.Monoidal.Reasoning Monoidal public
        using (_⟩⊗⟨_; refl⟩⊗⟨_)
      open BProps.Shorthands braided public

    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

    β : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (P C.⊗₀ R) C.⊗₀ Q
    β = C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

    module E₀ = Embed C Monoidal Traced

  open C.HomReasoning
  open E₀ using (⌜_,_⌝; ⌜⌝-resp-≈)

  -- The middle-four interchange: an involution, and the only structural
  -- morphism the tensor of G-morphisms needs.
  mid : ∀ {P Q R S : C.Obj} →
        (P C.⊗₀ Q) C.⊗₀ (R C.⊗₀ S) C.⇒ (P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S)
  mid = C.α⇐ C.∘ C.id C.⊗₁ (C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐) C.∘ C.α⇒

  _⊗₀ᴳ_ : C.Obj × C.Obj → C.Obj × C.Obj → C.Obj × C.Obj
  (A⁺ , A⁻) ⊗₀ᴳ (B⁺ , B⁻) = A⁺ C.⊗₀ B⁺ , A⁻ C.⊗₀ B⁻

  unitᴳ : C.Obj × C.Obj
  unitᴳ = C.unit , C.unit

  infixr 10 _⊗₁ᴳ_
  _⊗₁ᴳ_ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj} →
          A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺ → D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺ →
          (A⁺ C.⊗₀ D⁺) C.⊗₀ (B⁻ C.⊗₀ E⁻) C.⇒ (A⁻ C.⊗₀ D⁻) C.⊗₀ (B⁺ C.⊗₀ E⁺)
  f ⊗₁ᴳ g = mid C.∘ f C.⊗₁ g C.∘ mid

  ⊗₁ᴳ-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj}
                 {f f' : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺}
                 {g g' : D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺} →
               f C.≈ f' → g C.≈ g' → f ⊗₁ᴳ g C.≈ f' ⊗₁ᴳ g'
  ⊗₁ᴳ-resp-≈ e₁ e₂ = refl⟩∘⟨ ((e₁ C.⟩⊗⟨ e₂) ⟩∘⟨refl)

  -- Embedding is monoidal, hence so are the identities it produces.
  ⌜⌝-⊗ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj}
           {u : A⁺ C.⇒ B⁺} {v : B⁻ C.⇒ A⁻} {p : D⁺ C.⇒ E⁺} {q : E⁻ C.⇒ D⁻} →
         ⌜ u , v ⌝ ⊗₁ᴳ ⌜ p , q ⌝ C.≈ ⌜ u C.⊗₁ p , v C.⊗₁ q ⌝
  ⌜⌝-⊗ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {E⁺} {E⁻} {u} {v} {p} {q} =
    TCoh.T.Transport.WithGens.TX Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ u v p q

  module _ (trace-resp-≈ : ∀ {X A B} {f g : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                           f C.≈ g → C.trace f C.≈ C.trace g)
           (trace-∘ˡ : ∀ {X A B B'} {g : B C.⇒ B'} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                       g C.∘ C.trace f C.≈ C.trace (g C.⊗₁ C.id C.∘ f))
           (trace-∘ʳ : ∀ {X A A' B} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} {h : A' C.⇒ A} →
                       C.trace f C.∘ h C.≈ C.trace (f C.∘ h C.⊗₁ C.id))
           (trace-comm : ∀ {X Y A B} {f : (A C.⊗₀ X) C.⊗₀ Y C.⇒ (B C.⊗₀ X) C.⊗₀ Y} →
                         C.trace (C.trace f) C.≈ C.trace (C.trace (β C.∘ f C.∘ β)))
           where

    private
      G' : Category a b c
      G' = GConstruction C Monoidal Traced trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm
      module G = Category G'

    open E₀.WithTrace trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm

    -- `⌜⌝-⊗` with one factor the G-identity, which is `⌜ id , id ⌝`.
    ⌜⌝-⊗ˡ : ∀ {A⁺ A⁻ D⁺ D⁻ E⁺ E⁻ : C.Obj} {p : D⁺ C.⇒ E⁺} {q : E⁻ C.⇒ D⁻} →
            G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ p , q ⌝ C.≈ ⌜ C.id C.⊗₁ p , C.id C.⊗₁ q ⌝
    ⌜⌝-⊗ˡ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) C.Equiv.refl ○ ⌜⌝-⊗

    ⌜⌝-⊗ʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} {u : A⁺ C.⇒ B⁺} {v : B⁻ C.⇒ A⁻} →
            ⌜ u , v ⌝ ⊗₁ᴳ G.id {D⁺ , D⁻} C.≈ ⌜ u C.⊗₁ C.id , v C.⊗₁ C.id ⌝
    ⌜⌝-⊗ʳ = ⊗₁ᴳ-resp-≈ C.Equiv.refl (⟺ ⌜⌝-id) ○ ⌜⌝-⊗

    identityᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} →
                G.id {A⁺ , A⁻} ⊗₁ᴳ G.id {B⁺ , B⁻} C.≈ G.id
    identityᴳ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) (⟺ ⌜⌝-id)
              ○ ⌜⌝-⊗
              ○ ⌜⌝-resp-≈ C.⊗.identity C.⊗.identity
              ○ ⌜⌝-id

    triangleᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} →
                G._∘_ (G.id {A⁺ , A⁻} ⊗₁ᴳ ⌜ C.λ⇒ , C.λ⇐ ⌝) ⌜ C.α⇒ , C.α⇐ ⌝
                  C.≈ ⌜ C.ρ⇒ , C.ρ⇐ ⌝ ⊗₁ᴳ G.id {B⁺ , B⁻}
    triangleᴳ = G.∘-resp-≈ˡ ⌜⌝-⊗ˡ
              ○ ⌜⌝-∘
              ○ ⌜⌝-resp-≈ C.triangle C.triangle-inv
              ○ ⟺ ⌜⌝-⊗ʳ

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
    unitorˡ-commuteᴳ {A⁺} {A⁻} {B⁺} {B⁻} {f} =
      absorbˡ ○ TCoh.U.Transport.WithGen.UL Cˢ A⁺ A⁻ B⁺ B⁻ f ○ ⟺ absorbʳ

    unitorʳ-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj}
                         {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺} →
                       G._∘_ ⌜ C.ρ⇒ , C.ρ⇐ ⌝ (f ⊗₁ᴳ G.id {unitᴳ})
                         C.≈ G._∘_ f ⌜ C.ρ⇒ , C.ρ⇐ ⌝
    unitorʳ-commuteᴳ {A⁺} {A⁻} {B⁺} {B⁻} {f} =
      absorbˡ ○ TCoh.U.Transport.WithGen.UR Cˢ A⁺ A⁻ B⁺ B⁻ f ○ ⟺ absorbʳ

    assoc-commuteᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ : C.Obj}
                       {f : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺}
                       {g : D⁺ C.⊗₀ E⁻ C.⇒ D⁻ C.⊗₀ E⁺}
                       {h : P⁺ C.⊗₀ Q⁻ C.⇒ P⁻ C.⊗₀ Q⁺} →
                     G._∘_ ⌜ C.α⇒ , C.α⇐ ⌝ ((f ⊗₁ᴳ g) ⊗₁ᴳ h)
                       C.≈ G._∘_ (f ⊗₁ᴳ (g ⊗₁ᴳ h)) ⌜ C.α⇒ , C.α⇐ ⌝
    assoc-commuteᴳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {E⁺} {E⁻} {P⁺} {P⁻} {Q⁺} {Q⁻}
                   {f} {g} {h} =
      absorbˡ
      ○ TCoh.A.Transport.WithGens.AC Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ f g h
      ○ ⟺ absorbʳ

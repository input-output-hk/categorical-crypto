{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The monoidal structure of the G construction.  Objects tensor
-- polarity-wise, `(A⁺,A⁻) ⊗ (B⁺,B⁻) = (A⁺ ⊗ B⁺ , A⁻ ⊗ B⁻)` with unit
-- `(I,I)`, and morphisms tensor by conjugating the base tensor with the
-- middle-four interchange `mid`, so `f ⊗₁ᴳ g` uses NO trace.
--
-- Every structural morphism is an embedding `⌜ u , v ⌝`, so `⌜⌝-⊗`
-- (embedding is monoidal) with `⌜⌝-∘` and `absorbˡ`/`absorbʳ` transports
-- each base coherence law.  The bifunctor's `homomorphism` is the one
-- law that meets the trace: it compares the two composites' loops with
-- the tensor's single loop, which `⊗-trace-mid` fuses and `trace-mid`
-- re-brackets.  Its base-level residues are solver-discharged, in
-- `GConstructionTensorCoherence` and `GConstructionHomCoherence`.
------------------------------------------------------------------------

module Categories.GConstructionMonoidal where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
open import Categories.GConstruction
import Categories.GConstruction as GC
open import Categories.GConstructionEmbedding

open import Data.Product using (_×_; _,_)

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionHomCoherence as HCoh
import Categories.GConstructionLoop as GL
import Categories.GConstructionTensorCoherence as TCoh
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
      open BProps.Shorthands braided public

    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = M ; symmetric = C.symmetric }

    module E₀ = Embed C M T
    module W = GT C M T

  open C.HomReasoning
  open E₀ using (⌜_,_⌝; ⌜⌝-resp-≈)
  open W using (α; β; γ; mid)

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

    -- Embedding is monoidal.
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
      G' = GConstruction C M T trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm
      module G = Category G'

    open E₀.WithTrace trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm
    open GL.WithTrace C M T trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm
    open W.WithTrace trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm

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

    -- The gate: the two composites' loops `B⁻⊗B⁺` and `Q⁻⊗Q⁺` fuse into
    -- their tensor, and the tensor's own loop `(B⁻⊗Q⁻)⊗(B⁺⊗Q⁺)` re-brackets
    -- to that same tensor — the four wires interleaved the other way.
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
        ⊗₁ᴳ-resp-≈ (GC.composeᴳ-raw C M T) (GC.composeᴳ-raw C M T) ○ (begin
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
        C.trace Ψ ∎) ○ ⟺ (GC.composeᴳ-raw C M T)
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

          -- both sides' box product is `wiring ∘ boxes ∘ wiring`, by
          -- ⊗-∘-distributivity twice
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
      unfolding _⊗₁ᴳ_ GC.composeᴳ

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

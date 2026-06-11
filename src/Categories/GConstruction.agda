{-# OPTIONS --safe --without-K #-}
module Categories.GConstruction where

open import Level renaming (zero to ℓ0)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Properties
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded
open import Categories.Morphism
open import Categories.NaturalTransformation hiding (id)
open import Categories.Category.Monoidal.Traced
open import Categories.Category.Monoidal.Symmetric

open import Categories.Category.Instance.Sets
open import categorical-crypto.Prelude hiding (id; _∘_; _⊗_; lookup; Dec; [_]; ⊤; ⊥; Functor)
import categorical-crypto.Prelude as P
import Categories.Category.Monoidal.Braided.Properties

import Categories.Category.Monoidal.Utilities as U

open import Categories.Tactic.Category
import Categories.Morphism.Reasoning as MR

module _ {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    module C where
      open Category C public
      open Traced Traced public
      open U Monoidal public
      open Shorthands public
      module BP = Categories.Category.Monoidal.Braided.Properties braided
      open BP.Shorthands public

  -- Derived trace properties needed for the G-construction.
  -- These are standard properties of traced monoidal categories:
  --   trace-resp-≈ : congruence (trace is a setoid morphism)
  --   trace-∘ˡ     : left naturality (Hasegawa 1997, Thm 2.3)
  --   trace-∘ʳ     : right naturality
  -- All three are derivable from vanishing + superposing + yanking,
  -- but the derivation is non-trivial for setoid equality.
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
      ; ∘-resp-≈ = λ p q → trace-resp-≈ (C.∘-resp-≈ C.Equiv.refl
                     (C.∘-resp-≈ (Functor.F-resp-≈ C.⊗ (p , q)) C.Equiv.refl))
      }
      where
        open C.HomReasoning
        open MR C using (pullˡ; pullʳ; pushˡ; pushʳ; cancelˡ; cancelʳ; cancelInner; insertˡ; insertʳ)

        -- Coherence isomorphisms for the G-construction composition
        α : ∀ {A⁻ B⁺ B⁻ C⁺ : C.Obj} →
            (B⁻ C.⊗₀ C⁺) C.⊗₀ (A⁻ C.⊗₀ B⁺) C.⇒ (A⁻ C.⊗₀ C⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
        α = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id) C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒

        γ : ∀ {A⁺ B⁺ B⁻ C⁻ : C.Obj} →
            (A⁺ C.⊗₀ C⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) C.⇒ (B⁺ C.⊗₀ C⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)
        γ = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id)
          C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒ C.∘ C.id C.⊗₁ C.σ⇒

        -- ⊗ bifunctoriality helpers
        serialize₁₂ : ∀ {X₁ Y₁ X₂ Y₂ : C.Obj} {f' : X₁ C.⇒ Y₁} {g' : X₂ C.⇒ Y₂} →
                       f' C.⊗₁ g' C.≈ f' C.⊗₁ C.id C.∘ C.id C.⊗₁ g'
        serialize₁₂ = C.Equiv.trans
          (Functor.F-resp-≈ C.⊗ (C.Equiv.sym C.identityʳ , C.Equiv.sym C.identityˡ))
          (Functor.homomorphism C.⊗)

        serialize₂₁ : ∀ {X₁ Y₁ X₂ Y₂ : C.Obj} {f' : X₁ C.⇒ Y₁} {g' : X₂ C.⇒ Y₂} →
                       f' C.⊗₁ g' C.≈ C.id C.⊗₁ g' C.∘ f' C.⊗₁ C.id
        serialize₂₁ = C.Equiv.trans
          (Functor.F-resp-≈ C.⊗ (C.Equiv.sym C.identityˡ , C.Equiv.sym C.identityʳ))
          (Functor.homomorphism C.⊗)

        -- u ⊗₁ id ∘ v ⊗₁ id ≈ (u ∘ v) ⊗₁ id
        ⊗id-merge : ∀ {X₁ Y₁ Z₁ W : C.Obj} {u : Y₁ C.⇒ Z₁} {v : X₁ C.⇒ Y₁} →
                    u C.⊗₁ C.id {W} C.∘ v C.⊗₁ C.id C.≈ (u C.∘ v) C.⊗₁ C.id
        ⊗id-merge = C.Equiv.trans
          (C.Equiv.sym (Functor.homomorphism C.⊗))
          (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.identityˡ))

        -- id ⊗₁ u ∘ id ⊗₁ v ≈ id ⊗₁ (u ∘ v)
        id⊗-merge : ∀ {W X₁ Y₁ Z₁ : C.Obj} {u : Y₁ C.⇒ Z₁} {v : X₁ C.⇒ Y₁} →
                    C.id {W} C.⊗₁ u C.∘ C.id C.⊗₁ v C.≈ C.id C.⊗₁ (u C.∘ v)
        id⊗-merge = C.Equiv.trans
          (C.Equiv.sym (Functor.homomorphism C.⊗))
          (Functor.F-resp-≈ C.⊗ (C.identityˡ , C.Equiv.refl))

        -- Naturality of β: β ∘ (p ⊗₁ q) ⊗₁ r ≈ (p ⊗₁ r) ⊗₁ q ∘ β
        β-natural : ∀ {P P' Q Q' R R' : C.Obj}
          {p : P C.⇒ P'} {q' : Q C.⇒ Q'} {r : R C.⇒ R'} →
          β C.∘ (p C.⊗₁ q') C.⊗₁ r C.≈ (p C.⊗₁ r) C.⊗₁ q' C.∘ β
        β-natural {p = p} {q' = q'} {r = r} = begin
          (C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ (p C.⊗₁ q') C.⊗₁ r
            ≈⟨ C.assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ (p C.⊗₁ q') C.⊗₁ r
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ (p C.⊗₁ q') C.⊗₁ r
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc-commute-from ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ p C.⊗₁ (q' C.⊗₁ r) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ p C.⊗₁ (q' C.⊗₁ r)) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ (begin
                C.id C.⊗₁ C.σ⇒ C.∘ p C.⊗₁ (q' C.⊗₁ r)
                  ≈˘⟨ Functor.homomorphism C.⊗ ⟩
                (C.id C.∘ p) C.⊗₁ (C.σ⇒ C.∘ q' C.⊗₁ r)
                  ≈⟨ Functor.F-resp-≈ C.⊗ (C.identityˡ , C.braiding.⇒.commute (q' , r)) ⟩
                p C.⊗₁ (r C.⊗₁ q' C.∘ C.σ⇒)
                  ≈⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.sym C.identityʳ , C.Equiv.refl) ⟩
                (p C.∘ C.id) C.⊗₁ (r C.⊗₁ q' C.∘ C.σ⇒)
                  ≈⟨ Functor.homomorphism C.⊗ ⟩
                p C.⊗₁ (r C.⊗₁ q') C.∘ C.id C.⊗₁ C.σ⇒
                ∎) ⟩∘⟨refl ⟩
          C.α⇐ C.∘ (p C.⊗₁ (r C.⊗₁ q') C.∘ C.id C.⊗₁ C.σ⇒) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ C.∘ p C.⊗₁ (r C.⊗₁ q') C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ C.∘ p C.⊗₁ (r C.⊗₁ q')) C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
            ≈⟨ C.assoc-commute-to ⟩∘⟨refl ⟩
          ((p C.⊗₁ r) C.⊗₁ q' C.∘ C.α⇐) C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
            ≈⟨ C.assoc ⟩
          (p C.⊗₁ r) C.⊗₁ q' C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
          ∎

        -- β is involutive: β ∘ β ≈ id
        β-involutive : ∀ {P Q R : C.Obj} → β {P} {Q} {R} C.∘ β C.≈ C.id
        β-involutive = begin
          β C.∘ β
            ≈⟨ C.assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ β
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ (C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.α⇐) C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.associator.isoʳ ⟩∘⟨refl ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.id C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.identityˡ ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒) C.∘ C.α⇒
            ≈˘⟨ refl⟩∘⟨ Functor.homomorphism C.⊗ ⟩∘⟨refl ⟩
          C.α⇐ C.∘ (C.id C.∘ C.id) C.⊗₁ (C.σ⇒ C.∘ C.σ⇒) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.identityˡ , C.commutative) ⟩∘⟨refl ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.id C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ (Functor.identity C.⊗ ⟩∘⟨refl) ⟩
          C.α⇐ C.∘ C.id C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
          C.α⇐ C.∘ C.α⇒
            ≈⟨ C.associator.isoˡ ⟩
          C.id
          ∎

        -- The trace of β {M} {X} {X} over its last factor is the identity:
        -- β is literally the superposing shape α⇐ ∘ id ⊗₁ σ ∘ α⇒, and the
        -- trace of σ⇒ {X} {X} yanks to the identity.
        trace-β : ∀ {M X : C.Obj} → C.trace (β {M} {X} {X}) C.≈ C.id
        trace-β {M} {X} = begin
          C.trace (C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)
            ≈⟨ C.superposing ⟩
          C.id {M} C.⊗₁ C.trace (C.σ⇒ {X} {X})
            ≈⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.yanking) ⟩
          C.id {M} C.⊗₁ C.id {X}
            ≈⟨ Functor.identity C.⊗ ⟩
          C.id
          ∎

        -- Right superposing: trace(f) ⊗₁ id ≈ trace(β ∘ f ⊗₁ id ∘ β)
        right-superposing : ∀ {X Y A' B'} {f' : A' C.⊗₀ X C.⇒ B' C.⊗₀ X} →
          C.trace f' C.⊗₁ C.id {Y} C.≈ C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
        right-superposing {f' = f'} = begin
          C.trace f' C.⊗₁ C.id
            -- braiding: a ⊗₁ b ≈ σ⇐ ∘ (b ⊗₁ a) ∘ σ⇒ (from braiding naturality)
            ≈⟨ braiding-swap ⟩
          C.σ⇐ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
            -- superposing⁻¹: id ⊗₁ trace(f') → trace(α⇐ ∘ id ⊗₁ f' ∘ α⇒)
            ≈⟨ refl⟩∘⟨ C.Equiv.sym C.superposing ⟩∘⟨refl ⟩
          C.σ⇐ C.∘ C.trace (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒
            -- right naturality: trace(X) ∘ σ⇒ → trace(X ∘ (σ⇒ ⊗₁ id))
            ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
          C.σ⇐ C.∘ C.trace ((C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
            -- left naturality: σ⇐ ∘ trace(X) → trace((σ⇐ ⊗₁ id) ∘ X)
            ≈⟨ trace-∘ˡ ⟩
          C.trace (C.σ⇐ C.⊗₁ C.id C.∘ (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
            -- coherence: rewrite using assoc-commute, hexagon, braiding
            ≈⟨ trace-resp-≈ (coherence f') ⟩
          C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
          ∎
          where braiding-swap : C.trace f' C.⊗₁ C.id C.≈
                  C.σ⇐ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
                braiding-swap = begin
                  C.trace f' C.⊗₁ C.id
                    ≈˘⟨ C.identityˡ ⟩
                  C.id C.∘ C.trace f' C.⊗₁ C.id
                    ≈˘⟨ C.braiding.iso.isoˡ _ ⟩∘⟨refl ⟩
                  (C.σ⇐ C.∘ C.σ⇒) C.∘ C.trace f' C.⊗₁ C.id
                    ≈⟨ C.assoc ⟩
                  C.σ⇐ C.∘ C.σ⇒ C.∘ C.trace f' C.⊗₁ C.id
                    ≈⟨ refl⟩∘⟨ C.braiding.⇒.commute _ ⟩
                  C.σ⇐ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
                  ∎

                σ-pair-cancel : ∀ {A' Y Z} →
                  C.σ⇒ {Y} {A'} C.⊗₁ C.id {Z} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id C.≈ C.id
                σ-pair-cancel {A'} {Y} {Z} = begin
                  C.σ⇒ {Y} {A'} C.⊗₁ C.id {Z} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈˘⟨ Functor.homomorphism C.⊗ ⟩
                  (C.σ⇒ {Y} {A'} C.∘ C.σ⇒ {A'} {Y}) C.⊗₁ (C.id {Z} C.∘ C.id)
                    ≈⟨ Functor.F-resp-≈ C.⊗ (C.commutative , C.identityˡ) ⟩
                  C.id C.⊗₁ C.id
                    ≈⟨ Functor.identity C.⊗ ⟩
                  C.id
                  ∎

                -- α⇐{A',X,Y} ∘ id⊗σ{Y,X} ∘ α⇒{A',Y,X} ≈ σ⇒{Y,A'⊗X} ∘ α⇒{Y,A',X} ∘ (σ{A',Y}⊗id)
                claim-A' : ∀ {X Y A'} →
                  C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X}
                  C.≈ C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                claim-A' {X} {Y} {A'} = begin
                  C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X}
                    ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.identityʳ) ⟩
                  C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.id)
                    ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ σ-pair-cancel)) ⟩
                  C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ (C.σ⇒ {Y} {A'} C.⊗₁ C.id C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id))
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
                  C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
                  C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id)) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.sym-assoc ⟩
                  (C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.∘-resp-≈ˡ (refl⟩∘⟨ C.hexagon₁ {X = Y} {Y = A'} {Z = X}) ⟩
                  (C.α⇐ C.∘ (C.α⇒ {A'} {X} {Y} C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.∘-resp-≈ˡ C.sym-assoc ⟩
                  ((C.α⇐ C.∘ C.α⇒ {A'} {X} {Y}) C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.∘-resp-≈ˡ (C.∘-resp-≈ˡ (C.associator.isoˡ {X = A'} {Y = X} {Z = Y})) ⟩
                  (C.id C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.∘-resp-≈ˡ C.identityˡ ⟩
                  (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                    ≈⟨ C.assoc ⟩
                  C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
                  ∎

                -- α⇐{B',Y,X} ∘ id⊗σ{X,Y} ∘ α⇒{B',X,Y} ≈ (σ⇐{B',Y}⊗id) ∘ α⇐{Y,B',X} ∘ σ⇒{B'⊗X,Y}
                claim-B : ∀ {X Y B'} →
                  C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}
                  C.≈ C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y}
                claim-B {X} {Y} {B'} = begin
                  C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}
                    ≈˘⟨ C.identityˡ ⟩
                  C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
                    ≈˘⟨ C.∘-resp-≈ˡ (C.Equiv.trans (C.Equiv.sym (Functor.homomorphism C.⊗))
                           (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.braiding.iso.isoˡ _ , C.identityˡ)) (Functor.identity C.⊗))) ⟩
                  (C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ C.σ⇒ {B'} {Y} C.⊗₁ C.id) C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
                    ≈⟨ C.assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ (C.σ⇒ {B'} {Y} C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ (C.σ⇒ {B'} {Y} C.⊗₁ C.id C.∘ ((C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y}) C.∘ C.α⇒ {B'} {X} {Y}))
                    ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ ((C.σ⇒ {B'} {Y} C.⊗₁ C.id C.∘ (C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y})) C.∘ C.α⇒ {B'} {X} {Y})
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ˡ C.sym-assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ (((C.σ⇒ {B'} {Y} C.⊗₁ C.id C.∘ C.α⇐ {B'} {Y} {X}) C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y}) C.∘ C.α⇒ {B'} {X} {Y})
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ˡ (C.hexagon₂ {X = B'} {Y = X} {Z = Y}) ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ (((C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y}) C.∘ C.α⇐ {B'} {X} {Y}) C.∘ C.α⇒ {B'} {X} {Y})
                    ≈⟨ refl⟩∘⟨ C.assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ ((C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y}) C.∘ (C.α⇐ {B'} {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}))
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ʳ (C.associator.isoˡ {X = B'} {Y = X} {Z = Y}) ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ ((C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y}) C.∘ C.id)
                    ≈⟨ refl⟩∘⟨ C.identityʳ ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id C.∘ (C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y})
                  ∎

                -- Main coherence:
                -- σ⇐{B',Y}⊗id ∘ (α⇐{Y,B',X} ∘ id⊗f' ∘ α⇒{Y,A',X}) ∘ σ⇒{A',Y}⊗id ≈ β ∘ f'⊗id ∘ β
                coherence : ∀ {X Y A' B'} (f' : A' C.⊗₀ X C.⇒ B' C.⊗₀ X) →
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ C.id C.⊗₁ f' C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}
                  C.≈
                  (C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}) C.∘ f' C.⊗₁ C.id {Y} C.∘ (C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X})
                coherence {X} {Y} {A'} {B'} f' = begin
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ C.id C.⊗₁ f' C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}
                    ≈⟨ refl⟩∘⟨ C.assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ ((C.id C.⊗₁ f' C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}))
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ʳ C.assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ (C.id C.⊗₁ f' C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X})))
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ˡ
                         (C.Equiv.trans (C.Equiv.sym C.identityˡ)
                           (C.Equiv.trans (C.∘-resp-≈ˡ (C.Equiv.sym (C.commutative {B' C.⊗₀ X} {Y})))
                             (C.Equiv.trans C.assoc
                               (C.∘-resp-≈ʳ (C.braiding.⇒.commute (C.id , f'))))))) ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ ((C.σ⇒ {B' C.⊗₀ X} {Y} C.∘ (f' C.⊗₁ C.id {Y} C.∘ C.σ⇒ {Y} {A' C.⊗₀ X})) C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X})))
                    ≈⟨ refl⟩∘⟨ C.∘-resp-≈ʳ C.assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ (C.σ⇒ {B' C.⊗₀ X} {Y} C.∘ ((f' C.⊗₁ C.id {Y} C.∘ C.σ⇒ {Y} {A' C.⊗₀ X}) C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}))))
                    ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
                  C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ ((C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y}) C.∘ ((f' C.⊗₁ C.id {Y} C.∘ C.σ⇒ {Y} {A' C.⊗₀ X}) C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X})))
                    ≈⟨ C.sym-assoc ⟩
                  (C.σ⇐ {B'} {Y} C.⊗₁ C.id {X} C.∘ (C.α⇐ {Y} {B'} {X} C.∘ C.σ⇒ {B' C.⊗₀ X} {Y})) C.∘
                    ((f' C.⊗₁ C.id {Y} C.∘ C.σ⇒ {Y} {A' C.⊗₀ X}) C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}))
                    ≈⟨ C.∘-resp-≈ˡ (C.Equiv.sym (claim-B {X} {Y} {B'})) ⟩
                  (C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}) C.∘
                    ((f' C.⊗₁ C.id {Y} C.∘ C.σ⇒ {Y} {A' C.⊗₀ X}) C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X}))
                    ≈⟨ C.∘-resp-≈ʳ C.assoc ⟩
                  (C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}) C.∘
                    (f' C.⊗₁ C.id {Y} C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ (C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id {X})))
                    ≈⟨ C.∘-resp-≈ʳ (refl⟩∘⟨ C.Equiv.sym (claim-A' {X} {Y} {A'})) ⟩
                  (C.α⇐ {B'} {Y} {X} C.∘ C.id C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {B'} {X} {Y}) C.∘
                    f' C.⊗₁ C.id {Y} C.∘ (C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X})
                  ∎

        -- ── Pure-coherence residuals ─────────────────────────────────────
        -- Each of the six coh-* lemmas below equates two structural
        -- morphisms — built from α⇒, α⇐, σ⇒ and id only — that implement
        -- the same wire permutation, so each is an instance of coherence
        -- for symmetric monoidal categories.  All six are proven manually
        -- from the hexagons, the pentagon and naturality.  The 6-wire
        -- residuals of assoc' reduce to a single σ-free core (coh-core):
        -- coh-pre peels its γ-tails off with γ-decomp, and coh-post is
        -- precisely the inverse equation of a coh-core instance.  coh-core
        -- itself is proven by peeling spectator wires (β-split₂/β-split₃,
        -- J-conjugation) down to a 4-wire Yang–Baxter exchange (θ-exch).

        -- σ⇒ ⊗ id pair cancellation: σ⇒{Y,X} ⊗ id ∘ σ⇒{X,Y} ⊗ id ≈ id
        σσ-cancelʳ : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {Y} {X} C.⊗₁ C.id {Z} C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id {Z} C.≈ C.id
        σσ-cancelʳ {X} {Y} {Z} = begin
          C.σ⇒ {Y} {X} C.⊗₁ C.id {Z} C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ ⊗id-merge ⟩
          (C.σ⇒ {Y} {X} C.∘ C.σ⇒ {X} {Y}) C.⊗₁ C.id {Z}
            ≈⟨ Functor.F-resp-≈ C.⊗ (C.commutative , C.Equiv.refl) ⟩
          C.id C.⊗₁ C.id
            ≈⟨ Functor.identity C.⊗ ⟩
          C.id
          ∎

        -- α⇐{A',X,Y} ∘ id⊗σ{Y,X} ∘ α⇒{A',Y,X} ≈ σ⇒{Y,A'⊗X} ∘ α⇒{Y,A',X} ∘ (σ{A',Y}⊗id)
        σα-swap : ∀ {X Y A' : C.Obj} →
          C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X}
          C.≈ C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
        σα-swap {X} {Y} {A'} = begin
          C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X}
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.identityʳ) ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.id)
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ σσ-cancelʳ)) ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ (C.σ⇒ {Y} {A'} C.⊗₁ C.id C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id)) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ (refl⟩∘⟨ C.hexagon₁ {X = Y} {Y = A'} {Z = X}) ⟩
          (C.α⇐ C.∘ (C.α⇒ {A'} {X} {Y} C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ C.sym-assoc ⟩
          ((C.α⇐ C.∘ C.α⇒ {A'} {X} {Y}) C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ (C.∘-resp-≈ˡ (C.associator.isoˡ {X = A'} {Y = X} {Z = Y})) ⟩
          (C.id C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ C.identityˡ ⟩
          (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.assoc ⟩
          C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
          ∎

        -- ── Helpers for coh-sub1ˡ ────────────────────────────────────────

        -- σ ∘ σ cancellation under id ⊗₁ -
        idσσ : ∀ {W X Y : C.Obj} →
          C.id {W} C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.≈ C.id
        idσσ = id⊗-merge
             ○ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.commutative)
             ○ Functor.identity C.⊗

        -- σ ∘ σ cancellation under - ⊗₁ id
        σσid : ∀ {X Y W : C.Obj} →
          C.σ⇒ {X} {Y} C.⊗₁ C.id {W} C.∘ C.σ⇒ {Y} {X} C.⊗₁ C.id C.≈ C.id
        σσid = ⊗id-merge
             ○ Functor.F-resp-≈ C.⊗ (C.commutative , C.Equiv.refl)
             ○ Functor.identity C.⊗

        -- α⇒ ∘ α⇐ cancellation under - ⊗₁ id
        α⊗id-cancel : ∀ {X Y Z W : C.Obj} →
          C.α⇒ {X} {Y} {Z} C.⊗₁ C.id {W} C.∘ C.α⇐ {X} {Y} {Z} C.⊗₁ C.id C.≈ C.id
        α⊗id-cancel = ⊗id-merge
                    ○ Functor.F-resp-≈ C.⊗ (C.associator.isoʳ , C.Equiv.refl)
                    ○ Functor.identity C.⊗

        -- hexagon₂, packaged: merging an adjacent-braid normal form into σ {X⊗Y} {Z}
        braid-merge : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ {X} {Z} {Y}
            C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z} C.∘ C.α⇒ {X} {Y} {Z}
          C.≈ C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}
        braid-merge = (refl⟩∘⟨ C.sym-assoc) ○ C.sym-assoc ○ (C.sym-assoc ⟩∘⟨refl)
                    ○ (C.hexagon₂ ⟩∘⟨refl) ○ cancelʳ C.associator.isoˡ

        -- σ {X⊗Y} {Z} pre-composed with α⇐
        swap-low : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {X C.⊗₀ Y} {Z} C.∘ C.α⇐ {X} {Y} {Z}
          C.≈ C.α⇒ {Z} {X} {Y} C.∘ C.σ⇒ {X} {Z} C.⊗₁ C.id {Y}
              C.∘ C.α⇐ {X} {Z} {Y} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}
        swap-low = insertˡ C.associator.isoʳ
                 ○ (refl⟩∘⟨ (C.sym-assoc ○ (⟺ C.hexagon₂) ○ C.assoc))

        -- conjugated form used for the head of the main chain
        swap-cnj : ∀ {X Y Z : C.Obj} →
          C.α⇒ {Z} {X} {Y} C.∘ C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ {X} {Z} {Y}
          C.≈ C.σ⇒ {X C.⊗₀ Y} {Z} C.∘ C.α⇐ {X} {Y} {Z} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Z} {Y}
        swap-cnj = C.Equiv.sym
          ( C.sym-assoc ○ (swap-low ⟩∘⟨refl) ○ C.assoc
          ○ (refl⟩∘⟨ C.assoc) ○ (refl⟩∘⟨ (refl⟩∘⟨ cancelʳ idσσ)) )

        -- three-braid rotation
        swap-rot : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {Z C.⊗₀ X} {Y} C.∘ C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}
          C.≈ C.id {Y} C.⊗₁ C.σ⇒ {X} {Z} C.∘ C.α⇒ {Y} {X} {Z} C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id {Z}
        swap-rot = C.sym-assoc ○ (swap-low ⟩∘⟨refl) ○ C.assoc
                 ○ (refl⟩∘⟨ C.assoc) ○ (refl⟩∘⟨ (refl⟩∘⟨ C.assoc))
                 ○ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ ⟺ (C.braiding.⇒.commute (C.σ⇒ , C.id)))))
                 ○ (refl⟩∘⟨ (refl⟩∘⟨ pullˡ (⟺ braid-merge)))
                 ○ (refl⟩∘⟨ C.sym-assoc)
                 ○ (refl⟩∘⟨ (cancelˡ σσid ⟩∘⟨refl))
                 ○ (refl⟩∘⟨ C.assoc)
                 ○ cancelˡ C.associator.isoʳ
                 ○ C.assoc

        -- pentagon with one leg inverted
        pentagon-inv : ∀ {X Y Z W : C.Obj} →
          C.id {X} C.⊗₁ C.α⇒ {Y} {Z} {W} C.∘ C.α⇒ {X} {Y C.⊗₀ Z} {W}
          C.≈ C.α⇒ {X} {Y} {Z C.⊗₀ W} C.∘ C.α⇒ {X C.⊗₀ Y} {Z} {W}
              C.∘ C.α⇐ {X} {Y} {Z} C.⊗₁ C.id {W}
        pentagon-inv = insertʳ α⊗id-cancel ○ ((C.assoc ○ C.pentagon) ⟩∘⟨refl) ○ C.assoc

        -- slide f past α⇒ when it sits under id {X ⊗₀ Y} ⊗₁ -
        id₂-slide : ∀ {X Y Z W : C.Obj} {f : Z C.⇒ W} →
          C.α⇒ {X} {Y} {W} C.∘ C.id {X C.⊗₀ Y} C.⊗₁ f
          C.≈ C.id {X} C.⊗₁ (C.id {Y} C.⊗₁ f) C.∘ C.α⇒ {X} {Y} {Z}
        id₂-slide = (refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.sym (Functor.identity C.⊗) , C.Equiv.refl))
                  ○ C.assoc-commute-from

        -- ((p , q) , r) , s ↦ ((s , q) , (p , r))
        coh-sub1ˡ : ∀ {P Q R S : C.Obj} →
          γ {P} {S} {R} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
          C.≈ C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
              C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
              C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
              C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
        coh-sub1ˡ {P} {Q} {R} {S} = begin
          γ {P} {S} {R} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            -- fully right-associate
            ≈⟨ C.assoc ○ (refl⟩∘⟨ (C.assoc ○ (refl⟩∘⟨ (C.assoc ○ (refl⟩∘⟨ (C.assoc
               ○ (refl⟩∘⟨ (C.assoc ○ (refl⟩∘⟨ C.assoc))))))))) ⟩
          C.α⇒ {S C.⊗₀ Q} {P} {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            -- slide σ {R} {S} through the associator
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ id₂-slide ○ C.assoc) ⟩
          C.α⇒ {S C.⊗₀ Q} {P} {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            -- pentagon (backwards)
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.pentagon ⟩
          C.α⇒ {S C.⊗₀ Q} {P} {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- merge the id {P} ⊗₁ - block and apply hexagon₂ (braid-merge)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
               ( pullˡ id⊗-merge ○ pullˡ id⊗-merge ○ pullˡ id⊗-merge
               ○ ((Functor.F-resp-≈ C.⊗ (C.Equiv.refl , (C.assoc ○ C.assoc ○ braid-merge))) ⟩∘⟨refl)
               ○ pushˡ (C.Equiv.sym id⊗-merge) ) ⟩
          C.α⇒ {S C.⊗₀ Q} {P} {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- turn the head into the outer braid σ {P⊗R} {S⊗Q}
            ≈⟨ (refl⟩∘⟨ C.sym-assoc) ○ C.sym-assoc ○ (swap-cnj ⟩∘⟨refl)
               ○ C.assoc ○ (refl⟩∘⟨ C.assoc) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- rotate the three middle braids (swap-rot under id {P} ⊗₁ -)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨
               ( pullˡ id⊗-merge ○ pullˡ id⊗-merge
               ○ ((Functor.F-resp-≈ C.⊗ (C.Equiv.refl , (C.assoc ○ swap-rot))) ⟩∘⟨refl)
               ○ pushˡ (C.Equiv.sym id⊗-merge)
               ○ (refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge)) ) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- slide σ {Q} {R} through the associator
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
               (pullˡ (C.Equiv.sym C.assoc-commute-from) ○ C.assoc) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.α⇒ {P} {R C.⊗₀ Q} {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- pentagon with one leg inverted
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
               (pullˡ pentagon-inv ○ C.assoc ○ (refl⟩∘⟨ C.assoc)) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.α⇒ {P} {R} {Q C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- collapse the σ {Q} {S} conjugation
            ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (pullˡ (C.Equiv.sym id₂-slide) ○ C.assoc))
               ○ cancelˡ C.associator.isoˡ) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            -- reassemble β ⊗₁ id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
               (pullˡ ⊗id-merge ○ ⊗id-merge ○ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl)) ⟩
          C.σ⇒ {P C.⊗₀ R} {S C.⊗₀ Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
          ∎

        -- (σ⇒ ∘ σ⇒) ⊗ id ≈ id
        σσ⊗id : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {Y} {X} C.⊗₁ C.id {Z} C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id C.≈ C.id
        σσ⊗id = C.Equiv.trans ⊗id-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.commutative , C.Equiv.refl))
            (Functor.identity C.⊗))

        -- (α⇒ ∘ α⇐) ⊗ id ≈ id and (α⇐ ∘ α⇒) ⊗ id ≈ id
        α⇒α⇐⊗id : ∀ {X Y Z W : C.Obj} →
          C.α⇒ {X} {Y} {Z} C.⊗₁ C.id {W} C.∘ C.α⇐ {X} {Y} {Z} C.⊗₁ C.id C.≈ C.id
        α⇒α⇐⊗id = C.Equiv.trans ⊗id-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.associator.isoʳ , C.Equiv.refl))
            (Functor.identity C.⊗))

        α⇐α⇒⊗id : ∀ {X Y Z W : C.Obj} →
          C.α⇐ {X} {Y} {Z} C.⊗₁ C.id {W} C.∘ C.α⇒ {X} {Y} {Z} C.⊗₁ C.id C.≈ C.id
        α⇐α⇒⊗id = C.Equiv.trans ⊗id-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.associator.isoˡ , C.Equiv.refl))
            (Functor.identity C.⊗))

        -- id ⊗ (α⇐ ∘ α⇒) ≈ id
        id⊗α⇐α⇒ : ∀ {W X Y Z : C.Obj} →
          C.id {W} C.⊗₁ C.α⇐ {X} {Y} {Z} C.∘ C.id C.⊗₁ C.α⇒ {X} {Y} {Z} C.≈ C.id
        id⊗α⇐α⇒ = C.Equiv.trans id⊗-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.associator.isoˡ))
            (Functor.identity C.⊗))

        -- Hexagon₁ in β-form: β {A'} {Y} {X} ≈ σ⇒ ∘ α⇒ ∘ σ⇒ ⊗ id  (claim-A' of GConstruction)
        β-hex₁ : ∀ {A' X Y : C.Obj} →
          β {A'} {Y} {X}
          C.≈ C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
        β-hex₁ {A'} {X} {Y} = begin
          C.α⇐ {A'} {X} {Y} C.∘ C.id C.⊗₁ C.σ⇒ {Y} {X} C.∘ C.α⇒ {A'} {Y} {X}
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.identityʳ) ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.id)
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ σσ⊗id)) ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ (C.σ⇒ {Y} {A'} C.⊗₁ C.id C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id)) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ {Y} {A'} C.⊗₁ C.id))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ (refl⟩∘⟨ C.hexagon₁ {X = Y} {Y = A'} {Z = X}) ⟩
          (C.α⇐ C.∘ (C.α⇒ {A'} {X} {Y} C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}))) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ C.sym-assoc ⟩
          ((C.α⇐ C.∘ C.α⇒ {A'} {X} {Y}) C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ (C.∘-resp-≈ˡ (C.associator.isoˡ {X = A'} {Y = X} {Z = Y})) ⟩
          (C.id C.∘ (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X})) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.∘-resp-≈ˡ C.identityˡ ⟩
          (C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X}) C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
            ≈⟨ C.assoc ⟩
          C.σ⇒ {Y} {A' C.⊗₀ X} C.∘ C.α⇒ {Y} {A'} {X} C.∘ C.σ⇒ {A'} {Y} C.⊗₁ C.id
          ∎

        -- Hexagon₂ in β-form: σ⇒ ⊗ id ∘ α⇐ ∘ σ⇒ ≈ β
        β-hex₂ : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}
          C.≈ β {X} {Y} {Z}
        β-hex₂ {X} {Y} {Z} = begin
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertʳ C.associator.isoˡ ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y}
            C.∘ (C.σ⇒ {X C.⊗₀ Y} {Z} C.∘ C.α⇐ {X} {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y}
            C.∘ (C.α⇐ {Z} {X} {Y} C.∘ (C.σ⇒ {X C.⊗₀ Y} {Z} C.∘ C.α⇐ {X} {Y} {Z})) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.∘-resp-≈ˡ C.sym-assoc ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y}
            C.∘ ((C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}) C.∘ C.α⇐ {X} {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈˘⟨ refl⟩∘⟨ C.∘-resp-≈ˡ (C.hexagon₂ {X = X} {Y = Y} {Z = Z}) ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y}
            C.∘ ((C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ {X} {Z} {Y}) C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.∘-resp-≈ˡ C.assoc ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y}
            C.∘ (C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ {X} {Z} {Y} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y}
            C.∘ C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ (C.α⇐ {X} {Z} {Y} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ cancelˡ σσ⊗id ⟩
          (C.α⇐ {X} {Z} {Y} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}) C.∘ C.α⇒ {X} {Y} {Z}
            ≈⟨ C.assoc ⟩
          C.α⇐ {X} {Z} {Y} C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z} C.∘ C.α⇒ {X} {Y} {Z}
          ∎

        -- Variant: σ⇒ ⊗ id ∘ α⇐ ≈ β ∘ σ⇒
        β-hex₂' : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y}
          C.≈ β {X} {Y} {Z} C.∘ C.σ⇒ {Z} {X C.⊗₀ Y}
        β-hex₂' {X} {Y} {Z} = begin
          C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y}
            ≈⟨ insertʳ C.commutative ⟩
          ((C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y}) C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}) C.∘ C.σ⇒ {Z} {X C.⊗₀ Y}
            ≈⟨ C.assoc ⟩∘⟨refl ⟩
          (C.σ⇒ {Z} {X} C.⊗₁ C.id {Y} C.∘ C.α⇐ {Z} {X} {Y} C.∘ C.σ⇒ {X C.⊗₀ Y} {Z}) C.∘ C.σ⇒ {Z} {X C.⊗₀ Y}
            ≈⟨ β-hex₂ ⟩∘⟨refl ⟩
          β {X} {Y} {Z} C.∘ C.σ⇒ {Z} {X C.⊗₀ Y}
          ∎

        -- Reassociation ((W X) Y) Z ≅ W ((X Y) Z) used to extract a left spectator
        J⇒ : ∀ {W X Y Z : C.Obj} →
          ((W C.⊗₀ X) C.⊗₀ Y) C.⊗₀ Z C.⇒ W C.⊗₀ ((X C.⊗₀ Y) C.⊗₀ Z)
        J⇒ = C.α⇒ C.∘ C.α⇒ C.⊗₁ C.id

        J⇐ : ∀ {W X Y Z : C.Obj} →
          W C.⊗₀ ((X C.⊗₀ Y) C.⊗₀ Z) C.⇒ ((W C.⊗₀ X) C.⊗₀ Y) C.⊗₀ Z
        J⇐ = C.α⇐ C.⊗₁ C.id C.∘ C.α⇐

        J-isoʳ : ∀ {W X Y Z : C.Obj} → J⇒ {W} {X} {Y} {Z} C.∘ J⇐ {W} {X} {Y} {Z} C.≈ C.id
        J-isoʳ = C.Equiv.trans (cancelInner α⇒α⇐⊗id) C.associator.isoʳ

        -- Inverted pentagon
        pentagon⁻¹ : ∀ {A B D E : C.Obj} →
          C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
          C.≈ C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}
        pentagon⁻¹ {A} {B} {D} {E} = begin
          C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
            ≈⟨ insertʳ αα-pair ⟩
          ((C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
              C.∘ (C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E}))
            C.∘ (C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E})
            ≈⟨ collapse ⟩∘⟨refl ⟩
          C.id C.∘ (C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E})
            ≈⟨ C.identityˡ ⟩
          C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}
          ∎
          where
            αα-pair : (C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E})
                      C.∘ (C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}) C.≈ C.id
            αα-pair = C.Equiv.trans (cancelInner C.associator.isoʳ) C.associator.isoʳ

            collapse : (C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
                       C.∘ (C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E}) C.≈ C.id
            collapse = begin
              (C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
                C.∘ (C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E})
                ≈˘⟨ refl⟩∘⟨ C.pentagon ⟩
              (C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
                C.∘ (C.id {A} C.⊗₁ C.α⇒ {B} {D} {E} C.∘ C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E})
                ≈⟨ C.assoc ⟩
              C.α⇐ {A} {B} {D} C.⊗₁ C.id {E}
                C.∘ (C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
                C.∘ (C.id {A} C.⊗₁ C.α⇒ {B} {D} {E} C.∘ C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E})
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ {A} {B} {D} C.⊗₁ C.id {E}
                C.∘ C.α⇐ {A} {B C.⊗₀ D} {E}
                C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
                C.∘ (C.id {A} C.⊗₁ C.α⇒ {B} {D} {E} C.∘ C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E})
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ id⊗α⇐α⇒ ⟩
              C.α⇐ {A} {B} {D} C.⊗₁ C.id {E}
                C.∘ C.α⇐ {A} {B C.⊗₀ D} {E}
                C.∘ C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
                ≈⟨ refl⟩∘⟨ cancelˡ C.associator.isoˡ ⟩
              C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
                ≈⟨ α⇐α⇒⊗id ⟩
              C.id
              ∎

        -- β on a compound first factor: extract the left spectator W
        β-extract : ∀ {W X Y Z : C.Obj} →
          β {W C.⊗₀ X} {Y} {Z}
          C.≈ J⇐ {W} {X} {Z} {Y} C.∘ C.id {W} C.⊗₁ β {X} {Y} {Z} C.∘ J⇒ {W} {X} {Y} {Z}
        β-extract {W} {X} {Y} {Z} = C.Equiv.sym (begin
          J⇐ {W} {X} {Z} {Y} C.∘ C.id {W} C.⊗₁ β {X} {Y} {Z} C.∘ J⇒ {W} {X} {Y} {Z}
            ≈˘⟨ refl⟩∘⟨ C.∘-resp-≈ˡ (C.Equiv.trans (C.∘-resp-≈ʳ id⊗-merge) id⊗-merge) ⟩
          (C.α⇐ {W} {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ {W} {X C.⊗₀ Z} {Y})
            C.∘ (C.id {W} C.⊗₁ C.α⇐ {X} {Z} {Y}
              C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
              C.∘ C.id {W} C.⊗₁ C.α⇒ {X} {Y} {Z})
            C.∘ (C.α⇒ {W} {X C.⊗₀ Y} {Z} C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z})
            ≈⟨ C.Equiv.trans C.assoc (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ C.assoc)))) ⟩
          C.α⇐ {W} {X} {Z} C.⊗₁ C.id {Y}
            C.∘ C.α⇐ {W} {X C.⊗₀ Z} {Y}
            C.∘ C.id {W} C.⊗₁ C.α⇐ {X} {Z} {Y}
            C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
            C.∘ C.id {W} C.⊗₁ C.α⇒ {X} {Y} {Z}
            C.∘ C.α⇒ {W} {X C.⊗₀ Y} {Z} C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.pentagon))) ⟩
          C.α⇐ {W} {X} {Z} C.⊗₁ C.id {Y}
            C.∘ C.α⇐ {W} {X C.⊗₀ Z} {Y}
            C.∘ C.id {W} C.⊗₁ C.α⇐ {X} {Z} {Y}
            C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ C.Equiv.trans (C.∘-resp-≈ʳ C.sym-assoc) C.sym-assoc ⟩
          (C.α⇐ {W} {X} {Z} C.⊗₁ C.id {Y}
            C.∘ C.α⇐ {W} {X C.⊗₀ Z} {Y}
            C.∘ C.id {W} C.⊗₁ C.α⇐ {X} {Z} {Y})
            C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ pentagon⁻¹ ⟩∘⟨refl ⟩
          (C.α⇐ {W C.⊗₀ X} {Z} {Y} C.∘ C.α⇐ {W} {X} {Z C.⊗₀ Y})
            C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ C.assoc ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ C.α⇐ {W} {X} {Z C.⊗₀ Y}
            C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z})
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ (C.α⇐ {W} {X} {Z C.⊗₀ Y} C.∘ C.id {W} C.⊗₁ (C.id {X} C.⊗₁ C.σ⇒ {Y} {Z}))
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.assoc-commute-to ⟩∘⟨refl ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ ((C.id {W} C.⊗₁ C.id {X}) C.⊗₁ C.σ⇒ {Y} {Z} C.∘ C.α⇐ {W} {X} {Y C.⊗₀ Z})
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ (C.id {W} C.⊗₁ C.id {X}) C.⊗₁ C.σ⇒ {Y} {Z}
            C.∘ C.α⇐ {W} {X} {Y C.⊗₀ Z}
            C.∘ C.α⇒ {W} {X} {Y C.⊗₀ Z} C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoˡ ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ (C.id {W} C.⊗₁ C.id {X}) C.⊗₁ C.σ⇒ {Y} {Z}
            C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇐ {W C.⊗₀ X} {Z} {Y}
            C.∘ C.id {W C.⊗₀ X} C.⊗₁ C.σ⇒ {Y} {Z}
            C.∘ C.α⇒ {W C.⊗₀ X} {Y} {Z}
          ∎)

        -- β ⊗ id as a conjugate of σ ⊗ id by J
        β⊗id-extract : ∀ {W X Y Z : C.Obj} →
          β {W} {X} {Y} C.⊗₁ C.id {Z}
          C.≈ J⇐ {W} {Y} {X} {Z} C.∘ C.id {W} C.⊗₁ (C.σ⇒ {X} {Y} C.⊗₁ C.id {Z}) C.∘ J⇒ {W} {X} {Y} {Z}
        β⊗id-extract {W} {X} {Y} {Z} = C.Equiv.sym (begin
          J⇐ {W} {Y} {X} {Z} C.∘ C.id {W} C.⊗₁ (C.σ⇒ {X} {Y} C.⊗₁ C.id {Z}) C.∘ J⇒ {W} {X} {Y} {Z}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          (C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {W} {Y C.⊗₀ X} {Z})
            C.∘ (C.id {W} C.⊗₁ (C.σ⇒ {X} {Y} C.⊗₁ C.id {Z}) C.∘ C.α⇒ {W} {X C.⊗₀ Y} {Z})
            C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈˘⟨ refl⟩∘⟨ C.assoc-commute-from ⟩∘⟨refl ⟩
          (C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {W} {Y C.⊗₀ X} {Z})
            C.∘ (C.α⇒ {W} {Y C.⊗₀ X} {Z} C.∘ (C.id {W} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {Z})
            C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ C.assoc ⟩
          C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z}
            C.∘ C.α⇐ {W} {Y C.⊗₀ X} {Z}
            C.∘ (C.α⇒ {W} {Y C.⊗₀ X} {Z} C.∘ (C.id {W} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {Z})
            C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ refl⟩∘⟨ C.Equiv.trans C.sym-assoc (C.∘-resp-≈ˡ C.sym-assoc) ⟩
          C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z}
            C.∘ ((C.α⇐ {W} {Y C.⊗₀ X} {Z} C.∘ C.α⇒ {W} {Y C.⊗₀ X} {Z}) C.∘ (C.id {W} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {Z})
            C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ refl⟩∘⟨ C.∘-resp-≈ˡ (C.Equiv.trans (C.∘-resp-≈ˡ C.associator.isoˡ) C.identityˡ) ⟩
          C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z}
            C.∘ (C.id {W} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {Z}
            C.∘ C.α⇒ {W} {X} {Y} C.⊗₁ C.id {Z}
            ≈⟨ refl⟩∘⟨ ⊗id-merge ⟩
          C.α⇐ {W} {Y} {X} C.⊗₁ C.id {Z}
            C.∘ (C.id {W} C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {W} {X} {Y}) C.⊗₁ C.id {Z}
            ≈⟨ ⊗id-merge ⟩
          (C.α⇐ {W} {Y} {X} C.∘ C.id {W} C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {W} {X} {Y}) C.⊗₁ C.id {Z}
          ∎)

        -- Collapse a composite of three J-conjugates into one J-conjugate
        conj3 : ∀ {W X₁ Y₁ Z₁ X₂ Y₂ Z₂ X₃ Y₃ Z₃ X₄ Y₄ Z₄ : C.Obj}
          {u : (X₃ C.⊗₀ Y₃) C.⊗₀ Z₃ C.⇒ (X₄ C.⊗₀ Y₄) C.⊗₀ Z₄}
          {v : (X₂ C.⊗₀ Y₂) C.⊗₀ Z₂ C.⇒ (X₃ C.⊗₀ Y₃) C.⊗₀ Z₃}
          {w : (X₁ C.⊗₀ Y₁) C.⊗₀ Z₁ C.⇒ (X₂ C.⊗₀ Y₂) C.⊗₀ Z₂} →
          (J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ J⇒) C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ v C.∘ J⇒)
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
          C.≈ J⇐ C.∘ C.id {W} C.⊗₁ (u C.∘ v C.∘ w) C.∘ J⇒
        conj3 {W = W} {u = u} {v = v} {w = w} = begin
          (J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ J⇒) C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ v C.∘ J⇒)
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
            ≈⟨ C.Equiv.trans C.assoc (C.∘-resp-≈ʳ C.assoc) ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ J⇒ C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ v C.∘ J⇒)
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ (J⇒ C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ v C.∘ J⇒))
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ J-isoʳ ⟩∘⟨refl ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ (C.id {W} C.⊗₁ v C.∘ J⇒)
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ C.id {W} C.⊗₁ v C.∘ J⇒
            C.∘ (J⇐ C.∘ C.id {W} C.⊗₁ w C.∘ J⇒)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ J-isoʳ ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ C.id {W} C.⊗₁ v C.∘ C.id {W} C.⊗₁ w C.∘ J⇒
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ (C.id {W} C.⊗₁ v C.∘ C.id {W} C.⊗₁ w) C.∘ J⇒
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ id⊗-merge ⟩∘⟨refl ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ u C.∘ C.id {W} C.⊗₁ (v C.∘ w) C.∘ J⇒
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          J⇐ C.∘ (C.id {W} C.⊗₁ u C.∘ C.id {W} C.⊗₁ (v C.∘ w)) C.∘ J⇒
            ≈⟨ refl⟩∘⟨ id⊗-merge ⟩∘⟨refl ⟩
          J⇐ C.∘ C.id {W} C.⊗₁ (u C.∘ v C.∘ w) C.∘ J⇒
          ∎

        -- 3-wire core (hexagon₁): σ⇒ ∘ id ⊗ σ⇒ ∘ α⇒ ≈ β ∘ σ⇒ ⊗ id ∘ β
        core-hex : ∀ {P Q R : C.Obj} →
          C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
          C.≈ β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R}
        core-hex {P} {Q} {R} = begin
          C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ refl⟩∘⟨ insertˡ C.associator.isoʳ ⟩
          C.σ⇒ {P} {R C.⊗₀ Q}
            C.∘ C.α⇒ {P} {R} {Q}
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ C.sym-assoc ⟩
          (C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.α⇒ {P} {R} {Q})
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ insertˡ C.associator.isoˡ ⟩∘⟨refl ⟩
          (C.α⇐ {R} {Q} {P}
            C.∘ C.α⇒ {R} {Q} {P}
            C.∘ C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.α⇒ {P} {R} {Q})
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈˘⟨ (refl⟩∘⟨ C.hexagon₁ {X = P} {Y = R} {Z = Q}) ⟩∘⟨refl ⟩
          (C.α⇐ {R} {Q} {P}
            C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q}
            C.∘ C.α⇒ {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ (refl⟩∘⟨ C.sym-assoc) ⟩∘⟨refl ⟩
          (C.α⇐ {R} {Q} {P}
            C.∘ (C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
            C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ C.sym-assoc ⟩∘⟨refl ⟩
          ((C.α⇐ {R} {Q} {P}
            C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
            C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
            ≈⟨ C.assoc ⟩
          (C.α⇐ {R} {Q} {P}
            C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
            C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P} {R} {Q}
            C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
          ∎

        -- 3-wire core, other bracketing (hexagon₁ + naturality)
        core-hex' : ∀ {Q R S : C.Obj} →
          C.σ⇒ {Q} {S C.⊗₀ R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S}
          C.≈ C.σ⇒ {R} {S} C.⊗₁ C.id {Q} C.∘ β {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S}
        core-hex' {Q} {R} {S} = begin
          C.σ⇒ {Q} {S C.⊗₀ R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S}
            ≈⟨ C.sym-assoc ⟩
          (C.σ⇒ {Q} {S C.⊗₀ R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S}) C.∘ C.α⇒ {Q} {R} {S}
            ≈⟨ C.braiding.⇒.commute (C.id , C.σ⇒) ⟩∘⟨refl ⟩
          (C.σ⇒ {R} {S} C.⊗₁ C.id {Q} C.∘ C.σ⇒ {Q} {R C.⊗₀ S}) C.∘ C.α⇒ {Q} {R} {S}
            ≈⟨ C.assoc ⟩
          C.σ⇒ {R} {S} C.⊗₁ C.id {Q} C.∘ C.σ⇒ {Q} {R C.⊗₀ S} C.∘ C.α⇒ {Q} {R} {S}
            ≈⟨ refl⟩∘⟨ insertˡ C.associator.isoˡ ⟩
          C.σ⇒ {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {S} {Q}
            C.∘ (C.α⇒ {R} {S} {Q} C.∘ (C.σ⇒ {Q} {R C.⊗₀ S} C.∘ C.α⇒ {Q} {R} {S}))
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ C.hexagon₁ {X = Q} {Y = R} {Z = S} ⟩
          C.σ⇒ {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {S} {Q}
            C.∘ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ (C.α⇒ {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S}))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.σ⇒ {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {S} {Q}
            C.∘ ((C.id {R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇒ {R} {Q} {S}) C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.σ⇒ {R} {S} C.⊗₁ C.id {Q}
            C.∘ (C.α⇐ {R} {S} {Q} C.∘ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇒ {R} {Q} {S}))
            C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S}
          ∎

        -- Yang–Baxter identity for β with a left spectator W
        yb-β : ∀ {W Q R S : C.Obj} →
          β {W C.⊗₀ S} {Q} {R} C.∘ β {W} {Q} {S} C.⊗₁ C.id {R} C.∘ β {W C.⊗₀ Q} {R} {S}
          C.≈ β {W} {R} {S} C.⊗₁ C.id {Q} C.∘ β {W C.⊗₀ R} {Q} {S} C.∘ β {W} {Q} {R} C.⊗₁ C.id {S}
        yb-β {W} {Q} {R} {S} = begin
          β {W C.⊗₀ S} {Q} {R} C.∘ β {W} {Q} {S} C.⊗₁ C.id {R} C.∘ β {W C.⊗₀ Q} {R} {S}
            ≈⟨ β-extract ⟩∘⟨ (β⊗id-extract ⟩∘⟨ β-extract) ⟩
          (J⇐ {W} {S} {R} {Q} C.∘ C.id {W} C.⊗₁ β {S} {Q} {R} C.∘ J⇒ {W} {S} {Q} {R})
            C.∘ (J⇐ {W} {S} {Q} {R} C.∘ C.id {W} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R}) C.∘ J⇒ {W} {Q} {S} {R})
            C.∘ (J⇐ {W} {Q} {S} {R} C.∘ C.id {W} C.⊗₁ β {Q} {R} {S} C.∘ J⇒ {W} {Q} {R} {S})
            ≈⟨ conj3 ⟩
          J⇐ {W} {S} {R} {Q}
            C.∘ C.id {W} C.⊗₁ (β {S} {Q} {R} C.∘ C.σ⇒ {Q} {S} C.⊗₁ C.id {R} C.∘ β {Q} {R} {S})
            C.∘ J⇒ {W} {Q} {R} {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (Functor.F-resp-≈ C.⊗ (C.Equiv.refl ,
                 C.Equiv.trans (C.Equiv.sym (core-hex {Q} {R} {S})) (core-hex' {Q} {R} {S})))) ⟩
          J⇐ {W} {S} {R} {Q}
            C.∘ C.id {W} C.⊗₁ (C.σ⇒ {R} {S} C.⊗₁ C.id {Q} C.∘ β {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ J⇒ {W} {Q} {R} {S}
            ≈˘⟨ conj3 ⟩
          (J⇐ {W} {S} {R} {Q} C.∘ C.id {W} C.⊗₁ (C.σ⇒ {R} {S} C.⊗₁ C.id {Q}) C.∘ J⇒ {W} {R} {S} {Q})
            C.∘ (J⇐ {W} {R} {S} {Q} C.∘ C.id {W} C.⊗₁ β {R} {Q} {S} C.∘ J⇒ {W} {R} {Q} {S})
            C.∘ (J⇐ {W} {R} {Q} {S} C.∘ C.id {W} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S}) C.∘ J⇒ {W} {Q} {R} {S})
            ≈˘⟨ β⊗id-extract ⟩∘⟨ (β-extract ⟩∘⟨ β⊗id-extract) ⟩
          β {W} {R} {S} C.⊗₁ C.id {Q} C.∘ β {W C.⊗₀ R} {Q} {S} C.∘ β {W} {Q} {R} C.⊗₁ C.id {S}
          ∎


        -- ((p , q) , r) , s ↦ ((p , s) , r) , q
        coh-sub2ˡ : ∀ {P Q R S : C.Obj} →
          C.α⇐ {P C.⊗₀ S} {R} {Q} C.∘ α {P} {Q} {R} {S}
          C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
          C.∘ C.σ⇒ {P C.⊗₀ Q} {S C.⊗₀ R}
          C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
          C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
          C.≈ β {P} {R} {S} C.⊗₁ C.id {Q}
              C.∘ β {P C.⊗₀ R} {Q} {S}
              C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
        coh-sub2ˡ {P} {Q} {R} {S} = begin
          C.α⇐ {P C.⊗₀ S} {R} {Q} C.∘ α {P} {Q} {R} {S}
            C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {P C.⊗₀ S} {R} {Q}
            C.∘ C.α⇒ {P C.⊗₀ S} {R} {Q}
            C.∘ (C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
              C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
              C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
              C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
              C.∘ C.α⇒ {R} {S} {P C.⊗₀ Q})
            C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ cancelˡ C.associator.isoˡ ⟩
          (C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
            C.∘ C.α⇒ {R} {S} {P C.⊗₀ Q})
            C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.Equiv.trans C.assoc (C.∘-resp-≈ʳ (C.Equiv.trans C.assoc
                 (C.∘-resp-≈ʳ (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ C.assoc))))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
            C.∘ C.α⇒ {R} {S} {P C.⊗₀ Q}
            C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (C.Equiv.trans C.sym-assoc
                   (C.Equiv.trans (C.∘-resp-≈ˡ (C.braiding.⇒.commute (C.id , C.σ⇒))) C.assoc))))))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
            C.∘ C.α⇒ {R} {S} {P C.⊗₀ Q}
            C.∘ C.σ⇒ {S} {R} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {R} {S} C.⊗₁ C.id {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (cancelˡ σσ⊗id))))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
            C.∘ C.α⇒ {R} {S} {P C.⊗₀ Q}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (C.hexagon₁ {X = P C.⊗₀ Q} {Y = R} {Z = S})))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ C.α⇐ {S} {P} {Q}
            C.∘ C.id {R} C.⊗₁ C.σ⇒ {P C.⊗₀ Q} {S}
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (C.Equiv.trans C.sym-assoc (C.∘-resp-≈ˡ id⊗-merge)))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q})
            C.∘ C.id {R} C.⊗₁ (C.α⇐ {S} {P} {Q} C.∘ C.σ⇒ {P C.⊗₀ Q} {S})
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ
                 (C.Equiv.trans C.sym-assoc (C.∘-resp-≈ˡ id⊗-merge))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ (C.σ⇒ {S} {P} C.⊗₁ C.id {Q} C.∘ C.α⇐ {S} {P} {Q} C.∘ C.σ⇒ {P C.⊗₀ Q} {S})
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ
                 (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , β-hex₂ {P} {Q} {S})))) ⟩
          C.σ⇒ {R} {P C.⊗₀ S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {R} {P C.⊗₀ S} {Q}
            C.∘ C.id {R} C.⊗₁ β {P} {Q} {S}
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.Equiv.trans C.sym-assoc
                 (C.Equiv.trans (C.∘-resp-≈ˡ (β-hex₂' {P C.⊗₀ S} {Q} {R})) C.assoc) ⟩
          β {P C.⊗₀ S} {Q} {R}
            C.∘ C.σ⇒ {R} {(P C.⊗₀ S) C.⊗₀ Q}
            C.∘ C.id {R} C.⊗₁ β {P} {Q} {S}
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.∘-resp-≈ʳ (C.Equiv.trans C.sym-assoc
                 (C.Equiv.trans (C.∘-resp-≈ˡ (C.braiding.⇒.commute (C.id , β))) C.assoc)) ⟩
          β {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.σ⇒ {R} {(P C.⊗₀ Q) C.⊗₀ S}
            C.∘ C.α⇒ {R} {P C.⊗₀ Q} {S}
            C.∘ C.σ⇒ {P C.⊗₀ Q} {R} C.⊗₁ C.id {S}
            ≈˘⟨ C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (β-hex₁ {P C.⊗₀ Q} {S} {R})) ⟩
          β {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ β {P C.⊗₀ Q} {R} {S}
            ≈⟨ yb-β {P} {Q} {R} {S} ⟩
          β {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ β {P C.⊗₀ R} {Q} {S}
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
          ∎

        -- ((p , q) , r) , s ↦ ((s , q) , r) , p
        coh-sub1ʳ : ∀ {P Q R S : C.Obj} →
          C.α⇐ {S C.⊗₀ Q} {R} {P}
          C.∘ C.id {S C.⊗₀ Q} C.⊗₁ C.σ⇒ {P} {R}
          C.∘ γ {P} {S} {R} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
          C.≈ (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
              C.∘ β {Q C.⊗₀ R} {P} {S}
              C.∘ (C.σ⇒ {P} {Q C.⊗₀ R} C.∘ C.α⇒ {P} {Q} {R}) C.⊗₁ C.id {S}
        coh-sub1ʳ {P} {Q} {R} {S} = begin
          C.α⇐ {S C.⊗₀ Q} {R} {P}
            C.∘ C.id {S C.⊗₀ Q} C.⊗₁ C.σ⇒ {P} {R}
            C.∘ γ {P} {S} {R} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                 (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ
                   (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ
                     (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ
                       (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ
                         (C.Equiv.trans C.assoc (C.∘-resp-≈ʳ C.assoc)))))))))) ⟩
          C.α⇐ {S C.⊗₀ Q} {R} {P}
            C.∘ C.id {S C.⊗₀ Q} C.⊗₁ C.σ⇒ {P} {R}
            C.∘ C.α⇒ {S C.⊗₀ Q} {P} {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇐ {S C.⊗₀ Q} {R} {P}
            C.∘ (C.id {S C.⊗₀ Q} C.⊗₁ C.σ⇒ {P} {R} C.∘ C.α⇒ {S C.⊗₀ Q} {P} {R})
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ {S C.⊗₀ Q} {R} {P}
            C.∘ (C.id {S C.⊗₀ Q} C.⊗₁ C.σ⇒ {P} {R} C.∘ C.α⇒ {S C.⊗₀ Q} {P} {R}))
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ σα-swap {R} {P} {S C.⊗₀ Q} ⟩∘⟨refl ⟩
          (C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.α⇒ {P} {S C.⊗₀ Q} {R}
            C.∘ C.σ⇒ {S C.⊗₀ Q} {P} C.⊗₁ C.id {R})
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.assoc ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ (C.α⇒ {P} {S C.⊗₀ Q} {R}
              C.∘ C.σ⇒ {S C.⊗₀ Q} {P} C.⊗₁ C.id {R})
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.α⇒ {P} {S C.⊗₀ Q} {R}
            C.∘ C.σ⇒ {S C.⊗₀ Q} {P} C.⊗₁ C.id {R}
            C.∘ C.σ⇒ {P} {S C.⊗₀ Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ σσ-cancelʳ ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.α⇒ {P} {S C.⊗₀ Q} {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ cancelˡ C.associator.isoʳ ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                 (Functor.F-resp-≈ C.⊗ (C.Equiv.sym (Functor.identity C.⊗) , C.Equiv.refl) ⟩∘⟨refl) ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.α⇒ {P} {Q} {S C.⊗₀ R}
            C.∘ (C.id {P} C.⊗₁ C.id {Q}) C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                 C.Equiv.trans (pullˡ C.assoc-commute-from) C.assoc ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.pentagon ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R} C.∘ C.α⇐ {Q} {S} {R})
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ ((C.σ⇒ {Q} {S} C.⊗₁ C.id {R} C.∘ C.α⇐ {Q} {S} {R})
                                 C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (((C.σ⇒ {Q} {S} C.⊗₁ C.id {R} C.∘ C.α⇐ {Q} {S} {R})
                                  C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
                                 C.∘ C.α⇒ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗
                 (C.Equiv.refl ,
                  C.Equiv.trans (C.∘-resp-≈ˡ (C.hexagon₂ {X = Q} {Y = R} {Z = S}))
                                (cancelʳ C.associator.isoˡ)) ⟩∘⟨refl ⟩
          C.σ⇒ {P} {(S C.⊗₀ Q) C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.Equiv.trans (pullˡ (C.braiding.⇒.commute (C.id , C.α⇐ C.∘ C.σ⇒))) C.assoc ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ C.σ⇒ {P} {(Q C.⊗₀ R) C.⊗₀ S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ σσ-cancelʳ ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ C.σ⇒ {P} {(Q C.⊗₀ R) C.⊗₀ S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.σ⇒ {Q C.⊗₀ R} {P} C.⊗₁ C.id {S}
            C.∘ C.σ⇒ {P} {Q C.⊗₀ R} C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ C.σ⇒ {P} {(Q C.⊗₀ R) C.⊗₀ S}
            C.∘ (C.α⇒ {P} {Q C.⊗₀ R} {S}
              C.∘ C.σ⇒ {Q C.⊗₀ R} {P} C.⊗₁ C.id {S})
            C.∘ C.σ⇒ {P} {Q C.⊗₀ R} C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ (C.σ⇒ {P} {(Q C.⊗₀ R) C.⊗₀ S}
              C.∘ (C.α⇒ {P} {Q C.⊗₀ R} {S}
                C.∘ C.σ⇒ {Q C.⊗₀ R} {P} C.⊗₁ C.id {S}))
            C.∘ C.σ⇒ {P} {Q C.⊗₀ R} C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈˘⟨ refl⟩∘⟨ σα-swap {S} {P} {Q C.⊗₀ R} ⟩∘⟨refl ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ (C.α⇐ {Q C.⊗₀ R} {S} {P}
              C.∘ C.id C.⊗₁ C.σ⇒ {P} {S}
              C.∘ C.α⇒ {Q C.⊗₀ R} {P} {S})
            C.∘ C.σ⇒ {P} {Q C.⊗₀ R} C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-merge ⟩
          (C.α⇐ {S} {Q} {R} C.∘ C.σ⇒ {Q C.⊗₀ R} {S}) C.⊗₁ C.id {P}
            C.∘ β {Q C.⊗₀ R} {P} {S}
            C.∘ (C.σ⇒ {P} {Q C.⊗₀ R} C.∘ C.α⇒ {P} {Q} {R}) C.⊗₁ C.id {S}
          ∎

        -- ((p , q) , r) , s ↦ ((r , q) , p) , s
        coh-sub2ʳ : ∀ {P Q R S : C.Obj} →
          C.α⇐ {R C.⊗₀ Q} {P} {S} C.∘ α {R} {S} {P} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
          C.≈ (β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R})
              C.⊗₁ C.id {S}
        coh-sub2ʳ {P} {Q} {R} {S} = begin
          C.α⇐ {R C.⊗₀ Q} {P} {S} C.∘ α {R} {S} {P} {Q} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {R C.⊗₀ Q} {P} {S}
            C.∘ C.α⇒ {R C.⊗₀ Q} {P} {S}
            C.∘ (C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
              C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
              C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
              C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
              C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S})
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ cancelˡ C.associator.isoˡ ⟩
          (C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S})
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ (C.α⇐ {P} {R C.⊗₀ Q} {S}
              C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
              C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
              C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S})
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ (C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
              C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
              C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S})
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ (C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
              C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S})
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.pentagon ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ
                 (C.Equiv.trans (C.Equiv.sym (Functor.homomorphism C.⊗))
                   (C.Equiv.trans
                     (Functor.F-resp-≈ C.⊗ (C.identityˡ , C.associator.isoˡ))
                     (Functor.identity C.⊗))) ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ (C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
              C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S})
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc-commute-from ⟩∘⟨refl ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ (C.α⇒ {P} {R C.⊗₀ Q} {S}
              C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S})
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.α⇒ {P} {R C.⊗₀ Q} {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ cancelˡ C.associator.isoˡ ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ ⊗id-merge ⟩
          C.σ⇒ {P} {R C.⊗₀ Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}) C.⊗₁ C.id {S}
            ≈⟨ ⊗id-merge ⟩
          (C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R})
            C.⊗₁ C.id {S}
            ≈⟨ Functor.F-resp-≈ C.⊗ (core , C.Equiv.refl) ⟩
          (β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R})
            C.⊗₁ C.id {S}
          ∎
          where
            -- 3-wire core: σ ∘ (id ⊗ σ) ∘ α⇒ ≈ β ∘ (σ ⊗ id) ∘ β,
            -- an instance of hexagon₁.
            core : C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                   C.≈ β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R}
            core = begin
              C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ refl⟩∘⟨ insertˡ C.associator.isoʳ ⟩
              C.σ⇒ {P} {R C.⊗₀ Q}
                C.∘ C.α⇒ {P} {R} {Q}
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ C.sym-assoc ⟩
              (C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.α⇒ {P} {R} {Q})
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ insertˡ C.associator.isoˡ ⟩∘⟨refl ⟩
              (C.α⇐ {R} {Q} {P}
                C.∘ C.α⇒ {R} {Q} {P}
                C.∘ C.σ⇒ {P} {R C.⊗₀ Q} C.∘ C.α⇒ {P} {R} {Q})
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈˘⟨ (refl⟩∘⟨ C.hexagon₁ {X = P} {Y = R} {Z = Q}) ⟩∘⟨refl ⟩
              (C.α⇐ {R} {Q} {P}
                C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q}
                C.∘ C.α⇒ {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ (refl⟩∘⟨ C.sym-assoc) ⟩∘⟨refl ⟩
              (C.α⇐ {R} {Q} {P}
                C.∘ (C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
                C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ C.sym-assoc ⟩∘⟨refl ⟩
              ((C.α⇐ {R} {Q} {P}
                C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
                C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q})
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
                ≈⟨ C.assoc ⟩
              (C.α⇐ {R} {Q} {P}
                C.∘ C.id {R} C.⊗₁ C.σ⇒ {P} {Q} C.∘ C.α⇒ {R} {P} {Q})
                C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q}
                C.∘ C.α⇐ {P} {R} {Q}
                C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R} C.∘ C.α⇒ {P} {Q} {R}
              ∎

        -- The two box-free residuals of associativity (see assoc' below):
        -- coh-pre routes the inputs of the three data morphisms,
        -- coh-post routes their outputs.

        -- θ : distant 3-wire swap, exchanging the outer factors around the middle
        θ : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (R C.⊗₀ Q) C.⊗₀ P
        θ {P} {Q} {R} = β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R}


        -- α as a conjugate of θ ⊗ id (repackaged coh-sub2ʳ)
        α-θ : ∀ {W X Y Z : C.Obj} →
          α {W} {X} {Y} {Z}
          C.≈ C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
        α-θ {W} {X} {Y} {Z} = begin
          α {W} {X} {Y} {Z}
            ≈⟨ insertˡ C.associator.isoʳ ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (C.α⇐ {W C.⊗₀ Z} {Y} {X} C.∘ α {W} {X} {Y} {Z})
            ≈⟨ refl⟩∘⟨ insertʳ C.associator.isoʳ ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X}
            C.∘ ((C.α⇐ {W C.⊗₀ Z} {Y} {X} C.∘ α {W} {X} {Y} {Z}) C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X})
            C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩∘⟨refl ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X}
            C.∘ (C.α⇐ {W C.⊗₀ Z} {Y} {X} C.∘ α {W} {X} {Y} {Z} C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X})
            C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ coh-sub2ʳ {Y} {Z} {W} {X} ⟩∘⟨refl ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
          ∎


        -- ── Generic coherence toolkit ────────────────────────────────────

        -- hexagon₁ solved for σ⇒ {X} {Y ⊗ Z}: braiding against a tensor,
        -- split into the two component braidings.
        hexR : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {X} {Y C.⊗₀ Z} C.≈
            C.α⇐ C.∘ C.id {Y} C.⊗₁ C.σ⇒ {X} {Z} C.∘ C.α⇒ C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id {Z} C.∘ C.α⇐
        hexR {X} {Y} {Z} = begin
          C.σ⇒
            ≈⟨ insertˡ C.associator.isoˡ ⟩
          C.α⇐ C.∘ (C.α⇒ C.∘ C.σ⇒)
            ≈⟨ refl⟩∘⟨ insertʳ C.associator.isoʳ ⟩
          C.α⇐ C.∘ ((C.α⇒ C.∘ C.σ⇒) C.∘ C.α⇒) C.∘ C.α⇐
            ≈⟨ refl⟩∘⟨ C.assoc ⟩∘⟨refl ⟩
          C.α⇐ C.∘ (C.α⇒ C.∘ C.σ⇒ C.∘ C.α⇒) C.∘ C.α⇐
            ≈˘⟨ refl⟩∘⟨ C.hexagon₁ ⟩∘⟨refl ⟩
          C.α⇐ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id) C.∘ C.α⇐
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ (C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id) C.∘ C.α⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐
          ∎


        -- hexagon₂ solved for σ⇒ {X ⊗ Y} {Z}.
        hexL : ∀ {X Y Z : C.Obj} →
          C.σ⇒ {X C.⊗₀ Y} {Z} C.≈
            C.α⇒ C.∘ C.σ⇒ {X} {Z} C.⊗₁ C.id {Y} C.∘ C.α⇐ C.∘ C.id {X} C.⊗₁ C.σ⇒ {Y} {Z} C.∘ C.α⇒
        hexL {X} {Y} {Z} = begin
          C.σ⇒
            ≈⟨ insertˡ C.associator.isoʳ ⟩
          C.α⇒ C.∘ (C.α⇐ C.∘ C.σ⇒)
            ≈⟨ refl⟩∘⟨ insertʳ C.associator.isoˡ ⟩
          C.α⇒ C.∘ ((C.α⇐ C.∘ C.σ⇒) C.∘ C.α⇐) C.∘ C.α⇒
            ≈˘⟨ refl⟩∘⟨ C.hexagon₂ ⟩∘⟨refl ⟩
          C.α⇒ C.∘ ((C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐) C.∘ C.id C.⊗₁ C.σ⇒) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ C.assoc ⟩∘⟨refl ⟩
          C.α⇒ C.∘ (C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ (C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒) C.∘ C.α⇒
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
          ∎


        -- ── Pentagon frame lemmas ────────────────────────────────────────

        pent-frame₁ : ∀ {A B X Z : C.Obj} →
          C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z}
          C.≈ C.α⇒ {A C.⊗₀ B} {X} {Z} C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z}
        pent-frame₁ {A} {B} {X} {Z} = begin
          C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z}
            ≈⟨ insertʳ (C.Equiv.trans (cancelInner α⇒α⇐⊗id) C.associator.isoʳ) ⟩
          ((C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z})
            C.∘ (C.α⇒ {A} {B C.⊗₀ X} {Z} C.∘ C.α⇒ {A} {B} {X} C.⊗₁ C.id {Z}))
            C.∘ (C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z})
            ≈⟨ C.assoc ⟩∘⟨refl ⟩
          (C.α⇐ {A} {B} {X C.⊗₀ Z}
            C.∘ (C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z}
              C.∘ (C.α⇒ {A} {B C.⊗₀ X} {Z} C.∘ C.α⇒ {A} {B} {X} C.⊗₁ C.id {Z})))
            C.∘ (C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z})
            ≈⟨ (refl⟩∘⟨ C.pentagon) ⟩∘⟨refl ⟩
          (C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ (C.α⇒ {A} {B} {X C.⊗₀ Z} C.∘ C.α⇒ {A C.⊗₀ B} {X} {Z}))
            C.∘ (C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z})
            ≈⟨ cancelˡ C.associator.isoˡ ⟩∘⟨refl ⟩
          C.α⇒ {A C.⊗₀ B} {X} {Z}
            C.∘ (C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z})
          ∎


        pent-frame₁' : ∀ {A B X Z : C.Obj} →
          C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z} C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
          C.≈ C.α⇒ {A C.⊗₀ B} {X} {Z} C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z}
        pent-frame₁' {A} {B} {X} {Z} = begin
          C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z} C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ {A} {B} {X C.⊗₀ Z} C.∘ C.id {A} C.⊗₁ C.α⇒ {B} {X} {Z}) C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
            ≈⟨ pent-frame₁ ⟩∘⟨refl ⟩
          (C.α⇒ {A C.⊗₀ B} {X} {Z} C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z})
            C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
            ≈⟨ C.assoc ⟩
          C.α⇒ {A C.⊗₀ B} {X} {Z}
            C.∘ (C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z}) C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {A C.⊗₀ B} {X} {Z}
            C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z}
            C.∘ C.α⇐ {A} {B C.⊗₀ X} {Z} C.∘ C.α⇒ {A} {B C.⊗₀ X} {Z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.associator.isoˡ ⟩
          C.α⇒ {A C.⊗₀ B} {X} {Z} C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z} C.∘ C.id
            ≈⟨ refl⟩∘⟨ C.identityʳ ⟩
          C.α⇒ {A C.⊗₀ B} {X} {Z} C.∘ C.α⇐ {A} {B} {X} C.⊗₁ C.id {Z}
          ∎


        pent-frame₃ : ∀ {A B D E : C.Obj} →
          C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
          C.≈ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}
        pent-frame₃ {A} {B} {D} {E} = begin
          C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
            ≈⟨ insertˡ α⇒α⇐⊗id ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ (C.α⇐ {A} {B} {D} C.⊗₁ C.id {E}
              C.∘ (C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}))
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ ((C.α⇐ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A} {B C.⊗₀ D} {E})
              C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ (C.α⇐ {A} {B} {D} C.⊗₁ C.id {E}
              C.∘ C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E})
            ≈⟨ refl⟩∘⟨ pentagon⁻¹ ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}
          ∎


        pent-frame₄ : ∀ {A B D E : C.Obj} →
          C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E} C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
          C.≈ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A C.⊗₀ B} {D} {E}
        pent-frame₄ {A} {B} {D} {E} = begin
          C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E} C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
            ≈⟨ C.sym-assoc ⟩
          (C.α⇐ {A} {B C.⊗₀ D} {E} C.∘ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}) C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
            ≈⟨ pent-frame₃ ⟩∘⟨refl ⟩
          (C.α⇒ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E})
            C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
            ≈⟨ C.assoc ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ (C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.α⇐ {A} {B} {D C.⊗₀ E}) C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            C.∘ C.α⇐ {A C.⊗₀ B} {D} {E}
            C.∘ C.α⇐ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A} {B} {D C.⊗₀ E}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.associator.isoˡ ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A C.⊗₀ B} {D} {E} C.∘ C.id
            ≈⟨ refl⟩∘⟨ C.identityʳ ⟩
          C.α⇒ {A} {B} {D} C.⊗₁ C.id {E} C.∘ C.α⇐ {A C.⊗₀ B} {D} {E}
          ∎


        -- ── β with a compound middle/last factor, split into simple βs ───

        -- β {P} {Q ⊗ R} {S} via β {P} {Q} {S} and β {P ⊗ Q} {R} {S}
        β-split₂ : ∀ {P Q R S : C.Obj} →
          β {P} {Q C.⊗₀ R} {S}
          C.≈ C.α⇒ {P C.⊗₀ S} {Q} {R}
              C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
              C.∘ β {P C.⊗₀ Q} {R} {S}
              C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
        β-split₂ {P} {Q} {R} {S} = begin
          β {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , hexL {Q} {R} {S}) ⟩∘⟨refl ⟩
          C.α⇐ {P} {S} {Q C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.α⇒ {S} {Q} {R} C.∘ C.σ⇒ {Q} {S} C.⊗₁ C.id {R}
                  C.∘ C.α⇐ {Q} {S} {R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {S} {Q C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R}
                  C.∘ C.α⇐ {Q} {S} {R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {S} {Q C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ (C.α⇐ {Q} {S} {R} C.∘ C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {S} {Q C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {S} {Q C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {S} {Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ pullˡ pent-frame₁ ⟩
          (C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R})
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ (C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R} C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R})
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {S C.⊗₀ Q} {R}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {S} C.⊗₁ C.id {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-to ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ ((C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R} C.∘ C.α⇐ {P} {Q C.⊗₀ S} {R})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P} {Q C.⊗₀ S} {R}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {S} {R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pent-frame₃ ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ (C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
              C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
              C.∘ C.α⇐ {P} {Q} {S C.⊗₀ R})
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ (C.α⇐ {P C.⊗₀ Q} {S} {R} C.∘ C.α⇐ {P} {Q} {S C.⊗₀ R})
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.α⇐ {P} {Q} {S C.⊗₀ R}
            C.∘ C.id {P} C.⊗₁ (C.id {Q} C.⊗₁ C.σ⇒ {R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-to ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ ((C.id {P} C.⊗₁ C.id {Q}) C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇐ {P} {Q} {R C.⊗₀ S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                 ((Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ (C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇐ {P} {Q} {R C.⊗₀ S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇐ {P} {Q} {R C.⊗₀ S}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q C.⊗₀ R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pent-frame₁' ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ C.α⇐ {P} {S} {Q} C.⊗₁ C.id {R}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ (C.α⇐ {P} {S} {Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇒ {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ ((C.α⇐ {P} {S} {Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {S}) C.∘ C.α⇒ {P} {Q} {S}) C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S}
            C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ C.α⇐ {P C.⊗₀ Q} {S} {R}
            C.∘ (C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S})
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ (C.α⇐ {P C.⊗₀ Q} {S} {R}
              C.∘ (C.id {P C.⊗₀ Q} C.⊗₁ C.σ⇒ {R} {S} C.∘ C.α⇒ {P C.⊗₀ Q} {R} {S}))
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
            ≈⟨ C.Equiv.refl ⟩
          C.α⇒ {P C.⊗₀ S} {Q} {R}
            C.∘ β {P} {Q} {S} C.⊗₁ C.id {R}
            C.∘ β {P C.⊗₀ Q} {R} {S}
            C.∘ C.α⇐ {P} {Q} {R} C.⊗₁ C.id {S}
          ∎


        -- β {P} {Q} {R ⊗ S} via β {P} {Q} {R} and β {P ⊗ R} {Q} {S}
        β-split₃ : ∀ {P Q R S : C.Obj} →
          β {P} {Q} {R C.⊗₀ S}
          C.≈ C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
              C.∘ β {P C.⊗₀ R} {Q} {S}
              C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
              C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
        β-split₃ {P} {Q} {R} {S} = begin
          β {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , hexR {Q} {R} {S}) ⟩∘⟨refl ⟩
          C.α⇐ {P} {R C.⊗₀ S} {Q}
            C.∘ C.id {P} C.⊗₁ (C.α⇐ {R} {S} {Q} C.∘ C.id {R} C.⊗₁ C.σ⇒ {Q} {S}
                  C.∘ C.α⇒ {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {R C.⊗₀ S} {Q}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {R} {S} {Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S}
                  C.∘ C.α⇒ {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {R C.⊗₀ S} {Q}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {R} {S} {Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ (C.α⇒ {R} {Q} {S} C.∘ C.σ⇒ {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {R C.⊗₀ S} {Q}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {R} {S} {Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {Q} {R} {S})
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.α⇐ {P} {R C.⊗₀ S} {Q}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {R} {S} {Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ pullˡ pent-frame₃ ⟩
          (C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q})
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ (C.α⇐ {P C.⊗₀ R} {S} {Q} C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q})
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.α⇐ {P} {R} {S C.⊗₀ Q}
            C.∘ C.id {P} C.⊗₁ (C.id {R} C.⊗₁ C.σ⇒ {Q} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-to ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ ((C.id {P} C.⊗₁ C.id {R}) C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇐ {P} {R} {Q C.⊗₀ S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨
                 ((Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ (C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇐ {P} {R} {Q C.⊗₀ S})
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q C.⊗₀ S}
            C.∘ C.id {P} C.⊗₁ C.α⇒ {R} {Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pent-frame₁ ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ (C.α⇒ {P C.⊗₀ R} {Q} {S}
              C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
              C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S})
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ (C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S} C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S})
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {R C.⊗₀ Q} {S}
            C.∘ C.id {P} C.⊗₁ (C.σ⇒ {Q} {R} C.⊗₁ C.id {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-to ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ ((C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S} C.∘ C.α⇐ {P} {Q C.⊗₀ R} {S})
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P} {Q C.⊗₀ R} {S}
            C.∘ C.id {P} C.⊗₁ C.α⇐ {Q} {R} {S}
            C.∘ C.α⇒ {P} {Q} {R C.⊗₀ S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pent-frame₄ ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ C.α⇐ {P} {R} {Q} C.⊗₁ C.id {S}
            C.∘ (C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ (C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ (C.α⇐ {P} {R} {Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.⊗₁ C.id {S}
            C.∘ (C.α⇒ {P} {Q} {R} C.⊗₁ C.id {S} C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ ((C.α⇐ {P} {R} {Q} C.∘ C.id {P} C.⊗₁ C.σ⇒ {Q} {R}) C.∘ C.α⇒ {P} {Q} {R}) C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S}
            C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ C.α⇐ {P C.⊗₀ R} {S} {Q}
            C.∘ (C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S})
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
            ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ (C.α⇐ {P C.⊗₀ R} {S} {Q}
              C.∘ (C.id {P C.⊗₀ R} C.⊗₁ C.σ⇒ {Q} {S} C.∘ C.α⇒ {P C.⊗₀ R} {Q} {S}))
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
            ≈⟨ C.Equiv.refl ⟩
          C.α⇒ {P} {R} {S} C.⊗₁ C.id {Q}
            C.∘ β {P C.⊗₀ R} {Q} {S}
            C.∘ β {P} {Q} {R} C.⊗₁ C.id {S}
            C.∘ C.α⇐ {P C.⊗₀ Q} {R} {S}
          ∎


        -- β composed with a braiding on its middle factor, as a big braiding
        σα-combine : ∀ {X M U : C.Obj} →
          β {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U}
          C.≈ C.σ⇒ {X} {M C.⊗₀ U} C.∘ C.α⇒ {X} {M} {U}
        σα-combine {X} {M} {U} = begin
          β {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U}
            ≈⟨ insertʳ C.associator.isoˡ ⟩
          ((β {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U}) C.∘ C.α⇐ {X} {M} {U}) C.∘ C.α⇒ {X} {M} {U}
            ≈⟨ C.assoc ⟩∘⟨refl ⟩
          (β {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U} C.∘ C.α⇐ {X} {M} {U}) C.∘ C.α⇒ {X} {M} {U}
            ≈⟨ C.assoc ⟩∘⟨refl ⟩
          (C.α⇐ {M} {U} {X}
            C.∘ ((C.id {M} C.⊗₁ C.σ⇒ {X} {U} C.∘ C.α⇒ {M} {X} {U})
              C.∘ (C.σ⇒ {X} {M} C.⊗₁ C.id {U} C.∘ C.α⇐ {X} {M} {U})))
            C.∘ C.α⇒ {X} {M} {U}
            ≈⟨ (refl⟩∘⟨ C.assoc) ⟩∘⟨refl ⟩
          (C.α⇐ {M} {U} {X}
            C.∘ C.id {M} C.⊗₁ C.σ⇒ {X} {U}
            C.∘ (C.α⇒ {M} {X} {U} C.∘ (C.σ⇒ {X} {M} C.⊗₁ C.id {U} C.∘ C.α⇐ {X} {M} {U})))
            C.∘ C.α⇒ {X} {M} {U}
            ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc) ⟩∘⟨refl ⟩
          (C.α⇐ {M} {U} {X}
            C.∘ C.id {M} C.⊗₁ C.σ⇒ {X} {U}
            C.∘ (C.α⇒ {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U}) C.∘ C.α⇐ {X} {M} {U})
            C.∘ C.α⇒ {X} {M} {U}
            ≈⟨ ((refl⟩∘⟨ refl⟩∘⟨ C.assoc) ⟩∘⟨refl) ⟩
          (C.α⇐ {M} {U} {X}
            C.∘ C.id {M} C.⊗₁ C.σ⇒ {X} {U}
            C.∘ C.α⇒ {M} {X} {U} C.∘ C.σ⇒ {X} {M} C.⊗₁ C.id {U} C.∘ C.α⇐ {X} {M} {U})
            C.∘ C.α⇒ {X} {M} {U}
            ≈˘⟨ hexR {X} {M} {U} ⟩∘⟨refl ⟩
          C.σ⇒ {X} {M C.⊗₀ U} C.∘ C.α⇒ {X} {M} {U}
          ∎


        pent-frame₅ : ∀ {A B D E : C.Obj} →
          C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
          C.≈ C.id {A} C.⊗₁ C.α⇐ {B} {D} {E} C.∘ C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E}
        pent-frame₅ {A} {B} {D} {E} = begin
          C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}
            ≈⟨ insertˡ id⊗α⇐α⇒ ⟩
          C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
            C.∘ (C.id {A} C.⊗₁ C.α⇒ {B} {D} {E}
              C.∘ (C.α⇒ {A} {B C.⊗₀ D} {E} C.∘ C.α⇒ {A} {B} {D} C.⊗₁ C.id {E}))
            ≈⟨ refl⟩∘⟨ C.pentagon ⟩
          C.id {A} C.⊗₁ C.α⇐ {B} {D} {E}
            C.∘ (C.α⇒ {A} {B} {D C.⊗₀ E} C.∘ C.α⇒ {A C.⊗₀ B} {D} {E})
          ∎


        -- sliding a braiding through θ: θ ∘ σ⇒ ⊗ id ≈ σ⇒ ⊗ id ∘ β
        θσ-slide : ∀ {W B D : C.Obj} →
          θ {B} {W} {D} C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D}
          C.≈ C.σ⇒ {W} {D} C.⊗₁ C.id {B} C.∘ β {W} {B} {D}
        θσ-slide {W} {B} {D} = begin
          θ {B} {W} {D} C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D}
            ≈⟨ C.assoc ⟩
          β {D} {B} {W}
            C.∘ ((C.σ⇒ {B} {D} C.⊗₁ C.id {W} C.∘ β {B} {W} {D}) C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {B} {D} C.⊗₁ C.id {W}
            C.∘ β {B} {W} {D} C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (β-hex₁ {B} {D} {W}) ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {B} {D} C.⊗₁ C.id {W}
            C.∘ C.σ⇒ {W} {B C.⊗₀ D}
            C.∘ ((C.α⇒ {W} {B} {D} C.∘ C.σ⇒ {B} {W} C.⊗₁ C.id {D}) C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {B} {D} C.⊗₁ C.id {W}
            C.∘ C.σ⇒ {W} {B C.⊗₀ D}
            C.∘ C.α⇒ {W} {B} {D}
            C.∘ C.σ⇒ {B} {W} C.⊗₁ C.id {D} C.∘ C.σ⇒ {W} {B} C.⊗₁ C.id {D}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ σσ⊗id ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {B} {D} C.⊗₁ C.id {W}
            C.∘ C.σ⇒ {W} {B C.⊗₀ D}
            C.∘ C.α⇒ {W} {B} {D} C.∘ C.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.identityʳ ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {B} {D} C.⊗₁ C.id {W}
            C.∘ C.σ⇒ {W} {B C.⊗₀ D}
            C.∘ C.α⇒ {W} {B} {D}
            ≈⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym (C.braiding.⇒.commute (C.id , C.σ⇒))) ⟩
          β {D} {B} {W}
            C.∘ (C.σ⇒ {W} {D C.⊗₀ B} C.∘ C.id {W} C.⊗₁ C.σ⇒ {B} {D}) C.∘ C.α⇒ {W} {B} {D}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          β {D} {B} {W}
            C.∘ C.σ⇒ {W} {D C.⊗₀ B}
            C.∘ C.id {W} C.⊗₁ C.σ⇒ {B} {D} C.∘ C.α⇒ {W} {B} {D}
            ≈⟨ pullˡ (C.Equiv.sym (β-hex₂' {D} {B} {W})) ⟩
          (C.σ⇒ {W} {D} C.⊗₁ C.id {B} C.∘ C.α⇐ {W} {D} {B})
            C.∘ C.id {W} C.⊗₁ C.σ⇒ {B} {D} C.∘ C.α⇒ {W} {B} {D}
            ≈⟨ C.assoc ⟩
          C.σ⇒ {W} {D} C.⊗₁ C.id {B}
            C.∘ C.α⇐ {W} {D} {B}
            C.∘ C.id {W} C.⊗₁ C.σ⇒ {B} {D} C.∘ C.α⇒ {W} {B} {D}
          ∎


        -- ── 4-wire heart: exchanging two θ-dances against one θ and a σ ──
        θ-exch : ∀ {X W U Y : C.Obj} →
          θ {Y} {W} {U} C.⊗₁ C.id {X}
          C.∘ β {Y C.⊗₀ W} {X} {U}
          C.∘ θ {X} {W} {Y} C.⊗₁ C.id {U}
          C.∘ β {X C.⊗₀ W} {U} {Y}
          C.≈ C.α⇐ {U C.⊗₀ W} {Y} {X}
              C.∘ C.id {U C.⊗₀ W} C.⊗₁ C.σ⇒ {X} {Y}
              C.∘ C.α⇒ {U C.⊗₀ W} {X} {Y}
              C.∘ θ {X} {W} {U} C.⊗₁ C.id {Y}
        θ-exch {X} {W} {U} {Y} = begin
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ β {Y C.⊗₀ W} {X} {U}
            C.∘ θ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (core-hex {X} {W} {Y} , C.Equiv.refl) ⟩∘⟨refl ⟩
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ β {Y C.⊗₀ W} {X} {U}
            C.∘ (C.σ⇒ {X} {Y C.⊗₀ W} C.∘ C.id {X} C.⊗₁ C.σ⇒ {W} {Y} C.∘ C.α⇒ {X} {W} {Y}) C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ β {Y C.⊗₀ W} {X} {U}
            C.∘ C.σ⇒ {X} {Y C.⊗₀ W} C.⊗₁ C.id {U}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y} C.∘ C.α⇒ {X} {W} {Y}) C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ β {Y C.⊗₀ W} {X} {U}
            C.∘ C.σ⇒ {X} {Y C.⊗₀ W} C.⊗₁ C.id {U}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y}) C.⊗₁ C.id {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ pullˡ σα-combine ⟩
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ (C.σ⇒ {X} {(Y C.⊗₀ W) C.⊗₀ U} C.∘ C.α⇒ {X} {Y C.⊗₀ W} {U})
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y}) C.⊗₁ C.id {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          θ {Y} {W} {U} C.⊗₁ C.id {X}
            C.∘ C.σ⇒ {X} {(Y C.⊗₀ W) C.⊗₀ U}
            C.∘ C.α⇒ {X} {Y C.⊗₀ W} {U}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y}) C.⊗₁ C.id {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ pullˡ (C.Equiv.sym (C.braiding.⇒.commute (C.id , θ {Y} {W} {U}))) ⟩
          (C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y} C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U})
            C.∘ C.α⇒ {X} {Y C.⊗₀ W} {U}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y}) C.⊗₁ C.id {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.α⇒ {X} {Y C.⊗₀ W} {U}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {Y}) C.⊗₁ C.id {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-from ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ (C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U}) C.∘ C.α⇒ {X} {W C.⊗₀ Y} {U})
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.α⇒ {X} {W C.⊗₀ Y} {U}
            C.∘ C.α⇒ {X} {W} {Y} C.⊗₁ C.id {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pent-frame₅ ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ (C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
              C.∘ C.α⇒ {X} {W} {Y C.⊗₀ U}
              C.∘ C.α⇒ {X C.⊗₀ W} {Y} {U})
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ (C.α⇒ {X} {W} {Y C.⊗₀ U} C.∘ C.α⇒ {X C.⊗₀ W} {Y} {U})
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ C.α⇒ {X} {W} {Y C.⊗₀ U}
            C.∘ C.α⇒ {X C.⊗₀ W} {Y} {U}
            C.∘ β {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoʳ ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ C.α⇒ {X} {W} {Y C.⊗₀ U}
            C.∘ C.id {X C.⊗₀ W} C.⊗₁ C.σ⇒ {U} {Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                 (Functor.F-resp-≈ C.⊗ (C.Equiv.sym (Functor.identity C.⊗) , C.Equiv.refl) ⟩∘⟨refl) ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ C.α⇒ {X} {W} {Y C.⊗₀ U}
            C.∘ (C.id {X} C.⊗₁ C.id {W}) C.⊗₁ C.σ⇒ {U} {Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-from ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ (C.id {X} C.⊗₁ (C.id {W} C.⊗₁ C.σ⇒ {U} {Y}) C.∘ C.α⇒ {X} {W} {U C.⊗₀ Y})
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ θ {Y} {W} {U}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ C.id {X} C.⊗₁ (C.id {W} C.⊗₁ C.σ⇒ {U} {Y})
            C.∘ C.α⇒ {X} {W} {U C.⊗₀ Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ (θ {Y} {W} {U} C.∘ C.σ⇒ {W} {Y} C.⊗₁ C.id {U})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {Y} {U}
            C.∘ C.id {X} C.⊗₁ (C.id {W} C.⊗₁ C.σ⇒ {U} {Y})
            C.∘ C.α⇒ {X} {W} {U C.⊗₀ Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ ((θ {Y} {W} {U} C.∘ C.σ⇒ {W} {Y} C.⊗₁ C.id {U}) C.∘ C.α⇐ {W} {Y} {U})
            C.∘ C.id {X} C.⊗₁ (C.id {W} C.⊗₁ C.σ⇒ {U} {Y})
            C.∘ C.α⇒ {X} {W} {U C.⊗₀ Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ (((θ {Y} {W} {U} C.∘ C.σ⇒ {W} {Y} C.⊗₁ C.id {U}) C.∘ C.α⇐ {W} {Y} {U})
                  C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y})
            C.∘ (C.α⇒ {X} {W} {U C.⊗₀ Y} C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y})
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , claimG) ⟩∘⟨refl ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ C.α⇐ {W} {U} {Y})
            C.∘ (C.α⇒ {X} {W} {U C.⊗₀ Y} C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y})
            ≈⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym id⊗-merge) ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {U} C.⊗₁ C.id {Y})
            C.∘ C.id {X} C.⊗₁ C.α⇐ {W} {U} {Y}
            C.∘ C.α⇒ {X} {W} {U C.⊗₀ Y}
            C.∘ C.α⇒ {X C.⊗₀ W} {U} {Y}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ pent-frame₅ ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.id {X} C.⊗₁ (C.σ⇒ {W} {U} C.⊗₁ C.id {Y})
            C.∘ C.α⇒ {X} {W C.⊗₀ U} {Y}
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym C.assoc-commute-from) ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ (C.α⇒ {X} {U C.⊗₀ W} {Y} C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.⊗₁ C.id {Y})
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.σ⇒ {X} {(U C.⊗₀ W) C.⊗₀ Y}
            C.∘ C.α⇒ {X} {U C.⊗₀ W} {Y}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.⊗₁ C.id {Y}
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ pullˡ (C.Equiv.sym σα-combine) ⟩
          (β {U C.⊗₀ W} {X} {Y} C.∘ C.σ⇒ {X} {U C.⊗₀ W} C.⊗₁ C.id {Y})
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.⊗₁ C.id {Y}
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ C.assoc ⟩
          β {U C.⊗₀ W} {X} {Y}
            C.∘ C.σ⇒ {X} {U C.⊗₀ W} C.⊗₁ C.id {Y}
            C.∘ (C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.⊗₁ C.id {Y}
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          β {U C.⊗₀ W} {X} {Y}
            C.∘ (C.σ⇒ {X} {U C.⊗₀ W} C.∘ C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.⊗₁ C.id {Y}
            C.∘ C.α⇒ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ ⊗id-merge ⟩
          β {U C.⊗₀ W} {X} {Y}
            C.∘ ((C.σ⇒ {X} {U C.⊗₀ W} C.∘ C.id {X} C.⊗₁ C.σ⇒ {W} {U}) C.∘ C.α⇒ {X} {W} {U}) C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl) ⟩
          β {U C.⊗₀ W} {X} {Y}
            C.∘ (C.σ⇒ {X} {U C.⊗₀ W} C.∘ C.id {X} C.⊗₁ C.σ⇒ {W} {U} C.∘ C.α⇒ {X} {W} {U}) C.⊗₁ C.id {Y}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (core-hex {X} {W} {U} , C.Equiv.refl) ⟩
          β {U C.⊗₀ W} {X} {Y} C.∘ θ {X} {W} {U} C.⊗₁ C.id {Y}
            ≈⟨ C.assoc ⟩
          C.α⇐ {U C.⊗₀ W} {Y} {X}
            C.∘ ((C.id {U C.⊗₀ W} C.⊗₁ C.σ⇒ {X} {Y} C.∘ C.α⇒ {U C.⊗₀ W} {X} {Y})
                  C.∘ θ {X} {W} {U} C.⊗₁ C.id {Y})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {U C.⊗₀ W} {Y} {X}
            C.∘ C.id {U C.⊗₀ W} C.⊗₁ C.σ⇒ {X} {Y}
            C.∘ C.α⇒ {U C.⊗₀ W} {X} {Y}
            C.∘ θ {X} {W} {U} C.⊗₁ C.id {Y}
          ∎
          where
            claimG : ((θ {Y} {W} {U} C.∘ C.σ⇒ {W} {Y} C.⊗₁ C.id {U}) C.∘ C.α⇐ {W} {Y} {U})
                       C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                     C.≈ C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ C.α⇐ {W} {U} {Y}
            claimG = begin
              ((θ {Y} {W} {U} C.∘ C.σ⇒ {W} {Y} C.⊗₁ C.id {U}) C.∘ C.α⇐ {W} {Y} {U})
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ (θσ-slide {W} {Y} {U} ⟩∘⟨refl) ⟩∘⟨refl ⟩
              ((C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ β {W} {Y} {U}) C.∘ C.α⇐ {W} {Y} {U})
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ C.assoc ⟩∘⟨refl ⟩
              (C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ (β {W} {Y} {U} C.∘ C.α⇐ {W} {Y} {U}))
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ C.assoc ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ (β {W} {Y} {U} C.∘ C.α⇐ {W} {Y} {U}) C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ β {W} {Y} {U} C.∘ C.α⇐ {W} {Y} {U} C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ C.α⇐ {W} {U} {Y}
                C.∘ (C.id {W} C.⊗₁ C.σ⇒ {Y} {U} C.∘ C.α⇒ {W} {Y} {U})
                  C.∘ (C.α⇐ {W} {Y} {U} C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y})
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ C.α⇐ {W} {U} {Y}
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {Y} {U}
                C.∘ C.α⇒ {W} {Y} {U} C.∘ C.α⇐ {W} {Y} {U} C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoʳ ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ C.α⇐ {W} {U} {Y}
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {Y} {U}
                C.∘ C.id {W} C.⊗₁ C.σ⇒ {U} {Y}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ id⊗-merge ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ C.α⇐ {W} {U} {Y}
                C.∘ C.id {W} C.⊗₁ (C.σ⇒ {Y} {U} C.∘ C.σ⇒ {U} {Y})
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.commutative) ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y}
                C.∘ C.α⇐ {W} {U} {Y}
                C.∘ C.id {W} C.⊗₁ C.id {U C.⊗₀ Y}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.identity C.⊗ ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ C.α⇐ {W} {U} {Y} C.∘ C.id
                ≈⟨ refl⟩∘⟨ C.identityʳ ⟩
              C.σ⇒ {W} {U} C.⊗₁ C.id {Y} C.∘ C.α⇐ {W} {U} {Y}
              ∎


        -- ── small chain helpers: apply an n-ary equation before a tail ───

        pull₃ : ∀ {A B D E F : C.Obj}
          {a : E C.⇒ F} {b : D C.⇒ E} {c : B C.⇒ D} {d : B C.⇒ F} {f : A C.⇒ B} →
          a C.∘ b C.∘ c C.≈ d → a C.∘ b C.∘ c C.∘ f C.≈ d C.∘ f
        pull₃ eq = C.Equiv.trans (C.∘-resp-≈ʳ C.sym-assoc) (pullˡ eq)


        pull₄ : ∀ {A B D E F G : C.Obj}
          {a : F C.⇒ G} {b : E C.⇒ F} {c : D C.⇒ E} {d : B C.⇒ D} {e : B C.⇒ G} {f : A C.⇒ B} →
          a C.∘ b C.∘ c C.∘ d C.≈ e → a C.∘ b C.∘ c C.∘ d C.∘ f C.≈ e C.∘ f
        pull₄ eq = C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc)) (pull₃ eq)


        pull₅ : ∀ {A B D E F G H : C.Obj}
          {a : G C.⇒ H} {b : F C.⇒ G} {c : E C.⇒ F} {d : D C.⇒ E} {e : B C.⇒ D} {g : B C.⇒ H}
          {f : A C.⇒ B} →
          a C.∘ b C.∘ c C.∘ d C.∘ e C.≈ g → a C.∘ b C.∘ c C.∘ d C.∘ e C.∘ f C.≈ g C.∘ f
        pull₅ eq = C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc))) (pull₄ eq)


        pull₆ : ∀ {A B D E F G H I : C.Obj}
          {a : H C.⇒ I} {b : G C.⇒ H} {c : F C.⇒ G} {d : E C.⇒ F} {e : D C.⇒ E} {g : B C.⇒ D}
          {h : B C.⇒ I} {f : A C.⇒ B} →
          a C.∘ b C.∘ c C.∘ d C.∘ e C.∘ g C.≈ h → a C.∘ b C.∘ c C.∘ d C.∘ e C.∘ g C.∘ f C.≈ h C.∘ f
        pull₆ eq = C.Equiv.trans
          (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc)))) (pull₅ eq)


        -- α composed with the canonical reassociation, in θ form
        α-θ-cancel : ∀ {W X Y Z : C.Obj} →
          α {W} {X} {Y} {Z} C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X}
          C.≈ C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ θ {Y} {Z} {W} C.⊗₁ C.id {X}
        α-θ-cancel {W} {X} {Y} {Z} = begin
          α {W} {X} {Y} {Z} C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ α-θ ⟩∘⟨refl ⟩
          (C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ θ {Y} {Z} {W} C.⊗₁ C.id {X} C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X})
            C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ C.assoc ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X}
            C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X} C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}) C.∘ C.α⇒ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ cancelʳ C.associator.isoˡ ⟩
          C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ θ {Y} {Z} {W} C.⊗₁ C.id {X}
          ∎


        -- the defining dance of θ, transported under a left spectator A
        θ-frame : ∀ {A X V Y : C.Obj} →
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
          C.∘ β {A C.⊗₀ Y} {X} {V}
          C.∘ C.α⇐ {A} {Y} {X} C.⊗₁ C.id {V}
          C.∘ (C.id {A} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {V}
          C.∘ C.α⇒ {A} {X} {Y} C.⊗₁ C.id {V}
          C.∘ β {A C.⊗₀ X} {V} {Y}
          C.≈ C.α⇐ {A} {Y C.⊗₀ V} {X}
              C.∘ C.id {A} C.⊗₁ θ {X} {V} {Y}
              C.∘ C.α⇒ {A} {X C.⊗₀ V} {Y}
              C.∘ C.α⇒ {A} {X} {V} C.⊗₁ C.id {Y}
        θ-frame {A} {X} {V} {Y} = begin
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ β {A C.⊗₀ Y} {X} {V}
            C.∘ C.α⇐ {A} {Y} {X} C.⊗₁ C.id {V}
            C.∘ (C.id {A} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {V}
            C.∘ C.α⇒ {A} {X} {Y} C.⊗₁ C.id {V}
            C.∘ β {A C.⊗₀ X} {V} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ β {A C.⊗₀ Y} {X} {V}
            C.∘ (C.α⇐ {A} {Y} {X} C.∘ C.id {A} C.⊗₁ C.σ⇒ {X} {Y}) C.⊗₁ C.id {V}
            C.∘ C.α⇒ {A} {X} {Y} C.⊗₁ C.id {V}
            C.∘ β {A C.⊗₀ X} {V} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ β {A C.⊗₀ Y} {X} {V}
            C.∘ ((C.α⇐ {A} {Y} {X} C.∘ C.id {A} C.⊗₁ C.σ⇒ {X} {Y}) C.∘ C.α⇒ {A} {X} {Y}) C.⊗₁ C.id {V}
            C.∘ β {A C.⊗₀ X} {V} {Y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ β {A C.⊗₀ Y} {X} {V}
            C.∘ β {A} {X} {Y} C.⊗₁ C.id {V}
            C.∘ β {A C.⊗₀ X} {V} {Y}
            ≈⟨ refl⟩∘⟨ (β-extract ⟩∘⟨ (β⊗id-extract ⟩∘⟨ β-extract)) ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ (J⇐ {A} {Y} {V} {X} C.∘ C.id {A} C.⊗₁ β {Y} {X} {V} C.∘ J⇒ {A} {Y} {X} {V})
            C.∘ (J⇐ {A} {Y} {X} {V} C.∘ C.id {A} C.⊗₁ (C.σ⇒ {X} {Y} C.⊗₁ C.id {V}) C.∘ J⇒ {A} {X} {Y} {V})
            C.∘ (J⇐ {A} {X} {Y} {V} C.∘ C.id {A} C.⊗₁ β {X} {V} {Y} C.∘ J⇒ {A} {X} {V} {Y})
            ≈⟨ refl⟩∘⟨ conj3 ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ (J⇐ {A} {Y} {V} {X}
              C.∘ C.id {A} C.⊗₁ (β {Y} {X} {V} C.∘ C.σ⇒ {X} {Y} C.⊗₁ C.id {V} C.∘ β {X} {V} {Y})
              C.∘ J⇒ {A} {X} {V} {Y})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ C.α⇐ {A} {Y} {V} C.⊗₁ C.id {X}
            C.∘ C.α⇐ {A} {Y C.⊗₀ V} {X}
            C.∘ C.id {A} C.⊗₁ θ {X} {V} {Y}
            C.∘ J⇒ {A} {X} {V} {Y}
            ≈⟨ pullˡ α⇒α⇐⊗id ⟩
          C.id
            C.∘ C.α⇐ {A} {Y C.⊗₀ V} {X}
            C.∘ C.id {A} C.⊗₁ θ {X} {V} {Y}
            C.∘ J⇒ {A} {X} {V} {Y}
            ≈⟨ C.identityˡ ⟩
          C.α⇐ {A} {Y C.⊗₀ V} {X}
            C.∘ C.id {A} C.⊗₁ θ {X} {V} {Y}
            C.∘ C.α⇒ {A} {X C.⊗₀ V} {Y}
            C.∘ C.α⇒ {A} {X} {V} C.⊗₁ C.id {Y}
          ∎


        -- ── 5-wire core: coh-core with the inert pair-component z removed ─
        core₅ : ∀ {x w u v y : C.Obj} →
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
          C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
          C.∘ θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}
          C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y}
          C.≈ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
              C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
              C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
              C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y}
        core₅ {x} {w} {u} {v} {y} = begin
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
            C.∘ θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ β-split₂ ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
            C.∘ θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ C.α⇒ {(x C.⊗₀ w) C.⊗₀ y} {u} {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.Equiv.sym (Functor.identity C.⊗)) ⟩∘⟨refl ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
            C.∘ θ {x} {w} {y} C.⊗₁ (C.id {u} C.⊗₁ C.id {v})
            C.∘ C.α⇒ {(x C.⊗₀ w) C.⊗₀ y} {u} {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym C.assoc-commute-from) ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
            C.∘ (C.α⇒ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
              C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v})
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ pushˡ β-split₃ ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ C.α⇒ {y C.⊗₀ w} {u} {v} C.⊗₁ C.id {x}
            C.∘ (β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
              C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
              C.∘ C.α⇐ {(y C.⊗₀ w) C.⊗₀ x} {u} {v})
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ C.α⇒ {y C.⊗₀ w} {u} {v} C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ (β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v} C.∘ C.α⇐ {(y C.⊗₀ w) C.⊗₀ x} {u} {v})
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ C.α⇒ {y C.⊗₀ w} {u} {v} C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ C.α⇐ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ x} {u} {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoˡ ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x}
            C.∘ C.α⇒ {y C.⊗₀ w} {u} {v} C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ pullˡ ⊗id-merge ⟩
          (α {u} {v} {y} {w} C.∘ C.α⇒ {y C.⊗₀ w} {u} {v}) C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ Functor.F-resp-≈ C.⊗ (α-θ-cancel , C.Equiv.refl) ⟩∘⟨refl ⟩
          (C.α⇒ {u C.⊗₀ w} {y} {v} C.∘ θ {y} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ (θ {y} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {x}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ u} {x} {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym β-natural) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ (β {(u C.⊗₀ w) C.⊗₀ y} {x} {v} C.∘ (θ {y} {w} {u} C.⊗₁ C.id {x}) C.⊗₁ C.id {v})
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ (θ {y} {w} {u} C.⊗₁ C.id {x}) C.⊗₁ C.id {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u}) C.⊗₁ C.id {v}
            C.∘ β {x C.⊗₀ w} {u} {y} C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ (θ {y} {w} {u} C.⊗₁ C.id {x}) C.⊗₁ C.id {v}
            C.∘ β {y C.⊗₀ w} {x} {u} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u} C.∘ β {x C.⊗₀ w} {u} {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ (θ {y} {w} {u} C.⊗₁ C.id {x}) C.⊗₁ C.id {v}
            C.∘ (β {y C.⊗₀ w} {x} {u}
                  C.∘ θ {x} {w} {y} C.⊗₁ C.id {u} C.∘ β {x C.⊗₀ w} {u} {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ (θ {y} {w} {u} C.⊗₁ C.id {x}
                  C.∘ β {y C.⊗₀ w} {x} {u}
                  C.∘ θ {x} {w} {y} C.⊗₁ C.id {u}
                  C.∘ β {x C.⊗₀ w} {u} {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (θ-exch , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ (C.α⇐ {u C.⊗₀ w} {y} {x}
                  C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}
                  C.∘ C.α⇒ {u C.⊗₀ w} {x} {y}
                  C.∘ θ {x} {w} {u} C.⊗₁ C.id {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ C.α⇐ {u C.⊗₀ w} {y} {x} C.⊗₁ C.id {v}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}
                  C.∘ C.α⇒ {u C.⊗₀ w} {x} {y}
                  C.∘ θ {x} {w} {u} C.⊗₁ C.id {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ C.α⇐ {u C.⊗₀ w} {y} {x} C.⊗₁ C.id {v}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}) C.⊗₁ C.id {v}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x} {y} C.∘ θ {x} {w} {u} C.⊗₁ C.id {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ C.α⇐ {u C.⊗₀ w} {y} {x} C.⊗₁ C.id {v}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}) C.⊗₁ C.id {v}
            C.∘ C.α⇒ {u C.⊗₀ w} {x} {y} C.⊗₁ C.id {v}
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {y}) C.⊗₁ C.id {v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ u} {v} {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym β-natural) ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ C.α⇐ {u C.⊗₀ w} {y} {x} C.⊗₁ C.id {v}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}) C.⊗₁ C.id {v}
            C.∘ C.α⇒ {u C.⊗₀ w} {x} {y} C.⊗₁ C.id {v}
            C.∘ (β {(u C.⊗₀ w) C.⊗₀ x} {v} {y} C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y})
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {u C.⊗₀ w} {y} {v} C.⊗₁ C.id {x}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ y} {x} {v}
            C.∘ C.α⇐ {u C.⊗₀ w} {y} {x} C.⊗₁ C.id {v}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.σ⇒ {x} {y}) C.⊗₁ C.id {v}
            C.∘ C.α⇒ {u C.⊗₀ w} {x} {y} C.⊗₁ C.id {v}
            C.∘ β {(u C.⊗₀ w) C.⊗₀ x} {v} {y}
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ pull₆ θ-frame ⟩
          (C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x} {v} C.⊗₁ C.id {y})
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
              C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
              C.∘ C.α⇒ {u C.⊗₀ w} {x} {v} C.⊗₁ C.id {y})
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.∘ C.α⇒ {u C.⊗₀ w} {x} {v} C.⊗₁ C.id {y})
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x} {v} C.⊗₁ C.id {y}
            C.∘ (θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x} {v} C.∘ θ {x} {w} {u} C.⊗₁ C.id {v}) C.⊗₁ C.id {y}
            C.∘ C.α⇐ {x C.⊗₀ w} {u} {v} C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-merge ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ ((C.α⇒ {u C.⊗₀ w} {x} {v} C.∘ θ {x} {w} {u} C.⊗₁ C.id {v})
                  C.∘ C.α⇐ {x C.⊗₀ w} {u} {v}) C.⊗₁ C.id {y}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.assoc , C.Equiv.refl) ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x} {v}
                  C.∘ θ {x} {w} {u} C.⊗₁ C.id {v}
                  C.∘ C.α⇐ {x C.⊗₀ w} {u} {v}) C.⊗₁ C.id {y}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (α-θ , C.Equiv.refl) ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y}
          ∎


        -- γ with its rightmost braiding factor split off: γ ≈ α ∘ id ⊗ σ⇒
        γ-decomp : ∀ {P Q R S : C.Obj} →
          γ {P} {Q} {R} {S} C.≈ α {Q} {R} {P} {S} C.∘ C.id C.⊗₁ C.σ⇒ {R} {Q}
        γ-decomp =
          C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc))))
         (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc)))
         (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc))
         (C.Equiv.trans (C.∘-resp-≈ʳ C.sym-assoc) C.sym-assoc)))


        -- σ-free core of coh-pre, over six independent objects.
        coh-core : ∀ {x w u v y z : C.Obj} →
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
          C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
          C.∘ α {y} {z} {x} {w} C.⊗₁ C.id {u C.⊗₀ v}
          C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y C.⊗₀ z}
          C.≈ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
              C.∘ C.id {u C.⊗₀ w} C.⊗₁ α {y} {z} {x} {v}
              C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
              C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
        coh-core {x} {w} {u} {v} {y} {z} = begin
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ α {y} {z} {x} {w} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ β-split₃ ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ α {y} {z} {x} {w} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ C.α⇒ {x C.⊗₀ w} {y} {z} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ y} {u C.⊗₀ v} {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ (α {y} {z} {x} {w} C.∘ C.α⇒ {x C.⊗₀ w} {y} {z}) C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ y} {u C.⊗₀ v} {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (α-θ-cancel , C.Equiv.refl) ⟩∘⟨refl ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ (C.α⇒ {y C.⊗₀ w} {x} {z} C.∘ θ {x} {w} {y} C.⊗₁ C.id {z}) C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ y} {u C.⊗₀ v} {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {z}) C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {(x C.⊗₀ w) C.⊗₀ y} {u C.⊗₀ v} {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym β-natural) ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ (β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
              C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z})
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ β {y C.⊗₀ w} {x C.⊗₀ z} {u C.⊗₀ v}
            C.∘ C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ pushˡ β-split₂ ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ ((β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
              C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {z} {u C.⊗₀ v}
              C.∘ C.α⇐ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v})
            C.∘ (C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
              C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
              C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
              C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
              C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (β {(y C.⊗₀ w) C.⊗₀ x} {z} {u C.⊗₀ v}
              C.∘ C.α⇐ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v})
            C.∘ (C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
              C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
              C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
              C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
              C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {z} {u C.⊗₀ v}
            C.∘ (C.α⇐ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
              C.∘ (C.α⇒ {y C.⊗₀ w} {x} {z} C.⊗₁ C.id {u C.⊗₀ v}
                C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
                C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
                C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
                C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ α⇐α⇒⊗id ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {z} {u C.⊗₀ v}
            C.∘ β {(y C.⊗₀ w) C.⊗₀ x} {u C.⊗₀ v} {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ β-involutive ⟩
          α {u} {v} {y} {w} C.⊗₁ C.id {x C.⊗₀ z}
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.Equiv.sym (Functor.identity C.⊗)) ⟩∘⟨refl ⟩
          α {u} {v} {y} {w} C.⊗₁ (C.id {x} C.⊗₁ C.id {z})
            C.∘ C.α⇒ {(y C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {x} {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ pullˡ (C.Equiv.sym C.assoc-commute-from) ⟩
          (C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (α {u} {v} {y} {w} C.⊗₁ C.id {x}) C.⊗₁ C.id {z})
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ C.assoc ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (α {u} {v} {y} {w} C.⊗₁ C.id {x}) C.⊗₁ C.id {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}) C.⊗₁ C.id {z}
            C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (α {u} {v} {y} {w} C.⊗₁ C.id {x}) C.⊗₁ C.id {z}
            C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v} C.⊗₁ C.id {z}
            C.∘ (θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v} C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (α {u} {v} {y} {w} C.⊗₁ C.id {x}) C.⊗₁ C.id {z}
            C.∘ (β {y C.⊗₀ w} {x} {u C.⊗₀ v}
                  C.∘ θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}
                  C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (α {u} {v} {y} {w} C.⊗₁ C.id {x}
                  C.∘ β {y C.⊗₀ w} {x} {u C.⊗₀ v}
                  C.∘ θ {x} {w} {y} C.⊗₁ C.id {u C.⊗₀ v}
                  C.∘ β {x C.⊗₀ w} {u C.⊗₀ v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (core₅ , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ (C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x}
                  C.∘ C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
                  C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
                  C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x} C.⊗₁ C.id {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}
                  C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
                  C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x} C.⊗₁ C.id {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y}
                  C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x} C.⊗₁ C.id {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ (α {u} {v} {x} {w} C.⊗₁ C.id {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(x C.⊗₀ w) C.⊗₀ (u C.⊗₀ v)} {y} {z}
            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc-commute-to ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x} C.⊗₁ C.id {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ (C.id {y} C.⊗₁ C.id {z})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                 Functor.F-resp-≈ C.⊗ (C.Equiv.refl , Functor.identity C.⊗) ⟩
          C.α⇒ {(u C.⊗₀ w) C.⊗₀ (y C.⊗₀ v)} {x} {z}
            C.∘ C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x} C.⊗₁ C.id {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ pullˡ (C.Equiv.sym pent-frame₁') ⟩
          (C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {(y C.⊗₀ v) C.⊗₀ x} {z})
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
              C.∘ C.α⇒ {u C.⊗₀ w} {(y C.⊗₀ v) C.⊗₀ x} {z})
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {(y C.⊗₀ v) C.⊗₀ x} {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ θ {x} {v} {y}) C.⊗₁ C.id {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ C.assoc-commute-from ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ (C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
              C.∘ C.α⇒ {u C.⊗₀ w} {(x C.⊗₀ v) C.⊗₀ y} {z})
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
            C.∘ C.α⇒ {u C.⊗₀ w} {(x C.⊗₀ v) C.⊗₀ y} {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y} C.⊗₁ C.id {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pent-frame₅ ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
            C.∘ ((C.id {u C.⊗₀ w} C.⊗₁ C.α⇐ {x C.⊗₀ v} {y} {z}
              C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
              C.∘ C.α⇒ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z})
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇐ {x C.⊗₀ v} {y} {z}
            C.∘ (C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
              C.∘ C.α⇒ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z})
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇐ {x C.⊗₀ v} {y} {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
            C.∘ C.α⇒ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ C.α⇐ {(u C.⊗₀ w) C.⊗₀ (x C.⊗₀ v)} {y} {z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoʳ ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z})
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇐ {x C.⊗₀ v} {y} {z}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ C.α⇒ {y C.⊗₀ v} {x} {z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ (θ {x} {v} {y} C.⊗₁ C.id {z} C.∘ C.α⇐ {x C.⊗₀ v} {y} {z})
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈⟨ refl⟩∘⟨ pullˡ id⊗-merge ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁
                  (C.α⇒ {y C.⊗₀ v} {x} {z}
                    C.∘ θ {x} {v} {y} C.⊗₁ C.id {z} C.∘ C.α⇐ {x C.⊗₀ v} {y} {z})
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
            ≈˘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , α-θ) ⟩∘⟨refl ⟩
          C.α⇐ {u C.⊗₀ w} {y C.⊗₀ v} {x C.⊗₀ z}
            C.∘ C.id {u C.⊗₀ w} C.⊗₁ α {y} {z} {x} {v}
            C.∘ C.α⇒ {u C.⊗₀ w} {x C.⊗₀ v} {y C.⊗₀ z}
            C.∘ α {u} {v} {x} {w} C.⊗₁ C.id {y C.⊗₀ z}
          ∎

        coh-pre : ∀ {A⁺ E⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} →
          γ {B⁺} {D⁺} {D⁻} {E⁻} C.⊗₁ C.id {A⁺ C.⊗₀ B⁻}
          C.∘ β {B⁺ C.⊗₀ E⁻} {A⁺ C.⊗₀ B⁻} {D⁻ C.⊗₀ D⁺}
          C.∘ γ {A⁺} {B⁺} {B⁻} {E⁻} C.⊗₁ C.id {D⁻ C.⊗₀ D⁺}
          C.∘ β {A⁺ C.⊗₀ E⁻} {D⁻ C.⊗₀ D⁺} {B⁻ C.⊗₀ B⁺}
          C.≈ C.α⇐ {D⁺ C.⊗₀ E⁻} {B⁺ C.⊗₀ D⁻} {A⁺ C.⊗₀ B⁻}
              C.∘ C.id {D⁺ C.⊗₀ E⁻} C.⊗₁ γ {A⁺} {B⁺} {B⁻} {D⁻}
              C.∘ C.α⇒ {D⁺ C.⊗₀ E⁻} {A⁺ C.⊗₀ D⁻} {B⁻ C.⊗₀ B⁺}
              C.∘ γ {A⁺} {D⁺} {D⁻} {E⁻} C.⊗₁ C.id {B⁻ C.⊗₀ B⁺}
        coh-pre {x} {w} {y} {z} {u} {v} = begin
            γ {y} {u} {v} {w} C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {vu}
            C.∘ γ {x} {y} {z} {w} C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ Functor.F-resp-≈ C.⊗ (γ-decomp , C.Equiv.refl) ⟩∘⟨refl ⟩
            (χ₂ C.∘ C.id {yw} C.⊗₁ σD) C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {vu}
            C.∘ γ {x} {y} {z} {w} C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (γ-decomp , C.Equiv.refl) ⟩∘⟨refl ⟩
            (χ₂ C.∘ C.id {yw} C.⊗₁ σD) C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {vu}
            C.∘ (χ₁ C.∘ C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ (C.id {yw} C.⊗₁ σD) C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {vu}
            C.∘ (χ₁ C.∘ C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (C.Equiv.sym ⊗id-merge) ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ (C.id {yw} C.⊗₁ σD) C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {vu}
            C.∘ χ₁ C.⊗₁ C.id {vu}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ pullˡ (C.Equiv.sym β-natural) ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ (β {yw} {xz} {uv} C.∘ (C.id {yw} C.⊗₁ C.id {xz}) C.⊗₁ σD)
            C.∘ χ₁ C.⊗₁ C.id {vu}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl)) ⟩∘⟨refl ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ (β {yw} {xz} {uv} C.∘ C.id {yw C.⊗₀ xz} C.⊗₁ σD)
            C.∘ χ₁ C.⊗₁ C.id {vu}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ C.assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ C.id {yw C.⊗₀ xz} C.⊗₁ σD
            C.∘ χ₁ C.⊗₁ C.id {vu}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ swapD₁ ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ (χ₁ C.⊗₁ C.id {uv} C.∘ C.id {xw C.⊗₀ yz} C.⊗₁ σD)
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ C.id {xw C.⊗₀ yz} C.⊗₁ σD
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ swapDB ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ ((C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {uv} C.∘ C.id {xw C.⊗₀ zy} C.⊗₁ σD)
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {uv}
            C.∘ C.id {xw C.⊗₀ zy} C.⊗₁ σD
            C.∘ β {xw} {vu} {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushD ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {uv}
            C.∘ (β {xw} {uv} {zy} C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pushB ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ ((β {xw} {uv} {yz} C.∘ C.id {xw C.⊗₀ uv} C.⊗₁ σB) C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ χ₁ C.⊗₁ C.id {uv}
            C.∘ β {xw} {uv} {yz}
            C.∘ C.id {xw C.⊗₀ uv} C.⊗₁ σB
            C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ β {yw} {xz} {uv}
            C.∘ (χ₁ C.⊗₁ C.id {uv} C.∘ β {xw} {uv} {yz})
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
            χ₂ C.⊗₁ C.id {xz}
            C.∘ (β {yw} {xz} {uv} C.∘ (χ₁ C.⊗₁ C.id {uv} C.∘ β {xw} {uv} {yz}))
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ C.sym-assoc ⟩
            (χ₂ C.⊗₁ C.id {xz}
             C.∘ β {yw} {xz} {uv}
             C.∘ χ₁ C.⊗₁ C.id {uv}
             C.∘ β {xw} {uv} {yz})
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ coh-core ⟩∘⟨refl ⟩
            (C.α⇐ {uw} {yv} {xz}
             C.∘ C.id {uw} C.⊗₁ χ₃
             C.∘ C.α⇒ {uw} {xv} {yz}
             C.∘ χ₄ C.⊗₁ C.id {yz})
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ C.assoc ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ (C.id {uw} C.⊗₁ χ₃ C.∘ C.α⇒ {uw} {xv} {yz} C.∘ χ₄ C.⊗₁ C.id {yz})
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ C.assoc ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ (C.α⇒ {uw} {xv} {yz} C.∘ χ₄ C.⊗₁ C.id {yz})
            C.∘ (C.id {xw C.⊗₀ uv} C.⊗₁ σB C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ C.α⇒ {uw} {xv} {yz}
            C.∘ χ₄ C.⊗₁ C.id {yz}
            C.∘ C.id {xw C.⊗₀ uv} C.⊗₁ σB
            C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ swapB₄ ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ C.α⇒ {uw} {xv} {yz}
            C.∘ (C.id {uw C.⊗₀ xv} C.⊗₁ σB C.∘ χ₄ C.⊗₁ C.id {zy})
            C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ C.α⇒ {uw} {xv} {yz}
            C.∘ C.id {uw C.⊗₀ xv} C.⊗₁ σB
            C.∘ χ₄ C.⊗₁ C.id {zy}
            C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ mergeD₄ ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ C.α⇒ {uw} {xv} {yz}
            C.∘ C.id {uw C.⊗₀ xv} C.⊗₁ σB
            C.∘ γ {x} {u} {v} {w} C.⊗₁ C.id {zy}
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ pushB₃ ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ ((C.id {uw} C.⊗₁ (C.id {xv} C.⊗₁ σB) C.∘ C.α⇒ {uw} {xv} {zy})
                 C.∘ γ {x} {u} {v} {w} C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ χ₃
            C.∘ C.id {uw} C.⊗₁ (C.id {xv} C.⊗₁ σB)
            C.∘ (C.α⇒ {uw} {xv} {zy} C.∘ γ {x} {u} {v} {w} C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ pullˡ mergeB₃ ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ γ {x} {y} {z} {v}
            C.∘ (C.α⇒ {uw} {xv} {zy} C.∘ γ {x} {u} {v} {w} C.⊗₁ C.id {zy})
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.Equiv.refl ⟩
            C.α⇐ {uw} {yv} {xz}
            C.∘ C.id {uw} C.⊗₁ γ {x} {y} {z} {v}
            C.∘ C.α⇒ {uw} {xv} {zy}
            C.∘ γ {x} {u} {v} {w} C.⊗₁ C.id {zy}
          ∎
          where
            xw = x C.⊗₀ w
            yw = y C.⊗₀ w
            uw = u C.⊗₀ w
            xz = x C.⊗₀ z
            xv = x C.⊗₀ v
            yv = y C.⊗₀ v
            vu = v C.⊗₀ u
            uv = u C.⊗₀ v
            zy = z C.⊗₀ y
            yz = y C.⊗₀ z

            σB = C.σ⇒ {z} {y}
            σD = C.σ⇒ {v} {u}

            χ₁ = α {y} {z} {x} {w}
            χ₂ = α {u} {v} {y} {w}
            χ₃ = α {y} {z} {x} {v}
            χ₄ = α {u} {v} {x} {w}

            swapD₁ : C.id {yw C.⊗₀ xz} C.⊗₁ σD C.∘ χ₁ C.⊗₁ C.id {vu}
                     C.≈ χ₁ C.⊗₁ C.id {uv} C.∘ C.id {xw C.⊗₀ yz} C.⊗₁ σD
            swapD₁ = C.Equiv.trans (C.Equiv.sym serialize₂₁) serialize₁₂

            swapDB : C.id {xw C.⊗₀ yz} C.⊗₁ σD C.∘ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {vu}
                     C.≈ (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {uv} C.∘ C.id {xw C.⊗₀ zy} C.⊗₁ σD
            swapDB = C.Equiv.trans (C.Equiv.sym serialize₂₁) serialize₁₂

            pushD : C.id {xw C.⊗₀ zy} C.⊗₁ σD C.∘ β {xw} {vu} {zy}
                    C.≈ β {xw} {uv} {zy} C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
            pushD = C.Equiv.trans
              (C.∘-resp-≈ˡ (Functor.F-resp-≈ C.⊗ (C.Equiv.sym (Functor.identity C.⊗) , C.Equiv.refl)))
              (C.Equiv.sym β-natural)

            pushB : (C.id {xw} C.⊗₁ σB) C.⊗₁ C.id {uv} C.∘ β {xw} {uv} {zy}
                    C.≈ β {xw} {uv} {yz} C.∘ C.id {xw C.⊗₀ uv} C.⊗₁ σB
            pushB = C.Equiv.trans
              (C.Equiv.sym β-natural)
              (C.∘-resp-≈ʳ (Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl)))

            swapB₄ : χ₄ C.⊗₁ C.id {yz} C.∘ C.id {xw C.⊗₀ uv} C.⊗₁ σB
                     C.≈ C.id {uw C.⊗₀ xv} C.⊗₁ σB C.∘ χ₄ C.⊗₁ C.id {zy}
            swapB₄ = C.Equiv.trans (C.Equiv.sym serialize₁₂) serialize₂₁

            mergeD₄ : χ₄ C.⊗₁ C.id {zy} C.∘ (C.id {xw} C.⊗₁ σD) C.⊗₁ C.id {zy}
                      C.≈ γ {x} {u} {v} {w} C.⊗₁ C.id {zy}
            mergeD₄ = C.Equiv.trans ⊗id-merge
              (Functor.F-resp-≈ C.⊗ (C.Equiv.sym γ-decomp , C.Equiv.refl))

            pushB₃ : C.α⇒ {uw} {xv} {yz} C.∘ C.id {uw C.⊗₀ xv} C.⊗₁ σB
                     C.≈ C.id {uw} C.⊗₁ (C.id {xv} C.⊗₁ σB) C.∘ C.α⇒ {uw} {xv} {zy}
            pushB₃ = C.Equiv.trans
              (C.∘-resp-≈ʳ (Functor.F-resp-≈ C.⊗ (C.Equiv.sym (Functor.identity C.⊗) , C.Equiv.refl)))
              C.assoc-commute-from

            mergeB₃ : C.id {uw} C.⊗₁ χ₃ C.∘ C.id {uw} C.⊗₁ (C.id {xv} C.⊗₁ σB)
                      C.≈ C.id {uw} C.⊗₁ γ {x} {y} {z} {v}
            mergeB₃ = C.Equiv.trans id⊗-merge
              (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.Equiv.sym γ-decomp))


        -- ── Involutivity of θ and α, and the inverse-transport proof of coh-post ──

        -- θ is involutive
        θ-invol : ∀ {P Q R : C.Obj} → θ {R} {Q} {P} C.∘ θ {P} {Q} {R} C.≈ C.id
        θ-invol {P} {Q} {R} = begin
          (β {P} {R} {Q} C.∘ C.σ⇒ {R} {P} C.⊗₁ C.id {Q} C.∘ β {R} {Q} {P})
            C.∘ (β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R})
            ≈⟨ C.assoc ⟩
          β {P} {R} {Q} C.∘ (C.σ⇒ {R} {P} C.⊗₁ C.id {Q} C.∘ β {R} {Q} {P})
            C.∘ (β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          β {P} {R} {Q} C.∘ C.σ⇒ {R} {P} C.⊗₁ C.id {Q}
            C.∘ β {R} {Q} {P} C.∘ (β {R} {P} {Q} C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ (β-involutive {R} {Q} {P}) ⟩
          β {P} {R} {Q} C.∘ C.σ⇒ {R} {P} C.⊗₁ C.id {Q}
            C.∘ C.σ⇒ {P} {R} C.⊗₁ C.id {Q} C.∘ β {P} {Q} {R}
            ≈⟨ refl⟩∘⟨ pullˡ (σσ⊗id {P} {R} {Q}) ⟩
          β {P} {R} {Q} C.∘ C.id C.∘ β {P} {Q} {R}
            ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
          β {P} {R} {Q} C.∘ β {P} {Q} {R}
            ≈⟨ β-involutive {P} {R} {Q} ⟩
          C.id
          ∎


        -- α is involutive
        α-invol : ∀ {W X Y Z : C.Obj} →
          α {Y} {X} {W} {Z} C.∘ α {W} {X} {Y} {Z} C.≈ C.id
        α-invol {W} {X} {Y} {Z} = begin
          α {Y} {X} {W} {Z} C.∘ α {W} {X} {Y} {Z}
            ≈⟨ α-θ {Y} {X} {W} {Z} ⟩∘⟨ α-θ {W} {X} {Y} {Z} ⟩
          (C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ (θ {W} {Z} {Y} C.⊗₁ C.id {X}) C.∘ C.α⇐ {W C.⊗₀ Z} {Y} {X})
            C.∘ (C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X})
            ≈⟨ C.assoc ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ ((θ {W} {Z} {Y} C.⊗₁ C.id {X}) C.∘ C.α⇐ {W C.⊗₀ Z} {Y} {X})
            C.∘ (C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X})
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ (θ {W} {Z} {Y} C.⊗₁ C.id {X})
            C.∘ C.α⇐ {W C.⊗₀ Z} {Y} {X}
            C.∘ (C.α⇒ {W C.⊗₀ Z} {Y} {X} C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X})
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoˡ ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ (θ {W} {Z} {Y} C.⊗₁ C.id {X})
            C.∘ (θ {Y} {Z} {W} C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ ((θ {W} {Z} {Y} C.∘ θ {Y} {Z} {W}) C.⊗₁ C.id {X}) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (θ-invol {Y} {Z} {W} , C.Equiv.refl) ⟩∘⟨refl ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ (C.id C.⊗₁ C.id) C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ Functor.identity C.⊗ ⟩∘⟨refl ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ C.id C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
          C.α⇒ {Y C.⊗₀ Z} {W} {X} C.∘ C.α⇐ {Y C.⊗₀ Z} {W} {X}
            ≈⟨ C.associator.isoʳ ⟩
          C.id
          ∎


        -- (u ⊗ id) ∘ (v ⊗ id) ≈ id from u ∘ v ≈ id
        ⊗id-cancel : ∀ {X Y Z : C.Obj} {u : Y C.⇒ X} {v : X C.⇒ Y} →
          u C.∘ v C.≈ C.id → u C.⊗₁ C.id {Z} C.∘ v C.⊗₁ C.id C.≈ C.id
        ⊗id-cancel uv = C.Equiv.trans ⊗id-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (uv , C.Equiv.refl)) (Functor.identity C.⊗))


        -- (id ⊗ u) ∘ (id ⊗ v) ≈ id from u ∘ v ≈ id
        id⊗-cancel : ∀ {X Y Z : C.Obj} {u : Y C.⇒ X} {v : X C.⇒ Y} →
          u C.∘ v C.≈ C.id → C.id {Z} C.⊗₁ u C.∘ C.id C.⊗₁ v C.≈ C.id
        id⊗-cancel uv = C.Equiv.trans id⊗-merge
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , uv)) (Functor.identity C.⊗))


        -- a 4-chain composed with the reversed chain of its inverses is the identity
        cancel4 : ∀ {V₀ V₁ V₂ V₃ V₄ : C.Obj}
          {i : V₀ C.⇒ V₁} {h : V₁ C.⇒ V₂} {g : V₂ C.⇒ V₃} {f : V₃ C.⇒ V₄}
          {i' : V₁ C.⇒ V₀} {h' : V₂ C.⇒ V₁} {g' : V₃ C.⇒ V₂} {f' : V₄ C.⇒ V₃} →
          f' C.∘ f C.≈ C.id → g' C.∘ g C.≈ C.id →
          h' C.∘ h C.≈ C.id → i' C.∘ i C.≈ C.id →
          (i' C.∘ h' C.∘ g' C.∘ f') C.∘ (f C.∘ g C.∘ h C.∘ i) C.≈ C.id
        cancel4 {i = i} {h} {g} {f} {i'} {h'} {g'} {f'} ff gg hh ii = begin
          (i' C.∘ h' C.∘ g' C.∘ f') C.∘ (f C.∘ g C.∘ h C.∘ i)
            ≈⟨ C.assoc ⟩
          i' C.∘ ((h' C.∘ g' C.∘ f') C.∘ (f C.∘ g C.∘ h C.∘ i))
            ≈⟨ refl⟩∘⟨ C.assoc ⟩
          i' C.∘ h' C.∘ ((g' C.∘ f') C.∘ (f C.∘ g C.∘ h C.∘ i))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
          i' C.∘ h' C.∘ g' C.∘ (f' C.∘ (f C.∘ g C.∘ h C.∘ i))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ ff ⟩
          i' C.∘ h' C.∘ g' C.∘ (g C.∘ h C.∘ i)
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ gg ⟩
          i' C.∘ h' C.∘ (h C.∘ i)
            ≈⟨ refl⟩∘⟨ cancelˡ hh ⟩
          i' C.∘ i
            ≈⟨ ii ⟩
          C.id
          ∎

        coh-post : ∀ {A⁻ E⁺ B⁺ B⁻ D⁺ D⁻ : C.Obj} →
          β {A⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ B⁺} {D⁻ C.⊗₀ D⁺}
          C.∘ α {A⁻} {B⁺} {B⁻} {E⁺} C.⊗₁ C.id {D⁻ C.⊗₀ D⁺}
          C.∘ β {B⁻ C.⊗₀ E⁺} {D⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺}
          C.∘ α {B⁻} {D⁺} {D⁻} {E⁺} C.⊗₁ C.id {A⁻ C.⊗₀ B⁺}
          C.≈ α {A⁻} {D⁺} {D⁻} {E⁺} C.⊗₁ C.id {B⁻ C.⊗₀ B⁺}
              C.∘ C.α⇐ {D⁻ C.⊗₀ E⁺} {A⁻ C.⊗₀ D⁺} {B⁻ C.⊗₀ B⁺}
              C.∘ C.id {D⁻ C.⊗₀ E⁺} C.⊗₁ α {A⁻} {B⁺} {B⁻} {D⁺}
              C.∘ C.α⇒ {D⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺}
        coh-post {A⁻} {E⁺} {B⁺} {B⁻} {D⁺} {D⁻} =
          C.Equiv.trans (insertʳ rhs-cancel)
         (C.Equiv.trans (C.∘-resp-≈ˡ (C.∘-resp-≈ʳ (C.Equiv.sym (coh-core {A⁻} {E⁺} {D⁻} {D⁺} {B⁻} {B⁺}))))
         (C.Equiv.trans (C.∘-resp-≈ˡ lhs-cancel) C.identityˡ))
          where
            -- coh-post's LHS is the inverse of coh-core's LHS
            lhs-cancel :
              (β {A⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ B⁺} {D⁻ C.⊗₀ D⁺}
                C.∘ α {A⁻} {B⁺} {B⁻} {E⁺} C.⊗₁ C.id {D⁻ C.⊗₀ D⁺}
                C.∘ β {B⁻ C.⊗₀ E⁺} {D⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺}
                C.∘ α {B⁻} {D⁺} {D⁻} {E⁺} C.⊗₁ C.id {A⁻ C.⊗₀ B⁺})
              C.∘ (α {D⁻} {D⁺} {B⁻} {E⁺} C.⊗₁ C.id {A⁻ C.⊗₀ B⁺}
                C.∘ β {B⁻ C.⊗₀ E⁺} {A⁻ C.⊗₀ B⁺} {D⁻ C.⊗₀ D⁺}
                C.∘ α {B⁻} {B⁺} {A⁻} {E⁺} C.⊗₁ C.id {D⁻ C.⊗₀ D⁺}
                C.∘ β {A⁻ C.⊗₀ E⁺} {D⁻ C.⊗₀ D⁺} {B⁻ C.⊗₀ B⁺})
              C.≈ C.id
            lhs-cancel = cancel4
              (⊗id-cancel (α-invol {D⁻} {D⁺} {B⁻} {E⁺}))
              (β-involutive {B⁻ C.⊗₀ E⁺} {D⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺})
              (⊗id-cancel (α-invol {B⁻} {B⁺} {A⁻} {E⁺}))
              (β-involutive {A⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ B⁺} {D⁻ C.⊗₀ D⁺})

            -- coh-post's RHS is the inverse of coh-core's RHS
            rhs-cancel :
              (C.α⇐ {D⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺}
                C.∘ C.id {D⁻ C.⊗₀ E⁺} C.⊗₁ α {B⁻} {B⁺} {A⁻} {D⁺}
                C.∘ C.α⇒ {D⁻ C.⊗₀ E⁺} {A⁻ C.⊗₀ D⁺} {B⁻ C.⊗₀ B⁺}
                C.∘ α {D⁻} {D⁺} {A⁻} {E⁺} C.⊗₁ C.id {B⁻ C.⊗₀ B⁺})
              C.∘ (α {A⁻} {D⁺} {D⁻} {E⁺} C.⊗₁ C.id {B⁻ C.⊗₀ B⁺}
                C.∘ C.α⇐ {D⁻ C.⊗₀ E⁺} {A⁻ C.⊗₀ D⁺} {B⁻ C.⊗₀ B⁺}
                C.∘ C.id {D⁻ C.⊗₀ E⁺} C.⊗₁ α {A⁻} {B⁺} {B⁻} {D⁺}
                C.∘ C.α⇒ {D⁻ C.⊗₀ E⁺} {B⁻ C.⊗₀ D⁺} {A⁻ C.⊗₀ B⁺})
              C.≈ C.id
            rhs-cancel = cancel4
              (⊗id-cancel (α-invol {A⁻} {D⁺} {D⁻} {E⁺}))
              C.associator.isoʳ
              (id⊗-cancel (α-invol {A⁻} {B⁺} {B⁻} {D⁺}))
              C.associator.isoˡ

        -- identityˡ: id ∘G f ≈ f, i.e. trace(α ∘ σ⇒ ⊗₁ f ∘ γ) ≈ f
        --
        -- Wire calculus: α ∘ σ⇒ ⊗₁ f ∘ γ sends ((a , b) , (c , d)) to
        -- ((f₁(a,c) , d) , (b , f₂(a,c))).  Split the trace over B⁻ ⊗ B⁺
        -- with vanishing₂; after the coherence rewrite Ψ-decomp, the inner
        -- B⁺-loop and the outer B⁻-loop are both β-shaped and collapse via
        -- trace-β, leaving exactly f.
        identityˡ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.≈ f
        identityˡ' {A⁺ , A⁻} {B⁺ , B⁻} {f} = begin
            C.trace (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ)
          ≈˘⟨ C.vanishing₂ {X = B⁻} {Y = B⁺} ⟩
            C.trace (C.trace (C.α⇐ C.∘ (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.∘ C.α⇒))
          ≈⟨ trace-resp-≈ (trace-resp-≈ Ψ-decomp) ⟩
            C.trace (C.trace (β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
              C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ n C.⊗₁ C.id {B⁺}))
          ≈˘⟨ trace-resp-≈ trace-∘ˡ ⟩
            C.trace (β {A⁻} {B⁻} {B⁺}
              C.∘ C.trace (β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ n C.⊗₁ C.id {B⁺}))
          ≈˘⟨ trace-resp-≈ (refl⟩∘⟨ trace-∘ʳ) ⟩
            C.trace (β {A⁻} {B⁻} {B⁺} C.∘ C.trace (β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺}) C.∘ n)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ trace-β ⟩∘⟨refl) ⟩
            C.trace (β {A⁻} {B⁻} {B⁺} C.∘ C.id C.∘ n)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.identityˡ) ⟩
            C.trace (β {A⁻} {B⁻} {B⁺} C.∘ n)
          ≈⟨ trace-resp-≈ β∘n-reduce ⟩
            C.trace (f C.⊗₁ C.id {B⁻} C.∘ β {A⁺} {B⁻} {B⁻})
          ≈˘⟨ trace-∘ˡ ⟩
            f C.∘ C.trace (β {A⁺} {B⁻} {B⁻})
          ≈⟨ refl⟩∘⟨ trace-β ⟩
            f C.∘ C.id
          ≈⟨ C.identityʳ ⟩
            f
          ∎
          where
            n : (A⁺ C.⊗₀ B⁻) C.⊗₀ B⁻ C.⇒ (A⁻ C.⊗₀ B⁻) C.⊗₀ B⁺
            n = (β {A⁻} {B⁺} {B⁻} C.∘ f C.⊗₁ C.id {B⁻}) C.∘ β {A⁺} {B⁻} {B⁻}

            δ : ((A⁺ C.⊗₀ B⁻) C.⊗₀ B⁻) C.⊗₀ B⁺ C.⇒ (B⁺ C.⊗₀ B⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)
            δ = C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

            δ' : ((A⁻ C.⊗₀ B⁺) C.⊗₀ B⁻) C.⊗₀ B⁺ C.⇒ (B⁺ C.⊗₀ B⁻) C.⊗₀ (A⁻ C.⊗₀ B⁺)
            δ' = C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

            β∘n-reduce : β {A⁻} {B⁻} {B⁺} C.∘ n C.≈ f C.⊗₁ C.id {B⁻} C.∘ β {A⁺} {B⁻} {B⁻}
            β∘n-reduce = begin
              β C.∘ (β C.∘ f C.⊗₁ C.id) C.∘ β
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              β C.∘ β C.∘ f C.⊗₁ C.id C.∘ β
                ≈⟨ pullˡ β-involutive ⟩
              C.id C.∘ f C.⊗₁ C.id C.∘ β
                ≈⟨ C.identityˡ ⟩
              f C.⊗₁ C.id C.∘ β
              ∎

            -- slide f through δ (braiding naturality + interchange +
            -- associator naturality)
            f-slide : C.id C.⊗₁ f C.∘ δ C.≈ δ' C.∘ (f C.⊗₁ C.id {B⁻}) C.⊗₁ C.id {B⁺}
            f-slide = begin
              C.id C.⊗₁ f C.∘ C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
                ≈⟨ pullˡ (C.Equiv.sym (C.braiding.⇒.commute (f , C.id))) ⟩
              (C.σ⇒ C.∘ f C.⊗₁ C.id) C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
                ≈⟨ C.assoc ⟩
              C.σ⇒ C.∘ f C.⊗₁ C.id C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ pullˡ (C.Equiv.trans (C.Equiv.sym serialize₁₂) serialize₂₁) ⟩
              C.σ⇒ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ f C.⊗₁ C.id) C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ f C.⊗₁ C.id C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ f-bridge ⟩
              C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.σ⇒ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                ≈⟨ C.sym-assoc ⟩
              (C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
              ∎
              where
                f-bridge : f C.⊗₁ C.id C.∘ C.α⇒
                           C.≈ C.α⇒ C.∘ (f C.⊗₁ C.id {B⁻}) C.⊗₁ C.id {B⁺}
                f-bridge = begin
                  f C.⊗₁ C.id C.∘ C.α⇒
                    ≈˘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , Functor.identity C.⊗) ⟩∘⟨refl ⟩
                  f C.⊗₁ (C.id C.⊗₁ C.id) C.∘ C.α⇒
                    ≈˘⟨ C.assoc-commute-from ⟩
                  C.α⇒ C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                  ∎

            Ψ-decomp :
              C.α⇐ C.∘ (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.∘ C.α⇒
              C.≈ β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                  C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ n C.⊗₁ C.id {B⁺}
            Ψ-decomp = begin
              C.α⇐ C.∘ (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ (C.σ⇒ C.⊗₁ f C.∘ γ) C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
              C.α⇐ C.∘ α C.∘ (C.σ⇒ C.⊗₁ C.id C.∘ C.id C.⊗₁ f) C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.id C.⊗₁ f C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coh-sub1ˡ {A⁺} {B⁻} {B⁻} {B⁺} ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.id C.⊗₁ f
                C.∘ C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒ C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.id C.⊗₁ f
                C.∘ C.σ⇒ C.∘ (C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.id C.⊗₁ f
                C.∘ (C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒) C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id
                C.∘ (C.id C.⊗₁ f C.∘ (C.σ⇒ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒)) C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ f-slide ⟩∘⟨refl ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id
                C.∘ (δ' C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id) C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id
                C.∘ δ' C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ α C.∘ (C.σ⇒ C.⊗₁ C.id C.∘ δ')
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ (α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ δ')
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ C.sym-assoc ⟩
              (C.α⇐ C.∘ α C.∘ C.σ⇒ C.⊗₁ C.id C.∘ δ')
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ coh-sub2ˡ {A⁻} {B⁺} {B⁻} {B⁺} ⟩∘⟨refl ⟩
              (β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ β {A⁻} {B⁺} {B⁻} C.⊗₁ C.id {B⁺})
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ C.assoc ⟩
              β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                C.∘ (β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ β {A⁻} {B⁺} {B⁻} C.⊗₁ C.id {B⁺})
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺}
                C.∘ β {A⁻} {B⁺} {B⁻} C.⊗₁ C.id {B⁺}
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ⊗id-merge ⟩
              β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺}
                C.∘ (β {A⁻} {B⁺} {B⁻} C.∘ f C.⊗₁ C.id) C.⊗₁ C.id C.∘ β C.⊗₁ C.id
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-merge ⟩
              β {A⁻} {B⁻} {B⁺} C.⊗₁ C.id {B⁺}
                C.∘ β {A⁻ C.⊗₀ B⁻} {B⁺} {B⁺} C.∘ n C.⊗₁ C.id {B⁺}
              ∎

        -- identityʳ: f ∘G id ≈ f, i.e. trace(α ∘ f ⊗₁ σ⇒ ∘ γ) ≈ f
        --
        -- Mirror image of identityˡ': here the trace is over A⁻ ⊗ A⁺, the
        -- A⁺-input passes through the inner loop and f's A⁻-output through
        -- the outer one.
        identityʳ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.≈ f
        identityʳ' {A⁺ , A⁻} {B⁺ , B⁻} {f} = begin
            C.trace (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ)
          ≈˘⟨ C.vanishing₂ {X = A⁻} {Y = A⁺} ⟩
            C.trace (C.trace (C.α⇐ C.∘ (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.∘ C.α⇒))
          ≈⟨ trace-resp-≈ (trace-resp-≈ Ψʳ-decomp) ⟩
            C.trace (C.trace (n' C.⊗₁ C.id {A⁺}
              C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺} C.∘ r₀ C.⊗₁ C.id {A⁺}))
          ≈˘⟨ trace-resp-≈ trace-∘ˡ ⟩
            C.trace (n' C.∘ C.trace (β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺} C.∘ r₀ C.⊗₁ C.id {A⁺}))
          ≈˘⟨ trace-resp-≈ (refl⟩∘⟨ trace-∘ʳ) ⟩
            C.trace (n' C.∘ C.trace (β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}) C.∘ r₀)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ trace-β ⟩∘⟨refl) ⟩
            C.trace (n' C.∘ C.id C.∘ r₀)
          ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.identityˡ) ⟩
            C.trace (n' C.∘ r₀)
          ≈⟨ trace-resp-≈ n'r₀-reduce ⟩
            C.trace ((s₂' C.∘ f C.⊗₁ C.id {A⁻}))
          ≈⟨ trace-resp-≈ C.Equiv.refl ⟩
            C.trace (s₂' C.∘ f C.⊗₁ C.id {A⁻})
          ≈˘⟨ trace-∘ʳ ⟩
            C.trace s₂' C.∘ f
          ≈⟨ s₂'-trace ⟩∘⟨refl ⟩
            C.id C.∘ f
          ≈⟨ C.identityˡ ⟩
            f
          ∎
          where
            r₀ : (A⁺ C.⊗₀ B⁻) C.⊗₀ A⁻ C.⇒ (B⁻ C.⊗₀ A⁻) C.⊗₀ A⁺
            r₀ = C.σ⇒ C.∘ C.α⇒

            s₁' : (B⁻ C.⊗₀ A⁻) C.⊗₀ A⁺ C.⇒ (A⁺ C.⊗₀ B⁻) C.⊗₀ A⁻
            s₁' = C.α⇐ C.∘ C.σ⇒

            s₂' : (A⁻ C.⊗₀ B⁺) C.⊗₀ A⁻ C.⇒ (A⁻ C.⊗₀ B⁺) C.⊗₀ A⁻
            s₂' = β {A⁻} {A⁻} {B⁺} C.∘ C.σ⇒ {A⁻} {A⁻} C.⊗₁ C.id {B⁺} C.∘ β {A⁻} {B⁺} {A⁻}

            n' : (B⁻ C.⊗₀ A⁻) C.⊗₀ A⁺ C.⇒ (A⁻ C.⊗₀ B⁺) C.⊗₀ A⁻
            n' = (s₂' C.∘ f C.⊗₁ C.id {A⁻}) C.∘ s₁'

            s₁'r₀-cancel : s₁' C.∘ r₀ C.≈ C.id
            s₁'r₀-cancel = begin
              (C.α⇐ C.∘ C.σ⇒) C.∘ C.σ⇒ C.∘ C.α⇒
                ≈⟨ C.assoc ⟩
              C.α⇐ C.∘ C.σ⇒ C.∘ C.σ⇒ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ pullˡ C.commutative ⟩
              C.α⇐ C.∘ C.id C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
              C.α⇐ C.∘ C.α⇒
                ≈⟨ C.associator.isoˡ ⟩
              C.id
              ∎

            n'r₀-reduce : n' C.∘ r₀ C.≈ s₂' C.∘ f C.⊗₁ C.id {A⁻}
            n'r₀-reduce = begin
              ((s₂' C.∘ f C.⊗₁ C.id) C.∘ s₁') C.∘ r₀
                ≈⟨ C.assoc ⟩
              (s₂' C.∘ f C.⊗₁ C.id) C.∘ s₁' C.∘ r₀
                ≈⟨ refl⟩∘⟨ s₁'r₀-cancel ⟩
              (s₂' C.∘ f C.⊗₁ C.id) C.∘ C.id
                ≈⟨ C.identityʳ ⟩
              s₂' C.∘ f C.⊗₁ C.id
              ∎

            s₂'-trace : C.trace s₂' C.≈ C.id
            s₂'-trace = begin
              C.trace (β C.∘ C.σ⇒ {A⁻} {A⁻} C.⊗₁ C.id {B⁺} C.∘ β)
                ≈˘⟨ right-superposing ⟩
              C.trace (C.σ⇒ {A⁻} {A⁻}) C.⊗₁ C.id {B⁺}
                ≈⟨ Functor.F-resp-≈ C.⊗ (C.yanking , C.Equiv.refl) ⟩
              C.id {A⁻} C.⊗₁ C.id {B⁺}
                ≈⟨ Functor.identity C.⊗ ⟩
              C.id
              ∎

            f-bridgeʳ : f C.⊗₁ C.id
                        C.≈ C.α⇒ C.∘ (f C.⊗₁ C.id {A⁻}) C.⊗₁ C.id {A⁺} C.∘ C.α⇐
            f-bridgeʳ = begin
              f C.⊗₁ C.id
                ≈˘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , Functor.identity C.⊗) ⟩
              f C.⊗₁ (C.id C.⊗₁ C.id)
                ≈⟨ insertˡ C.associator.isoʳ ⟩
              C.α⇒ C.∘ C.α⇐ C.∘ f C.⊗₁ (C.id C.⊗₁ C.id)
                ≈⟨ refl⟩∘⟨ C.assoc-commute-to ⟩
              C.α⇒ C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ C.α⇐
              ∎

            Ψʳ-decomp :
              C.α⇐ C.∘ (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.∘ C.α⇒
              C.≈ n' C.⊗₁ C.id {A⁺}
                  C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺} C.∘ r₀ C.⊗₁ C.id {A⁺}
            Ψʳ-decomp = begin
              C.α⇐ C.∘ (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ (f C.⊗₁ C.σ⇒ C.∘ γ) C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
              C.α⇐ C.∘ α C.∘ (f C.⊗₁ C.id C.∘ C.id C.⊗₁ C.σ⇒) C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ f C.⊗₁ C.id C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ f-bridgeʳ ⟩∘⟨refl ⟩
              C.α⇐ C.∘ α C.∘ (C.α⇒ C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id C.∘ C.α⇐)
                C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ C.α⇒ C.∘ ((f C.⊗₁ C.id) C.⊗₁ C.id C.∘ C.α⇐)
                C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              C.α⇐ C.∘ α C.∘ C.α⇒ C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
              C.α⇐ C.∘ (α C.∘ C.α⇒) C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ C.sym-assoc ⟩
              (C.α⇐ C.∘ α C.∘ C.α⇒) C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                C.∘ C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ γ C.∘ C.α⇒
                ≈⟨ coh-sub2ʳ {A⁻} {B⁺} {A⁻} {A⁺} ⟩∘⟨
                     (refl⟩∘⟨ coh-sub1ʳ {A⁺} {B⁻} {A⁻} {A⁺}) ⟩
              (β {A⁻} {A⁻} {B⁺} C.∘ C.σ⇒ {A⁻} {A⁻} C.⊗₁ C.id {B⁺} C.∘ β {A⁻} {B⁺} {A⁻})
                C.⊗₁ C.id {A⁺}
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id
                C.∘ (C.α⇐ {A⁺} {B⁻} {A⁻} C.∘ C.σ⇒ {B⁻ C.⊗₀ A⁻} {A⁺}) C.⊗₁ C.id {A⁺}
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}
                C.∘ (C.σ⇒ {A⁺} {B⁻ C.⊗₀ A⁻} C.∘ C.α⇒ {A⁺} {B⁻} {A⁻}) C.⊗₁ C.id {A⁺}
                ≈⟨ C.sym-assoc ⟩
              ((β {A⁻} {A⁻} {B⁺} C.∘ C.σ⇒ {A⁻} {A⁻} C.⊗₁ C.id {B⁺} C.∘ β {A⁻} {B⁺} {A⁻})
                C.⊗₁ C.id {A⁺}
                C.∘ (f C.⊗₁ C.id) C.⊗₁ C.id)
                C.∘ (C.α⇐ {A⁺} {B⁻} {A⁻} C.∘ C.σ⇒ {B⁻ C.⊗₀ A⁻} {A⁺}) C.⊗₁ C.id {A⁺}
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}
                C.∘ (C.σ⇒ {A⁺} {B⁻ C.⊗₀ A⁻} C.∘ C.α⇒ {A⁺} {B⁻} {A⁻}) C.⊗₁ C.id {A⁺}
                ≈⟨ ⊗id-merge ⟩∘⟨refl ⟩
              (s₂' C.∘ f C.⊗₁ C.id) C.⊗₁ C.id {A⁺}
                C.∘ (C.α⇐ {A⁺} {B⁻} {A⁻} C.∘ C.σ⇒ {B⁻ C.⊗₀ A⁻} {A⁺}) C.⊗₁ C.id {A⁺}
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}
                C.∘ (C.σ⇒ {A⁺} {B⁻ C.⊗₀ A⁻} C.∘ C.α⇒ {A⁺} {B⁻} {A⁻}) C.⊗₁ C.id {A⁺}
                ≈⟨ C.sym-assoc ⟩
              ((s₂' C.∘ f C.⊗₁ C.id) C.⊗₁ C.id {A⁺}
                C.∘ (C.α⇐ {A⁺} {B⁻} {A⁻} C.∘ C.σ⇒ {B⁻ C.⊗₀ A⁻} {A⁺}) C.⊗₁ C.id {A⁺})
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}
                C.∘ (C.σ⇒ {A⁺} {B⁻ C.⊗₀ A⁻} C.∘ C.α⇒ {A⁺} {B⁻} {A⁻}) C.⊗₁ C.id {A⁺}
                ≈⟨ ⊗id-merge ⟩∘⟨refl ⟩
              n' C.⊗₁ C.id {A⁺}
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺}
                C.∘ (C.σ⇒ {A⁺} {B⁻ C.⊗₀ A⁻} C.∘ C.α⇒ {A⁺} {B⁻} {A⁻}) C.⊗₁ C.id {A⁺}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.Equiv.refl ⟩
              n' C.⊗₁ C.id {A⁺}
                C.∘ β {B⁻ C.⊗₀ A⁻} {A⁺} {A⁺} C.∘ r₀ C.⊗₁ C.id {A⁺}
              ∎

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
            -- 1. serialize: trace(m) ⊗₁ f → (trace(m) ⊗₁ id) ∘ (id ⊗₁ f)
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl) ⟩
          C.trace (α C.∘ (C.trace m C.⊗₁ C.id C.∘ C.id C.⊗₁ f) C.∘ γ)
            -- 2. reassociate
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.assoc) ⟩
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
            -- 10. reassociate
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.sym-assoc) ⟩
          C.trace (α C.∘ (C.id C.⊗₁ C.trace k C.∘ h C.⊗₁ C.id) C.∘ γ)
            -- 11. serialize⁻¹: (id ⊗₁ trace(k)) ∘ (h ⊗₁ id) → h ⊗₁ trace(k)
            ≈⟨ trace-resp-≈ (refl⟩∘⟨ C.Equiv.sym serialize₂₁ ⟩∘⟨refl) ⟩
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
            -- Proof: extract the three data morphisms by naturality of β,
            -- ⊗-functoriality and associator naturality, so that both sides
            -- become  POST ∘ (h' ⊗₁ g') ⊗₁ f' ∘ PRE  with POST and PRE
            -- structural; the box-free residuals are exactly coh-pre and
            -- coh-post.
            assoc'-coherence {A⁺} {A⁻'} {B⁺'} {B⁻'} {D⁺'} {D⁻'} {E⁺'} {E⁻'} f' g' h' = begin
              βt C.∘ (αL C.⊗₁ C.id {XD} C.∘ m₀'' C.∘ (C.id C.⊗₁ f' C.∘ γf) C.⊗₁ C.id {XD}) C.∘ β₀
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ (m₀'' C.∘ (C.id C.⊗₁ f' C.∘ γf) C.⊗₁ C.id {XD}) C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ m₀'' C.∘ (C.id C.⊗₁ f' C.∘ γf) C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ (m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'} C.∘ βm)
                C.∘ (C.id C.⊗₁ f' C.∘ γf) C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ βm C.∘ (C.id C.⊗₁ f' C.∘ γf) C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                     refl⟩∘⟨ C.Equiv.sym ⊗id-merge ⟩∘⟨refl ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ βm C.∘ ((C.id C.⊗₁ f') C.⊗₁ C.id {XD} C.∘ γf C.⊗₁ C.id {XD}) C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ βm C.∘ (C.id C.⊗₁ f') C.⊗₁ C.id {XD} C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ (βm C.∘ (C.id C.⊗₁ f') C.⊗₁ C.id {XD}) C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ slide-f' ⟩∘⟨refl ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ (C.id C.⊗₁ f' C.∘ βm') C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ C.id C.⊗₁ f' C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn
                C.∘ (m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'} C.∘ C.id C.⊗₁ f')
                C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge-L ⟩∘⟨refl ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn
                C.∘ (αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'} C.∘ (h' C.⊗₁ g') C.⊗₁ f' C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'})
                C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn
                C.∘ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ ((h' C.⊗₁ g') C.⊗₁ f' C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'})
                C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn
                C.∘ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'} C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              βt C.∘ αL C.⊗₁ C.id {XD}
                C.∘ (βn C.∘ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'} C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
              βt C.∘ (αL C.⊗₁ C.id {XD} C.∘ βn C.∘ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'} C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ C.sym-assoc ⟩
              (βt C.∘ αL C.⊗₁ C.id {XD} C.∘ βn C.∘ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'} C.∘ βm' C.∘ γf C.⊗₁ C.id {XD} C.∘ β₀
                ≈⟨ coh-post {A⁻'} {E⁺'} {B⁺'} {B⁻'} {D⁺'} {D⁻'} ⟩∘⟨
                     (refl⟩∘⟨ coh-pre {A⁺} {E⁻'} {B⁺'} {B⁻'} {D⁺'} {D⁻'}) ⟩
              (αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {B⁻' C.⊗₀ D⁺'} {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ (C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                  C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                  C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {B⁻' C.⊗₀ D⁺'} {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ (C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                  C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {B⁻' C.⊗₀ D⁺'} {A⁻' C.⊗₀ B⁺'})
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {B⁻' C.⊗₀ D⁺'} {A⁻' C.⊗₀ B⁺'}
                C.∘ (h' C.⊗₁ g') C.⊗₁ f'
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ (C.α⇒ {D⁻' C.⊗₀ E⁺'} {B⁻' C.⊗₀ D⁺'} {A⁻' C.⊗₀ B⁺'}
                  C.∘ (h' C.⊗₁ g') C.⊗₁ f')
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc-commute-from ⟩∘⟨refl ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ (h' C.⊗₁ (g' C.⊗₁ f')
                  C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'})
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ h' C.⊗₁ (g' C.⊗₁ f')
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.α⇐ {D⁺' C.⊗₀ E⁻'} {B⁺' C.⊗₀ D⁻'} {A⁺ C.⊗₀ B⁻'}
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ C.associator.isoʳ ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                C.∘ h' C.⊗₁ (g' C.⊗₁ f')
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ (C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk C.∘ h' C.⊗₁ (g' C.⊗₁ f'))
                C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ ((C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk C.∘ h' C.⊗₁ (g' C.⊗₁ f'))
                  C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf)
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩∘⟨refl ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ (C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                  C.∘ h' C.⊗₁ (g' C.⊗₁ f') C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf)
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ splitk ⟩∘⟨refl ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ (C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0 C.∘ h' C.⊗₁ C.id {(A⁺ C.⊗₀ D⁻') C.⊗₀ XB})
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                C.∘ h' C.⊗₁ C.id {(A⁺ C.⊗₀ D⁻') C.⊗₀ XB}
                C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                C.∘ (h' C.⊗₁ C.id {(A⁺ C.⊗₀ D⁻') C.⊗₀ XB}
                  C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB})
                C.∘ γh C.⊗₁ C.id {XB}
                ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ hbox ⟩∘⟨refl ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                C.∘ (C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB}
                  C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'}) C.⊗₁ C.id {XB})
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'}) C.⊗₁ C.id {XB}
                C.∘ γh C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-merge ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB}
                C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'} C.∘ γh) C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                C.∘ (C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0 C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB})
                C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'} C.∘ γh) C.⊗₁ C.id {XB}
                ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
              αR C.⊗₁ C.id {XB}
                C.∘ (C.α⇐ {D⁻' C.⊗₀ E⁺'} {A⁻' C.⊗₀ D⁺'} {XB}
                  C.∘ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0 C.∘ C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB})
                C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'} C.∘ γh) C.⊗₁ C.id {XB}
              ∎
              where
                XB = B⁻' C.⊗₀ B⁺'
                XD = D⁻' C.⊗₀ D⁺'

                γf  = γ {A⁺} {B⁺'} {B⁻'} {E⁻'}
                γh  = γ {A⁺} {D⁺'} {D⁻'} {E⁻'}
                γhg = γ {B⁺'} {D⁺'} {D⁻'} {E⁻'}
                γgf = γ {A⁺} {B⁺'} {B⁻'} {D⁻'}
                αm  = α {B⁻'} {D⁺'} {D⁻'} {E⁺'}
                αk  = α {A⁻'} {B⁺'} {B⁻'} {D⁺'}
                αL  = α {A⁻'} {B⁺'} {B⁻'} {E⁺'}
                αR  = α {A⁻'} {D⁺'} {D⁻'} {E⁺'}

                β₀  = β {A⁺ C.⊗₀ E⁻'} {XD} {XB}
                βm  = β {B⁺' C.⊗₀ E⁻'} {A⁻' C.⊗₀ B⁺'} {XD}
                βm' = β {B⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ B⁻'} {XD}
                βn  = β {B⁻' C.⊗₀ E⁺'} {XD} {A⁻' C.⊗₀ B⁺'}
                βt  = β {A⁻' C.⊗₀ E⁺'} {XB} {XD}

                m0 = αm C.∘ h' C.⊗₁ g' C.∘ γhg
                k0 = αk C.∘ g' C.⊗₁ f' C.∘ γgf
                m₀'' = βn C.∘ m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'} C.∘ βm

                -- β slides past a tensored morphism in its middle factor
                slide-f' : βm C.∘ (C.id C.⊗₁ f') C.⊗₁ C.id {XD}
                           C.≈ C.id C.⊗₁ f' C.∘ βm'
                slide-f' = begin
                  βm C.∘ (C.id C.⊗₁ f') C.⊗₁ C.id {XD}
                    ≈⟨ β-natural ⟩
                  (C.id C.⊗₁ C.id) C.⊗₁ f' C.∘ βm'
                    ≈⟨ Functor.F-resp-≈ C.⊗ (Functor.identity C.⊗ , C.Equiv.refl) ⟩∘⟨refl ⟩
                  C.id C.⊗₁ f' C.∘ βm'
                  ∎

                -- (m₀ ⊗ id) ∘ (id ⊗ f') ≈ (αm ⊗ id) ∘ (h'⊗g')⊗f' ∘ (γhg ⊗ id)
                merge-L : m0 C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'} C.∘ C.id C.⊗₁ f'
                          C.≈ αm C.⊗₁ C.id {A⁻' C.⊗₀ B⁺'}
                              C.∘ (h' C.⊗₁ g') C.⊗₁ f' C.∘ γhg C.⊗₁ C.id {A⁺ C.⊗₀ B⁻'}
                merge-L = begin
                  m0 C.⊗₁ C.id C.∘ C.id C.⊗₁ f'
                    ≈˘⟨ serialize₁₂ ⟩
                  m0 C.⊗₁ f'
                    ≈˘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.identityˡ) ⟩
                  m0 C.⊗₁ (C.id C.∘ f')
                    ≈⟨ Functor.homomorphism C.⊗ ⟩
                  αm C.⊗₁ C.id C.∘ (h' C.⊗₁ g' C.∘ γhg) C.⊗₁ f'
                    ≈˘⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.identityʳ) ⟩
                  αm C.⊗₁ C.id C.∘ (h' C.⊗₁ g' C.∘ γhg) C.⊗₁ (f' C.∘ C.id)
                    ≈⟨ refl⟩∘⟨ Functor.homomorphism C.⊗ ⟩
                  αm C.⊗₁ C.id C.∘ (h' C.⊗₁ g') C.⊗₁ f' C.∘ γhg C.⊗₁ C.id
                  ∎

                -- (id ⊗ αk) ∘ h'⊗(g'⊗f') ∘ (id ⊗ γgf) ≈ (id ⊗ k₀) ∘ (h' ⊗ id)
                splitk : C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ αk
                         C.∘ h' C.⊗₁ (g' C.⊗₁ f') C.∘ C.id {D⁺' C.⊗₀ E⁻'} C.⊗₁ γgf
                         C.≈ C.id {D⁻' C.⊗₀ E⁺'} C.⊗₁ k0
                             C.∘ h' C.⊗₁ C.id {(A⁺ C.⊗₀ D⁻') C.⊗₀ XB}
                splitk = begin
                  C.id C.⊗₁ αk C.∘ h' C.⊗₁ (g' C.⊗₁ f') C.∘ C.id C.⊗₁ γgf
                    ≈˘⟨ refl⟩∘⟨ Functor.homomorphism C.⊗ ⟩
                  C.id C.⊗₁ αk C.∘ (h' C.∘ C.id) C.⊗₁ ((g' C.⊗₁ f') C.∘ γgf)
                    ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ C.⊗ (C.identityʳ , C.Equiv.refl) ⟩
                  C.id C.⊗₁ αk C.∘ h' C.⊗₁ ((g' C.⊗₁ f') C.∘ γgf)
                    ≈˘⟨ Functor.homomorphism C.⊗ ⟩
                  (C.id C.∘ h') C.⊗₁ (αk C.∘ (g' C.⊗₁ f') C.∘ γgf)
                    ≈⟨ Functor.F-resp-≈ C.⊗ (C.identityˡ , C.Equiv.refl) ⟩
                  h' C.⊗₁ (αk C.∘ (g' C.⊗₁ f') C.∘ γgf)
                    ≈⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.sym C.identityˡ , C.Equiv.sym C.identityʳ) ⟩
                  (C.id C.∘ h') C.⊗₁ (k0 C.∘ C.id)
                    ≈⟨ Functor.homomorphism C.⊗ ⟩
                  C.id C.⊗₁ k0 C.∘ h' C.⊗₁ C.id
                  ∎

                -- α⇒ ∘ (h' ⊗ id) ⊗ id ≈ h' ⊗ id ∘ α⇒
                hbox : C.α⇒ {D⁻' C.⊗₀ E⁺'} {A⁺ C.⊗₀ D⁻'} {XB}
                       C.∘ (h' C.⊗₁ C.id {A⁺ C.⊗₀ D⁻'}) C.⊗₁ C.id {XB}
                       C.≈ h' C.⊗₁ C.id {(A⁺ C.⊗₀ D⁻') C.⊗₀ XB}
                           C.∘ C.α⇒ {D⁺' C.⊗₀ E⁻'} {A⁺ C.⊗₀ D⁻'} {XB}
                hbox = begin
                  C.α⇒ C.∘ (h' C.⊗₁ C.id) C.⊗₁ C.id
                    ≈⟨ C.assoc-commute-from ⟩
                  h' C.⊗₁ (C.id C.⊗₁ C.id) C.∘ C.α⇒
                    ≈⟨ Functor.F-resp-≈ C.⊗ (C.Equiv.refl , Functor.identity C.⊗) ⟩∘⟨refl ⟩
                  h' C.⊗₁ C.id C.∘ C.α⇒
                  ∎


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
import Categories.GConstructionCoherence as GCoh
import Categories.GConstructionIdentityCoherence as GCohId

module _ {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    Cᵤ : Category a b c
    Cᵤ = C

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
          C.Equiv.trans C.superposing
          (C.Equiv.trans (Functor.F-resp-≈ C.⊗ (C.Equiv.refl , C.yanking))
                         (Functor.identity C.⊗))

        -- framed yanking: a loop whose body is a yanking core followed by
        -- loop-independent processing g collapses to g.
        trace-gyank : ∀ {Y X B' : C.Obj} {g : Y C.⊗₀ X C.⇒ B'} →
                      C.trace (g C.⊗₁ C.id C.∘ β {Y} {X} {X}) C.≈ g
        trace-gyank =
          C.Equiv.trans (C.Equiv.sym trace-∘ˡ)
          (C.Equiv.trans (C.∘-resp-≈ʳ trace-βyank) C.identityʳ)

        -- identityˡ: id ∘G f ≈ f, i.e. trace(α ∘ σ⇒ ⊗₁ f ∘ γ) ≈ f
        identityˡ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ C.σ⇒ C.⊗₁ f C.∘ γ) C.≈ f
        identityˡ' {A} {B} {f} =
          C.Equiv.trans (C.Equiv.sym (C.vanishing₂ {X = proj₂ B} {Y = proj₁ B}))
          (C.Equiv.trans (trace-resp-≈ (trace-resp-≈ ICW.C1L))
          (C.Equiv.trans (trace-resp-≈ (C.Equiv.sym trace-∘ʳ))
          (C.Equiv.trans (trace-resp-≈ (C.∘-resp-≈ˡ trace-gyank))
          (C.Equiv.trans (trace-resp-≈ ICW.C3L)
          trace-gyank))))
          where
            module ICW = GCohId.Transport.WithGen
              (record { U = Cᵤ ; monoidal = Monoidal ; symmetric = C.symmetric })
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) f

        -- identityʳ: f ∘G id ≈ f, i.e. trace(α ∘ f ⊗₁ σ⇒ ∘ γ) ≈ f
        identityʳ' : ∀ {A B : C.Obj × C.Obj}
                       {f : proj₁ A C.⊗₀ proj₂ B C.⇒ proj₂ A C.⊗₀ proj₁ B} →
                     C.trace (α C.∘ f C.⊗₁ C.σ⇒ C.∘ γ) C.≈ f
        identityʳ' {A} {B} {f} =
          C.Equiv.trans (C.Equiv.sym (C.vanishing₂ {X = proj₂ A} {Y = proj₁ A}))
          (C.Equiv.trans (trace-resp-≈ (trace-resp-≈ ICW.C1R))
          (C.Equiv.trans (trace-resp-≈
            (C.Equiv.trans (C.Equiv.sym trace-∘ˡ)
            (C.∘-resp-≈ʳ (C.Equiv.trans (C.Equiv.sym trace-∘ʳ)
                         (C.Equiv.trans (C.∘-resp-≈ˡ trace-βyank) C.identityˡ)))))
          (C.Equiv.trans (trace-resp-≈ ICW.C3R)
          (C.Equiv.trans (C.Equiv.sym trace-∘ʳ)
          (C.Equiv.trans (C.∘-resp-≈ˡ trace-gyank)
          (C.Equiv.trans (C.Equiv.sym C.assoc)
          (C.Equiv.trans (C.∘-resp-≈ˡ C.commutative)
          C.identityˡ)))))))
          where
            module ICW = GCohId.Transport.WithGen
              (record { U = Cᵤ ; monoidal = Monoidal ; symmetric = C.symmetric })
              (proj₁ A) (proj₂ A) (proj₁ B) (proj₂ B) f

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

            -- Naturality of β: β ∘ (p ⊗₁ q) ⊗₁ r ≈ (p ⊗₁ r) ⊗₁ q ∘ β
            β-natural : ∀ {P P' Q Q' R R'}
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
            β-involutive : ∀ {P Q R} → β {P} {Q} {R} C.∘ β C.≈ C.id
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
            --
            -- Proof strategy: expand m₀' and q₀, use naturality of α, γ, β
            -- to extract the data morphisms (h', g', f'), then show the
            -- remaining coherence isomorphisms are equal.
            --
            -- Key tools needed:
            --   β-natural:    β ∘ (p ⊗₁ q) ⊗₁ r ≈ (p ⊗₁ r) ⊗₁ q ∘ β
            --   β-involutive: β ∘ β ≈ id
            --   assoc-commute-from/to: naturality of associator
            --   braiding.⇒.commute: naturality of braiding
            --   Functor.homomorphism C.⊗: (f ∘ g) ⊗₁ (h ∘ k) ≈ (f ⊗₁ h) ∘ (g ⊗₁ k)
            assoc'-coherence {A⁺} {A⁻'} {B⁺'} {B⁻'} {D⁺'} {D⁻'} {E⁺'} {E⁻'} f' g' h' =
              GCoh.Transport.WithGens.coherence
                (record { U = Cᵤ ; monoidal = Monoidal ; symmetric = C.symmetric })
                A⁺ A⁻' B⁺' B⁻' D⁺' D⁻' E⁺' E⁻'
                f' g' h'


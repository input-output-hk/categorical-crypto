{-# OPTIONS --safe --without-K #-}

-- Transport of structure along a re-indexing U : I → Obj 𝕄 with isos
-- φ : U a ⊗₀ U b ≅ U (a ⊕ b) and υ : unit ≅ U 𝟙.  Every structure map is 𝕄's own
-- conjugated by φ and υ, so each law is 𝕄's once the φ/υ round trips cancel.  Over a
-- class R of maps closed under identities, ∘ and these conjugates, the subcategory of 𝕄
-- indexed by I with homs in R is monoidal, and its inclusion is strong monoidal with
-- ⊗-homo φ and ε υ.  The conjugates are literal right-nested composites, not built with
-- 𝕄's iso combinators, because clients identify them term by term.

open import Categories.Category.Monoidal.Bundle
open import Categories.Morphism.Notation

module Categories.Category.Monoidal.Construction.Transport
  {o ℓ e i} (𝕄 : MonoidalCategory o ℓ e) {I : Set i}
  (U : I → MonoidalCategory.Obj 𝕄) (_⊕_ : I → I → I) (𝟙 : I)
  (φ : ∀ {a b} → MonoidalCategory.U 𝕄 [ MonoidalCategory._⊗₀_ 𝕄 (U a) (U b) ≅ U (a ⊕ b) ])
  (υ : MonoidalCategory.U 𝕄 [ MonoidalCategory.unit 𝕄 ≅ U 𝟙 ])
  where

open import Data.Product
open import Level

open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Properties.Ext (MonoidalCategory.monoidal 𝕄)
open import Categories.Category.Monoidal.Reasoning (MonoidalCategory.monoidal 𝕄)
open import Categories.Category.Monoidal.Utilities (MonoidalCategory.monoidal 𝕄)
open import Categories.Category.SubCategory (MonoidalCategory.U 𝕄)
open import Categories.Functor.Construction.SubCategory (MonoidalCategory.U 𝕄)
open import Categories.Functor.Monoidal
open import Categories.Morphism (MonoidalCategory.U 𝕄)
open import Categories.Morphism.Reasoning (MonoidalCategory.U 𝕄)
open import Categories.NaturalTransformation.NaturalIsomorphism

open MonoidalCategory 𝕄 hiding (U)
open Shorthands

private
  module φ {a b} = _≅_ (φ {a} {b})
  module υ = _≅_ υ

  variable a b c d a′ b′ c′ : I

  pad-invʳ : ∀ {A B X} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id → f ⊗₁ id {X} ∘ g ⊗₁ id ≈ id
  pad-invʳ e = merge₁ˡ ○ e ⟩⊗⟨refl ○ ⊗.identity

infixr 10 _⊗ᵗ_

_⊗ᵗ_ : U a ⇒ U b → U c ⇒ U d → U (a ⊕ c) ⇒ U (b ⊕ d)
f ⊗ᵗ g = φ.from ∘ (f ⊗₁ g) ∘ φ.to

⊗ᵗ-identity : id {U a} ⊗ᵗ id {U b} ≈ id
⊗ᵗ-identity = elim-center ⊗.identity ○ φ.isoʳ

⊗ᵗ-homomorphism : {f : U b ⇒ U c} {g : U b′ ⇒ U c′} {h : U a ⇒ U b} {k : U a′ ⇒ U b′}
                → (f ∘ h) ⊗ᵗ (g ∘ k) ≈ f ⊗ᵗ g ∘ h ⊗ᵗ k
⊗ᵗ-homomorphism = refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ○ ⟺ (pullʳ (cancelInner φ.isoˡ))

⊗ᵗ-resp-≈ : {f h : U a ⇒ U b} {g k : U a′ ⇒ U b′} → f ≈ h → g ≈ k → f ⊗ᵗ g ≈ h ⊗ᵗ k
⊗ᵗ-resp-≈ p q = refl⟩∘⟨ p ⟩⊗⟨ q ⟩∘⟨refl

φ-commute : {f : U a ⇒ U b} {g : U c ⇒ U d} → φ.from ∘ f ⊗₁ g ≈ f ⊗ᵗ g ∘ φ.from
φ-commute = ⟺ (pullʳ (cancelʳ φ.isoˡ))

λᵗ⇒ : U (𝟙 ⊕ a) ⇒ U a
λᵗ⇒ = λ⇒ ∘ (υ.to ⊗₁ id) ∘ φ.to

λᵗ⇐ : U a ⇒ U (𝟙 ⊕ a)
λᵗ⇐ = φ.from ∘ (υ.from ⊗₁ id) ∘ λ⇐

unitorˡᵗ : U (𝟙 ⊕ a) ≅ U a
unitorˡᵗ = record { from = λᵗ⇒ ; to = λᵗ⇐ ; iso = record
  { isoˡ = pullʳ (cancelInner unitorˡ.isoˡ) ○ refl⟩∘⟨ cancelˡ (pad-invʳ υ.isoʳ) ○ φ.isoʳ
  ; isoʳ = pullʳ (cancelInner φ.isoˡ) ○ refl⟩∘⟨ cancelˡ (pad-invʳ υ.isoˡ) ○ unitorˡ.isoʳ } }

λᵗ-commute : {f : U a ⇒ U b} → λᵗ⇒ ∘ id ⊗ᵗ f ≈ f ∘ λᵗ⇒
λᵗ-commute {f = f} = pullʳ (cancelInner φ.isoˡ) ○ refl⟩∘⟨ extendʳ (⟺ (pad-transport υ.to f))
                   ○ extendʳ unitorˡ-commute-from

unitaryˡᵗ : λᵗ⇒ {a} ∘ φ.from ∘ υ.from ⊗₁ id ≈ λ⇒
unitaryˡᵗ = pullʳ (cancelInner φ.isoˡ) ○ elimʳ (pad-invʳ υ.isoˡ)

ρᵗ⇒ : U (a ⊕ 𝟙) ⇒ U a
ρᵗ⇒ = ρ⇒ ∘ (id ⊗₁ υ.to) ∘ φ.to

ρᵗ⇐ : U a ⇒ U (a ⊕ 𝟙)
ρᵗ⇐ = φ.from ∘ (id ⊗₁ υ.from) ∘ ρ⇐

unitorʳᵗ : U (a ⊕ 𝟙) ≅ U a
unitorʳᵗ = record { from = ρᵗ⇒ ; to = ρᵗ⇐ ; iso = record
  { isoˡ = pullʳ (cancelInner unitorʳ.isoˡ) ○ refl⟩∘⟨ cancelˡ (pad-inv υ.isoʳ) ○ φ.isoʳ
  ; isoʳ = pullʳ (cancelInner φ.isoˡ) ○ refl⟩∘⟨ cancelˡ (pad-inv υ.isoˡ) ○ unitorʳ.isoʳ } }

ρᵗ-commute : {f : U a ⇒ U b} → ρᵗ⇒ ∘ f ⊗ᵗ id ≈ f ∘ ρᵗ⇒
ρᵗ-commute {f = f} = pullʳ (cancelInner φ.isoˡ) ○ refl⟩∘⟨ extendʳ (pad-transport f υ.to)
                   ○ extendʳ unitorʳ-commute-from

unitaryʳᵗ : ρᵗ⇒ {a} ∘ φ.from ∘ id ⊗₁ υ.from ≈ ρ⇒
unitaryʳᵗ = pullʳ (cancelInner φ.isoˡ) ○ elimʳ (pad-inv υ.isoˡ)

αᵗ⇒ : U ((a ⊕ b) ⊕ c) ⇒ U (a ⊕ (b ⊕ c))
αᵗ⇒ = φ.from ∘ (id ⊗₁ φ.from) ∘ α⇒ ∘ (φ.to ⊗₁ id) ∘ φ.to

αᵗ⇐ : U (a ⊕ (b ⊕ c)) ⇒ U ((a ⊕ b) ⊕ c)
αᵗ⇐ = φ.from ∘ (φ.from ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ φ.to) ∘ φ.to

associatorᵗ : U ((a ⊕ b) ⊕ c) ≅ U (a ⊕ (b ⊕ c))
associatorᵗ = record { from = αᵗ⇒ ; to = αᵗ⇐ ; iso = record
  { isoˡ = pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ)))
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ (pad-inv φ.isoˡ)
         ○ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoˡ ○ refl⟩∘⟨ cancelˡ (pad-invʳ φ.isoʳ) ○ φ.isoʳ
  ; isoʳ = pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ)))
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ (pad-invʳ φ.isoˡ)
         ○ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ○ refl⟩∘⟨ cancelˡ (pad-inv φ.isoʳ) ○ φ.isoʳ } }

αᵗ-commute : {f : U a ⇒ U a′} {g : U b ⇒ U b′} {h : U c ⇒ U c′}
           → αᵗ⇒ ∘ (f ⊗ᵗ g) ⊗ᵗ h ≈ f ⊗ᵗ (g ⊗ᵗ h) ∘ αᵗ⇒
αᵗ-commute {f = f} {g} {h} = begin
  αᵗ⇒ ∘ (f ⊗ᵗ g) ⊗ᵗ h
    ≈⟨ pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ))) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ (f ⊗ᵗ g) ⊗₁ h ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (parallel (cancelˡ φ.isoˡ) id-comm-sym) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ α⇒ ∘ (f ⊗₁ g) ⊗₁ h ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ extendʳ (parallel id-comm-sym φ-commute) ⟩
  φ.from ∘ f ⊗₁ (g ⊗ᵗ h) ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈˘⟨ pullʳ (cancelInner φ.isoˡ) ⟩
  f ⊗ᵗ (g ⊗ᵗ h) ∘ αᵗ⇒ ∎

associativityᵗ : αᵗ⇒ {a} {b} {c} ∘ φ.from ∘ φ.from ⊗₁ id ≈ φ.from ∘ id ⊗₁ φ.from ∘ α⇒
associativityᵗ =
  pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ))) ○ refl⟩∘⟨ refl⟩∘⟨ elimʳ (pad-invʳ φ.isoˡ)

triangleᵗ : id ⊗ᵗ λᵗ⇒ ∘ αᵗ⇒ ≈ ρᵗ⇒ {a} ⊗ᵗ id {U b}
triangleᵗ = begin
  id ⊗ᵗ λᵗ⇒ ∘ αᵗ⇒
    ≈⟨ pullʳ (cancelInner φ.isoˡ) ⟩
  φ.from ∘ id ⊗₁ λᵗ⇒ ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ pullʳ (cancelʳ φ.isoˡ)) ⟩
  φ.from ∘ id ⊗₁ (λ⇒ ∘ υ.to ⊗₁ id) ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ○ refl⟩∘⟨ refl⟩∘⟨ extendʳ (⟺ assoc-commute-from) ⟩
  φ.from ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ (id ⊗₁ υ.to) ⊗₁ id ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
  φ.from ∘ ρ⇒ ⊗₁ id ∘ (id ⊗₁ υ.to) ⊗₁ id ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ (pullˡ merge₁ˡ ○ pullˡ merge₁ˡ ○ (assoc ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
  ρᵗ⇒ ⊗ᵗ id ∎

pentagonᵗ : id ⊗ᵗ αᵗ⇒ ∘ αᵗ⇒ ∘ αᵗ⇒ ⊗ᵗ id ≈ αᵗ⇒ ∘ αᵗ⇒ {a ⊕ b} {c} {d}
pentagonᵗ = begin
  id ⊗ᵗ αᵗ⇒ ∘ αᵗ⇒ ∘ αᵗ⇒ ⊗ᵗ id
    ≈⟨ refl⟩∘⟨ pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ))) ○ pullʳ (cancelInner φ.isoˡ) ⟩
  φ.from ∘ id ⊗₁ αᵗ⇒ ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ αᵗ⇒ ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ (pullˡ merge₂ʳ ○ (refl⟩⊗⟨ pullʳ (pullʳ (pullʳ (cancelʳ φ.isoˡ)))) ⟩∘⟨refl) ⟩
  φ.from ∘ id ⊗₁ (φ.from ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id) ∘ α⇒ ∘ φ.to ⊗₁ id ∘ αᵗ⇒ ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ (pushˡ split₂ˡ ○ refl⟩∘⟨ pushˡ split₂ˡ ○ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (φ.to ⊗₁ id) ∘ α⇒
    ∘ φ.to ⊗₁ id ∘ αᵗ⇒ ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         (pullˡ merge₁ˡ ○ (cancelˡ φ.isoˡ ⟩⊗⟨refl) ⟩∘⟨refl ○ pushˡ split₁ˡ) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ id ⊗₁ α⇒ ∘ id ⊗₁ (φ.to ⊗₁ id) ∘ α⇒
    ∘ (id ⊗₁ φ.from) ⊗₁ id ∘ (α⇒ ∘ φ.to ⊗₁ id ∘ φ.to) ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         (refl⟩∘⟨ extendʳ assoc-commute-from ○ cancelˡ (pad-inv (pad-invʳ φ.isoˡ))) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ (α⇒ ∘ φ.to ⊗₁ id ∘ φ.to) ⊗₁ id
    ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         (refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ○ refl⟩∘⟨ sym-assoc ○ pullˡ pentagon ○ assoc) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ α⇒ ∘ α⇒ ∘ (φ.to ⊗₁ id ∘ φ.to) ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ α⇒ ∘ α⇒ ∘ (φ.to ⊗₁ id) ⊗₁ id
    ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         extendʳ (assoc-commute-from ○ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ id ⊗₁ (id ⊗₁ φ.from) ∘ α⇒ ∘ φ.to ⊗₁ id ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (⟺ assoc-commute-from ○ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ α⇒ ∘ id ⊗₁ φ.from ∘ φ.to ⊗₁ id ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (pad-transport φ.to φ.from) ⟩
  φ.from ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ id ⊗₁ φ.from ∘ α⇒ ∘ φ.to ⊗₁ id ∘ φ.to
    ≈˘⟨ pullʳ (pullʳ (pullʳ (cancelInner φ.isoˡ))) ⟩
  αᵗ⇒ ∘ αᵗ⇒ ∎

module Restriction {r} (R : ∀ {a b} → U a ⇒ U b → Set r)
         (R-id : ∀ {a} → R (id {U a}))
         (R-∘ : ∀ {a b c} {f : U b ⇒ U c} {g : U a ⇒ U b} → R f → R g → R (f ∘ g))
         (R-⊗ : ∀ {a b c d} {f : U a ⇒ U b} {g : U c ⇒ U d} → R f → R g → R (f ⊗ᵗ g))
         (R-λ⇒ : ∀ {a} → R (λᵗ⇒ {a})) (R-λ⇐ : ∀ {a} → R (λᵗ⇐ {a}))
         (R-ρ⇒ : ∀ {a} → R (ρᵗ⇒ {a})) (R-ρ⇐ : ∀ {a} → R (ρᵗ⇐ {a}))
         (R-α⇒ : ∀ {a b c} → R (αᵗ⇒ {a} {b} {c})) (R-α⇐ : ∀ {a b c} → R (αᵗ⇐ {a} {b} {c}))
         where

  subCat : SubCat I
  subCat = record { U = U ; R = R ; Rid = R-id ; _∘R_ = R-∘ }

  private
    lift≅ : (j : U a ≅ U b) → R (_≅_.from j) → R (_≅_.to j) → SubCategory subCat [ a ≅ b ]
    lift≅ j rf rt = record
      { from = from , rf ; to = to , rt ; iso = record { isoˡ = isoˡ ; isoʳ = isoʳ } }
      where open _≅_ j

  transport : MonoidalCategory i (ℓ ⊔ r) e
  transport = record
    { U = SubCategory subCat
    ; monoidal = monoidalHelper (SubCategory subCat) record
      { ⊗ = record
        { F₀ = uncurry _⊕_ ; F₁ = λ ((f , rf) , (g , rg)) → f ⊗ᵗ g , R-⊗ rf rg
        ; identity = ⊗ᵗ-identity ; homomorphism = ⊗ᵗ-homomorphism ; F-resp-≈ = uncurry ⊗ᵗ-resp-≈ }
      ; unit = 𝟙 ; unitorˡ = lift≅ unitorˡᵗ R-λ⇒ R-λ⇐ ; unitorʳ = lift≅ unitorʳᵗ R-ρ⇒ R-ρ⇐
      ; associator = lift≅ associatorᵗ R-α⇒ R-α⇐ ; unitorˡ-commute = λᵗ-commute
      ; unitorʳ-commute = ρᵗ-commute ; assoc-commute = αᵗ-commute ; triangle = triangleᵗ
      ; pentagon = pentagonᵗ } }

  transportF : StrongMonoidalFunctor transport 𝕄
  transportF = record
    { F = Sub subCat
    ; isStrongMonoidal = record
      { ε = υ
      ; ⊗-homo = niHelper record
        { η = λ _ → φ.from ; η⁻¹ = λ _ → φ.to ; commute = λ _ → φ-commute ; iso = λ _ → φ.iso }
      ; associativity = associativityᵗ ; unitaryˡ = unitaryˡᵗ ; unitaryʳ = unitaryʳᵗ } }

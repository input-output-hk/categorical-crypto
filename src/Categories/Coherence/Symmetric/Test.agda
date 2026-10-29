{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Public Solver behavior: coherence, positioned/syntactic/deep rewriting,
-- driver endpoints, and chained Frobenius rewrites.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle

module Categories.Coherence.Symmetric.Test
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin
open import Data.List
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Categories.Coherence.Symmetric

private module C = SymmetricMonoidalCategory C
open C hiding (_⊗₀_)
open MonoidalUtilities.Shorthands C.monoidal

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

private
  σ : ∀ {X Y} → (X C.⊗₀ Y) ⇒ (Y C.⊗₀ X)
  σ {X} {Y} = C.braiding.⇒.η (X , Y)

module Atom1 (A : C.Obj) where
  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ) public

  a : ObjTerm
  a = Var zero

  objects : Vec C.Obj 1
  objects = A ∷ []

module Atoms3 (A₀ A₁ A₂ : C.Obj) where
  open FreeMonoidalHelper Symm (Fin 3) using (ObjTerm; Var) public

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

  objects : Vec C.Obj 3
  objects = A₀ ∷ A₁ ∷ A₂ ∷ []

--------------------------------------------------------------------------------
-- solveH!: category and monoidal coherence
--------------------------------------------------------------------------------
module Cycle3 (A₀ A₁ A₂ : C.Obj) (fᴹ : A₀ C.⇒ A₁) (gᴹ : A₁ C.⇒ A₂) (hᴹ : A₂ C.⇒ A₀) where

  open Atoms3 A₀ A₁ A₂

  open Solver C objects ((a₀ , a₁ , fᴹ) ∷ (a₁ , a₂ , gᴹ) ∷ (a₂ , a₀ , hᴹ) ∷ [])

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  test-idˡ : id ∘ fᴹ ≈ fᴹ
  test-idˡ = solveH! (S.id S.∘ f) f

  test-idʳ : fᴹ ∘ id ≈ fᴹ
  test-idʳ = solveH! (f S.∘ S.id) f

  test-≈-refl : fᴹ ≈ fᴹ
  test-≈-refl = solveH! f f

  test-id⊗id : id {A₀} ⊗₁ id {A₁} ≈ id {A₀ C.⊗₀ A₁}
  test-id⊗id = solveH! (S.id {a₀} S.⊗₁ S.id {a₁}) (S.id {a₀ S.⊗₀ a₁})

  test-assoc : (hᴹ ∘ gᴹ) ∘ fᴹ ≈ hᴹ ∘ (gᴹ ∘ fᴹ)
  test-assoc = solveH! ((h S.∘ g) S.∘ f) (h S.∘ (g S.∘ f))

  test-⊗-∘-dist : (gᴹ ∘ fᴹ) ⊗₁ (fᴹ ∘ hᴹ) ≈ (gᴹ ⊗₁ fᴹ) ∘ (fᴹ ⊗₁ hᴹ)
  test-⊗-∘-dist = solveH! ((g S.∘ f) S.⊗₁ (f S.∘ h)) ((g S.⊗₁ f) S.∘ (f S.⊗₁ h))

  test-λ⇐∘λ⇒ : λ⇐ ∘ λ⇒ {A₀} ≈ id {C.unit C.⊗₀ A₀}
  test-λ⇐∘λ⇒ = solveH! (S.λ⇐ S.∘ S.λ⇒ {a₀}) (S.id {S.unit S.⊗₀ a₀})

  test-λ⇒∘λ⇐ : λ⇒ ∘ λ⇐ {A₀} ≈ id {A₀}
  test-λ⇒∘λ⇐ = solveH! (S.λ⇒ S.∘ S.λ⇐ {a₀}) (S.id {a₀})

  test-ρ⇐∘ρ⇒ : ρ⇐ ∘ ρ⇒ {A₀} ≈ id {A₀ C.⊗₀ C.unit}
  test-ρ⇐∘ρ⇒ = solveH! (S.ρ⇐ S.∘ S.ρ⇒ {a₀}) (S.id {a₀ S.⊗₀ S.unit})

  test-ρ⇒∘ρ⇐ : ρ⇒ ∘ ρ⇐ {A₀} ≈ id {A₀}
  test-ρ⇒∘ρ⇐ = solveH! (S.ρ⇒ S.∘ S.ρ⇐ {a₀}) (S.id {a₀})

  test-α⇐∘α⇒ : α⇐ ∘ α⇒ {A₀} {A₁} {A₂} ≈ id {(A₀ C.⊗₀ A₁) C.⊗₀ A₂}
  test-α⇐∘α⇒ = solveH! (S.α⇐ S.∘ S.α⇒ {a₀} {a₁} {a₂}) S.id

  test-α⇒∘α⇐ : α⇒ ∘ α⇐ {A₀} {A₁} {A₂} ≈ id {A₀ C.⊗₀ (A₁ C.⊗₀ A₂)}
  test-α⇒∘α⇐ = solveH! (S.α⇒ S.∘ S.α⇐ {a₀} {a₁} {a₂}) S.id

  test-λ⇒∘id⊗f : λ⇒ ∘ (id {C.unit} ⊗₁ fᴹ) ≈ fᴹ ∘ λ⇒
  test-λ⇒∘id⊗f = solveH! (S.λ⇒ S.∘ (S.id {S.unit} S.⊗₁ f)) (f S.∘ S.λ⇒)

  test-ρ⇒∘f⊗id : ρ⇒ ∘ (fᴹ ⊗₁ id {C.unit}) ≈ fᴹ ∘ ρ⇒
  test-ρ⇒∘f⊗id = solveH! (S.ρ⇒ S.∘ (f S.⊗₁ S.id {S.unit})) (f S.∘ S.ρ⇒)

  test-α-comm : α⇒ ∘ ((fᴹ ⊗₁ gᴹ) ⊗₁ hᴹ) ≈ (fᴹ ⊗₁ (gᴹ ⊗₁ hᴹ)) ∘ α⇒
  test-α-comm = solveH! (S.α⇒ S.∘ ((f S.⊗₁ g) S.⊗₁ h))
                        ((f S.⊗₁ (g S.⊗₁ h)) S.∘ S.α⇒)

  test-triangle : (id ⊗₁ λ⇒) ∘ α⇒ ≈ ρ⇒ {A₀} ⊗₁ id {A₁}
  test-triangle = solveH! ((S.id S.⊗₁ S.λ⇒) S.∘ S.α⇒) (S.ρ⇒ {a₀} S.⊗₁ S.id {a₁})

  test-pentagon
    : (id {A₀} ⊗₁ α⇒ {A₁} {A₂} {A₀}) ∘ α⇒ ∘ (α⇒ ⊗₁ id {A₀})
    ≈ α⇒ ∘ α⇒ {A₀ C.⊗₀ A₁} {A₂} {A₀}
  test-pentagon =
    solveH! ((S.id {a₀} S.⊗₁ S.α⇒ {a₁} {a₂} {a₀}) S.∘ S.α⇒ S.∘ (S.α⇒ S.⊗₁ S.id {a₀}))
            (S.α⇒ S.∘ S.α⇒ {a₀ S.⊗₀ a₁} {a₂} {a₀})

--------------------------------------------------------------------------------
-- solveH!: braiding
--------------------------------------------------------------------------------
module Braiding (A₀ A₁ A₂ : C.Obj) (pᴹ qᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂) where

  open Atoms3 A₀ A₁ A₂
  open C using (_⊗₀_)

  open Solver C objects ((a₀ , a₁ , pᴹ) ∷ (a₀ , a₁ , qᴹ) ∷ (a₁ , a₂ , sᴹ) ∷ [])

  private
    p q s : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    s = S.Agen (gen (suc (suc zero)))

  test-σ-invol : σ ∘ σ ≈ id {A₀ ⊗₀ A₁}
  test-σ-invol = solveH! (S.σ S.∘ S.σ) (S.id {a₀ S.⊗₀ a₁})

  test-σ-nat : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-σ-nat = solveH! (S.σ S.∘ (p S.⊗₁ s)) ((s S.⊗₁ p) S.∘ S.σ)

  test-σ-conj : σ ∘ (pᴹ ⊗₁ qᴹ) ∘ σ ≈ qᴹ ⊗₁ pᴹ
  test-σ-conj = solveH! (S.σ S.∘ (p S.⊗₁ q) S.∘ S.σ) (q S.⊗₁ p)

  test-hexagon : id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈ α⇒ ∘ σ ∘ α⇒ {A₀} {A₁} {A₂}
  test-hexagon = solveH! (S.id S.⊗₁ S.σ S.∘ S.α⇒ S.∘ S.σ S.⊗₁ S.id)
                         (S.α⇒ S.∘ S.σ S.∘ S.α⇒ {a₀} {a₁} {a₂})

  test-σ-slide : σ ∘ ((sᴹ ∘ pᴹ) ⊗₁ id {A₂}) ≈ (id {A₂} ⊗₁ (sᴹ ∘ pᴹ)) ∘ σ
  test-σ-slide = solveH! (S.σ S.∘ ((s S.∘ p) S.⊗₁ S.id {a₂}))
                         ((S.id {a₂} S.⊗₁ (s S.∘ p)) S.∘ S.σ)

--------------------------------------------------------------------------------
-- solveH!: reflexive, reassociated and wrapped equations
--------------------------------------------------------------------------------
module SplitConfig (A₀ A₁ A₂ : C.Obj)
  (pᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂)
  (wᴹ : (A₂ C.⊗₀ A₁) C.⇒ (A₂ C.⊗₀ A₁))
  where

  open Atoms3 A₀ A₁ A₂
  open FreeMonoidalHelper Symm (Fin 3) using (_⊗₀_)

  open Solver C objects
    ((a₀ , a₁ , pᴹ) ∷ (a₁ , a₂ , sᴹ) ∷ ((a₂ ⊗₀ a₁) , (a₂ ⊗₀ a₁) , wᴹ) ∷ [])

  private
    p s w : S.HomTerm _ _
    p = S.Agen (gen zero)
    s = S.Agen (gen (suc zero))
    w = S.Agen (gen (suc (suc zero)))

    lhs-core rhs-core : S.HomTerm (a₀ S.⊗₀ a₁) (a₂ S.⊗₀ a₁)
    lhs-core = S.σ S.∘ (p S.⊗₁ s)
    rhs-core = (s S.⊗₁ p) S.∘ S.σ

  test-refl : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ σ ∘ (pᴹ ⊗₁ sᴹ)
  test-refl = solveH! lhs-core lhs-core

  test-reassoc-refl : (wᴹ ∘ σ) ∘ (pᴹ ⊗₁ sᴹ) ≈ wᴹ ∘ (σ ∘ (pᴹ ⊗₁ sᴹ))
  test-reassoc-refl = solveH! ((w S.∘ S.σ) S.∘ (p S.⊗₁ s))
                            (w S.∘ (S.σ S.∘ (p S.⊗₁ s)))

  test-wrapped : wᴹ ∘ (wᴹ ∘ (σ ∘ (pᴹ ⊗₁ sᴹ))) ≈ wᴹ ∘ (wᴹ ∘ ((sᴹ ⊗₁ pᴹ) ∘ σ))
  test-wrapped = solveH! (w S.∘ (w S.∘ lhs-core)) (w S.∘ (w S.∘ rhs-core))

  test-fallback : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-fallback = solveH! lhs-core rhs-core

--------------------------------------------------------------------------------
-- solveH!: braided merge, compared with a manual proof
--------------------------------------------------------------------------------
module Crossings (A₀ A₁ A₂ : C.Obj)
  (fᴹ : A₀ C.⇒ A₁) (gᴹ : (A₂ C.⊗₀ A₁) C.⇒ A₀) (hᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂
  open FreeMonoidalHelper Symm (Fin 3) using (_⊗₀_)

  open Solver C objects ((a₀ , a₁ , fᴹ) ∷ ((a₂ ⊗₀ a₁) , a₀ , gᴹ) ∷ (a₁ , a₂ , hᴹ) ∷ [])

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  private module MR = MonoidalReasoning C.monoidal
  open C.HomReasoning

  byHand : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
       C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  byHand = begin
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.braiding.⇒.commute (fᴹ , C.id) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ (id {A₁ C.⊗₀ A₂} ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (MR.⊗-resp-≈ˡ (⟺ C.⊗.identity) ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ)) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (C.assoc-commute-from ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ (((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ α⇒) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ ((hᴹ ⊗₁ gᴹ) ∘ (id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ)
        ≈⟨ refl⟩∘⟨ ((⟺ C.⊗.homomorphism) ⟩∘⟨refl) ⟩
      σ ∘ (((hᴹ ∘ id {A₁}) ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ ((MR.⊗-resp-≈ˡ C.identityʳ) ⟩∘⟨refl) ⟩
      σ ∘ ((hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ C.sym-assoc ⟩
      (σ ∘ (hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ)))) ∘ (α⇒ ∘ σ)
        ≈⟨ C.braiding.⇒.commute (hᴹ , gᴹ C.∘ (C.id C.⊗₁ fᴹ)) ⟩∘⟨refl ⟩
      (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ) ∎

  auto : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
     C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  auto = solveH! (S.σ S.∘ (h S.⊗₁ g) S.∘ S.α⇒ S.∘ S.σ S.∘ (f S.⊗₁ S.id {a₁ S.⊗₀ a₂}))
                 ((((g S.∘ (S.id {a₂} S.⊗₁ f)) S.⊗₁ h) S.∘ S.σ) S.∘ (S.α⇒ S.∘ S.σ))

--------------------------------------------------------------------------------
-- rewriteH! / rewriteAutoₙ!: monoid unit law and syntactic occurrences
--------------------------------------------------------------------------------
module MonoidRewrite (A : C.Obj) (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A) where

  open Atom1 A renaming (a to a₀)

  open Solver C objects (((a₀ ⊗₀ a₀) , a₀ , mᴹ) ∷ (unitᵗ , a₀ , uᴹ) ∷ [])

  private
    m u : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))

    lᵗ : S.HomTerm (unitᵗ S.⊗₀ a₀) a₀
    lᵗ = m S.∘ (u S.⊗₁ S.id)

  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id {A}) ≈ λ⇒) where

    test-unitˡ-in-context : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ mᴹ ∘ (id {A} ⊗₁ λ⇒)
    test-unitˡ-in-context =
      rewriteH!
        (m S.∘ (S.id {a₀} S.⊗₁ lᵗ))
        (m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒))
        (S.id {a₀ S.⊗₀ (unitᵗ S.⊗₀ a₀)})
        m
        lᵗ S.λ⇒ unitLawˡ

    test-unitˡ-auto : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ _
    test-unitˡ-auto = rewriteAutoₙ! (m S.∘ (S.id {a₀} S.⊗₁ lᵗ)) lᵗ S.λ⇒ 0 unitLawˡ

    -- Root occurrence, with no surrounding generator.
    test-unitˡ-at-root : mᴹ ∘ (uᴹ ⊗₁ id {A}) ≈ _
    test-unitˡ-at-root = rewriteAutoₙ! lᵗ lᵗ S.λ⇒ 0 unitLawˡ

    -- Coherence-equivalent spelling of the same redex.
    test-unitˡ-noisy : (mᴹ ∘ (uᴹ ⊗₁ id {A}) ∘ id) ∘ (σ ∘ σ) ≈ _
    test-unitˡ-noisy =
      rewriteAutoₙ! ((m S.∘ (u S.⊗₁ S.id) S.∘ S.id) S.∘ (S.σ S.∘ S.σ))
                    lᵗ S.λ⇒ 0 unitLawˡ

    -- Index 1 selects the other copy.
    test-unitˡ-auto-occ1 : (mᴹ ∘ (uᴹ ⊗₁ id {A})) ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A})) ≈ _
    test-unitˡ-auto-occ1 = rewriteAutoₙ! (lᵗ S.⊗₁ lᵗ) lᵗ S.λ⇒ 1 unitLawˡ

    test-rewrite-then-coherence
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ (mᴹ ∘ (id {A} ⊗₁ λ⇒)) ∘ id
    test-rewrite-then-coherence = begin
      mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A})))
        ≈⟨ test-unitˡ-in-context ⟩
      mᴹ ∘ (id {A} ⊗₁ λ⇒)
        ≈⟨ solveH! (m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒))
                   ((m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒)) S.∘ S.id) ⟩
      (mᴹ ∘ (id {A} ⊗₁ λ⇒)) ∘ id ∎
      where open C.HomReasoning

--------------------------------------------------------------------------------
-- rewriteDeepₙ! / rewriteDeepTo!: interchange, braiding and disconnected redexes
--------------------------------------------------------------------------------
module DeepRewrite (A₀ A₁ A₂ : C.Obj) (pᴹ qᴹ : A₀ C.⇒ A₁) (wᴹ : A₁ C.⇒ A₂) where

  open Atoms3 A₀ A₁ A₂

  open Solver C objects ((a₀ , a₁ , pᴹ) ∷ (a₀ , a₁ , qᴹ) ∷ (a₁ , a₂ , wᴹ) ∷ [])

  private
    p q w : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    w = S.Agen (gen (suc (suc zero)))

  module _ (collapse : wᴹ ∘ pᴹ ≈ wᴹ ∘ qᴹ) where

    -- A composite redex spread across tensor factors.
    test-deep-rewrite : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ _
    test-deep-rewrite =
      rewriteDeepₙ! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) (w S.∘ p) (w S.∘ q) 0 collapse

    -- `p` crosses the braiding to feed the first `w`.
    test-deep-σ-crossing : (wᴹ ⊗₁ wᴹ) ∘ σ ∘ (qᴹ ⊗₁ pᴹ) ≈ _
    test-deep-σ-crossing =
      rewriteDeepₙ! ((w S.⊗₁ w) S.∘ S.σ S.∘ (q S.⊗₁ p)) (w S.∘ p) (w S.∘ q) 0 collapse

    -- The subject includes an input permutation.
    test-deep-permuted-boundary : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ∘ σ {A₀} {A₀} ≈ _
    test-deep-permuted-boundary =
      rewriteDeepₙ! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q) S.∘ S.σ {a₀} {a₀})
                    (w S.∘ p) (w S.∘ q) 0 collapse

    test-deep-chain : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ (wᴹ ⊗₁ wᴹ) ∘ (qᴹ ⊗₁ qᴹ)
    test-deep-chain =
      rewriteDeepTo! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) ((w S.⊗₁ w) S.∘ (q S.⊗₁ q))
                     (w S.∘ p) (w S.∘ q) 0 collapse

    -- No syntactic focus crosses this interchange: `found` fails, so the
    -- result cannot be built.

    -- auto-cannot-cross-interchange : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ (wᴹ ⊗₁ wᴹ) ∘ (qᴹ ⊗₁ qᴹ)
    -- auto-cannot-cross-interchange =
    --   rewriteAutoₙ! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) (w S.∘ p) (w S.∘ q) 0 collapse

  module _ (commute : pᴹ ⊗₁ qᴹ ≈ qᴹ ⊗₁ pᴹ) where

    -- A disconnected redex.
    test-deep-parallel : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ _
    test-deep-parallel =
      rewriteDeepₙ! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q))
                    (p S.⊗₁ q) (q S.⊗₁ p) 0 commute

  ------------------------------------------------------------------------------
  -- Padded rules
  ------------------------------------------------------------------------------
  -- Tensor need not be faithful: these hypotheses hold only at padded types.
  module _ (padded : pᴹ ⊗₁ id {A₀} ≈ qᴹ ⊗₁ id {A₀}) where

    test-deep-padded-rule : pᴹ ⊗₁ qᴹ ≈ qᴹ ⊗₁ qᴹ
    test-deep-padded-rule =
      rewriteDeepTo! (p S.⊗₁ q) (q S.⊗₁ q)
                     (p S.⊗₁ S.id {a₀}) (q S.⊗₁ S.id {a₀}) 0 padded

  module _ (paddedL : id {A₁} ⊗₁ pᴹ ≈ id {A₁} ⊗₁ qᴹ) where

    test-deep-padded-left : wᴹ ⊗₁ pᴹ ≈ wᴹ ⊗₁ qᴹ
    test-deep-padded-left =
      rewriteDeepTo! (w S.⊗₁ p) (w S.⊗₁ q)
                     (S.id {a₁} S.⊗₁ p) (S.id {a₁} S.⊗₁ q) 0 paddedL

  module _ (padded² : (pᴹ ⊗₁ id {A₀}) ⊗₁ id {A₁} ≈ (qᴹ ⊗₁ id {A₀}) ⊗₁ id {A₁}) where

    test-deep-padded-two : (pᴹ ⊗₁ qᴹ) ⊗₁ wᴹ ≈ (qᴹ ⊗₁ qᴹ) ⊗₁ wᴹ
    test-deep-padded-two =
      rewriteDeepTo! ((p S.⊗₁ q) S.⊗₁ w) ((q S.⊗₁ q) S.⊗₁ w)
                     ((p S.⊗₁ S.id {a₀}) S.⊗₁ S.id {a₁})
                     ((q S.⊗₁ S.id {a₀}) S.⊗₁ S.id {a₁}) 0 padded²

  module _ (collapseP : (wᴹ ∘ pᴹ) ⊗₁ id {A₁} ≈ (wᴹ ∘ qᴹ) ⊗₁ id {A₁}) where

    test-deep-padded-composite : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ (wᴹ ⊗₁ wᴹ) ∘ (qᴹ ⊗₁ qᴹ)
    test-deep-padded-composite =
      rewriteDeepTo! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) ((w S.⊗₁ w) S.∘ (q S.⊗₁ q))
                     ((w S.∘ p) S.⊗₁ S.id {a₁}) ((w S.∘ q) S.⊗₁ S.id {a₁}) 0 collapseP

--------------------------------------------------------------------------------
-- rewriteDeepₙ!: multi-arity generators and convex occurrences
--------------------------------------------------------------------------------
module DeepArity (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (eᴹ : A C.⇒ (A C.⊗₀ A))
  (kᴹ : A C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open Atom1 A

  open Solver C objects
    (((a ⊗₀ a) , a , mᴹ) ∷ (a , (a ⊗₀ a) , eᴹ) ∷ (a , a , kᴹ) ∷ (unitᵗ , a , uᴹ) ∷ [])

  private
    m sp k u : S.HomTerm _ _
    m  = S.Agen (gen zero)
    sp = S.Agen (gen (suc zero))
    k  = S.Agen (gen (suc (suc zero)))
    u  = S.Agen (gen (suc (suc (suc zero))))

  module _ (identityLaw : id {A} ≈ kᴹ) where

    -- Deep search cannot insert this one-wire identity LHS.

    -- deep-cannot-insert-identity-law : kᴹ ≈ kᴹ ∘ kᴹ
    -- deep-cannot-insert-identity-law =
    --   rewriteDeepTo! k (k S.∘ k) (S.id {a}) k 0 identityLaw

    positioned-identity-law : kᴹ ≈ kᴹ ∘ kᴹ
    positioned-identity-law =
      rewriteH! k (k S.∘ k) S.λ⇐ (k S.∘ S.λ⇒) (S.id {a}) k identityLaw

  -- Multi-wire redex under a closing merge.
  module _ (fuse : (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ eᴹ) where

    test-deep-multiwire : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ _
    test-deep-multiwire =
      rewriteDeepₙ! (m S.∘ (k S.⊗₁ k) S.∘ sp) ((k S.⊗₁ k) S.∘ sp) sp 0 fuse

  -- Empty input interface on the redex.
  module _ (grow : uᴹ ≈ kᴹ ∘ uᴹ) where

    test-deep-scalar : mᴹ ∘ (uᴹ ⊗₁ kᴹ) ≈ _
    test-deep-scalar =
      rewriteDeepₙ! (m S.∘ (u S.⊗₁ k)) u (k S.∘ u) 0 grow

  -- Identical generator labels on swapped merge inputs.
  module _ (slide : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ≈ kᴹ ∘ mᴹ) where

    test-deep-swapped-merge : mᴹ ∘ σ ∘ (kᴹ ⊗₁ kᴹ) ≈ _
    test-deep-swapped-merge =
      rewriteDeepₙ! (m S.∘ S.σ S.∘ (k S.⊗₁ k)) (m S.∘ (k S.⊗₁ k)) (k S.∘ m) 0 slide

  module _ (mix : kᴹ ⊗₁ kᴹ ≈ eᴹ ∘ mᴹ) where

    test-deep-retry : (kᴹ ∘ kᴹ ∘ kᴹ) ⊗₁ kᴹ ≈ _
    test-deep-retry =
      rewriteDeepₙ! ((k S.∘ k S.∘ k) S.⊗₁ k) (k S.⊗₁ k) (sp S.∘ m) 0 mix

--------------------------------------------------------------------------------
-- Deep padding: typed context wires and selected occurrences
--------------------------------------------------------------------------------
module DeepPadding (A B C₀ D : C.Obj)
  (pᴹ qᴹ : A C.⇒ B) (rᴹ : D C.⇒ C₀) (gᴹ : C₀ C.⇒ D) (zᴹ : C.unit C.⇒ C.unit)
  where

  open FreeMonoidalHelper Symm (Fin 4) using (ObjTerm; Var)
    renaming (unit to unitᵗ)

  a b c d : ObjTerm
  a = Var zero
  b = Var (suc zero)
  c = Var (suc (suc zero))
  d = Var (suc (suc (suc zero)))

  open Solver C (A ∷ B ∷ C₀ ∷ D ∷ [])
    ((a , b , pᴹ) ∷ (a , b , qᴹ) ∷ (d , c , rᴹ) ∷ (c , d , gᴹ) ∷ (unitᵗ , unitᵗ , zᴹ) ∷ [])

  private
    p q r g z : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    r = S.Agen (gen (suc (suc zero)))
    g = S.Agen (gen (suc (suc (suc zero))))
    z = S.Agen (gen (suc (suc (suc (suc zero)))))

  module _ (padD : pᴹ ⊗₁ id {D} ≈ qᴹ ⊗₁ id {D}) where

    test-pad-input : pᴹ ⊗₁ rᴹ ≈ qᴹ ⊗₁ rᴹ
    test-pad-input =
      rewriteDeepTo! (p S.⊗₁ r) (q S.⊗₁ r) (p S.⊗₁ S.id {d}) (q S.⊗₁ S.id {d}) 0 padD

  module _ (padC : pᴹ ⊗₁ id {C₀} ≈ qᴹ ⊗₁ id {C₀}) where

    test-pad-output : pᴹ ⊗₁ rᴹ ≈ qᴹ ⊗₁ rᴹ
    test-pad-output =
      rewriteDeepTo! (p S.⊗₁ r) (q S.⊗₁ r) (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) 0 padC

    -- Composing the padded LHS with id hides the outer pad.

    -- deep-cannot-see-wrapped-pad : pᴹ ⊗₁ rᴹ ≈ qᴹ ⊗₁ rᴹ
    -- deep-cannot-see-wrapped-pad =
    --   rewriteDeepTo! (p S.⊗₁ r) (q S.⊗₁ r)
    --                  ((p S.⊗₁ S.id {c}) S.∘ S.id) (q S.⊗₁ S.id {c}) 0
    --                  (C.Equiv.trans C.identityʳ padC)

    test-pad-output-context : pᴹ ⊗₁ rᴹ ≈ qᴹ ⊗₁ rᴹ
    test-pad-output-context =
      rewriteH! (p S.⊗₁ r) (q S.⊗₁ r)
                (S.λ⇐ S.∘ (S.id {a} S.⊗₁ r)) S.λ⇒
                (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) padC

    test-pad-output-driver : pᴹ ⊗₁ rᴹ ≈ qᴹ ⊗₁ rᴹ
    test-pad-output-driver =
      normalizeTo! (p S.⊗₁ r) (q S.⊗₁ r)
                   (mkRule (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) padC ∷ []) 2

    test-pad-intermediate : pᴹ ⊗₁ (gᴹ ∘ rᴹ) ≈ qᴹ ⊗₁ (gᴹ ∘ rᴹ)
    test-pad-intermediate =
      rewriteDeepTo! (p S.⊗₁ (g S.∘ r)) (q S.⊗₁ (g S.∘ r))
                     (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) 0 padC

    test-pad-intermediate-context : pᴹ ⊗₁ (gᴹ ∘ rᴹ) ≈ qᴹ ⊗₁ (gᴹ ∘ rᴹ)
    test-pad-intermediate-context =
      rewriteH! (p S.⊗₁ (g S.∘ r)) (q S.⊗₁ (g S.∘ r))
                (S.λ⇐ S.∘ (S.id {a} S.⊗₁ r)) ((S.id {b} S.⊗₁ g) S.∘ S.λ⇒)
                (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) padC

    test-pad-two-cores-0 : (pᴹ ⊗₁ rᴹ) ⊗₁ pᴹ ≈ (qᴹ ⊗₁ rᴹ) ⊗₁ pᴹ
    test-pad-two-cores-0 =
      rewriteDeepTo! ((p S.⊗₁ r) S.⊗₁ p) ((q S.⊗₁ r) S.⊗₁ p)
                     (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) 0 padC

    test-pad-two-cores-1 : (pᴹ ⊗₁ rᴹ) ⊗₁ pᴹ ≈ (pᴹ ⊗₁ rᴹ) ⊗₁ qᴹ
    test-pad-two-cores-1 =
      rewriteDeepTo! ((p S.⊗₁ r) S.⊗₁ p) ((p S.⊗₁ r) S.⊗₁ q)
                     (p S.⊗₁ S.id {c}) (q S.⊗₁ S.id {c}) 1 padC

  module _ (pq : pᴹ ≈ qᴹ) where

    test-unpadded-0 : (pᴹ ⊗₁ rᴹ) ⊗₁ pᴹ ≈ (qᴹ ⊗₁ rᴹ) ⊗₁ pᴹ
    test-unpadded-0 = rewriteDeepTo! ((p S.⊗₁ r) S.⊗₁ p) ((q S.⊗₁ r) S.⊗₁ p) p q 0 pq

    test-unpadded-1 : (pᴹ ⊗₁ rᴹ) ⊗₁ pᴹ ≈ (pᴹ ⊗₁ rᴹ) ⊗₁ qᴹ
    test-unpadded-1 = rewriteDeepTo! ((p S.⊗₁ r) S.⊗₁ p) ((p S.⊗₁ r) S.⊗₁ q) p q 1 pq

  module _ (grow : pᴹ ⊗₁ id {C₀} ≈ qᴹ ⊗₁ (rᴹ ∘ gᴹ)) where

    test-pad-repeated-0 : pᴹ ⊗₁ (rᴹ ⊗₁ rᴹ) ≈ qᴹ ⊗₁ ((rᴹ ∘ (gᴹ ∘ rᴹ)) ⊗₁ rᴹ)
    test-pad-repeated-0 =
      rewriteDeepTo! (p S.⊗₁ (r S.⊗₁ r)) (q S.⊗₁ ((r S.∘ (g S.∘ r)) S.⊗₁ r))
                     (p S.⊗₁ S.id {c}) (q S.⊗₁ (r S.∘ g)) 0 grow

    test-pad-repeated-1 : pᴹ ⊗₁ (rᴹ ⊗₁ rᴹ) ≈ qᴹ ⊗₁ (rᴹ ⊗₁ (rᴹ ∘ (gᴹ ∘ rᴹ)))
    test-pad-repeated-1 =
      rewriteDeepTo! (p S.⊗₁ (r S.⊗₁ r)) (q S.⊗₁ (r S.⊗₁ (r S.∘ (g S.∘ r))))
                     (p S.⊗₁ S.id {c}) (q S.⊗₁ (r S.∘ g)) 1 grow

  module _ (growL : id {C₀} ⊗₁ (pᴹ ⊗₁ id {C₀}) ≈ (rᴹ ∘ gᴹ) ⊗₁ (qᴹ ⊗₁ id {C₀})) where

    test-pad-nested-aligned : rᴹ ⊗₁ (pᴹ ⊗₁ rᴹ) ≈ (rᴹ ∘ (gᴹ ∘ rᴹ)) ⊗₁ (qᴹ ⊗₁ rᴹ)
    test-pad-nested-aligned =
      rewriteDeepTo! (r S.⊗₁ (p S.⊗₁ r)) ((r S.∘ (g S.∘ r)) S.⊗₁ (q S.⊗₁ r))
                     (S.id {c} S.⊗₁ (p S.⊗₁ S.id {c}))
                     ((r S.∘ g) S.⊗₁ (q S.⊗₁ S.id {c})) 0 growL

    test-pad-nested-crossed : rᴹ ⊗₁ (pᴹ ⊗₁ rᴹ) ≈ rᴹ ⊗₁ (qᴹ ⊗₁ (rᴹ ∘ (gᴹ ∘ rᴹ)))
    test-pad-nested-crossed =
      rewriteDeepTo! (r S.⊗₁ (p S.⊗₁ r)) (r S.⊗₁ (q S.⊗₁ (r S.∘ (g S.∘ r))))
                     (S.id {c} S.⊗₁ (p S.⊗₁ S.id {c}))
                     ((r S.∘ g) S.⊗₁ (q S.⊗₁ S.id {c})) 1 growL

  module _ (padCD : id {C₀} ⊗₁ (id {D} ⊗₁ pᴹ) ≈ id {C₀} ⊗₁ (id {D} ⊗₁ qᴹ)) where

    test-pad-left-stack : rᴹ ⊗₁ (gᴹ ⊗₁ pᴹ) ≈ rᴹ ⊗₁ (gᴹ ⊗₁ qᴹ)
    test-pad-left-stack =
      rewriteDeepTo! (r S.⊗₁ (g S.⊗₁ p)) (r S.⊗₁ (g S.⊗₁ q))
                     (S.id {c} S.⊗₁ (S.id {d} S.⊗₁ p))
                     (S.id {c} S.⊗₁ (S.id {d} S.⊗₁ q)) 1 padCD

  module _ (selfL : rᴹ ⊗₁ id {C₀} ≈ rᴹ ⊗₁ (rᴹ ∘ gᴹ)) where

    test-pad-skip-upstream : (rᴹ ∘ gᴹ) ⊗₁ id {C₀} ≈ (rᴹ ∘ gᴹ) ⊗₁ (rᴹ ∘ gᴹ)
    test-pad-skip-upstream =
      rewriteDeepTo! ((r S.∘ g) S.⊗₁ S.id {c}) ((r S.∘ g) S.⊗₁ (r S.∘ g))
                     (r S.⊗₁ S.id {c}) (r S.⊗₁ (r S.∘ g)) 0 selfL

  module _ (scalar : zᴹ ⊗₁ id {C₀} ≈ zᴹ ⊗₁ (rᴹ ∘ gᴹ)) where

    test-pad-scalar : zᴹ ⊗₁ rᴹ ≈ zᴹ ⊗₁ (rᴹ ∘ (gᴹ ∘ rᴹ))
    test-pad-scalar =
      rewriteDeepTo! (z S.⊗₁ r) (z S.⊗₁ (r S.∘ (g S.∘ r)))
                     (z S.⊗₁ S.id {c}) (z S.⊗₁ (r S.∘ g)) 0 scalar

--------------------------------------------------------------------------------
-- normalize! / normalizeTo!: unit laws, zero fuel and reflexive-rule starvation
--------------------------------------------------------------------------------
module MonoidNormalize (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open Atom1 A

  open Solver C objects (((a ⊗₀ a) , a , mᴹ) ∷ (unitᵗ , a , uᴹ) ∷ [])

  private
    m u : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))

  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒) (unitLawʳ : mᴹ ∘ (id ⊗₁ uᴹ) ≈ ρ⇒) where

    private
      rules : List Rule
      rules = mkRule (m S.∘ (u S.⊗₁ S.id)) S.λ⇒ unitLawˡ
            ∷ mkRule (m S.∘ (S.id S.⊗₁ u)) S.ρ⇒ unitLawʳ
            ∷ []

    -- Extra fuel leaves the endpoint unchanged after both unit rewrites.
    test-normalize-pair
      : (mᴹ ∘ (uᴹ ⊗₁ id)) ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id)) ≈ λ⇒ ⊗₁ λ⇒
    test-normalize-pair =
      normalizeTo! ((m S.∘ (u S.⊗₁ S.id)) S.⊗₁ (m S.∘ (u S.⊗₁ S.id)))
                   (S.λ⇒ S.⊗₁ S.λ⇒)
                   (mkRule (m S.∘ (u S.⊗₁ S.id)) S.λ⇒ unitLawˡ ∷ []) 3

    -- Nested redexes require both unit laws.
    test-normalize-both
      : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ λ⇒ ∘ (id ⊗₁ ρ⇒)
    test-normalize-both =
      normalizeTo! (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))
                   (S.λ⇒ S.∘ (S.id S.⊗₁ S.ρ⇒))
                   rules 3

    -- Same rules and fuel, with the endpoint inferred.
    test-normalize-open : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ _
    test-normalize-open =
      normalize! rules 3 (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))

    -- A reflexive first rule consumes fuel before the unit law can fire.
    test-normalize-reflexive-starves
      : mᴹ ∘ (uᴹ ⊗₁ id) ≈ mᴹ ∘ (uᴹ ⊗₁ id)
    test-normalize-reflexive-starves =
      normalizeTo! (m S.∘ (u S.⊗₁ S.id)) (m S.∘ (u S.⊗₁ S.id))
                   (mkRule m m C.Equiv.refl ∷ rules) 2

    -- A reflexive root rule starves the unit rule: the final coherence gate
    -- fails. Removing that head lets one step reach λ⇒.

    -- normalize-reflexive-misses-unit : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒
    -- normalize-reflexive-misses-unit =
    --   normalizeTo! (m S.∘ (u S.⊗₁ S.id)) S.λ⇒
    --                (mkRule (m S.∘ (u S.⊗₁ S.id))
    --                        (m S.∘ (u S.⊗₁ S.id)) C.Equiv.refl ∷ rules) 1

    normalize-without-reflexive : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒
    normalize-without-reflexive =
      normalizeTo! (m S.∘ (u S.⊗₁ S.id)) S.λ⇒ rules 1

--------------------------------------------------------------------------------
-- rewriteDeepTo!: Frobenius formulations (TensorRocq §5, arXiv:2604.17592)
--------------------------------------------------------------------------------

module FrobeniusAlgebra (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  (nᴹ : A C.⇒ (A C.⊗₀ A)) (vᴹ : A C.⇒ C.unit)
  where

  open Atom1 A

  open Solver C objects
    (((a ⊗₀ a) , a , mᴹ) ∷ (unitᵗ , a , uᴹ) ∷ (a , (a ⊗₀ a) , nᴹ) ∷ (a , unitᵗ , vᴹ) ∷ [])

  private
    -- The counit remains in the signature but is unused by these laws.
    m u n : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))
    n = S.Agen (gen (suc (suc zero)))

    unitLᵗ : S.HomTerm (unitᵗ S.⊗₀ a) a
    unitLᵗ = m S.∘ (u S.⊗₁ S.id)

    assocLᵗ assocRᵗ : S.HomTerm ((a S.⊗₀ a) S.⊗₀ a) a
    assocLᵗ = m S.∘ (m S.⊗₁ S.id)
    assocRᵗ = m S.∘ (S.id S.⊗₁ m) S.∘ S.α⇒

    Xᵗ Yᵗ : S.HomTerm (a S.⊗₀ a) (a S.⊗₀ a)
    Xᵗ = (S.id S.⊗₁ m) S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id)
    Yᵗ = (m S.⊗₁ S.id) S.∘ S.α⇐ S.∘ (S.id S.⊗₁ n)

    T₁ T₂ T₃ T₄ : S.HomTerm (a S.⊗₀ a) (a S.⊗₀ a)
    T₁ = (m S.⊗₁ m) S.∘ S.α⇐ S.∘ (S.id S.⊗₁ S.α⇒)
           S.∘ (u S.⊗₁ (n S.⊗₁ S.id)) S.∘ S.λ⇐
    T₂ = (S.id S.⊗₁ m) S.∘ (S.id S.⊗₁ (m S.⊗₁ S.id)) S.∘ (S.id S.⊗₁ S.α⇐)
           S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id) S.∘ (u S.⊗₁ S.id) S.∘ S.λ⇐
    T₃ = (S.id S.⊗₁ m) S.∘ (S.id S.⊗₁ (S.id S.⊗₁ m))
           S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id) S.∘ (u S.⊗₁ S.id) S.∘ S.λ⇐
    T₄ = (m S.⊗₁ S.id) S.∘ S.α⇐ S.∘ (u S.⊗₁ n) S.∘ S.λ⇐ S.∘ m

  module _
    (unitL  : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒)
    (assocH : mᴹ ∘ (mᴹ ⊗₁ id) ≈ mᴹ ∘ (id ⊗₁ mᴹ) ∘ α⇒)
    (frobH  : (id ⊗₁ mᴹ) ∘ α⇒ ∘ (nᴹ ⊗₁ id) ≈ (mᴹ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ nᴹ))
    where

    private
      step₁ : ⟦ T₁ ⟧₁ C.≈ ⟦ Xᵗ ⟧₁
      step₁ = rewriteDeepTo! T₁ Xᵗ unitLᵗ S.λ⇒ 0 unitL

      step₂ : ⟦ T₁ ⟧₁ C.≈ ⟦ T₂ ⟧₁
      step₂ = rewriteDeepTo! T₁ T₂ Yᵗ Xᵗ 0 (C.Equiv.sym frobH)

      step₃ : ⟦ T₂ ⟧₁ C.≈ ⟦ T₃ ⟧₁
      step₃ = rewriteDeepTo! T₂ T₃ assocLᵗ assocRᵗ 0 assocH

      step₄ : ⟦ T₃ ⟧₁ C.≈ ⟦ T₄ ⟧₁
      step₄ = rewriteDeepTo! T₃ T₄ Xᵗ Yᵗ 0 frobH

      step₅ : ⟦ T₄ ⟧₁ C.≈ ⟦ n S.∘ m ⟧₁
      step₅ = rewriteDeepTo! T₄ (n S.∘ m) unitLᵗ S.λ⇒ 0 unitL

    open C.HomReasoning

    frobL : (id ⊗₁ mᴹ) ∘ α⇒ ∘ (nᴹ ⊗₁ id) ≈ nᴹ ∘ mᴹ
    frobL = ⟺ step₁ ○ step₂ ○ step₃ ○ step₄ ○ step₅

    frobR : (mᴹ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ nᴹ) ≈ nᴹ ∘ mᴹ
    frobR = ⟺ frobH ○ frobL

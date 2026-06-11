{-# OPTIONS --safe #-}

module Categories.GradedKleisli where

open import Level renaming (zero to ℓ0)

open import Relation.Binary using (IsEquivalence)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal
open import Categories.Functor hiding (id)
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded
open import Categories.NaturalTransformation hiding (id)
open import Categories.Tactic.Category

import Categories.Morphism.Reasoning as MR
import Categories.Category.Monoidal.Reasoning as MonR

open import Data.Fin
open import Data.Product
open import Data.Vec using (_∷_; [])

open import Categories.MonoidalCoherence

record UC-model : Set₁ where
  field C : Category ℓ0 ℓ0 ℓ0
        I : MonoidalCategory ℓ0 ℓ0 ℓ0
        M : GradedMonad I C
        ℰ : Presheaf C (Sets ℓ0)

module _ {o ℓ e : Level}
         (C : Category o ℓ e) (I : MonoidalCategory ℓ0 ℓ0 ℓ0)
         (M : GradedKleisliTriple I C) where

  private
    module C = Category C
    module I = MonoidalCategory I

  open C using () renaming (id to idC; _∘_ to _∘C_; _≈_ to _≈C_; _⇒_ to _⇒C_)
  open I using (unit; _⊗₀_; _⊗₁_; -⊗_; _⊗-) renaming (id to idI; _∘_ to _∘I_; _≈_ to _≈I_; _⇒_ to _⇒I_)
  open Functor
  open GradedKleisliTriple M
  open import Categories.Category.Monoidal.Utilities I.monoidal
  open Shorthands

  private
    module CR where
      open C.HomReasoning public
      open MR C public
    module IR where
      open MonR I.monoidal public
      open MR I.U public

  -- ─────────────────────────────────────────────────────────────────────
  -- The data of the graded-Kleisli category. Objects pair a grade with a
  -- C-object; a hom (i , c) ⇒ (j , d) is a Kleisli map c ⇒ T₀ k d at some
  -- grade k, together with a grade morphism i ⊗ k ⇒ j absorbing k into
  -- the bookkeeping.
  -- ─────────────────────────────────────────────────────────────────────

  GKObj : Set o
  GKObj = I.Obj × C.Obj

  GKHom : GKObj → GKObj → Set ℓ
  GKHom (i , c) (j , d) = ∃[ k ] (c ⇒C T₀ k d) × (i ⊗₀ k ⇒I j)

  GKid : ∀ {X} → GKHom X X
  GKid = unit , return , ρ⇒

  GK∘ : ∀ {X Y Z} → GKHom Y Z → GKHom X Y → GKHom X Z
  GK∘ (j , g , β) (i , f , α) =
    i ⊗₀ j , μ i j ∘C T₁ i g ∘C f , β ∘I ₁ (-⊗ j) α ∘I α⇐

  -- ─────────────────────────────────────────────────────────────────────
  -- Hom equivalence. The natural notion of "same morphism at a coarser
  -- grade" is the *directed* subsumption GK≲: a grade morphism φ
  -- translating one representative into the other. This relation is
  -- reflexive and transitive but not symmetric (φ need not be
  -- invertible), so the hom-setoid equality GK≈ pairs a subsumption with
  -- one in the opposite direction. All structural laws are witnessed by
  -- coherence isomorphisms, whose directed proofs reverse generically
  -- (≲-flip below).
  -- ─────────────────────────────────────────────────────────────────────

  GK≲ : ∀ {X Y} → GKHom X Y → GKHom X Y → Set e
  GK≲ {ai , _} (i , f , α) (j , g , β) =
    Σ[ φ ∈ i ⇒I j ] (sub φ ∘C f ≈C g) × (β ∘I ₁ (ai ⊗-) φ ≈I α)

  GK≈ : ∀ {X Y} → GKHom X Y → GKHom X Y → Set e
  GK≈ F G = GK≲ F G × GK≲ G F

  ≲-refl : ∀ {X Y} {F : GKHom X Y} → GK≲ F F
  ≲-refl {ai , _} {F = i , f , α} =
      idI
    , (let open CR in elimˡ sub-identity)
    , (let open IR in elimʳ (identity (ai ⊗-)))

  ≲-trans : ∀ {X Y} {F G H : GKHom X Y} → GK≲ F G → GK≲ G H → GK≲ F H
  ≲-trans {ai , _} {F = i , f , α} {j , g , β} {k , h , γ}
          (φ₁ , p₁ , q₁) (φ₂ , p₂ , q₂) =
      φ₂ ∘I φ₁
    , (let open CR in begin
        sub (φ₂ ∘I φ₁) ∘C f          ≈⟨ pushˡ sub-homomorphism ⟩
        sub φ₂ ∘C (sub φ₁ ∘C f)      ≈⟨ refl⟩∘⟨ p₁ ⟩
        sub φ₂ ∘C g                  ≈⟨ p₂ ⟩
        h                            ∎)
    , (let open IR in begin
        γ ∘I ₁ (ai ⊗-) (φ₂ ∘I φ₁)              ≈⟨ refl⟩∘⟨ homomorphism (ai ⊗-) ⟩
        γ ∘I (₁ (ai ⊗-) φ₂ ∘I ₁ (ai ⊗-) φ₁)    ≈⟨ pullˡ q₂ ⟩
        β ∘I ₁ (ai ⊗-) φ₁                      ≈⟨ q₁ ⟩
        α                                      ∎)

  -- A directed subsumption whose grade morphism is invertible reverses.
  ≲-flip : ∀ {X Y} {F G : GKHom X Y}
         → (P : GK≲ F G) (ψ : proj₁ G ⇒I proj₁ F)
         → proj₁ P ∘I ψ ≈I idI
         → ψ ∘I proj₁ P ≈I idI
         → GK≲ G F
  ≲-flip {ai , _} {F = i , f , α} {j , g , β} (φ , p , q) ψ isoʳ isoˡ =
      ψ
    , (let open CR in begin
        sub ψ ∘C g             ≈⟨ refl⟩∘⟨ ⟺ p ⟩
        sub ψ ∘C (sub φ ∘C f)  ≈⟨ pullˡ (⟺ sub-homomorphism) ⟩
        sub (ψ ∘I φ) ∘C f      ≈⟨ elimˡ (sub-resp-≈ isoˡ ○ sub-identity) ⟩
        f                      ∎)
    , (let open IR in begin
        α ∘I ₁ (ai ⊗-) ψ                    ≈⟨ ⟺ q ⟩∘⟨refl ⟩
        (β ∘I ₁ (ai ⊗-) φ) ∘I ₁ (ai ⊗-) ψ   ≈⟨ pullʳ (⟺ (homomorphism (ai ⊗-))) ⟩
        β ∘I ₁ (ai ⊗-) (φ ∘I ψ)             ≈⟨ elimʳ (F-resp-≈ (ai ⊗-) isoʳ ○ identity (ai ⊗-)) ⟩
        β                                   ∎)

  GK-equiv : ∀ {X Y} → IsEquivalence (GK≈ {X} {Y})
  GK-equiv = record
    { refl  = ≲-refl , ≲-refl
    ; sym   = swap
    ; trans = λ where (p⁺ , p⁻) (q⁺ , q⁻) → ≲-trans p⁺ q⁺ , ≲-trans q⁻ p⁻
    }

  -- ─────────────────────────────────────────────────────────────────────
  -- Directed structural laws. The C-side equations come from the graded
  -- triple (ext-identityʳ, ext-assoc, ext-T-fusion, sub-commute); the
  -- I-side ones are monoidal coherence (discharged by the solver) plus
  -- naturality of the associator.
  -- ─────────────────────────────────────────────────────────────────────

  ≲-identityˡ : ∀ {X Y} {F : GKHom X Y} → GK≲ (GK∘ GKid F) F
  ≲-identityˡ {ai , _} {F = i , f , α} =
      ρ⇒
    , (let open CR in begin
        sub ρ⇒ ∘C (μ i unit ∘C T₁ i return ∘C f)
          ≈⟨ solve C ⟩
        (sub ρ⇒ ∘C μ i unit ∘C T₁ i return) ∘C f
          ≈⟨ μ-identityʳ ⟩∘⟨refl ⟩
        idC ∘C f
          ≈⟨ solve C ⟩
        f ∎)
    , (let open IR
           module S = Solver I (ai ∷ i ∷ []) in begin
        α ∘I ₁ (ai ⊗-) ρ⇒
          ≈⟨ refl⟩∘⟨ (S.solveM {Y = S.Var (# 0) S.⊗₀ S.Var (# 1)}
               (S.id S.⊗₁ S.ρ⇒) (S.ρ⇒ S.∘ S.α⇐)) ⟩
        α ∘I (ρ⇒ ∘I α⇐)
          ≈⟨ solve I.U ⟩
        (α ∘I ρ⇒) ∘I α⇐
          ≈⟨ I.unitorʳ-commute-from ⟩∘⟨refl ⟨
        (ρ⇒ ∘I ₁ (-⊗ unit) α) ∘I α⇐
          ≈⟨ solve I.U ⟩
        ρ⇒ ∘I ₁ (-⊗ unit) α ∘I α⇐ ∎)

  ≲-identityʳ : ∀ {X Y} {F : GKHom X Y} → GK≲ (GK∘ F GKid) F
  ≲-identityʳ {ai , _} {F = i , f , α} =
      λ⇒
    , (let open CR in begin
        sub λ⇒ ∘C (μ unit i ∘C T₁ unit f ∘C return)
          ≈⟨ refl⟩∘⟨ pullˡ ext-T-fusion ⟩
        sub λ⇒ ∘C (ext unit (idC ∘C f) ∘C return)
          ≈⟨ refl⟩∘⟨ (ext-resp-≈ C.identityˡ ⟩∘⟨refl) ⟩
        sub λ⇒ ∘C (ext unit f ∘C return)
          ≈⟨ ext-identityʳ ⟩
        f ∎)
    , (let open IR
           module S = Solver I (ai ∷ i ∷ []) in begin
        α ∘I ₁ (ai ⊗-) λ⇒
          ≈⟨ refl⟩∘⟨ (S.solveM {Y = S.Var (# 0) S.⊗₀ S.Var (# 1)}
               (S.id S.⊗₁ S.λ⇒) ((S.ρ⇒ S.⊗₁ S.id) S.∘ S.α⇐)) ⟩
        α ∘I ₁ (-⊗ i) ρ⇒ ∘I α⇐ ∎)

  ≲-assoc : ∀ {W X Y Z} {F : GKHom W X} {G : GKHom X Y} {H : GKHom Y Z}
          → GK≲ (GK∘ (GK∘ H G) F) (GK∘ H (GK∘ G F))
  ≲-assoc {aw , _} {ax , _} {ay , _} {az , _} {i , f , α} {j , g , β} {k , h , γ} =
      α⇐
    , C-side
    , I-side
    where
      -- idC ∘ (μ ∘ T₁ h ∘ g) ≈ ext h ∘ g, used under `ext i` below.
      inner : idC ∘C (μ j k ∘C T₁ j h ∘C g) ≈C ext j h ∘C g
      inner = let open CR in
        C.identityˡ ○ pullˡ ext-T-fusion ○ (ext-resp-≈ C.identityˡ ⟩∘⟨refl)

      -- μ/T₁ composites reduce to Kleisli extension form.
      outer : μ (i ⊗₀ j) k ∘C T₁ (i ⊗₀ j) h ∘C (μ i j ∘C T₁ i g ∘C f)
                ≈C ext (i ⊗₀ j) h ∘C ext i g ∘C f
      outer = let open CR in
            pullˡ ext-T-fusion
          ○ (ext-resp-≈ C.identityˡ ⟩∘⟨refl)
          ○ (refl⟩∘⟨ (pullˡ ext-T-fusion ○ (ext-resp-≈ C.identityˡ ⟩∘⟨refl)))

      C-side = let open CR in begin
        sub α⇐ ∘C (μ i (j ⊗₀ k) ∘C T₁ i (μ j k ∘C T₁ j h ∘C g) ∘C f)
          ≈⟨ refl⟩∘⟨ pullˡ ext-T-fusion ⟩
        sub α⇐ ∘C (ext i (idC ∘C (μ j k ∘C T₁ j h ∘C g)) ∘C f)
          ≈⟨ refl⟩∘⟨ (ext-resp-≈ inner ⟩∘⟨refl) ⟩
        sub α⇐ ∘C (ext i (ext j h ∘C g) ∘C f)
          ≈⟨ refl⟩∘⟨ (ext-assoc ⟩∘⟨refl) ⟩
        sub α⇐ ∘C ((sub α⇒ ∘C ext (i ⊗₀ j) h ∘C ext i g) ∘C f)
          ≈⟨ solve C ⟩
        (sub α⇐ ∘C sub α⇒) ∘C ext (i ⊗₀ j) h ∘C ext i g ∘C f
          ≈⟨ elimˡ (⟺ sub-homomorphism ○ sub-resp-≈ I.associator.isoˡ ○ sub-identity) ⟩
        ext (i ⊗₀ j) h ∘C ext i g ∘C f
          ≈⟨ outer ⟨
        μ (i ⊗₀ j) k ∘C T₁ (i ⊗₀ j) h ∘C (μ i j ∘C T₁ i g ∘C f) ∎

      -- Naturality of the associator against α, padded by identities.
      nat : ₁ (-⊗ k) (₁ (-⊗ j) α) ∘I α⇐ ≈I α⇐ ∘I ₁ (-⊗ (j ⊗₀ k)) α
      nat = let open IR in begin
        ₁ (-⊗ k) (₁ (-⊗ j) α) ∘I α⇐
          ≈⟨ I.assoc-commute-to ⟨
        α⇐ ∘I (α ⊗₁ (idI ⊗₁ idI))
          ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ identity I.⊗) ⟩
        α⇐ ∘I ₁ (-⊗ (j ⊗₀ k)) α ∎

      I-side = let open IR
                   module S = Solver I (aw ∷ i ∷ j ∷ k ∷ []) in begin
        (γ ∘I ₁ (-⊗ k) (β ∘I ₁ (-⊗ j) α ∘I α⇐) ∘I α⇐) ∘I ₁ (aw ⊗-) α⇐
          ≈⟨ (refl⟩∘⟨ ((homomorphism (-⊗ k) ○ (refl⟩∘⟨ homomorphism (-⊗ k))) ⟩∘⟨refl)) ⟩∘⟨refl ⟩
        (γ ∘I (₁ (-⊗ k) β ∘I ₁ (-⊗ k) (₁ (-⊗ j) α) ∘I ₁ (-⊗ k) α⇐) ∘I α⇐) ∘I ₁ (aw ⊗-) α⇐
          ≈⟨ solve I.U ⟩
        γ ∘I ₁ (-⊗ k) β ∘I ₁ (-⊗ k) (₁ (-⊗ j) α) ∘I (₁ (-⊗ k) α⇐ ∘I α⇐ ∘I ₁ (aw ⊗-) α⇐)
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨
               (S.solveM
                 {X = S.Var (# 0) S.⊗₀ (S.Var (# 1) S.⊗₀ (S.Var (# 2) S.⊗₀ S.Var (# 3)))}
                 {Y = ((S.Var (# 0) S.⊗₀ S.Var (# 1)) S.⊗₀ S.Var (# 2)) S.⊗₀ S.Var (# 3)}
                 ((S.α⇐ S.⊗₁ S.id) S.∘ (S.α⇐ S.∘ (S.id S.⊗₁ S.α⇐)))
                 (S.α⇐ S.∘ S.α⇐)))) ⟩
        γ ∘I ₁ (-⊗ k) β ∘I ₁ (-⊗ k) (₁ (-⊗ j) α) ∘I (α⇐ ∘I α⇐)
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ pullˡ nat) ⟩
        γ ∘I ₁ (-⊗ k) β ∘I ((α⇐ ∘I ₁ (-⊗ (j ⊗₀ k)) α) ∘I α⇐)
          ≈⟨ solve I.U ⟩
        (γ ∘I ₁ (-⊗ k) β ∘I α⇐) ∘I ₁ (-⊗ (j ⊗₀ k)) α ∘I α⇐ ∎

  ≲-∘-resp : ∀ {X Y Z} {F G : GKHom Y Z} {H K : GKHom X Y}
           → GK≲ F G → GK≲ H K → GK≲ (GK∘ F H) (GK∘ G K)
  ≲-∘-resp {a₁ , _} {a₂ , _} {a₃ , _} {F = i , f , α} {j , g , β} {H = k , h , γ} {l , m , δ}
           (φ , p , q) (ψ , r , s) =
      ψ ⊗₁ φ
    , C-side
    , I-side
    where
      C-side = let open CR in begin
        sub (ψ ⊗₁ φ) ∘C (μ k i ∘C T₁ k f ∘C h)
          ≈⟨ refl⟩∘⟨ pullˡ ext-T-fusion ⟩
        sub (ψ ⊗₁ φ) ∘C (ext k (idC ∘C f) ∘C h)
          ≈⟨ refl⟩∘⟨ (ext-resp-≈ C.identityˡ ⟩∘⟨refl) ⟩
        sub (ψ ⊗₁ φ) ∘C (ext k f ∘C h)
          ≈⟨ pullˡ (⟺ sub-commute) ⟩
        (ext l (sub φ ∘C f) ∘C sub ψ) ∘C h
          ≈⟨ (ext-resp-≈ p ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (ext l g ∘C sub ψ) ∘C h
          ≈⟨ pullʳ r ⟩
        ext l g ∘C m
          ≈⟨ pullˡ ext-T-fusion ○ (ext-resp-≈ C.identityˡ ⟩∘⟨refl) ⟨
        μ l j ∘C T₁ l g ∘C m ∎

      merge : ₁ (-⊗ j) δ ∘I ((idI ⊗₁ ψ) ⊗₁ φ) ≈I γ ⊗₁ φ
      merge = let open IR in ⟺ ⊗-distrib-over-∘ ○ (s ⟩⊗⟨ I.identityˡ)

      I-side = let open IR in begin
        (β ∘I ₁ (-⊗ j) δ ∘I α⇐) ∘I ₁ (a₁ ⊗-) (ψ ⊗₁ φ)
          ≈⟨ solve I.U ⟩
        β ∘I ₁ (-⊗ j) δ ∘I (α⇐ ∘I ₁ (a₁ ⊗-) (ψ ⊗₁ φ))
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ I.assoc-commute-to) ⟩
        β ∘I ₁ (-⊗ j) δ ∘I (((idI ⊗₁ ψ) ⊗₁ φ) ∘I α⇐)
          ≈⟨ refl⟩∘⟨ pullˡ merge ⟩
        β ∘I ((γ ⊗₁ φ) ∘I α⇐)
          ≈⟨ refl⟩∘⟨ (serialize₂₁ ⟩∘⟨refl) ⟩
        β ∘I (((idI ⊗₁ φ) ∘I (γ ⊗₁ idI)) ∘I α⇐)
          ≈⟨ solve I.U ⟩
        (β ∘I (idI ⊗₁ φ)) ∘I (γ ⊗₁ idI) ∘I α⇐
          ≈⟨ q ⟩∘⟨refl ⟩
        α ∘I ₁ (-⊗ i) γ ∘I α⇐ ∎

  GradedKleisli : Category o ℓ e
  GradedKleisli = categoryHelper record
    { Obj       = GKObj
    ; _⇒_       = GKHom
    ; _≈_       = GK≈
    ; id        = GKid
    ; _∘_       = GK∘
    ; assoc     = ≲-assoc , ≲-flip ≲-assoc α⇒ I.associator.isoˡ I.associator.isoʳ
    ; identityˡ = ≲-identityˡ , ≲-flip ≲-identityˡ ρ⇐ I.unitorʳ.isoʳ I.unitorʳ.isoˡ
    ; identityʳ = ≲-identityʳ , ≲-flip ≲-identityʳ λ⇐ I.unitorˡ.isoʳ I.unitorˡ.isoˡ
    ; equiv     = GK-equiv
    ; ∘-resp-≈  = λ where (p⁺ , p⁻) (q⁺ , q⁻) → ≲-∘-resp p⁺ q⁺ , ≲-∘-resp p⁻ q⁻
    }

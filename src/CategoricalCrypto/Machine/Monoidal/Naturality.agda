{-# OPTIONS --safe #-}

-- ============================================================================
-- The Kleisli shuffles `∘ᴷ-fwd` and `⊗ᴷ-fwd` are natural.
--
-- Both shuffles are composites of associators and symmetries
-- (`Machine.Monoidal.Coherence`), and the machine category is symmetric
-- monoidal (`Machine.MonoidalCategory`), so each law is an instance of the
-- naturality of the structural isomorphisms.  The bookkeeping is left to the
-- symmetric coherence solver of `Categories.Coherence.Monoidal`: the abstract
-- machines are opaque generators, and the solver slides them through the
-- structural maps.
-- ============================================================================

module CategoricalCrypto.Machine.Monoidal.Naturality where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Fin using (#_)
open import Data.Vec using (_∷_; [])

open import Categories.Category using (Category)
open import Categories.Coherence.Monoidal using (module SymAtoms; module SymSolve)
open import Categories.FreeMonoidal using (v≤v)   -- the instance that enables `S.σ`

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal.Coherence
  using (∘ᴷ-fwd-decomp; ⊗ᴷ-fwd-decomp; mid4-decomp)
open import CategoricalCrypto.Machine.MonoidalCategory

open Category MachineCategory using (module HomReasoning)
open HomReasoning

-- ----------------------------------------------------------------------------
-- `∘ᴷ-fwd` is natural.
-- ----------------------------------------------------------------------------

∘ᴷ-fwd-natural : ∀ {C C' E₁ E₁' E₂ E₂'}
                 (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
               → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd)
                 ≅ᴹ (∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
∘ᴷ-fwd-natural {C} {C'} {E₁} {E₁'} {E₂} {E₂'} c u₁ u₂ = begin
    (c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd
  ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl ∘ᴷ-fwd-decomp ⟩
    (c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ((CC.id ⊗₁ ⊗-symₘ) CC.∘ ⊗-assoc)
  ≈⟨ solveMorσ! lhs rhs ⟩
    ((CC.id ⊗₁ ⊗-symₘ) CC.∘ ⊗-assoc) CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁)
  ≈⟨ ∘-resp-≅ᴹ (≅ᴹ-sym ∘ᴷ-fwd-decomp) ≅ᴹ-refl ⟩
    ∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁)
  ∎
  where
  vars = C ∷ C' ∷ E₁ ∷ E₁' ∷ E₂ ∷ E₂' ∷ []
  open SymAtoms machine-monoidal-category machine-symmetric vars
  open SymSolve machine-monoidal-category machine-symmetric vars
    ( ((V (# 0) , V (# 1)) , c)
    ∷ ((V (# 2) , V (# 3)) , u₁)
    ∷ ((V (# 4) , V (# 5)) , u₂) ∷ [] )
  lhs = (gen (# 0) S.⊗₁ (gen (# 1) S.⊗₁ gen (# 2)))
        S.∘ ((S.id {V (# 0)} S.⊗₁ S.σ {V (# 4)} {V (# 2)}) S.∘ S.α⇒ {V (# 0)} {V (# 4)} {V (# 2)})
  rhs = ((S.id {V (# 1)} S.⊗₁ S.σ {V (# 5)} {V (# 3)}) S.∘ S.α⇒ {V (# 1)} {V (# 5)} {V (# 3)})
        S.∘ ((gen (# 0) S.⊗₁ gen (# 2)) S.⊗₁ gen (# 1))

-- ----------------------------------------------------------------------------
-- `⊗ᴷ-fwd` is natural.
-- ----------------------------------------------------------------------------

⊗ᴷ-fwd-natural : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                 (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                 (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
               → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd)
                 ≅ᴹ (⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
⊗ᴷ-fwd-natural {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ = begin
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd
  ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-trans ⊗ᴷ-fwd-decomp mid4-decomp) ⟩
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ mid4-core
  ≈⟨ solveMorσ! lhs rhs ⟩
    mid4-core CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ≈⟨ ∘-resp-≅ᴹ (≅ᴹ-sym (≅ᴹ-trans ⊗ᴷ-fwd-decomp mid4-decomp)) ≅ᴹ-refl ⟩
    ⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ∎
  where
  mid4-core : ∀ {P Q R S} → Machine ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
  mid4-core = ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))) CC.∘ ⊗-assoc)
  vars = B₁ ∷ B₁' ∷ E₁ ∷ E₁' ∷ B₂ ∷ B₂' ∷ E₂ ∷ E₂' ∷ []
  open SymAtoms machine-monoidal-category machine-symmetric vars
  open SymSolve machine-monoidal-category machine-symmetric vars
    ( ((V (# 0) , V (# 1)) , b₁)
    ∷ ((V (# 2) , V (# 3)) , u₁)
    ∷ ((V (# 4) , V (# 5)) , b₂)
    ∷ ((V (# 6) , V (# 7)) , u₂) ∷ [] )
  -- `mid4-core` in the term language, at atoms `p q r s`.
  core : (p q r s : ObjTerm) → S.HomTerm ((p ⊗ᵒ q) ⊗ᵒ (r ⊗ᵒ s)) ((p ⊗ᵒ r) ⊗ᵒ (q ⊗ᵒ s))
  core p q r s =
    S.α⇐ {p} {r} {q ⊗ᵒ s}
    S.∘ ((S.id {p} S.⊗₁ (S.α⇒ {r} {q} {s} S.∘ ((S.σ {q} {r} S.⊗₁ S.id {s}) S.∘ S.α⇐ {q} {r} {s})))
         S.∘ S.α⇒ {p} {q} {r ⊗ᵒ s})
  lhs = ((gen (# 0) S.⊗₁ gen (# 2)) S.⊗₁ (gen (# 1) S.⊗₁ gen (# 3)))
        S.∘ core (V (# 0)) (V (# 2)) (V (# 4)) (V (# 6))
  rhs = core (V (# 1)) (V (# 3)) (V (# 5)) (V (# 7))
        S.∘ ((gen (# 0) S.⊗₁ gen (# 1)) S.⊗₁ (gen (# 2) S.⊗₁ gen (# 3)))

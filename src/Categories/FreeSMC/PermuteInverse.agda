{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- `permute-inverse-left` at the `d`-level: `permute (↭-sym p) ∘ permute p
-- ≈Term id`.  Ported (unconditional) from the APROP-level
-- `Discharge/Sub/PermuteCoherenceFin.agda`; its proof uses only `permute`,
-- the FreeMonoidal axioms, and `σ-block-{involutive,natural₃}` — all of
-- which are now available at the `d`-level (the σ-block lemmas via the
-- generalised `SigmaBlockHexagon`).
--
-- Plus the `permute-via-vlab` corollary `pvv-inverse-left` (the cancel
-- tool the `swap-core` faithfulness-route uses for the input permutes).
--
-- `--safe`.  No postulates.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.PermuteInverse
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d
open import Categories.FreeSMC.Steps d using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon d
  using (σ-block-involutive; σ-block-natural₃)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## `permute (↭-sym p) ∘ permute p ≈ id`.

permute-inverse-left
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → permute (Perm.↭-sym p) ∘ permute p ≈Term id
permute-inverse-left Perm.refl = idˡ
permute-inverse-left (Perm.prep x p) =
  ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
  (≈-Term-trans (⊗-resp-≈ idˡ (permute-inverse-left p))
                id⊗id≈id)
permute-inverse-left (Perm.swap x y p) =
  let f   = permute p
      f⁻¹ = permute (Perm.↭-sym p)
      ih  = permute-inverse-left p
  in begin
       ((id ⊗₁ (id ⊗₁ f⁻¹)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ assoc ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f)))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ-block-natural₃ ≈-Term-refl) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ (id ⊗₁ (id ⊗₁ f))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-block-involutive) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (id ⊗₁ (id ⊗₁ f)) ∘ id
         ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (id ⊗₁ (id ⊗₁ f))
         ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
       (id ∘ id) ⊗₁ ((id ⊗₁ f⁻¹) ∘ (id ⊗₁ f))
         ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
       id ⊗₁ ((id ∘ id) ⊗₁ (f⁻¹ ∘ f))
         ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ih) ⟩
       id ⊗₁ (id ⊗₁ id)
         ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎
permute-inverse-left (Perm.trans p₁ p₂) =
  let ih₁ = permute-inverse-left p₁
      ih₂ = permute-inverse-left p₂
  in ≈-Term-trans assoc
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym assoc)
                                  (∘-resp-≈ ih₂ ≈-Term-refl)))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ) ih₁))

--------------------------------------------------------------------------------
-- ## `map⁺` commutes with `↭-sym` (so `permute-inverse-left` lifts to
-- `permute-via-vlab`).

map⁺-sym
  : ∀ {n} (vlab : Fin n → X) {xs ys : List (Fin n)} (p : xs Perm.↭ ys)
  → PermProp.map⁺ vlab (Perm.↭-sym p) ≡ Perm.↭-sym (PermProp.map⁺ vlab p)
map⁺-sym vlab Perm.refl         = refl
map⁺-sym vlab (Perm.prep x p)   = cong (Perm.prep (vlab x)) (map⁺-sym vlab p)
map⁺-sym vlab (Perm.swap x y p) = cong (Perm.swap (vlab y) (vlab x)) (map⁺-sym vlab p)
map⁺-sym vlab (Perm.trans p q)  =
  cong₂ Perm.trans (map⁺-sym vlab q) (map⁺-sym vlab p)
  where open import Relation.Binary.PropositionalEquality using (cong₂)

--------------------------------------------------------------------------------
-- ## `permute-via-vlab` corollary.

pvv-inverse-left
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X) (p : xs Perm.↭ ys)
  → permute-via-vlab vlab (Perm.↭-sym p) ∘ permute-via-vlab vlab p ≈Term id
pvv-inverse-left vlab p
  rewrite map⁺-sym vlab p = permute-inverse-left (PermProp.map⁺ vlab p)

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Step ① foundation: the `σ-block` / `braid` keystone at the
-- `FreeMonoidalData` level (ported from the APROP-parameterised
-- `APROP/.../Discharge/Sub/{SigmaBlockHexagon,BraidBlock}.agda`, whose
-- bodies use only `FreeMonoidal` + the σ axioms).
--
-- Provides:
--   * `σ-block`            — braid one object past a nested pair.
--   * `σ-block-natural₁`   — a generator in the braided slot slides
--                            through one σ-block (from σ∘[f⊗g]≈[g⊗f]∘σ).
--   * `braid` / `braid-natural` — the iterated version: a generator
--                            slides through a braiding of a whole block.
--
-- This is the machinery `swap-core` needs, now available at the generic
-- `d` level (the swap-core slide additionally needs the block-σ ≈
-- atom-`permute` bridge, the remaining step-① work).
--
-- `--safe`.  No postulates.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.BraidBlock
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.Category using (Category)
open import Data.List using (List; []; _∷_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

-- `σ-block` and its slot-1 naturality now come from the (generalised)
-- `SigmaBlockHexagon` so there is a single source of truth shared with
-- the σ-block-⊗ development.
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SigmaBlockHexagon d
  using (σ-block; σ-block-natural₁) public

--------------------------------------------------------------------------------
-- ## Iterated block braiding (move A past a list of objects).

nest : List ObjTerm → ObjTerm → ObjTerm
nest []       T = T
nest (B ∷ Bs) T = B ⊗₀ nest Bs T

nest-tail-map
  : ∀ (Bs : List ObjTerm) {T T' : ObjTerm}
  → HomTerm T T' → HomTerm (nest Bs T) (nest Bs T')
nest-tail-map []       f = f
nest-tail-map (B ∷ Bs) f = id {A = B} ⊗₁ nest-tail-map Bs f

braid
  : ∀ (A : ObjTerm) (Bs : List ObjTerm) (T : ObjTerm)
  → HomTerm (A ⊗₀ nest Bs T) (nest Bs (A ⊗₀ T))
braid A []       T = id
braid A (B ∷ Bs) T = (id {A = B} ⊗₁ braid A Bs T) ∘ σ-block {A} {B} {nest Bs T}

--------------------------------------------------------------------------------
-- ## The keystone: a generator slides through a whole block braiding.

braid-natural
  : ∀ {A A' : ObjTerm} (f : HomTerm A A') (Bs : List ObjTerm) (T : ObjTerm)
  → braid A' Bs T ∘ (f ⊗₁ id {A = nest Bs T})
    ≈Term nest-tail-map Bs (f ⊗₁ id {A = T}) ∘ braid A Bs T
braid-natural f []       T = ≈-Term-trans idˡ (≈-Term-sym idʳ)
braid-natural {A} {A'} f (B ∷ Bs) T = begin
    braid A' (B ∷ Bs) T ∘ (f ⊗₁ id {A = nest (B ∷ Bs) T})
      ≡⟨⟩
    ((id {A = B} ⊗₁ braid A' Bs T) ∘ σ-block {A'} {B} {nest Bs T})
      ∘ (f ⊗₁ id {A = B ⊗₀ nest Bs T})
      ≈⟨ assoc ⟩
    (id {A = B} ⊗₁ braid A' Bs T)
      ∘ (σ-block {A'} {B} {nest Bs T} ∘ (f ⊗₁ id {A = B ⊗₀ nest Bs T}))
      ≈⟨ ∘-resp-≈ ≈-Term-refl σ-block-natural₁ ⟩
    (id {A = B} ⊗₁ braid A' Bs T)
      ∘ ((id {A = B} ⊗₁ (f ⊗₁ id {A = nest Bs T})) ∘ σ-block {A} {B} {nest Bs T})
      ≈⟨ ≈-Term-sym assoc ⟩
    ((id {A = B} ⊗₁ braid A' Bs T) ∘ (id {A = B} ⊗₁ (f ⊗₁ id {A = nest Bs T})))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl ⟩
    ((id {A = B} ∘ id {A = B}) ⊗₁ (braid A' Bs T ∘ (f ⊗₁ id {A = nest Bs T})))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (⊗-resp-≈ idˡ (braid-natural f Bs T)) ≈-Term-refl ⟩
    (id {A = B} ⊗₁ (nest-tail-map Bs (f ⊗₁ id {A = T}) ∘ braid A Bs T))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist)
                   ≈-Term-refl ⟩
    ((id {A = B} ⊗₁ nest-tail-map Bs (f ⊗₁ id {A = T}))
       ∘ (id {A = B} ⊗₁ braid A Bs T))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ assoc ⟩
    (id {A = B} ⊗₁ nest-tail-map Bs (f ⊗₁ id {A = T}))
      ∘ ((id {A = B} ⊗₁ braid A Bs T) ∘ σ-block {A} {B} {nest Bs T})
      ≡⟨⟩
    nest-tail-map (B ∷ Bs) (f ⊗₁ id {A = T}) ∘ braid A (B ∷ Bs) T
  ∎

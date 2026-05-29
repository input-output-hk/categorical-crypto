{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- KEYSTONE for the atom-(1) reduction (route 1).
--
-- `braid` moves a single object `A` rightward past a right-nested block
-- of objects `Bs`, leaving a tail `T` fixed:
--
--   braid A Bs T : A ⊗ nest Bs T  →  nest Bs (A ⊗ T)
--
-- built by iterating `σ-block` (from `SigmaBlockHexagon`), one σ per
-- block element.
--
-- `braid-natural` is THE workhorse the swap-atom chase needs: a
-- generator `f : A → A'` sitting in the braided slot slides through the
-- whole block braiding, ending up in the tail position:
--
--   braid A' Bs T ∘ (f ⊗ id)  ≈Term  nest-tail-map Bs (f ⊗ id) ∘ braid A Bs T
--
-- This is proved by induction on `Bs` using ONLY:
--   * `σ-block-natural₁`  (itself derived from σ∘[f⊗g]≈[g⊗f]∘σ + α-coherence)
--   * `⊗-∘-dist`, identity laws, associativity.
--
-- NO new postulate.  NO σ-naturality applied between two generators —
-- σ only ever moves a generator past a *braiding*, which is the axiom.
-- This is the constructive heart of why atom (1) reduces to
-- {axioms + permute-faithfulness} with no extra trust.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BraidBlock
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon
  asFreeMonoidalData
  using (σ-block; σ-block-natural₁)

open import Categories.Category using (Category)
open import Data.List using (List; []; _∷_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Right-nested tensor of a block over a tail.

nest : List ObjTerm → ObjTerm → ObjTerm
nest []       T = T
nest (B ∷ Bs) T = B ⊗₀ nest Bs T

-- Lift a tail morphism through the (identity-on-block) nest.
nest-tail-map
  : ∀ (Bs : List ObjTerm) {T T' : ObjTerm}
  → HomTerm T T' → HomTerm (nest Bs T) (nest Bs T')
nest-tail-map []       f = f
nest-tail-map (B ∷ Bs) f = id {B} ⊗₁ nest-tail-map Bs f

--------------------------------------------------------------------------------
-- ## The block braiding: move A past Bs (tail T fixed).

braid
  : ∀ (A : ObjTerm) (Bs : List ObjTerm) (T : ObjTerm)
  → HomTerm (A ⊗₀ nest Bs T) (nest Bs (A ⊗₀ T))
braid A []       T = id
braid A (B ∷ Bs) T = (id {B} ⊗₁ braid A Bs T) ∘ σ-block {A} {B} {nest Bs T}

--------------------------------------------------------------------------------
-- ## The keystone naturality.

braid-natural
  : ∀ {A A' : ObjTerm} (f : HomTerm A A') (Bs : List ObjTerm) (T : ObjTerm)
  → braid A' Bs T ∘ (f ⊗₁ id {nest Bs T})
    ≈Term nest-tail-map Bs (f ⊗₁ id {T}) ∘ braid A Bs T
braid-natural f []       T = ≈-Term-trans idˡ (≈-Term-sym idʳ)
braid-natural {A} {A'} f (B ∷ Bs) T = begin
    braid A' (B ∷ Bs) T ∘ (f ⊗₁ id {nest (B ∷ Bs) T})
      ≡⟨⟩
    ((id {B} ⊗₁ braid A' Bs T) ∘ σ-block {A'} {B} {nest Bs T})
      ∘ (f ⊗₁ id {B ⊗₀ nest Bs T})
      ≈⟨ assoc ⟩
    (id {B} ⊗₁ braid A' Bs T)
      ∘ (σ-block {A'} {B} {nest Bs T} ∘ (f ⊗₁ id {B ⊗₀ nest Bs T}))
      ≈⟨ ∘-resp-≈ ≈-Term-refl σ-block-natural₁ ⟩
    (id {B} ⊗₁ braid A' Bs T)
      ∘ ((id {B} ⊗₁ (f ⊗₁ id {nest Bs T})) ∘ σ-block {A} {B} {nest Bs T})
      ≈⟨ ≈-Term-sym assoc ⟩
    ((id {B} ⊗₁ braid A' Bs T) ∘ (id {B} ⊗₁ (f ⊗₁ id {nest Bs T})))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl ⟩
    ((id {B} ∘ id {B}) ⊗₁ (braid A' Bs T ∘ (f ⊗₁ id {nest Bs T})))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (⊗-resp-≈ idˡ (braid-natural f Bs T)) ≈-Term-refl ⟩
    (id {B} ⊗₁ (nest-tail-map Bs (f ⊗₁ id {T}) ∘ braid A Bs T))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ ∘-resp-≈ (≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist)
                   ≈-Term-refl ⟩
    ((id {B} ⊗₁ nest-tail-map Bs (f ⊗₁ id {T}))
       ∘ (id {B} ⊗₁ braid A Bs T))
      ∘ σ-block {A} {B} {nest Bs T}
      ≈⟨ assoc ⟩
    (id {B} ⊗₁ nest-tail-map Bs (f ⊗₁ id {T}))
      ∘ ((id {B} ⊗₁ braid A Bs T) ∘ σ-block {A} {B} {nest Bs T})
      ≡⟨⟩
    nest-tail-map (B ∷ Bs) (f ⊗₁ id {T}) ∘ braid A (B ∷ Bs) T
  ∎

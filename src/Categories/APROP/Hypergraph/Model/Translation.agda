{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation from APROP terms to hypergraphs. Pruned composition aligns
-- vertex counts across the ≈Term laws.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.Translation (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality

open APROP sig
open FreeMonoidalHelper Symm X using (flatten)

private
  variable
    A B : ObjTerm

⟪_⟫     : HomTerm A B → Hypergraph FlatGen
⟪⟫-domL : (f : HomTerm A B) → domL ⟪ f ⟫ ≡ flatten A
⟪⟫-codL : (f : HomTerm A B) → codL ⟪ f ⟫ ≡ flatten B

⟪ Agen f ⟫            = hGen f
⟪ id {A} ⟫            = hId A
⟪ g ∘ f ⟫             = hComposeP ⟪ f ⟫ ⟪ g ⟫
                                   (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
⟪ f ⊗₁ g ⟫            = hTensor ⟪ f ⟫ ⟪ g ⟫
⟪ λ⇒ {A} ⟫            = hId A
⟪ λ⇐ {A} ⟫            = hId A
⟪ ρ⇒ {A} ⟫            = hId (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫            = hId (A ⊗₀ unit)
⟪ α⇒ {A}{B}{C} ⟫      = hId ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A}{B}{C} ⟫      = hId ((A ⊗₀ B) ⊗₀ C)
⟪ σ {A}{B} ⟫          = hSwap A B

⟪⟫-domL (Agen f)        = domL-hGen f
⟪⟫-domL (id {A})        = domL-hId A
⟪⟫-domL (g ∘ f)         =
  trans (domL-hComposeP ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g))))
        (⟪⟫-domL f)

⟪⟫-domL (f ⊗₁ g)        = trans (domL-hTensor ⟪ f ⟫ ⟪ g ⟫)
                                 (cong₂ _++_ (⟪⟫-domL f) (⟪⟫-domL g))

⟪⟫-domL (λ⇒ {A})        = domL-hId A
⟪⟫-domL (λ⇐ {A})        = domL-hId A
⟪⟫-domL (ρ⇒ {A})        = domL-hId (A ⊗₀ unit)
⟪⟫-domL (ρ⇐ {A})        = trans (domL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))

⟪⟫-domL (α⇒ {A}{B}{C})  = domL-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-domL (α⇐ {A}{B}{C})  = trans (domL-hId ((A ⊗₀ B) ⊗₀ C))
                                 (++-assoc (flatten A) (flatten B) (flatten C))

⟪⟫-domL (σ {A}{B})      = domL-hSwap A B

⟪⟫-codL (Agen f)        = codL-hGen f
⟪⟫-codL (id {A})        = codL-hId A
⟪⟫-codL (g ∘ f)         =
  trans (codL-hComposeP ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g))))
        (⟪⟫-codL g)

⟪⟫-codL (f ⊗₁ g)        = trans (codL-hTensor ⟪ f ⟫ ⟪ g ⟫)
                                 (cong₂ _++_ (⟪⟫-codL f) (⟪⟫-codL g))

⟪⟫-codL (λ⇒ {A})        = codL-hId A
⟪⟫-codL (λ⇐ {A})        = codL-hId A
⟪⟫-codL (ρ⇒ {A})        = trans (codL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))

⟪⟫-codL (ρ⇐ {A})        = codL-hId (A ⊗₀ unit)
⟪⟫-codL (α⇒ {A}{B}{C})  = trans (codL-hId ((A ⊗₀ B) ⊗₀ C))
                                 (++-assoc (flatten A) (flatten B) (flatten C))

⟪⟫-codL (α⇐ {A}{B}{C})  = codL-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-codL (σ {A}{B})      = codL-hSwap A B

-- Mark `⟪_⟫` injective for inference: lets Agda solve the implicit term
-- args of a focused goal like `∀ {A B C D} → ⟪ LHS ⟫ ≅ᴴ ⟪ RHS ⟫` by
-- inverting `⟪_⟫` on the goal's `⟪ LHS ⟫`.
{-# INJECTIVE_FOR_INFERENCE ⟪_⟫ #-}

-- Structural constructors all translate to hId, so one handler serves them.
-- Keep subterms in the composite handlers: consumers may need another
-- predicate's proof about them, not only this recursor's result.

module _ {ℓ} (Q : Hypergraph FlatGen → Set ℓ)
  (q-gen  : ∀ {A B} (g : mor A B) → Q (hGen g))
  (q-id   : ∀ A → Q (hId A))
  (q-com  : ∀ {A B C} (f : HomTerm A B) (g : HomTerm B C)
            → Q ⟪ f ⟫ → Q ⟪ g ⟫ → Q ⟪ g ∘ f ⟫)
  (q-ten  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
            → Q ⟪ f ⟫ → Q ⟪ g ⟫ → Q ⟪ f ⊗₁ g ⟫)
  (q-swap : ∀ A B → Q (hSwap A B))
  where

  HomTermRec : (f : HomTerm A B) → Q ⟪ f ⟫
  HomTermRec (Agen g)        = q-gen g
  HomTermRec (id {A})        = q-id A
  HomTermRec (g ∘ f)         = q-com f g (HomTermRec f) (HomTermRec g)
  HomTermRec (f ⊗₁ g)        = q-ten f g (HomTermRec f) (HomTermRec g)
  HomTermRec (λ⇒ {A})        = q-id A
  HomTermRec (λ⇐ {A})        = q-id A
  HomTermRec (ρ⇒ {A})        = q-id (A ⊗₀ unit)
  HomTermRec (ρ⇐ {A})        = q-id (A ⊗₀ unit)
  HomTermRec (α⇒ {A}{B}{C})  = q-id ((A ⊗₀ B) ⊗₀ C)
  HomTermRec (α⇐ {A}{B}{C})  = q-id ((A ⊗₀ B) ⊗₀ C)
  HomTermRec (σ {A}{B})      = q-swap A B

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation ⟪_⟫ : HomTerm → Hypergraph using the PRUNED `hComposeP`.
--
-- Same as `FromAPROP.⟪_⟫` except `∘` uses `hComposeP` (Option A) rather
-- than `hCompose`. This version enables the group-(b)/(c) ≈Term axioms
-- (idˡ, idʳ, etc.) where the LHS would otherwise have strictly more
-- vertices than the RHS due to unreachable K-side dom vertices.
--
-- Separate file because `FromAPROP` can't import `PrunedCompose` — the
-- latter imports `FromAPROP` for `FlatGen`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Translation (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hGen; hId; hTensor; hSwap)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)

open import Data.List using (List; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)

--------------------------------------------------------------------------------
-- Translation from APROP terms.
--
-- Structurally identical to the original `FromAPROP.⟪_⟫`, except `∘`
-- dispatches to `hComposeP` for the canonical pruned cospan composition.

-- Mutual definition: `⟪_⟫` produces an unindexed hypergraph; the
-- boundary lemmas `⟪⟫-domL`/`⟪⟫-codL` witness that its `domL`/`codL`
-- agree with the term's source/target via `flatten`.

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (domL-hId; codL-hId; domL-hTensor; codL-hTensor;
         domL-hSwap; codL-hSwap; domL-hGen; codL-hGen)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (domL-hComposeP; codL-hComposeP)

⟪_⟫     : ∀ {A B} → HomTerm A B → Hypergraph FlatGen
⟪⟫-domL : ∀ {A B} (f : HomTerm A B) → domL ⟪ f ⟫ ≡ flatten A
⟪⟫-codL : ∀ {A B} (f : HomTerm A B) → codL ⟪ f ⟫ ≡ flatten B

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

-- Mark `⟪_⟫` injective for type inference.  Without this, dispatching a
-- focused postulate like `pentagon-sound : ∀ {A B C D} → ⟪ LHS ⟫ ≅ᴴ
-- ⟪ RHS ⟫` can't solve the implicit {A B C D} from the goal's `⟪ LHS ⟫`
-- expression, because Agda can't invert `⟪_⟫` otherwise.  With this
-- pragma, `⟪ f₁ ⟫ = ⟪ f₂ ⟫` is taken to imply `f₁ = f₂`.
{-# INJECTIVE_FOR_INFERENCE ⟪_⟫ #-}

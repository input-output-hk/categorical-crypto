{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable propositional equality on `Diag`.
--
-- Matching `_≡_` on `Diag` directly is blocked by index unification on the
-- `pre ++ (a ++ suf)` cons index. Routing the decision through a first-order
-- `encode` and its injectivity `encode-inj` sidesteps that.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Compare where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt
import Data.Product.Properties as ProdProp
open import Function using () renaming (_∘_ to _∙f_)

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal

module CompareI {X : Set} (Mor : List X → List X → Set) ⦃ _ : DecEq X ⦄ where

  open DiagramI Mor

  Gen : Set
  Gen = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  private
    variable n n' m m' : List X

    gen : ∀ {a b} → Mor a b → Gen
    gen {a} {b} f = a , b , f

  module Decide ⦃ _ : DecEq Gen ⦄ where

    private
      -- one layer, first-order: offset, suffix, and the generator triple.
      LayerE : Set
      LayerE = List X × (List X × Gen)

      encode : ∀ {n m} → Diag n m → List LayerE
      encode ([]_ n)               = []
      encode (pre ▸ suf ∷ f ⟨ d ⟩) = (pre , suf , gen f) ∷ encode d

      -- `encode` is injective on equal-endpoint diagrams.  The `[]`-diagonal
      -- ties both endpoints, so exactly one of the two endpoint equations can
      -- be refl-matched; the other goes through Hedberg UIP on `List X`.
      encode-inj : (d : Diag n m) (d' : Diag n' m') (en : n ≡ n') (em : m ≡ m')
                 → encode d ≡ encode d' → substDiagᵒ em (substDiag en d) ≡ d'
      encode-inj ([]_ n) ([]_ n') refl em _ rewrite ListExt.≡-irrelevant _≟_ em refl = refl
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en refl ee with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl rewrite ListExt.≡-irrelevant _≟_ en refl =
              cong (pre ▸ suf ∷ f ⟨_⟩) (encode-inj d d' refl refl te)

    infix 4 _≟Diag_

    _≟Diag_ : (d d' : Diag n m) → Dec (d ≡ d')
    _≟Diag_ d d' = case encode d ≟ encode d' of λ where
      (yes ee) → yes (encode-inj d d' refl refl ee)
      (no  e≢) → no λ eq → e≢ (cong encode eq)

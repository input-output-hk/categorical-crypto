{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable normal-form equality on `Diag`.
--
-- `_≟Diag_` decides the heterogeneous structural relation `_≈NF_` on
-- `Diag n m` / `Diag n' m'` (possibly different endpoints); `≈NF⇒≡` collapses
-- a witness at equal endpoints to a genuine `≡`.  Deciding propositional `≡`
-- directly is blocked by index unification on the `pre ++ (a ++ suf)` cons
-- index; routing through `_≈NF_` (whose constructors only relate same-endpoint
-- diagrams) and a first-order `encode` sidesteps it `--without-K`-safely.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Compare where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt
import Data.Product.Properties as ProdProp
open import Function using () renaming (_∘_ to _∙f_)

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal

module CompareI {v : Variant} {X : Set}
  (E : WireEngine v)
  ⦃ _ : DecEq X ⦄
  where

  open WireEngine E
  open DiagramI E

  Gen : Set
  Gen = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  private
    variable n n' m m' : List X

    gen : ∀ {a b} → Mor a b → Gen
    gen {a} {b} f = a , b , f

  module Decide ⦃ _ : DecEq Gen ⦄ where

    infix 4 _≈NF_
    data _≈NF_ : Diag n m → Diag n' m' → Set where
      nf[] : ∀ {n} → ([]_ n) ≈NF ([]_ n)
      nf∷  : ∀ {a b m} {pre suf : List X}
               {d d' : Diag (pre ++ (b ++ suf)) m} (f : Mor a b)
           → d ≈NF d'
           → (pre ▸ suf ∷ f ⟨ d ⟩) ≈NF (pre ▸ suf ∷ f ⟨ d' ⟩)

    -- The decision goes through a FIRST-ORDER layer encoding: deciding the
    -- encoded layer lists avoids every match against the `++`-composite
    -- indices.

    private
      -- one layer, first-order: offset, suffix, and the generator triple.
      LayerE : Set
      LayerE = List X × (List X × Gen)

      encode : ∀ {n m} → Diag n m → List LayerE
      encode ([]_ n)               = []
      encode (pre ▸ suf ∷ f ⟨ d ⟩) = (pre , suf , gen f) ∷ encode d

      ≈NF⇒width : {d : Diag n m} {d' : Diag n' m'} → d ≈NF d' → n ≡ n'
      ≈NF⇒width nf[]        = refl
      ≈NF⇒width (nf∷ _ _)   = refl

      ≈NF⇒cod : {d : Diag n m} {d' : Diag n' m'} → d ≈NF d' → m ≡ m'
      ≈NF⇒cod nf[]        = refl
      ≈NF⇒cod (nf∷ _ _)   = refl

      -- `encode` is injective on equal-endpoint diagrams.  The recursion is
      -- driven by the input index; one residual endpoint equation refl-matches
      -- at a variable index, the other is discharged by the Hedberg UIP on
      -- `List X` (the `[]`-diagonal ties both output and input, so exactly one
      -- can be matched).
      encode-inj : (d : Diag n m) (d' : Diag n' m') (en : n ≡ n') (em : m ≡ m')
                 → encode d ≡ encode d' → substDiagᵒ em (substDiag en d) ≡ d'
      encode-inj ([]_ n) ([]_ n') refl em _ rewrite ListExt.≡-irrelevant _≟_ em refl = refl
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en refl ee with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl rewrite ListExt.≡-irrelevant _≟_ en refl =
              cong (pre ▸ suf ∷ f ⟨_⟩) (encode-inj d d' refl refl te)

      ≈NF-refl : (d : Diag n m) → d ≈NF d
      ≈NF-refl ([]_ n)               = nf[]
      ≈NF-refl (pre ▸ suf ∷ f ⟨ d ⟩) = nf∷ f (≈NF-refl d)

      ≈NF⇒encode : {d : Diag n m} {d' : Diag n' m'} → d ≈NF d' → encode d ≡ encode d'
      ≈NF⇒encode nf[]       = refl
      ≈NF⇒encode (nf∷ _ eq) = cong (_ ∷_) (≈NF⇒encode eq)

      encode⇒≈NF : {d : Diag n m} {d' : Diag n' m'}
                 → n ≡ n' → m ≡ m' → encode d ≡ encode d' → d ≈NF d'
      encode⇒≈NF {d = d} {d'} refl refl ee =
        subst (d ≈NF_) (encode-inj d d' refl refl ee) (≈NF-refl d)

    infix 4 _≟Diag_

    _≟Diag_ : (d : Diag n m) (d' : Diag n' m') → Dec (d ≈NF d')
    _≟Diag_ {n} {m} {n'} {m'} d d' = case n ≟ n' of λ where
      (no  n≢) → no λ eq → n≢ (≈NF⇒width eq)
      (yes en) → case m ≟ m' of λ where
        (no  m≢) → no λ eq → m≢ (≈NF⇒cod eq)
        (yes em) → case encode d ≟ encode d' of λ where
          (yes ee) → yes (encode⇒≈NF en em ee)
          (no  e≢) → no λ eq → e≢ (≈NF⇒encode eq)

    ≈NF⇒≡ : {d d' : Diag n m} → d ≈NF d' → d ≡ d'
    ≈NF⇒≡ {d = d} {d' = d'} eq = encode-inj d d' refl refl (≈NF⇒encode eq)

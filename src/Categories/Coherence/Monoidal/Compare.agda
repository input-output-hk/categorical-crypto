{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable normal-form equality on `DiagU`, abstracting the label set, the
-- generator family, and the box interpretation as module parameters.
--
-- `_≟DiagU_` decides the heterogeneous structural relation `_≈NF_` on
-- `DiagU n m` / `DiagU n' m'` (possibly different endpoints); `≈NF⇒≡` collapses
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

module SolverCompareI
  {v : Variant} {X : Set}
  (E : WireEngine v {X})
  (_≟X_ : DecidableEquality X)
  where

  open WireEngine E

  open UntypedI E

  -- the "same generator" test: a box `f : Mor a b` is identified by the
  -- dependent triple `(a , b , f) : Gen`, decided by the caller's `_≟Gen_`.
  Gen : Set
  Gen = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  private
    _≟L_ : DecidableEquality (List X)
    _≟L_ = ≡-dec _≟X_

    gen : ∀ {a b} → Mor a b → Gen
    gen {a} {b} f = a , b , f

  module Decide (_≟Gen_ : DecidableEquality Gen) where

    --------------------------------------------------------------------------------
    -- (A) Decidable normal-form equality on `DiagU`
    --------------------------------------------------------------------------------
    --
    -- The *heterogeneous* structural relation `_≈NF_` is defined by data so its
    -- constructors never force the unification `pre' ++ (a' ++ suf') ≟
    -- pre ++ (a ++ suf)` (`_++_` is not injective, so the homogeneous `≡` split
    -- is `UnificationStuck`).  Its constructors only relate same-width diagrams,
    -- so `_≈NF_` is observationally `≡`; callers chain the `≈Term` soundness.
    infix 4 _≈NF_

    data _≈NF_ : ∀ {n n' m m'} → DiagU n m → DiagU n' m' → Set where
      nf[] : ∀ {n} → ([]_ n) ≈NF ([]_ n)
      nf∷  : ∀ {a b m} {pre suf : List X}
               {d d' : DiagU (pre ++ (b ++ suf)) m} (f : Mor a b)
           → d ≈NF d'
           → (pre ▸ suf ∷ f ⟨ d ⟩) ≈NF (pre ▸ suf ∷ f ⟨ d' ⟩)

    -- The decision goes through a FIRST-ORDER layer encoding: deciding the
    -- encoded layer lists avoids every match against the `++`-composite
    -- indices.  Matching `_≈NF_`/`DiagU` constructors happens only at
    -- variable indices (never against a `++`-composite index), so the procedure
    -- is `--without-K`-compatible.

    private
      -- the two related diagrams have equal input width.
      ≈NF⇒width : ∀ {n n' m m'} {d : DiagU n m} {d' : DiagU n' m'} → d ≈NF d' → n ≡ n'
      ≈NF⇒width nf[]        = refl
      ≈NF⇒width (nf∷ _ _)   = refl

      -- and equal output width.
      ≈NF⇒cod : ∀ {n n' m m'} {d : DiagU n m} {d' : DiagU n' m'} → d ≈NF d' → m ≡ m'
      ≈NF⇒cod nf[]        = refl
      ≈NF⇒cod (nf∷ _ _)   = refl

      -- one layer, first-order: offset, suffix, and the generator triple.
      LayerE : Set
      LayerE = List X × (List X × Gen)

      encode : ∀ {n m} → DiagU n m → List LayerE
      encode ([]_ n)               = []
      encode (pre ▸ suf ∷ f ⟨ d ⟩) = (pre , suf , gen f) ∷ encode d

      _≟E_ : DecidableEquality (List LayerE)
      _≟E_ = ≡-dec (ProdProp.≡-dec _≟L_ (ProdProp.≡-dec _≟L_ _≟Gen_))

      -- an ≈NF witness yields equal encodings.
      ≈NF⇒encode : ∀ {n n' m m'} {d : DiagU n m} {d' : DiagU n' m'}
                 → d ≈NF d' → encode d ≡ encode d'
      ≈NF⇒encode nf[]       = refl
      ≈NF⇒encode (nf∷ _ eq) = cong (_ ∷_) (≈NF⇒encode eq)

      -- `encode` is injective on equal-endpoint diagrams.  The recursion is
      -- driven by the input index; one residual endpoint equation refl-matches
      -- at a variable index, the other is discharged by the Hedberg UIP on
      -- `List X` (the `[]`-diagonal ties both output and input, so exactly one
      -- can be matched).
      encode-inj : ∀ {n n' m m'} (d : DiagU n m) (d' : DiagU n' m')
                   (en : n ≡ n') (em : m ≡ m')
                 → encode d ≡ encode d' → substDiagUᵒ em (substDiagU en d) ≡ d'
      encode-inj ([]_ n) ([]_ n') refl em _
        rewrite ListExt.≡-irrelevant _≟X_ em refl = refl
      encode-inj ([]_ n) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) _ _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) ([]_ n') _ _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en refl ee
        with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl rewrite ListExt.≡-irrelevant _≟X_ en refl =
              cong (λ z → pre ▸ suf ∷ f ⟨ z ⟩) (encode-inj d d' refl refl te)

      -- reflexivity of `_≈NF_` (used to derive encode⇒≈NF).
      ≈NF-refl : ∀ {n m} (d : DiagU n m) → d ≈NF d
      ≈NF-refl ([]_ n)               = nf[]
      ≈NF-refl (pre ▸ suf ∷ f ⟨ d ⟩) = nf∷ f (≈NF-refl d)

      -- equal endpoints + equal encodings rebuild an ≈NF witness, derived from
      -- encode-inj (injectivity) and ≈NF-refl (reflexivity).
      encode⇒≈NF : ∀ {n n' m m'} (d : DiagU n m) (d' : DiagU n' m')
                 → n ≡ n' → m ≡ m' → encode d ≡ encode d' → d ≈NF d'
      encode⇒≈NF d d' refl refl ee =
        subst (d ≈NF_) (encode-inj d d' refl refl ee) (≈NF-refl d)

    infix 4 _≟DiagU_

    _≟DiagU_ : ∀ {n n' m m'} (d : DiagU n m) (d' : DiagU n' m') → Dec (d ≈NF d')
    _≟DiagU_ {n} {n'} {m} {m'} d d' = case n ≟L n' of λ where
      (no  n≢) → no λ eq → n≢ (≈NF⇒width eq)
      (yes en) → case m ≟L m' of λ where
        (no  m≢) → no λ eq → m≢ (≈NF⇒cod eq)
        (yes em) → case encode d ≟E encode d' of λ where
          (yes ee) → yes (encode⇒≈NF d d' en em ee)
          (no  e≢) → no λ eq → e≢ (≈NF⇒encode eq)

    ≈NF⇒≡ : ∀ {n m} {d d' : DiagU n m} → d ≈NF d' → d ≡ d'
    ≈NF⇒≡ {d = d} {d' = d'} eq = encode-inj d d' refl refl (≈NF⇒encode eq)

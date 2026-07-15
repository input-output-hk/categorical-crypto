{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable normal-form equality on `DiagU`, abstracting the label set, the
-- generator family, and the box interpretation as module parameters.
--
-- `_≟DiagU_` decides the heterogeneous structural relation `_≈NF_` on
-- `DiagU n` / `DiagU n'` (possibly different widths); `≈NF⇒≡` collapses a
-- witness at equal width to a genuine `≡`.  Deciding propositional `≡` directly
-- is blocked by index unification on the `pre ++ (a ++ suf)` cons index;
-- routing through `_≈NF_` (whose constructors only relate same-width diagrams)
-- and a first-order `encode` sidesteps it `--without-K`-safely.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Compare where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties using (≡-dec; ∷-injective)
import Data.List.Properties.Ext as ListExt
import Data.Product.Properties as ProdProp
open import Function using () renaming (_∘_ to _∙f_)

open import Categories.Coherence.Monoidal.Diagram using (WireEngine; module WireSig; module UntypedI; module Untyped)
open import Categories.FreeMonoidal using (Variant; module FreeMonoidalHelper)

module SolverCompareI
  {v : Variant} {X : Set}
  (E : WireEngine v {X})
  (_≟X_ : DecidableEquality X)
  where

  open WireEngine E

  -- the structural merge/split family already comes through `UntypedI`, so
  -- hide it from the second open.
  open UntypedI E
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)

  -- decidable equality on offsets (List X), from DecidableEquality X.
  _≟L_ : DecidableEquality (List X)
  _≟L_ = ≡-dec _≟X_

  -- the "same generator" test: a box `f : Mor a b` is identified by the
  -- dependent triple `(a , b , f) : Gen`, decided by the caller's `_≟Mor_`.
  Gen : Set
  Gen = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  private
    gen : ∀ {a b} → Mor a b → Gen
    gen {a} {b} f = a , b , f

  module Decide
    (_≟Mor_ : DecidableEquality Gen)   -- decide `(a,b,f) ≡ (a',b',g)` of Gen
    where

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

    data _≈NF_ : ∀ {n n'} → DiagU n → DiagU n' → Set where
      nf[] : ∀ {n} → ([]_ n) ≈NF ([]_ n)
      nf∷  : ∀ {a b} {pre suf : List X}
               {d d' : DiagU (pre ++ (b ++ suf))} (f : Mor a b)
           → d ≈NF d'
           → (pre ▸ suf ∷ f ⟨ d ⟩) ≈NF (pre ▸ suf ∷ f ⟨ d' ⟩)

    -- The decision goes through a FIRST-ORDER layer encoding: deciding the
    -- encoded layer lists avoids every match against the `++`-composite
    -- indices.  Matching `_≈NF_`/`DiagU` constructors happens only inside the
    -- two conversion lemmas, at variable indices, so the procedure is
    -- `--without-K`-compatible.

    private
      -- the two related diagrams have equal input width.
      ≈NF⇒width : ∀ {n n'} {d : DiagU n} {d' : DiagU n'} → d ≈NF d' → n ≡ n'
      ≈NF⇒width nf[]        = refl
      ≈NF⇒width (nf∷ _ _)   = refl

      -- one layer, first-order: offset, suffix, and the generator triple.
      LayerE : Set
      LayerE = List X × (List X × Gen)

      encode : ∀ {n} → DiagU n → List LayerE
      encode ([]_ n)               = []
      encode (pre ▸ suf ∷ f ⟨ d ⟩) = (pre , suf , gen f) ∷ encode d

      _≟E_ : DecidableEquality (List LayerE)
      _≟E_ = ≡-dec
               (ProdProp.≡-dec _≟L_ (ProdProp.≡-dec _≟L_ _≟Mor_))

      -- an ≈NF witness yields equal encodings.
      ≈NF⇒encode : ∀ {n n'} {d : DiagU n} {d' : DiagU n'}
                 → d ≈NF d' → encode d ≡ encode d'
      ≈NF⇒encode nf[]       = refl
      ≈NF⇒encode (nf∷ f eq) = cong (_ ∷_) (≈NF⇒encode eq)

      -- `encode` is injective on equal-width diagrams, with the residual
      -- reflexive width equation discharged by the Hedberg UIP on `List X`.
      encode-inj : ∀ {n n'} (d : DiagU n) (d' : DiagU n') (en : n ≡ n')
                 → encode d ≡ encode d' → subst DiagU en d ≡ d'
      encode-inj ([]_ n) ([]_ n') refl _ = refl
      encode-inj ([]_ n) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) ([]_ n') _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en ee
        with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl rewrite ListExt.≡-irrelevant _≟X_ en refl =
              cong (λ z → pre ▸ suf ∷ f ⟨ z ⟩) (encode-inj d d' refl te)

      -- reflexivity of `_≈NF_` (used to derive encode⇒≈NF).
      ≈NF-refl : ∀ {n} (d : DiagU n) → d ≈NF d
      ≈NF-refl ([]_ n)               = nf[]
      ≈NF-refl (pre ▸ suf ∷ f ⟨ d ⟩) = nf∷ f (≈NF-refl d)

      -- equal widths + equal encodings rebuild an ≈NF witness, derived from
      -- encode-inj (injectivity) and ≈NF-refl (reflexivity).
      encode⇒≈NF : ∀ {n n'} (d : DiagU n) (d' : DiagU n')
                 → n ≡ n' → encode d ≡ encode d' → d ≈NF d'
      encode⇒≈NF d d' refl ee = subst (d ≈NF_) (encode-inj d d' refl ee) (≈NF-refl d)

    infix 4 _≟DiagU_

    _≟DiagU_ : ∀ {n n'} (d : DiagU n) (d' : DiagU n') → Dec (d ≈NF d')
    _≟DiagU_ {n} {n'} d d' = case n ≟L n' of λ where
      (no  n≢) → no λ eq → n≢ (≈NF⇒width eq)
      (yes en) → case encode d ≟E encode d' of λ where
        (yes ee) → yes (encode⇒≈NF d d' en ee)
        (no  e≢) → no λ eq → e≢ (≈NF⇒encode eq)

    ≈NF⇒≡ : ∀ {n} {d d' : DiagU n} → d ≈NF d' → d ≡ d'
    ≈NF⇒≡ {d = d} {d' = d'} eq = encode-inj d d' refl (≈NF⇒encode eq)

--------------------------------------------------------------------------------
-- Wrapper: `SolverCompareI` at the standard interpretation `Untyped.⟦box⟧`
-- (= `var ∘ box`).
--------------------------------------------------------------------------------
module SolverCompare
  (v : Variant)
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor : List X → List X → Set)
  where

  open Untyped v {X} Mor using (⟦box⟧)
  open SolverCompareI (record { Mor = Mor ; ⟦box⟧ = ⟦box⟧ }) _≟X_ public

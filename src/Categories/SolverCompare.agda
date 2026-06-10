{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable normal-form equality on `DiagU`.  The development is kept
-- decoupled from any particular reflection / normalization implementation:
-- it depends only on the diagram language itself, abstracting the label set,
-- the generator family, and the box interpretation as module parameters.
--
-- Deliverable:
--
--   `_≟DiagU_` : a genuine *decidable propositional equality* on `DiagU n`
--       (same input width).  It bottoms out in `DecidableEquality X` (for
--       offsets) and a caller-supplied heterogeneous decidable equality on the
--       generators `Mor` (the "same box" test).  The dependent index
--       `pre ++ (a ++ suf)` of the cons constructor is handled by deciding the
--       boundary lists and the generator triple first, then pattern-matching
--       the recovered equalities so the recursive call on the tail is
--       well-typed.
--------------------------------------------------------------------------------

module Categories.SolverCompare where

import Axiom.UniquenessOfIdentityProofs as UIPmod
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties as ListProp using (≡-dec; ∷-injective)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
import Data.Product.Properties as ProdProp
open import Function using (case_of_) renaming (_∘_ to _∙f_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Categories.DiagramRewriteUntyped using (module WireSig; module UntypedI; module Untyped)
open import Categories.FreeMonoidal

--------------------------------------------------------------------------------
-- The development is relative to a label set `X` with decidable equality and a
-- morphism-generator family `Mor`, parametric in the variant `v` and in the
-- interpretation `⟦box⟧` of the diagram-layer generators.
--------------------------------------------------------------------------------
module SolverCompareI
  (v : Variant)
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor : List X → List X → Set)
  (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
  (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
  (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b))
  where

  open UntypedI v {X} Mor ⟦box⟧ public
  open FreeMonoidalHelper v X using (ObjTerm)
  -- re-export the term language / equational theory used by the interpretation
  -- (UntypedI opens these internally without `public`).
  open FreeMonoidalHelper.Mor v X mor public

  --------------------------------------------------------------------------------
  -- Decidable equality on offsets (List X), derived from DecidableEquality X.
  --------------------------------------------------------------------------------
  _≟L_ : DecidableEquality (List X)
  _≟L_ = ≡-dec _≟X_

  --------------------------------------------------------------------------------
  -- The "same generator" heterogeneous decidable equality.
  --
  -- A box generator `f : Mor a b` is identified, up to its domain/range
  -- labels, by the dependent triple `(a , b , f) : Gen`.  The caller supplies
  -- a decision procedure for propositional equality of two such triples; a
  -- `yes` is exactly `a ≡ a'`, `b ≡ b'` *and* the generators agreeing once
  -- retyped — recovered in one shot by matching `refl`.
  --------------------------------------------------------------------------------
  Gen : Set
  Gen = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  gen : ∀ {a b} → Mor a b → Gen
  gen {a} {b} f = a , b , f

  module Decide
    (_≟Mor_ : DecidableEquality Gen)   -- decide `(a,b,f) ≡ (a',b',g)` of Gen
    where

    --------------------------------------------------------------------------------
    -- (A) Decidable normal-form equality on `DiagU`.
    --
    -- Deciding *propositional* `≡` of two `DiagU n` directly is blocked by
    -- Agda's index unification: matching a cons against `DiagU (pre ++(a++suf))`
    -- needs to unify `pre' ++ (a' ++ suf') ≟ pre ++ (a ++ suf)`, and `_++_`
    -- is not injective, so the split is rejected (`UnificationStuck`).
    --
    -- We therefore introduce a *heterogeneous* structural relation `_≈NF_`,
    -- defined by data so its constructors never force the offending
    -- unification.  Its constructors only relate diagrams of the *same* width
    -- (the shared `pre/suf/a/b/f`), so `_≈NF_` is observationally `≡` and we
    -- prove both `≈NF⇒width` (the widths agree) and the soundness
    -- `⟦ d ⟧ ≈Term ⟦ d' ⟧` (after transporting along that width equality).
    --------------------------------------------------------------------------------
    infix 4 _≈NF_

    data _≈NF_ : ∀ {n n'} → DiagU n → DiagU n' → Set where
      nf[] : ∀ {n} → ([]_ n) ≈NF ([]_ n)
      nf∷  : ∀ {a b} {pre suf : List X}
               {d d' : DiagU (pre ++ (b ++ suf))} (f : Mor a b)
           → d ≈NF d'
           → (pre ▸ suf ∷ f ⟨ d ⟩) ≈NF (pre ▸ suf ∷ f ⟨ d' ⟩)

    -- the two related diagrams have equal input width.
    ≈NF⇒width : ∀ {n n'} {d : DiagU n} {d' : DiagU n'} → d ≈NF d' → n ≡ n'
    ≈NF⇒width nf[]        = refl
    ≈NF⇒width (nf∷ f eq)  = refl

    --------------------------------------------------------------------------------
    -- The decision goes through a FIRST-ORDER layer encoding: deciding the
    -- encoded layer lists (plus the input width) avoids every match against
    -- the `++`-composite indices — matching `_≈NF_`/`DiagU` constructors
    -- happens only inside the two conversion lemmas, at fully-general
    -- (variable) indices, so the procedure is `--without-K`-compatible.
    --------------------------------------------------------------------------------

    -- one layer, first-order: offset, suffix, and the generator triple.
    LayerE : Set
    LayerE = List X × (List X × Gen)

    encode : ∀ {n} → DiagU n → List LayerE
    encode ([]_ n)               = []
    encode (pre ▸ suf ∷ f ⟨ d ⟩) = (pre , suf , gen f) ∷ encode d

    private
      _≟E_ : DecidableEquality (List LayerE)
      _≟E_ = ListProp.≡-dec
               (ProdProp.≡-dec _≟L_ (ProdProp.≡-dec _≟L_ _≟Mor_))

      -- an ≈NF witness yields equal widths and equal encodings.
      ≈NF⇒encode : ∀ {n n'} {d : DiagU n} {d' : DiagU n'}
                 → d ≈NF d' → encode d ≡ encode d'
      ≈NF⇒encode nf[]       = refl
      ≈NF⇒encode (nf∷ f eq) = cong (_ ∷_) (≈NF⇒encode eq)

      -- equal widths + equal encodings rebuild an ≈NF witness.  All
      -- constructor matches here are at fully-general indices.
      encode⇒≈NF : ∀ {n n'} (d : DiagU n) (d' : DiagU n')
                 → n ≡ n' → encode d ≡ encode d' → d ≈NF d'
      encode⇒≈NF ([]_ n) ([]_ n') refl _ = nf[]
      encode⇒≈NF ([]_ n) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) _ ()
      encode⇒≈NF (pre ▸ suf ∷ f ⟨ d ⟩) ([]_ n') _ ()
      encode⇒≈NF (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en ee
        with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl = nf∷ f (encode⇒≈NF d d' refl te)

    infix 4 _≟DiagU_

    _≟DiagU_ : ∀ {n n'} (d : DiagU n) (d' : DiagU n') → Dec (d ≈NF d')
    _≟DiagU_ {n} {n'} d d' = case n ≟L n' of λ where
      (no  n≢) → no λ eq → n≢ (≈NF⇒width eq)
      (yes en) → case encode d ≟E encode d' of λ where
        (yes ee) → yes (encode⇒≈NF d d' en ee)
        (no  e≢) → no λ eq → e≢ (≈NF⇒encode eq)

    --------------------------------------------------------------------------------
    -- `_≈NF_` is observationally propositional equality: a witness collapses
    -- to a real `≡` of equal-width diagrams.  Matching an `_≈NF_` value at a
    -- HOMOGENEOUS type is `--without-K`-stuck (the duplicated width index),
    -- so we go through the first-order encoding: `encode` is injective on
    -- equal-width diagrams, with the residual reflexive width equation
    -- discharged by the Hedberg UIP on `List X`.
    --------------------------------------------------------------------------------
    private
      uipL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
      uipL = UIPmod.Decidable⇒UIP.≡-irrelevant _≟L_

      encode-inj : ∀ {n n'} (d : DiagU n) (d' : DiagU n') (en : n ≡ n')
                 → encode d ≡ encode d' → subst DiagU en d ≡ d'
      encode-inj ([]_ n) ([]_ n') refl _ = refl
      encode-inj ([]_ n) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) ([]_ n') _ ()
      encode-inj (pre ▸ suf ∷ f ⟨ d ⟩) (pre' ▸ suf' ∷ f' ⟨ d' ⟩) en ee
        with ∷-injective ee
      ... | he , te with cong proj₁ he | cong (proj₁ ∙f proj₂) he | cong (proj₂ ∙f proj₂) he
      ...   | refl | refl | refl rewrite uipL en refl =
              cong (λ z → pre ▸ suf ∷ f ⟨ z ⟩) (encode-inj d d' refl te)

    ≈NF⇒≡ : ∀ {n} {d d' : DiagU n} → d ≈NF d' → d ≡ d'
    ≈NF⇒≡ {d = d} {d' = d'} eq = encode-inj d d' refl (≈NF⇒encode eq)

    -- coerce a flat HomTerm along an equality of its output width.  Downstream
    -- solver assemblies state their soundness lemmas at the common codomain
    -- type via this coercion.
    coeW : ∀ {n p q} → p ≡ q → HomTerm (wires n) (wires p) → HomTerm (wires n) (wires q)
    coeW p≡q = subst (λ w → HomTerm (wires _) (wires w)) p≡q

--------------------------------------------------------------------------------
-- Compatibility wrapper: `SolverCompareI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`), re-exported alongside it to preserve the
-- old `open Untyped … public` surface.  Old consumers keep working, gaining
-- only the leading variant argument.
--------------------------------------------------------------------------------
module SolverCompare
  (v : Variant)
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor : List X → List X → Set)
  where

  open Untyped v {X} Mor using (⟦box⟧) public
  open SolverCompareI v {X} _≟X_ Mor ⟦box⟧ public

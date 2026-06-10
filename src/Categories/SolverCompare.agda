{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decidable normal-form equality on `DiagU` together with the final solver
-- assembly, *parameterized* over the reflect / normalize milestones (which
-- are built concurrently in sibling modules — hence NOT imported here, only
-- abstracted as interface parameters).
--
-- Two deliverables:
--
--   (A) `_≟DiagU_` : a genuine *decidable propositional equality* on `DiagU n`
--       (same input width).  It bottoms out in `DecidableEquality X` (for
--       offsets) and a caller-supplied heterogeneous decidable equality on the
--       generators `Mor` (the "same box" test).  The dependent index
--       `pre ++ (a ++ suf)` of the cons constructor is handled by deciding the
--       boundary lists and the generator triple first, then pattern-matching
--       the recovered equalities so the recursive call on the tail is
--       well-typed.
--
--   (B) `Assembly.solveMor?` : the hole-free gluing
--           reflect-sound + normalize-sound + NF-equality  ⇒  f ≈Term g.
--       We work in the *wires-flat* fragment: a term lives between flat wire
--       objects `wires n` / `wires m`, which is exactly the fragment the
--       `reflect` milestone targets, so no `flatten`/`Φ` conjugation is
--       needed beyond the `out`-equality bookkeeping the interface carries
--       explicitly.
--------------------------------------------------------------------------------

module Categories.SolverCompare where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec; ∷-injective)
import Data.List.Properties as ListProp
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
import Data.Product.Properties as ProdProp
open import Function using () renaming (_∘_ to _∙f_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

import Axiom.UniquenessOfIdentityProofs as UIPmod

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped using (module Untyped)

--------------------------------------------------------------------------------
-- The development is relative to a label set `X` with decidable equality and a
-- morphism-generator family `Mor`.
--------------------------------------------------------------------------------
module SolverCompare
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor : List X → List X → Set)
  where

  open Untyped {X = X} Mor public
  open FreeMonoidalHelper Mon X using (ObjTerm)
  -- re-export the term language / equational theory used by the interpretation
  -- (Untyped opens these internally without `public`).
  open FreeMonoidalHelper.Mor Mon X mor public

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
    _≟DiagU_ {n} {n'} d d' with n ≟L n' | encode d ≟E encode d'
    ... | yes en | yes ee = yes (encode⇒≈NF d d' en ee)
    ... | no  n≢ | _      = no λ eq → n≢ (≈NF⇒width eq)
    ... | yes _  | no e≢  = no λ eq → e≢ (≈NF⇒encode eq)

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

    --------------------------------------------------------------------------------
    -- (B) The final assembly, parameterized over the reflect / normalize
    -- milestones.
    --
    -- We work in the wires-flat fragment: every term to be solved lives
    -- between flat wire objects `wires n` / `wires m` (the fragment the
    -- `reflect` milestone targets).  The only bookkeeping is the output
    -- width: a reflected/normalized diagram has some output `out d`, which the
    -- interface witnesses to equal the term's codomain width `m`.  We package
    -- that as a *width coercion* `coeW` of the interpretation onto the common
    -- type `HomTerm (wires n) (wires m)`, and the interface states its
    -- soundness already at that common type — so the gluing is pure `≈Term`
    -- transitivity, with the single `≈NF` equation transported across the
    -- (definitionally equal) output widths.
    --------------------------------------------------------------------------------

    -- coerce a flat HomTerm along an equality of its output width.
    coeW : ∀ {n p q} → p ≡ q → HomTerm (wires n) (wires p) → HomTerm (wires n) (wires q)
    coeW p≡q = subst (λ w → HomTerm (wires _) (wires w)) p≡q

    module Assembly
      -- reflect a flat term to a width-n diagram, with its output width
      (reflect      : ∀ {n m} → HomTerm (wires n) (wires m) → DiagU n)
      (reflect-out  : ∀ {n m} (t : HomTerm (wires n) (wires m)) → out (reflect t) ≡ m)
      -- soundness, stated at the common type after width coercion
      (reflect-sound : ∀ {n m} (t : HomTerm (wires n) (wires m))
                     → coeW (reflect-out t) ⟦ reflect t ⟧ ≈Term t)
      -- normalize a diagram, output-width preserving and sound
      (normalize       : ∀ {n} → DiagU n → DiagU n)
      (normalize-out   : ∀ {n} (d : DiagU n) → out (normalize d) ≡ out d)
      (normalize-sound : ∀ {n} (d : DiagU n)
                       → coeW (normalize-out d) ⟦ normalize d ⟧ ≈Term ⟦ d ⟧)
      where

      open ≈R

      -- normal form of a flat term, coerced back to the common codomain.
      -- nf t  : DiagU n   with output width m (witnessed by nf-out).
      nf : ∀ {n m} → HomTerm (wires n) (wires m) → DiagU n
      nf t = normalize (reflect t)

      nf-out : ∀ {n m} (t : HomTerm (wires n) (wires m)) → out (nf t) ≡ m
      nf-out t = trans (normalize-out (reflect t)) (reflect-out t)

      -- the coerced interpretation of the normal form is ≈Term the term.
      -- Chains  normalize-sound · reflect-sound, with the two width coercions
      -- fused into the single `nf-out` coercion (a `subst`-on-`subst`).
      nf-sound : ∀ {n m} (t : HomTerm (wires n) (wires m))
               → coeW (nf-out t) ⟦ nf t ⟧ ≈Term t
      nf-sound {n} {m} t = begin
        coeW (nf-out t) ⟦ nf t ⟧
          ≈⟨ ≡⇒≈Term (subst-fuse (normalize-out (reflect t)) (reflect-out t) ⟦ nf t ⟧) ⟩
        coeW (reflect-out t) (coeW (normalize-out (reflect t)) ⟦ normalize (reflect t) ⟧)
          ≈⟨ coeW-resp (reflect-out t) (normalize-sound (reflect t)) ⟩
        coeW (reflect-out t) ⟦ reflect t ⟧
          ≈⟨ reflect-sound t ⟩
        t ∎
        where
          -- subst over a trans splits into two nested substs.
          subst-fuse : ∀ {n p q r} (p≡q : p ≡ q) (q≡r : q ≡ r)
                       (h : HomTerm (wires n) (wires p))
                     → coeW (trans p≡q q≡r) h ≡ coeW q≡r (coeW p≡q h)
          subst-fuse refl refl h = refl
          -- coercion respects ≈Term.
          coeW-resp : ∀ {n p q} (p≡q : p ≡ q) {h k : HomTerm (wires n) (wires p)}
                    → h ≈Term k → coeW p≡q h ≈Term coeW p≡q k
          coeW-resp refl eq = eq

      -- transport the NF equality across the two diagrams' output widths so it
      -- lands at the common codomain type.  Since both nf t / nf u are DiagU n
      -- and `≈NF⇒≈Term` already gives the raw interpretation equality, we just
      -- coerce both sides by their (equal) output-width witnesses.
      nfEq-coerced : ∀ {n m} (t u : HomTerm (wires n) (wires m))
                   → nf t ≈NF nf u
                   → coeW (nf-out t) ⟦ nf t ⟧ ≈Term coeW (nf-out u) ⟦ nf u ⟧
      nfEq-coerced t u eq = nfEq-aux (≈NF⇒≡ eq) (nf-out t) (nf-out u)
        where
          -- generalize over the diagrams so that matching `refl` on the
          -- *propositional* `d ≡ d'` no longer faces stuck `normalize/reflect`
          -- applications.  Once unified, the two output-width witnesses are
          -- proofs of the same List-equality, hence equal by UIP from
          -- `DecidableEquality (List X)`.
          nfEq-aux : ∀ {n p} {d d' : DiagU n}
                       (e : d ≡ d') (q₁ : out d ≡ p) (q₂ : out d' ≡ p)
                   → coeW q₁ ⟦ d ⟧ ≈Term coeW q₂ ⟦ d' ⟧
          nfEq-aux {d = d} refl q₁ q₂ =
            ≡⇒≈Term (cong (λ z → coeW z ⟦ d ⟧)
                       (UIPmod.Decidable⇒UIP.≡-irrelevant _≟L_ q₁ q₂))

      --------------------------------------------------------------------------------
      -- The solver: reflect+normalize both sides, decide NF equality, and on a
      -- positive decision chain
      --   f ≈ coeW⟦nf f⟧ ≈ coeW⟦nf g⟧ ≈ g
      -- using nf-sound on each end and nfEq-coerced in the middle.
      --------------------------------------------------------------------------------
      solveMor? : ∀ {n m} (f g : HomTerm (wires n) (wires m)) → Maybe (f ≈Term g)
      solveMor? f g with nf f ≟DiagU nf g
      ... | no  _  = nothing
      ... | yes eq = just (begin
              f
                ≈⟨ nf-sound f ⟨
              coeW (nf-out f) ⟦ nf f ⟧
                ≈⟨ nfEq-coerced f g eq ⟩
              coeW (nf-out g) ⟦ nf g ⟧
                ≈⟨ nf-sound g ⟩
              g ∎)

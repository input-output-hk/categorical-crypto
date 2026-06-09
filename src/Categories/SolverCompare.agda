{-# OPTIONS --safe #-}

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
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
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
  []       ≟L []       = yes refl
  []       ≟L (_ ∷ _)  = no λ ()
  (_ ∷ _)  ≟L []       = no λ ()
  (x ∷ xs) ≟L (y ∷ ys) with x ≟X y
  ... | no  x≢y  = no λ { refl → x≢y refl }
  ... | yes refl with xs ≟L ys
  ...   | no  xs≢ys = no λ { refl → xs≢ys refl }
  ...   | yes refl  = yes refl

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
    -- The decision procedure is itself stated *heterogeneously* (`d : DiagU n`,
    -- `d' : DiagU n'` with possibly different widths).  This is essential: with
    -- a single shared width, matching the second cons against `DiagU (pre ++
    -- (a ++ suf))` would again provoke the `_++_` unification that Agda gets
    -- stuck on.  Independent widths let both cons constructors split freely;
    -- the structural relation `_≈NF_` then carries the equality, and matching
    -- the generator-triple `refl` retypes the box and tail in one step.
    --------------------------------------------------------------------------------
    infix 4 _≟DiagU_

    _≟DiagU_ : ∀ {n n'} (d : DiagU n) (d' : DiagU n') → Dec (d ≈NF d')

    -- []/[] : equal iff the two (now independent) widths agree.
    ([]_ n)               ≟DiagU ([]_ n')               with n ≟L n'
    ... | yes refl = yes nf[]
    ... | no  n≢   = no λ { nf[] → n≢ refl }

    -- []/cons and cons/[] : structurally distinct head constructors.
    ([]_ n)               ≟DiagU (pre ▸ suf ∷ f ⟨ d' ⟩) = no λ ()
    (pre ▸ suf ∷ f ⟨ d ⟩) ≟DiagU ([]_ n)                = no λ ()

    -- cons/cons : decide pre, suf and the generator triple, then recurse.
    (pre ▸ suf ∷ f ⟨ d ⟩) ≟DiagU (pre' ▸ suf' ∷ f' ⟨ d' ⟩)
      with pre ≟L pre' | suf ≟L suf' | gen f ≟Mor gen f'
    ... | no  pre≢ | _        | _        = no λ { (nf∷ _ _) → pre≢ refl }
    ... | yes _    | no suf≢  | _        = no λ { (nf∷ _ _) → suf≢ refl }
    ... | yes _    | yes _    | no gen≢  = no λ { (nf∷ _ _) → gen≢ refl }
    ... | yes refl | yes refl | yes refl with d ≟DiagU d'
    ...   | yes eq  = yes (nf∷ f eq)
    ...   | no  d≢  = no λ { (nf∷ _ eq) → d≢ eq }

    --------------------------------------------------------------------------------
    -- `_≈NF_` is observationally propositional equality: its constructors only
    -- ever relate equal-width diagrams that agree on every field, so a witness
    -- collapses to a real `≡`.  (Because the two index args of `_≈NF_` are
    -- forced equal by each constructor, we may state this homogeneously.)
    --------------------------------------------------------------------------------
    ≈NF⇒≡ : ∀ {n} {d d' : DiagU n} → d ≈NF d' → d ≡ d'
    ≈NF⇒≡ nf[]                              = refl
    ≈NF⇒≡ (nf∷ {pre = pre} {suf = suf} f eq) =
      cong (λ z → pre ▸ suf ∷ f ⟨ z ⟩) (≈NF⇒≡ eq)

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

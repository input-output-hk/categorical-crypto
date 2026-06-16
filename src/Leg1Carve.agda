{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- LEG 1 of proof-carrying Route A: the carve combinatorics.
--
-- Two genuinely-new sub-proofs feed the replacement-leg isomorphism
-- `H'[h ↦ ⟪lᵗ⟫] ≅ᴴ ⟪s⟫` (see docs/findiso-witness-plan.md, leg 1):
--
--   (a) `kahn`'s output edge list is a PERMUTATION of its input list
--       `holeEdge ∷ complement`.  Stated order-agnostically as a stdlib
--       `_↭_`.  `findReady` removes the chosen edge from the middle of the
--       pending list (order-preserving on the rest), so `e ∷ rest` is a
--       permutation of `pending`; induction over the fuel then assembles the
--       full permutation.  This is label-agnostic: `kahn` only inspects edge
--       endpoints, so we work over an abstract `Edge` carrier with `ins`/
--       `outs : List V` for a `V` with decidable equality (matching
--       `Deep.At.Build`, which instantiates `V = Fin S.nV`).
--
--   (b) carve-then-substitute = identity up to the (a)-permutation and the
--       embedding.  [see below]
--------------------------------------------------------------------------------

module Leg1Carve where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; _++_; [_]; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
open import Relation.Nullary using (yes; no)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; prep; swap; ↭-sym; ↭-trans; ↭-refl)
  renaming (refl to ↭refl; trans to ↭trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (shift)

--------------------------------------------------------------------------------
-- Part (a): kahn is a permutation of its input list.
--
-- Abstracted over the vertex carrier `V` (decidable equality) and an edge
-- carrier `E` exposing endpoint lists.  This is exactly the data `kahn`
-- inspects; labels are irrelevant to its control flow.

module KahnPerm
  {V : Set} (_≟V_ : DecidableEquality V)
  {E : Set} (eins eouts : E → List V)
  where

  -- `remove1 v xs` deletes the first occurrence of `v` from `xs`.
  remove1 : V → List V → Maybe (List V)
  remove1 v []       = nothing
  remove1 v (w ∷ ws) with v ≟V w
  ... | yes _ = just ws
  ... | no  _ = Maybe.map (w ∷_) (remove1 v ws)

  -- `consume vs avail` removes each `v ∈ vs` from `avail` in turn.
  consume : List V → List V → Maybe (List V)
  consume []       avail = just avail
  consume (v ∷ vs) avail = remove1 v avail >>= consume vs

  -- First pending edge whose inputs are all available; returns the chosen
  -- edge, the new availability, and the remaining pending list (order
  -- preserved).
  findReady : List V → List E
            → Maybe (E × List V × List E)
  findReady avail []       = nothing
  findReady avail (e ∷ es) with consume (eins e) avail
  ... | just avail' = just (e , avail' , es)
  ... | nothing     =
        Maybe.map (λ { (r , av , rest) → (r , av , e ∷ rest) })
                  (findReady avail es)

  kahn : ℕ → List V → List E → Maybe (List E)
  kahn _          _     []      = just []
  kahn zero       _     _       = nothing
  kahn (suc fuel) avail pending with findReady avail pending
  ... | nothing                 = nothing
  ... | just (e , avail' , rest) =
        Maybe.map (e ∷_) (kahn fuel (avail' ++ eouts e) rest)

  private
    just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
    just-inj refl = refl

    -- `Maybe.map f` is `just` only via `f` of a `just`.
    map-just-inv : ∀ {A B : Set} (f : A → B) {ma : Maybe A} {b : B}
                 → Maybe.map f ma ≡ just b
                 → Σ A (λ a → (ma ≡ just a) × (f a ≡ b))
    map-just-inv f {just a}  refl = a , refl , refl
    map-just-inv f {nothing} ()

  ------------------------------------------------------------------------------
  -- (a.1) findReady, when it succeeds, returns a chosen edge `e` and a
  -- remaining list `rest` such that `e ∷ rest` is a permutation of the input
  -- `pending`.  `e` is pulled from somewhere in the middle; the prefix it
  -- skipped is preserved in front of it inside `rest`, so this is precisely
  -- the `shift` lemma applied at the skip point.

  findReady-↭ : ∀ avail pending {e av rest}
              → findReady avail pending ≡ just (e , av , rest)
              → e ∷ rest ↭ pending
  findReady-↭ avail (x ∷ pending) {e} {av} {rest} eq
        with consume (eins x) avail
  -- ready immediately: e = x, rest = pending.
  ... | just _  with refl ← just-inj eq = ↭-refl
  -- not ready: recurse on `findReady avail pending`.  Capture its result with
  -- `in eq2`; the outer `eq` then forces it to be a `just (r , av' , rest')`
  -- with `rest = x ∷ rest'`, `e = r`.  IH gives `r ∷ rest' ↭ pending`, so
  -- `r ∷ x ∷ rest' ↭ x ∷ pending` by a `swap` then `prep x`.
  ... | nothing with findReady avail pending in eq2
  ...   | just (r , av' , rest') with refl ← just-inj eq =
            ↭-trans (swap r x ↭-refl) (prep x (findReady-↭ avail pending eq2))
  findReady-↭ avail (x ∷ pending) () | nothing | nothing

  ------------------------------------------------------------------------------
  -- (a.2) The main lemma: `kahn` produces a permutation of its pending input.
  -- Induct on fuel.  Each step pulls a ready edge `e` (findReady-↭ gives
  -- `e ∷ rest ↭ pending`), emits it, and recurses on `rest` (IH gives
  -- `out' ↭ rest`).  Then `e ∷ out' ↭ e ∷ rest ↭ pending`.

  kahn-↭ : ∀ fuel avail pending {out}
         → kahn fuel avail pending ≡ just out
         → out ↭ pending
  kahn-↭ fuel       avail []            refl = ↭-refl
  kahn-↭ (suc fuel) avail (p ∷ pending) eq
        with findReady avail (p ∷ pending) in eqfr
  ... | just (e , av' , rest) with kahn fuel (av' ++ eouts e) rest in eq-rec
  ...   | just out' with refl ← just-inj eq =
            ↭-trans (prep e (kahn-↭ fuel (av' ++ eouts e) rest eq-rec))
                    (findReady-↭ avail (p ∷ pending) eqfr)
  kahn-↭ (suc fuel) avail (p ∷ pending) eq | just (e , av' , rest) | nothing
        with () ← eq
  kahn-↭ (suc fuel) avail (p ∷ pending) () | nothing

--------------------------------------------------------------------------------
-- Part (b): carve-then-substitute is the identity up to permutation.
--
-- `complement` walks `range S.nE` keeping exactly the S-edges with NO ψ-
-- preimage (`ψ⁻¹ e ≡ nothing`).  Substituting the hole back with ⟪lᵗ⟫ via the
-- embedding restores exactly the ψ-IMAGE edges.  The combinatorial heart of
-- (b) is therefore: regrouping `range S.nE` into [ψ-image part] ++ [complement
-- part] is a PERMUTATION of `range S.nE`.  Stated abstractly over a classifier
-- `cls : I → Maybe J` (= ψ⁻¹), with `image`/`comp` the two sublists carved by a
-- single walk — this is "a stable partition of a list is a permutation of it".

module Partition {I J : Set} (cls : I → Maybe J) where

  -- The ψ-image part: indices `e` with `cls e ≡ just _`, in input order.
  imagePart : List I → List I
  imagePart []       = []
  imagePart (e ∷ es) with cls e
  ... | just _  = e ∷ imagePart es
  ... | nothing = imagePart es

  -- The complement part: indices with `cls e ≡ nothing` (= Build.complement's
  -- keep, modulo carrying the index rather than the relabelled S-edge).
  compPart : List I → List I
  compPart []       = []
  compPart (e ∷ es) with cls e
  ... | just _  = compPart es
  ... | nothing = e ∷ compPart es

  -- The regrouping is a permutation of the original list.  Induct on the
  -- list; at a `just` head the element sits at the front of `imagePart`
  -- (`prep`); at a `nothing` head it sits at the front of `compPart`, i.e. in
  -- the MIDDLE of `imagePart ++ (e ∷ compPart')` — `shift` pulls it out.
  partition-↭ : (es : List I) → imagePart es ++ compPart es ↭ es
  partition-↭ []       = ↭-refl
  partition-↭ (e ∷ es) with cls e
  ... | just _  = prep e (partition-↭ es)
  ... | nothing =
        ↭-trans (shift e (imagePart es) (compPart es))
                (prep e (partition-↭ es))

--------------------------------------------------------------------------------
-- Part (b) bridge: a propositional permutation `xs ↭ ys` induces an index
-- function `Fin (length xs) → Fin (length ys)` whose `lookup` agrees.  This is
-- a propositional, `≡`-based reconstruction of the stdlib's setoid `onIndices`
-- / `onIndices-lookup` (the stdlib only proves it for the SETOID permutation,
-- and `≅ᴴ`'s `ψ`/`ψ-ein` want plain functions with `≡` laws, not an `Inverse`
-- bundle over a setoid).  We build the FORWARD index map + its lookup law;
-- the backward map is the same construction on `↭-sym`, and the two-sided
-- inverse laws are the remaining (structural) work — see Perm→Iso below.

module PermIdx {A : Set} where

  open import Data.Fin using (Fin; zero; suc)
  open import Data.List.Base using (lookup)
  open import Function using (_∘_)

  -- Forward index map.  Mirrors `onIndices` (Homogeneous):
  --   refl → identity, prep → lift, swap → swap-of-first-two, trans → compose.
  -- We must transport along `↭-length` to retype `Fin (length xs)` targets.
  toIdx : ∀ {xs ys : List A} → xs ↭ ys → Fin (length xs) → Fin (length ys)
  toIdx ↭refl            i             = i
  toIdx (prep x p)      zero          = zero
  toIdx (prep x p)      (suc i)       = suc (toIdx p i)
  toIdx (swap x y p)    zero          = suc zero
  toIdx (swap x y p)    (suc zero)    = zero
  toIdx (swap x y p)    (suc (suc i)) = suc (suc (toIdx p i))
  toIdx (↭trans p q)     i             = toIdx q (toIdx p i)

  -- Lookup-agreement: the permuted list, read at the mapped index, gives the
  -- original element.  This is the law `≅ᴴ`'s endpoint/label fields rest on.
  toIdx-lookup : ∀ {xs ys : List A} (p : xs ↭ ys) (i : Fin (length xs))
               → lookup ys (toIdx p i) ≡ lookup xs i
  toIdx-lookup ↭refl            i             = refl
  toIdx-lookup (prep x p)      zero          = refl
  toIdx-lookup (prep x p)      (suc i)       = toIdx-lookup p i
  toIdx-lookup (swap x y p)    zero          = refl
  toIdx-lookup (swap x y p)    (suc zero)    = refl
  toIdx-lookup (swap x y p)    (suc (suc i)) = toIdx-lookup p i
  toIdx-lookup (↭trans p q)     i             =
    trans (toIdx-lookup q (toIdx p i)) (toIdx-lookup p i)

  -- Backward index map and the two-sided inverse laws — `↭-sym` is structural
  -- (`↭-sym (prep x p) = prep x (↭-sym p)` etc.), so the round-trips follow by
  -- induction on `p`.  Gives `≅ᴴ`'s `ψ`/`ψ⁻¹`/`ψ-left`/`ψ-right` directly.
  fromIdx : ∀ {xs ys : List A} → xs ↭ ys → Fin (length ys) → Fin (length xs)
  fromIdx p = toIdx (↭-sym p)

  toIdx-fromIdx : ∀ {xs ys : List A} (p : xs ↭ ys) (i : Fin (length xs))
                → fromIdx p (toIdx p i) ≡ i
  toIdx-fromIdx ↭refl         i             = refl
  toIdx-fromIdx (prep x p)    zero          = refl
  toIdx-fromIdx (prep x p)    (suc i)       = cong suc (toIdx-fromIdx p i)
  toIdx-fromIdx (swap x y p)  zero          = refl
  toIdx-fromIdx (swap x y p)  (suc zero)    = refl
  toIdx-fromIdx (swap x y p)  (suc (suc i)) = cong (λ z → suc (suc z)) (toIdx-fromIdx p i)
  toIdx-fromIdx (↭trans p q)  i             =
    trans (cong (toIdx (↭-sym p)) (toIdx-fromIdx q (toIdx p i)))
          (toIdx-fromIdx p i)

  fromIdx-toIdx : ∀ {xs ys : List A} (p : xs ↭ ys) (j : Fin (length ys))
                → toIdx p (fromIdx p j) ≡ j
  fromIdx-toIdx ↭refl         j             = refl
  fromIdx-toIdx (prep x p)    zero          = refl
  fromIdx-toIdx (prep x p)    (suc j)       = cong suc (fromIdx-toIdx p j)
  fromIdx-toIdx (swap x y p)  zero          = refl
  fromIdx-toIdx (swap x y p)  (suc zero)    = refl
  fromIdx-toIdx (swap x y p)  (suc (suc j)) = cong (λ z → suc (suc z)) (fromIdx-toIdx p j)
  fromIdx-toIdx (↭trans p q)  j             =
    trans (cong (toIdx q) (fromIdx-toIdx p (toIdx (↭-sym q) j)))
          (fromIdx-toIdx q j)

--------------------------------------------------------------------------------
-- Part (b) capstone: a permuted-edge hypergraph is ≅ᴴ to the original.
--
-- Given a hypergraph `G` and an index list `idx : List (Fin G.nE)` that is a
-- permutation of `range G.nE` (i.e. a reordering of ALL of G's edges with no
-- repeats/omissions), the hypergraph `K` with the SAME vertices/labels/
-- boundary but whose edges are G's edges re-read through `idx` is isomorphic
-- to `G`.  Vertex bijection = identity; edge bijection = `PermIdx.toIdx` of
-- the permutation.  This is the lemma that turns the (a)+(b)-core combinatorics
-- (`kahn-↭`, `partition-↭`) into the `≅ᴴ` for LEG 1: instantiate `G = ⟪s⟫`,
-- `idx = ` the carved-then-substituted edge order (complement ++ ψ-image),
-- `idx ↭ range G.nE` from `partition-↭`.

module PermEdges where

  open import Categories.APROP.Hypergraph.Core using (Hypergraph)
  open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
  open import Data.Fin using (Fin; zero; suc; cast)
  open import Data.List.Base using (lookup; length; map; allFin; tabulate)
  open import Data.List.Properties
    using (length-map; map-id; length-tabulate; lookup-tabulate)
  open import Function using (id)
  open import Relation.Binary.PropositionalEquality using (subst; subst₂)

  ------------------------------------------------------------------------------
  -- (A) Assembly lemma.  Given an explicit edge bijection between G and K with
  -- the SAME vertices/vlab/dom/cod whose endpoint/label data agree on the
  -- nose (`K.ein (ψ e) ≡ G.ein e`, etc. — no `map φ` because φ = id), build
  -- `G ≅ᴴ K`.  This is `refl-≅ᴴ` with the edge identity loosened to a supplied
  -- bijection; all the `subst₂`/`map φ` plumbing collapses because φ = id.

  module _ {X : Set} {Gen : List X → List X → Set} where
    open Hypergraph

    -- K is `reEdge G nE' ein' eout' elab'`: same vertices/labels/boundary as
    -- G, but a fresh edge family.  (`assemble` in Deep.Build is exactly this
    -- shape: it keeps `nV`, `vlab`, `dom`, `cod` from S.)
    reEdge : (G : Hypergraph Gen) (nE' : ℕ)
           → (ein' eout' : Fin nE' → List (Fin (nV G)))
           → (elab' : (e : Fin nE')
                    → Gen (map (vlab G) (ein' e)) (map (vlab G) (eout' e)))
           → Hypergraph Gen
    reEdge G nE' ein' eout' elab' = record
      { nV = nV G ; vlab = vlab G
      ; nE = nE' ; ein = ein' ; eout = eout' ; elab = elab'
      ; dom = dom G ; cod = cod G }

    -- Assembly: a fresh edge family that is a bijective, on-the-nose-equal
    -- reindexing of G's edges yields `G ≅ᴴ reEdge G …`.  φ = id, so every
    -- vertex/boundary law is `refl`/`map-id`; the edge laws come from the
    -- supplied bijection + endpoint/label equalities.
    reEdge-≅ᴴ :
      (G : Hypergraph Gen) (nE' : ℕ)
      (ein' eout' : Fin nE' → List (Fin (nV G)))
      (elab' : (e : Fin nE') → Gen (map (vlab G) (ein' e)) (map (vlab G) (eout' e)))
      -- edge bijection ψ : G.nE ↔ nE'
      (ψ : Fin (nE G) → Fin nE') (ψ⁻¹ : Fin nE' → Fin (nE G))
      (ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e) (ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e)
      -- on-the-nose endpoint agreement at the matched edges.
      (ein-ok  : ∀ e → ein'  (ψ e) ≡ ein  G e)
      (eout-ok : ∀ e → eout' (ψ e) ≡ eout G e)
      -- label agreement, up to subst₂ along the (derived) atom equalities.
      (elab-ok : ∀ e →
        subst₂ Gen (cong (map (vlab G)) (ein-ok e))
                   (cong (map (vlab G)) (eout-ok e))
                   (elab' (ψ e))
        ≡ elab G e)
      → G ≅ᴴ reEdge G nE' ein' eout' elab'
    reEdge-≅ᴴ G nE' ein' eout' elab' ψ ψ⁻¹ ψ-left ψ-rght
              ein-ok eout-ok elab-ok = record
      { φ = id ; φ⁻¹ = id ; φ-left = λ _ → refl ; φ-rght = λ _ → refl
      ; ψ = ψ ; ψ⁻¹ = ψ⁻¹ ; ψ-left = ψ-left ; ψ-rght = ψ-rght
      ; φ-lab = λ _ → refl
      ; ψ-ein  = λ e → trans (ein-ok  e) (sym (map-id (ein  G e)))
      ; ψ-eout = λ e → trans (eout-ok e) (sym (map-id (eout G e)))
      ; φ-dom = sym (map-id (dom G)) ; φ-cod = sym (map-id (cod G))
      ; atom-ein  = λ e → cong (map (vlab G)) (ein-ok  e)
      ; atom-eout = λ e → cong (map (vlab G)) (eout-ok e)
      ; ψ-elab = elab-ok
      }

    ----------------------------------------------------------------------------
    -- (B) Producer.  From a permutation `p : idx ↭ allFin (nE G)` of ALL of
    -- G's edge indices, build the bijection feeding `reEdge-≅ᴴ`, where K's
    -- edges are G's read through `idx`:  K.ein i = G.ein (lookup idx i), etc.
    -- The edge bijection is `PermIdx.toIdx`/`fromIdx` of `↭-sym p` (composed
    -- with the `allFin` length cast); the on-the-nose endpoint/label laws come
    -- from `toIdx-lookup` together with `lookup (allFin n) (cast i) ≡ i`.

    module _ (G : Hypergraph Gen)
             (idx : List (Fin (nE G)))
             (p : idx ↭ allFin (nE G)) where

      private
        n = nE G
        -- length cast: Fin n ↔ Fin (length (allFin n)).
        castIn : Fin n → Fin (length (allFin n))
        castIn = cast (sym (length-tabulate id))
        q : allFin n ↭ idx
        q = ↭-sym p

        module P = PermIdx {A = Fin n}

        -- edge bijection: G-edge `e` ↦ its position in `idx`.
        ψ : Fin n → Fin (length idx)
        ψ e = P.toIdx q (castIn e)
        ψ⁻¹ : Fin (length idx) → Fin n
        ψ⁻¹ j = cast (length-tabulate id) (P.fromIdx q j)

        -- K's edges, read through idx.
        ein'  = λ (i : Fin (length idx)) → ein  G (lookup idx i)
        eout' = λ (i : Fin (length idx)) → eout G (lookup idx i)
        elab' : (i : Fin (length idx))
              → Gen (map (vlab G) (ein' i)) (map (vlab G) (eout' i))
        elab' i = elab G (lookup idx i)

        -- `lookup idx (ψ e) ≡ e`: through `idx` at the bijected position lands
        -- on `e`.  `toIdx-lookup q` rewrites lookup-of-idx to lookup-of-allFin;
        -- `lookup-tabulate id` (the range-id law, cast-handled) finishes.
        idxψ : ∀ e → lookup idx (ψ e) ≡ e
        idxψ e = trans (P.toIdx-lookup q (castIn e)) (lookup-tabulate id e)

      permIdx-≅ᴴ : G ≅ᴴ reEdge G (length idx) ein' eout' elab'
      permIdx-≅ᴴ = reEdge-≅ᴴ G (length idx) ein' eout' elab'
        ψ ψ⁻¹ ψ-left ψ-rght ein-ok eout-ok elab-ok
        where
          ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
          ψ-left e =
            trans (cong (cast (length-tabulate id)) (P.toIdx-fromIdx q (castIn e)))
                  (cast-involutive-id e)
            where
              open import Data.Fin.Properties using (cast-involutive)
              -- cast (sym L) then cast L is identity.
              cast-involutive-id : ∀ e → cast (length-tabulate id) (castIn e) ≡ e
              cast-involutive-id e =
                cast-involutive (length-tabulate id) (sym (length-tabulate id)) e
          ψ-rght : ∀ j → ψ (ψ⁻¹ j) ≡ j
          ψ-rght j =
            trans (cong (P.toIdx q) (castInL (P.fromIdx q j)))
                  (P.fromIdx-toIdx q j)
            where
              open import Data.Fin.Properties using (cast-involutive)
              -- castIn (cast L x) = x  (inverse casts collapse), so
              -- ψ (ψ⁻¹ j) = toIdx q (fromIdx q j) = j.
              castInL : ∀ (x : Fin (length (allFin n)))
                      → cast (sym (length-tabulate id))
                             (cast {n = n} (length-tabulate id) x) ≡ x
              castInL x =
                cast-involutive {m = n} {n = length (allFin n)}
                  (sym (length-tabulate id)) (length-tabulate id) x
          ein-ok  : ∀ e → ein'  (ψ e) ≡ ein  G e
          ein-ok  e = cong (ein  G) (idxψ e)
          eout-ok : ∀ e → eout' (ψ e) ≡ eout G e
          eout-ok e = cong (eout G) (idxψ e)
          elab-ok : ∀ e →
            subst₂ Gen (cong (map (vlab G)) (ein-ok e))
                       (cong (map (vlab G)) (eout-ok e))
                       (elab' (ψ e))
            ≡ elab G e
          elab-ok e = elab-cong (idxψ e)
            where
              -- `elab' (ψ e) = elab G (lookup idx (ψ e))`, and along
              -- `idxψ e : lookup idx (ψ e) ≡ e` the subst₂ collapses to refl.
              elab-cong : ∀ {a b : Fin n} (eq : a ≡ b)
                → subst₂ Gen
                    (cong (map (vlab G)) (cong (ein  G) eq))
                    (cong (map (vlab G)) (cong (eout G) eq))
                    (elab G a)
                  ≡ elab G b
              elab-cong refl = refl

--------------------------------------------------------------------------------
-- Wiring: composing (a) `kahn-↭` with (b) the hole-substitution into a single
-- `idx ↭ allFin (nE S)`.  The carve assembles `kahn (holeEdge ∷ complement)`;
-- substituting the hole back with ⟪lᵗ⟫ replaces the hole element by the list
-- of ⟪lᵗ⟫'s edges (= the embedding's ψ-image, `expand-hole` below) while every
-- complement element expands to a singleton (itself).  This is a `concatMap`,
-- which preserves `↭`; composed with `kahn-↭` and `partition-↭` it closes the
-- index-level permutation that `permIdx-≅ᴴ` consumes.

module Wiring {A : Set} where

  open import Data.List.Base using (concatMap; concat)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (++⁺ˡ; shifts)

  -- `concat` preserves `↭`.  prep → ++⁺ˡ; swap → the stdlib `shifts` lemma
  -- (`xs ++ ys ++ zs ↭ ys ++ xs ++ zs`) is exactly the two-block exchange.
  concat-↭ : ∀ {xss yss : List (List A)} → xss ↭ yss → concat xss ↭ concat yss
  concat-↭ ↭refl          = ↭-refl
  concat-↭ (prep xs p)    = ++⁺ˡ xs (concat-↭ p)
  concat-↭ (swap xs ys p) =
    ↭-trans (shifts xs ys) (++⁺ˡ ys (++⁺ˡ xs (concat-↭ p)))
  concat-↭ (↭trans p q)   = ↭-trans (concat-↭ p) (concat-↭ q)

  -- Hence `concatMap f` preserves `↭` (= `concat ∘ map f`, and `map f`
  -- preserves `↭` by a direct induction).
  concatMap-↭ : ∀ {B : Set} (f : B → List A) {xs ys : List B}
              → xs ↭ ys → concatMap f xs ↭ concatMap f ys
  concatMap-↭ f p = concat-↭ (mapPerm p)
    where
      open import Data.List.Base using (map)
      mapPerm : ∀ {xs ys} → xs ↭ ys → map f xs ↭ map f ys
      mapPerm ↭refl        = ↭-refl
      mapPerm (prep x p)   = prep (f x) (mapPerm p)
      mapPerm (swap x y p) = swap (f x) (f y) (mapPerm p)
      mapPerm (↭trans p q) = ↭-trans (mapPerm p) (mapPerm q)

--------------------------------------------------------------------------------
-- End-to-end index permutation for LEG 1 (combinatorial closure).
--
-- Model a carve item as `Maybe I`: `nothing` is the hole, `just c` a kept
-- complement edge (carrying its originating S-index `c : I = Fin S.nE`).  The
-- carve assembles `kahn (nothing ∷ map just comp)`; `kahn-↭` says that is a
-- permutation of `nothing ∷ map just comp`.  Substituting the hole back with
-- ⟪lᵗ⟫ expands each item via `expand`:  the hole → `image` (⟪lᵗ⟫'s edges = the
-- embedding ψ-image S-indices), each `just c` → `[ c ]`.  Then
--
--     concatMap expand assembled  ↭  image ++ comp  ↭  allFin (nE S)
--
-- the first by `concatMap-↭` + `kahn-↭`, the second by `partition-↭` (with
-- `image = imagePart`, `comp = compPart`).  This is the `idx ↭ allFin (nE S)`
-- that `PermEdges.permIdx-≅ᴴ` consumes — closing LEG 1 at the index level.

module Closure {I J : Set} (cls : I → Maybe J) where

  open Partition cls using (imagePart; compPart; partition-↭)
  open import Data.List.Base using (concatMap; map; concat; _++_)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (++⁺ʳ)

  -- expansion of a carve item.
  expand : List I → Maybe I → List I
  expand image nothing  = image
  expand image (just c) = c ∷ []

  -- `concatMap (expand image) (map just comp) ≡ comp` (every kept item is a
  -- singleton, so the concatMap is the identity on `comp`).
  concatMap-just : (image comp : List I)
                 → concatMap (expand image) (map just comp) ≡ comp
  concatMap-just image []        = refl
  concatMap-just image (c ∷ cs)  = cong (c ∷_) (concatMap-just image cs)

  -- Substituting the hole in `nothing ∷ map just comp` yields `image ++ comp`.
  expand-hole : (image comp : List I)
              → concatMap (expand image) (nothing ∷ map just comp) ≡ image ++ comp
  expand-hole image comp = cong (image ++_) (concatMap-just image comp)

  -- THE CLOSURE.  For any `assembled ↭ nothing ∷ map just comp` (e.g. the kahn
  -- output) and `image ++ comp ↭ es` (e.g. `partition-↭` with `image =
  -- imagePart es`, `comp = compPart es`), the substituted edge order is a
  -- permutation of `es`.
  closure : (es image comp : List I)
          → (assembled : List (Maybe I))
          → assembled ↭ (nothing ∷ map just comp)
          → image ++ comp ↭ es
          → concatMap (expand image) assembled ↭ es
  closure es image comp assembled asm-↭ part-↭ =
    ↭-trans (Wiring.concatMap-↭ {A = I} (expand image) asm-↭)
            (↭-trans (subst-≡ (expand-hole image comp)) part-↭)
    where
      open import Relation.Binary.PropositionalEquality using (subst)
      -- a propositional equality, viewed as a ↭.
      subst-≡ : ∀ {xs ys : List I} → xs ≡ ys → xs ↭ ys
      subst-≡ refl = ↭-refl

  -- And specialised to the actual partition (`image = imagePart es`,
  -- `comp = compPart es`), the `image ++ comp ↭ es` premise is `partition-↭`:
  closure-partition : (es : List I) (assembled : List (Maybe I))
                    → assembled ↭ (nothing ∷ map just (compPart es))
                    → concatMap (expand (imagePart es)) assembled ↭ es
  closure-partition es assembled asm-↭ =
    closure es (imagePart es) (compPart es) assembled asm-↭ (partition-↭ es)

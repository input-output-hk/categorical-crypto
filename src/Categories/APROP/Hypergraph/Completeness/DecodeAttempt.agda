{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 4 (start) — discharging `decode-attempt-Linear` for
-- translated hypergraphs, plus the derivation of the total `decode`.
--
-- The cospan-form algorithm `decode-attempt` returns a `Maybe` (see
-- `Decode.agda`).  We discharge the `Maybe` for hypergraphs of the
-- form `⟪ f ⟫` by induction on the term `f`.  Each smart-constructor
-- case is a separate lemma.  Status:
--
--   * Constructive (no postulate):
--     - `decode-attempt-hEmpty` : `decode-attempt hEmpty ≡ just _`
--       (concrete lists ⇒ algorithm reduces by `refl`).
--     - `decode-attempt-hVar`   : `decode-attempt (hVar x) ≡ just _`
--       (singleton stack ⇒ algorithm reduces by `refl`).
--     - `decode-attempt-hSwap`  : reduces via `extract-prefix-from-↭`
--       (in `DecodeProperties.agda`) applied to `Perm.++-comm`.
--     - `decode-attempt-hGen`   : `extract-prefix-self` for the single
--       edge step, then `extract-prefix-from-↭` for the final
--       `R ++ [] ↭ R` bridge via `PermProp.++-identityʳ`.
--     - `decode-attempt-hId`    : structural recursion on `A`.
--     - `decode-attempt-subst₂` : `subst₂ refl refl` is the identity.
--
--   * Postulated (still): `hTensor`, `hCompose`.
--     These have non-trivial edge sets that require `extract-prefix`
--     to interact with `injL`/`injR`/`remap`-mapped lists.  Their
--     signatures *now take induction hypotheses* for the sub-
--     hypergraphs (matching the eventual proof shape); the bodies
--     remain postulated pending the disjoint-injection lifting
--     lemmas.
--
-- Composing the per-case lemmas gives a constructive proof of
-- `decode-attempt-Linear f : ∃ t. decode-attempt ⟪ f ⟫ ≡ just t`,
-- from which the total `decode` is defined as the projection.
-- `decode` and `bridge` live here (rather than in `Decoder.agda`) so
-- that `DecodeRoundtrip.agda` can refer to them without going through
-- `Decoder.agda` (avoiding a module cycle).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeAttempt (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; ⟪_⟫; range;
         hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose;
         module hTensor-impl; module hCompose-impl)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt; edge-step; extract-prefix; process-edges;
         process-all-edges; extract-exact)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-self; extract-prefix-from-↭;
         extract-prefix-↑ˡ-on-mixed-just; extract-prefix-↑ʳ-on-mixed-just;
         extract-prefix-↑ˡ-on-mixed-nothing; extract-prefix-↑ʳ-on-mixed-nothing;
         extract-prefix-↭-residual; extract-prefix-↭-nothing;
         extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Categories.Morphism FreeMonoidal using (_≅_)

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (_+_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

--------------------------------------------------------------------------------
-- Per-case lemmas, one for each smart constructor of `FromAPROP`.
--
-- Statement form: `∃ t. decode-attempt H ≡ just t` for the relevant
-- smart-constructor application `H`.  Inductive cases (hTensor /
-- hCompose) take the witness for the sub-hypergraphs as input.
--
-- The base cases `hEmpty` and `hVar` are *not* postulated — their
-- `dom`/`cod` are concrete enough that the algorithm reduces by `refl`.

decode-attempt-hEmpty
  : Σ[ t ∈ HomTerm (unflatten []) (unflatten []) ]
      decode-attempt hEmpty ≡ just t
decode-attempt-hEmpty = _ , refl

decode-attempt-hVar
  : ∀ (x : X)
  → Σ[ t ∈ HomTerm (unflatten (x ∷ [])) (unflatten (x ∷ [])) ]
      decode-attempt (hVar x) ≡ just t
decode-attempt-hVar x = _ , refl

--------------------------------------------------------------------------------
-- Extraction lemma: from `decode-attempt H ≡ just _` we can recover
-- the final stack of `process-all-edges` together with a permutation
-- to `H.cod`.  This is what makes the decode-attempt-hTensor IHs
-- usable in the body — without it, we know the algorithm succeeded
-- but can't reason about *why*.

decode-attempt-perm-from-just
  : ∀ {As Bs} (H : Hypergraph FlatGen As Bs)
  → ∃[ tH ] decode-attempt H ≡ just tH
  → ∃[ s_final ] ∃[ t' ]
       (process-all-edges H (Hypergraph.dom H) ≡ (s_final , t'))
     × (s_final Perm.↭ Hypergraph.cod H)
decode-attempt-perm-from-just H (tH , eq)
    with process-all-edges H (Hypergraph.dom H) in eq-proc
... | s_final , t'
    with extract-exact (Hypergraph.cod H) s_final in eq-ext
... | just perm = s_final , t' , refl , perm
... | nothing
    with eq
... | ()

--------------------------------------------------------------------------------
-- Decomposition of `process-edges` over `_++_`: the stack output of
-- `process-edges (xs ++ ys) s` factors as `process-edges ys` applied
-- to the result of `process-edges xs`.  The term-level composition is
-- not tracked here (we only need the stack to compose the per-edge
-- liftings).

process-edges-++-stack
  : ∀ {As Bs} (H : Hypergraph FlatGen As Bs)
      (xs ys : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → proj₁ (process-edges H (xs ++ ys) s)
    ≡ proj₁ (process-edges H ys (proj₁ (process-edges H xs s)))
process-edges-++-stack H []       ys s = refl
process-edges-++-stack H (e ∷ xs) ys s
    with edge-step H s e
... | s' , _ = process-edges-++-stack H xs ys s'

--------------------------------------------------------------------------------
-- Edge-step lifting for `hTensor`: when an edge is on the G-side
-- (resp. K-side), edge-step's result on the mixed stack factors
-- through the underlying single-side search.
--
-- Strategy: rewrite away the `ein-c` / `eout-c` reductions and the
-- inner extract-prefix's success, then bridge the resulting `++-assoc
-- + map-++` shape to the desired form via a single `subst` over an
-- equational-reasoning chain.

module _
  {As Bs Cs Ds : List X}
  (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Cs Ds)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module hT-impl = hTensor-impl G K

  edge-step-↑ˡ-on-mixed-just
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
        (rest-G : List (Fin G.nV))
        (p-G : xs-G Perm.↭ G.ein eG ++ rest-G)
    → extract-prefix (G.ein eG) xs-G ≡ just (rest-G , p-G)
    → ∃[ t ]
         edge-step (hTensor G K)
                   (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                   (eG ↑ˡ K.nE)
         ≡ (map (_↑ˡ K.nV) (G.eout eG ++ rest-G) ++ map (G.nV ↑ʳ_) ys , t)
  edge-step-↑ˡ-on-mixed-just eG xs-G ys rest-G p-G eq =
      subst (λ s → ∃[ t ]
                     edge-step (hTensor G K) stack (eG ↑ˡ K.nE)
                     ≡ (s , t))
            list-eq
            reduce-result
    where
      open ≡-Reasoning

      stack = map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys

      -- Transport `extract-prefix-↑ˡ-on-mixed-just`'s output from the
      -- `map (_↑ˡ K.nV) (G.ein eG)` form to the ein-c form Agda actually
      -- sees in `edge-step`'s body.  Wrapping the existential in `subst`'s
      -- predicate lets a single subst transport both the residual
      -- permutation and the equation simultaneously.
      eq-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE)) stack
                 ≡ just (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys , q)
      eq-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just ( map (_↑ˡ K.nV) rest-G
                                         ++ map (G.nV ↑ʳ_) ys
                                     , q ))
              (sym (hT-impl.ein-c-inj₁-red eG))
              (extract-prefix-↑ˡ-on-mixed-just K.nV (G.ein eG)
                                                xs-G ys rest-G p-G eq)

      reduce-result
        : ∃[ t ]
            edge-step (hTensor G K) stack (eG ↑ˡ K.nE)
            ≡ ( Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE)
                  ++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys)
              , t )
      reduce-result rewrite proj₂ eq-on-ein-c = _ , refl

      -- Equational chain bridging edge-step's raw output to the
      -- claimed lifted form; absorbs eout-c-inj₁-red, ++-assoc, map-++.
      list-eq : Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE)
                  ++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys)
              ≡ map (_↑ˡ K.nV) (G.eout eG ++ rest-G)
                  ++ map (G.nV ↑ʳ_) ys
      list-eq = begin
        Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE)
          ++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys)
        ≡⟨ cong (_++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys))
                (hT-impl.eout-c-inj₁-red eG) ⟩
        map (_↑ˡ K.nV) (G.eout eG)
          ++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys)
        ≡⟨ sym (++-assoc (map (_↑ˡ K.nV) (G.eout eG))
                          (map (_↑ˡ K.nV) rest-G)
                          (map (G.nV ↑ʳ_) ys)) ⟩
        (map (_↑ˡ K.nV) (G.eout eG) ++ map (_↑ˡ K.nV) rest-G)
          ++ map (G.nV ↑ʳ_) ys
        ≡⟨ cong (_++ map (G.nV ↑ʳ_) ys)
                (sym (map-++ (_↑ˡ K.nV) (G.eout eG) rest-G)) ⟩
        map (_↑ˡ K.nV) (G.eout eG ++ rest-G) ++ map (G.nV ↑ʳ_) ys
        ∎

  -- K-side symmetric: when the edge is on the K-side, edge-step on the
  -- mixed stack produces `map injR (K.eout eK)` *prepended* to the
  -- L-side and the K-residual.  Unlike the G-side, this output cannot
  -- be factored as `(map injL ?) ++ (map injR ?)` — the K-eouts sit on
  -- the *left* of the L-block, so we expose the literal stack shape and
  -- defer the permutation reasoning to `process-edges`-level lemmas.
  edge-step-↑ʳ-on-mixed-just
    : ∀ (eK : Fin K.nE)
        (xs : List (Fin G.nV))
        (ys-K : List (Fin K.nV))
        (rest-K : List (Fin K.nV))
        (p-K : ys-K Perm.↭ K.ein eK ++ rest-K)
    → extract-prefix (K.ein eK) ys-K ≡ just (rest-K , p-K)
    → ∃[ t ]
         edge-step (hTensor G K)
                   (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys-K)
                   (G.nE ↑ʳ eK)
         ≡ ( map (G.nV ↑ʳ_) (K.eout eK)
               ++ map (_↑ˡ K.nV) xs
               ++ map (G.nV ↑ʳ_) rest-K
           , t )
  edge-step-↑ʳ-on-mixed-just eK xs ys-K rest-K p-K eq =
      subst (λ s → ∃[ t ]
                     edge-step (hTensor G K) stack (G.nE ↑ʳ eK)
                     ≡ (s , t))
            list-eq
            reduce-result
    where
      stack = map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys-K

      -- Same single-subst trick as the G-side: wrap the existential
      -- in subst's predicate so one transport carries both residual
      -- permutation and equation across the ein-c reduction.
      eq-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) stack
                 ≡ just (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K , q)
      eq-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just ( map (_↑ˡ K.nV) xs
                                         ++ map (G.nV ↑ʳ_) rest-K
                                     , q ))
              (sym (hT-impl.ein-c-inj₂-red eK))
              (extract-prefix-↑ʳ-on-mixed-just G.nV (K.ein eK)
                                                xs ys-K rest-K p-K eq)

      reduce-result
        : ∃[ t ]
            edge-step (hTensor G K) stack (G.nE ↑ʳ eK)
            ≡ ( Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK)
                  ++ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K)
              , t )
      reduce-result rewrite proj₂ eq-on-ein-c = _ , refl

      -- Single `cong` step rewrites `eout-c (G.nE ↑ʳ eK)` to
      -- `map (G.nV ↑ʳ_) (K.eout eK)`; no associator / map-distribution
      -- needed because the eouts stay on the left.
      list-eq : Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK)
                  ++ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K)
              ≡ map (G.nV ↑ʳ_) (K.eout eK)
                  ++ map (_↑ˡ K.nV) xs
                  ++ map (G.nV ↑ʳ_) rest-K
      list-eq = cong (_++ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K))
                     (hT-impl.eout-c-inj₂-red eK)

  -- Failure-direction edge-step lifting (G-side).  When G's edge
  -- cannot fire (extract-prefix on G's stack returns `nothing`), the
  -- lifted edge-step on the mixed stack also cannot fire — by the
  -- nothing-lifting of extract-prefix.  Result: stack unchanged, term
  -- is identity.
  edge-step-↑ˡ-on-mixed-nothing
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → extract-prefix (G.ein eG) xs-G ≡ nothing
    → ∃[ t ]
         edge-step (hTensor G K)
                   (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                   (eG ↑ˡ K.nE)
         ≡ (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys , t)
  edge-step-↑ˡ-on-mixed-nothing eG xs-G ys eq = aux nothing-lifted
    where
      stack = map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (hT-impl.ein-c-inj₁-red eG))
              (extract-prefix-↑ˡ-on-mixed-nothing K.nV (G.ein eG) xs-G ys eq)

      aux : extract-prefix (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE)) stack
              ≡ nothing
          → ∃[ t ] edge-step (hTensor G K) stack (eG ↑ˡ K.nE) ≡ (stack , t)
      aux p rewrite p = _ , refl

  -- K-side failure: same shape as G-side failure.  Uses
  -- `extract-prefix-↑ʳ-on-mixed-nothing` and `ein-c-inj₂-red`.
  edge-step-↑ʳ-on-mixed-nothing
    : ∀ (eK : Fin K.nE)
        (xs : List (Fin G.nV))
        (ys-K : List (Fin K.nV))
    → extract-prefix (K.ein eK) ys-K ≡ nothing
    → ∃[ t ]
         edge-step (hTensor G K)
                   (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys-K)
                   (G.nE ↑ʳ eK)
         ≡ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys-K , t)
  edge-step-↑ʳ-on-mixed-nothing eK xs ys-K eq = aux nothing-lifted
    where
      stack = map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys-K

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (hT-impl.ein-c-inj₂-red eK))
              (extract-prefix-↑ʳ-on-mixed-nothing G.nV (K.ein eK) xs ys-K eq)

      aux : extract-prefix (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) stack
              ≡ nothing
          → ∃[ t ] edge-step (hTensor G K) stack (G.nE ↑ʳ eK) ≡ (stack , t)
      aux p rewrite p = _ , refl

  -- Unified G-side per-edge lemma: combines just/nothing into a single
  -- statement about edge-step's result on the mixed stack, which factors
  -- through G's edge-step's stack output.  Since G's edges only touch
  -- the L-side, the output stays in `(map injL _) ++ (map injR ys)` form
  -- regardless of whether the edge fired.
  edge-step-↑ˡ-on-mixed
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → ∃[ t ]
         edge-step (hTensor G K)
                   (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                   (eG ↑ˡ K.nE)
         ≡ ( map (_↑ˡ K.nV) (proj₁ (edge-step G xs-G eG))
               ++ map (G.nV ↑ʳ_) ys
           , t )
  edge-step-↑ˡ-on-mixed eG xs-G ys
      with extract-prefix (G.ein eG) xs-G in eq
  ... | just (rest , p) = edge-step-↑ˡ-on-mixed-just eG xs-G ys rest p eq
  ... | nothing         = edge-step-↑ˡ-on-mixed-nothing eG xs-G ys eq

  -- Iterate `edge-step-↑ˡ-on-mixed` over a list of G-edges.  By
  -- induction on `es`: each step reduces the lifted edge-step to the
  -- factored form, and the IH continues on the residual stack.
  process-edges-↑ˡ-on-mixed
    : ∀ (es : List (Fin G.nE))
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → ∃[ t ]
         process-edges (hTensor G K)
                       (map (_↑ˡ K.nE) es)
                       (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
         ≡ ( map (_↑ˡ K.nV) (proj₁ (process-edges G es xs-G))
               ++ map (G.nV ↑ʳ_) ys
           , t )
  process-edges-↑ˡ-on-mixed []       xs-G ys = _ , refl
  process-edges-↑ˡ-on-mixed (e ∷ es) xs-G ys
      with edge-step-↑ˡ-on-mixed e xs-G ys
  ... | _ , eq-edge
      with process-edges-↑ˡ-on-mixed es (proj₁ (edge-step G xs-G e)) ys
  ... | _ , eq-prefix
      rewrite eq-edge | eq-prefix = _ , refl

  --------------------------------------------------------------------
  -- K-side per-edge lifting on a permutation-equivalent input.
  --
  -- Unlike the G-side, K-edges' eouts get prepended to the front of
  -- the stack, breaking the `(map injL ?) ++ (map injR ?)` form.  We
  -- track only a permutation invariant: the lifted edge-step's
  -- output permutes to `L ++ map injR (proj₁ (edge-step K ys eK))`.
  --
  -- Strategy: case-split on K's edge-step; in each case use the
  -- foundation lemmas + permutation reasoning to lift to s.
  edge-step-↑ʳ-on-perm
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → ∃[ s' ] ∃[ t ]
         edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ (s' , t)
       × s' Perm.↭ map (_↑ˡ K.nV) xs
                     ++ map (G.nV ↑ʳ_) (proj₁ (edge-step K ys eK))
  edge-step-↑ʳ-on-perm eK s xs ys s↭std
      with extract-prefix (K.ein eK) ys in eq-K
  ... | just (rest , p-K) = R-out ++ r
                          , proj₁ edge-step-eq
                          , proj₂ edge-step-eq
                          , final-perm
    where
      open Perm.PermutationReasoning
      L     = map (_↑ˡ K.nV)  xs
      R-pre = map (G.nV ↑ʳ_)  (K.ein  eK)
      R-out = map (G.nV ↑ʳ_)  (K.eout eK)
      R-rst = map (G.nV ↑ʳ_)  rest

      -- Permute s so that K's ein elements sit at the front.  Used to
      -- feed `extract-prefix-↭-residual`, which requires the prefix
      -- exposed at the head.
      s↭shuffled : s Perm.↭ R-pre ++ (L ++ R-rst)
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        L ++ map (G.nV ↑ʳ_) ys
          ↭⟨ PermProp.++⁺ˡ L (PermProp.map⁺ (G.nV ↑ʳ_) p-K) ⟩
        L ++ map (G.nV ↑ʳ_) (K.ein eK ++ rest)
          ≡⟨ cong (L ++_) (map-++ (G.nV ↑ʳ_) (K.ein eK) rest) ⟩
        L ++ (R-pre ++ R-rst)
          ≡⟨ sym (++-assoc L R-pre R-rst) ⟩
        (L ++ R-pre) ++ R-rst
          ↭⟨ PermProp.++⁺ʳ R-rst (PermProp.++-comm L R-pre) ⟩
        (R-pre ++ L) ++ R-rst
          ≡⟨ ++-assoc R-pre L R-rst ⟩
        R-pre ++ (L ++ R-rst)
          ∎

      -- Pull the residual `r` and its permutation out via the
      -- partial form of `extract-prefix-from-↭`.
      extract-step
        : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p)
                       × (L ++ R-rst) Perm.↭ r
      extract-step =
        extract-prefix-↭-residual R-pre s (L ++ R-rst) s↭shuffled

      r  = proj₁ extract-step
      r↭ : (L ++ R-rst) Perm.↭ r
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      -- Bridge `ein-c-inj₂-red` so the lifted extract result is
      -- expressed in terms of the algorithm's actual lookup.
      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) s
                 ≡ just (r , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
              (sym (hT-impl.ein-c-inj₂-red eK))
              (proj₁ (proj₂ extract-step) ,
               proj₁ (proj₂ (proj₂ extract-step)))

      -- After rewriting the lifted extract's success, edge-step
      -- reduces to `(eout-c (G.nE ↑ʳ eK) ++ r , _)`.
      reduce-result
        : ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK)
                   ≡ (Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ r , t)
      reduce-result rewrite proj₂ extract-on-ein-c = _ , refl

      -- Use `eout-c-inj₂-red` to convert eout-c to `R-out`.
      edge-step-eq
        : ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ (R-out ++ r , t)
      edge-step-eq =
        subst (λ ks → ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK)
                              ≡ (ks ++ r , t))
              (hT-impl.eout-c-inj₂-red eK)
              reduce-result

      -- Show R-out ++ r permutes to `L ++ map injR (K.eout eK ++ rest)`.
      final-perm
        : R-out ++ r Perm.↭ L ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest)
      final-perm = begin
        R-out ++ r
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ (L ++ R-rst)
          ≡⟨ sym (++-assoc R-out L R-rst) ⟩
        (R-out ++ L) ++ R-rst
          ↭⟨ PermProp.++⁺ʳ R-rst (PermProp.++-comm R-out L) ⟩
        (L ++ R-out) ++ R-rst
          ≡⟨ ++-assoc L R-out R-rst ⟩
        L ++ (R-out ++ R-rst)
          ≡⟨ cong (L ++_) (sym (map-++ (G.nV ↑ʳ_) (K.eout eK) rest)) ⟩
        L ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest)
          ∎

  ... | nothing = nothing-result
    where
      open Perm.PermutationReasoning
      L = map (_↑ˡ K.nV) xs
      R = map (G.nV ↑ʳ_) ys

      nothing-on-std : extract-prefix
                         (map (G.nV ↑ʳ_) (K.ein eK)) (L ++ R) ≡ nothing
      nothing-on-std =
        extract-prefix-↑ʳ-on-mixed-nothing G.nV (K.ein eK) xs ys eq-K

      nothing-on-s : extract-prefix (map (G.nV ↑ʳ_) (K.ein eK)) s ≡ nothing
      nothing-on-s =
        extract-prefix-↭-nothing
          (map (G.nV ↑ʳ_) (K.ein eK))
          (L ++ R) s
          (Perm.↭-sym s↭std)
          nothing-on-std

      nothing-on-ein-c
        : extract-prefix
            (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) s
            ≡ nothing
      nothing-on-ein-c =
        subst (λ ks → extract-prefix ks s ≡ nothing)
              (sym (hT-impl.ein-c-inj₂-red eK))
              nothing-on-s

      reduce-to-id
        : ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ (s , t)
      reduce-to-id rewrite nothing-on-ein-c = _ , refl

      nothing-result : ∃[ s' ] ∃[ t ]
                         edge-step (hTensor G K) s (G.nE ↑ʳ eK)
                           ≡ (s' , t)
                       × s' Perm.↭ L ++ R
      nothing-result = s , proj₁ reduce-to-id , proj₂ reduce-to-id , s↭std

  -- Iterate the perm-respecting per-edge lifting over a list of K-edges.
  -- The output stack permutes to `L ++ map injR (proj₁ (process-edges K es ys))`.
  process-edges-↑ʳ-on-perm
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → ∃[ s' ] ∃[ t ]
         process-edges (hTensor G K) (map (G.nE ↑ʳ_) es) s ≡ (s' , t)
       × s' Perm.↭ map (_↑ˡ K.nV) xs
                     ++ map (G.nV ↑ʳ_) (proj₁ (process-edges K es ys))
  process-edges-↑ʳ-on-perm []       s xs ys s↭std =
    s , _ , refl , s↭std
  process-edges-↑ʳ-on-perm (e ∷ es) s xs ys s↭std
      with edge-step-↑ʳ-on-perm e s xs ys s↭std
  ... | _ , _ , eq-edge , perm-edge
      with process-edges-↑ʳ-on-perm es _ xs (proj₁ (edge-step K ys e)) perm-edge
  ... | _ , _ , eq-rec , perm-rec
      rewrite eq-edge | eq-rec = _ , _ , refl , perm-rec

--------------------------------------------------------------------------------
-- hCompose lifts.  Parallel to hTensor lifts above, but:
--   * G-side: pure-L stack `map injL ?` (no R-side mixing) — uses
--     `extract-prefix-via-injective-{just,nothing}` with f = injL.
--   * K-side: stack ↭ `map remap ?` — uses extract-prefix-via-injective-
--     nothing with f = remap (whose injectivity comes from
--     `Lin.hCompose-Linear-utils.remap-injective`, requiring Linear G +
--     Linear K).

module _
  {As Bs Cs : List X}
  (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Bs Cs)
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K
  -- Brings into scope: injL, injR, remap, ein-c, eout-c, vlab-c,
  -- ein-c-inj₁-red, eout-c-inj₁-red, ein-c-inj₂-red, eout-c-inj₂-red,
  -- and helpers map-remap-K-dom, remap-noDom, remap-injective.
  open Lin.hCompose-Linear-utils G K lin-G lin-K

  --------------------------------------------------------------------
  -- G-side: per-edge lifting on a pure-L stack `map injL xs`.

  edge-step-↑ˡ-pure-L-just
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
        (rest : List (Fin G.nV)) (p : xs Perm.↭ G.ein eG ++ rest)
    → extract-prefix (G.ein eG) xs ≡ just (rest , p)
    → ∃[ t ]
         edge-step (hCompose G K) (map (_↑ˡ K.nV) xs) (eG ↑ˡ K.nE)
         ≡ (map (_↑ˡ K.nV) (G.eout eG ++ rest) , t)
  edge-step-↑ˡ-pure-L-just eG xs rest p eq =
      subst (λ s → ∃[ t ] edge-step (hCompose G K) stack (eG ↑ˡ K.nE)
                            ≡ (s , t))
            list-eq
            reduce-result
    where
      open ≡-Reasoning
      stack = map (_↑ˡ K.nV) xs

      eq-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hCompose G K) (eG ↑ˡ K.nE)) stack
                 ≡ just (map (_↑ˡ K.nV) rest , q)
      eq-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just (map (_↑ˡ K.nV) rest , q))
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-just (_↑ˡ K.nV) (inject+-inj K.nV)
                                                  (G.ein eG) xs rest p eq)

      reduce-result
        : ∃[ t ] edge-step (hCompose G K) stack (eG ↑ˡ K.nE)
                  ≡ (Hypergraph.eout (hCompose G K) (eG ↑ˡ K.nE)
                       ++ map (_↑ˡ K.nV) rest , t)
      reduce-result rewrite proj₂ eq-on-ein-c = _ , refl

      list-eq : Hypergraph.eout (hCompose G K) (eG ↑ˡ K.nE)
                  ++ map (_↑ˡ K.nV) rest
              ≡ map (_↑ˡ K.nV) (G.eout eG ++ rest)
      list-eq = begin
        Hypergraph.eout (hCompose G K) (eG ↑ˡ K.nE)
          ++ map (_↑ˡ K.nV) rest
          ≡⟨ cong (_++ map (_↑ˡ K.nV) rest) (eout-c-inj₁-red eG) ⟩
        map (_↑ˡ K.nV) (G.eout eG) ++ map (_↑ˡ K.nV) rest
          ≡⟨ sym (map-++ (_↑ˡ K.nV) (G.eout eG) rest) ⟩
        map (_↑ˡ K.nV) (G.eout eG ++ rest)
          ∎

  edge-step-↑ˡ-pure-L-nothing
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → extract-prefix (G.ein eG) xs ≡ nothing
    → ∃[ t ]
         edge-step (hCompose G K) (map (_↑ˡ K.nV) xs) (eG ↑ˡ K.nE)
         ≡ (map (_↑ˡ K.nV) xs , t)
  edge-step-↑ˡ-pure-L-nothing eG xs eq = aux nothing-lifted
    where
      stack = map (_↑ˡ K.nV) xs

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hCompose G K) (eG ↑ˡ K.nE))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-nothing (_↑ˡ K.nV)
                                                     (inject+-inj K.nV)
                                                     (G.ein eG) xs eq)

      aux : extract-prefix (Hypergraph.ein (hCompose G K) (eG ↑ˡ K.nE)) stack
              ≡ nothing
          → ∃[ t ] edge-step (hCompose G K) stack (eG ↑ˡ K.nE) ≡ (stack , t)
      aux p rewrite p = _ , refl

  edge-step-↑ˡ-pure-L
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → ∃[ t ]
         edge-step (hCompose G K) (map (_↑ˡ K.nV) xs) (eG ↑ˡ K.nE)
         ≡ (map (_↑ˡ K.nV) (proj₁ (edge-step G xs eG)) , t)
  edge-step-↑ˡ-pure-L eG xs
      with extract-prefix (G.ein eG) xs in eq
  ... | just (rest , p) = edge-step-↑ˡ-pure-L-just eG xs rest p eq
  ... | nothing         = edge-step-↑ˡ-pure-L-nothing eG xs eq

  process-edges-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → ∃[ t ]
         process-edges (hCompose G K) (map (_↑ˡ K.nE) es) (map (_↑ˡ K.nV) xs)
         ≡ (map (_↑ˡ K.nV) (proj₁ (process-edges G es xs)) , t)
  process-edges-↑ˡ-pure-L []       xs = _ , refl
  process-edges-↑ˡ-pure-L (e ∷ es) xs
      with edge-step-↑ˡ-pure-L e xs
  ... | _ , eq-edge
      with process-edges-↑ˡ-pure-L es (proj₁ (edge-step G xs e))
  ... | _ , eq-prefix
      rewrite eq-edge | eq-prefix = _ , refl

  --------------------------------------------------------------------
  -- K-side: perm-respecting per-edge lifting via remap.  Stack
  -- assumed `↭ map remap ys`; output stack `↭ map remap (proj₁
  -- (edge-step K ys eK))`.

  edge-step-↑ʳ-via-remap
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + K.nV)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remap ys
    → ∃[ s' ] ∃[ t ]
         (edge-step (hCompose G K) s (G.nE ↑ʳ eK) ≡ (s' , t))
       × (s' Perm.↭ map remap (proj₁ (edge-step K ys eK)))
  edge-step-↑ʳ-via-remap eK s ys s↭std
      with extract-prefix (K.ein eK) ys in eq-K
  ... | just (rest , p-K) =
        map remap (K.eout eK) ++ r
      , proj₁ edge-step-eq
      , proj₂ edge-step-eq
      , final-perm
    where
      open Perm.PermutationReasoning
      R-pre = map remap (K.ein eK)
      R-out = map remap (K.eout eK)
      R-rst = map remap rest

      -- Permute s to expose K.ein eK as the prefix.
      s↭shuffled : s Perm.↭ R-pre ++ R-rst
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        map remap ys
          ↭⟨ PermProp.map⁺ remap p-K ⟩
        map remap (K.ein eK ++ rest)
          ≡⟨ map-++ remap (K.ein eK) rest ⟩
        R-pre ++ R-rst
          ∎

      extract-step
        : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p) × R-rst Perm.↭ r
      extract-step = extract-prefix-↭-residual R-pre s R-rst s↭shuffled

      r = proj₁ extract-step
      r↭ : R-rst Perm.↭ r
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hCompose G K) (G.nE ↑ʳ eK)) s
                 ≡ just (r , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
              (sym (ein-c-inj₂-red eK))
              (proj₁ (proj₂ extract-step) ,
               proj₁ (proj₂ (proj₂ extract-step)))

      reduce-result
        : ∃[ t ] edge-step (hCompose G K) s (G.nE ↑ʳ eK)
                  ≡ (Hypergraph.eout (hCompose G K) (G.nE ↑ʳ eK) ++ r , t)
      reduce-result rewrite proj₂ extract-on-ein-c = _ , refl

      edge-step-eq
        : ∃[ t ] edge-step (hCompose G K) s (G.nE ↑ʳ eK) ≡ (R-out ++ r , t)
      edge-step-eq =
        subst (λ ks → ∃[ t ] edge-step (hCompose G K) s (G.nE ↑ʳ eK)
                              ≡ (ks ++ r , t))
              (eout-c-inj₂-red eK)
              reduce-result

      final-perm : R-out ++ r Perm.↭ map remap (K.eout eK ++ rest)
      final-perm = begin
        R-out ++ r
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ R-rst
          ≡⟨ sym (map-++ remap (K.eout eK) rest) ⟩
        map remap (K.eout eK ++ rest)
          ∎

  ... | nothing = nothing-result
    where
      nothing-on-std
        : extract-prefix (map remap (K.ein eK)) (map remap ys) ≡ nothing
      nothing-on-std =
        extract-prefix-via-injective-nothing remap remap-injective
                                              (K.ein eK) ys eq-K

      nothing-on-s
        : extract-prefix (map remap (K.ein eK)) s ≡ nothing
      nothing-on-s =
        extract-prefix-↭-nothing
          (map remap (K.ein eK)) (map remap ys) s
          (Perm.↭-sym s↭std) nothing-on-std

      nothing-on-ein-c
        : extract-prefix
            (Hypergraph.ein (hCompose G K) (G.nE ↑ʳ eK)) s ≡ nothing
      nothing-on-ein-c =
        subst (λ ks → extract-prefix ks s ≡ nothing)
              (sym (ein-c-inj₂-red eK))
              nothing-on-s

      reduce-to-id
        : ∃[ t ] edge-step (hCompose G K) s (G.nE ↑ʳ eK) ≡ (s , t)
      reduce-to-id rewrite nothing-on-ein-c = _ , refl

      nothing-result
        : ∃[ s' ] ∃[ t ]
             (edge-step (hCompose G K) s (G.nE ↑ʳ eK) ≡ (s' , t))
           × (s' Perm.↭ map remap ys)
      nothing-result = s , proj₁ reduce-to-id , proj₂ reduce-to-id , s↭std

  process-edges-↑ʳ-via-remap
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remap ys
    → ∃[ s' ] ∃[ t ]
         (process-edges (hCompose G K) (map (G.nE ↑ʳ_) es) s ≡ (s' , t))
       × (s' Perm.↭ map remap (proj₁ (process-edges K es ys)))
  process-edges-↑ʳ-via-remap []       s ys s↭std =
    s , _ , refl , s↭std
  process-edges-↑ʳ-via-remap (e ∷ es) s ys s↭std
      with edge-step-↑ʳ-via-remap e s ys s↭std
  ... | _ , _ , eq-edge , perm-edge
      with process-edges-↑ʳ-via-remap es _ (proj₁ (edge-step K ys e)) perm-edge
  ... | _ , _ , eq-rec , perm-rec
      rewrite eq-edge | eq-rec = _ , _ , refl , perm-rec

--------------------------------------------------------------------------------
-- `hSwap A B`: nE = 0, dom = L ++ R, cod = R ++ L (where
-- L = map (_↑ˡ nB) (range nA), R = map (nA ↑ʳ_) (range nB)).
-- `process-all-edges` returns (dom, id) trivially since nE = 0.
-- Then `extract-exact (R ++ L) (L ++ R)` succeeds because
-- (L ++ R) ↭ (R ++ L) by stdlib's `++-comm`, and
-- `extract-prefix-from-↭` discharges the search.

decode-attempt-hSwap
  : ∀ (A B : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (flatten A ++ flatten B))
                   (unflatten (flatten B ++ flatten A)) ]
      decode-attempt (hSwap A B) ≡ just t
decode-attempt-hSwap A B
    with extract-prefix-from-↭
           (map (_↑ˡ length (flatten B)) (range (length (flatten A)))
            ++ map (length (flatten A) ↑ʳ_) (range (length (flatten B))))
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))
            ++ map (_↑ˡ length (flatten B)) (range (length (flatten A))))
           (PermProp.++-comm
             (map (_↑ˡ length (flatten B)) (range (length (flatten A))))
             (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))))
... | p , eq rewrite eq = _ , refl

--------------------------------------------------------------------------------
-- `hGen g`: nE = 1, ein 0 = dom = L, eout 0 = cod = R (where
-- L = map (_↑ˡ nB) (range nA), R = map (nA ↑ʳ_) (range nB)).
--
-- `process-all-edges` runs the single edge:
--   `edge-step L 0` calls `extract-prefix L L`, which succeeds by
--   `extract-prefix-self`.  After the edge the stack becomes `R ++ []`.
--
-- The final `extract-exact R (R ++ [])` then needs `(R ++ []) ↭ R`,
-- discharged by `PermProp.++-identityʳ` + `extract-prefix-from-↭`.

decode-attempt-hGen
  : ∀ {A B : ObjTerm} (g : mor A B)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten B)) ]
      decode-attempt (hGen g) ≡ just t
decode-attempt-hGen {A} {B} g
    with extract-prefix-self
           (map (_↑ˡ length (flatten B)) (range (length (flatten A))))
... | _ , eq1 rewrite eq1
    with extract-prefix-from-↭
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B))) ++ [])
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B))))
           (PermProp.++-identityʳ
             (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))))
... | _ , eq2 rewrite eq2 = _ , refl

-- `decode-attempt-hTensor` and `decode-attempt-hCompose` are stated
-- *with* induction hypotheses for the sub-hypergraphs.  This is the
-- API that the eventual constructive proof needs — even though the
-- bodies are still postulated, the IHs are now plumbed through
-- `decode-attempt-Linear` (so a future proof can use them without
-- changing the call sites again).
--
-- The proof shape (sketch):
--   * `process-all-edges` factors via stdlib's
--     `Invariant.range-++ : range (n + m) ≡ map _↑ˡ_ (range n) ++ map _↑ʳ_ (range m)`
--     and a `process-edges-++` decomposition (provable by induction).
--   * Each branch (G's edges then K's) interacts only with one side
--     of the disjoint-injection stack.  This requires lifting lemmas
--     analogous to `extract-prefix-from-↭` but specialised to
--     `extract-prefix (map injL ks) (map injL xs ++ map injR ys)` —
--     the proofs reuse `disj-L-R` (Invariant) to skip the wrong-side
--     prefix and `inject+-inj`/`raise-inj` to thread through the
--     matching side.
--   * The final `extract-exact cod final-stack` succeeds by
--     `extract-exact-self` on the (provably equal) `cod`.

--------------------------------------------------------------------------------
-- Inverse of `decode-attempt-perm-from-just`: from a final stack with
-- a permutation to `H.cod`, derive `decode-attempt H ≡ just _`.
-- This is what we feed at the end of `decode-attempt-hTensor`.

decode-attempt-from-perm
  : ∀ {As Bs} (H : Hypergraph FlatGen As Bs)
  → ∃[ s_final ] ∃[ t' ]
       (process-all-edges H (Hypergraph.dom H) ≡ (s_final , t'))
     × (s_final Perm.↭ Hypergraph.cod H)
  → Σ[ t ∈ HomTerm (unflatten As) (unflatten Bs) ]
      decode-attempt H ≡ just t
decode-attempt-from-perm H (s_final , t' , eq-proc , perm)
    with extract-prefix-from-↭ s_final (Hypergraph.cod H) perm
... | _ , eq-prefix
    rewrite eq-proc | eq-prefix = _ , refl

--------------------------------------------------------------------------------
-- `decode-attempt-hTensor`: combines the per-edge / process-edges
-- liftings into a constructive proof.
--
-- Strategy:
--   1. Extract `s_G_final ↭ G.cod` and `s_K_final ↭ K.cod` via
--      `decode-attempt-perm-from-just`.
--   2. Factor `process-all-edges (hTensor G K) hTensor.dom` via
--      `Invariant.range-++` and `process-edges-++-stack`.
--   3. Apply `process-edges-↑ˡ-on-mixed` for the G-edges block,
--      yielding a stack of form `map injL s_G_final ++ map injR K.dom`.
--   4. Apply `process-edges-↑ʳ-on-perm` for the K-edges block (with
--      reflexivity as the input perm), yielding a stack `s_K'` with
--      `s_K' ↭ map injL s_G_final ++ map injR s_K_final`.
--   5. Combine `perm-G`, `perm-K` via `map⁺` and `++⁺` to get
--      `s_K' ↭ map injL G.cod ++ map injR K.cod = hTensor.cod`.
--   6. Feed to `decode-attempt-from-perm`.

decode-attempt-hTensor
  : ∀ {As Bs Cs Ds : List X}
      (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Cs Ds)
  → (∃[ tG ] decode-attempt G ≡ just tG)
  → (∃[ tK ] decode-attempt K ≡ just tK)
  → Σ[ t ∈ HomTerm (unflatten (As ++ Cs)) (unflatten (Bs ++ Ds)) ]
      decode-attempt (hTensor G K) ≡ just t
decode-attempt-hTensor {As} {Bs} {Cs} {Ds} G K ih-G ih-K =
    decode-attempt-from-perm (hTensor G K)
      (proj₁ proc , proj₂ proc , refl , perm-final)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open Perm.PermutationReasoning

    -- Extract from IHs.
    ih-G' = decode-attempt-perm-from-just G ih-G
    s_G_final = proj₁ ih-G'
    eq-G = proj₁ (proj₂ (proj₂ ih-G'))
    perm-G = proj₂ (proj₂ (proj₂ ih-G'))

    ih-K' = decode-attempt-perm-from-just K ih-K
    s_K_final = proj₁ ih-K'
    eq-K = proj₁ (proj₂ (proj₂ ih-K'))
    perm-K = proj₂ (proj₂ (proj₂ ih-K'))

    -- The full process-all-edges call we want to compute.
    proc = process-all-edges (hTensor G K) (Hypergraph.dom (hTensor G K))

    -- After the G-edges block.
    after-G-stack = proj₁ (process-edges (hTensor G K)
                            (map (_↑ˡ K.nE) (range G.nE))
                            (Hypergraph.dom (hTensor G K)))

    -- G-side process-edges lifting: after-G-stack equals the standard
    -- form `map injL G.s_G_final ++ map injR K.dom`.
    G-lift = process-edges-↑ˡ-on-mixed G K (range G.nE) G.dom K.dom

    after-G-≡ : after-G-stack
              ≡ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) K.dom
    after-G-≡ = trans (cong proj₁ (proj₂ G-lift))
                       (cong (λ x → map (_↑ˡ K.nV) x ++ map (G.nV ↑ʳ_) K.dom)
                             (cong proj₁ eq-G))

    after-G-↭-std : after-G-stack
                  Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) K.dom
    after-G-↭-std = Perm.↭-reflexive after-G-≡

    -- K-side perm-respecting process-edges lifting.
    K-lift = process-edges-↑ʳ-on-perm G K (range K.nE) after-G-stack
              s_G_final K.dom after-G-↭-std

    s_K' = proj₁ K-lift
    K-lift-eq   = proj₁ (proj₂ (proj₂ K-lift))
    K-lift-perm = proj₂ (proj₂ (proj₂ K-lift))

    -- Bridge: `proj₁ proc ≡ s_K'`.
    -- proc = process-edges (hTensor G K) (range (G.nE + K.nE)) hTensor.dom
    --      ≡ process-edges (hTensor G K) (map (_↑ˡ K.nE) (range G.nE)
    --                                  ++ map (G.nE ↑ʳ_) (range K.nE)) hTensor.dom
    --      stack-projects to (process-edges-++-stack)
    --      ≡ process-edges (hTensor G K) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
    --      ≡ (s_K' , _) by K-lift-eq
    proc-≡-s_K' : proj₁ proc ≡ s_K'
    proc-≡-s_K' =
      trans (cong (λ es → proj₁ (process-edges (hTensor G K) es
                                  (Hypergraph.dom (hTensor G K))))
                  (Inv.range-++ G.nE K.nE))
            (trans (process-edges-++-stack (hTensor G K)
                     (map (_↑ˡ K.nE) (range G.nE))
                     (map (G.nE ↑ʳ_) (range K.nE))
                     (Hypergraph.dom (hTensor G K)))
                   (cong proj₁ K-lift-eq))

    -- The K-lift's perm output uses `proj₁ (process-edges K (range K.nE) K.dom)`.
    -- Substitute via eq-K to get `s_K_final`.
    K-final-perm
      : s_K' Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) s_K_final
    K-final-perm =
      subst (λ x → s_K' Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) x)
            (cong proj₁ eq-K)
            K-lift-perm

    -- Combine perms: s_K' ↭ map injL G.cod ++ map injR K.cod = hTensor.cod.
    perm-final : proj₁ proc Perm.↭ Hypergraph.cod (hTensor G K)
    perm-final = begin
      proj₁ proc
        ≡⟨ proc-≡-s_K' ⟩
      s_K'
        ↭⟨ K-final-perm ⟩
      map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) s_K_final
        ↭⟨ PermProp.++⁺ (PermProp.map⁺ (_↑ˡ K.nV) perm-G)
                         (PermProp.map⁺ (G.nV ↑ʳ_) perm-K) ⟩
      map (_↑ˡ K.nV) G.cod ++ map (G.nV ↑ʳ_) K.cod
        ∎

--------------------------------------------------------------------------------
-- `decode-attempt-hCompose`: combines G-side and K-side liftings,
-- using `hCompose-Linear-utils.map-remap-K-dom` to bridge from
-- `map injL G.cod` (after G-edges) to `map remap K.dom` (start of
-- K-edges).
--
-- Strategy:
--   1. Extract `s_G_final ↭ G.cod` and `s_K_final ↭ K.cod` via
--      `decode-attempt-perm-from-just`.
--   2. Factor `process-all-edges (hCompose G K)` via
--      `Invariant.range-++` and `process-edges-++-stack`.
--   3. G-edges block: `process-edges-↑ˡ-pure-L` reduces to
--      `map injL s_G_final`.
--   4. Bridge to K-side: `map injL s_G_final ↭ map injL G.cod ≡
--      map remap K.dom`.
--   5. K-edges block: `process-edges-↑ʳ-via-remap` (with the bridge
--      perm as input) yields `s_K' ↭ map remap s_K_final`.
--   6. Combine via `perm-K`: `map remap s_K_final ↭ map remap K.cod
--      = (hCompose G K).cod`.
--   7. Feed to `decode-attempt-from-perm`.

decode-attempt-hCompose
  : ∀ {As Bs Cs : List X}
      (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Bs Cs)
  → Lin.Linear G → Lin.Linear K
  → (∃[ tG ] decode-attempt G ≡ just tG)
  → (∃[ tK ] decode-attempt K ≡ just tK)
  → Σ[ t ∈ HomTerm (unflatten As) (unflatten Cs) ]
      decode-attempt (hCompose G K) ≡ just t
decode-attempt-hCompose {As} {Bs} {Cs} G K lin-G lin-K ih-G ih-K =
    decode-attempt-from-perm (hCompose G K)
      (proj₁ proc , proj₂ proc , refl , perm-final)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open Lin.hCompose-Linear-utils G K lin-G lin-K
    open Perm.PermutationReasoning

    -- Extract from IHs.
    ih-G' = decode-attempt-perm-from-just G ih-G
    s_G_final = proj₁ ih-G'
    eq-G = proj₁ (proj₂ (proj₂ ih-G'))
    perm-G = proj₂ (proj₂ (proj₂ ih-G'))

    ih-K' = decode-attempt-perm-from-just K ih-K
    s_K_final = proj₁ ih-K'
    eq-K = proj₁ (proj₂ (proj₂ ih-K'))
    perm-K = proj₂ (proj₂ (proj₂ ih-K'))

    proc = process-all-edges (hCompose G K) (Hypergraph.dom (hCompose G K))

    -- Stack after G-edges: equals `map injL s_G_final`.
    after-G-stack = proj₁ (process-edges (hCompose G K)
                            (map (_↑ˡ K.nE) (range G.nE))
                            (Hypergraph.dom (hCompose G K)))

    G-lift = process-edges-↑ˡ-pure-L G K lin-G lin-K (range G.nE) G.dom

    after-G-≡ : after-G-stack ≡ map (_↑ˡ K.nV) s_G_final
    after-G-≡ = trans (cong proj₁ (proj₂ G-lift))
                       (cong (map (_↑ˡ K.nV)) (cong proj₁ eq-G))

    -- Bridge: after-G-stack ↭ map remap K.dom.
    -- Via perm-G + map-remap-K-dom.
    after-G-↭-remap-Kdom
      : after-G-stack Perm.↭ map remap K.dom
    after-G-↭-remap-Kdom = begin
      after-G-stack
        ≡⟨ after-G-≡ ⟩
      map (_↑ˡ K.nV) s_G_final
        ↭⟨ PermProp.map⁺ (_↑ˡ K.nV) perm-G ⟩
      map (_↑ˡ K.nV) G.cod
        ≡⟨ sym map-remap-K-dom ⟩
      map remap K.dom
        ∎

    -- K-side perm-respecting lift.
    K-lift = process-edges-↑ʳ-via-remap G K lin-G lin-K
              (range K.nE) after-G-stack K.dom after-G-↭-remap-Kdom

    s_K' = proj₁ K-lift
    K-lift-eq   = proj₁ (proj₂ (proj₂ K-lift))
    K-lift-perm = proj₂ (proj₂ (proj₂ K-lift))

    -- proj₁ proc ≡ s_K' via range-++ + process-edges-++-stack +
    -- the K-lift's equation.
    proc-≡-s_K' : proj₁ proc ≡ s_K'
    proc-≡-s_K' =
      trans (cong (λ es → proj₁ (process-edges (hCompose G K) es
                                  (Hypergraph.dom (hCompose G K))))
                  (Inv.range-++ G.nE K.nE))
            (trans (process-edges-++-stack (hCompose G K)
                     (map (_↑ˡ K.nE) (range G.nE))
                     (map (G.nE ↑ʳ_) (range K.nE))
                     (Hypergraph.dom (hCompose G K)))
                   (cong proj₁ K-lift-eq))

    -- Substitute proj₁ K's process-edges output for s_K_final.
    K-final-perm
      : s_K' Perm.↭ map remap s_K_final
    K-final-perm =
      subst (λ x → s_K' Perm.↭ map remap x)
            (cong proj₁ eq-K)
            K-lift-perm

    perm-final : proj₁ proc Perm.↭ Hypergraph.cod (hCompose G K)
    perm-final = begin
      proj₁ proc
        ≡⟨ proc-≡-s_K' ⟩
      s_K'
        ↭⟨ K-final-perm ⟩
      map remap s_K_final
        ↭⟨ PermProp.map⁺ remap perm-K ⟩
      map remap K.cod
        ∎

--------------------------------------------------------------------------------
-- `subst₂` transport: pure type-level shuffling.  Generalized to handle
-- *non-`refl`* equations by exposing the transport explicitly.
--
-- The old definition (`decode-attempt-subst₂ H refl refl (t , p) = (t , p)`)
-- only fired when both `eq-As` and `eq-Bs` were *literally* `refl`.  For
-- ~++-identityʳ (flatten A)~ etc. — which only reduce to `refl` for
-- *concrete* `A` — the function was stuck, leaving `decode (ρ⇒ {A})`
-- opaque for symbolic `A`.
--
-- The new definition produces, for *any* equations, a result whose
-- first projection is the explicit transport
-- `subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) t`.
-- Downstream proofs (notably `decode-roundtrip-ρ⇒/ρ⇐/α⇒/α⇐`) can then
-- reason about the transported term directly, using
-- `subst`-of-the-result combinators rather than relying on definitional
-- reduction to fire.

private
  -- Maybe-of-HomTerm subst₂ commutes with `just`.  Refl-refl-defined,
  -- so stuck on non-refl args at the term level — but the *type* of the
  -- equation is well-formed for any args.
  subst₂-Maybe-of-HomTerm-just
    : ∀ {As Bs As' Bs' : List X}
        (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
        (t : HomTerm (unflatten As) (unflatten Bs))
    → subst₂ (λ X Y → Maybe (HomTerm (unflatten X) (unflatten Y)))
            eq-As eq-Bs (just t)
      ≡ just (subst₂ HomTerm
                    (cong unflatten eq-As)
                    (cong unflatten eq-Bs)
                    t)
  subst₂-Maybe-of-HomTerm-just refl refl t = refl

  -- `decode-attempt` commutes with the `subst₂` on `Hypergraph`'s
  -- boundary types.  Same shape: refl-refl is `refl`, non-refl is
  -- well-typed but doesn't reduce.
  decode-attempt-resp-subst₂
    : ∀ {As Bs As' Bs' : List X} (H : Hypergraph FlatGen As Bs)
        (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
    → decode-attempt (subst₂ (Hypergraph FlatGen) eq-As eq-Bs H)
      ≡ subst₂ (λ X Y → Maybe (HomTerm (unflatten X) (unflatten Y)))
              eq-As eq-Bs
              (decode-attempt H)
  decode-attempt-resp-subst₂ H refl refl = refl

decode-attempt-subst₂
  : ∀ {As Bs As' Bs' : List X} (H : Hypergraph FlatGen As Bs)
      (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
  → Σ[ t ∈ HomTerm (unflatten As) (unflatten Bs) ] decode-attempt H ≡ just t
  → Σ[ t' ∈ HomTerm (unflatten As') (unflatten Bs') ]
      decode-attempt (subst₂ (Hypergraph FlatGen) eq-As eq-Bs H) ≡ just t'
decode-attempt-subst₂ {As} {Bs} {As'} {Bs'} H eq-As eq-Bs (t , p) =
  ( subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) t
  , trans (decode-attempt-resp-subst₂ H eq-As eq-Bs)
          (trans (cong (subst₂ (λ X Y → Maybe (HomTerm (unflatten X) (unflatten Y)))
                              eq-As eq-Bs) p)
                 (subst₂-Maybe-of-HomTerm-just eq-As eq-Bs t))
  )

-- Now the first projection is just the explicit `subst₂ HomTerm ... t`,
-- definitionally — making it usable in downstream `≈Term` chains.
decode-attempt-subst₂-proj₁
  : ∀ {As Bs As' Bs' : List X} (H : Hypergraph FlatGen As Bs)
      (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
      (w : Σ[ t ∈ HomTerm (unflatten As) (unflatten Bs) ] decode-attempt H ≡ just t)
  → proj₁ (decode-attempt-subst₂ H eq-As eq-Bs w)
  ≡ subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) (proj₁ w)
decode-attempt-subst₂-proj₁ H eq-As eq-Bs (t , p) = refl

--------------------------------------------------------------------------------
-- `hId A`: structural recursion on `A`.  `hId unit = hEmpty`,
-- `hId (Var x) = hVar x`, `hId (A ⊗₀ B) = hTensor (hId A) (hId B)`.
-- The first two are constructive base cases; the tensor case
-- delegates to the (still-postulated) `decode-attempt-hTensor`.

decode-attempt-hId
  : ∀ (A : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten A)) ]
      decode-attempt (hId A) ≡ just t
decode-attempt-hId unit       = decode-attempt-hEmpty
decode-attempt-hId (Var x)    = decode-attempt-hVar x
decode-attempt-hId (A ⊗₀ B)   =
  decode-attempt-hTensor (hId A) (hId B)
    (decode-attempt-hId A) (decode-attempt-hId B)

--------------------------------------------------------------------------------
-- Constructive proof of `decode-attempt-Linear` for translated
-- hypergraphs, by induction on the term `f`.  This is the function
-- `Decoder.agda` uses to define the total `decode`.
--
-- Each branch unfolds `⟪_⟫` and applies the corresponding per-case
-- lemma above.  The unitor / associator branches (`λ⇒`, `λ⇐`, `ρ⇒`,
-- `ρ⇐`, `α⇒`, `α⇐`) translate via `subst₂` on `hId`, so they go
-- through `decode-attempt-subst₂`.

decode-attempt-Linear
  : ∀ {A B} (f : HomTerm A B)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten B)) ]
      decode-attempt ⟪ f ⟫ ≡ just t
decode-attempt-Linear (Agen g)  = decode-attempt-hGen g
decode-attempt-Linear (id {A})  = decode-attempt-hId A
decode-attempt-Linear (g ∘ f)   =
  decode-attempt-hCompose ⟪ f ⟫ ⟪ g ⟫
    (Lin.⟪⟫-Linear f) (Lin.⟪⟫-Linear g)
    (decode-attempt-Linear f) (decode-attempt-Linear g)
decode-attempt-Linear (f ⊗₁ g)  =
  decode-attempt-hTensor ⟪ f ⟫ ⟪ g ⟫
    (decode-attempt-Linear f) (decode-attempt-Linear g)
decode-attempt-Linear (λ⇒ {A})  = decode-attempt-hId A
decode-attempt-Linear (λ⇐ {A})  = decode-attempt-hId A
decode-attempt-Linear (ρ⇒ {A})  =
  decode-attempt-subst₂ (hId (A ⊗₀ unit)) refl (++-identityʳ (flatten A))
    (decode-attempt-hId (A ⊗₀ unit))
decode-attempt-Linear (ρ⇐ {A})  =
  decode-attempt-subst₂ (hId (A ⊗₀ unit)) (++-identityʳ (flatten A)) refl
    (decode-attempt-hId (A ⊗₀ unit))
decode-attempt-Linear (α⇒ {A} {B} {C}) =
  decode-attempt-subst₂ (hId ((A ⊗₀ B) ⊗₀ C))
    refl (++-assoc (flatten A) (flatten B) (flatten C))
    (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C))
decode-attempt-Linear (α⇐ {A} {B} {C}) =
  decode-attempt-subst₂ (hId ((A ⊗₀ B) ⊗₀ C))
    (++-assoc (flatten A) (flatten B) (flatten C)) refl
    (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C))
decode-attempt-Linear (σ {A} {B}) = decode-attempt-hSwap A B

--------------------------------------------------------------------------------
-- The total `decode` and the `bridge` it commutes with, derived from
-- `decode-attempt-Linear`.

decode
  : ∀ {A B} (f : HomTerm A B)
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decode f = proj₁ (decode-attempt-Linear f)

-- `bridge`: `f` composed with the unflatten-flatten coherence isos
-- on each side.  When `flatten`/`unflatten` were definitional inverses
-- this would just be `f`; under propositional/iso-only inversion we
-- need the explicit bridge.
bridge
  : ∀ {A B}
  → HomTerm A B
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f =
  _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)

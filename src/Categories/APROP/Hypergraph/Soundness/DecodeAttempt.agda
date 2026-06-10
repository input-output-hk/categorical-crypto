{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Per-smart-constructor `decode-attempt` success lemmas (hEmpty/hVar/
-- hId/hGen/hSwap/hTensor) plus the generic edge-step/process-edges
-- lifting machinery, shared by the pruned totality
-- (`DecodeAttemptLinearP.decode-attempt-LinearP`, which derives the
-- total pruned decoder `decodeP`).  `bridge` lives here too.
--
-- The unpruned `decode-attempt-hCompose`/`decode-attempt-Linear`/`decode`
-- were retired together with the unpruned `hCompose` (see
-- docs/size-reduction-strategies.md, 2026-06-10 addendum).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.DecodeAttempt (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range;
         hEmpty; hVar; hId; hGen; hSwap; hTensor;
         module hTensor-impl)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (decode-attempt; edge-step; extract-prefix; process-edges;
         process-all-edges; extract-exact)
open import Categories.APROP.Hypergraph.Soundness.DecodeProperties sig
  using (extract-prefix-self; extract-prefix-from-↭;
         extract-prefix-↑ˡ-on-mixed-just; extract-prefix-↑ʳ-on-mixed-just;
         extract-prefix-↑ˡ-on-mixed-nothing; extract-prefix-↑ʳ-on-mixed-nothing;
         extract-prefix-↭-residual; extract-prefix-↭-nothing;
         extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj)
import Categories.APROP.Hypergraph.Soundness.Linearity sig as Lin

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
-- Per-case lemmas, one per smart constructor of `FromAPROP`.  The
-- `hEmpty`/`hVar` base cases reduce by `refl`.

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
-- Extraction: from `decode-attempt H ≡ just _` recover the final stack of
-- `process-all-edges` together with a permutation to `H.cod`.

decode-attempt-perm-from-just
  : (H : Hypergraph FlatGen)
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
-- `process-edges (xs ++ ys) s` factors at the stack level as
-- `process-edges ys` applied to the result of `process-edges xs`.

process-edges-++-stack
  : (H : Hypergraph FlatGen)
      (xs ys : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → proj₁ (process-edges H (xs ++ ys) s)
    ≡ proj₁ (process-edges H ys (proj₁ (process-edges H xs s)))
process-edges-++-stack H []       ys s = refl
process-edges-++-stack H (e ∷ xs) ys s
    with edge-step H s e
... | s' , _ = process-edges-++-stack H xs ys s'

--------------------------------------------------------------------------------
-- Edge-step lifting for `hTensor`: a G-side (resp. K-side) edge's result
-- on the mixed stack factors through the underlying single-side search.

module _ (G K : Hypergraph FlatGen) where
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

      -- Transport the mixed-just output to the ein-c form `edge-step` sees;
      -- wrapping the existential in the `subst` predicate carries both the
      -- residual permutation and the equation at once.
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

      -- Bridge edge-step's raw output to the lifted form (eout-c-inj₁-red,
      -- ++-assoc, map-++).
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

  -- K-side: edge-step prepends `map injR (K.eout eK)` to the L-side and
  -- the K-residual.  This output is NOT of the form `(map injL ?) ++
  -- (map injR ?)` (the K-eouts sit left of the L-block), so we expose the
  -- literal stack shape and defer permutation reasoning to the
  -- `process-edges`-level lemmas.
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

      -- One `cong` rewriting `eout-c (G.nE ↑ʳ eK)` to `map injR (K.eout eK)`;
      -- no associator needed since the eouts stay on the left.
      list-eq : Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK)
                  ++ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K)
              ≡ map (G.nV ↑ʳ_) (K.eout eK)
                  ++ map (_↑ˡ K.nV) xs
                  ++ map (G.nV ↑ʳ_) rest-K
      list-eq = cong (_++ (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) rest-K))
                     (hT-impl.eout-c-inj₂-red eK)

  -- Failure-direction G-side lifting: if G's edge cannot fire, neither
  -- can the lifted edge-step (stack unchanged, term is identity).
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

  -- K-side failure: same shape as G-side.
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

  -- Unified G-side per-edge lemma (just/nothing).  Since G's edges only
  -- touch the L-side, the output stays in `(map injL _) ++ (map injR ys)`.
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

  -- Iterate `edge-step-↑ˡ-on-mixed` over a list of G-edges.
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
  -- K-side per-edge lifting on a permutation-equivalent input.  K-edges'
  -- eouts get prepended, breaking the `(map injL ?) ++ (map injR ?)`
  -- form, so we track only a permutation invariant: the output permutes
  -- to `L ++ map injR (proj₁ (edge-step K ys eK))`.
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

      -- Expose K's ein at the front, for `extract-prefix-↭-residual`.
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

      -- Pull out the residual `r` and its permutation.
      extract-step
        : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p)
                       × (L ++ R-rst) Perm.↭ r
      extract-step =
        extract-prefix-↭-residual R-pre s (L ++ R-rst) s↭shuffled

      r  = proj₁ extract-step
      r↭ : (L ++ R-rst) Perm.↭ r
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      -- Bridge `ein-c-inj₂-red` to the algorithm's actual lookup.
      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) s
                 ≡ just (r , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
              (sym (hT-impl.ein-c-inj₂-red eK))
              (proj₁ (proj₂ extract-step) ,
               proj₁ (proj₂ (proj₂ extract-step)))

      reduce-result
        : ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK)
                   ≡ (Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ r , t)
      reduce-result rewrite proj₂ extract-on-ein-c = _ , refl

      -- `eout-c-inj₂-red` converts eout-c to `R-out`.
      edge-step-eq
        : ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ (R-out ++ r , t)
      edge-step-eq =
        subst (λ ks → ∃[ t ] edge-step (hTensor G K) s (G.nE ↑ʳ eK)
                              ≡ (ks ++ r , t))
              (hT-impl.eout-c-inj₂-red eK)
              reduce-result

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

  -- Iterate `edge-step-↑ʳ-on-perm` over a list of K-edges.
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
-- `hSwap A B`: nE = 0, dom = L ++ R, cod = R ++ L.  `process-all-edges`
-- returns (dom, id); `extract-exact` succeeds via `++-comm` +
-- `extract-prefix-from-↭`.

decode-attempt-hSwap
  : ∀ (A B : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (domL (hSwap A B))) (unflatten (codL (hSwap A B))) ]
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
-- `hGen g`: nE = 1, ein 0 = dom = L, eout 0 = cod = R.  The single edge
-- fires via `extract-prefix-self` (stack becomes `R ++ []`); the final
-- `extract-exact` needs `(R ++ []) ↭ R` via `++-identityʳ`.

decode-attempt-hGen
  : ∀ {A B : ObjTerm} (g : mor A B)
  → Σ[ t ∈ HomTerm (unflatten (domL (hGen g))) (unflatten (codL (hGen g))) ]
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

--------------------------------------------------------------------------------
-- Inverse of `decode-attempt-perm-from-just`: from a final stack with a
-- permutation to `H.cod`, derive `decode-attempt H ≡ just _`.

decode-attempt-from-perm
  : (H : Hypergraph FlatGen)
  → ∃[ s_final ] ∃[ t' ]
       (process-all-edges H (Hypergraph.dom H) ≡ (s_final , t'))
     × (s_final Perm.↭ Hypergraph.cod H)
  → Σ[ t ∈ HomTerm (unflatten (domL H)) (unflatten (codL H)) ]
      decode-attempt H ≡ just t
decode-attempt-from-perm H (s_final , t' , eq-proc , perm)
    with extract-prefix-from-↭ s_final (Hypergraph.cod H) perm
... | _ , eq-prefix
    rewrite eq-proc | eq-prefix = _ , refl

--------------------------------------------------------------------------------
-- `decode-attempt-hTensor`: combines the per-edge / process-edges
-- liftings.  Run the G-edges block (`process-edges-↑ˡ-on-mixed`) then the
-- K-edges block (`process-edges-↑ʳ-on-perm`), then combine the two side
-- permutations and feed `decode-attempt-from-perm`.

decode-attempt-hTensor
  : (G K : Hypergraph FlatGen)
  → (∃[ tG ] decode-attempt G ≡ just tG)
  → (∃[ tK ] decode-attempt K ≡ just tK)
  → Σ[ t ∈ HomTerm (unflatten (domL (hTensor G K))) (unflatten (codL (hTensor G K))) ]
      decode-attempt (hTensor G K) ≡ just t
decode-attempt-hTensor G K ih-G ih-K =
    decode-attempt-from-perm (hTensor G K)
      (proj₁ proc , proj₂ proc , refl , perm-final)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open Perm.PermutationReasoning

    ih-G' = decode-attempt-perm-from-just G ih-G
    s_G_final = proj₁ ih-G'
    eq-G = proj₁ (proj₂ (proj₂ ih-G'))
    perm-G = proj₂ (proj₂ (proj₂ ih-G'))

    ih-K' = decode-attempt-perm-from-just K ih-K
    s_K_final = proj₁ ih-K'
    eq-K = proj₁ (proj₂ (proj₂ ih-K'))
    perm-K = proj₂ (proj₂ (proj₂ ih-K'))

    proc = process-all-edges (hTensor G K) (Hypergraph.dom (hTensor G K))

    -- After the G-edges block.
    after-G-stack = proj₁ (process-edges (hTensor G K)
                            (map (_↑ˡ K.nE) (range G.nE))
                            (Hypergraph.dom (hTensor G K)))

    G-lift = process-edges-↑ˡ-on-mixed G K (range G.nE) G.dom K.dom

    after-G-≡ : after-G-stack
              ≡ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) K.dom
    after-G-≡ = trans (cong proj₁ (proj₂ G-lift))
                       (cong (λ x → map (_↑ˡ K.nV) x ++ map (G.nV ↑ʳ_) K.dom)
                             (cong proj₁ eq-G))

    after-G-↭-std : after-G-stack
                  Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) K.dom
    after-G-↭-std = Perm.↭-reflexive after-G-≡

    K-lift = process-edges-↑ʳ-on-perm G K (range K.nE) after-G-stack
              s_G_final K.dom after-G-↭-std

    s_K' = proj₁ K-lift
    K-lift-eq   = proj₁ (proj₂ (proj₂ K-lift))
    K-lift-perm = proj₂ (proj₂ (proj₂ K-lift))

    -- `proj₁ proc ≡ s_K'` via `range-++` + `process-edges-++-stack` +
    -- the K-lift's equation.
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

    K-final-perm
      : s_K' Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) s_K_final
    K-final-perm =
      subst (λ x → s_K' Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) x)
            (cong proj₁ eq-K)
            K-lift-perm

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
-- `hId A`: structural recursion on `A`.

decode-attempt-hId
  : ∀ (A : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (domL (hId A))) (unflatten (codL (hId A))) ]
      decode-attempt (hId A) ≡ just t
decode-attempt-hId unit       = decode-attempt-hEmpty
decode-attempt-hId (Var x)    = decode-attempt-hVar x
decode-attempt-hId (A ⊗₀ B)   =
  decode-attempt-hTensor (hId A) (hId B)
    (decode-attempt-hId A) (decode-attempt-hId B)

-- `bridge`: `f` composed with the unflatten-flatten coherence isos on
-- each side (needed because `flatten`/`unflatten` are inverse only up to iso).
bridge
  : ∀ {A B}
  → HomTerm A B
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f =
  _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)

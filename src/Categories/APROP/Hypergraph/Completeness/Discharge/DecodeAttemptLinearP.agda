{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Totality of the decoder on the PRUNED translation `⟪_⟫ₚ`.
--
-- This mirrors `DecodeAttempt.decode-attempt-Linear` but for the pruned
-- translation `Categories.APROP.Hypergraph.Translation.⟪_⟫` (here aliased
-- `⟪_⟫ₚ`), whose `∘` case uses `hComposeP` instead of `hCompose`.
--
-- Three pieces:
--   (#6) `decode-attempt-hComposeP` — the load-bearing port of
--        `DecodeAttempt.decode-attempt-hCompose` with `hCompose`→`hComposeP`,
--        `remap`→`remapP`, `_↑ˡ K.nV`→`injL = _↑ˡ cn` (cn = count-non K.dom).
--   (#7) `⟪⟫-LinearP`  — clone of `Linearity.⟪⟫-Linear`; only `∘` differs
--        (uses `Linear-hComposeP` from the spike `LinearHComposeP`).
--   (#8) `decode-attempt-LinearP` — clone of `decode-attempt-Linear`; only
--        `∘` differs (uses `decode-attempt-hComposeP`).
--
-- The pruned/unpruned translations agree byte-for-byte on all 11 HomTerm
-- constructors EXCEPT `∘`; pruning removes only vertices, never edges
-- (same `nE`, same Fin order). Hence every atomic decode/linearity lemma is
-- reused verbatim from `DecodeAttempt` / `Linearity`; only the `∘` machinery
-- is re-proven, with the proof skeleton identical modulo the two renamings.
--
-- No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range;
         hEmpty; hVar; hId; hGen; hSwap; hTensor)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl;
         domL-hComposeP; codL-hComposeP)
open import Categories.APROP.Hypergraph.Prune
  using (count-non)
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt; edge-step; extract-prefix; process-edges;
         process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing;
         extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
open import Categories.APROP.Hypergraph.Completeness.Discharge.LinearHComposeP sig
  using (Linear-hComposeP)
import Categories.APROP.Hypergraph.Completeness.Discharge.LinearHComposeP sig as LP

-- Reused-as-is generic decode lemmas (mention only an arbitrary `H`).
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-perm-from-just; decode-attempt-from-perm;
         process-edges-++-stack;
         decode-attempt-hGen; decode-attempt-hId; decode-attempt-hSwap;
         decode-attempt-hTensor)

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

--------------------------------------------------------------------------------
-- (#6) Per-edge / process-edges liftings for `hComposeP`.
--
-- Parallel to `DecodeAttempt`'s hCompose lifts, but:
--   * the G-side raise `_↑ˡ K.nV` becomes `injL = _↑ˡ cn`
--     (cn = count-non K.dom), from `hComposeP-impl`;
--   * the K-side `remap` becomes `remapP`, whose injectivity comes from
--     the spike `LinearHComposeP.remapP-injective` (needs Linear G + K).

module _
  (G K : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ domL K)
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  open hComposeP-impl G K bdy-eq
    using (remapP; injL; ein-c-inj₁-red; eout-c-inj₁-red;
           ein-c-inj₂-red; eout-c-inj₂-red)

  -- From the spike: injectivity of remapP (needs the linearity invariants).
  -- The spike's `remapP-injective` lives in an anonymous `module _ (G K
  -- bdy-eq lin-G lin-K)`, so its contents are lifted to top-level functions
  -- with those parameters prepended.
  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = LP.remapP-injective G K bdy-eq lin-G lin-K

  cn : ℕ
  cn = count-non K.dom

  --------------------------------------------------------------------
  -- G-side: per-edge lifting on a pure-L stack `map injL xs`.

  edge-step-↑ˡ-pure-L-just
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
        (rest : List (Fin G.nV)) (p : xs Perm.↭ G.ein eG ++ rest)
    → extract-prefix (G.ein eG) xs ≡ just (rest , p)
    → ∃[ t ]
         edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
         ≡ (map injL (G.eout eG ++ rest) , t)
  edge-step-↑ˡ-pure-L-just eG xs rest p eq =
      subst (λ s → ∃[ t ] edge-step (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE)
                            ≡ (s , t))
            list-eq
            reduce-result
    where
      open ≡-Reasoning
      stack = map injL xs

      eq-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)) stack
                 ≡ just (map injL rest , q)
      eq-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just (map injL rest , q))
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-just injL (inject+-inj cn)
                                                  (G.ein eG) xs rest p eq)

      reduce-result
        : ∃[ t ] edge-step (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE)
                  ≡ (Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
                       ++ map injL rest , t)
      reduce-result rewrite proj₂ eq-on-ein-c = _ , refl

      list-eq : Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
                  ++ map injL rest
              ≡ map injL (G.eout eG ++ rest)
      list-eq = begin
        Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
          ++ map injL rest
          ≡⟨ cong (_++ map injL rest) (eout-c-inj₁-red eG) ⟩
        map injL (G.eout eG) ++ map injL rest
          ≡⟨ sym (map-++ injL (G.eout eG) rest) ⟩
        map injL (G.eout eG ++ rest)
          ∎

  edge-step-↑ˡ-pure-L-nothing
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → extract-prefix (G.ein eG) xs ≡ nothing
    → ∃[ t ]
         edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
         ≡ (map injL xs , t)
  edge-step-↑ˡ-pure-L-nothing eG xs eq = aux nothing-lifted
    where
      stack = map injL xs

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hComposeP G K bdy-eq) (eG ↑ˡ K.nE))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-nothing injL
                                                     (inject+-inj cn)
                                                     (G.ein eG) xs eq)

      aux : extract-prefix (Hypergraph.ein (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)) stack
              ≡ nothing
          → ∃[ t ] edge-step (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE) ≡ (stack , t)
      aux p rewrite p = _ , refl

  edge-step-↑ˡ-pure-L
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → ∃[ t ]
         edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
         ≡ (map injL (proj₁ (edge-step G xs eG)) , t)
  edge-step-↑ˡ-pure-L eG xs
      with extract-prefix (G.ein eG) xs in eq
  ... | just (rest , p) = edge-step-↑ˡ-pure-L-just eG xs rest p eq
  ... | nothing         = edge-step-↑ˡ-pure-L-nothing eG xs eq

  process-edges-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → ∃[ t ]
         process-edges (hComposeP G K bdy-eq) (map (_↑ˡ K.nE) es) (map injL xs)
         ≡ (map injL (proj₁ (process-edges G es xs)) , t)
  process-edges-↑ˡ-pure-L []       xs = _ , refl
  process-edges-↑ˡ-pure-L (e ∷ es) xs
      with edge-step-↑ˡ-pure-L e xs
  ... | _ , eq-edge
      with process-edges-↑ˡ-pure-L es (proj₁ (edge-step G xs e))
  ... | _ , eq-prefix
      rewrite eq-edge | eq-prefix = _ , refl

  --------------------------------------------------------------------
  -- K-side: perm-respecting per-edge lifting via remapP.  Stack
  -- assumed `↭ map remapP ys`; output stack `↭ map remapP (proj₁
  -- (edge-step K ys eK))`.

  edge-step-↑ʳ-via-remapP
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + cn)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remapP ys
    → ∃[ s' ] ∃[ t ]
         (edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ (s' , t))
       × (s' Perm.↭ map remapP (proj₁ (edge-step K ys eK)))
  edge-step-↑ʳ-via-remapP eK s ys s↭std
      with extract-prefix (K.ein eK) ys in eq-K
  ... | just (rest , p-K) =
        map remapP (K.eout eK) ++ r
      , proj₁ edge-step-eq
      , proj₂ edge-step-eq
      , final-perm
    where
      open Perm.PermutationReasoning
      R-pre = map remapP (K.ein eK)
      R-out = map remapP (K.eout eK)
      R-rst = map remapP rest

      s↭shuffled : s Perm.↭ R-pre ++ R-rst
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        map remapP ys
          ↭⟨ PermProp.map⁺ remapP p-K ⟩
        map remapP (K.ein eK ++ rest)
          ≡⟨ map-++ remapP (K.ein eK) rest ⟩
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
                   (Hypergraph.ein (hComposeP G K bdy-eq) (G.nE ↑ʳ eK)) s
                 ≡ just (r , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
              (sym (ein-c-inj₂-red eK))
              (proj₁ (proj₂ extract-step) ,
               proj₁ (proj₂ (proj₂ extract-step)))

      reduce-result
        : ∃[ t ] edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
                  ≡ (Hypergraph.eout (hComposeP G K bdy-eq) (G.nE ↑ʳ eK) ++ r , t)
      reduce-result rewrite proj₂ extract-on-ein-c = _ , refl

      edge-step-eq
        : ∃[ t ] edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ (R-out ++ r , t)
      edge-step-eq =
        subst (λ ks → ∃[ t ] edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
                              ≡ (ks ++ r , t))
              (eout-c-inj₂-red eK)
              reduce-result

      final-perm : R-out ++ r Perm.↭ map remapP (K.eout eK ++ rest)
      final-perm = begin
        R-out ++ r
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ R-rst
          ≡⟨ sym (map-++ remapP (K.eout eK) rest) ⟩
        map remapP (K.eout eK ++ rest)
          ∎

  ... | nothing = nothing-result
    where
      nothing-on-std
        : extract-prefix (map remapP (K.ein eK)) (map remapP ys) ≡ nothing
      nothing-on-std =
        extract-prefix-via-injective-nothing remapP remapP-injective
                                              (K.ein eK) ys eq-K

      nothing-on-s
        : extract-prefix (map remapP (K.ein eK)) s ≡ nothing
      nothing-on-s =
        extract-prefix-↭-nothing
          (map remapP (K.ein eK)) (map remapP ys) s
          (Perm.↭-sym s↭std) nothing-on-std

      nothing-on-ein-c
        : extract-prefix
            (Hypergraph.ein (hComposeP G K bdy-eq) (G.nE ↑ʳ eK)) s ≡ nothing
      nothing-on-ein-c =
        subst (λ ks → extract-prefix ks s ≡ nothing)
              (sym (ein-c-inj₂-red eK))
              nothing-on-s

      reduce-to-id
        : ∃[ t ] edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ (s , t)
      reduce-to-id rewrite nothing-on-ein-c = _ , refl

      nothing-result
        : ∃[ s' ] ∃[ t ]
             (edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ (s' , t))
           × (s' Perm.↭ map remapP ys)
      nothing-result = s , proj₁ reduce-to-id , proj₂ reduce-to-id , s↭std

  process-edges-↑ʳ-via-remapP
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + cn)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remapP ys
    → ∃[ s' ] ∃[ t ]
         (process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) es) s ≡ (s' , t))
       × (s' Perm.↭ map remapP (proj₁ (process-edges K es ys)))
  process-edges-↑ʳ-via-remapP []       s ys s↭std =
    s , _ , refl , s↭std
  process-edges-↑ʳ-via-remapP (e ∷ es) s ys s↭std
      with edge-step-↑ʳ-via-remapP e s ys s↭std
  ... | _ , _ , eq-edge , perm-edge
      with process-edges-↑ʳ-via-remapP es _ (proj₁ (edge-step K ys e)) perm-edge
  ... | _ , _ , eq-rec , perm-rec
      rewrite eq-edge | eq-rec = _ , _ , refl , perm-rec

--------------------------------------------------------------------------------
-- (#6) `decode-attempt-hComposeP` — mirrors `decode-attempt-hCompose`.

decode-attempt-hComposeP
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  → Lin.Linear G → Lin.Linear K
  → (∃[ tG ] decode-attempt G ≡ just tG)
  → (∃[ tK ] decode-attempt K ≡ just tK)
  → Σ[ t ∈ HomTerm (unflatten (domL (hComposeP G K bdy-eq)))
                    (unflatten (codL (hComposeP G K bdy-eq))) ]
      decode-attempt (hComposeP G K bdy-eq) ≡ just t
decode-attempt-hComposeP G K bdy-eq lin-G lin-K ih-G ih-K =
    decode-attempt-from-perm (hComposeP G K bdy-eq)
      (proj₁ proc , proj₂ proc , refl , perm-final)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy-eq using (remapP; injL)
    map-remapP-K-dom = LP.map-remapP-K-dom G K bdy-eq lin-G lin-K
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

    proc = process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))

    -- Stack after G-edges: equals `map injL s_G_final`.
    after-G-stack = proj₁ (process-edges (hComposeP G K bdy-eq)
                            (map (_↑ˡ K.nE) (range G.nE))
                            (Hypergraph.dom (hComposeP G K bdy-eq)))

    G-lift = process-edges-↑ˡ-pure-L G K bdy-eq lin-G lin-K (range G.nE) G.dom

    after-G-≡ : after-G-stack ≡ map injL s_G_final
    after-G-≡ = trans (cong proj₁ (proj₂ G-lift))
                       (cong (map injL) (cong proj₁ eq-G))

    -- Bridge: after-G-stack ↭ map remapP K.dom.
    after-G-↭-remap-Kdom
      : after-G-stack Perm.↭ map remapP K.dom
    after-G-↭-remap-Kdom = begin
      after-G-stack
        ≡⟨ after-G-≡ ⟩
      map injL s_G_final
        ↭⟨ PermProp.map⁺ injL perm-G ⟩
      map injL G.cod
        ≡⟨ sym map-remapP-K-dom ⟩
      map remapP K.dom
        ∎

    -- K-side perm-respecting lift.
    K-lift = process-edges-↑ʳ-via-remapP G K bdy-eq lin-G lin-K
              (range K.nE) after-G-stack K.dom after-G-↭-remap-Kdom

    s_K' = proj₁ K-lift
    K-lift-eq   = proj₁ (proj₂ (proj₂ K-lift))
    K-lift-perm = proj₂ (proj₂ (proj₂ K-lift))

    proc-≡-s_K' : proj₁ proc ≡ s_K'
    proc-≡-s_K' =
      trans (cong (λ es → proj₁ (process-edges (hComposeP G K bdy-eq) es
                                  (Hypergraph.dom (hComposeP G K bdy-eq))))
                  (Inv.range-++ G.nE K.nE))
            (trans (process-edges-++-stack (hComposeP G K bdy-eq)
                     (map (_↑ˡ K.nE) (range G.nE))
                     (map (G.nE ↑ʳ_) (range K.nE))
                     (Hypergraph.dom (hComposeP G K bdy-eq)))
                   (cong proj₁ K-lift-eq))

    K-final-perm
      : s_K' Perm.↭ map remapP s_K_final
    K-final-perm =
      subst (λ x → s_K' Perm.↭ map remapP x)
            (cong proj₁ eq-K)
            K-lift-perm

    perm-final : proj₁ proc Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
    perm-final = begin
      proj₁ proc
        ≡⟨ proc-≡-s_K' ⟩
      s_K'
        ↭⟨ K-final-perm ⟩
      map remapP s_K_final
        ↭⟨ PermProp.map⁺ remapP perm-K ⟩
      map remapP K.cod
        ∎

--------------------------------------------------------------------------------
-- (#7) `⟪⟫-LinearP` — clone of `Linearity.⟪⟫-Linear`; only `∘` differs.

⟪⟫-LinearP : ∀ {A B} (f : HomTerm A B) → Lin.Linear ⟪ f ⟫ₚ
⟪⟫-LinearP (Agen g)        = Lin.Linear-hGen g
⟪⟫-LinearP (id {A})        = Lin.Linear-hId A
⟪⟫-LinearP (g ∘ f)         =
  Linear-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (f ⊗₁ g)        =
  Lin.Linear-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (λ⇒ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (λ⇐ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (ρ⇒ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (ρ⇐ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (α⇒ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (α⇐ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (σ {A}{B})      = Lin.Linear-hSwap A B

--------------------------------------------------------------------------------
-- (#8) `decode-attempt-LinearP` — clone of `decode-attempt-Linear`.

decode-attempt-LinearP
  : ∀ {A B} (f : HomTerm A B)
  → Σ[ t ∈ HomTerm (unflatten (domL ⟪ f ⟫ₚ)) (unflatten (codL ⟪ f ⟫ₚ)) ]
      decode-attempt ⟪ f ⟫ₚ ≡ just t
decode-attempt-LinearP (Agen g)        = decode-attempt-hGen g
decode-attempt-LinearP (id {A})        = decode-attempt-hId A
decode-attempt-LinearP (g ∘ f)         =
  decode-attempt-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (f ⊗₁ g)        =
  decode-attempt-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (λ⇒ {A})        = decode-attempt-hId A
decode-attempt-LinearP (λ⇐ {A})        = decode-attempt-hId A
decode-attempt-LinearP (ρ⇒ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (ρ⇐ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (α⇒ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (α⇐ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (σ {A}{B})      = decode-attempt-hSwap A B

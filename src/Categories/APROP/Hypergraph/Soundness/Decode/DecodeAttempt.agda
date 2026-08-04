{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Per-smart-constructor decode totality witnesses (hEmpty/hVar/hId/hGen/
-- hSwap/hTensor), each the bare permutation `process-all-edges H dom ↭ cod`,
-- plus the generic edge-step/process-edges lifting machinery, shared by the
-- pruned totality (`DecodeAttemptLinearP.decode-attempt-LinearP`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig

import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv

open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_)
open import Data.Nat
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality


--------------------------------------------------------------------------------
-- Per-case lemmas, one per smart constructor of `FromAPROP`.  Each produces
-- the *bare* totality witness — the permutation of `process-all-edges`'s
-- final stack onto `H.cod` (what `decode-attempt`'s `just` payload always
-- was; the `Maybe`/`≡ just` wrapping was pre-demotion residue).  The
-- `hEmpty`/`hVar` base cases have `nE = 0` and `dom = cod`, so
-- `process-all-edges` reduces to `dom` and the witness is reflexivity.

decode-attempt-hEmpty
  : process-all-edges hEmpty (Hypergraph.dom hEmpty) Perm.↭ Hypergraph.cod hEmpty
decode-attempt-hEmpty = Perm.↭-refl

decode-attempt-hVar
  : ∀ (x : X)
  → process-all-edges (hVar x) (Hypergraph.dom (hVar x)) Perm.↭ Hypergraph.cod (hVar x)
decode-attempt-hVar x = Perm.↭-refl

--------------------------------------------------------------------------------
-- `process-edges (xs ++ ys) s` factors as `process-edges ys` applied to the
-- result of `process-edges xs`.

process-edges-++-stack
  : (H : Hypergraph FlatGen)
      (xs ys : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → process-edges H (xs ++ ys) s
    ≡ process-edges H ys (process-edges H xs s)
process-edges-++-stack H []       ys s = refl
process-edges-++-stack H (e ∷ xs) ys s = process-edges-++-stack H xs ys (edge-step H s e)

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
    → edge-step (hTensor G K)
                (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                (eG ↑ˡ K.nE)
      ≡ map (_↑ˡ K.nV) (G.eout eG ++ rest-G) ++ map (G.nV ↑ʳ_) ys
  edge-step-↑ˡ-on-mixed-just eG xs-G ys rest-G p-G eq =
      trans reduce-result list-eq
    where
      open ≡-Reasoning

      stack = map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys

      -- Transport the mixed-just output to the ein-c form `edge-step` sees.
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

      -- Generic abstract edge-step reduction (avoids normalising the
      -- concrete `edge-step (hTensor G K) …` at this site).
      reduce-result
        : edge-step (hTensor G K) stack (eG ↑ˡ K.nE)
          ≡ Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE)
              ++ (map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys)
      reduce-result = edge-step-just (hTensor G K) stack (eG ↑ˡ K.nE) (proj₂ eq-on-ein-c)

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

  -- Failure-direction G-side lifting: if G's edge cannot fire, neither
  -- can the lifted edge-step (stack unchanged, term is identity).
  edge-step-↑ˡ-on-mixed-nothing
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → extract-prefix (G.ein eG) xs-G ≡ nothing
    → edge-step (hTensor G K)
                (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                (eG ↑ˡ K.nE)
      ≡ map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys
  edge-step-↑ˡ-on-mixed-nothing eG xs-G ys eq =
      edge-step-nothing (hTensor G K) stack (eG ↑ˡ K.nE) nothing-lifted
    where
      stack = map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (hT-impl.ein-c-inj₁-red eG))
              (extract-prefix-↑ˡ-on-mixed-nothing K.nV (G.ein eG) xs-G ys eq)

  -- Unified G-side per-edge lemma (just/nothing).  Since G's edges only
  -- touch the L-side, the output stays in `(map injL _) ++ (map injR ys)`.
  edge-step-↑ˡ-on-mixed
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → edge-step (hTensor G K)
                (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
                (eG ↑ˡ K.nE)
      ≡ map (_↑ˡ K.nV) (edge-step G xs-G eG) ++ map (G.nV ↑ʳ_) ys
  edge-step-↑ˡ-on-mixed eG xs-G ys with extract-prefix (G.ein eG) xs-G in eq
  ... | just (rest , p) = edge-step-↑ˡ-on-mixed-just eG xs-G ys rest p eq
  ... | nothing         = edge-step-↑ˡ-on-mixed-nothing eG xs-G ys eq

  -- Iterate `edge-step-↑ˡ-on-mixed` over a list of G-edges.
  process-edges-↑ˡ-on-mixed
    : ∀ (es : List (Fin G.nE))
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → process-edges (hTensor G K)
                    (map (_↑ˡ K.nE) es)
                    (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
      ≡ map (_↑ˡ K.nV) (process-edges G es xs-G) ++ map (G.nV ↑ʳ_) ys
  process-edges-↑ˡ-on-mixed []       xs-G ys = refl
  process-edges-↑ˡ-on-mixed (e ∷ es) xs-G ys
    rewrite edge-step-↑ˡ-on-mixed e xs-G ys =
      process-edges-↑ˡ-on-mixed es (edge-step G xs-G e) ys

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
    → edge-step (hTensor G K) s (G.nE ↑ʳ eK)
        Perm.↭ map (_↑ˡ K.nV) xs
                 ++ map (G.nV ↑ʳ_) (edge-step K ys eK)
  edge-step-↑ʳ-on-perm eK s xs ys s↭std with extract-prefix (K.ein eK) ys in eq-K
  ... | just (rest , p-K) =
        Perm.↭-trans (Perm.↭-reflexive edge-step-eq) final-perm
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
      extract-step = extract-prefix-↭-residual R-pre s (L ++ R-rst) s↭shuffled

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
        : edge-step (hTensor G K) s (G.nE ↑ʳ eK)
          ≡ Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ r
      reduce-result = edge-step-just (hTensor G K) s (G.nE ↑ʳ eK) (proj₂ extract-on-ein-c)

      -- `eout-c-inj₂-red` converts eout-c to `R-out`.
      edge-step-eq : edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ R-out ++ r
      edge-step-eq =
        subst (λ ks → edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ ks ++ r)
              (hT-impl.eout-c-inj₂-red eK)
              reduce-result

      -- `edge-step K ys eK` reduces (via `eq-K`) to `K.eout eK ++ rest`.
      final-perm : R-out ++ r Perm.↭ L ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest)
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

  ... | nothing =
        Perm.↭-trans (Perm.↭-reflexive reduce-to-id) s↭std
    where
      L = map (_↑ˡ K.nV) xs
      R = map (G.nV ↑ʳ_) ys

      nothing-on-std : extract-prefix (map (G.nV ↑ʳ_) (K.ein eK)) (L ++ R) ≡ nothing
      nothing-on-std = extract-prefix-↑ʳ-on-mixed-nothing G.nV (K.ein eK) xs ys eq-K

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

      -- `edge-step K ys eK` reduces (via `eq-K`) to `ys`.
      reduce-to-id : edge-step (hTensor G K) s (G.nE ↑ʳ eK) ≡ s
      reduce-to-id = edge-step-nothing (hTensor G K) s (G.nE ↑ʳ eK) nothing-on-ein-c

  -- Iterate `edge-step-↑ʳ-on-perm` over a list of K-edges.
  process-edges-↑ʳ-on-perm
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → process-edges (hTensor G K) (map (G.nE ↑ʳ_) es) s
        Perm.↭ map (_↑ˡ K.nV) xs
                 ++ map (G.nV ↑ʳ_) (process-edges K es ys)
  process-edges-↑ʳ-on-perm []       s xs ys s↭std = s↭std
  process-edges-↑ʳ-on-perm (e ∷ es) s xs ys s↭std =
    process-edges-↑ʳ-on-perm es (edge-step (hTensor G K) s (G.nE ↑ʳ e))
      xs (edge-step K ys e)
      (edge-step-↑ʳ-on-perm e s xs ys s↭std)

--------------------------------------------------------------------------------
-- `hSwap A B`: nE = 0, dom = L ++ R, cod = R ++ L.  `process-all-edges`
-- returns `dom` (by `refl`); the boundary permutation `dom ↭ cod` is
-- `++-comm L R`.

decode-attempt-hSwap
  : ∀ (A B : ObjTerm)
  → process-all-edges (hSwap A B) (Hypergraph.dom (hSwap A B))
      Perm.↭ Hypergraph.cod (hSwap A B)
decode-attempt-hSwap A B =
    PermProp.++-comm
      (map (_↑ˡ length (flatten B)) (range (length (flatten A))))
      (map (length (flatten A) ↑ʳ_) (range (length (flatten B))))

--------------------------------------------------------------------------------
-- `hGen g`: nE = 1, ein 0 = dom = L, eout 0 = cod = R.  The single edge
-- fires via `extract-prefix-self` (stack becomes `R ++ []`); the final
-- `extract-exact` needs `(R ++ []) ↭ R` via `++-identityʳ`.

decode-attempt-hGen
  : ∀ {A B : ObjTerm} (g : mor A B)
  → process-all-edges (hGen g) (Hypergraph.dom (hGen g)) Perm.↭ Hypergraph.cod (hGen g)
decode-attempt-hGen {A} {B} g = perm
  where
    H = hGen g
    module H = Hypergraph H
    -- The single edge fires on the whole `dom = ein 0` with empty residual.
    self : Σ[ p ∈ (H.dom Perm.↭ H.dom ++ []) ]
             extract-prefix (H.ein zero) H.dom ≡ just ([] , p)
    self = extract-prefix-self H.dom
    -- process-all-edges (range 1) = process-edges (zero ∷ []) dom folds the
    -- single `edge-step`, which fires to `H.eout zero ++ [] = H.cod ++ []`.
    proc-≡ : process-all-edges H H.dom ≡ H.eout zero ++ []
    proc-≡ = edge-step-just H H.dom zero (proj₂ self)
    perm : process-all-edges H H.dom Perm.↭ H.cod
    perm = subst (Perm._↭ H.cod) (sym proc-≡) (PermProp.++-identityʳ H.cod)

--------------------------------------------------------------------------------
-- `decode-attempt-hTensor`: combines the per-edge / process-edges
-- liftings.  Run the G-edges block (`process-edges-↑ˡ-on-mixed`) then the
-- K-edges block (`process-edges-↑ʳ-on-perm`), then combine the two side
-- permutations and feed `decode-attempt-from-perm`.

decode-attempt-hTensor
  : (G K : Hypergraph FlatGen)
  → process-all-edges G (Hypergraph.dom G) Perm.↭ Hypergraph.cod G
  → process-all-edges K (Hypergraph.dom K) Perm.↭ Hypergraph.cod K
  → process-all-edges (hTensor G K) (Hypergraph.dom (hTensor G K))
      Perm.↭ Hypergraph.cod (hTensor G K)
decode-attempt-hTensor G K perm-G perm-K =
    perm-final
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open Perm.PermutationReasoning

    s_G_final = process-all-edges G G.dom
    s_K_final = process-all-edges K K.dom

    proc = process-all-edges (hTensor G K) (Hypergraph.dom (hTensor G K))

    -- After the G-edges block (still on the natural mixed stack).
    after-G-stack = process-edges (hTensor G K)
                      (map (_↑ˡ K.nE) (range G.nE))
                      (Hypergraph.dom (hTensor G K))

    after-G-≡ : after-G-stack ≡ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) K.dom
    after-G-≡ = process-edges-↑ˡ-on-mixed G K (range G.nE) G.dom K.dom

    K-lift : process-edges (hTensor G K) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
               Perm.↭ map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) s_K_final
    K-lift = process-edges-↑ʳ-on-perm G K (range K.nE) after-G-stack
              s_G_final K.dom (Perm.↭-reflexive after-G-≡)

    -- `proc ≡ process-edges (K-block) after-G-stack` via `range-++` +
    -- `process-edges-++-stack`.
    proc-≡ : proc
             ≡ process-edges (hTensor G K) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
    proc-≡ =
      trans (cong (λ es → process-edges (hTensor G K) es
                            (Hypergraph.dom (hTensor G K)))
                  (Inv.range-++ G.nE K.nE))
            (process-edges-++-stack (hTensor G K)
              (map (_↑ˡ K.nE) (range G.nE))
              (map (G.nE ↑ʳ_) (range K.nE))
              (Hypergraph.dom (hTensor G K)))

    perm-final : proc Perm.↭ Hypergraph.cod (hTensor G K)
    perm-final = begin
      proc
        ≡⟨ proc-≡ ⟩
      process-edges (hTensor G K) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
        ↭⟨ K-lift ⟩
      map (_↑ˡ K.nV) s_G_final ++ map (G.nV ↑ʳ_) s_K_final
        ↭⟨ PermProp.++⁺ (PermProp.map⁺ (_↑ˡ K.nV) perm-G)
                         (PermProp.map⁺ (G.nV ↑ʳ_) perm-K) ⟩
      map (_↑ˡ K.nV) G.cod ++ map (G.nV ↑ʳ_) K.cod
        ∎

--------------------------------------------------------------------------------
-- `hId A`: structural recursion on `A`.

decode-attempt-hId
  : ∀ (A : ObjTerm)
  → process-all-edges (hId A) (Hypergraph.dom (hId A)) Perm.↭ Hypergraph.cod (hId A)
decode-attempt-hId unit       = decode-attempt-hEmpty
decode-attempt-hId (Var x)    = decode-attempt-hVar x
decode-attempt-hId (A ⊗₀ B)   =
  decode-attempt-hTensor (hId A) (hId B)
    (decode-attempt-hId A) (decode-attempt-hId B)

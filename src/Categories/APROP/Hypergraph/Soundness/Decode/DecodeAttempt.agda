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

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig

import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv

open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_)
open import Data.Nat
open import Data.List.Properties
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)


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
-- The per-edge decode lifting, once.
--
-- Both binary composites lift a sub-hypergraph's run to the composite along an
-- edge embedding `κ` and a stack former `out`, and both do it in three steps:
-- transport the sub-search's outcome onto `C.ein (κ e)`, apply the generic
-- `edge-step-{just,nothing}` reduction, and rewrite `C.eout (κ e) ++ …` into
-- the lifted form.  The two shapes differ only in *what is invariant*: a
-- G-side edge leaves the stack in the `out` image (`StackLift`, an `_≡_`),
-- while a K-side edge prepends its eouts and only a permutation survives
-- (`PermLift`).  The search-lifting facts and the `out`-algebra are
-- parameters, so `hTensor`'s framed instances and `hComposeP`'s frame-free
-- ones are the same proof.
--------------------------------------------------------------------------------

module StackLift
  (C G : Hypergraph FlatGen)
  (κ : Fin (Hypergraph.nE G) → Fin (Hypergraph.nE C))
  (out : List (Fin (Hypergraph.nV G)) → List (Fin (Hypergraph.nV C)))
  (hit : ∀ (e : Fin (Hypergraph.nE G)) (xs rest : List (Fin (Hypergraph.nV G)))
           (p : xs Perm.↭ Hypergraph.ein G e ++ rest)
       → extract-prefix (Hypergraph.ein G e) xs ≡ just (rest , p)
       → ∃[ q ] extract-prefix (Hypergraph.ein C (κ e)) (out xs)
                ≡ just (out rest , q))
  (miss : ∀ (e : Fin (Hypergraph.nE G)) (xs : List (Fin (Hypergraph.nV G)))
        → extract-prefix (Hypergraph.ein G e) xs ≡ nothing
        → extract-prefix (Hypergraph.ein C (κ e)) (out xs) ≡ nothing)
  (fold : ∀ (e : Fin (Hypergraph.nE G)) (rest : List (Fin (Hypergraph.nV G)))
        → Hypergraph.eout C (κ e) ++ out rest ≡ out (Hypergraph.eout G e ++ rest))
  where

  private
    module G = Hypergraph G

  edge-step-lift
    : ∀ (e : Fin G.nE) (xs : List (Fin G.nV))
    → edge-step C (out xs) (κ e) ≡ out (edge-step G xs e)
  edge-step-lift e xs with extract-prefix (G.ein e) xs in eq
  ... | just (rest , p) =
        trans (edge-step-just C (out xs) (κ e) (proj₂ (hit e xs rest p eq)))
              (fold e rest)
  ... | nothing =
        edge-step-nothing C (out xs) (κ e) (miss e xs eq)

  process-edges-lift
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → process-edges C (map κ es) (out xs) ≡ out (process-edges G es xs)
  process-edges-lift []       xs = refl
  process-edges-lift (e ∷ es) xs
    rewrite edge-step-lift e xs = process-edges-lift es (edge-step G xs e)

module PermLift
  (C K : Hypergraph FlatGen)
  (κ : Fin (Hypergraph.nE K) → Fin (Hypergraph.nE C))
  (ι : Fin (Hypergraph.nV K) → Fin (Hypergraph.nV C))
  (out : List (Fin (Hypergraph.nV K)) → List (Fin (Hypergraph.nV C)))
  (ein-red : ∀ (e : Fin (Hypergraph.nE K))
           → Hypergraph.ein C (κ e) ≡ map ι (Hypergraph.ein K e))
  (eout-red : ∀ (e : Fin (Hypergraph.nE K))
            → Hypergraph.eout C (κ e) ≡ map ι (Hypergraph.eout K e))
  (front : ∀ (e : Fin (Hypergraph.nE K)) (ys rest : List (Fin (Hypergraph.nV K)))
         → ys Perm.↭ Hypergraph.ein K e ++ rest
         → out ys Perm.↭ map ι (Hypergraph.ein K e) ++ out rest)
  (fold : ∀ (e : Fin (Hypergraph.nE K)) (rest : List (Fin (Hypergraph.nV K)))
        → map ι (Hypergraph.eout K e) ++ out rest
          Perm.↭ out (Hypergraph.eout K e ++ rest))
  (miss : ∀ (e : Fin (Hypergraph.nE K)) (ys : List (Fin (Hypergraph.nV K)))
        → extract-prefix (Hypergraph.ein K e) ys ≡ nothing
        → extract-prefix (map ι (Hypergraph.ein K e)) (out ys) ≡ nothing)
  where

  private
    module K = Hypergraph K

  edge-step-lift
    : ∀ (e : Fin K.nE) (s : List (Fin (Hypergraph.nV C))) (ys : List (Fin K.nV))
    → s Perm.↭ out ys
    → edge-step C s (κ e) Perm.↭ out (edge-step K ys e)
  edge-step-lift e s ys s↭ with extract-prefix (K.ein e) ys in eq
  ... | just (rest , p) =
        Perm.↭-trans (Perm.↭-reflexive step-eq)
          (Perm.↭-trans (PermProp.++⁺ˡ (map ι (K.eout e)) (Perm.↭-sym r↭))
                        (fold e rest))
    where
      ex = extract-prefix-↭-residual (map ι (K.ein e)) s (out rest)
             (Perm.↭-trans s↭ (front e ys rest p))
      r = proj₁ ex
      r↭ : out rest Perm.↭ r
      r↭ = proj₂ (proj₂ (proj₂ ex))
      hit-c : ∃[ q ] extract-prefix (Hypergraph.ein C (κ e)) s ≡ just (r , q)
      hit-c = subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
                    (sym (ein-red e))
                    (proj₁ (proj₂ ex) , proj₁ (proj₂ (proj₂ ex)))
      step-eq : edge-step C s (κ e) ≡ map ι (K.eout e) ++ r
      step-eq = trans (edge-step-just C s (κ e) (proj₂ hit-c))
                      (cong (_++ r) (eout-red e))
  ... | nothing =
        Perm.↭-trans (Perm.↭-reflexive (edge-step-nothing C s (κ e) miss-c)) s↭
    where
      miss-c : extract-prefix (Hypergraph.ein C (κ e)) s ≡ nothing
      miss-c =
        subst (λ ks → extract-prefix ks s ≡ nothing) (sym (ein-red e))
              (extract-prefix-↭-nothing (map ι (K.ein e)) (out ys) s
                 (Perm.↭-sym s↭) (miss e ys eq))

  process-edges-lift
    : ∀ (es : List (Fin K.nE)) (s : List (Fin (Hypergraph.nV C)))
        (ys : List (Fin K.nV))
    → s Perm.↭ out ys
    → process-edges C (map κ es) s Perm.↭ out (process-edges K es ys)
  process-edges-lift []       s ys s↭ = s↭
  process-edges-lift (e ∷ es) s ys s↭ =
    process-edges-lift es (edge-step C s (κ e)) (edge-step K ys e)
      (edge-step-lift e s ys s↭)

--------------------------------------------------------------------------------
-- Edge-step lifting for `hTensor`: a G-side (resp. K-side) edge's result
-- on the mixed stack factors through the underlying single-side search.

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module hT-impl = hTensor-impl G K

  -- The G-side instance: the stack former frames `map injL _` on the right by
  -- the untouched K-block `map injR ys`.
  module GSide (ys : List (Fin K.nV)) where

    out : List (Fin G.nV) → List (Fin (G.nV + K.nV))
    out xs = map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys

    private
      hit : ∀ (e : Fin G.nE) (xs rest : List (Fin G.nV))
              (p : xs Perm.↭ G.ein e ++ rest)
          → extract-prefix (G.ein e) xs ≡ just (rest , p)
          → ∃[ q ] extract-prefix (Hypergraph.ein (hTensor G K) (e ↑ˡ K.nE)) (out xs)
                   ≡ just (out rest , q)
      hit e xs rest p eq =
        subst (λ ks → ∃[ q ] extract-prefix ks (out xs) ≡ just (out rest , q))
              (sym (hT-impl.ein-c-inj₁-red e))
              (extract-prefix-↑ˡ-on-mixed-just K.nV (G.ein e) xs ys rest p eq)

      miss : ∀ (e : Fin G.nE) (xs : List (Fin G.nV))
           → extract-prefix (G.ein e) xs ≡ nothing
           → extract-prefix (Hypergraph.ein (hTensor G K) (e ↑ˡ K.nE)) (out xs)
             ≡ nothing
      miss e xs eq =
        subst (λ ks → extract-prefix ks (out xs) ≡ nothing)
              (sym (hT-impl.ein-c-inj₁-red e))
              (extract-prefix-↑ˡ-on-mixed-nothing K.nV (G.ein e) xs ys eq)

      -- `eout-c-inj₁-red`, then re-associate the frame out of the way.
      fold : ∀ (e : Fin G.nE) (rest : List (Fin G.nV))
           → Hypergraph.eout (hTensor G K) (e ↑ˡ K.nE) ++ out rest
             ≡ out (G.eout e ++ rest)
      fold e rest = begin
        Hypergraph.eout (hTensor G K) (e ↑ˡ K.nE) ++ out rest
          ≡⟨ cong (_++ out rest) (hT-impl.eout-c-inj₁-red e) ⟩
        map (_↑ˡ K.nV) (G.eout e)
          ++ (map (_↑ˡ K.nV) rest ++ map (G.nV ↑ʳ_) ys)
          ≡⟨ sym (++-assoc (map (_↑ˡ K.nV) (G.eout e))
                            (map (_↑ˡ K.nV) rest) (map (G.nV ↑ʳ_) ys)) ⟩
        (map (_↑ˡ K.nV) (G.eout e) ++ map (_↑ˡ K.nV) rest)
          ++ map (G.nV ↑ʳ_) ys
          ≡⟨ cong (_++ map (G.nV ↑ʳ_) ys)
                  (sym (map-++ (_↑ˡ K.nV) (G.eout e) rest)) ⟩
        out (G.eout e ++ rest)
          ∎
        where open ≡-Reasoning

    open StackLift (hTensor G K) G (_↑ˡ K.nE) out hit miss fold public

  -- Iterate the G-side lifting over a list of G-edges.
  process-edges-↑ˡ-on-mixed
    : ∀ (es : List (Fin G.nE))
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → process-edges (hTensor G K)
                    (map (_↑ˡ K.nE) es)
                    (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
      ≡ map (_↑ˡ K.nV) (process-edges G es xs-G) ++ map (G.nV ↑ʳ_) ys
  process-edges-↑ˡ-on-mixed es xs-G ys = GSide.process-edges-lift ys es xs-G

  --------------------------------------------------------------------
  -- K-side per-edge lifting on a permutation-equivalent input: K-edges'
  -- eouts get prepended, breaking the `(map injL ?) ++ (map injR ?)`
  -- form, so only a permutation onto `L ++ map injR _` survives.  The
  -- L-block is what `front`/`fold` commute past.
  module KSide (xs : List (Fin G.nV)) where

    private
      L = map (_↑ˡ K.nV) xs

    out : List (Fin K.nV) → List (Fin (G.nV + K.nV))
    out ys = L ++ map (G.nV ↑ʳ_) ys

    private
      front : ∀ (e : Fin K.nE) (ys rest : List (Fin K.nV))
            → ys Perm.↭ K.ein e ++ rest
            → out ys Perm.↭ map (G.nV ↑ʳ_) (K.ein e) ++ out rest
      front e ys rest p = begin
        L ++ map (G.nV ↑ʳ_) ys
          ↭⟨ PermProp.++⁺ˡ L (PermProp.map⁺ (G.nV ↑ʳ_) p) ⟩
        L ++ map (G.nV ↑ʳ_) (K.ein e ++ rest)
          ≡⟨ cong (L ++_) (map-++ (G.nV ↑ʳ_) (K.ein e) rest) ⟩
        L ++ (Rp ++ Rr)
          ≡⟨ sym (++-assoc L Rp Rr) ⟩
        (L ++ Rp) ++ Rr
          ↭⟨ PermProp.++⁺ʳ Rr (PermProp.++-comm L Rp) ⟩
        (Rp ++ L) ++ Rr
          ≡⟨ ++-assoc Rp L Rr ⟩
        Rp ++ (L ++ Rr)
          ∎
        where
          open Perm.PermutationReasoning
          Rp = map (G.nV ↑ʳ_) (K.ein e)
          Rr = map (G.nV ↑ʳ_) rest

      fold : ∀ (e : Fin K.nE) (rest : List (Fin K.nV))
           → map (G.nV ↑ʳ_) (K.eout e) ++ out rest
             Perm.↭ out (K.eout e ++ rest)
      fold e rest = begin
        Ro ++ (L ++ Rr)
          ≡⟨ sym (++-assoc Ro L Rr) ⟩
        (Ro ++ L) ++ Rr
          ↭⟨ PermProp.++⁺ʳ Rr (PermProp.++-comm Ro L) ⟩
        (L ++ Ro) ++ Rr
          ≡⟨ ++-assoc L Ro Rr ⟩
        L ++ (Ro ++ Rr)
          ≡⟨ cong (L ++_) (sym (map-++ (G.nV ↑ʳ_) (K.eout e) rest)) ⟩
        L ++ map (G.nV ↑ʳ_) (K.eout e ++ rest)
          ∎
        where
          open Perm.PermutationReasoning
          Ro = map (G.nV ↑ʳ_) (K.eout e)
          Rr = map (G.nV ↑ʳ_) rest

      miss : ∀ (e : Fin K.nE) (ys : List (Fin K.nV))
           → extract-prefix (K.ein e) ys ≡ nothing
           → extract-prefix (map (G.nV ↑ʳ_) (K.ein e)) (out ys) ≡ nothing
      miss e ys eq = extract-prefix-↑ʳ-on-mixed-nothing G.nV (K.ein e) xs ys eq

    open PermLift (hTensor G K) K (G.nE ↑ʳ_) (G.nV ↑ʳ_) out
           hT-impl.ein-c-inj₂-red hT-impl.eout-c-inj₂-red front fold miss public

  -- Iterate the K-side lifting over a list of K-edges.
  process-edges-↑ʳ-on-perm
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → process-edges (hTensor G K) (map (G.nE ↑ʳ_) es) s
        Perm.↭ map (_↑ˡ K.nV) xs
                 ++ map (G.nV ↑ʳ_) (process-edges K es ys)
  process-edges-↑ʳ-on-perm es s xs ys = KSide.process-edges-lift xs es s ys

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
-- permutations with `PermProp.++⁺`/`map⁺` in the local `perm-final` chain.

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
    -- `process-edges-++`.
    proc-≡ : proc
             ≡ process-edges (hTensor G K) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
    proc-≡ =
      trans (cong (λ es → process-edges (hTensor G K) es
                            (Hypergraph.dom (hTensor G K)))
                  (Inv.range-++ G.nE K.nE))
            (process-edges-++ (hTensor G K)
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

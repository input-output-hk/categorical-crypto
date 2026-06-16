{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The FULL strict decoder `decodePˢ`: the algorithmic decoder run inside
-- the presented strict SMC `S` (`FreeStrictSMC.Build` at `FlatGen`).
--
--   decodePˢ f = castˢ (⟪⟫-domL f) (⟪⟫-codL f)
--                  (permuteˢ (finalPermˢ f) ∘ˢ proj₂ (runˢ ⟪ f ⟫))
--
-- where `runˢ H = process-edgesˢ (range H.nE) H.dom` is the strict run and
-- `finalPermˢ f` is the permutation produced by `extract-exact` on the
-- final stack.  Totality is NOT re-proved: the strict and non-strict
-- decoders branch on the SAME `extract-prefix` calls, so their stack
-- evolutions agree (`stacks-agree`), and the success witness of the live
-- decoder (`decode-attempt-LinearP`) transfers.  `extract-exact-total`
-- upgrades the transferred semantic permutation into the actual
-- `extract-exact ... ≡ just _` equation, so downstream shape lemmas can
-- compute the final permutation derivation by `just`-injectivity.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.DecodeS
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (extract-prefix; extract-exact; edge-step; process-edges;
         decode-attempt; ++-[]-↭)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (decode-attempt-perm-from-just)
open import Categories.APROP.Hypergraph.Soundness.DecodeProperties sig
  using (extract-prefix-↭-residual)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_ public

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- `extract-exact` totality from a semantic permutation: if ANY
-- permutation `xs ↭ ks` exists, `extract-exact ks xs` succeeds — and we
-- get hold of the equation, so the returned derivation is computable.

extract-exact-total
  : ∀ {n} (ks xs : List (Fin n)) → xs Perm.↭ ks
  → Σ[ p ∈ xs Perm.↭ ks ] extract-exact ks xs ≡ just p
extract-exact-total {n} ks xs perm =
  finish (proj₁ w) (proj₁ (proj₂ w)) (proj₁ (proj₂ (proj₂ w))) (sym r≡[])
  where
    w = extract-prefix-↭-residual ks xs []
          (Perm.↭-trans perm (Perm.↭-sym (++-[]-↭ ks)))

    r≡[] : proj₁ w ≡ []
    r≡[] = PermProp.↭-empty-inv (Perm.↭-sym (proj₂ (proj₂ (proj₂ w))))

    finish : ∀ r' (p : xs Perm.↭ ks ++ r')
           → extract-prefix ks xs ≡ just (r' , p) → [] ≡ r'
           → Σ[ q ∈ xs Perm.↭ ks ] extract-exact ks xs ≡ just q
    finish .[] p eq refl rewrite eq = Perm.trans p (++-[]-↭ ks) , refl

--------------------------------------------------------------------------------
-- Per-hypergraph strict run.

module Run (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open StrictDecoder H public

  runˢ : Σ[ s ∈ List (Fin H.nV) ] HomS (map vl H.dom) (map vl s)
  runˢ = process-edgesˢ (range H.nE) H.dom

  s-finˢ : List (Fin H.nV)
  s-finˢ = proj₁ runˢ

  ------------------------------------------------------------------------
  -- The strict and non-strict decoders branch on the same
  -- `extract-prefix` calls, hence walk the SAME stacks.

  edge-stack-agree
    : ∀ s e → proj₁ (edge-stepˢ s e) ≡ proj₁ (edge-step H s e)
  edge-stack-agree s e with extract-prefix (H.ein e) s
  ... | nothing = refl
  ... | just _  = refl

  stacks-agree
    : ∀ es s → proj₁ (process-edgesˢ es s) ≡ proj₁ (process-edges H es s)
  stacks-agree []       s = refl
  stacks-agree (e ∷ es) s
    rewrite edge-stack-agree s e = stacks-agree es (proj₁ (edge-step H s e))

--------------------------------------------------------------------------------
-- Transfer of the live decoder's success witness: the strict final stack
-- permutes onto `H.cod`, with the `extract-exact` equation in hand.

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫

  s-fin-cod-↭ : RF.s-finˢ Perm.↭ Hf.cod
  s-fin-cod-↭ =
    subst (Perm._↭ Hf.cod)
      (sym (trans (RF.stacks-agree (range Hf.nE) Hf.dom)
                  (cong proj₁ (proj₁ (proj₂ (proj₂ w))))))
      (proj₂ (proj₂ (proj₂ w)))
    where
      w = decode-attempt-perm-from-just ⟪ f ⟫ (decode-attempt-LinearP f)

  decode-pkgˢ : Σ[ p ∈ RF.s-finˢ Perm.↭ Hf.cod ]
                  extract-exact Hf.cod RF.s-finˢ ≡ just p
  decode-pkgˢ = extract-exact-total Hf.cod RF.s-finˢ s-fin-cod-↭

  finalPermˢ : RF.s-finˢ Perm.↭ Hf.cod
  finalPermˢ = proj₁ decode-pkgˢ

--------------------------------------------------------------------------------
-- The full strict decoder.

decodePˢ : ∀ {A B} (f : HomTerm A B) → HomS (flatten A) (flatten B)
decodePˢ f =
  castˢ (⟪⟫-domL f) (⟪⟫-codL f)
    (Run.permuteˢ ⟪ f ⟫ (finalPermˢ f) ∘ˢ proj₂ (Run.runˢ ⟪ f ⟫))

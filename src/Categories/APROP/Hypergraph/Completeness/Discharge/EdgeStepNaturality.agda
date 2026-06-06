{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Per-edge term-level naturality of the decoder under a hypergraph
-- isomorphism, proved OVER the `edge-step` relation `EdgeStepR` (rather
-- than the opaque `with`-defined `edge-step`) so the case analysis is
-- well-typed (no green-slime with-abstraction).
--
-- `edge-step-term-rel`, at the aligned form (H-edge `e`, J-stack `map φ sH`):
--   * SKIP/SKIP : both terms `id`, closed by `objUIP`;
--   * mixed     : impossible, via `extract-prefix-J-{just,nothing}`;
--   * FIRE/FIRE : ∘-split into box (`fire-mid-rel`, via `box-of-cong` +
--     `objUIP` + `ψ-elab`) and permute (`fire-perm-rel`, via K).
--
-- `objUIP` is available downstream from `Discharge.ObjUIP.objUIP′`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepNaturality
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig using (extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Permute sig using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of; box-of-cong)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using ( subst₂-∘-distrib
        ; just≢nothing; subst₂-HomTerm-id; subst₂-id-≈
        ; permute-subst₂; eval-subst₂-↭ )

open import Categories.APROP.Hypergraph.Completeness.Permute sig using (permute)
open import Categories.Hypergraph.ExtractPrefixEvalPhi using (eval-coincide; ≈-fb-of-≡)
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_; ≈-fb-trans)

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map; length)
open import Data.List.Properties using (map-∘; map-cong; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

--------------------------------------------------------------------------------
-- ≈Term plumbing.  `≡⇒≈Term` comes from `Categories.FreeMonoidal`
-- via `open APROP sig`.

just-injective-fst
  : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
  → just (x , p) ≡ just (y , q) → x ≡ y
just-injective-fst refl = refl

-- Composition of two `subst₂ HomTerm` casts along trans (refl-pattern).
subst₂-∘
  : ∀ {A A' A'' B B' B''}
      (p₁ : A ≡ A') (p₂ : A' ≡ A'') (q₁ : B ≡ B') (q₂ : B' ≡ B'')
      (f : HomTerm A B)
  → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ f)
    ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) f
subst₂-∘ refl refl refl refl f = refl

--------------------------------------------------------------------------------

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
         (K : FaithfulnessResidual) where
  private
    module H = Hypergraph H
    module J = Hypergraph J
  open _≅ᴴ_ Φ using (φ; φ⁻¹; ψ; φ-left; φ-lab; ψ-ein; atom-ein; atom-eout; ψ-elab)
  open FaithfulnessResidual K using (permute-resp-≅↭)

  φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  -- "vertex relabel is free": map J.vlab (map φ s) ≡ map H.vlab s.
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  -- J-side extract-prefix results from the H-side ones, via the injective
  -- lemmas transported along `ψ-ein e`.
  extract-prefix-J-nothing
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
    → extract-prefix (H.ein e) sH ≡ nothing
    → extract-prefix (J.ein (ψ e)) (map φ sH) ≡ nothing
  extract-prefix-J-nothing e sH eqH =
    subst (λ ks → extract-prefix ks (map φ sH) ≡ nothing) (sym (ψ-ein e))
          (extract-prefix-via-injective-nothing φ φ-inj (H.ein e) sH eqH)

  extract-prefix-J-just
    : ∀ (e : Fin H.nE) (sH restH : List (Fin H.nV))
        (pH : sH Perm.↭ H.ein e ++ restH)
    → extract-prefix (H.ein e) sH ≡ just (restH , pH)
    → Σ[ q ∈ map φ sH Perm.↭ J.ein (ψ e) ++ map φ restH ]
        extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (map φ restH , q)
  extract-prefix-J-just e sH restH pH eqH =
    subst (λ ks → Σ[ q ∈ map φ sH Perm.↭ ks ++ map φ restH ]
                    extract-prefix ks (map φ sH) ≡ just (map φ restH , q))
          (sym (ψ-ein e))
          (extract-prefix-via-injective-just φ φ-inj (H.ein e) sH restH pH eqH)

  -- FIRE box factor (M): the two `fire-mid`s agree after the boundary
  -- transport, by splitting each as `subst₂`-of-`box-of`, collapsing the
  -- transports (`subst₂-∘`, `objUIP`), and rewriting the core with
  -- `box-of-cong` fed by `ψ-elab`.
  fire-mid-rel
    : ∀ (e : Fin H.nE)
        (restH : List (Fin H.nV)) (restJ : List (Fin J.nV))
        (restJ≡ : restJ ≡ map φ restH)
        (q : map J.vlab (J.ein  (ψ e) ++ restJ) ≡ map H.vlab (H.ein  e ++ restH))
        (r : map J.vlab (J.eout (ψ e) ++ restJ) ≡ map H.vlab (H.eout e ++ restH))
    → subst₂ HomTerm (cong unflatten q) (cong unflatten r) (fire-mid J (ψ e) restJ)
      ≈Term fire-mid H e restH
  fire-mid-rel e restH restJ restJ≡ q r = ≡⇒≈Term goal-≡
    where
      rest-lab : map J.vlab restJ ≡ map H.vlab restH
      rest-lab = trans (cong (map J.vlab) restJ≡) (vlab-φ restH)

      box-J : HomTerm (unflatten (map J.vlab (J.ein  (ψ e)) ++ map J.vlab restJ))
                      (unflatten (map J.vlab (J.eout (ψ e)) ++ map J.vlab restJ))
      box-J = box-of (map J.vlab (J.ein (ψ e))) (map J.vlab (J.eout (ψ e)))
                     (map J.vlab restJ) (J.elab (ψ e))

      aJ = cong unflatten (sym (map-++ J.vlab (J.ein  (ψ e)) restJ))
      bJ = cong unflatten (sym (map-++ J.vlab (J.eout (ψ e)) restJ))
      aH = cong unflatten (sym (map-++ H.vlab (H.ein  e) restH))
      bH = cong unflatten (sym (map-++ H.vlab (H.eout e) restH))

      goal-≡ : subst₂ HomTerm (cong unflatten q) (cong unflatten r) (fire-mid J (ψ e) restJ)
               ≡ fire-mid H e restH
      goal-≡ =
        trans (subst₂-∘ aJ (cong unflatten q) bJ (cong unflatten r) box-J)
        (trans (cong₂ (λ P Q → subst₂ HomTerm P Q box-J) (objUIP _ _) (objUIP _ _))
        (trans (sym (subst₂-∘
                      (cong unflatten (cong₂ _++_ (atom-ein e) rest-lab)) aH
                      (cong unflatten (cong₂ _++_ (atom-eout e) rest-lab)) bH
                      box-J))
               (cong (subst₂ HomTerm aH bH)
                     (box-of-cong (atom-ein e) (atom-eout e) rest-lab
                                  (J.elab (ψ e)) (H.elab e) (ψ-elab e)))))

  -- FIRE permute factor (K): the two search-permutes agree after the
  -- boundary transport.  The J-side search is the `map φ`-image of the
  -- H-side; `permute-subst₂` pushes the boundary `subst₂` through
  -- `permute`, the derivations have coinciding evaluated bijections
  -- (`eval-coincide`), and K closes the `≈Term`.
  fire-perm-rel
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (p : map J.vlab (map φ sH) ≡ map H.vlab sH)
        (q : map J.vlab (J.ein (ψ e) ++ restJ) ≡ map H.vlab (H.ein e ++ restH))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute-via-vlab J.vlab permJ)
      ≈Term permute-via-vlab H.vlab permH
  fire-perm-rel e sH restH permH eqH restJ permJ eqJ p q =
    helper restJ permJ eqJ q
      (just-injective-fst
        (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH))))
    where
      -- `restJ`-dependents abstracted so matching `restJ ≡ map φ restH`
      -- (then `rewrite ψ-ein e`) is well-typed.
      helper
        : (rJ : List (Fin J.nV))
          (pJ : map φ sH Perm.↭ J.ein (ψ e) ++ rJ)
          (eJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (rJ , pJ))
          (qq : map J.vlab (J.ein (ψ e) ++ rJ) ≡ map H.vlab (H.ein e ++ restH))
        → rJ ≡ map φ restH
        → subst₂ HomTerm (cong unflatten p) (cong unflatten qq)
            (permute-via-vlab J.vlab pJ)
          ≈Term permute-via-vlab H.vlab permH
      helper .(map φ restH) pJ eJ qq refl rewrite ψ-ein e =
        ≈-Term-trans
          (≡⇒≈Term (permute-subst₂ p qq (PermProp.map⁺ J.vlab pJ)))
          (permute-resp-≅↭
            (subst₂ Perm._↭_ p qq (PermProp.map⁺ J.vlab pJ))
            (PermProp.map⁺ H.vlab permH)
            ≅↭ev)
        where
          ≅↭ev : eval-↭ (subst₂ Perm._↭_ p qq (PermProp.map⁺ J.vlab pJ))
               ≈-fb eval-↭ (PermProp.map⁺ H.vlab permH)
          ≅↭ev rewrite eval-subst₂-↭ p qq (PermProp.map⁺ J.vlab pJ) =
            eval-coincide φ φ-inj J.vlab H.vlab φ-lab
              (H.ein e) sH restH permH pJ p qq eqH eJ

  -- FIRE/FIRE: split `fire-mid ∘ permute` (`subst₂-∘-distrib`), then box
  -- (`fire-mid-rel`) ∘ permute (`fire-perm-rel`).
  edge-step-fire-rel
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (stk : J.eout (ψ e) ++ restJ ≡ map φ (H.eout e ++ restH))
    → subst₂ HomTerm
        (cong unflatten (vlab-φ sH))
        (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ (H.eout e ++ restH))))
        (fire-term J (ψ e) (map φ sH) restJ permJ)
      ≈Term fire-term H e sH restH permH
  edge-step-fire-rel e sH restH permH eqH restJ permJ eqJ stk =
    ≈-Term-trans
      (≡⇒≈Term (subst₂-∘-distrib pDom pMidBox rPath
                  (fire-mid J (ψ e) restJ) (permute-via-vlab J.vlab permJ)))
      (∘-resp-≈ (fire-mid-rel e restH restJ restJ≡ pMidBox rPath)
                (fire-perm-rel e sH restH permH eqH restJ permJ eqJ pDom pMidBox))
    where
      pDom : map J.vlab (map φ sH) ≡ map H.vlab sH
      pDom = vlab-φ sH
      restJ≡ : restJ ≡ map φ restH
      restJ≡ = just-injective-fst
                 (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH)))
      pMidBox : map J.vlab (J.ein (ψ e) ++ restJ) ≡ map H.vlab (H.ein e ++ restH)
      pMidBox = trans (cong (map J.vlab)
                        (trans (cong₂ _++_ (ψ-ein e) restJ≡)
                               (sym (map-++ φ (H.ein e) restH))))
                      (vlab-φ (H.ein e ++ restH))
      rPath : map J.vlab (J.eout (ψ e) ++ restJ) ≡ map H.vlab (H.eout e ++ restH)
      rPath = trans (cong (map J.vlab) stk) (vlab-φ (H.eout e ++ restH))

  -- Per-edge-step term naturality, over the `EdgeStepR` witnesses.
  edge-step-term-rel
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        {s'H : List (Fin H.nV)}
        {tH : HomTerm (unflatten (map H.vlab sH)) (unflatten (map H.vlab s'H))}
        {s'J : List (Fin J.nV)}
        {tJ : HomTerm (unflatten (map J.vlab (map φ sH))) (unflatten (map J.vlab s'J))}
        (wH : EdgeStepR H sH e s'H tH)
        (wJ : EdgeStepR J (map φ sH) (ψ e) s'J tJ)
        (stk : s'J ≡ map φ s'H)
    → subst₂ HomTerm
        (cong unflatten (vlab-φ sH))
        (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ s'H)))
        tJ
      ≈Term tH
  edge-step-term-rel e sH (skipR eqH) (skipR eqJ) stk =
    subst₂-id-≈ objUIP (cong unflatten (vlab-φ sH))
                (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ sH)))
  edge-step-term-rel e sH (skipR eqH) (fireR restJ permJ eqJ) stk =
    ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
  edge-step-term-rel e sH (fireR restH permH eqH) (skipR eqJ) stk =
    ⊥-elim (just≢nothing
      (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
  edge-step-term-rel e sH (fireR restH permH eqH) (fireR restJ permJ eqJ) stk =
    edge-step-fire-rel e sH restH permH eqH restJ permJ eqJ stk

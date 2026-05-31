{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Per-edge term-level naturality of the decoder under a hypergraph
-- isomorphism, proved OVER the `edge-step` relation `EdgeStepR`
-- (`EdgeStepRelation.agda`) rather than over the opaque `with`-defined
-- `edge-step` — which is what makes the case analysis well-typed (no
-- green-slime with-abstraction).
--
-- `edge-step-term-rel` is the per-edge-step `≈Term` naturality at the ALIGNED
-- form (H-edge `e`, J-stack literally `map φ sH`):
--   * SKIP/SKIP : both terms are `id`; closed by `objUIP` (UIP on `ObjTerm`),
--     which collapses the boundary loop;
--   * mixed     : impossible, via `extract-prefix-J-{just,nothing}`;
--   * FIRE/FIRE : the genuine content, ∘-split into box (`M`, PROVEN as
--     `fire-mid-rel` via `box-of-cong`+`objUIP`+`ψ-elab`) and permute (`K`,
--     the residual postulate `fire-perm-rel` — a §5b `permute-relabel-free`
--     clone + K).  This is the only postulate left here, strictly smaller than
--     the original per-edge-step `edge-step-term-φ` (now a theorem, bridged in
--     `IsoTransport`).
--
-- The `objUIP` parameter is available downstream from `DecidableEquality X`
-- (`Discharge.ObjUIP.objUIP′`).
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

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-∘; map-cong; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

--------------------------------------------------------------------------------
-- ≈Term plumbing (trivial; local copies, as in IsoTransport §0).

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

subst₂-HomTerm-id : ∀ {A B} (p : A ≡ B) → subst₂ HomTerm p p id ≡ id
subst₂-HomTerm-id refl = refl

just-injective-fst
  : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
  → just (x , p) ≡ just (y , q) → x ≡ y
just-injective-fst refl = refl

-- `subst₂ HomTerm` distributes over `∘` (refl-pattern; as in IsoTransport §0).
subst₂-∘-distrib
  : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
      (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
      (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
      (g : HomTerm (unflatten As₁) (unflatten Bs₁))
  → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ g)
    ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
      ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) g
subst₂-∘-distrib refl refl refl _ _ = refl

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
         (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q) where
  private
    module H = Hypergraph H
    module J = Hypergraph J
  open _≅ᴴ_ Φ using (φ; φ⁻¹; ψ; φ-left; φ-lab; ψ-ein; atom-ein; atom-eout; ψ-elab)

  -- φ is injective (φ-left exhibits φ⁻¹ as a left inverse).
  φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  -- "vertex relabel is free": map J.vlab (map φ s) ≡ map H.vlab s.
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  -- J-side extract-prefix results from the H-side ones (lock-step), via the
  -- injective lemmas transported along `ψ-ein e : J.ein (ψ e) ≡ map φ (H.ein e)`.
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

  -- SKIP closer: with objUIP, transporting `id` along any two boundary paths
  -- with equal endpoints is `≈Term id`.
  subst₂-id-≈ : ∀ {A B : ObjTerm} (p q : A ≡ B) → subst₂ HomTerm p q id ≈Term id
  subst₂-id-≈ p q =
    ≡⇒≈Term (trans (cong (λ z → subst₂ HomTerm z q id) (objUIP p q))
                   (subst₂-HomTerm-id q))

  -- FIRE box factor (M): the generator-carrying `fire-mid` agrees after the
  -- boundary transport.  PROVEN: split each `fire-mid` as `subst₂`-of-`box-of`,
  -- collapse the boundary `subst₂`s with `subst₂-∘`, identify the resulting
  -- ObjTerm paths via `objUIP`, and rewrite the core with `box-of-cong` fed by
  -- the generator agreement `ψ-elab`.
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

  -- FIRE permute factor (K): the two search-permutes agree after the boundary
  -- transport.  TO PROVE by a §5b `permute-relabel-free-≅↭` clone + K.
  postulate
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

  -- FIRE/FIRE assembled: split `fire-mid ∘ permute` via `subst₂-∘-distrib`,
  -- then box (`fire-mid-rel`) ∘ permute (`fire-perm-rel`).
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

  -- The per-edge-step term naturality, over the `EdgeStepR` witnesses.
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
    subst₂-id-≈ (cong unflatten (vlab-φ sH))
                (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ sH)))
  edge-step-term-rel e sH (skipR eqH) (fireR restJ permJ eqJ) stk =
    ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
  edge-step-term-rel e sH (fireR restH permH eqH) (skipR eqJ) stk =
    ⊥-elim (just≢nothing
      (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
  edge-step-term-rel e sH (fireR restH permH eqH) (fireR restJ permJ eqJ) stk =
    edge-step-fire-rel e sH restH permH eqH restJ permJ eqJ stk

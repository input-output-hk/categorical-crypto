{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Lemma 0 of the completeness proof: "vertex relabelling is free + ψ
-- re-indexing".  Discharges the `iso-transport` obligation of
-- `Discharge.IsoInvarianceWiring` (the cross-iso `module _ {H J} (Φ)`).
--
-- ## Mathematical content
--
-- The decoder `process-edges`/`decodeOrd` factors entirely through
-- `map vlab` of the incidence and boundary data; it never inspects
-- vertex *identities*.  Hence the iso's vertex relabel `φ` and edge
-- reindex `ψ` are "free": running `process-edges J (range J.nE)` from
-- `J.dom` and running `process-edges H τ` (`τ = map ψ⁻¹ (range J.nE)`)
-- from `H.dom` produce final stacks related by `map φ`, and the produced
-- HomTerms agree up to `≈Term` after transporting along the iso's
-- label-agreement fields `φ-lab` (vertices) and `ψ-elab` (edge generators).
--
-- ## Interface
--
-- The cross-iso module takes three extra explicit parameters, supplied by
-- `IsoInvarianceConcrete` at the `H = ⟪f⟫`, `J = ⟪g⟫` call site:
--   * `K : FaithfulnessResidual`     (the Kelly faithfulness residual),
--   * `codUniqueH : Unique (cod H)`, `codUniqueJ : Unique (cod J)`
--     (dischargeable from `Sub.FromAPROPCodUnique.⟪_⟫F-cod-unique`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.IsoTransport
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core
  using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; Agen-edge; Agen-edge-aux; extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
open import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig
  using (module PerHG)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (edge-step-graph)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepNaturality sig
  using (edge-step-term-rel)

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (map-∘; map-cong; map-++; map-injective; length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Function using (Injective)
import Data.Fin.Permutation as P
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

-- The Kelly faithfulness residual K and the K-free FinBij/eval
-- infrastructure, taken at the APROP `FreeMonoidalData` so that
-- `permute`/`unflatten`/`HomTerm`/`≈Term` line up definitionally with the
-- APROP-level ones used here.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Categories.PermuteCoherence.EvalRigidKFree
  using ( lookup-injective-unique; lookup-sound; lookup-map; eval-subst₂-↭
        ; subst₂-FinBij-as-subst; cast-irr; subst-Fin-trans; lookup-subst-list
        ; subst-Fin-roundtrip; subst-Fin-roundtrip'; subst-Fin-sym-sym
        ; eval-map⁺ )

--------------------------------------------------------------------------------
-- §0.  ≈Term plumbing.

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

private
  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

-- Transporting the identity along a single path on both ends is the identity.
subst₂-HomTerm-id
  : ∀ {A B} (p : A ≡ B) → subst₂ HomTerm p p id ≡ id
subst₂-HomTerm-id refl = refl

-- `subst₂ HomTerm` distributes over composition.
subst₂-∘-distrib
  : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
      (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
      (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
      (g : HomTerm (unflatten As₁) (unflatten Bs₁))
  → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ g)
    ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
      ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) g
subst₂-∘-distrib refl refl refl _ _ = refl

--------------------------------------------------------------------------------
-- §1.  Cross-iso module.  Mirrors `IsoInvarianceWiring`'s cross-iso
-- module so the names (`PH`, `PJ`, `τ`, `domL-iso`, `codL-iso`) line up
-- exactly with the target `iso-transport` type.

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (dihH : ∀ {e} → ¬ (Dep H e e))
         (dihJ : ∀ {e} → ¬ (Dep J e e))
         (K : FaithfulnessResidual)
         (codUniqueH : Unique (Hypergraph.cod H))
         (codUniqueJ : Unique (Hypergraph.cod J))
         (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q) where
  private
    module PH = PerHG H dihH
    module PJ = PerHG J dihJ
    module H  = Hypergraph H
    module J  = Hypergraph J
  open _≅ᴴ_ Φ
    using (φ; φ⁻¹; ψ; ψ⁻¹; φ-left; φ-rght; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod; ψ-ein; ψ-eout; atom-ein; atom-eout; ψ-elab)
  open FaithfulnessResidual K using (permute-resp-≅↭)

  ------------------------------------------------------------------------
  -- §1.1  Injectivity of φ (re-derived locally; same as EdgeDependency).

  φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  ------------------------------------------------------------------------
  -- §1.2  Boundary identifications, at the same `cong unflatten _`
  -- boundary the target uses.

  domL-iso : domL J ≡ domL H
  domL-iso =
    trans (cong (map J.vlab) φ-dom)
          (trans (sym (map-∘ H.dom))
                 (map-cong φ-lab H.dom))

  codL-iso : codL J ≡ codL H
  codL-iso =
    trans (cong (map J.vlab) φ-cod)
          (trans (sym (map-∘ H.cod))
                 (map-cong φ-lab H.cod))

  ------------------------------------------------------------------------
  -- §1.3  The ψ-pullback order.

  τ : PH.Order
  τ = map ψ⁻¹ (range J.nE)

  ------------------------------------------------------------------------
  -- §2.  Per-edge generator agreement, "vertex relabel is free for
  -- generators".  From the iso's `ψ-elab e` field — which says
  --     subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e)) ≡ H.elab e
  -- — we conclude the relabelled J-generator equals the H-generator.

  subst₂-Agen-edge-aux-nat
    : ∀ {ins₁ ins₂ outs₁ outs₂ : List X}
        (p : ins₁ ≡ ins₂) (q : outs₁ ≡ outs₂)
        (x : FlatGen ins₁ outs₁)
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (Agen-edge-aux x)
    ≡ Agen-edge-aux (subst₂ FlatGen p q x)
  subst₂-Agen-edge-aux-nat refl refl _ = refl

  Agen-edge-respects-ψ
    : ∀ (e : Fin H.nE)
    → subst₂ HomTerm
        (cong unflatten (atom-ein  e))
        (cong unflatten (atom-eout e))
        (Agen-edge J (ψ e))
      ≡ Agen-edge H e
  Agen-edge-respects-ψ e =
    trans (subst₂-Agen-edge-aux-nat (atom-ein e) (atom-eout e) (J.elab (ψ e)))
          (cong Agen-edge-aux (ψ-elab e))

  ------------------------------------------------------------------------
  -- §2b.  Per-edge `edge-step` φ-naturality, STACK component.
  --
  -- For an H-edge `e` and the corresponding J-edge `ψ e`, running
  -- `edge-step J (ψ e)` from `map φ sH` produces the `map φ`-image of the
  -- stack produced by `edge-step H e` from `sH`.  Case-split on
  -- `extract-prefix (H.ein e) sH`; the injective lemmas (transported along
  -- `ψ-ein e : J.ein (ψ e) ≡ map φ (H.ein e)`) put the J-side in the SAME
  -- branch.

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

  edge-step-stack-φ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
    → proj₁ (edge-step J (map φ sH) (ψ e))
      ≡ map φ (proj₁ (edge-step H sH e))
  edge-step-stack-φ e sH
    with extract-prefix (H.ein e) sH
       in eqH
  ... | nothing
        with extract-prefix (J.ein (ψ e)) (map φ sH)
           in eqJ
  ...    | nothing = refl
  ...    | just (restJ , pJ) =
           ⊥-elim (just≢nothing
             (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
  edge-step-stack-φ e sH
      | just (restH , pH)
        with extract-prefix (J.ein (ψ e)) (map φ sH)
           in eqJ
  ...    | nothing =
           ⊥-elim (just≢nothing
             (trans (sym (proj₂ (extract-prefix-J-just e sH restH pH eqH))) eqJ))
  ...    | just (restJ , pJ) =
           -- FIRE/FIRE: the injective lemma forces `restJ ≡ map φ restH`;
           -- combine with `ψ-eout e` + `map-++`.
           let restJ≡ : restJ ≡ map φ restH
               restJ≡ = just-injective-fst
                          (trans (sym eqJ)
                                 (proj₂ (extract-prefix-J-just e sH restH pH eqH)))
           in trans (cong₂ _++_ (ψ-eout e) restJ≡)
                    (sym (map-++ φ (H.eout e) restH))

  ------------------------------------------------------------------------
  -- §2c.  Per-edge-LIST STACK component, by induction on `eJ` using
  -- `edge-step-stack-φ` per step.  This is the `proj₁` (final-stack) half
  -- of the kernel; it provides the `fin≡` component of
  -- `process-edges-respects-φ-T`.

  edge-step-fin-φ
    : ∀ (j : Fin J.nE) {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
        (sJ≡ : sJ ≡ map φ sH)
    → proj₁ (edge-step J sJ j)
      ≡ map φ (proj₁ (edge-step H sH (ψ⁻¹ j)))
  edge-step-fin-φ j {sH} {sJ} sJ≡ =
    trans (cong₂ (λ s u → proj₁ (edge-step J s u)) sJ≡ (sym (ψ-rght j)))
          (edge-step-stack-φ (ψ⁻¹ j) sH)

  process-edges-fin-φ
    : ∀ (eJ : List (Fin J.nE))
        {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
        (sJ≡ : sJ ≡ map φ sH)
    → proj₁ (process-edges J eJ sJ)
      ≡ map φ (proj₁ (process-edges H (map ψ⁻¹ eJ) sH))
  process-edges-fin-φ []       {sH} {sJ} sJ≡ = sJ≡
  process-edges-fin-φ (j ∷ es) {sH} {sJ} sJ≡ =
    process-edges-fin-φ es {proj₁ (edge-step H sH (ψ⁻¹ j))}
                           {proj₁ (edge-step J sJ j)} (edge-step-fin-φ j sJ≡)

  ------------------------------------------------------------------------
  -- §3.  THE TERM-LEVEL INDUCTION KERNEL  (`process-edges-respects-φ`).
  --
  -- The genuine content of Lemma 0, lifted to the `Σ[ stack ] HomTerm`
  -- output of `process-edges`.  For every J-edge list `eJ` and a pair of
  -- stacks related by `map φ`, processing H along the ψ⁻¹-pullback
  -- `map ψ⁻¹ eJ` and J along `eJ` yields final stacks related by `map φ`
  -- and HomTerms agreeing up to `≈Term` after the boundary `subst₂`.
  -- Induct on `eJ`; the per-step content is `edge-step-term-φ`.

  -- The object-equality identifying a J-stack `map J.vlab (map φ s)` with
  -- the corresponding H-stack `map H.vlab s` (free vertex relabel).
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  -- The conclusion-type of the kernel, abstracted so the `[]` case and the
  -- `_∷_` step share a shape.  `fin≡` is fixed to `process-edges-fin-φ`, so
  -- the type is a plain `≈Term` (the cons step plugs the IH term half in
  -- directly, with no opaque `proj₁` to reconcile).
  process-edges-respects-φ-T
    : (eJ : List (Fin J.nE))
      {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
      (sJ≡ : sJ ≡ map φ sH) → Set
  process-edges-respects-φ-T eJ {sH} {sJ} sJ≡ =
    subst₂ HomTerm
      (cong unflatten (trans (cong (map J.vlab) sJ≡) (vlab-φ sH)))
      (cong unflatten (trans (cong (map J.vlab) (process-edges-fin-φ eJ sJ≡))
                             (vlab-φ (proj₁ (process-edges H (map ψ⁻¹ eJ) sH)))))
      (proj₂ (process-edges J eJ sJ))
    ≈Term
    proj₂ (process-edges H (map ψ⁻¹ eJ) sH)

  -- The per-EDGE-STEP `≈Term` φ-naturality: running ONE `edge-step` of
  -- the J-edge `j` vs the H-edge `ψ⁻¹ j` produces `≈Term`-equal HomTerms
  -- after the boundary `subst₂`.  Its boundary `subst₂` paths are exactly
  -- the DOM/MID factor produced by the `subst₂-∘-distrib` split in
  -- `process-edges-respects-φ-step`, so it plugs in directly.
  --
  -- Proven by the relation-view naturality `edge-step-term-rel`
  -- (`EdgeStepNaturality`), bridged to the `j`/`ψ⁻¹ j` form: `rewrite sJ≡`
  -- aligns the J-stack to `map φ sH`, then a single `subst` over the J-edge
  -- (along `ψ-rght j`) with a Π-over-stack-path motive `G` (which absorbs
  -- the boundary-path difference) converts the `ψ (ψ⁻¹ j)` statement to the
  -- `j` statement.
  edge-step-term-φ
    : ∀ (j : Fin J.nE) {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
        (sJ≡ : sJ ≡ map φ sH)
    → subst₂ HomTerm
        (cong unflatten (trans (cong (map J.vlab) sJ≡) (vlab-φ sH)))
        (cong unflatten (trans (cong (map J.vlab) (edge-step-fin-φ j sJ≡))
                               (vlab-φ (proj₁ (edge-step H sH (ψ⁻¹ j))))))
        (proj₂ (edge-step J sJ j))
      ≈Term proj₂ (edge-step H sH (ψ⁻¹ j))
  edge-step-term-φ j {sH} {sJ} sJ≡ rewrite sJ≡ =
    subst G (ψ-rght j)
      (λ pth → edge-step-term-rel Φ objUIP K (ψ⁻¹ j) sH
                 (edge-step-graph H sH (ψ⁻¹ j))
                 (edge-step-graph J (map φ sH) (ψ (ψ⁻¹ j)))
                 pth)
      (edge-step-fin-φ j refl)
    where
      G : (jE : Fin J.nE) → Set
      G jE = (pth : proj₁ (edge-step J (map φ sH) jE)
                    ≡ map φ (proj₁ (edge-step H sH (ψ⁻¹ j))))
           → subst₂ HomTerm
               (cong unflatten (vlab-φ sH))
               (cong unflatten (trans (cong (map J.vlab) pth)
                                      (vlab-φ (proj₁ (edge-step H sH (ψ⁻¹ j))))))
               (proj₂ (edge-step J (map φ sH) jE))
             ≈Term proj₂ (edge-step H sH (ψ⁻¹ j))

  -- The per-edge-LIST STEP, from `edge-step-term-φ` + the IH.  The
  -- composite `proj₂ (process-edges J (j ∷ es) sJ) = tJ' ∘ tJ` has its
  -- boundary `subst₂` split at the intermediate object by
  -- `subst₂-∘-distrib`; the COD factor is the IH term half on `es`, the
  -- DOM factor is `edge-step-term-φ`.
  process-edges-respects-φ-step
    : ∀ (j : Fin J.nE) (es : List (Fin J.nE))
    → ( ∀ {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)} (sJ≡ : sJ ≡ map φ sH)
        → process-edges-respects-φ-T es sJ≡ )
    → ∀ {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)} (sJ≡ : sJ ≡ map φ sH)
    → process-edges-respects-φ-T (j ∷ es) sJ≡
  process-edges-respects-φ-step j es IH {sH} {sJ} sJ≡ = term-half
    where
      sH'  = proj₁ (edge-step H sH (ψ⁻¹ j))
      sJ'  = proj₁ (edge-step J sJ j)
      tJ   = proj₂ (edge-step J sJ j)
      tH   = proj₂ (edge-step H sH (ψ⁻¹ j))
      tJ'  = proj₂ (process-edges J es sJ')
      tH'  = proj₂ (process-edges H (map ψ⁻¹ es) sH')
      step≡ : sJ' ≡ map φ sH'
      step≡ = edge-step-fin-φ j sJ≡

      sFinH = proj₁ (process-edges H (map ψ⁻¹ es) sH')

      -- The three boundary list-equalities of the split.
      pDom = trans (cong (map J.vlab) sJ≡)   (vlab-φ sH)
      pMid = trans (cong (map J.vlab) step≡) (vlab-φ sH')
      pCod = trans (cong (map J.vlab) (process-edges-fin-φ es step≡)) (vlab-φ sFinH)

      split
        : subst₂ HomTerm (cong unflatten pDom) (cong unflatten pCod) (tJ' ∘ tJ)
          ≡ subst₂ HomTerm (cong unflatten pMid) (cong unflatten pCod) tJ'
            ∘ subst₂ HomTerm (cong unflatten pDom) (cong unflatten pMid) tJ
      split = subst₂-∘-distrib pDom pMid pCod tJ' tJ

      term-half
        : subst₂ HomTerm (cong unflatten pDom) (cong unflatten pCod) (tJ' ∘ tJ)
          ≈Term tH' ∘ tH
      term-half =
        ≈-Term-trans (≡⇒≈Term split)
          (∘-resp-≈ (IH {sH'} {sJ'} step≡)
                    (edge-step-term-φ j sJ≡))

  -- The kernel, by induction on `eJ`.
  process-edges-respects-φ
    : ∀ (eJ : List (Fin J.nE))
        {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
        (sJ≡ : sJ ≡ map φ sH)
    → process-edges-respects-φ-T eJ sJ≡
  process-edges-respects-φ []       {sH} {sJ} sJ≡ =
    -- `[]`: DOM and COD boundary paths coincide; goal is
    -- `subst₂ HomTerm p p id ≈Term id`.
    ≡⇒≈Term (subst₂-HomTerm-id
              (cong unflatten (trans (cong (map J.vlab) sJ≡) (vlab-φ sH))))
  process-edges-respects-φ (j ∷ es) {sH} {sJ} sJ≡ =
    process-edges-respects-φ-step j es
      (λ {sH'} {sJ'} sJ≡' → process-edges-respects-φ es sJ≡') sJ≡

  ------------------------------------------------------------------------
  -- §4.  Validity (stack) transport.
  --
  -- From the final-stack equation at the natural order and `J.cod ≡ map φ
  -- H.cod` (`φ-cod`), both endpoints of `vJ` become `map φ` of an H-list;
  -- `map φ` reflects `↭` (φ injective ⇒ `map⁻`), giving the H-side validity
  -- `vτ : proj₁ (process-edges H τ H.dom) ↭ H.cod`.

  private
    -- The H-side final stack of the natural pullback order.
    sH-final : List (Fin H.nV)
    sH-final = proj₁ (process-edges H τ H.dom)

    -- Final-stack equation at the natural order (`map ψ⁻¹ (range J.nE) = τ`).
    fin-eq : proj₁ (process-edges J (range J.nE) J.dom) ≡ map φ sH-final
    fin-eq = process-edges-fin-φ (range J.nE) {H.dom} {J.dom} φ-dom

  -- `map φ` reflects `↭` for injective `φ`, via stdlib's `↭-map-inv` +
  -- `map-injective`.
  φ-Injective : Injective _≡_ _≡_ φ
  φ-Injective = φ-inj

  map-φ-↭⁻ : ∀ {xs ys : List (Fin H.nV)} → map φ xs Perm.↭ map φ ys → xs Perm.↭ ys
  map-φ-↭⁻ {xs} {ys} p with PermProp.↭-map-inv φ p
  ... | ys' , mapφys≡mapφys' , xs↭ys' =
        subst (xs Perm.↭_)
              (sym (map-injective {f = φ} φ-Injective mapφys≡mapφys'))
              xs↭ys'

  iso-valid : PJ.Valid (range J.nE) → PH.Valid τ
  iso-valid vJ = map-φ-↭⁻ step
    where
      step : map φ sH-final Perm.↭ map φ H.cod
      step =
        subst (λ z → z Perm.↭ map φ H.cod)
              fin-eq
              (subst (λ z → proj₁ (process-edges J (range J.nE) J.dom) Perm.↭ z)
                     φ-cod
                     vJ)

  ------------------------------------------------------------------------
  -- §5.  Assembly:  `iso-transport`.
  --
  -- `decodeOrd o p = permute-via-vlab vlab p ∘ proj₂ (process-edges o dom)`.
  -- After the boundary `subst₂`, the composite splits as `∘-resp-≈`:
  --   * the `proj₂ (process-edges …)` factors match by
  --     `process-edges-respects-φ` (§3);
  --   * the final `permute-via-vlab` factors match by `permute-relabel-free`
  --     (§5b) — vertex relabel is free for permutes too.

  private
    -- The J-side final stack.
    sJ-final : List (Fin J.nV)
    sJ-final = proj₁ (process-edges J (range J.nE) J.dom)

    -- The bridge object-equality at the intermediate (final-stack) point.
    mid-iso : map J.vlab sJ-final ≡ map H.vlab sH-final
    mid-iso = trans (cong (map J.vlab) fin-eq) (vlab-φ sH-final)

  ------------------------------------------------------------------------
  -- §5b.  Permute relabel-freeness (`permute-relabel-free`).
  --
  -- Proven given K.  The boundary `subst₂` is pushed THROUGH `permute` onto
  -- the underlying `_↭_` derivation (`permute-subst₂`); both sides then
  -- become `permute` of two derivations over the SAME pair of `map H.vlab _`
  -- lists, so the Kelly residual K (`permute-resp-≅↭`) closes the `≈Term`
  -- goal from the `≅↭` evidence `permute-relabel-free-≅↭`.
  --
  -- That `≅↭` evidence — the φ-equivariant rigidity of the two final
  -- permutes — is discharged constructively below: their evaluated
  -- bijections coincide because the vertex relabel `φ` is a bijection and
  -- the Fin-level codomain `H.cod` is `Unique` (`codUniqueH`).

  -- `permute` commutes with `subst₂` along list equalities.
  permute-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
      ≡ permute (subst₂ Perm._↭_ p q r)
  permute-subst₂ refl refl r = refl

  -- The two final-permute derivations, brought onto the common pair of
  -- `map H.vlab _` lists.
  private
    permJ-↭ : (vJ : PJ.Valid (range J.nE))
            → map J.vlab sJ-final Perm.↭ map J.vlab J.cod
    permJ-↭ vJ = PermProp.map⁺ J.vlab vJ

    permJ-↭' : (vJ : PJ.Valid (range J.nE))
             → map H.vlab sH-final Perm.↭ map H.vlab H.cod
    permJ-↭' vJ = subst₂ Perm._↭_ mid-iso codL-iso (permJ-↭ vJ)

    permH-↭ : (vJ : PJ.Valid (range J.nE))
            → map H.vlab sH-final Perm.↭ map H.vlab H.cod
    permH-↭ vJ = PermProp.map⁺ H.vlab (iso-valid vJ)

  -- φ-equivariant rigidity of the two final permutes, at the
  -- finite-bijection level.  Both `eval-↭ (permJ-↭' vJ)` and
  -- `eval-↭ (permH-↭ vJ)` are bijections `Fin (length (map H.vlab
  -- sH-final)) → Fin (length (map H.vlab H.cod))`; their forward maps agree
  -- pointwise.  Cast the image index back to `Fin (length H.cod)` and
  -- discriminate through the `Unique` list `H.cod`: both sides land on the
  -- SAME position, because `lookup-sound` pins each image to the
  -- corresponding `sH-final` vertex (J-side via `lookup J.cod = φ ∘ lookup
  -- H.cod` from `φ-cod`, and `sJ-final = map φ sH-final` from `fin-eq`,
  -- with `φ` injective).

  private
    -- The two length-casts used to descend from the `map H.vlab _` sizes to
    -- the underlying Fin-list sizes.
    cH-dom : length (map H.vlab sH-final) ≡ length sH-final
    cH-dom = length-map H.vlab sH-final

    cH-cod : length (map H.vlab H.cod) ≡ length H.cod
    cH-cod = length-map H.vlab H.cod

    -- The composite cast `length J.cod ≡ length H.cod` along `φ-cod`.
    cJH : length J.cod ≡ length H.cod
    cJH = trans (cong length φ-cod) (length-map φ H.cod)

    -- `lookup J.cod` factors as `φ ∘ lookup H.cod` after the `cJH` cast.
    lookup-Jcod-φ
      : (k : Fin (length J.cod))
      → φ (lookup H.cod (subst Fin cJH k)) ≡ lookup J.cod k
    lookup-Jcod-φ k =
      trans (sym (lookup-map φ H.cod (subst Fin cJH k)))
        (trans (cong (lookup (map φ H.cod)) reduce-idx)
               (lookup-subst-list φ-cod k))
      where
        reduce-idx
          : subst Fin (sym (length-map φ H.cod)) (subst Fin cJH k)
            ≡ subst Fin (cong length φ-cod) k
        reduce-idx =
          trans (cong (subst Fin (sym (length-map φ H.cod)))
                      (sym (subst-Fin-trans (cong length φ-cod) (length-map φ H.cod) k)))
                (subst-Fin-roundtrip (length-map φ H.cod)
                   (subst Fin (cong length φ-cod) k))

    -- `lookup sJ-final` factors as `φ ∘ lookup sH-final` after the
    -- `fin-eq`-cast.
    cSJH : length sJ-final ≡ length sH-final
    cSJH = trans (cong length fin-eq) (length-map φ sH-final)

    lookup-sJ-φ
      : (k : Fin (length sJ-final))
      → φ (lookup sH-final (subst Fin cSJH k)) ≡ lookup sJ-final k
    lookup-sJ-φ k =
      trans (sym (lookup-map φ sH-final (subst Fin cSJH k)))
        (trans (cong (lookup (map φ sH-final)) reduce-idx)
               (lookup-subst-list fin-eq k))
      where
        reduce-idx
          : subst Fin (sym (length-map φ sH-final)) (subst Fin cSJH k)
            ≡ subst Fin (cong length fin-eq) k
        reduce-idx =
          trans (cong (subst Fin (sym (length-map φ sH-final)))
                      (sym (subst-Fin-trans (cong length fin-eq) (length-map φ sH-final) k)))
                (subst-Fin-roundtrip (length-map φ sH-final)
                   (subst Fin (cong length fin-eq) k))

  permute-relabel-free-≅↭
    : (vJ : PJ.Valid (range J.nE))
    → eval-↭ (permJ-↭' vJ) ≈-fb eval-↭ (permH-↭ vJ)
  permute-relabel-free-≅↭ vJ i = goal
    where
      -- The two images of `i` (at the `map H.vlab _` sizes).
      kJ kH : Fin (length (map H.vlab H.cod))
      kJ = eval-↭ (permJ-↭' vJ) P.⟨$⟩ʳ i
      kH = eval-↭ (permH-↭ vJ) P.⟨$⟩ʳ i

      -- The shared descent of the DOMAIN index `i` to `Fin (length sH-final)`.
      iH : Fin (length sH-final)
      iH = subst Fin cH-dom i

      ----------------------------------------------------------------
      -- H-side.  Rewrite `kH` via `eval-map⁺`, peel the `subst₂` to a pair
      -- of `subst Fin`-casts, cancel the codomain cast against `cH-cod`, and
      -- apply `lookup-sound (iso-valid vJ)`.
      ----------------------------------------------------------------
      kH≡ : subst Fin cH-cod kH
            ≡ eval-↭ (iso-valid vJ) P.⟨$⟩ʳ iH
      kH≡ =
        trans (cong (λ z → subst Fin cH-cod (z P.⟨$⟩ʳ i))
                    (eval-map⁺ H.vlab (iso-valid vJ)))
        (trans (cong (subst Fin cH-cod)
                     (subst₂-FinBij-as-subst (sym cH-dom) (sym cH-cod)
                        (eval-↭ (iso-valid vJ)) i))
        (trans (subst-Fin-roundtrip' cH-cod
                  (eval-↭ (iso-valid vJ) P.⟨$⟩ʳ subst Fin (sym (sym cH-dom)) i))
               (cong (eval-↭ (iso-valid vJ) P.⟨$⟩ʳ_)
                     (subst-Fin-sym-sym cH-dom i))))

      H-step
        : lookup H.cod (subst Fin cH-cod kH)
          ≡ lookup sH-final iH
      H-step =
        trans (cong (lookup H.cod) kH≡)
              (lookup-sound (iso-valid vJ) iH)

      ----------------------------------------------------------------
      -- J-side.  Rewrite `kJ` via `eval-subst₂-↭` then `eval-map⁺`, peel the
      -- nested `subst₂`s, normalise the codomain casts to the single `cJH`
      -- cast (`cast-irr`/`subst-Fin-trans`), and obtain the underlying
      -- J-index `jJ`.
      ----------------------------------------------------------------
      -- The DOMAIN index `i` descended to `Fin (length sJ-final)` (through
      -- the H-final stack and the φ-relabel `cSJH`).
      iJ : Fin (length sJ-final)
      iJ = subst Fin (sym cSJH) iH

      jJ : Fin (length J.cod)
      jJ = eval-↭ vJ P.⟨$⟩ʳ iJ

      private-lmJd : length (map J.vlab sJ-final) ≡ length sJ-final
      private-lmJd = length-map J.vlab sJ-final

      private-lmJc : length (map J.vlab J.cod) ≡ length J.cod
      private-lmJc = length-map J.vlab J.cod

      -- The J-side image, with its domain index normalised to `iJ` and its
      -- codomain cast normalised to `cJH`.  Peels the two nested `subst₂`s
      -- into single `subst Fin` casts and collapses them.
      kJ≡ : subst Fin cH-cod kJ ≡ subst Fin cJH jJ
      kJ≡ =
        trans (cong (λ z → subst Fin cH-cod (z P.⟨$⟩ʳ i))
                    (trans (eval-subst₂-↭ mid-iso codL-iso (permJ-↭ vJ))
                           (cong (subst₂ FinBij (cong length mid-iso)
                                                 (cong length codL-iso))
                                 (eval-map⁺ J.vlab vJ))))
        (trans (cong (subst Fin cH-cod)
                     (subst₂-FinBij-as-subst (cong length mid-iso) (cong length codL-iso)
                        (subst₂ FinBij (sym private-lmJd) (sym private-lmJc) (eval-↭ vJ)) i))
        (trans (cong (λ z → subst Fin cH-cod (subst Fin (cong length codL-iso) z))
                     (subst₂-FinBij-as-subst (sym private-lmJd) (sym private-lmJc) (eval-↭ vJ)
                        (subst Fin (sym (cong length mid-iso)) i)))
          (cod-collapse)))
        where
          DOM₀ : Fin (length sJ-final)
          DOM₀ = subst Fin (sym (sym private-lmJd))
                   (subst Fin (sym (cong length mid-iso)) i)

          -- The image we are casting on the codomain side.
          IMG : Fin (length J.cod)
          IMG = eval-↭ vJ P.⟨$⟩ʳ DOM₀

          -- DOM₀ ≡ iJ (domain index normalisation).
          dom-eq : DOM₀ ≡ iJ
          dom-eq =
            trans (subst-Fin-trans (sym (cong length mid-iso)) (sym (sym private-lmJd)) i)
            (trans (cast-irr (trans (sym (cong length mid-iso)) (sym (sym private-lmJd)))
                             (trans cH-dom (sym cSJH)) i)
                   (sym (subst-Fin-trans cH-dom (sym cSJH) i)))

          -- Codomain casts collapse:
          --   subst cH-cod (subst (cong length codL-iso) (subst (sym private-lmJc) IMG))
          --     ≡ subst cJH IMG.
          cod-collapse
            : subst Fin cH-cod
                (subst Fin (cong length codL-iso)
                   (subst Fin (sym private-lmJc) IMG))
              ≡ subst Fin cJH jJ
          cod-collapse =
            trans (cong (subst Fin cH-cod)
                        (subst-Fin-trans (sym private-lmJc) (cong length codL-iso) IMG))
            (trans (subst-Fin-trans
                      (trans (sym private-lmJc) (cong length codL-iso)) cH-cod IMG)
            (trans (cast-irr
                      (trans (trans (sym private-lmJc) (cong length codL-iso)) cH-cod)
                      cJH IMG)
                   (cong (subst Fin cJH) (cong (eval-↭ vJ P.⟨$⟩ʳ_) dom-eq))))

      ----------------------------------------------------------------
      -- J-side `lookup` discriminator: descended kJ lands on `lookup sH-final iH`.
      ----------------------------------------------------------------
      J-step
        : lookup H.cod (subst Fin cH-cod kJ)
          ≡ lookup sH-final iH
      J-step =
        φ-inj
          (trans
            -- φ (lookup H.cod (subst cH-cod kJ)) ≡ lookup sJ-final iJ
            (trans (cong (λ z → φ (lookup H.cod z)) kJ≡)
              (trans (lookup-Jcod-φ jJ)
                     (lookup-sound vJ iJ)))
            -- lookup sJ-final iJ ≡ φ (lookup sH-final iH)
            (trans (sym (lookup-sJ-φ iJ))
                   (cong (λ z → φ (lookup sH-final z))
                         (subst-Fin-roundtrip' cSJH iH))))

      ----------------------------------------------------------------
      -- Both descended images discriminate to the SAME `H.cod` position;
      -- `H.cod` is `Unique` so the descended indices are equal, and the
      -- descent cast `subst Fin cH-cod` is injective.
      ----------------------------------------------------------------
      goal : kJ ≡ kH
      goal =
        trans (sym (subst-Fin-roundtrip cH-cod kJ))
        (trans (cong (subst Fin (sym cH-cod))
                     (lookup-injective-unique codUniqueH
                        (subst Fin cH-cod kJ) (subst Fin cH-cod kH)
                        (trans J-step (sym H-step))))
               (subst-Fin-roundtrip cH-cod kH))

  -- The headline §5 lemma, from K + the `≅↭` evidence.
  permute-relabel-free
    : (vJ : PJ.Valid (range J.nE))
    → subst₂ HomTerm
        (cong unflatten mid-iso) (cong unflatten codL-iso)
        (permute-via-vlab J.vlab vJ)
      ≈Term permute-via-vlab H.vlab (iso-valid vJ)
  permute-relabel-free vJ =
    ≈-Term-trans
      (≡⇒≈Term (permute-subst₂ mid-iso codL-iso (permJ-↭ vJ)))
      (permute-resp-≅↭ (permJ-↭' vJ) (permH-↭ vJ) (permute-relabel-free-≅↭ vJ))

  -- The assembly `≈Term`, from the §3 kernel + `permute-relabel-free`.
  iso-transport-≈
    : (vJ : PJ.Valid (range J.nE))
    → subst₂ HomTerm
        (cong unflatten domL-iso) (cong unflatten codL-iso)
        (PJ.decodeOrd (range J.nE) vJ)
      ≈Term PH.decodeOrd τ (iso-valid vJ)
  iso-transport-≈ vJ =
    ≈-Term-trans (≡⇒≈Term split) (∘-resp-≈ perm-factor proc-factor)
    where
      procJ′ : HomTerm (unflatten (map J.vlab J.dom)) (unflatten (map J.vlab sJ-final))
      procJ′ = proj₂ (process-edges J (range J.nE) J.dom)

      permJ′ : HomTerm (unflatten (map J.vlab sJ-final)) (unflatten (map J.vlab J.cod))
      permJ′ = permute-via-vlab J.vlab vJ

      -- Split the outer subst₂ over the `permJ′ ∘ procJ′` composite at
      -- the intermediate object `unflatten (map H.vlab sH-final)`.
      split
        : subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                 (permJ′ ∘ procJ′)
        ≡ subst₂ HomTerm (cong unflatten mid-iso) (cong unflatten codL-iso) permJ′
          ∘ subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten mid-iso) procJ′
      split = subst₂-∘-distrib domL-iso mid-iso codL-iso permJ′ procJ′

      -- The permute factor: `permute-relabel-free`.
      perm-factor
        : subst₂ HomTerm (cong unflatten mid-iso) (cong unflatten codL-iso) permJ′
        ≈Term permute-via-vlab H.vlab (iso-valid vJ)
      perm-factor = permute-relabel-free vJ

      -- The process factor: EXACTLY the §3 kernel's LHS at
      -- `eJ = range J.nE`, `sH = H.dom`, `sJ = J.dom`, `sJ≡ = φ-dom`
      -- (the boundary proofs match literally).
      proc-factor
        : subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten mid-iso) procJ′
        ≈Term proj₂ (process-edges H τ H.dom)
      proc-factor = process-edges-respects-φ (range J.nE) {H.dom} {J.dom} φ-dom

  -- The exported lemma, matching the `IsoInvarianceWiring` type verbatim.
  iso-transport
    : (vJ : PJ.Valid (range J.nE))
    → Σ[ vτ ∈ PH.Valid τ ]
        ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                 (PJ.decodeOrd (range J.nE) vJ)
          ≈Term PH.decodeOrd τ vτ )
  iso-transport vJ = iso-valid vJ , iso-transport-≈ vJ

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Congruence rules for `hComposeP` (the pruned `hCompose`, Option A).
--
-- Parallel to `Hypergraph.Congruence.hCompose-resp-≅ᴴ`. The existing
-- Congruence proof operates on the unpruned `hCompose`; this module ports
-- the structural piece to the pruned variant so a future Soundness
-- rewrite can use `hComposeP` in its `∘-resp-≈` case and still get a
-- congruence lemma out.
--
-- CURRENT STATUS: vertex + edge bijections with left/right inverse
-- proofs. Full `hComposeP-resp-≅ᴴ` record remaining:
--
--   * φ-lab-P (vertex label preservation): inj₁ case identical to
--     Congruence.φ-lab-C; inj₂ case needs
--       vlab-P₂ (raise G₂.nV (pruneK jK))
--       = K₂.vlab (lookup (nonMem K₂.dom) (pruneK jK))
--       ≡? K₁.vlab (lookup (nonMem K₁.dom) jK)
--     which reduces via `subst` on IK.φ-dom and `lookup-pruneMap`
--     (+ IK.φ-lab).
--
--   * ψ-ein-P / ψ-eout-P (edge endpoint preservation): for the inj₂
--     (K-side) branch, use `map-via-remapP` lifted along pruneK.
--
--   * φ-dom-P / φ-cod-P (boundary preservation): map injL-style for
--     dom (G-side only), map-through-pruneMap for cod.
--
--   * atom-ein-P / atom-eout-P (atom-level equality for ≅ᴴ's
--     derived fields).
--
--   * ψ-elab-P (the big six-step subst₂ chain): longest piece, same
--     shape as the unpruned `ψ-elab-C`, with extra subst through
--     pruneK in the inj₂ case.
--
-- Once assembled, `hComposeP-resp-≅ᴴ : G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
--                                    → hComposeP G₁ K₁ ≅ᴴ hComposeP G₂ K₂`
-- discharges `∘-resp-≈` in a Soundness rewrite using `hComposeP`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CongruenceP (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Prune
  using ( count-non; nonMem; nonMem?; classify
        ; classify-inj₁-lookup; classify-inj₂-lookup
        ; classify-inj₁-∈; classify-inj₂-∉
        ; pruneMap; pruneMap⁻¹
        ; pruneMap-left-inverse; pruneMap-right-inverse
        ; ∉-map-injective; nonMem-member
        ; index-∈-filter-irrelevant
        ; subst-∈-filter-index; subst-lookup-nonMem
        ; lookup-pruneMap; nonMem-Unique; lookup-injective-unique)
open import Categories.APROP.Hypergraph.PrunedCompose sig

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; inject+; raise; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-inject+; splitAt-raise;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List using (List; []; _∷_; map; lookup)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Vertex bijection for the pruned composite, parametric in two hypergraph
-- isos iG : G₁ ≅ᴴ G₂, iK : K₁ ≅ᴴ K₂, plus a distinctness assumption on
-- K₁.dom (required to pin down the K-side `remapP-comm` — holds for all
-- translated APROP terms ⟪ f ⟫ via a future invariant).

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

module _
    {As Bs Cs : List X}
    {G₁ G₂ : Hypergraph FlatGen As Bs}
    {K₁ K₂ : Hypergraph FlatGen Bs Cs}
    (iG : G₁ ≅ᴴ G₂) (iK : K₁ ≅ᴴ K₂)
    (K₁-dom-unique : Unique (Hypergraph.dom K₁)) where

  private
    module G₁ = Hypergraph G₁
    module G₂ = Hypergraph G₂
    module K₁ = Hypergraph K₁
    module K₂ = Hypergraph K₂
    module IG = _≅ᴴ_ iG
    module IK = _≅ᴴ_ iK

  -- IK.φ is injective, derivable from IK.φ-left.
  private
    IK-φ-inj : ∀ {x y} → IK.φ x ≡ IK.φ y → x ≡ y
    IK-φ-inj {x} {y} eq =
      trans (sym (IK.φ-left x)) (trans (cong IK.φ⁻¹ eq) (IK.φ-left y))

  -- Pruned K-side bijection: `Fin (count-non K₁.dom) → Fin (count-non K₂.dom)`.
  -- Routes `jK` through `pruneMap` on IK.φ, then `subst`s across
  -- `K₂.dom ≡ map IK.φ K₁.dom`.
  pruneK : Fin (count-non K₁.dom) → Fin (count-non K₂.dom)
  pruneK jK = subst (λ ys → Fin (count-non ys)) (sym IK.φ-dom)
                    (pruneMap IK.φ IK-φ-inj K₁.dom jK)

  pruneK⁻¹ : Fin (count-non K₂.dom) → Fin (count-non K₁.dom)
  pruneK⁻¹ kK =
    pruneMap⁻¹ IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom
               (subst (λ ys → Fin (count-non ys)) IK.φ-dom kK)

  -- Vertex bijection of the composites.
  φ-P : Fin (G₁.nV + count-non K₁.dom) → Fin (G₂.nV + count-non K₂.dom)
  φ-P i = [ (λ iG → inject+ (count-non K₂.dom) (IG.φ iG))
          , (λ iK → raise G₂.nV (pruneK iK))
          ]′ (splitAt G₁.nV i)

  φ⁻¹-P : Fin (G₂.nV + count-non K₂.dom) → Fin (G₁.nV + count-non K₁.dom)
  φ⁻¹-P j = [ (λ jG → inject+ (count-non K₁.dom) (IG.φ⁻¹ jG))
            , (λ jK → raise G₁.nV (pruneK⁻¹ jK))
            ]′ (splitAt G₂.nV j)

  -- Left inverse of the K-side pruned bijection.
  -- `pruneK⁻¹ (pruneK jK) = pruneMap⁻¹ ... (subst ... (subst ... (pruneMap ... jK)))`
  -- and the two substs cancel via `subst-sym-subst`.
  private
    subst-sym-subst : ∀ {A : Set} {B : A → Set} {a₁ a₂ : A}
                    → (eq : a₁ ≡ a₂) (x : B a₁)
                    → subst B (sym eq) (subst B eq x) ≡ x
    subst-sym-subst refl _ = refl

    subst-subst-sym : ∀ {A : Set} {B : A → Set} {a₁ a₂ : A}
                    → (eq : a₁ ≡ a₂) (x : B a₂)
                    → subst B eq (subst B (sym eq) x) ≡ x
    subst-subst-sym refl _ = refl

  pruneK-left : ∀ jK → pruneK⁻¹ (pruneK jK) ≡ jK
  pruneK-left jK =
    trans (cong (pruneMap⁻¹ IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom)
                (subst-subst-sym IK.φ-dom
                                  (pruneMap IK.φ IK-φ-inj K₁.dom jK)))
          (pruneMap-left-inverse IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom jK)

  pruneK-right : ∀ kK → pruneK (pruneK⁻¹ kK) ≡ kK
  pruneK-right kK =
    trans (cong (subst (λ ys → Fin (count-non ys)) (sym IK.φ-dom))
                (pruneMap-right-inverse IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght
                                         K₁.dom _))
          (subst-sym-subst IK.φ-dom kK)

  -- φ-P / φ⁻¹-P roundtrips. Same structure as the unpruned Congruence,
  -- split on `splitAt G₁.nV i` and use `splitAt-inject+` / `splitAt-raise`
  -- to collapse.
  φ-left-P : ∀ i → φ⁻¹-P (φ-P i) ≡ i
  φ-left-P i with splitAt G₁.nV i in eq
  ... | inj₁ iG rewrite splitAt-inject+ G₂.nV (count-non K₂.dom) (IG.φ iG)
                      | IG.φ-left iG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ jK rewrite splitAt-raise G₂.nV (count-non K₂.dom) (pruneK jK)
                      | pruneK-left jK
                    = splitAt⁻¹-↑ʳ eq

  φ-rght-P : ∀ j → φ-P (φ⁻¹-P j) ≡ j
  φ-rght-P j with splitAt G₂.nV j in eq
  ... | inj₁ jG rewrite splitAt-inject+ G₁.nV (count-non K₁.dom) (IG.φ⁻¹ jG)
                      | IG.φ-rght jG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ kK rewrite splitAt-raise G₁.nV (count-non K₁.dom) (pruneK⁻¹ kK)
                      | pruneK-right kK
                    = splitAt⁻¹-↑ʳ eq

  --------------------------------------------------------------------------------
  -- Edge bijection. Identical structure to the unpruned
  -- `Congruence.hCompose-resp-≅ᴴ`, since `hComposeP` has the same edge
  -- count (G.nE + K.nE) as `hCompose` — pruning only affects vertices.

  ψ-P : Fin (G₁.nE + K₁.nE) → Fin (G₂.nE + K₂.nE)
  ψ-P e = [ (λ eG → inject+ K₂.nE (IG.ψ eG))
          , (λ eK → raise G₂.nE (IK.ψ eK))
          ]′ (splitAt G₁.nE e)

  ψ⁻¹-P : Fin (G₂.nE + K₂.nE) → Fin (G₁.nE + K₁.nE)
  ψ⁻¹-P e = [ (λ eG → inject+ K₁.nE (IG.ψ⁻¹ eG))
            , (λ eK → raise G₁.nE (IK.ψ⁻¹ eK))
            ]′ (splitAt G₂.nE e)

  ψ-left-P : ∀ e → ψ⁻¹-P (ψ-P e) ≡ e
  ψ-left-P e with splitAt G₁.nE e in eq
  ... | inj₁ eG rewrite splitAt-inject+ G₂.nE K₂.nE (IG.ψ eG)
                      | IG.ψ-left eG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK rewrite splitAt-raise G₂.nE K₂.nE (IK.ψ eK)
                      | IK.ψ-left eK
                    = splitAt⁻¹-↑ʳ eq

  ψ-rght-P : ∀ e → ψ-P (ψ⁻¹-P e) ≡ e
  ψ-rght-P e with splitAt G₂.nE e in eq
  ... | inj₁ eG rewrite splitAt-inject+ G₁.nE K₁.nE (IG.ψ⁻¹ eG)
                      | IG.ψ-rght eG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK rewrite splitAt-raise G₁.nE K₁.nE (IK.ψ⁻¹ eK)
                      | IK.ψ-rght eK
                    = splitAt⁻¹-↑ʳ eq

  --------------------------------------------------------------------------------
  -- Label preservation φ-lab-P.
  --
  -- vlab-P₂ (φ-P i) ≡ vlab-P₁ i, where vlab-P is the pruned composite's
  -- labeling `[ G.vlab , λ j → K.vlab (lookup (nonMem K.dom) j) ]′ ∘ splitAt`.

  open import Categories.APROP.Hypergraph.Prune
    using (pruneMap-left-inverse)

  private
    vlab-P₁ : Fin (G₁.nV + count-non K₁.dom) → X
    vlab-P₁ v = [ G₁.vlab , (λ j → K₁.vlab (lookup (nonMem K₁.dom) j)) ]′
                  (splitAt G₁.nV v)

    vlab-P₂ : Fin (G₂.nV + count-non K₂.dom) → X
    vlab-P₂ v = [ G₂.vlab , (λ j → K₂.vlab (lookup (nonMem K₂.dom) j)) ]′
                  (splitAt G₂.nV v)

    -- When we pattern-match on IK.φ-dom as refl (unifying K₂.dom with
    -- map IK.φ K₁.dom), the subst in pruneK collapses and pruneK
    -- becomes pruneMap directly.
    pruneK-lookup : ∀ jK → K₂.vlab (lookup (nonMem K₂.dom) (pruneK jK))
                         ≡ K₁.vlab (lookup (nonMem K₁.dom) jK)
    pruneK-lookup jK with K₂.dom | IK.φ-dom
    ... | ._ | refl =
      -- After unification: K₂.dom := map IK.φ K₁.dom, pruneK jK := pruneMap ... jK.
      -- Goal: K₂.vlab (lookup (nonMem (map IK.φ K₁.dom)) (pruneMap ... jK))
      --    ≡ K₁.vlab (lookup (nonMem K₁.dom) jK)
      -- Rewrite using lookup-pruneMap: lookup (nonMem (map IK.φ K₁.dom)) (pruneMap ... jK)
      --                              ≡ IK.φ (lookup (nonMem K₁.dom) jK)
      -- Then IK.φ-lab: K₂.vlab (IK.φ v) ≡ K₁.vlab v.
      trans (cong K₂.vlab
                   (Prune.lookup-pruneMap IK.φ IK-φ-inj K₁.dom jK))
            (IK.φ-lab (lookup (nonMem K₁.dom) jK))
      where import Categories.APROP.Hypergraph.Prune as Prune

  φ-lab-P : ∀ i → vlab-P₂ (φ-P i) ≡ vlab-P₁ i
  φ-lab-P i with splitAt G₁.nV i
  ... | inj₁ iG =
    trans (cong [ G₂.vlab , _ ]′
                 (splitAt-inject+ G₂.nV (count-non K₂.dom) (IG.φ iG)))
          (IG.φ-lab iG)
  ... | inj₂ jK =
    trans (cong [ G₂.vlab , _ ]′
                 (splitAt-raise G₂.nV (count-non K₂.dom) (pruneK jK)))
          (pruneK-lookup jK)

  --------------------------------------------------------------------------------
  -- Boundary helpers: φ-P applied to an `injL` (G-side inject).

  open import Data.List.Properties using (map-∘; map-cong)

  φ-P-injL : ∀ i → φ-P (inject+ (count-non K₁.dom) i)
                 ≡ inject+ (count-non K₂.dom) (IG.φ i)
  φ-P-injL i rewrite splitAt-inject+ G₁.nV (count-non K₁.dom) i = refl

  -- List-wise version used in the dom-P case of hComposeP-resp-≅ᴴ.
  map-φ-P-injL : (xs : List (Fin G₁.nV))
               → map φ-P (map (inject+ (count-non K₁.dom)) xs)
               ≡ map (inject+ (count-non K₂.dom)) (map IG.φ xs)
  map-φ-P-injL xs = trans (sym (map-∘ xs))
                          (trans (map-cong φ-P-injL xs) (map-∘ xs))

  --------------------------------------------------------------------------------
  -- Boundary preservation (dom only; cod requires the deeper remapP-comm).
  --
  -- `dom-P : (hComposeP G₂ K₂).dom ≡ map φ-P (hComposeP G₁ K₁).dom`
  -- reduces to `G₂.dom ≡ map IG.φ G₁.dom` after the inject+ commutation.

  private
    module hCP₁ = hComposeP-impl G₁ K₁
    module hCP₂ = hComposeP-impl G₂ K₂

  dom-P : Hypergraph.dom (hComposeP G₂ K₂)
        ≡ map φ-P (Hypergraph.dom (hComposeP G₁ K₁))
  dom-P = trans (cong (map (inject+ (count-non K₂.dom))) IG.φ-dom)
                (sym (map-φ-P-injL G₁.dom))

  --------------------------------------------------------------------------------
  -- G-side ψ-ein/ψ-eout clauses. The inj₁ case of the full `ψ-ein-P /
  -- ψ-eout-P` is identical to the unpruned version: an `inject+` of
  -- `G.ein`/`G.eout` followed by the `map-φ-P-injL` commutation. The
  -- inj₂ (K-side) branch requires `map-remapP-comm` (the pruned analog
  -- of `Congruence.map-remap-comm`), which relies on a `remapP-comm`
  -- showing `φ-P ∘ remapP₁ ≡ remapP₂ ∘ IK.φ` — left for the next
  -- iteration of this module.

  open import Data.List.Properties using () renaming (map-∘ to List-map-∘)

  -- Inj₁ branch (G-side) of ψ-ein-P.
  ψ-ein-P-inj₁ : ∀ (eG : Fin G₁.nE)
               → hCP₂.ein-c (inject+ K₂.nE (IG.ψ eG))
               ≡ map φ-P (map (inject+ (count-non K₁.dom)) (G₁.ein eG))
  ψ-ein-P-inj₁ eG =
    trans (hCP₂.ein-c-inj₁-red (IG.ψ eG))
          (trans (cong (map (inject+ (count-non K₂.dom))) (IG.ψ-ein eG))
                 (sym (map-φ-P-injL (G₁.ein eG))))

  -- Inj₁ branch of ψ-eout-P.
  ψ-eout-P-inj₁ : ∀ (eG : Fin G₁.nE)
                → hCP₂.eout-c (inject+ K₂.nE (IG.ψ eG))
                ≡ map φ-P (map (inject+ (count-non K₁.dom)) (G₁.eout eG))
  ψ-eout-P-inj₁ eG =
    trans (hCP₂.eout-c-inj₁-red (IG.ψ eG))
          (trans (cong (map (inject+ (count-non K₂.dom))) (IG.ψ-eout eG))
                 (sym (map-φ-P-injL (G₁.eout eG))))

  --------------------------------------------------------------------------------
  -- Atom-list equalities. These don't require `remapP-comm` — they go
  -- through `map-via-remapP` from both sides, meeting in the middle at
  -- the K-side boundary atoms.

  atom-ein-P : ∀ e → map hCP₂.vlab-P (hCP₂.ein-c (ψ-P e))
                   ≡ map hCP₁.vlab-P (hCP₁.ein-c e)
  atom-ein-P e with splitAt G₁.nE e
  ... | inj₁ eG =
    -- ψ-P on inj₁ produces `inject+ K₂.nE (IG.ψ eG)`; reduce via
    -- ein-c-inj₁-red to `map injL₂ (G₂.ein (IG.ψ eG))`; then thread
    -- through `sym (map-via-inj vlab-injL)` + `IG.atom-ein` +
    -- `map-via-inj vlab-injL` (matching the unpruned proof verbatim,
    -- except injL is `inject+ (count-non K.dom)` instead of `inject+ K.nV`).
    trans (cong (map hCP₂.vlab-P) (hCP₂.ein-c-inj₁-red (IG.ψ eG)))
    (trans (sym (map-via-inj hCP₂.vlab-injL (G₂.ein (IG.ψ eG))))
    (trans (IG.atom-ein eG)
           (map-via-inj hCP₁.vlab-injL (G₁.ein eG))))
  ... | inj₂ eK =
    trans (cong (map hCP₂.vlab-P) (hCP₂.ein-c-inj₂-red (IK.ψ eK)))
    (trans (sym (hCP₂.map-via-remapP (K₂.ein (IK.ψ eK))))
    (trans (IK.atom-ein eK)
           (hCP₁.map-via-remapP (K₁.ein eK))))

  atom-eout-P : ∀ e → map hCP₂.vlab-P (hCP₂.eout-c (ψ-P e))
                    ≡ map hCP₁.vlab-P (hCP₁.eout-c e)
  atom-eout-P e with splitAt G₁.nE e
  ... | inj₁ eG =
    trans (cong (map hCP₂.vlab-P) (hCP₂.eout-c-inj₁-red (IG.ψ eG)))
    (trans (sym (map-via-inj hCP₂.vlab-injL (G₂.eout (IG.ψ eG))))
    (trans (IG.atom-eout eG)
           (map-via-inj hCP₁.vlab-injL (G₁.eout eG))))
  ... | inj₂ eK =
    trans (cong (map hCP₂.vlab-P) (hCP₂.eout-c-inj₂-red (IK.ψ eK)))
    (trans (sym (hCP₂.map-via-remapP (K₂.eout (IK.ψ eK))))
    (trans (IK.atom-eout eK)
           (hCP₁.map-via-remapP (K₁.eout eK))))

  --------------------------------------------------------------------------------
  -- Impossibility lemmas for the cross-iso membership cases in
  -- `remapP-comm`. Uses IK-φ-inj (derived from IK.φ-left) plus IK.φ-dom
  -- to relate K₁.dom membership with K₂.dom membership.

  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-map⁺; ∈-map⁻)
  open import Data.List.Membership.DecPropositional (_≟_ {n = K₁.nV})
    using () renaming (_∈?_ to _∈K₁?_)
  open import Data.List.Membership.DecPropositional (_≟_ {n = K₂.nV})
    using () renaming (_∈?_ to _∈K₂?_)
  open import Data.Product using (_,_; proj₁; proj₂)

  private
    -- If v ∈ K₁.dom, then IK.φ v ∈ K₂.dom (via K₂.dom ≡ map IK.φ K₁.dom).
    ∈K₁→∈K₂ : ∀ {v} → v ∈ K₁.dom → IK.φ v ∈ K₂.dom
    ∈K₁→∈K₂ v∈ =
      subst (IK.φ _ ∈_) (sym IK.φ-dom) (∈-map⁺ IK.φ v∈)

    -- If IK.φ v ∈ K₂.dom, then v ∈ K₁.dom (via ∈-map⁻ + IK-φ-inj).
    -- Note: ∈-map⁻ returns `∃ λ v' → v' ∈ K₁.dom × IK.φ v ≡ IK.φ v'`,
    -- so we apply IK-φ-inj to get v ≡ v' and sym to convert for subst.
    ∈K₂→∈K₁ : ∀ {v} → IK.φ v ∈ K₂.dom → v ∈ K₁.dom
    ∈K₂→∈K₁ {v} φv∈ with ∈-map⁻ IK.φ (subst (IK.φ v ∈_) IK.φ-dom φv∈)
    ... | v' , v'∈K₁ , φv≡φv' =
      subst (_∈ K₁.dom) (sym (IK-φ-inj φv≡φv')) v'∈K₁

  --------------------------------------------------------------------------------
  -- remapP-comm — the central commutation lemma for the K-side
  -- vertex bijection. Four-way case split.

  open import Categories.APROP.Hypergraph.Prune
    using (nonMem-member; lookup-pruneMap)

  -- Derived φ-P formulae on injL / injR, for use below.
  private
    φ-P-injR : ∀ jK → φ-P (raise G₁.nV jK) ≡ raise G₂.nV (pruneK jK)
    φ-P-injR jK rewrite splitAt-raise G₁.nV (count-non K₁.dom) jK = refl

  open import Data.List.Relation.Unary.Any using (index)
  open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
  open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-allFin)

  open import Data.List using (length)
  open import Data.List.Properties using (length-map)
  open import Data.Fin using (cast)
  open import Data.Fin.Properties using (cast-is-id; toℕ-cast)
  open import Categories.APROP.Hypergraph.Prune
    using (lookup-map-cast; lookup-≡-map-cast)

  -- Derived: Unique K₂.dom (since K₂.dom = map IK.φ K₁.dom, and IK.φ
  -- is injective — follows from IK.φ-left).
  private
    import Data.List.Relation.Unary.Unique.Propositional.Properties as UP

    K₂-dom-unique : Unique K₂.dom
    K₂-dom-unique =
      subst Unique (sym IK.φ-dom) (UP.map⁺ IK-φ-inj K₁-dom-unique)

  -- The yes-yes index coherence, now fully proved.
  --
  -- Strategy: both sides compare positions in Fin (length G₂.cod).
  -- Using `K₂-dom-unique` + `lookup-injective-unique`, we pin down
  -- that i₂ equals `cast (cong length IK.φ-dom) i₁` in Fin (length K₂.dom).
  -- Then `IG.φ-cod` + `lookup-map-cast` commute `IG.φ` through the
  -- G₂-cod lookup, yielding the desired equality.

  open import Data.Fin.Properties using (cast-trans; cast-is-id)

  lookup-cod-coherence
    : ∀ (v : Fin K₁.nV)
        (i₁ : Fin (length K₁.dom))
        (i₂ : Fin (length K₂.dom))
    → classify K₁.dom v ≡ inj₁ i₁
    → classify K₂.dom (IK.φ v) ≡ inj₁ i₂
    → IG.φ (hCP₁.lookup-cod i₁) ≡ hCP₂.lookup-cod i₂
  lookup-cod-coherence v i₁ i₂ eq₁ eq₂ = proof
    where
      look-v : lookup K₁.dom i₁ ≡ v
      look-v = classify-inj₁-lookup K₁.dom v i₁ eq₁

      look-φv : lookup K₂.dom i₂ ≡ IK.φ v
      look-φv = classify-inj₁-lookup K₂.dom (IK.φ v) i₂ eq₂

      len-eq : length K₂.dom ≡ length K₁.dom
      len-eq = trans (cong length IK.φ-dom) (length-map IK.φ K₁.dom)

      i₁→₂ : Fin (length K₂.dom)
      i₁→₂ = cast (sym len-eq) i₁

      look-i₁→₂ : lookup K₂.dom i₁→₂ ≡ IK.φ v
      look-i₁→₂ = trans (lookup-≡-map-cast IK.φ IK.φ-dom i₁)
                        (cong IK.φ look-v)

      i₁→₂≡i₂ : i₁→₂ ≡ i₂
      i₁→₂≡i₂ = lookup-injective-unique K₂-dom-unique i₁→₂ i₂
                  (trans look-i₁→₂ (sym look-φv))

      i₁-in-G₁ : Fin (length G₁.cod)
      i₁-in-G₁ = cast hCP₁.dom-cod-len i₁

      look-G : IG.φ (hCP₁.lookup-cod i₁)
             ≡ lookup G₂.cod
                 (cast (sym (trans (cong length IG.φ-cod)
                                    (length-map IG.φ G₁.cod)))
                       i₁-in-G₁)
      look-G = sym (lookup-≡-map-cast IG.φ IG.φ-cod i₁-in-G₁)

      -- Two casts of i₁ into Fin (length G₂.cod) with different proofs.
      -- Since Fin.cast's proof is irrelevant, they are propositionally equal.
      cast-irr : ∀ .(p q : length K₁.dom ≡ length G₂.cod)
               → cast p i₁ ≡ cast q i₁
      cast-irr _ _ = refl

      fin-eq : cast (sym (trans (cong length IG.φ-cod)
                                 (length-map IG.φ G₁.cod)))
                    i₁-in-G₁
             ≡ cast hCP₂.dom-cod-len i₂
      fin-eq =
        trans (cast-trans hCP₁.dom-cod-len _ i₁)
          (trans (cast-irr _ _)
            (sym (trans (cong (cast hCP₂.dom-cod-len) (sym i₁→₂≡i₂))
                        (cast-trans (sym len-eq) hCP₂.dom-cod-len i₁))))

      proof : IG.φ (hCP₁.lookup-cod i₁) ≡ hCP₂.lookup-cod i₂
      proof = trans look-G (cong (lookup G₂.cod) fin-eq)

  remapP-comm : ∀ v → φ-P (hCP₁.remapP v) ≡ hCP₂.remapP (IK.φ v)
  remapP-comm v with classify K₁.dom v in eq₁ | classify K₂.dom (IK.φ v) in eq₂
  ... | inj₁ i₁ | inj₁ i₂ =
    -- φ-P (inject+ (count-non K₁.dom) (lookup-cod₁ i₁))
    --   ≡ inject+ (count-non K₂.dom) (IG.φ (lookup-cod₁ i₁))     [φ-P-injL]
    --   ≡ inject+ (count-non K₂.dom) (lookup-cod₂ i₂)             [lookup-cod-coherence]
    --   ≡ hCP₂.remapP (IK.φ v)                                    [classify gives inj₁ i₂]
    trans (φ-P-injL (hCP₁.lookup-cod i₁))
          (cong (inject+ (count-non K₂.dom))
                (lookup-cod-coherence v i₁ i₂ eq₁ eq₂))
  ... | inj₁ i₁ | inj₂ j₂ =
    ⊥-elim (classify-inj₂-∉ eq₂ (∈K₁→∈K₂ (classify-inj₁-∈ eq₁)))
  ... | inj₂ j₁ | inj₁ i₂ =
    ⊥-elim (classify-inj₂-∉ eq₁ (∈K₂→∈K₁ (classify-inj₁-∈ eq₂)))
  ... | inj₂ j₁ | inj₂ j₂ =
    -- φ-P (raise G₁.nV j₁) ≡ raise G₂.nV (pruneK j₁)  [φ-P-injR]
    -- pruneK j₁ ≡ j₂                                  [lookup-injective-unique]
    trans (φ-P-injR j₁)
          (cong (raise G₂.nV)
            (lookup-injective-unique (nonMem-Unique K₂.dom) (pruneK j₁) j₂
              (trans lookup-LHS (sym lookup-RHS))))
    where
      lookup-j₁≡v : lookup (nonMem K₁.dom) j₁ ≡ v
      lookup-j₁≡v = classify-inj₂-lookup K₁.dom v j₁ eq₁

      lookup-j₂≡φv : lookup (nonMem K₂.dom) j₂ ≡ IK.φ v
      lookup-j₂≡φv = classify-inj₂-lookup K₂.dom (IK.φ v) j₂ eq₂

      lookup-LHS : lookup (nonMem K₂.dom) (pruneK j₁) ≡ IK.φ v
      lookup-LHS = trans
        (subst-lookup-nonMem (sym IK.φ-dom)
                              (pruneMap IK.φ IK-φ-inj K₁.dom j₁))
        (trans (lookup-pruneMap IK.φ IK-φ-inj K₁.dom j₁)
               (cong IK.φ lookup-j₁≡v))

      lookup-RHS : lookup (nonMem K₂.dom) j₂ ≡ IK.φ v
      lookup-RHS = lookup-j₂≡φv

  --------------------------------------------------------------------------------
  -- Edge label compatibility ψ-elab-P (the big six-step subst₂ chain).
  --
  -- Structure mirrors `Congruence.ψ-elab-C`: three nested `subst₂-trans`
  -- collapses to re-associate proof chains, then `subst₂-sym-subst₂`
  -- cancellation, one more `subst₂-trans`, and finally the IG.ψ-elab /
  -- IK.ψ-elab endpoint. Only difference from the unpruned proof: the
  -- K-side `map-via-remap` is replaced by `map-via-remapP`, and all
  -- `hC?.*` calls become `hCP?.*`.

  open import Relation.Binary.PropositionalEquality using (subst₂)

  private
    subst₂-trans : ∀ {A B : Set} {P : A → B → Set} {a₁ a₂ a₃} {b₁ b₂ b₃}
                 → (p : a₁ ≡ a₂) (p' : a₂ ≡ a₃) (q : b₁ ≡ b₂) (q' : b₂ ≡ b₃)
                 → (x : P a₁ b₁)
                 → subst₂ P p' q' (subst₂ P p q x)
                 ≡ subst₂ P (trans p p') (trans q q') x
    subst₂-trans refl refl refl refl _ = refl

    subst₂-sym-subst₂ : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                      → (p : a ≡ a') (q : b ≡ b') (x : P a b)
                      → subst₂ P (sym p) (sym q) (subst₂ P p q x) ≡ x
    subst₂-sym-subst₂ refl refl _ = refl

  ψ-elab-P : ∀ e →
    subst₂ FlatGen (atom-ein-P e) (atom-eout-P e)
                   (hCP₂.elab-c (ψ-P e))
    ≡ hCP₁.elab-c e
  ψ-elab-P e with splitAt G₁.nE e
  ... | inj₁ eG =
    let
      α   = cong (map hCP₂.vlab-P) (hCP₂.ein-c-inj₁-red (IG.ψ eG))
      α'  = cong (map hCP₂.vlab-P) (hCP₂.eout-c-inj₁-red (IG.ψ eG))
      β̄   = map-via-inj hCP₂.vlab-injL (G₂.ein  (IG.ψ eG))
      β̄'  = map-via-inj hCP₂.vlab-injL (G₂.eout (IG.ψ eG))
      γ   = IG.atom-ein  eG
      γ'  = IG.atom-eout eG
      δ   = map-via-inj hCP₁.vlab-injL (G₁.ein  eG)
      δ'  = map-via-inj hCP₁.vlab-injL (G₁.eout eG)
      x   = hCP₂.elab-c (inject+ K₂.nE (IG.ψ eG))
    in
    trans
      (sym (subst₂-trans α (trans (sym β̄) (trans γ δ))
                         α' (trans (sym β̄') (trans γ' δ'))
                         x))
    (trans
      (cong (subst₂ FlatGen (trans (sym β̄) (trans γ δ))
                            (trans (sym β̄') (trans γ' δ')))
            (hCP₂.elab-c-inj₁ (IG.ψ eG)))
    (trans
      (sym (subst₂-trans (sym β̄) (trans γ δ)
                         (sym β̄') (trans γ' δ')
                         (subst₂ FlatGen β̄ β̄' (G₂.elab (IG.ψ eG)))))
    (trans
      (cong (subst₂ FlatGen (trans γ δ) (trans γ' δ'))
            (subst₂-sym-subst₂ β̄ β̄' (G₂.elab (IG.ψ eG))))
    (trans
      (sym (subst₂-trans γ δ γ' δ' (G₂.elab (IG.ψ eG))))
      (cong (subst₂ FlatGen δ δ') (IG.ψ-elab eG))))))
  ... | inj₂ eK =
    let
      α   = cong (map hCP₂.vlab-P) (hCP₂.ein-c-inj₂-red (IK.ψ eK))
      α'  = cong (map hCP₂.vlab-P) (hCP₂.eout-c-inj₂-red (IK.ψ eK))
      β̄   = hCP₂.map-via-remapP (K₂.ein  (IK.ψ eK))
      β̄'  = hCP₂.map-via-remapP (K₂.eout (IK.ψ eK))
      γ   = IK.atom-ein  eK
      γ'  = IK.atom-eout eK
      δ   = hCP₁.map-via-remapP (K₁.ein  eK)
      δ'  = hCP₁.map-via-remapP (K₁.eout eK)
      x   = hCP₂.elab-c (raise G₂.nE (IK.ψ eK))
    in
    trans
      (sym (subst₂-trans α (trans (sym β̄) (trans γ δ))
                         α' (trans (sym β̄') (trans γ' δ'))
                         x))
    (trans
      (cong (subst₂ FlatGen (trans (sym β̄) (trans γ δ))
                            (trans (sym β̄') (trans γ' δ')))
            (hCP₂.elab-c-inj₂ (IK.ψ eK)))
    (trans
      (sym (subst₂-trans (sym β̄) (trans γ δ)
                         (sym β̄') (trans γ' δ')
                         (subst₂ FlatGen β̄ β̄' (K₂.elab (IK.ψ eK)))))
    (trans
      (cong (subst₂ FlatGen (trans γ δ) (trans γ' δ'))
            (subst₂-sym-subst₂ β̄ β̄' (K₂.elab (IK.ψ eK))))
    (trans
      (sym (subst₂-trans γ δ γ' δ' (K₂.elab (IK.ψ eK))))
      (cong (subst₂ FlatGen δ δ') (IK.ψ-elab eK))))))

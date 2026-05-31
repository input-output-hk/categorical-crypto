{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Decoder STACK-EQUIVARIANCE.
--
-- Running the hypergraph decoder's `process-edges` on a *permuted* input
-- stack equals running it on the original stack, sandwiched between an
-- input-permute (precompose) and an output-permute (postcompose).  This is
-- the lemma that lets the per-swap interchange `run-eq` of `SwapStep.agda`
-- (the `RunInterchange` record) be reduced from an arbitrary tail `qs` to
-- the empty-tail two-edge core: equivariance lets you strip a permutation of
-- the running stack and re-attach it as `permute`s on the boundary.
--
-- It is generator-OPAQUE — it touches no generator box content, no
-- associator chase — only permute/permutation-coherence bookkeeping and
-- firing-stability.  Proven by induction on the edge list, over the
-- `EdgeStepR` relation view (`EdgeStepRelation.agda`) to dodge the
-- green-slime `with`-abstraction wall.
--
-- ## Precise statement (`process-edges-equivariant`)
--
-- For an edge list `qs`, stacks `s s'`, and a permutation `ρ : s' ↭ s`,
-- there is an induced output permutation `ρ_f : pe-stack qs s' ↭ pe-stack
-- qs s` with
--
--   pe-term qs s'
--     ≈Term  permute-via-vlab vlab (↭-sym ρ_f)
--              ∘ pe-term qs s ∘ permute-via-vlab vlab ρ
--
-- ("permute the input into canonical order, run, permute the output back").
--
-- ## Status / residual
--
-- The induction, the SKIP and impossible cross-cases, the list-level
-- threading, the inverse/self-loop permute facts (via the Kelly residual
-- `K : FaithfulnessResidual`), and the FIRE-permute reconciliation (also via
-- K) are PROVEN here, postulate-free except for TWO clearly-flagged residual
-- sub-lemmas about a SINGLE edge-step's FIRE branch:
--
--   * `fire-mid-equivariant` — the per-edge FIRE box is natural in its
--     residual stack under a *permutation* of that residual.  Concretely:
--     `splitJoin`-ing the (fixed, edge-only) box `(Agen-edge e ⊗ id)` over a
--     residual `restH'` equals doing it over a permuted residual `restH`
--     conjugated by the residual permute on the `id`-block.  TRUE — the box
--     acts as identity on the residual, so a permutation of the residual
--     commutes with it (interchange `id ∘ p ⊗ q ∘ id`); but the boundary
--     `subst₂`/`unflatten-++-≅` bookkeeping makes the constructive chase
--     lengthy, so it is isolated here.  This is strictly the box-naturality
--     half (no firing data, no `cod`).
--
--   * `fire-locate-coherent` — the two locating permutations agree as
--     bijections after vertex labelling (a `≅↭`), so K reconciles them.  This
--     is the identity-relabel / stack-permute analogue of the proven
--     `Categories.Hypergraph.ExtractPrefixEvalPhi.eval-coincide` (which proves
--     exactly this for a φ-relabel and NO stack-permute).  TRUE because
--     `extract-prefix` locates the same multiset-prefix canonically; isolated
--     here as the locating-coherence half (no box, no `cod`).
--
-- Both residuals concern only ONE edge's FIRE box; they carry NO firing data
-- across the list and NO final `cod` permute — the same residual posture as
-- `EdgeStepNaturality.fire-perm-rel` and `SwapStep.RunInterchange.run-eq`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; edge-step-graph; edge-step-sound)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidEquivariant sig as FME

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual; permute-self-loop-id-wide)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; inv-fb; _∘-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (≈-fb-trans; eval-↭-sym)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

--------------------------------------------------------------------------------
-- ≈Term plumbing.

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) (K : FaithfulnessResidual) where
  private module H = Hypergraph H
  open FaithfulnessResidual K using (permute-resp-≅↭)

  -- Abbreviations matching SwapStep's `pe-stack`/`pe-term`.
  pe-stack : List (Fin H.nE) → List (Fin H.nV) → List (Fin H.nV)
  pe-stack qs s = proj₁ (process-edges H qs s)

  pe-term : (qs : List (Fin H.nE)) (s : List (Fin H.nV))
          → HomTerm (unflatten (map H.vlab s))
                    (unflatten (map H.vlab (pe-stack qs s)))
  pe-term qs s = proj₂ (process-edges H qs s)

  ----------------------------------------------------------------------
  -- `permute-via-vlab` algebra (all under K / definitional).
  --
  -- `permute-via-vlab vlab p = permute (map⁺ vlab p)` definitionally;
  -- `permute (trans p q) = permute q ∘ permute p` definitionally; and
  -- `map⁺ vlab (trans p q) = trans (map⁺ vlab p) (map⁺ vlab q)`.
  ----------------------------------------------------------------------

  -- `permute-via-vlab` of a `trans` splits as a ∘ (postcompose the first).
  pvv-trans
    : ∀ {xs ys zs : List (Fin H.nV)} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → permute-via-vlab H.vlab (Perm.trans p q)
      ≈Term permute-via-vlab H.vlab q ∘ permute-via-vlab H.vlab p
  pvv-trans p q = ≈-Term-refl

  -- `map⁺` commutes with `↭-sym` PROPOSITIONALLY (both are structural
  -- recursions with matching shapes).  Pure induction on ρ; no K.
  map⁺-↭-sym
    : ∀ {A B : Set} (f : A → B) {xs ys : List A} (ρ : xs Perm.↭ ys)
    → PermProp.map⁺ f (Perm.↭-sym ρ) ≡ Perm.↭-sym (PermProp.map⁺ f ρ)
  map⁺-↭-sym f Perm.refl          = refl
  map⁺-↭-sym f (Perm.prep x ρ)    = cong (Perm.prep _) (map⁺-↭-sym f ρ)
  map⁺-↭-sym f (Perm.swap x y ρ)  = cong (Perm.swap _ _) (map⁺-↭-sym f ρ)
  map⁺-↭-sym f (Perm.trans p q)   =
    cong₂ Perm.trans (map⁺-↭-sym f q) (map⁺-↭-sym f p)

  -- `↭-sym` commutes through `++⁺ˡ` (the fixed prefix is `prep`-built, and
  -- `↭-sym (prep x p) = prep x (↭-sym p)`).  Induction on `xs`.
  ++⁺ˡ-↭-sym
    : ∀ {A : Set} (xs : List A) {ys zs : List A} (p : ys Perm.↭ zs)
    → Perm.↭-sym (PermProp.++⁺ˡ xs p) ≡ PermProp.++⁺ˡ xs (Perm.↭-sym p)
  ++⁺ˡ-↭-sym []       p = refl
  ++⁺ˡ-↭-sym (x ∷ xs) p = cong (Perm.prep x) (++⁺ˡ-↭-sym xs p)

  -- `permute-via-vlab vlab (↭-sym ρ) ∘ permute-via-vlab vlab ρ ≈Term id`,
  -- via K: `trans ρ (↭-sym ρ)` is a self-loop evaluating to id-fb.
  pvv-inverse-left
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permute-via-vlab H.vlab (Perm.↭-sym ρ) ∘ permute-via-vlab H.vlab ρ ≈Term id
  pvv-inverse-left {xs} {ys} ρ =
    ≈-Term-trans (≈-Term-sym (pvv-trans ρ (Perm.↭-sym ρ)))
                 (permute-self-loop-id-wide K
                    (PermProp.map⁺ H.vlab (Perm.trans ρ (Perm.↭-sym ρ)))
                    self-loop-id)
    where
      -- The vertex-level bijection of ρ.
      e : FinBij _ _
      e = eval-↭ (PermProp.map⁺ H.vlab ρ)

      -- `eval (map⁺ vlab (↭-sym ρ)) ≈-fb inv-fb e` by `map⁺-↭-sym` + `eval-↭-sym`.
      sym-eval : eval-↭ (PermProp.map⁺ H.vlab (Perm.↭-sym ρ)) ≈-fb inv-fb e
      sym-eval = subst (λ z → eval-↭ z ≈-fb inv-fb e)
                       (sym (map⁺-↭-sym H.vlab ρ))
                       (eval-↭-sym (PermProp.map⁺ H.vlab ρ))

      -- `eval (map⁺ vlab (trans ρ (↭-sym ρ))) = eval(map⁺ (↭-sym ρ)) ∘-fb e`
      -- (definitional), and `inv-fb e ∘-fb e ≈-fb id-fb` by `P.inverseˡ`.
      -- `eval (map⁺ vlab (trans ρ (↭-sym ρ))) ⟨$⟩ʳ i`
      --   = eval(map⁺ (↭-sym ρ)) ⟨$⟩ʳ (e ⟨$⟩ʳ i)   (def: eval-trans + map⁺-trans)
      --   = inv-fb e ⟨$⟩ʳ (e ⟨$⟩ʳ i)                (sym-eval, pointwise at e⟨$⟩ʳi)
      --   = e ⟨$⟩ˡ (e ⟨$⟩ʳ i) = i                   (P.inverseˡ).
      self-loop-id
        : eval-↭ (PermProp.map⁺ H.vlab (Perm.trans ρ (Perm.↭-sym ρ))) ≈-fb id-fb
      self-loop-id i =
        trans (sym-eval (e P.⟨$⟩ʳ i)) (P.inverseˡ e)

  -- `permute-via-vlab vlab ρ ∘ permute-via-vlab vlab (↭-sym ρ) ≈Term id`.
  pvv-inverse-right
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permute-via-vlab H.vlab ρ ∘ permute-via-vlab H.vlab (Perm.↭-sym ρ) ≈Term id
  pvv-inverse-right {xs} {ys} ρ =
    ≈-Term-trans (≈-Term-sym (pvv-trans (Perm.↭-sym ρ) ρ))
                 (permute-self-loop-id-wide K
                    (PermProp.map⁺ H.vlab (Perm.trans (Perm.↭-sym ρ) ρ))
                    self-loop-id)
    where
      e : FinBij _ _
      e = eval-↭ (PermProp.map⁺ H.vlab ρ)

      sym-eval : eval-↭ (PermProp.map⁺ H.vlab (Perm.↭-sym ρ)) ≈-fb inv-fb e
      sym-eval = subst (λ z → eval-↭ z ≈-fb inv-fb e)
                       (sym (map⁺-↭-sym H.vlab ρ))
                       (eval-↭-sym (PermProp.map⁺ H.vlab ρ))

      -- `eval (map⁺ (trans (↭-sym ρ) ρ)) ⟨$⟩ʳ i = e ⟨$⟩ʳ (eval(map⁺(↭-sym ρ)) ⟨$⟩ʳ i)`
      --   = e ⟨$⟩ʳ (inv-fb e ⟨$⟩ʳ i) = e ⟨$⟩ʳ (e ⟨$⟩ˡ i) = i  (P.inverseʳ).
      self-loop-id
        : eval-↭ (PermProp.map⁺ H.vlab (Perm.trans (Perm.↭-sym ρ) ρ)) ≈-fb id-fb
      self-loop-id i =
        trans (cong (e P.⟨$⟩ʳ_) (sym-eval i)) (P.inverseʳ e)

  ----------------------------------------------------------------------
  -- FIRING STABILITY under a stack permutation.
  --
  -- Given `ρ : s' ↭ s`, an edge fires on `s` iff it fires on `s'`, and
  -- the residual permutes.  Both directions are imported from
  -- `DecodeProperties` (`extract-prefix-↭-residual` / `-↭-nothing`).
  ----------------------------------------------------------------------

  -- If `e` fires on `s` with residual `restH`, it fires on `s'` with a
  -- residual `restH'` that `restH` permutes onto.
  fire-stable-just
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {restH : List (Fin H.nV)} (permH : s Perm.↭ H.ein e ++ restH)
    → extract-prefix (H.ein e) s ≡ just (restH , permH)
    → Σ[ restH' ∈ List (Fin H.nV) ]
      Σ[ permH' ∈ s' Perm.↭ H.ein e ++ restH' ]
        extract-prefix (H.ein e) s' ≡ just (restH' , permH')
        × restH Perm.↭ restH'
  fire-stable-just e {s} {s'} ρ {restH} permH eqH =
    let step = extract-prefix-↭-residual (H.ein e) s' restH
                 (Perm.↭-trans ρ permH)
    in proj₁ step , proj₁ (proj₂ step)
       , proj₁ (proj₂ (proj₂ step)) , proj₂ (proj₂ (proj₂ step))

  -- If `e` does not fire on `s`, it does not fire on `s'`.
  fire-stable-nothing
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → extract-prefix (H.ein e) s ≡ nothing
    → extract-prefix (H.ein e) s' ≡ nothing
  fire-stable-nothing e {s} {s'} ρ eqH =
    extract-prefix-↭-nothing (H.ein e) s s' (Perm.↭-sym ρ) eqH

  ----------------------------------------------------------------------
  -- RESIDUAL 1 — FIRE box naturality under a residual permutation.
  --
  -- The FIRE "box" `fire-mid e rest` is `(Agen-edge e ⊗ id_rest)` framed
  -- by `unflatten-++-≅` coercions.  It depends on `rest` ONLY through the
  -- `id`-on-`rest` block, so permuting the residual commutes with the box:
  --
  --   fire-mid e restH'
  --     ≈Term  permute-via-vlab vlab (++⁺ˡ (eout e) μ)
  --              ∘ fire-mid e restH
  --              ∘ permute-via-vlab vlab (++⁺ˡ (ein e) (↭-sym μ))
  --
  -- for `μ : restH ↭ restH'`  (the input permute maps `ein e ++ restH'`
  -- back to `ein e ++ restH`, the output permute maps `eout e ++ restH`
  -- forward to `eout e ++ restH'`).  TRUE by the interchange law on
  -- `(Agen-edge e) ⊗ (permute μ)` (the box is identity on the `id`-block,
  -- so a permute of that block slides through), but the boundary
  -- `subst₂`/`unflatten-++-≅` bookkeeping makes the constructive chase
  -- long; isolated here as the box-naturality half.  No firing data,
  -- no `cod`.
  -- PROVEN (no longer a postulate): discharged by the standalone
  -- `Sub/FireMidEquivariant.agda` (box-naturality via `permute-++⁺ˡ-slide`
  -- + `⊗-∘-dist` + the K self-loop inverse).
  fire-mid-equivariant
      : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
          (μ : restH Perm.↭ restH')
      → fire-mid H e restH'
        ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) μ)
                ∘ ( fire-mid H e restH
                    ∘ permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)) )
  fire-mid-equivariant = FME.fire-mid-equivariant H K

  ----------------------------------------------------------------------
  -- RESIDUAL 2 — FIRE locating-permute coherence.
  --
  -- The two locating permutations (the one `extract-prefix` finds on `s'`
  -- pushed through the box-residual permute, vs. the one found on `s`
  -- precomposed with ρ) realise the SAME bijection after vertex
  -- labelling — i.e. they are `≅↭`-equal — so K reconciles their
  -- `permute`s.  This is the identity-relabel / stack-permute analogue of
  -- `ExtractPrefixEvalPhi.eval-coincide` (which proves it for a φ-relabel
  -- with NO stack permute).  TRUE because `extract-prefix` locates the
  -- same multiset-prefix canonically; isolated here as the locating
  -- coherence (no box, no `cod`).
  postulate
    fire-locate-coherent
      : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
          {restH restH' : List (Fin H.nV)}
          (permH  : s  Perm.↭ H.ein e ++ restH)
          (permH' : s' Perm.↭ H.ein e ++ restH')
          (μ : restH Perm.↭ restH')
      → PermProp.map⁺ H.vlab (Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)))
        ≅↭ PermProp.map⁺ H.vlab (Perm.trans ρ permH)

  ----------------------------------------------------------------------
  -- FIRE/FIRE term equivariance — assembled from Residuals 1 & 2 + K.
  -- The output factor is `permute (++⁺ˡ (eout e) μ)`, i.e. the forward
  -- output permutation `eout e ++ restH ↭ eout e ++ restH'`.
  ----------------------------------------------------------------------

  edge-step-fire-equivariant
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {restH restH' : List (Fin H.nV)}
        (permH  : s  Perm.↭ H.ein e ++ restH)
        (permH' : s' Perm.↭ H.ein e ++ restH')
        (μ : restH Perm.↭ restH')
    → fire-term H e s' restH' permH'
      ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) μ)
              ∘ ( fire-term H e s restH permH
                  ∘ permute-via-vlab H.vlab ρ )
  edge-step-fire-equivariant e {s} {s'} ρ {restH} {restH'} permH permH' μ =
    -- fire-term e s' restH' permH' = fire-mid e restH' ∘ permute permH'
    --   ≈ (permute(++eoutμ) ∘ fire-mid e restH ∘ permute μ_in) ∘ permute permH'  [R1]
    --   ≈ permute(++eoutμ) ∘ fire-mid e restH ∘ (permute μ_in ∘ permute permH')  [assoc]
    --   = permute(++eoutμ) ∘ fire-mid e restH ∘ permute (trans permH' μ_in)
    --   ≈ permute(++eoutμ) ∘ fire-mid e restH ∘ permute (trans ρ permH)          [R2 + K]
    --   = permute(++eoutμ) ∘ fire-mid e restH ∘ (permute permH ∘ permute ρ)
    --   = permute(++eoutμ) ∘ (fire-mid e restH ∘ permute permH) ∘ permute ρ
    --   = permute(++eoutμ) ∘ fire-term e s restH permH ∘ permute ρ
    ≈-Term-trans
      (∘-resp-≈ (fire-mid-equivariant e μ) ≈-Term-refl)
      (≈-Term-trans assoc
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl assoc)
          (∘-resp-≈ ≈-Term-refl
            (≈-Term-trans
              (∘-resp-≈ ≈-Term-refl perm-reconcile)
              (≈-Term-sym assoc)))))
    where
      μ-in  = PermProp.++⁺ˡ (H.ein  e) (Perm.↭-sym μ)

      -- `permute μ_in ∘ permute permH' = permute (trans permH' μ_in)`
      --   ≈ permute (trans ρ permH) = permute permH ∘ permute ρ        [R2 + K]
      perm-reconcile
        : permute-via-vlab H.vlab μ-in ∘ permute-via-vlab H.vlab permH'
          ≈Term permute-via-vlab H.vlab permH ∘ permute-via-vlab H.vlab ρ
      perm-reconcile =
        ≈-Term-trans (≈-Term-sym (pvv-trans permH' μ-in))
          (≈-Term-trans
            (permute-resp-≅↭
              (PermProp.map⁺ H.vlab (Perm.trans permH' μ-in))
              (PermProp.map⁺ H.vlab (Perm.trans ρ permH))
              (fire-locate-coherent e ρ permH permH' μ))
            (pvv-trans ρ permH))

  ----------------------------------------------------------------------
  -- PER-EDGE-STEP equivariance, over the `EdgeStepR` witnesses.
  --
  -- Given `ρ : s' ↭ s` and the two edge-step relations (on `s`, on `s'`),
  -- the two output stacks `s'H` (from `s`) and `s'H'` (from `s'`) carry an
  -- induced permutation `ρf : s'H' ↭ s'H`, and the two step terms relate by
  -- the equivariance sandwich.  Bundled as an existential over `ρf`.
  ----------------------------------------------------------------------

  edge-step-equivariant
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {s'H : List (Fin H.nV)}
        {tH : HomTerm (unflatten (map H.vlab s)) (unflatten (map H.vlab s'H))}
        {s'H' : List (Fin H.nV)}
        {tH' : HomTerm (unflatten (map H.vlab s')) (unflatten (map H.vlab s'H'))}
        (wH  : EdgeStepR H s  e s'H  tH)
        (wH' : EdgeStepR H s' e s'H' tH')
    → Σ[ ρf ∈ s'H' Perm.↭ s'H ]
        tH' ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                    ∘ ( tH ∘ permute-via-vlab H.vlab ρ )
  -- SKIP/SKIP: both terms are id, output stacks are s'/s, ρf = ρ.
  edge-step-equivariant e ρ (skipR eqH) (skipR eqH') =
    ρ , ≈-Term-sym
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                        (pvv-inverse-left ρ))
  -- SKIP/FIRE & FIRE/SKIP: impossible by firing stability.
  edge-step-equivariant e ρ (skipR eqH) (fireR restH' permH' eqH') =
    ⊥-elim (just≢nothing (trans (sym eqH') (fire-stable-nothing e ρ eqH)))
  edge-step-equivariant e {s} {s'} ρ (fireR restH permH eqH) (skipR eqH') =
    ⊥-elim (just≢nothing
      (let st = fire-stable-just e ρ permH eqH
       in trans (sym (proj₁ (proj₂ (proj₂ st)))) eqH'-as))
    where
      -- `fire-stable-just` says `e` fires on `s'`, contradicting `eqH'`.
      -- Re-expose `eqH'` after noting the residual that fires.
      eqH'-as : extract-prefix (H.ein e) s' ≡ nothing
      eqH'-as = eqH'
  -- FIRE/FIRE: the substantive case.  The residual from `s` permutes onto
  -- the residual from `s'` (`fire-stable-just`); but the residual `wH'`
  -- carries (`restH'`,`permH'`) may differ from the one `fire-stable-just`
  -- found — they agree by `extract-prefix` determinism (`just`-injective).
  edge-step-equivariant e {s} {s'} ρ
      (fireR restH permH eqH) (fireR restH' permH' eqH') =
        PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym μ)
      , subst (λ z → fire-term H e s' restH' permH'
                       ≈Term permute-via-vlab H.vlab z
                               ∘ ( fire-term H e s restH permH
                                   ∘ permute-via-vlab H.vlab ρ ))
              -- `↭-sym (++⁺ˡ (eout e) (↭-sym μ)) ≡ ++⁺ˡ (eout e) μ`.
              (sym (trans (++⁺ˡ-↭-sym (H.eout e) (Perm.↭-sym μ))
                          (cong (PermProp.++⁺ˡ (H.eout e))
                                (PermProp.↭-sym-involutive μ))))
              (edge-step-fire-equivariant e ρ permH permH' μ)
    where
      -- `μ : restH ↭ restH'`, recovered from `fire-stable-just` (whose
      -- found residual is `restH'` by `extract-prefix` determinism).
      st = fire-stable-just e ρ permH eqH
      restH'≡ : proj₁ st ≡ restH'
      restH'≡ = just-injective-fst
                  (trans (sym (proj₁ (proj₂ (proj₂ st)))) eqH')
      μ : restH Perm.↭ restH'
      μ = subst (restH Perm.↭_) restH'≡ (proj₂ (proj₂ (proj₂ st)))

  ----------------------------------------------------------------------
  -- MAIN THEOREM — `process-edges-equivariant`.
  --
  -- For an edge list `qs`, stacks `s s'`, and `ρ : s' ↭ s`, there is an
  -- induced output permutation `ρf : pe-stack qs s' ↭ pe-stack qs s` with
  --
  --   pe-term qs s'
  --     ≈Term permute-via-vlab vlab (↭-sym ρf)
  --             ∘ ( pe-term qs s ∘ permute-via-vlab vlab ρ ).
  --
  -- Induction on `qs`.  Empty: ρf = ρ, terms are id, inverse-left closes.
  -- Cons: one `edge-step-equivariant` (over the `EdgeStepR` graph view) on
  -- the head edge gives the per-step ρ1 + term relation; recurse on the
  -- tail with ρ1; compose the two sandwiches (the middle permutes telescope
  -- through `pvv-trans`-style ∘-reassociation, leaving the outer input
  -- permute `ρ` and output permute `↭-sym ρf` intact).
  ----------------------------------------------------------------------

  process-edges-equivariant
    : ∀ (qs : List (Fin H.nE)) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → Σ[ ρf ∈ pe-stack qs s' Perm.↭ pe-stack qs s ]
        pe-term qs s'
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ ( pe-term qs s ∘ permute-via-vlab H.vlab ρ )
  -- Empty list: pe-term [] s = id, pe-stack [] s = s, ρf = ρ.
  process-edges-equivariant [] {s} {s'} ρ =
    ρ , ≈-Term-sym
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                        (pvv-inverse-left ρ))
  process-edges-equivariant (e ∷ qs) {s} {s'} ρ
      with edge-step-graph H s e | edge-step-graph H s' e
  ... | wH | wH'
      with edge-step-equivariant e ρ wH wH'
  ... | ρ1 , step-eq
      with process-edges-equivariant qs ρ1
  ... | ρf , tail-eq =
        ρf , goal
    where
      -- After running edge `e`: stacks `s1 = proj₁ (edge-step H s e)`,
      -- `s1' = proj₁ (edge-step H s' e)`, with `ρ1 : s1' ↭ s1`.
      s1  = proj₁ (edge-step H s  e)
      s1' = proj₁ (edge-step H s' e)
      tH  = proj₂ (edge-step H s  e)
      tH' = proj₂ (edge-step H s' e)

      -- `pe-term (e ∷ qs) s = pe-term qs s1 ∘ tH` (definitional).
      -- LHS:  pe-term qs s1' ∘ tH'
      --   ≈ (permute(↭-sym ρf) ∘ pe-term qs s1 ∘ permute ρ1) ∘ tH'      [tail-eq]
      --   ≈ permute(↭-sym ρf) ∘ pe-term qs s1 ∘ (permute ρ1 ∘ tH')      [assoc]
      -- and  step-eq : tH' ≈ permute(↭-sym ρ1) ∘ (tH ∘ permute ρ), so
      --   permute ρ1 ∘ tH' ≈ permute ρ1 ∘ permute(↭-sym ρ1) ∘ (tH ∘ permute ρ)
      --                    ≈ tH ∘ permute ρ                              [pvv-inv-right]
      --   ⇒ permute(↭-sym ρf) ∘ pe-term qs s1 ∘ (tH ∘ permute ρ)
      --   = permute(↭-sym ρf) ∘ (pe-term qs s1 ∘ tH) ∘ permute ρ
      --   = permute(↭-sym ρf) ∘ (pe-term (e ∷ qs) s) ∘ permute ρ.
      goal
        : pe-term (e ∷ qs) s'
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ ( pe-term (e ∷ qs) s ∘ permute-via-vlab H.vlab ρ )
      goal =
        ≈-Term-trans
          (∘-resp-≈ tail-eq ≈-Term-refl)
          (≈-Term-trans assoc
            (≈-Term-trans
              (∘-resp-≈ ≈-Term-refl assoc)
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans
                  (∘-resp-≈ ≈-Term-refl mid-collapse)
                  (≈-Term-sym assoc)))))
        where
          -- `permute ρ1 ∘ tH' ≈ tH ∘ permute ρ`.
          mid-collapse
            : permute-via-vlab H.vlab ρ1 ∘ tH'
              ≈Term tH ∘ permute-via-vlab H.vlab ρ
          mid-collapse =
            ≈-Term-trans (∘-resp-≈ ≈-Term-refl step-eq)
              (≈-Term-trans (≈-Term-sym assoc)
                (≈-Term-trans
                  (∘-resp-≈ (pvv-inverse-right ρ1) ≈-Term-refl)
                  idˡ))

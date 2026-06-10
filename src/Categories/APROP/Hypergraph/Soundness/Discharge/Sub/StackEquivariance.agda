{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Decoder STACK-EQUIVARIANCE.
--
-- Running the decoder's `process-edges` on a *permuted* input stack equals
-- running it on the original stack, sandwiched between an input-permute
-- (precompose) and an output-permute (postcompose).  This lets the per-swap
-- interchange `run-eq` of `SwapStep.agda` be reduced from an arbitrary tail
-- to the empty-tail two-edge core: equivariance strips a permutation of the
-- running stack and re-attaches it as `permute`s on the boundary.
--
-- Generator-OPAQUE — only permute/permutation-coherence bookkeeping and
-- firing-stability, no generator box content.  Proven by induction on the
-- edge list, over the `EdgeStepR` relation view (`EdgeStepRelation.agda`) to
-- dodge the green-slime `with`-abstraction wall.
--
-- ## Statement (`process-edges-equivariant`)
--
-- For an edge list `qs`, stacks `s s'`, and `ρ : s' ↭ s`, there is an
-- induced output permutation `ρ_f : pe-stack qs s' ↭ pe-stack qs s` with
--
--   pe-term qs s'
--     ≈Term  permute-via-vlab vlab (↭-sym ρ_f)
--              ∘ pe-term qs s ∘ permute-via-vlab vlab ρ.
--
-- ## Structure
--
--   * `fire-mid-equivariant` — the per-edge FIRE box is natural in its
--     residual stack under a permutation of that residual.  Delegated to
--     `Sub/FireMidEquivariant.agda`.
--
--   * `residual-recon` reconciles the `extract-prefix-↭-residual` output
--     against the input perm, as a `≅↭`.  It delegates to
--     `StackUnique.residual-recon` (= `eval-rigid` on a `Unique` codomain),
--     which needs `Unique (ks ++ rest)`.  At the FIRE/FIRE call site that
--     codomain is the `↭`-image of the decoder stack `s'`, so `Unique s'`
--     (via `Unique-resp-↭`) supplies it.
--
-- The only HYPOTHESIS the recursion carries is `Reservoir≤1`-freshness on
-- `process-edges-equivariant` (giving `Unique s'` at every stage), which
-- the caller must source.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackEquivariance
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-edges; edge-step; extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Soundness.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; edge-step-graph; edge-step-sound)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using (just≢nothing)
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidEquivariant sig as FME
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual; permute-self-loop-id-wide)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; inv-fb; _∘-fb_; cons-fb; swap-fb; ≈-fb-trans)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (eval-↭-sym)

open import Data.Fin using (Fin)
open import Data.Nat.Base using (suc)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Categories.PermuteCoherence.Map using (eval-map⁺; subst₂-FinBij-≈)

--------------------------------------------------------------------------------
-- ≈Term plumbing.

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
  -- `permute-via-vlab` algebra.  `permute-via-vlab vlab p = permute (map⁺
  -- vlab p)`, `permute (trans p q) = permute q ∘ permute p`, and `map⁺ vlab
  -- (trans p q) = trans (map⁺ vlab p) (map⁺ vlab q)`, all definitional.
  ----------------------------------------------------------------------

  -- `permute-via-vlab` of a `trans` splits as a ∘ (postcompose the first).
  pvv-trans
    : ∀ {xs ys zs : List (Fin H.nV)} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → permute-via-vlab H.vlab (Perm.trans p q)
      ≈Term permute-via-vlab H.vlab q ∘ permute-via-vlab H.vlab p
  pvv-trans p q = ≈-Term-refl

  -- `map⁺` commutes with `↭-sym` propositionally.  Induction on ρ; no K.
  map⁺-↭-sym
    : ∀ {A B : Set} (f : A → B) {xs ys : List A} (ρ : xs Perm.↭ ys)
    → PermProp.map⁺ f (Perm.↭-sym ρ) ≡ Perm.↭-sym (PermProp.map⁺ f ρ)
  map⁺-↭-sym f Perm.refl          = refl
  map⁺-↭-sym f (Perm.prep x ρ)    = cong (Perm.prep _) (map⁺-↭-sym f ρ)
  map⁺-↭-sym f (Perm.swap x y ρ)  = cong (Perm.swap _ _) (map⁺-↭-sym f ρ)
  map⁺-↭-sym f (Perm.trans p q)   =
    cong₂ Perm.trans (map⁺-↭-sym f q) (map⁺-↭-sym f p)

  -- `↭-sym` commutes through `++⁺ˡ`.  Induction on `xs`.
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
      e : FinBij _ _
      e = eval-↭ (PermProp.map⁺ H.vlab ρ)

      -- `eval (map⁺ vlab (↭-sym ρ)) ≈-fb inv-fb e` by `map⁺-↭-sym` + `eval-↭-sym`.
      sym-eval : eval-↭ (PermProp.map⁺ H.vlab (Perm.↭-sym ρ)) ≈-fb inv-fb e
      sym-eval = subst (λ z → eval-↭ z ≈-fb inv-fb e)
                       (sym (map⁺-↭-sym H.vlab ρ))
                       (eval-↭-sym (PermProp.map⁺ H.vlab ρ))

      -- `inv-fb e ⟨$⟩ʳ (e ⟨$⟩ʳ i) = i` by `P.inverseˡ`.
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

      -- `e ⟨$⟩ʳ (inv-fb e ⟨$⟩ʳ i) = i` by `P.inverseʳ`.
      self-loop-id
        : eval-↭ (PermProp.map⁺ H.vlab (Perm.trans (Perm.↭-sym ρ) ρ)) ≈-fb id-fb
      self-loop-id i =
        trans (cong (e P.⟨$⟩ʳ_) (sym-eval i)) (P.inverseʳ e)

  ----------------------------------------------------------------------
  -- FIRING STABILITY under a stack permutation.  Given `ρ : s' ↭ s`, an
  -- edge fires on `s` iff it fires on `s'`, and the residual permutes.
  -- Both directions from `DecodeProperties`.
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
  -- `id`-on-`rest` block, so permuting the residual slides through the box:
  --
  --   fire-mid e restH'
  --     ≈Term  permute-via-vlab vlab (++⁺ˡ (eout e) μ)
  --              ∘ fire-mid e restH
  --              ∘ permute-via-vlab vlab (++⁺ˡ (ein e) (↭-sym μ))
  --
  -- for `μ : restH ↭ restH'`.  Delegated to `Sub/FireMidEquivariant.agda`.
  fire-mid-equivariant
      : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
          (μ : restH Perm.↭ restH')
      → fire-mid H e restH'
        ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) μ)
                ∘ ( fire-mid H e restH
                    ∘ permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)) )
  fire-mid-equivariant = FME.fire-mid-equivariant H K

  ----------------------------------------------------------------------
  -- RESIDUAL 2 — FIRE locating-permute coherence (CANONICAL residual).
  --
  -- The two locating permutations realise the SAME multiset prefix
  -- CANONICALLY, so they coincide as vertex `↭`-derivations up to `≅↭`.
  --
  -- CAVEAT: the unconstrained four-permutation form is FALSE (a free
  -- `μ = swap` on a repeated-vertex residual `[v,v]` is a machine-checked
  -- counterexample).  Hence the CANONICAL form below: `residual-recon`
  -- reconciles the SINGLE `extract-prefix-↭-residual` output (exactly what
  -- `edge-step-graph` returns at the call site) against the input perm,
  -- re-attaching the residual reshuffle on the `rest` block:
  --
  --   trans (located) (++⁺ˡ ks (↭-sym residual-↭))  ≅↭  perm-in
  --
  -- Provable unconditionally only in the empty-prefix base case; the cons
  -- case reduces to `drop-∷` eval-faithfulness, hence the `Unique`
  -- hypothesis (closed by `eval-rigid`).  Delegates to
  -- `StackUnique.residual-recon`; the codomain `Unique (ks ++ rest)` is
  -- supplied at the call site as `Unique-resp-↭ perm-in (Unique s')`.
  residual-recon
    : ∀ {n} (ks xs rest : List (Fin n)) (perm-in : xs Perm.↭ ks ++ rest)
    → Unique (ks ++ rest)
    → let st = extract-prefix-↭-residual ks xs rest perm-in in
      Perm.trans (proj₁ (proj₂ st))
                 (PermProp.++⁺ˡ ks (Perm.↭-sym (proj₂ (proj₂ (proj₂ st)))))
      ≅↭ perm-in
  residual-recon = SU.residual-recon

  ----------------------------------------------------------------------
  -- map⁺ LIFT — vertex-level `≅↭` → X-level `≅↭` through `map⁺ vlab`, via
  -- `eval-map⁺` + `subst₂-FinBij-≈` (J-only).
  ----------------------------------------------------------------------
  map⁺-lift-≅↭
    : ∀ {xs ys : List (Fin H.nV)} (p q : xs Perm.↭ ys)
    → p ≅↭ q
    → PermProp.map⁺ H.vlab p ≅↭ PermProp.map⁺ H.vlab q
  map⁺-lift-≅↭ {xs} {ys} p q p≅q =
    subst (λ z → z ≈-fb eval-↭ (PermProp.map⁺ H.vlab q))
          (sym (eval-map⁺ H.vlab p))
      (subst (λ z → subst₂ FinBij (sym (length-map H.vlab xs))
                                  (sym (length-map H.vlab ys)) (eval-↭ p)
                    ≈-fb z)
             (sym (eval-map⁺ H.vlab q))
        (subst₂-FinBij-≈ (sym (length-map H.vlab xs))
                         (sym (length-map H.vlab ys)) p≅q))

  ----------------------------------------------------------------------
  -- CANONICAL residual reshuffle `fire-μ` — the SINGLE source of the
  -- FIRE residual permutation, shared by `edge-step-fire-equivariant`
  -- and `edge-step-equivariant`'s output witness.  Uses the RAW
  -- `Perm.trans ρ permH` as the input perm so the `residual-recon`
  -- reconciliation lands exactly where the goal's right-hand factor needs.
  -- The residual list it locates is `restH'` by `extract-prefix`
  -- determinism (`eqH'`).
  ----------------------------------------------------------------------
  module _ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
           {restH restH' : List (Fin H.nV)}
           (permH  : s  Perm.↭ H.ein e ++ restH)
           (permH' : s' Perm.↭ H.ein e ++ restH')
           (eqH' : extract-prefix (H.ein e) s' ≡ just (restH' , permH'))
           (us' : Unique s')
           where
    private
      -- The canonical `extract-prefix-↭-residual` output on the RAW
      -- `Perm.trans ρ permH` — `residual-recon` is stated for exactly this.
      st = extract-prefix-↭-residual (H.ein e) s' restH (Perm.trans ρ permH)
      restHc  = proj₁ st
      permHc  = proj₁ (proj₂ st)
      eqHc    = proj₁ (proj₂ (proj₂ st))   -- extract-prefix … ≡ just (restHc , permHc)
      rpc     = proj₂ (proj₂ (proj₂ st))   -- restH ↭ restHc

      -- The canonical Σ-pair IS the call-site one (determinism).
      pair-eq : (restHc , permHc) ≡ (restH' , permH')
      pair-eq = just-injective (trans (sym eqHc) eqH')

      restHc≡ : restHc ≡ restH'
      restHc≡ = cong proj₁ pair-eq

    -- The residual reshuffle, transported onto `restH'`.
    fire-μ : restH Perm.↭ restH'
    fire-μ = subst (restH Perm.↭_) restHc≡ rpc

    ------------------------------------------------------------------
    -- LOCATING-PERMUTE COHERENCE — the X-level `≅↭` that
    -- `permute-resp-≅↭` consumes, derived from `residual-recon`.
    -- `residual-recon` gives the vertex-level `≅↭`; the determinism
    -- transport `restHc≡` identifies `(restHc, permHc, rpc)` with
    -- `(restH', permH', fire-μ)`, and `map⁺-lift-≅↭` lifts it through
    -- `map⁺ vlab`.
    ------------------------------------------------------------------
    private
      -- The call-site `permH'`/`fire-μ` ARE the canonical `permHc`/`rpc`
      -- after the `restHc≡` transport (matched at `refl`).
      recon-collapse
        : ∀ {rc} (pc : s' Perm.↭ H.ein e ++ rc) (rp : restH Perm.↭ rc)
            (req : rc ≡ restH')
            (peq : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) req pc)
        → Perm.trans permH'
            (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym (subst (restH Perm.↭_) req rp)))
          ≅↭ Perm.trans pc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rp))
      recon-collapse pc rp refl refl i = refl

      -- `permH'`-determinism in `subst` form (`req = restHc≡ = cong proj₁ pair-eq`).
      permHc≡ : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) restHc≡ permHc
      permHc≡ = sym (subst-pair-snd pair-eq)
        where
          -- `proj₂` of a transported Σ-pair, generalised then matched at refl.
          subst-pair-snd
            : ∀ {rc : List (Fin H.nV)} {pc : s' Perm.↭ H.ein e ++ rc}
                (pe : (rc , pc) ≡ (restH' , permH'))
            → subst (λ r → s' Perm.↭ H.ein e ++ r) (cong proj₁ pe) pc ≡ permH'
          subst-pair-snd refl = refl

    locate-coherent
      : PermProp.map⁺ H.vlab
          (Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)))
        ≅↭ PermProp.map⁺ H.vlab (Perm.trans ρ permH)
    locate-coherent =
      map⁺-lift-≅↭
        (Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)))
        (Perm.trans ρ permH)
        chained
      where
        -- The shared middle derivation, named to pin `≈-fb-trans`'s `ρ`.
        mid : s' Perm.↭ H.ein e ++ restH
        mid = Perm.trans permHc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rpc))

        half₁ : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
                ≅↭ mid
        half₁ = recon-collapse permHc rpc restHc≡ permHc≡

        half₂ : mid ≅↭ Perm.trans ρ permH
        half₂ = residual-recon (H.ein e) s' restH (Perm.trans ρ permH)
                  (SU.Unique-resp-↭ (Perm.trans ρ permH) us')

        chained
          : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
            ≅↭ Perm.trans ρ permH
        chained i = trans (half₁ i) (half₂ i)

  ----------------------------------------------------------------------
  -- FIRE/FIRE term equivariance — assembled from Residuals 1 & 2 + K.
  -- The output factor is `permute (++⁺ˡ (eout e) μ)`, the forward output
  -- permutation `eout e ++ restH ↭ eout e ++ restH'`, with `μ = fire-μ …`
  -- the canonical residual reshuffle and `locate-coherent` the coherence.
  ----------------------------------------------------------------------

  edge-step-fire-equivariant
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {restH restH' : List (Fin H.nV)}
        (permH  : s  Perm.↭ H.ein e ++ restH)
        (permH' : s' Perm.↭ H.ein e ++ restH')
        (eqH' : extract-prefix (H.ein e) s' ≡ just (restH' , permH'))
        (us' : Unique s')
    → fire-term H e s' restH' permH'
      ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) (fire-μ e ρ permH permH' eqH' us'))
              ∘ ( fire-term H e s restH permH
                  ∘ permute-via-vlab H.vlab ρ )
  edge-step-fire-equivariant e {s} {s'} ρ {restH} {restH'} permH permH' eqH' us' =
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
      μ     = fire-μ e ρ permH permH' eqH' us'
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
              (locate-coherent e ρ permH permH' eqH' us'))
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
        (us' : Unique s')
    → Σ[ ρf ∈ s'H' Perm.↭ s'H ]
        tH' ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                    ∘ ( tH ∘ permute-via-vlab H.vlab ρ )
  -- SKIP/SKIP: both terms are id, output stacks are s'/s, ρf = ρ.
  edge-step-equivariant e ρ (skipR eqH) (skipR eqH') us' =
    ρ , ≈-Term-sym
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                        (pvv-inverse-left ρ))
  -- SKIP/FIRE & FIRE/SKIP: impossible by firing stability.
  edge-step-equivariant e ρ (skipR eqH) (fireR restH' permH' eqH') us' =
    ⊥-elim (just≢nothing (trans (sym eqH') (fire-stable-nothing e ρ eqH)))
  edge-step-equivariant e {s} {s'} ρ (fireR restH permH eqH) (skipR eqH') us' =
    ⊥-elim (just≢nothing
      (let st = fire-stable-just e ρ permH eqH
       in trans (sym (proj₁ (proj₂ (proj₂ st)))) eqH'-as))
    where
      eqH'-as : extract-prefix (H.ein e) s' ≡ nothing
      eqH'-as = eqH'
  -- FIRE/FIRE: the substantive case.  The residual from `s` permutes onto
  -- the residual from `s'` (`fire-μ`, the canonical reshuffle); the located
  -- pair agrees with the canonical one by `extract-prefix` determinism.
  edge-step-equivariant e {s} {s'} ρ
      (fireR restH permH eqH) (fireR restH' permH' eqH') us' =
        PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym μ)
      , subst (λ z → fire-term H e s' restH' permH'
                       ≈Term permute-via-vlab H.vlab z
                               ∘ ( fire-term H e s restH permH
                                   ∘ permute-via-vlab H.vlab ρ ))
              -- `↭-sym (++⁺ˡ (eout e) (↭-sym μ)) ≡ ++⁺ˡ (eout e) μ`.
              (sym (trans (++⁺ˡ-↭-sym (H.eout e) (Perm.↭-sym μ))
                          (cong (PermProp.++⁺ˡ (H.eout e))
                                (PermProp.↭-sym-involutive μ))))
              (edge-step-fire-equivariant e ρ permH permH' eqH' us')
    where
      μ : restH Perm.↭ restH'
      μ = fire-μ e ρ permH permH' eqH' us'

  ----------------------------------------------------------------------
  -- MAIN THEOREM — `process-edges-equivariant`.
  --
  -- Induction on `qs`.  Empty: ρf = ρ, terms are id, inverse-left closes.
  -- Cons: one `edge-step-equivariant` on the head edge gives the per-step
  -- ρ1 + term relation; recurse on the tail with ρ1; compose the two
  -- sandwiches (the middle permutes telescope through ∘-reassociation,
  -- leaving the outer `ρ` / `↭-sym ρf` intact).
  --
  -- The `Reservoir≤1` freshness invariant on the PERMUTED stack `s'` is
  -- advanced one `edge-step` per recursion (so each `s'` is `Unique`); the
  -- `Linear H`-sourced GLOBAL reservoir is supplied by the caller.
  ----------------------------------------------------------------------
  process-edges-equivariant
    : ∀ (qs : List (Fin H.nE)) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → SUR.Reservoir≤1 H qs s'
    → Σ[ ρf ∈ pe-stack qs s' Perm.↭ pe-stack qs s ]
        pe-term qs s'
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ ( pe-term qs s ∘ permute-via-vlab H.vlab ρ )
  -- Empty list: pe-term [] s = id, pe-stack [] s = s, ρf = ρ.
  process-edges-equivariant [] {s} {s'} ρ _ =
    ρ , ≈-Term-sym
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                        (pvv-inverse-left ρ))
  process-edges-equivariant (e ∷ qs) {s} {s'} ρ inv
      with edge-step-graph H s e | edge-step-graph H s' e
  ... | wH | wH'
      with edge-step-equivariant e ρ wH wH'
              (SUR.Reservoir≤1⇒Unique H (e ∷ qs) s' inv)
  ... | ρ1 , step-eq
      with process-edges-equivariant qs ρ1
             (SUR.edge-step-Reservoir≤1 H e qs s' inv)
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

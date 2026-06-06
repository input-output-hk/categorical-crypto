{-# OPTIONS --safe --with-K #-}

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
-- ## Structure
--
-- The induction, the SKIP and impossible cross-cases, the list-level
-- threading, the inverse/self-loop permute facts (via the Kelly residual
-- `K : FaithfulnessResidual`), the FIRE-box naturality, and the FIRE-permute
-- reconciliation (via K) are POSTULATE-FREE here:
--
--   * `fire-mid-equivariant` — the per-edge FIRE box is natural in its
--     residual stack under a *permutation* of that residual.  Discharged by
--     the standalone `Sub/FireMidEquivariant.agda`.
--
--   * `residual-recon` reconciles the `extract-prefix-↭-residual` output
--     (the located perm `proj₁ (proj₂ st)` re-attached to the residual
--     reshuffle on the `rest` block) against the input perm, as a `≅↭`:
--       `trans (located) (++⁺ˡ ks (↭-sym residual-↭)) ≅↭ perm-in`.
--     It DELEGATES to `StackUnique.residual-recon` (= `eval-rigid` on a
--     `Unique` codomain), which needs `Unique (ks ++ rest)`.  At the FIRE/FIRE
--     call site (`locate-coherent`) that codomain `ein e ++ restH` is the
--     `↭`-image of the decoder stack `s'`, so `Unique s' →` (via
--     `Unique-resp-↭`) supplies it.  `Unique s'` is THREADED through
--     `process-edges-equivariant` as the `Reservoir≤1`-freshness invariant
--     (advanced one `edge-step` per recursion via
--     `StackUniqueReach.edge-step-Reservoir≤1`); the caller
--     `RunInterchangeTail` sources the GLOBAL reservoir from `Linear H`.
--
-- The only residual this module's recursion now carries is the
-- `Reservoir≤1`-freshness HYPOTHESIS on `process-edges-equivariant`, which
-- the caller must source (TRUE for the permutation-of-`range` orders the
-- downstream `swap-≈` consumes; see `RunInterchangeTail.dom-reservoir`).
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
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig as SU

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual; permute-self-loop-id-wide)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; inv-fb; _∘-fb_; cons-fb; swap-fb)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (≈-fb-trans; eval-↭-sym)

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

  ----------------------------------------------------------------------
  -- `eval-map⁺` and its `subst₂`-on-FinBij algebra (copies of the
  -- `SwapStep.agda` private helpers / `PermuteCoherence.Map` lemmas;
  -- all J-only, no K).  Used to LIFT a vertex-level `≅↭` (from
  -- `residual-recon`) through `map⁺ vlab` to the X-level `≅↭` that
  -- `permute-resp-≅↭` consumes — the `SwapStep.permute-bridge-≅↭`
  -- pattern, minus the `eval-rigid` step (we already HAVE the ≅↭).
  ----------------------------------------------------------------------

  subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
  subst₂-FinBij-id refl = refl

  cons-cast
    : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
    → cons-fb (subst₂ FinBij (sym ex) (sym ey) π)
      ≡ subst₂ FinBij (sym (cong suc ex)) (sym (cong suc ey)) (cons-fb π)
  cons-cast refl refl π = refl

  swap-cast
    : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
    → swap-fb m' ∘-fb cons-fb (cons-fb (subst₂ FinBij (sym ex) (sym ey) π))
      ≡ subst₂ FinBij (sym (cong suc (cong suc ex)))
                      (sym (cong suc (cong suc ey)))
                      (swap-fb m ∘-fb cons-fb (cons-fb π))
  swap-cast refl refl π = refl

  comp-cast
    : ∀ {n n' m m' k k'}
        (ex : n' ≡ n) (ey : m' ≡ m) (ez : k' ≡ k)
        (g : FinBij m k) (f : FinBij n m)
    → subst₂ FinBij (sym ey) (sym ez) g ∘-fb subst₂ FinBij (sym ex) (sym ey) f
      ≡ subst₂ FinBij (sym ex) (sym ez) (g ∘-fb f)
  comp-cast refl refl refl g f = refl

  eval-map⁺ : ∀ {A C : Set}
    (h : A → C) {xs ys : List A} (p : xs Perm.↭ ys)
    → eval-↭ (PermProp.map⁺ h p)
      ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
  eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
  eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
    trans (cong cons-fb (eval-map⁺ h p))
          (cons-cast (length-map h xs) (length-map h ys) (eval-↭ p))
  eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
    trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
          (swap-cast (length-map h xs) (length-map h ys) (eval-↭ p))
  eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
    trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
          (comp-cast (length-map h xs) (length-map h ys) (length-map h zs)
                     (eval-↭ q) (eval-↭ p))

  subst₂-FinBij-≈ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') {π ρ : FinBij n m}
    → π ≈-fb ρ → subst₂ FinBij a b π ≈-fb subst₂ FinBij a b ρ
  subst₂-FinBij-≈ refl refl eq = eq

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
  -- Discharged by the standalone `Sub/FireMidEquivariant.agda`
  -- (box-naturality via `permute-++⁺ˡ-slide` + `⊗-∘-dist` + the K self-loop
  -- inverse).
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
  -- The two locating permutations (the one `extract-prefix` finds on `s'`
  -- pushed through the box-residual permute, vs. the one found on `s`
  -- precomposed with ρ) realise the SAME multiset prefix CANONICALLY, so
  -- they coincide as vertex `↭`-derivations up to `≅↭`.
  --
  -- The previous `fire-locate-coherent` postulate was FALSE as stated: it
  -- took FOUR UNCONSTRAINED permutations and asserted two separately-built
  -- bijections coincide (a free `μ = swap` on a repeated-vertex residual
  -- `[v,v]` is a machine-checked counterexample).  It is REPLACED by this
  -- TRUE, CANONICAL form: `residual-recon` reconciles the SINGLE
  -- `extract-prefix-↭-residual` output (which is exactly what
  -- `edge-step-graph` returns at the call site) against the input perm.
  --
  -- For `st = extract-prefix-↭-residual ks xs rest perm-in`, with
  -- `proj₁ (proj₂ st) : xs ↭ ks ++ rest'` the located perm and
  -- `proj₂ (proj₂ (proj₂ st)) : rest ↭ rest'` the residual reshuffle,
  -- re-attaching the residual reshuffle on the `rest` block recovers the
  -- input perm:
  --
  --   trans (located) (++⁺ˡ ks (↭-sym residual-↭))  ≅↭  perm-in
  --
  -- The unconditional form is provable only in the empty-prefix base case
  -- (`extract-prefix [] xs ≡ just (xs , refl)` makes `located = refl` and
  -- `residual-↭ = ↭-sym perm-in`, so the LHS is `trans refl (↭-sym (↭-sym
  -- perm-in)) ≅↭ perm-in` by `↭-sym-involutive` + eval); the cons case
  -- reduces to `drop-∷` eval-faithfulness, hence the `Unique` hypothesis.
  --
  -- soundness: `StackUnique.residual-recon` proves the EXACT conclusion
  -- below, modulo a `Unique (ks ++ rest)` hypothesis on the codomain (closed
  -- by `eval-rigid`).  This module THREADS a running-stack uniqueness
  -- witness `Unique s'` down to the FIRE/FIRE call site (via the
  -- `Reservoir≤1` freshness invariant carried through
  -- `process-edges-equivariant`, advanced by
  -- `StackUniqueReach.edge-step-Reservoir≤1`); the `Linear H`-sourced
  -- GLOBAL reservoir is supplied by the caller (`RunInterchangeTail`).
  -- `residual-recon` delegates to `StackUnique.residual-recon`, with the
  -- codomain `Unique (ks ++ rest)` supplied at the call site as
  -- `Unique-resp-↭ perm-in (Unique s')`.
  residual-recon
    : ∀ {n} (ks xs rest : List (Fin n)) (perm-in : xs Perm.↭ ks ++ rest)
    → Unique (ks ++ rest)
    → let st = extract-prefix-↭-residual ks xs rest perm-in in
      Perm.trans (proj₁ (proj₂ st))
                 (PermProp.++⁺ˡ ks (Perm.↭-sym (proj₂ (proj₂ (proj₂ st)))))
      ≅↭ perm-in
  residual-recon = SU.residual-recon

  ----------------------------------------------------------------------
  -- map⁺ LIFT — vertex-level `≅↭` → X-level `≅↭` through `map⁺ vlab`.
  --
  -- This is the `SwapStep.permute-bridge-≅↭` map-lift pattern, MINUS the
  -- `eval-rigid` step: we already HAVE the vertex-level `≅↭` (from
  -- `residual-recon`), so we only transport it through `map⁺ vlab` via
  -- `eval-map⁺` + `subst₂-FinBij-≈` (J-only, `--without-K`-clean).
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
  -- and `edge-step-equivariant`'s output witness.  It uses the RAW
  -- `Perm.trans ρ permH` as the input perm so the `residual-recon`
  -- reconciliation lands exactly on the `Perm.trans ρ permH` the goal's
  -- right-hand factor needs.  The residual list it locates is `restH'`
  -- by `extract-prefix` determinism (`eqH'`).
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

      -- determinism: the canonical Σ-pair IS the call-site one.
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
    --
    --   map⁺ vlab (trans permH' (++⁺ˡ (ein e) (↭-sym fire-μ)))
    --     ≅↭ map⁺ vlab (Perm.trans ρ permH)
    --
    -- `residual-recon` gives the VERTEX-level `≅↭`
    --   trans permHc (++⁺ˡ (ein e) (↭-sym rpc)) ≅↭ Perm.trans ρ permH;
    -- the determinism transport `restHc≡` identifies `(restHc, permHc, rpc)`
    -- with `(restH', permH', fire-μ)` (matched at `refl`), and `map⁺-lift-≅↭`
    -- lifts the result through `map⁺ vlab`.
    ------------------------------------------------------------------
    private
      -- The `restHc≡`-`refl`-matching collapse: the call-site
      -- `permH'`/`fire-μ` ARE the canonical `permHc`/`rpc` after transport.
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
  -- The output factor is `permute (++⁺ˡ (eout e) μ)`, i.e. the forward
  -- output permutation `eout e ++ restH ↭ eout e ++ restH'`.  The residual
  -- `μ = fire-μ …` is the CANONICAL residual reshuffle, and the locating
  -- coherence is `locate-coherent` (from the TRUE `residual-recon`), NOT
  -- the old FALSE free-μ `fire-locate-coherent`.
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
      -- `fire-stable-just` says `e` fires on `s'`, contradicting `eqH'`.
      -- Re-expose `eqH'` after noting the residual that fires.
      eqH'-as : extract-prefix (H.ein e) s' ≡ nothing
      eqH'-as = eqH'
  -- FIRE/FIRE: the substantive case.  The residual from `s` permutes onto
  -- the residual from `s'` (`fire-μ`, the canonical residual reshuffle);
  -- the located `(restH'`,`permH')` agree with the canonical ones by
  -- `extract-prefix` determinism, threaded inside `fire-μ`/`locate-coherent`
  -- via `eqH'`.
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
      -- `μ : restH ↭ restH'` is the CANONICAL residual reshuffle `fire-μ`,
      -- the SAME one `edge-step-fire-equivariant` uses internally.
      μ : restH Perm.↭ restH'
      μ = fire-μ e ρ permH permH' eqH' us'

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

  -- The freshness invariant on the PERMUTED stack `s'`, advanced one
  -- `edge-step` per recursion via `SUR.edge-step-Reservoir≤1` (so each
  -- running stack `s'` is `Unique` via `SUR.Reservoir≤1⇒Unique`).  The
  -- `Linear H`-sourced GLOBAL reservoir is supplied by the caller
  -- (`RunInterchangeTail`, via the reservoir-split lemma).
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

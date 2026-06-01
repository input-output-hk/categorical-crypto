-- NOT `--safe`: this module discharges the analytic `swap-≈` postulate
-- of `IsoInvarianceWiring.agda`'s `PerHG` module — §(II) of the informal
-- completeness proof (docs/completeness-proof.typ) — down to two clearly
-- isolated bottom axioms:
--
--   (N)  the symmetric-monoidal *interchange / σ-naturality* axiom
--        `σ ∘ (p ⊗ q) ≈ (q ⊗ p) ∘ σ`  (the `_≈Term_` constructor
--        `σ∘[f⊗g]≈[g⊗f]∘σ` of `Categories.FreeMonoidal`), applied to the
--        two opaque edge boxes `(Agen-edge ⊗ id)` that act on DISJOINT
--        wire blocks; and
--   (K)  the permutation-coherence axiom
--        `Categories.PermuteCoherence.Faithfulness.FaithfulnessResidual`'s
--        `permute-resp-≅↭` — two `permute-via-vlab` reshuffles realising
--        the SAME bijection are `≈Term`-equal.
--
-- Everything BETWEEN `swap-≈` and {N , K} is real plumbing proved here:
--
--   * `process-edges-++-≈`  — term-level factoring of `process-edges`
--     over `_++_` (a fixed prefix `ps` of already-processed edges just
--     precomposes).  Proven by induction on `ps` using `assoc`.  This
--     reduces the general swap (after prefix `ps`) to a FRONT swap.
--   * `decodeOrd-factor` — `decodeOrd` over `ps ++ rest` exposes the
--     prefix term as a right factor, and the validity-carried final
--     `permute-via-vlab` as a left factor.
--   * `front-swap-≈` — the front-of-stack two-edge swap, where the two
--     edges are `Dep`-INCOMPARABLE (independent: neither shares a wire
--     with the other).  This is the locus where N and K are invoked.
--
-- ## What is now PROVEN (vs. postulated) — 2026-05-30 refactor
--
-- `front-swap-≈` is NO LONGER a postulate.  It is now a THEOREM, derived
-- from:
--
--   * (K)  `final-permute-coh` — PROVEN here, GIVEN the Kelly residual
--          `K : FaithfulnessResidual` and a VERTEX-level `Unique (cod H)`
--          witness.  This is the final-permute reconciliation: two
--          validity witnesses `va : a-stk ↭ cod`, `vb : b-stk ↭ cod`
--          bridged by a reshuffle `r : a-stk ↭ b-stk` give
--          `permute va ≈Term permute vb ∘ permute r`, because both `va`
--          and `trans r vb` evaluate to the SAME FinBij by `eval-rigid`
--          on the vertex-level `Unique (cod H)` codomain, lifted through
--          `map⁺ vlab` by `eval-map⁺` + `subst₂-FinBij-≈` — i.e. they
--          are `≅↭`-equal — and K closes the gap.  This is EXACTLY the
--          `permute-via-vlab-coh` pattern of `Sub/DecodeOrdBoundary.agda`,
--          generalised to two distinct domains bridged by `r`.  The
--          `eval-rigid`/`eval-map⁺`/`subst₂-FinBij-≈` helpers are inlined
--          (J-only, `--without-K`-clean), verbatim from `DecodeOrdBoundary`.
--
--   * (N)  `RunInterchange` — the SOLE remaining residual, exposed as a
--          RECORD parameter (the per-swap N-content).  It packages the
--          reshuffle `r : fs₁ ↭ fs₂` between the two post-front stacks
--          and the run-level interchange equation
--          `run₂ ≈Term permute r ∘ run₁`.  Because the two edges are
--          `Incomp` (DISJOINT blocks), the two boxes `(Agen-edge ⊗ id)`
--          commute by N (`σ∘[f⊗g]≈[g⊗f]∘σ`) and the surrounding permutes
--          collapse to `permute r`.  This residual mentions NEITHER the
--          final permute NOR `cod` — only the two front runs — so it is
--          strictly the interchange-axiom content, with the K-half
--          factored out and proven.
--
-- The `coe-cod` codomain-transport bookkeeping between the
-- `decodeOrd-factor` shape and the un-transported `fs` level is also
-- PROVEN here (`coe-vanish`, by matching the `++-stack` proof at `refl`
-- on a generalised source stack).
--
-- INTERFACE CHANGE: `FrontSwap` and the `swap-≈` assembly module now take
-- `(K : FaithfulnessResidual)` + `(uniq-cod : Unique (cod H))` — the
-- VERTEX-level codomain uniqueness (TRUE; dischargeable from
-- `⟪_⟫-cod-unique`), NOT the X-level `Unique (map vlab cod)` (which is
-- FALSE when boundary atoms repeat).  `swap-≈` additionally takes a
-- per-swap `run-interchange` supplying the `RunInterchange` (N) witness.
-- Downstream rewiring supplies K (as in `DecodeOrdBoundary`), the
-- vertex-level `cod` uniqueness (from `⟪_⟫-cod-unique`), and the
-- `RunInterchange` (the interchange axiom on the two disjoint boxes).
{-# OPTIONS --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

-- The chain we discharge against, imported read-only.
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (process-edges-++-stack)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

-- The Kelly faithfulness residual K (`permute-resp-≅↭`), exposed as a
-- record in the `--without-K` module `PermuteCoherence.Faithfulness`,
-- parameterised over the APROP `FreeMonoidalData`.  This is the SAME K
-- threaded through `Discharge/Sub/DecodeOrdBoundary.agda`.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

-- K-free FinBij/eval infrastructure (`--cubical-compatible` modules).
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; _∘-fb_; cons-fb; swap-fb)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H` and a `Dep`-irreflexivity witness `dih`
-- (supplied at the use sites at `H = ⟪f⟫` via `DepIrrefl.dep-irrefl-⟪⟫`),
-- and open the existing `PerHG` machinery.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H

  -- The existing per-hypergraph module from the chain (read-only).  This
  -- is the module whose `swap-≈` postulate we are discharging; we match
  -- its `Order`, `Valid`, `_↝_`, `decodeOrd` definitionally.
  module PH = IW.PerHG H dih

  -- Re-export the linear-extension layer's swap-step constructor and the
  -- incomparability predicate.  `PH.L` is `LinExt (Fin nE) (Dep H) …`;
  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)` — i.e. the two edges
  -- are INDEPENDENT: neither produces a wire the other consumes.
  open PH.L public using (Incomp; swap-step)

  Order : Set
  Order = PH.Order

  Valid : Order → Set
  Valid = PH.Valid

  decodeOrd : (o : Order) → Valid o
            → HomTerm (unflatten (domL H)) (unflatten (codL H))
  decodeOrd = PH.decodeOrd

  --------------------------------------------------------------------
  -- Abbreviations for the two `process-edges` projections.

  -- Final stack of running `o` from stack `s`.
  pe-stack : Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  -- Composed term of running `o` from stack `s`.
  pe-term : (o : Order) (s : List (Fin H.nV))
          → HomTerm (unflatten (map H.vlab s))
                    (unflatten (map H.vlab (pe-stack o s)))
  pe-term o s = proj₂ (process-edges H o s)

  ------------------------------------------------------------------------
  -- Codomain transport: re-index a `HomTerm`'s codomain along a stack
  -- equality.  `process-edges`'s codomain is `unflatten (map vlab s')`
  -- where `s'` is the final stack; since the `_++_`-factoring of the stack
  -- (`process-edges-++-stack`) is only PROPOSITIONAL (it inducts under
  -- `with edge-step`, blocking definitional reduction), we transport
  -- terms across it explicitly.
  ------------------------------------------------------------------------

  coe-cod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s))
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s'))
  coe-cod {d} eq = subst (λ z → HomTerm (unflatten (map H.vlab d))
                                         (unflatten (map H.vlab z)))
                          eq

  -- The stack `_++_`-factoring (imported, real): the final stack of
  -- `ps ++ rest` from `s` is that of `rest` from the post-`ps` stack.
  ++-stack
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  ++-stack = process-edges-++-stack H

  ------------------------------------------------------------------------
  -- PLUMBING 1 — term-level factoring of `process-edges` over `_++_`.
  --
  -- Running `ps ++ rest` from `s` is, on the term level, running `rest`
  -- from the post-`ps` stack, precomposed with running `ps` from `s` —
  -- modulo the codomain transport `coe-cod (++-stack …)`.  Proven by
  -- induction on `ps` using `assoc`; the codomain `subst` is threaded by
  -- a `subst`-naturality step at each cons.
  ------------------------------------------------------------------------

  process-edges-++-≈
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-term (ps ++ rest) s
      ≈Term coe-cod (sym (++-stack ps rest s))
              (pe-term rest (pe-stack ps s) ∘ pe-term ps s)
  process-edges-++-≈ []         rest s = ≈-Term-sym idʳ
  process-edges-++-≈ (e ∷ ps)   rest s
    with edge-step H s e
  ... | s' , t =
    -- process-edges ((e ∷ ps) ++ rest) s
    --   = let (s'',t') = process-edges (ps ++ rest) s' in (s'', t' ∘ t)
    -- so the term is `pe-term (ps ++ rest) s' ∘ t`.  By IH this is (modulo
    -- the codomain transport) `(pe-term rest (pe-stack ps s') ∘
    -- pe-term ps s') ∘ t`, and `assoc` re-brackets it; the right factor
    -- `pe-term ps s' ∘ t` is exactly `pe-term (e ∷ ps) s`.
    --
    -- The codomain transports on the two sides coincide because
    -- `++-stack (e ∷ ps) rest s` reduces (under `with edge-step`) to
    -- `++-stack ps rest s'`, so the leading `subst` matches the IH's.
    ≈-Term-trans
      (∘-resp-≈ (process-edges-++-≈ ps rest s') ≈-Term-refl)
      (coe-cod-assoc (sym (++-stack ps rest s'))
                     (pe-term rest (pe-stack ps s')) (pe-term ps s') t)
    where
      -- Re-bracket the codomain-transported composite past the prefix
      -- edge term `t0`:  `coe (g ∘ f) ∘ t0 ≈ coe (g ∘ (f ∘ t0))`.  The
      -- `coe-cod` (a codomain `subst`) only touches `g`, so it commutes
      -- with the re-association of the lower factors; with `eq = refl`
      -- this is exactly `assoc`.
      coe-cod-assoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomTerm (unflatten (map H.vlab (pe-stack ps s')))
                         (unflatten (map H.vlab a)))
            (f : HomTerm (unflatten (map H.vlab s'))
                         (unflatten (map H.vlab (pe-stack ps s'))))
            (t0 : HomTerm (unflatten (map H.vlab s))
                          (unflatten (map H.vlab s')))
        → coe-cod eq (g ∘ f) ∘ t0
          ≈Term coe-cod eq (g ∘ (f ∘ t0))
      coe-cod-assoc refl g f t0 = assoc

  ------------------------------------------------------------------------
  -- PLUMBING 2 — `decodeOrd` over a prefixed order factors so the prefix
  -- term sits as a right factor.
  --
  --   decodeOrd (ps ++ rest) p
  --     = permute-via-vlab vlab p ∘ pe-term (ps ++ rest) dom
  --     ≈ (permute-via-vlab vlab p ∘ coe-cod (sym ++-stack) (pe-term rest sp))
  --         ∘ pe-term ps dom
  --
  -- where `sp = pe-stack ps dom`.  The codomain transport on `pe-term rest`
  -- is absorbed into the left factor (its codomain is `unflatten (codL H)`
  -- regardless, fixed by the validity witness `p`).
  ------------------------------------------------------------------------

  decodeOrd-factor
    : ∀ (ps rest : Order) (p : Valid (ps ++ rest))
    → decodeOrd (ps ++ rest) p
      ≈Term ( permute-via-vlab H.vlab p
                ∘ coe-cod (sym (++-stack ps rest H.dom))
                          (pe-term rest (pe-stack ps H.dom)) )
              ∘ pe-term ps H.dom
  decodeOrd-factor ps rest p =
    -- decodeOrd (ps++rest) p ≡ permute-via-vlab p ∘ pe-term (ps++rest) dom
    -- (definitional), rewrite the right operand by `process-edges-++-≈`
    -- (yielding `permute ∘ coe-cod eq (pe-term rest sp ∘ pe-term ps dom)`),
    -- push the `coe-cod` into the left factor (`coe-cod-∘`, by subst-nat),
    -- then re-associate the triple composition by `≈-Term-sym assoc`.
    ≈-Term-trans
      (∘-resp-≈ ≈-Term-refl (process-edges-++-≈ ps rest H.dom))
      (≈-Term-trans
        (∘-resp-≈ ≈-Term-refl
          (coe-cod-∘ (sym (++-stack ps rest H.dom))
                     (pe-term rest (pe-stack ps H.dom))
                     (pe-term ps H.dom)))
        (≈-Term-sym assoc))
    where
      -- `coe-cod` only touches the codomain, which lives in the left
      -- factor, so it commutes out of a composition (subst-naturality).
      coe-cod-∘
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomTerm (unflatten (map H.vlab (pe-stack ps H.dom)))
                         (unflatten (map H.vlab a)))
            (f : HomTerm (unflatten (map H.vlab H.dom))
                         (unflatten (map H.vlab (pe-stack ps H.dom))))
        → coe-cod eq (g ∘ f) ≈Term coe-cod eq g ∘ f
      coe-cod-∘ refl g f = ≈-Term-refl

------------------------------------------------------------------------
-- The analytic front-of-stack swap.
--
-- We now fix `H` and an INDEPENDENT pair of edges `e e'` that sit at the
-- front of the remaining stack `rest = e ∷ e' ∷ qs` vs `e' ∷ e ∷ qs`,
-- both run from the SAME stack `sp`.  The two runs:
--
--   run₁ = pe-term (e ∷ e' ∷ qs) sp
--   run₂ = pe-term (e' ∷ e ∷ qs) sp
--
-- are related up to ≈Term — but as factors of `decodeOrd` they are wrapped
-- between the shared prefix term (right) and the validity-carried final
-- `permute-via-vlab` (left).  The CONTENT is:
--
--   (a) Each edge fires as `splitJoin (Agen-edge ⊗ id) rest` after a
--       `permute-via-vlab` locating its inputs (see `Decode.edge-step`'s
--       success branch / `FreeSMC.Steps.fire-bridged`).
--   (b) INDEPENDENCE (`Incomp (Dep H) e e'`): neither edge consumes a
--       wire the other produces, so `e`'s outputs do not overlap `e'`'s
--       inputs (and vice versa).  Hence both orders fire successfully,
--       reaching `↭`-equal post-stacks (this is the multiset content,
--       already proven generically as `post-swap-stack-↭` in
--       `Sub/AllFireEdgeSwap.agda`).
--   (c) The two opaque boxes `(Agen-edge e ⊗ id)` and `(Agen-edge e' ⊗ id)`
--       act on DISJOINT blocks, so they COMMUTE by the interchange axiom
--       (N) `σ ∘ (p ⊗ q) ≈ (q ⊗ p) ∘ σ`.
--   (d) The surrounding `permute-via-vlab` reshuffles differ between the
--       two orders but realise the SAME total bijection on wires; they are
--       reconciled by (K) `FaithfulnessResidual.permute-resp-≅↭`.
--
-- Of these, (d) [the K-instance] is now PROVEN here (`final-permute-coh`,
-- GIVEN the Kelly residual K + a `Unique (map vlab cod)` witness), and
-- (b)+(c) [the N-instance: the post-stack reshuffle and the run-level
-- interchange of the two disjoint boxes] are the SOLE residual, packaged
-- as the `RunInterchange` record.  `front-swap-≈` is assembled from both,
-- stated at the `decodeOrd`-factor level so it plugs straight into
-- `swap-≈` after the prefix reduction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- K-FREE helper infrastructure (inlined, J-only copies of the
-- intrinsically K-free lemmas that live in the `--with-K` modules
-- `PermuteCoherence.{Rigid,Map}`).  These are VERBATIM copies of the
-- §0 block of `Discharge/Sub/DecodeOrdBoundary.agda`; co-infectivity
-- forbids importing those `--with-K` modules into this `--without-K`
-- module, so the (intrinsically J-only) helpers are re-derived here.
------------------------------------------------------------------------

private
  ----------------------------------------------------------------------
  -- Rigidity of `eval-↭` on `Unique` codomains (copy of
  -- `PermuteCoherence.Rigid.eval-rigid`; structural, no K).
  ----------------------------------------------------------------------

  All-lookup : ∀ {a p} {A : Set a} {Q : A → Set p} {xs : List A}
             → All Q xs → (i : Fin (length xs)) → Q (lookup xs i)
  All-lookup (q ∷ _)  zero    = q
  All-lookup (_ ∷ qs) (suc i) = All-lookup qs i

  lookup-injective-unique
    : ∀ {a} {A : Set a} {xs : List A}
    → Unique xs → (i j : Fin (length xs))
    → lookup xs i ≡ lookup xs j
    → i ≡ j
  lookup-injective-unique (_  ∷ᵘ _ ) zero    zero    _  = refl
  lookup-injective-unique (x≢ ∷ᵘ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
  lookup-injective-unique (x≢ ∷ᵘ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
  lookup-injective-unique (_  ∷ᵘ uq) (suc i) (suc j) eq =
    cong suc (lookup-injective-unique uq i j eq)

  lookup-sound
    : ∀ {a} {A : Set a} {xs ys : List A} (p : xs Perm.↭ ys) (i : Fin (length xs))
    → lookup ys (eval-↭ p P.⟨$⟩ʳ i) ≡ lookup xs i
  lookup-sound Perm.refl         i             = refl
  lookup-sound (Perm.prep x p)   0F            = refl
  lookup-sound (Perm.prep x p)   (suc i)       = lookup-sound p i
  lookup-sound (Perm.swap x y p) 0F            = refl
  lookup-sound (Perm.swap x y p) (suc 0F)      = refl
  lookup-sound (Perm.swap x y p) (suc (suc i)) = lookup-sound p i
  lookup-sound (Perm.trans p q)  i             =
    trans (lookup-sound q (eval-↭ p P.⟨$⟩ʳ i)) (lookup-sound p i)

  eval-rigid
    : ∀ {a} {A : Set a} {xs ys : List A} → Unique ys
    → (p q : xs Perm.↭ ys)
    → eval-↭ p ≈-fb eval-↭ q
  eval-rigid uniq p q i =
    lookup-injective-unique uniq _ _
      (trans (lookup-sound p i) (sym (lookup-sound q i)))

  ----------------------------------------------------------------------
  -- `eval-map⁺` and its `subst₂`-on-FinBij algebra (copies of the
  -- `PermuteCoherence.Map` lemmas; all J-only, no K).
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

-- The `FrontSwap` module is now parameterised by the Kelly faithfulness
-- residual `K : FaithfulnessResidual` (the SAME K threaded through
-- `Discharge/Sub/DecodeOrdBoundary.agda`) and a `Unique` witness on the
-- vertex-labelled codomain `map vlab cod` (supplied downstream at
-- `H = ⟪f⟫` via `⟪_⟫-cod-unique` after `map`; for an arbitrary `H` it
-- is a genuine hypothesis, exactly as `objUIP`/`uniq` are in
-- `DecodeOrdBoundary`).  GIVEN those, the K-half of the front swap (the
-- final-permute reconciliation) is a THEOREM (`final-permute-coh`);
-- only the N-half (the run-level interchange) remains a residual.
-- SOUNDNESS NOTE: `uniq-cod` is the VERTEX-level `Unique (cod H)` (TRUE,
-- dischargeable from `⟪_⟫-cod-unique` at `H = ⟪f⟫`), NOT the X-level
-- `Unique (map vlab cod)` (which is FALSE when boundary atoms repeat).
-- The final-permute reconciliation runs `eval-rigid` on the VERTEX-level
-- derivations `va`/`trans r vb : … ↭ cod`, then lifts through `map⁺ vlab`
-- via `eval-map⁺` + `subst₂-FinBij-≈` — exactly the `DecodeOrdBoundary`
-- pattern.
module FrontSwap (H : Hypergraph FlatGen)
                 (dih : ∀ {e} → ¬ (Dep H e e))
                 (K : FaithfulnessResidual)
                 (uniq-cod : Unique (Hypergraph.cod H))
                 where
  private module H = Hypergraph H
  open PerHG H dih
  open FaithfulnessResidual K

  --------------------------------------------------------------------
  -- (K)  THE FINAL-PERMUTE RECONCILIATION — fully PROVEN given K.
  --
  -- Given a reshuffle `r : a-stk ↭ b-stk` between two post-front stacks
  -- and two validity-style witnesses `va : a-stk ↭ cod`, `vb : b-stk ↭
  -- cod`, the `permute-via-vlab` of `va` agrees (up to ≈Term) with the
  -- `permute-via-vlab` of `vb` PRECOMPOSED by the reshuffle's permute:
  --
  --     permute-via-vlab va  ≈Term  permute-via-vlab vb ∘ permute-via-vlab r
  --
  -- because both `va` and `trans r vb` are `↭`-derivations into the SAME
  -- codomain `cod`, which is `Unique` after `map vlab`; hence their
  -- `map⁺ vlab` liftings evaluate to the same FinBij by `eval-rigid`,
  -- i.e. they are `≅↭`-equal, and K (`permute-resp-≅↭`) closes the gap.
  -- (`permute-via-vlab v = permute (map⁺ vlab v)` definitionally, and
  -- `map⁺ vlab (trans r vb) = trans (map⁺ vlab r) (map⁺ vlab vb)`, with
  -- `permute (trans a b) = permute b ∘ permute a`.)
  --
  -- This is the K-instance of the front swap, isolated and discharged —
  -- exactly the `permute-via-vlab-coh` pattern of `DecodeOrdBoundary`,
  -- generalised to two distinct domains bridged by `r`.
  --------------------------------------------------------------------

  private
    -- `≅↭`-equality of the two map-lifted derivations into `map vlab cod`.
    permute-bridge-≅↭
      : ∀ {a-stk b-stk : List (Fin H.nV)}
          (r  : a-stk Perm.↭ b-stk)
          (va : a-stk Perm.↭ H.cod)
          (vb : b-stk Perm.↭ H.cod)
      → eval-↭ (PermProp.map⁺ H.vlab va)
        ≈-fb eval-↭ (PermProp.map⁺ H.vlab (Perm.trans r vb))
    permute-bridge-≅↭ {a-stk} {b-stk} r va vb =
      -- `eval-rigid` is run on the VERTEX-level derivations `va` and
      -- `trans r vb`, both `a-stk ↭ cod`, against the TRUE vertex-level
      -- `Unique (cod H)`; the result is transported through `map⁺ vlab`
      -- by `eval-map⁺` + `subst₂-FinBij-≈` (the `DecodeOrdBoundary`
      -- pattern), so NO X-level `Unique (map vlab cod)` is needed.
      subst (λ z → z ≈-fb eval-↭ (PermProp.map⁺ H.vlab (Perm.trans r vb)))
            (sym (eval-map⁺ H.vlab va))
        (subst (λ z → subst₂ FinBij (sym (length-map H.vlab a-stk))
                                    (sym (length-map H.vlab H.cod)) (eval-↭ va)
                      ≈-fb z)
               (sym (eval-map⁺ H.vlab (Perm.trans r vb)))
          (subst₂-FinBij-≈ (sym (length-map H.vlab a-stk))
                           (sym (length-map H.vlab H.cod))
            (eval-rigid uniq-cod va (Perm.trans r vb))))

  final-permute-coh
    : ∀ {a-stk b-stk : List (Fin H.nV)}
        (r  : a-stk Perm.↭ b-stk)
        (va : a-stk Perm.↭ H.cod)
        (vb : b-stk Perm.↭ H.cod)
    → permute-via-vlab H.vlab va
      ≈Term permute-via-vlab H.vlab vb ∘ permute-via-vlab H.vlab r
  final-permute-coh r va vb =
    -- permute-via-vlab va = permute (map⁺ vlab va)
    --   ≈Term [K on (map⁺ va , map⁺ (trans r vb)) via ≅↭ bridge]
    -- permute (map⁺ vlab (trans r vb))
    --   = permute (trans (map⁺ vlab r) (map⁺ vlab vb))
    --   = permute (map⁺ vlab vb) ∘ permute (map⁺ vlab r)
    --   = permute-via-vlab vb ∘ permute-via-vlab r          (definitional)
    permute-resp-≅↭
      (PermProp.map⁺ H.vlab va)
      (PermProp.map⁺ H.vlab (Perm.trans r vb))
      (permute-bridge-≅↭ r va vb)

  --------------------------------------------------------------------
  -- (N)  THE RUN-LEVEL INTERCHANGE — the SOLE residual.
  --
  -- This is the genuinely-analytic, K-free content of the front swap:
  -- running the two INDEPENDENT front edges in the order `e' ∷ e` from
  -- the shared post-prefix stack `sp` equals running them in the order
  -- `e ∷ e'` followed by a reshuffle `r`, where `r` is a permutation of
  -- the two post-front stacks.  Because the two edges are `Incomp`
  -- (DISJOINT wire blocks), the two opaque boxes `(Agen-edge ⊗ id)`
  -- commute by the interchange axiom (N) `σ ∘ (f ⊗ g) ≈ (g ⊗ f) ∘ σ`
  -- (the `_≈Term_` constructor `σ∘[f⊗g]≈[g⊗f]∘σ` of `Categories.
  -- FreeMonoidal`), and the surrounding `permute-via-vlab` reshuffles
  -- collapse to a single `permute-via-vlab r`.
  --
  -- We expose it as a record so it carries BOTH the reshuffle `r` and
  -- the run equation; `final-permute-coh` (K) then closes the gap
  -- between the two validity witnesses.  This is the smallest residual:
  -- it mentions NEITHER the final permute NOR `cod`, only the two front
  -- runs and the reshuffle between their post-stacks — i.e. EXACTLY the
  -- interchange axiom applied to the two boxes, plus the bookkeeping
  -- that the surrounding `permute-via-vlab` collapse to `permute r`.
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- (N)  THE INTERCHANGE KERNEL — PROVEN here, isolated as the literal
  -- σ-naturality application.
  --
  -- This is the genuine §II interchange axiom (N), `σ ∘ (f ⊗ g) ≈
  -- (g ⊗ f) ∘ σ`, packaged in the σ-conjugation form
  --
  --     g ⊗₁ f  ≈Term  σ ∘ (f ⊗₁ g) ∘ σ
  --
  -- that is the algebraic heart of "two boxes on DISJOINT blocks
  -- commute": precompose+postcompose with the braid and the two boxes
  -- swap places.  It is derived purely from the FreeMonoidal primitives
  -- `σ∘[f⊗g]≈[g⊗f]∘σ` (the N constructor) and `σ∘σ≈id` (involutivity),
  -- with no K and no firing data — it is the K-free, hypergraph-free
  -- core of the run-level interchange.
  --
  -- `run-eq` (the residual below) is exactly this kernel TRANSPORTED
  -- through the two `edge-step` boxes' `splitJoin`/`unflatten-++-≅`
  -- bookkeeping and the tail recursion on `qs`; that transport (the
  -- Mac-Lane "swap-mac-lane-residual" chase of `Sub/SwapAtomAligned.agda`,
  -- which even the `--with-K` development leaves open) plus the
  -- topological firing-success of both orders (FALSE from `Incomp`
  -- alone — see `EdgeReorder.agda`) is what keeps `run-eq` a residual.
  -- The N-axiom itself, however, enters ONLY through `box-interchange`.
  --------------------------------------------------------------------

  box-interchange
    : ∀ {A B C D : ObjTerm}
        (f : HomTerm A B) (g : HomTerm C D)
    → g ⊗₁ f ≈Term σ ∘ ((f ⊗₁ g) ∘ σ)
  box-interchange f g =
    -- σ ∘ (f ⊗ g) ∘ σ
    --   ≈ ((g ⊗ f) ∘ σ) ∘ σ           [N: σ∘[f⊗g]≈[g⊗f]∘σ, under ∘ σ]
    --   ≈ (g ⊗ f) ∘ (σ ∘ σ)           [assoc]
    --   ≈ (g ⊗ f) ∘ id                [σ∘σ≈id]
    --   ≈ g ⊗ f                       [idʳ]
    ≈-Term-sym
      (≈-Term-trans
        (≈-Term-trans
          (≈-Term-sym assoc)
          (∘-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ ≈-Term-refl))
        (≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl σ∘σ≈id) idʳ)))

  record RunInterchange (ps qs : Order) {e e' : Fin H.nE}
                        (inc : Incomp e e') : Set where
    private
      sp  = pe-stack ps H.dom
      fs₁ = pe-stack (e ∷ e' ∷ qs) sp
      fs₂ = pe-stack (e' ∷ e ∷ qs) sp
    field
      -- The reshuffle between the two post-front stacks.
      reshuffle : fs₁ Perm.↭ fs₂
      -- The interchange equation (N): the `e' ∷ e` run equals the
      -- `e ∷ e'` run followed by the reshuffle's permute.
      run-eq
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term permute-via-vlab H.vlab reshuffle ∘ pe-term (e ∷ e' ∷ qs) sp

  --------------------------------------------------------------------
  -- (N + K) FRONT SWAP — assembled from the N-residual + the proven
  -- K-coherence.  GIVEN a `RunInterchange` witness `RI`, the front swap
  -- is a THEOREM.  Stated at exactly the shape `decodeOrd-factor`
  -- produces, so it plugs straight into `swap-≈`'s `∘-resp-≈`.
  --------------------------------------------------------------------

  front-swap-≈
    : ∀ (ps qs : Order) {e e' : Fin H.nE}
        (inc : Incomp e e')
        (RI : RunInterchange ps qs inc)
        (p₁ : Valid (ps ++ e ∷ e' ∷ qs))
        (p₂ : Valid (ps ++ e' ∷ e ∷ qs))
    → ( permute-via-vlab H.vlab p₁
          ∘ coe-cod (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
                    (pe-term (e ∷ e' ∷ qs) (pe-stack ps H.dom)) )
      ≈Term
      ( permute-via-vlab H.vlab p₂
          ∘ coe-cod (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
                    (pe-term (e' ∷ e ∷ qs) (pe-stack ps H.dom)) )
  front-swap-≈ ps qs {e} {e'} inc RI p₁ p₂ =
    -- Both `coe-cod` transports vanish into the UN-transported `fs`
    -- level by matching the `++-stack` proofs at `refl` (`coe-vanish`):
    -- the codomain equalities are between `pe-stack (ps ++ _) dom` and
    -- `pe-stack _ sp`, and `permute-via-vlab pᵢ`'s domain is the FORMER
    -- while the runs land in the LATTER, so the two `subst`s on each side
    -- compose to the identity transport once `p₁,p₂` are re-expressed at
    -- the `fs` level (`p₁', p₂'` below).
    ≈-Term-trans (coe-vanish (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁
                             (pe-term (e ∷ e' ∷ qs) sp))
      (≈-Term-trans assembled
        (≈-Term-sym (coe-vanish (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂
                                (pe-term (e' ∷ e ∷ qs) sp))))
    where
      open RunInterchange RI

      sp  = pe-stack ps H.dom
      fs₁ = pe-stack (e ∷ e' ∷ qs) sp
      fs₂ = pe-stack (e' ∷ e ∷ qs) sp

      run₁ = pe-term (e ∷ e' ∷ qs) sp
      run₂ = pe-term (e' ∷ e ∷ qs) sp

      -- Re-express the validity witnesses at the `fs` level.
      p₁' : fs₁ Perm.↭ H.cod
      p₁' = subst (Perm._↭ H.cod) (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁
      p₂' : fs₂ Perm.↭ H.cod
      p₂' = subst (Perm._↭ H.cod) (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂

      -- `coe-vanish`: with the stack-equality matched at `refl`, the
      -- codomain `subst` on the run and the codomain `subst` on the
      -- validity witness compose to the un-transported composite.  The
      -- source stack `FS` is GENERALISED to a variable so the `refl`
      -- split is not unification-stuck under `--without-K` (both sides
      -- are `pe-stack`-redexes that do not reduce; abstracting `FS` makes
      -- the inferred index a variable).
      coe-vanish
        : ∀ {FS B : List (Fin H.nV)} (eq : FS ≡ B)
            (pv : FS Perm.↭ H.cod)
            (run : HomTerm (unflatten (map H.vlab sp))
                           (unflatten (map H.vlab B)))
        → permute-via-vlab H.vlab pv ∘ coe-cod (sym eq) run
          ≈Term permute-via-vlab H.vlab (subst (Perm._↭ H.cod) eq pv) ∘ run
      coe-vanish refl pv run = ≈-Term-refl

      -- The core assembly at the `fs` level:
      --   permute p₁' ∘ run₁
      --     ≈ (permute p₂' ∘ permute reshuffle) ∘ run₁      [K: final-permute-coh]
      --     ≈ permute p₂' ∘ (permute reshuffle ∘ run₁)      [assoc]
      --     ≈ permute p₂' ∘ run₂                            [N: run-eq, sym]
      assembled
        : permute-via-vlab H.vlab p₁' ∘ run₁
          ≈Term permute-via-vlab H.vlab p₂' ∘ run₂
      assembled =
        ≈-Term-trans
          (∘-resp-≈ (final-permute-coh reshuffle p₁' p₂') ≈-Term-refl)
          (≈-Term-trans assoc
            (∘-resp-≈ ≈-Term-refl (≈-Term-sym run-eq)))

------------------------------------------------------------------------
-- Assembly of `swap-≈`.
--
-- Match the swap-step `swap-step ps qs inc : (ps ++ e ∷ e' ∷ qs) ↝
-- (ps ++ e' ∷ e ∷ qs)`.  Then:
--
--   decodeOrd (ps ++ e ∷ e' ∷ qs) p₁
--     ≈ (permute-via-vlab p₁ ∘ pe-term (e ∷ e' ∷ qs) sp) ∘ pe-term ps dom
--                                                       [decodeOrd-factor]
--     ≈ (permute-via-vlab p₂ ∘ pe-term (e' ∷ e ∷ qs) sp) ∘ pe-term ps dom
--                                                       [front-swap-≈ (N+K)]
--     ≈ decodeOrd (ps ++ e' ∷ e ∷ qs) p₂
--                                                  [decodeOrd-factor, sym]
--
-- where `sp = pe-stack ps dom`.  The shared right factor `pe-term ps dom`
-- (the already-processed prefix) is carried through by `∘-resp-≈`.
------------------------------------------------------------------------

-- The `swap-≈` assembly is now parameterised by K + the `Unique`
-- codomain witness (threaded into `FrontSwap`), and by the SOLE residual
-- `run-interchange` — the N-content witness supplied per swap.  This is
-- the smallest residual the front swap reduces to (the run-level
-- interchange / `RunInterchange` record); the K-half and all plumbing
-- are PROVEN.  Downstream rewiring (`DecodeRelRespIsoWired`) supplies K
-- (as in `DecodeOrdBoundary`), the `map vlab cod` Uniqueness (from
-- `⟪_⟫-cod-unique`), and the per-swap `RunInterchange` (the interchange
-- axiom applied to the two disjoint boxes).
module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         where
  open PerHG H dih
  module FS = FrontSwap H dih K uniq-cod
  open FS using (front-swap-≈; RunInterchange)

  -- The `run-interchange` consumer now carries the SWAP-SITE PROVENANCE:
  -- the order it is asked about, `ps ++ e' ∷ e ∷ qs`, is a permutation of
  -- the natural order `range nE`.  This is the SOUND side condition the
  -- (previously false-as-stated) `dom-reservoir` was missing: the
  -- reservoir bound `Reservoir≤1 H o H.dom` holds for `o ↭ range nE`
  -- (every edge appears exactly once, so `eout` is not over-counted), and
  -- every order the connectivity chase visits is `↝*`-reachable from
  -- `range nE`, hence a permutation of it.  The producer
  -- (`DecodeRelRespIsoWired`) discharges the reservoir from this `↭ range`
  -- witness via `StackUniqueReach.dom-reservoir-prov`.
  module _ (run-interchange
              : ∀ (ps qs : Order) {e e' : Fin (Hypergraph.nE H)} (inc : Incomp e e')
              → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
              → RunInterchange ps qs inc) where

    swap-≈
      : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂
      → o₁ Perm.↭ range (Hypergraph.nE H)
      → (p₁ : PH.Valid o₁) (p₂ : PH.Valid o₂)
      → PH.decodeOrd o₁ p₁ ≈Term PH.decodeOrd o₂ p₂
    swap-≈ (swap-step ps {e} {e'} qs inc) o₁↭range p₁ p₂ =
      ≈-Term-trans
        (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₁)
        (≈-Term-trans
          (∘-resp-≈ (front-swap-≈ ps qs inc
                       (run-interchange ps qs inc o₂↭range) p₁ p₂)
                    ≈-Term-refl)
          (≈-Term-sym (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₂)))
      where
        -- `o₂ = ps ++ e' ∷ e ∷ qs` is `↭ o₁ = ps ++ e ∷ e' ∷ qs` (an
        -- adjacent transposition under the prefix `ps`), hence `↭ range`.
        o₂↭range : (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
        o₂↭range =
          Perm.↭-trans
            (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl))
            o₁↭range

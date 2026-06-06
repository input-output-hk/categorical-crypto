{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Lemma 0 of the informal completeness proof: "vertex relabelling is free
-- + ψ re-indexing".  This is the constructive discharge of the
-- `iso-transport` postulate kept in
-- `Discharge.IsoInvarianceWiring` (the cross-iso `module _ {H J} (Φ)`).
--
-- ## The statement (verbatim from IsoInvarianceWiring, cross-iso module)
--
--     iso-transport :
--       (vJ : PJ.Valid (range J.nE))
--       → Σ[ vτ ∈ PH.Valid τ ]
--           ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
--                    (PJ.decodeOrd (range J.nE) vJ)
--             ≈Term PH.decodeOrd τ vτ )
--
-- where `τ = map ψ⁻¹ (range J.nE)` is the ψ-pullback of J's natural Fin
-- order onto H's edges, and
--
--     decodeOrd o p = permute-via-vlab vlab p ∘ proj₂ (process-edges o dom).
--
-- ## Mathematical content
--
-- The decoder `process-edges`/`decodeOrd` factors entirely through
-- `map vlab` of the incidence and boundary data; it never inspects
-- vertex *identities*.  Hence the iso's vertex relabel `φ` and edge
-- reindex `ψ` are "free": running `process-edges J (range J.nE)` from
-- `J.dom` and running `process-edges H τ` from `H.dom` produce final
-- stacks related by `map φ`, and the produced HomTerms agree up to
-- `≈Term` after transporting along the iso's label-agreement fields
-- `φ-lab` (vertices) and `ψ-elab` (edge generators).
--
-- This is the TERM-level naturality analogue of the multiset-level
-- `Discharge/StackPerm.agda` lemma `process-edges-resp-iso-stack`, and
-- a term-level analogue of the AllFire-transport in
-- `Discharge/Sub/IsoInducesEdgePerm.agda`
-- (`AllFire-resp-aligned-tabulate`).
--
-- ## Status (see the per-definition headers below)
--
-- CONSTRUCTIVE here (real proofs, no postulates):
--   * the boundary identifications `domL-iso`/`codL-iso` (§1.2),
--   * `φ` injectivity (§1.1) and `map φ`-reflection of `↭` (§4),
--   * the per-edge generator agreement `Agen-edge-respects-ψ` (§2), from
--     `ψ-elab`, mirroring `Agen-edge-respects-elab-eq` of
--     `Sub/BridgeToGFull.agda`,
--   * the *stack/validity* transport `iso-valid` (§4),
--   * the entire §5 ASSEMBLY: the outer `subst₂` is split over `∘`
--     (`subst₂-∘-distrib`), the `process-edges` factor is discharged by
--     the §3 kernel, and `iso-transport` is assembled from the pieces.
--
-- NEWLY DISCHARGED (given the module parameters `K`/`codUnique*`):
--   * (§2b/§2c) The STACK (`proj₁`) component of the kernel is now FULLY
--     CONSTRUCTIVE at both granularities: `edge-step-stack-φ` (per-edge,
--     FIRE/SKIP branch-lockstep via `extract-prefix-via-injective-*` +
--     `ψ-ein`/`ψ-eout`) and `process-edges-fin-φ` (per-edge-LIST, by
--     induction).  This is the list-level analogue of
--     `StackPerm.process-edges-resp-iso-stack`.
--   * (§3) `process-edges-respects-φ` is now a REAL function by induction
--     on `eJ`; the `[]` base case is proven constructively
--     (`subst₂-HomTerm-id`).  Its `_∷_` step `process-edges-respects-φ-step`
--     is ALSO CONSTRUCTIVE now: the `proj₁` half is `process-edges-fin-φ`,
--     and the term half is assembled by splitting the boundary `subst₂`
--     over the `tJ' ∘ tJ` composite (`subst₂-∘-distrib`), discharging the
--     COD factor by the IH and the DOM factor by the per-`edge-step`
--     residual `edge-step-term-φ` (`∘-resp-≈`).  (The kernel type
--     `process-edges-respects-φ-T` now fixes `fin≡ := process-edges-fin-φ`,
--     so it is a plain `≈Term` rather than a Σ.)
--   * (§5b) `permute-relabel-free` is now PROVEN GIVEN K: the boundary
--     `subst₂` is pushed through `permute` (`permute-subst₂`), bringing
--     both sides onto a common pair of `map H.vlab _` lists, and the Kelly
--     residual K (`permute-resp-≅↭`) closes the `≈Term` goal from the
--     `≅↭` evidence.
--   * (§5b) `permute-relabel-free-≅↭` — the FinBij-level φ-equivariant
--     rigidity of the two final permutes — is now CONSTRUCTIVELY PROVEN
--     (no postulate).  Both `eval-↭` images are descended to `Fin (length
--     H.cod)` (via `length-map`) and discriminated through the `Unique`
--     Fin-list `H.cod` (`codUniqueH`): `lookup-sound` pins each image to the
--     matching `sH-final` vertex, the J-side passing through
--     `lookup J.cod = φ ∘ lookup H.cod` (from `φ-cod`) and `sJ-final =
--     map φ sH-final` (from `fin-eq`), with `φ` injective.  The chase uses
--     only the §0b–0d K-free helpers (`eval-map⁺`, `eval-subst₂-↭`,
--     `lookup-sound`, `lookup-injective-unique`, `lookup-map`) plus
--     `Data.Nat.Properties.≡-irrelevant` for `subst Fin` cast-irrelevance.
--
-- ONE clearly-scoped residual postulate remains (NARROWED from the old
-- per-edge-LIST `process-edges-respects-φ-step` to a single per-`edge-step`
-- `≈Term`; precise "what it needs" note at its definition):
--   (§3) `edge-step-term-φ` — the per-`edge-step` term-level φ-naturality:
--        running ONE `edge-step` of the J-edge `j` vs the H-edge `ψ⁻¹ j`
--        produces `≈Term`-equal HomTerms after the boundary `subst₂`.
--        SKIP branch: both `edge-step`s are `(_, id)`, so the goal is
--        `subst₂ HomTerm p q id ≈Term id`.  FIRE branch: the genuine
--        Mac-Lane core — the `mid' = unflatten-++-≅ ∘ (Agen-edge ⊗₁ id) ∘
--        unflatten-++-≅` factor agrees via `Agen-edge-respects-ψ` (§2) +
--        `id⊗id≈id`, and the `permute-via-vlab` factor agrees by a second
--        Kelly `permute-resp-≅↭` (K) application at the φ-relabel between
--        the two `extract-prefix` permutations (a φ-equivariant rigidity
--        proof analogous to §5b).  Everything ELSE in the kernel — both
--        stack components, the list-level composition, the IH threading,
--        and the §4/§5 assembly — is now constructive.
--
-- ## Interface change
--
-- The cross-iso module now takes THREE extra explicit parameters,
-- supplied by the downstream wiring (`IsoInvarianceConcrete`) at the
-- `H = ⟪f⟫`, `J = ⟪g⟫` call site:
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

-- The Kelly faithfulness residual K (`permute-resp-≅↭`), and the K-free
-- FinBij/eval infrastructure, taken at the APROP `FreeMonoidalData` so
-- that `permute`/`unflatten`/`HomTerm`/`≈Term` all line up definitionally
-- with the APROP-level ones used here.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

-- The shared `--without-K` FinBij/eval-rigid leaf (the union of the
-- inlined K-free helpers, hosted once in `PermuteCoherence`).  IsoTransport
-- previously held the SUPERSET copy of this block (§0b–0d below).
open import Categories.PermuteCoherence.EvalRigidKFree
  using ( lookup-injective-unique; lookup-sound; lookup-map; eval-subst₂-↭
        ; subst₂-FinBij-as-subst; cast-irr; subst-Fin-trans; lookup-subst-list
        ; subst-Fin-roundtrip; subst-Fin-roundtrip'; subst-Fin-sym-sym
        ; eval-map⁺ )

--------------------------------------------------------------------------------
-- §0.  ≈Term plumbing (local copies of the trivial helpers used widely
-- elsewhere — `Completeness.DecodeRespIso`, `Sub/BridgeToGFull`, etc.).
-- Both are `refl`-pattern lemmas, fine under `--without-K`.

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

-- Trivial `Maybe` helpers used by the §2b branch-lockstep.
private
  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

  -- First-component injectivity for `just (a , _) ≡ just (b , _)`.
  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

-- Transporting the identity morphism along a SINGLE path on both ends
-- yields the identity (path induction, without-K clean).
subst₂-HomTerm-id
  : ∀ {A B} (p : A ≡ B) → subst₂ HomTerm p p id ≡ id
subst₂-HomTerm-id refl = refl

-- `subst₂ HomTerm` distributes over composition (local copy of
-- `DecodeRespIso.subst₂-∘-distrib`; `refl/refl/refl`-pattern, so
-- without-K clean).
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
-- §0b.  K-FREE rigidity infrastructure — now imported from the shared leaf
-- `Categories.PermuteCoherence.EvalRigidKFree` (IsoTransport previously held
-- the SUPERSET inlined copy of this block).

--------------------------------------------------------------------------------
-- §1.  Cross-iso module.  Mirrors `IsoInvarianceWiring`'s cross-iso
-- module so the names (`PH`, `PJ`, `τ`, `domL-iso`, `codL-iso`) line up
-- exactly with the target `iso-transport` type.

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (dihH : ∀ {e} → ¬ (Dep H e e))
         (dihJ : ∀ {e} → ¬ (Dep J e e))
         -- The Kelly faithfulness residual that gates every final
         -- `permute` in this development (a record value of the
         -- `--without-K` module `PermuteCoherence.Faithfulness`); supplied
         -- by the downstream wiring (`IsoInvarianceConcrete`) at the
         -- `H = ⟪f⟫`, `J = ⟪g⟫` call site.
         (K : FaithfulnessResidual)
         -- Fin-level codomain uniqueness, dischargeable downstream from
         -- `Sub.FromAPROPCodUnique.⟪_⟫F-cod-unique` at `H = ⟪f⟫`,
         -- `J = ⟪g⟫`.
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
  -- §1.2  Boundary identifications (verbatim from IsoInvarianceWiring,
  -- needed at the same `cong unflatten _` boundary the target uses).

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
  -- §1.3  The ψ-pullback order (verbatim).

  τ : PH.Order
  τ = map ψ⁻¹ (range J.nE)

  ------------------------------------------------------------------------
  -- §2.  Per-edge generator agreement, "vertex relabel is free for
  -- generators".  Mirrors `Agen-edge-respects-elab-eq` of
  -- `Sub/BridgeToGFull.agda` (there for FromAPROP-level isos; here the
  -- iso is given directly so the fields are immediately available).
  --
  -- From the iso's `ψ-elab e` field — which says
  --     subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e)) ≡ H.elab e
  -- — we conclude the relabelled J-generator equals the H-generator:
  --     subst₂ HomTerm (cong unflatten (atom-ein e)) (cong unflatten (atom-eout e))
  --            (Agen-edge J (ψ e))
  --       ≡ Agen-edge H e

  -- Naturality of `Agen-edge-aux` under `subst₂` along atom-list
  -- equalities.  `refl/refl` match (without-K clean — both proofs are
  -- the same `refl` constructor at the same equation).
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
  -- §2b.  Per-edge `edge-step` φ-naturality, STACK component (CONSTRUCTIVE).
  --
  -- For an H-edge `e` and the corresponding J-edge `ψ e`, running
  -- `edge-step J (ψ e)` from `map φ sH` produces a final stack that is
  -- the `map φ`-image of the stack produced by `edge-step H e` from `sH`.
  --
  -- Proof: case-split on `extract-prefix (H.ein e) sH`.  By
  -- `extract-prefix-via-injective-{nothing,just} φ φ-inj` (transported along
  -- `ψ-ein e : J.ein (ψ e) ≡ map φ (H.ein e)`) the J-side `extract-prefix`
  -- lands in the SAME branch:
  --   * SKIP/SKIP: both stacks are the inputs, `map φ sH ≡ map φ sH`.
  --   * FIRE/FIRE: J stack = `J.eout (ψ e) ++ map φ rest`, H stack =
  --     `H.eout e ++ rest`; equal by `ψ-eout e` + `map-++ φ`.

  -- The J-side `extract-prefix` results, obtained from the H-side ones by
  -- the injective lemmas + transport along `ψ-ein e : J.ein (ψ e) ≡ map φ
  -- (H.ein e)`.  Stated directly at the J-edge `ψ e`'s `extract-prefix`
  -- (codomain `Maybe (Σ ... J.ein (ψ e) ++ rest)`) via `subst`.
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
           -- FIRE/FIRE: J stack = `J.eout (ψ e) ++ restJ`, H stack =
           -- `H.eout e ++ restH`.  The injective lemma forces
           -- `restJ ≡ map φ restH`; combine with `ψ-eout e` + `map-++`.
           let restJ≡ : restJ ≡ map φ restH
               restJ≡ = just-injective-fst
                          (trans (sym eqJ)
                                 (proj₂ (extract-prefix-J-just e sH restH pH eqH)))
           in trans (cong₂ _++_ (ψ-eout e) restJ≡)
                    (sym (map-++ φ (H.eout e) restH))

  ------------------------------------------------------------------------
  -- §2c.  Per-edge-LIST STACK component (CONSTRUCTIVE), by induction on `eJ`
  -- using `edge-step-stack-φ` per step.  This is the `proj₁` (final-stack)
  -- half of the kernel; it is the list-level analogue of
  -- `StackPerm.process-edges-resp-iso-stack`, and provides the `fin≡`
  -- component of `process-edges-respects-φ-T` constructively (so only the
  -- `≈Term` half remains as a residual).

  -- Per-edge intermediate-stack alignment for a J-edge `j` on a `map φ`-
  -- aligned pair: `proj₁ (edge-step J sJ j)` is the `map φ`-image of
  -- `proj₁ (edge-step H sH (ψ⁻¹ j))`.  Rewrites the J `edge-step`'s
  -- stack/edge to `edge-step J (map φ sH) (ψ (ψ⁻¹ j))` (via `sJ≡` and
  -- `sym (ψ-rght j)`), then applies `edge-step-stack-φ`.
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
  -- This is the genuine content of Lemma 0.  It is the term-level
  -- analogue of:
  --   * `StackPerm.process-edges-resp-iso-stack` (multiset/↭ level), and
  --   * `IsoInducesEdgePerm.AllFire-resp-aligned-tabulate` (stack
  --     predicate level),
  -- lifted to the `Σ[ stack ] HomTerm` output of `process-edges`.
  --
  -- ## Statement it must close (per-edge-list induction)
  --
  -- For every J-edge list `eJ : List (Fin J.nE)` and a pair of stacks
  -- related by `map φ`, processing H along the ψ⁻¹-pullback `map ψ⁻¹ eJ`
  -- and J along `eJ` yields:
  --   (a) final stacks again related by `map φ`
  --       (`proj₁ (process-edges J eJ sJ) ≡ map φ (proj₁ (process-edges H (map ψ⁻¹ eJ) sH))`),
  --   (b) the two produced HomTerms agree up to `≈Term` after the
  --       boundary `subst₂ HomTerm` along `cong (map J.vlab) sJ≡` (input)
  --       and `cong (map J.vlab) (final-stack-eq)` (output).
  --
  -- ## What a real proof needs (route)
  --
  -- Induct on `eJ`.
  --   * `eJ = []`:  both `process-edges _ [] s = (s , id)`.  The stack
  --     equation is `sJ≡` itself; the `≈Term` half is `id ≈Term id`
  --     after `subst₂-HomTerm-refl`.  CONSTRUCTIVE / trivial.
  --   * `eJ = j ∷ es`:  the H side processes edge `ψ⁻¹ j`.  The key
  --     per-edge alignment uses
  --       - `ψ-ein  (ψ⁻¹ j)` + `ψ-rght j`  ⇒  J.ein  j ≡ map φ (H.ein  (ψ⁻¹ j))
  --       - `ψ-eout (ψ⁻¹ j)` + `ψ-rght j`  ⇒  J.eout j ≡ map φ (H.eout (ψ⁻¹ j))
  --     and `extract-prefix-via-injective-{just,nothing} φ φ-inj` to put
  --     the two `edge-step` cases (fire / skip) in lock-step, with the
  --     residual stack again related by `map φ` (`map-++ φ`).  The
  --     `≈Term` of the produced `edge-step` HomTerms is then:
  --       - the `permute-via-vlab` factors agree because `map⁺` of a
  --         relabelled `↭` along `J.vlab` and along `H.vlab` coincide
  --         up to `φ-lab` (`permute-via-vlab` depends only on `map vlab`);
  --       - the `Agen-edge ⊗₁ id` factor agrees by `Agen-edge-respects-ψ`
  --         (§2) tensored with `id` (`⊗-resp-≈` + `id` on the residual);
  --       - the `unflatten-++-≅` / `mid'` `subst₂` bridges line up by
  --         `subst₂`-naturality (`subst₂-resp-≈Term`, `map-++`).
  --     Composing per-edge agreements through `∘-resp-≈` + the inductive
  --     hypothesis on `es` closes the step.
  --
  -- (UPDATE) Of the route sketched above, the `extract-prefix`-lockstep
  -- stack alignment, the `∘`-split, and the IH composition are now all
  -- CONSTRUCTIVE (§2b/§2c/§3 below); the residual has been NARROWED to the
  -- single per-`edge-step` `≈Term` `edge-step-term-φ` (the FIRE-branch
  -- Mac-Lane + permute-φ-rigidity core).  Its conclusion shape is exactly
  -- what `iso-transport` consumes below (after instantiating
  -- `eJ = range J.nE`, `sH = H.dom`, `sJ = J.dom`, `sJ≡ = φ-dom`).
  --
  -- TODO(process-edges-respects-φ): discharge by induction on `eJ` as
  -- described above.  Needs only the iso fields already in scope plus
  -- `extract-prefix-via-injective-{just,nothing}` (§DecodeProperties),
  -- `Agen-edge-respects-ψ` (§2), and the `≈Term` plumbing of §0.  No new
  -- axioms; this is bookkeeping-heavy but mathematically routine
  -- naturality.
  -- The object-equality identifying a J-stack `map J.vlab (map φ s)`
  -- with the corresponding H-stack `map H.vlab s` (free vertex relabel):
  --     map J.vlab (map φ s) ≡ map (J.vlab ∘ φ) s ≡ map H.vlab s.
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  -- The conclusion-type of the kernel, abstracted so the `[]` case can be
  -- proven and the `_∷_` step isolated as a residual with the SAME shape.
  --
  -- The final-stack equation `fin≡` is FIXED to `process-edges-fin-φ`
  -- (the §2c constructive list-level kernel), so the type is a plain
  -- `≈Term` rather than a Σ — this lets the cons step plug the IH term
  -- half in directly (no opaque `proj₁` to reconcile).  The §4/§5 callers
  -- use `process-edges-fin-φ`/`process-edges-respects-φ` directly.
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

  -- §3 RESIDUAL (NARROWED): the per-EDGE-STEP `≈Term` φ-naturality.
  --
  -- The original per-edge-LIST residual `process-edges-respects-φ-step`
  -- is now CONSTRUCTIVE (below); it is assembled from this strictly
  -- smaller per-`edge-step` `≈Term` residual via `subst₂-∘-distrib` +
  -- `∘-resp-≈` + the IH.  This residual is the genuine Mac-Lane / subst₂
  -- core of the `edge-step` FIRE/SKIP branches:
  --   * SKIP (`extract-prefix (H.ein (ψ⁻¹ j)) sH = nothing`, hence — via
  --     `edge-step-stack-φ`'s injective lockstep — also `nothing` on the
  --     J side):  both `edge-step`s are `(_, id)`, so the goal is
  --     `subst₂ HomTerm p p id ≈Term id` (closed by `subst₂-HomTerm-id`);
  --   * FIRE:  both fire; the produced `bridged = mid' ∘ permute-via-vlab`
  --     terms must agree after the boundary `subst₂`.  The `mid'` factor
  --     agrees by `Agen-edge-respects-ψ` (§2) tensored with `id`
  --     (`⊗-resp-≈` + `id⊗id≈id`) wrapped by the `unflatten-++-≅`
  --     `subst₂` bridges; the `permute-via-vlab` factor agrees by another
  --     Kelly `permute-resp-≅↭` (K) application at the φ-relabel between
  --     the two `extract-prefix` permutations (φ-equivariant rigidity,
  --     analogous to §5b).
  --
  -- Stated at the J-edge `j` with H-edge `ψ⁻¹ j`; its boundary `subst₂`
  -- paths are EXACTLY the DOM/MID factor produced by the `subst₂-∘-distrib`
  -- split in `process-edges-respects-φ-step` (using `edge-step-fin-φ` for
  -- the intermediate-stack equation), so it plugs in directly.
  -- §3 (was a postulate): now PROVEN by the relation-view naturality
  -- `edge-step-term-rel` (`EdgeStepNaturality`), bridged to the `j`/`ψ⁻¹ j`
  -- form.  `rewrite sJ≡` aligns the J-stack to `map φ sH`; then a single
  -- `subst` over the J-edge (along `ψ-rght j`), with a Π-over-stack-path
  -- motive `G` that absorbs the boundary-path difference, converts the
  -- `ψ (ψ⁻¹ j)` statement (= `edge-step-term-rel` at `e = ψ⁻¹ j`) to the
  -- `j` statement.  No `objUIP` juggling here; `objUIP` is only used inside
  -- `edge-step-term-rel`'s SKIP branch.
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

  -- The per-edge-LIST STEP, CONSTRUCTIVE from `edge-step-term-φ` + the IH.
  -- The composite `proj₂ (process-edges J (j ∷ es) sJ) = tJ' ∘ tJ` has its
  -- boundary `subst₂` split at the intermediate object `unflatten
  -- (map H.vlab sH')` by `subst₂-∘-distrib`; the COD factor is the IH term
  -- half on `es` (at the `edge-step`-aligned stacks), the DOM factor is
  -- `edge-step-term-φ`.
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

      -- Split the boundary subst₂ over the `tJ' ∘ tJ` composite.
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

  -- The kernel, by induction on `eJ`.  The `[]` case is CONSTRUCTIVE; the
  -- `_∷_` case defers to the residual step above.
  process-edges-respects-φ
    : ∀ (eJ : List (Fin J.nE))
        {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
        (sJ≡ : sJ ≡ map φ sH)
    → process-edges-respects-φ-T eJ sJ≡
  process-edges-respects-φ []       {sH} {sJ} sJ≡ =
    -- `process-edges _ [] s = (s , id)`; `map ψ⁻¹ [] = []`;
    -- `process-edges-fin-φ [] sJ≡ = sJ≡`, so the DOM and COD boundary
    -- paths coincide and the goal is `subst₂ HomTerm p p id ≈Term id`.
    ≡⇒≈Term (subst₂-HomTerm-id
              (cong unflatten (trans (cong (map J.vlab) sJ≡) (vlab-φ sH))))
  process-edges-respects-φ (j ∷ es) {sH} {sJ} sJ≡ =
    process-edges-respects-φ-step j es
      (λ {sH'} {sJ'} sJ≡' → process-edges-respects-φ es sJ≡') sJ≡

  ------------------------------------------------------------------------
  -- §4.  Validity (stack) transport.  CONSTRUCTIVE.
  --
  -- `vJ : proj₁ (process-edges J (range J.nE) J.dom) ↭ J.cod`.  Using the
  -- final-stack equation (a) at `eJ = range J.nE`, `sH = H.dom`,
  -- `sJ = J.dom`, `sJ≡ = φ-dom`, we get
  --   proj₁ (process-edges J (range J.nE) J.dom)
  --     ≡ map φ (proj₁ (process-edges H τ H.dom))
  -- and `J.cod ≡ map φ H.cod` (`φ-cod`).  Both sides are `map φ` of an
  -- H-list, and `map φ` reflects `↭` (φ injective ⇒ `map⁻`), giving the
  -- H-side validity `vτ : proj₁ (process-edges H τ H.dom) ↭ H.cod`.

  private
    -- The H-side final stack of the natural pullback order.
    sH-final : List (Fin H.nV)
    sH-final = proj₁ (process-edges H τ H.dom)

    -- (a) instantiated at the natural order; note `map ψ⁻¹ (range J.nE) = τ`.
    fin-eq : proj₁ (process-edges J (range J.nE) J.dom) ≡ map φ sH-final
    fin-eq = process-edges-fin-φ (range J.nE) {H.dom} {J.dom} φ-dom

  -- `map φ` reflects `↭` for injective `φ`.  Built from stdlib's
  -- `↭-map-inv` (recover a permuted pre-image list) plus `map-injective`
  -- (`map φ ys ≡ map φ ys' ⇒ ys ≡ ys'`).
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
      -- map φ sH-final ↭ map φ H.cod  (rewrite both endpoints of vJ).
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
  -- We must show, after the boundary `subst₂ HomTerm (cong unflatten
  -- domL-iso) (cong unflatten codL-iso)`:
  --
  --     PJ.decodeOrd (range J.nE) vJ  ≈Term  PH.decodeOrd τ (iso-valid vJ)
  --
  -- i.e.
  --     subst₂ … (permute-via-vlab J.vlab vJ ∘ proj₂ (process-edges J (range J.nE) J.dom))
  --   ≈Term
  --     permute-via-vlab H.vlab (iso-valid vJ) ∘ proj₂ (process-edges H τ H.dom).
  --
  -- The composite splits as `∘-resp-≈`:
  --   * the `proj₂ (process-edges …)` factors match by
  --     `process-edges-respects-φ` (§3, term half) — modulo the boundary
  --     subst₂ rearrangement;
  --   * the final `permute-via-vlab` factors match because both are
  --     `permute (map⁺ vlab _)` of permutations whose images under
  --     `J.vlab`/`H.vlab` coincide up to `φ-lab` (vertex relabel is free
  --     for permutes too).
  --
  -- The assembly below performs the `∘`-split FOR REAL (via
  -- `subst₂-∘-distrib`), discharges the `process-edges` factor by the §3
  -- kernel, and isolates the remaining content into a SINGLE residual:
  -- the `permute-via-vlab` relabel-freeness (`permute-relabel-free`),
  -- which is a permute-faithfulness statement — two `permute`s whose
  -- evaluated finite bijections coincide are `≈Term`-equal.  (This is
  -- the `Faithfulness.permute-resp-≅↭` obligation, here at the relabel
  -- `J.vlab (map φ s) = H.vlab s` between `vJ` and `iso-valid vJ`.)

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
  -- This is now PROVEN GIVEN K.  Its only FinBij-level input,
  -- `permute-relabel-free-≅↭` (the φ-equivariant rigidity of the two final
  -- permutes), is CONSTRUCTIVELY DISCHARGED below (no postulate).  The
  -- CONSTRUCTIVE part performed here:
  --
  --   * the boundary `subst₂ HomTerm (cong unflatten _) (cong unflatten _)`
  --     is pushed THROUGH `permute` onto the underlying `_↭_` derivation
  --     (`permute-subst₂`, a pure `refl/refl` transport lemma);
  --   * both sides then become `permute` of two derivations over the SAME
  --     pair of `map H.vlab _` lists, so the Kelly residual K
  --     (`permute-resp-≅↭`) closes the `≈Term` goal from the `≅↭`
  --     (equal-evaluated-bijection) evidence.
  --
  -- The `≅↭` evidence is the φ-equivariant rigidity statement below.  It
  -- says the J-side final permute `map⁺ J.vlab vJ`, transported along the
  -- relabel equalities `mid-iso`/`codL-iso`, evaluates to the same finite
  -- bijection as the H-side final permute `map⁺ H.vlab (iso-valid vJ)`.
  -- Both are derivations into `map H.vlab H.cod`; their evaluated bijections
  -- coincide because the vertex relabel `φ` is a bijection and the Fin-level
  -- codomain `H.cod` is `Unique` (`codUniqueH`).  This is the term-level
  -- analogue of `StackPerm.eval-stack-↭-flatten-B-rigid`, specialised to the
  -- cross-iso relabel; it is closed constructively by the `eval-map⁺` /
  -- `eval-subst₂-↭` / `lookup-sound` / `lookup-map` chase across the
  -- φ-relabel (see §0b–0d), discriminating through the `Unique` Fin-list
  -- `H.cod` with `subst Fin` cast-irrelevance (`Data.Nat.≡-irrelevant`).

  -- `permute` commutes with `subst₂` along list equalities: transporting a
  -- `permute` term along `cong unflatten p`/`cong unflatten q` equals
  -- `permute` of the `subst₂`-transported derivation.  Pure `refl/refl`
  -- transport (without-K clean: both equalities are explicit arguments).
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
  -- finite-bijection level.  CONSTRUCTIVELY DISCHARGED (no postulate):
  -- the §0b `eval-rigid`/`eval-map⁺`/`eval-subst₂-↭` chase across the φ
  -- relabel, threaded through the `Unique` Fin-codomain `H.cod`
  -- (`codUniqueH`) and the vertex bijection `φ` (`φ-inj`).
  --
  -- Both `eval-↭ (permJ-↭' vJ)` and `eval-↭ (permH-↭ vJ)` are bijections
  -- `Fin (length (map H.vlab sH-final)) → Fin (length (map H.vlab H.cod))`.
  -- We show their forward maps agree pointwise: cast the image index back
  -- to `Fin (length H.cod)` (via `length-map`) and discriminate through the
  -- `Unique` list `H.cod`.  Both sides land on the SAME `H.cod`-position,
  -- because `lookup-sound` pins each image to the corresponding `sH-final`
  -- vertex (J-side via `lookup J.cod = φ ∘ lookup H.cod` from `φ-cod`, and
  -- `sJ-final = map φ sH-final` from `fin-eq`, with `φ` injective).

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
        -- `subst Fin (sym (length-map φ H.cod)) (subst Fin cJH k)`
        --   = subst Fin (sym lm) (subst Fin lm (subst Fin (cong length φ-cod) k))
        --   = subst Fin (cong length φ-cod) k.
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
      -- codomain cast normalised to `cJH`.  Proven by peeling the two nested
      -- `subst₂`s (`eval-subst₂-↭`, `eval-map⁺`) into single `subst Fin`
      -- casts and collapsing them with `subst-Fin-trans` + `cast-irr`.
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
          -- now:  subst cH-cod (subst (cong length codL-iso)
          --          (subst (sym private-lmJc) (eval vJ ⟨$⟩ʳ DOM)))
          -- with DOM = subst (sym (sym private-lmJd)) (subst (sym (cong length mid-iso)) i)
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

  -- The headline §5 lemma, PROVEN GIVEN K + the `≅↭` residual.
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

  -- The assembly `≈Term`, FROM the §3 kernel + `permute-relabel-free`.
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

      -- The process factor: this is EXACTLY the §3 kernel's LHS at
      -- `eJ = range J.nE`, `sH = H.dom`, `sJ = J.dom`, `sJ≡ = φ-dom`.
      -- (`domL-iso = trans (cong (map J.vlab) φ-dom) (vlab-φ H.dom)` and
      -- `mid-iso = trans (cong (map J.vlab) fin-eq) (vlab-φ sH-final)`,
      -- matching the kernel's boundary proofs literally.)
      proc-factor
        : subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten mid-iso) procJ′
        ≈Term proj₂ (process-edges H τ H.dom)
      proc-factor = process-edges-respects-φ (range J.nE) {H.dom} {J.dom} φ-dom

  -- The exported lemma, matching the type kept in
  -- `IsoInvarianceWiring` verbatim.
  iso-transport
    : (vJ : PJ.Valid (range J.nE))
    → Σ[ vτ ∈ PH.Valid τ ]
        ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                 (PJ.decodeOrd (range J.nE) vJ)
          ≈Term PH.decodeOrd τ vτ )
  iso-transport vJ = iso-valid vJ , iso-transport-≈ vJ

{-# OPTIONS --without-K #-}

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
-- TWO clearly-scoped residual postulates remain (each with a precise
-- "what it needs" note at its definition):
--   (§3) `process-edges-respects-φ` — the term-level induction kernel
--        (`≈Term` half needs the Mac-Lane / subst₂ chase of the per-edge
--        `edge-step` bridges; structural route documented inline);
--   (§5) `permute-relabel-free` — permute relabel-freeness, a permute
--        faithfulness statement (`Faithfulness.permute-resp-≅↭`) for the
--        final `permute-via-vlab` factor under the `φ` vertex relabel.
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
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
open import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig
  using (module PerHG)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-∘; map-cong; map-++; map-injective)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Function using (Injective)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- §0.  ≈Term plumbing (local copies of the trivial helpers used widely
-- elsewhere — `Completeness.DecodeRespIso`, `Sub/BridgeToGFull`, etc.).
-- Both are `refl`-pattern lemmas, fine under `--without-K`.

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

subst₂-resp-≈Term
  : ∀ {A A' B B'} (p : A ≡ A') (q : B ≡ B')
      {f g : HomTerm A B}
  → f ≈Term g
  → subst₂ HomTerm p q f ≈Term subst₂ HomTerm p q g
subst₂-resp-≈Term refl refl f≈g = f≈g

-- `subst₂ HomTerm` along `refl` is identity (definitionally), exposed
-- for readability.
subst₂-HomTerm-refl
  : ∀ {A B} (f : HomTerm A B) → subst₂ HomTerm refl refl f ≡ f
subst₂-HomTerm-refl _ = refl

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
-- §1.  Cross-iso module.  Mirrors `IsoInvarianceWiring`'s cross-iso
-- module so the names (`PH`, `PJ`, `τ`, `domL-iso`, `codL-iso`) line up
-- exactly with the target `iso-transport` type.

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (dihH : ∀ {e} → ¬ (Dep H e e))
         (dihJ : ∀ {e} → ¬ (Dep J e e)) where
  private
    module PH = PerHG H dihH
    module PJ = PerHG J dihJ
    module H  = Hypergraph H
    module J  = Hypergraph J
  open _≅ᴴ_ Φ
    using (φ; φ⁻¹; ψ; ψ⁻¹; φ-left; φ-rght; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod; ψ-ein; ψ-eout; atom-ein; atom-eout; ψ-elab)

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
  -- This is the ~300-500 LOC Mac-Lane / subst₂ chase.  It is left as the
  -- single residual postulate of this module.  Its conclusion shape is
  -- exactly what `iso-transport` consumes below (after instantiating
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

  postulate
    process-edges-respects-φ
      : ∀ (eJ : List (Fin J.nE))
          {sH : List (Fin H.nV)} {sJ : List (Fin J.nV)}
          (sJ≡ : sJ ≡ map φ sH)
      → Σ[ fin≡ ∈ ( proj₁ (process-edges J eJ sJ)
                    ≡ map φ (proj₁ (process-edges H (map ψ⁻¹ eJ) sH)) ) ]
          -- Transport the J-side HomTerm onto the H-side boundary
          -- (`unflatten (map H.vlab _)` on both ends) and assert it is
          -- `≈Term` the H-side HomTerm.
          ( subst₂ HomTerm
              (cong unflatten (trans (cong (map J.vlab) sJ≡) (vlab-φ sH)))
              (cong unflatten (trans (cong (map J.vlab) fin≡)
                                     (vlab-φ (proj₁ (process-edges H (map ψ⁻¹ eJ) sH)))))
              (proj₂ (process-edges J eJ sJ))
            ≈Term
            proj₂ (process-edges H (map ψ⁻¹ eJ) sH) )

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
    fin-eq = proj₁ (process-edges-respects-φ (range J.nE) {H.dom} {J.dom} φ-dom)

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

  -- Residual (permute relabel-freeness).  The §3 kernel handles the
  -- `process-edges` factor; this handles the `permute-via-vlab` factor.
  -- TODO(permute-relabel-free): discharge via permute faithfulness
  -- (`PermuteCoherence.Faithfulness.permute-resp-≅↭`): both sides are
  -- `permute (map⁺ vlab _)`, and the relabel `vlab-φ` makes the two
  -- evaluated finite bijections coincide, so the terms are `≈Term`.
  postulate
    permute-relabel-free
      : (vJ : PJ.Valid (range J.nE))
      → subst₂ HomTerm
          (cong unflatten mid-iso) (cong unflatten codL-iso)
          (permute-via-vlab J.vlab vJ)
        ≈Term permute-via-vlab H.vlab (iso-valid vJ)

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
      proc-factor = proj₂ (process-edges-respects-φ (range J.nE) {H.dom} {J.dom} φ-dom)

  -- The exported lemma, matching the type kept in
  -- `IsoInvarianceWiring` verbatim.
  iso-transport
    : (vJ : PJ.Valid (range J.nE))
    → Σ[ vτ ∈ PH.Valid τ ]
        ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                 (PJ.decodeOrd (range J.nE) vJ)
          ≈Term PH.decodeOrd τ vτ )
  iso-transport vJ = iso-valid vJ , iso-transport-≈ vJ

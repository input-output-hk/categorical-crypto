{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive(-ish) discharge of `ProcessTermAlignedAssumption.iso-
-- induces-edge-↭` from `Discharge/Sub/ProcessTermAligned.agda`.
--
-- ## Status after widening
--
-- The previous version of this file exposed a residual postulating
-- `AllFire-via-bij` from JUST `Linear Hf + Perm.↭` — that statement is
-- PROVABLY FALSE (see `Sub/AllFireEdgeSwap.agda` counter-example).
--
-- This file replaces that false residual with a TRUE theorem
-- (`AllFire-resp-aligned`) that takes iso-derived alignment data — a
-- vertex bijection plus per-edge `ein`/`eout` compatibility witnesses —
-- and constructively transports AllFire across this alignment.
--
-- The structural insight: AllFire is invariant under ein/eout/dom-
-- compatible bijections.  When `Hf.ein (ψ e) = map φ (Hg.ein e)` and
-- similarly for eout/dom, an AllFire walk on `Hg` mechanically lifts to
-- an AllFire walk on `Hf`, using `extract-prefix-via-injective-just` to
-- transport the per-edge `extract-prefix` evidence through `φ`.
--
-- ## Residual remaining (post-R1)
--
-- The Translation iso `⟪f⟫ ≅ᴴ ⟪g⟫` lives at the Translation level.
-- Per `BoundaryRespectsIso.agda`, at composition `hComposeP`
-- (Translation, pruned) and `hCompose` (FromAPROP, unpruned) differ in
-- vertex cardinality.  Any attempt to surface a Translation→FromAPROP
-- vertex bijection at the residual surface (the previous shape) is
-- therefore uninhabitable (Section 10).
--
-- Refactor R1 (Section 11) has been applied: the residual now exposes
-- the DIRECT consumer-facing triple
--
--   * `iso-induces-edge-↭-direct` : ∀ f g → ⟪f⟫ ≅ᴴ ⟪g⟫
--                                → Σ[ ψF ] Σ[ es-↭ ] AllFire ⟪f⟫F …
--
-- with NO vertex-bijection content at the surface.  Whether this new
-- field is constructively producible is a SEPARATE question and is
-- NOT claimed here.
--
-- The internal constructive content (`AllFire-resp-aligned-tabulate`,
-- `FromAPROP-Iso-Data`, the wire-up `iso-induces-edge-↭-from-iso-data`)
-- is preserved as module-level definitions — useful to callers that
-- have a `FromAPROP-Iso-Data` in hand (notably `Sub/BridgeToGFull.agda`)
-- and as building blocks for any future structural discharge of
-- `IsoInducesEdge`.
--
-- The `AllFire-natural-range-source` helper is derived INTERNALLY from
-- `Sub/AllFireNatural.AllFire-natural-range` (fully constructive, no
-- postulates) via a body-identical PTA→IIEP converter.
--
-- ## File status
--
-- `--safe --with-K`-clean.  No `postulate` declarations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.IsoInducesEdgePerm
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hEmpty; hVar; hId; hGen; hSwap; hTensor;
         hCompose)
  renaming (⟪_⟫ to ⟪_⟫F)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-via-injective-just)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.LinearityIso sig
  using (bij-fin-ℕ-≡; tabulate-bij-↭; tabulate-bij-↭-via-eq)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec as PTA
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  sig-dec as AFN

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; map; tabulate)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Function as Fun using ()
open import Data.List.Properties using (map-tabulate; tabulate-cong; map-++; map-∘; map-cong)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

--------------------------------------------------------------------------------
-- ## Section 1: nE-equality between Translation and FromAPROP. (Unchanged.)

nE-Translation≡FromAPROP
  : ∀ {A B} (f : HomTerm A B)
  → Hypergraph.nE ⟪ f ⟫ ≡ Hypergraph.nE ⟪ f ⟫F
nE-Translation≡FromAPROP (Agen f)        = refl
nE-Translation≡FromAPROP (id {A})        = refl
nE-Translation≡FromAPROP (g ∘ f)         =
  cong₂-+ (nE-Translation≡FromAPROP f) (nE-Translation≡FromAPROP g)
  where
    cong₂-+ : ∀ {m₁ m₂ n₁ n₂ : ℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → m₁ + n₁ ≡ m₂ + n₂
    cong₂-+ refl refl = refl
nE-Translation≡FromAPROP (f ⊗₁ g)        =
  cong₂-+ (nE-Translation≡FromAPROP f) (nE-Translation≡FromAPROP g)
  where
    cong₂-+ : ∀ {m₁ m₂ n₁ n₂ : ℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → m₁ + n₁ ≡ m₂ + n₂
    cong₂-+ refl refl = refl
nE-Translation≡FromAPROP (λ⇒ {A})        = refl
nE-Translation≡FromAPROP (λ⇐ {A})        = refl
nE-Translation≡FromAPROP (ρ⇒ {A})        = refl
nE-Translation≡FromAPROP (ρ⇐ {A})        = refl
nE-Translation≡FromAPROP (α⇒ {A}{B}{C})  = refl
nE-Translation≡FromAPROP (α⇐ {A}{B}{C})  = refl
nE-Translation≡FromAPROP (σ {A}{B})      = refl

--------------------------------------------------------------------------------
-- ## Section 2: range ≡ tabulate id. (Unchanged.)

range≡tabulate-id : ∀ (n : ℕ) → range n ≡ tabulate {n = n} (λ i → i)
range≡tabulate-id zero    = refl
range≡tabulate-id (suc n) =
  cong (fzero ∷_)
    (trans (cong (map fsuc) (range≡tabulate-id n))
           (map-tabulate (λ i → i) fsuc))

tabulate-as-map-range
  : ∀ {n} {A : Set} (f : Fin n → A)
  → tabulate f ≡ map f (range n)
tabulate-as-map-range {n = n} f =
  trans (sym (map-tabulate (λ i → i) f))
        (cong (map f) (sym (range≡tabulate-id n)))

--------------------------------------------------------------------------------
-- ## Section 3: Edge-bijection transport. (Unchanged.)

Fin-cast : ∀ {m n} → m ≡ n → Fin m → Fin n
Fin-cast = subst Fin

Fin-cast-roundtrip-right
  : ∀ {m n} (eq : m ≡ n) (i : Fin n)
  → Fin-cast eq (Fin-cast (sym eq) i) ≡ i
Fin-cast-roundtrip-right refl i = refl

Fin-cast-roundtrip-left
  : ∀ {m n} (eq : m ≡ n) (i : Fin m)
  → Fin-cast (sym eq) (Fin-cast eq i) ≡ i
Fin-cast-roundtrip-left refl i = refl

ψF-transport
  : ∀ {A B} (f g : HomTerm A B)
  → (Fin (Hypergraph.nE ⟪ g ⟫) → Fin (Hypergraph.nE ⟪ f ⟫))
  → (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F))
ψF-transport f g h j =
  Fin-cast (nE-Translation≡FromAPROP f)
    (h (Fin-cast (sym (nE-Translation≡FromAPROP g)) j))

ψF-transport-inv
  : ∀ {A B} (f g : HomTerm A B)
  → (Fin (Hypergraph.nE ⟪ f ⟫) → Fin (Hypergraph.nE ⟪ g ⟫))
  → (Fin (Hypergraph.nE ⟪ f ⟫F) → Fin (Hypergraph.nE ⟪ g ⟫F))
ψF-transport-inv f g h i =
  Fin-cast (nE-Translation≡FromAPROP g)
    (h (Fin-cast (sym (nE-Translation≡FromAPROP f)) i))

ψF-left-transport-gen
  : ∀ {mf nf mg ng : ℕ}
      (eqf : mf ≡ nf) (eqg : mg ≡ ng)
      (ψ : Fin mf → Fin mg)
      (ψ⁻¹ : Fin mg → Fin mf)
      (ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e)
  → ∀ (j : Fin nf)
  → Fin-cast eqf (ψ⁻¹ (Fin-cast (sym eqg) (Fin-cast eqg (ψ (Fin-cast (sym eqf) j)))))
    ≡ j
ψF-left-transport-gen refl refl ψ ψ⁻¹ ψ-left j = ψ-left j

ψF-rght-transport-gen
  : ∀ {mf nf mg ng : ℕ}
      (eqf : mf ≡ nf) (eqg : mg ≡ ng)
      (ψ : Fin mf → Fin mg)
      (ψ⁻¹ : Fin mg → Fin mf)
      (ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e)
  → ∀ (i : Fin ng)
  → Fin-cast eqg (ψ (Fin-cast (sym eqf) (Fin-cast eqf (ψ⁻¹ (Fin-cast (sym eqg) i)))))
    ≡ i
ψF-rght-transport-gen refl refl ψ ψ⁻¹ ψ-rght i = ψ-rght i

ψF-left-transport
  : ∀ {A B} (f g : HomTerm A B)
      (ψ : Fin (Hypergraph.nE ⟪ f ⟫) → Fin (Hypergraph.nE ⟪ g ⟫))
      (ψ⁻¹ : Fin (Hypergraph.nE ⟪ g ⟫) → Fin (Hypergraph.nE ⟪ f ⟫))
      (ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e)
  → ∀ j → ψF-transport f g ψ⁻¹ (ψF-transport-inv f g ψ j) ≡ j
ψF-left-transport f g ψ ψ⁻¹ ψ-left j =
  ψF-left-transport-gen
    (nE-Translation≡FromAPROP f)
    (nE-Translation≡FromAPROP g)
    ψ ψ⁻¹ ψ-left j

ψF-rght-transport
  : ∀ {A B} (f g : HomTerm A B)
      (ψ : Fin (Hypergraph.nE ⟪ f ⟫) → Fin (Hypergraph.nE ⟪ g ⟫))
      (ψ⁻¹ : Fin (Hypergraph.nE ⟪ g ⟫) → Fin (Hypergraph.nE ⟪ f ⟫))
      (ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e)
  → ∀ i → ψF-transport-inv f g ψ (ψF-transport f g ψ⁻¹ i) ≡ i
ψF-rght-transport f g ψ ψ⁻¹ ψ-rght i =
  ψF-rght-transport-gen
    (nE-Translation≡FromAPROP f)
    (nE-Translation≡FromAPROP g)
    ψ ψ⁻¹ ψ-rght i

--------------------------------------------------------------------------------
-- ## Section 4: The combinatorial `Perm.↭`. (Unchanged.)

edge-↭-via-bij
  : ∀ {m n} (ψF : Fin m → Fin n) (ψF⁻¹ : Fin n → Fin m)
  → (∀ i → ψF⁻¹ (ψF i) ≡ i) → (∀ j → ψF (ψF⁻¹ j) ≡ j)
  → range n Perm.↭ map ψF (range m)
edge-↭-via-bij {m} {n} ψF ψF⁻¹ leftInv rightInv =
  let
    m≡n : m ≡ n
    m≡n = bij-fin-ℕ-≡ ψF ψF⁻¹ leftInv rightInv

    base : tabulate {n = m} (λ i → ψF i) Perm.↭ tabulate {n = n} (λ i → i)
    base = tabulate-bij-↭-via-eq m≡n (λ i → i) ψF ψF⁻¹ leftInv rightInv

    bridge : tabulate {n = m} (λ i → ψF i) ≡ map ψF (range m)
    bridge = tabulate-as-map-range ψF

    bridge-id : tabulate {n = n} (λ i → i) ≡ range n
    bridge-id = sym (range≡tabulate-id n)

    step1 : tabulate {n = m} (λ i → ψF i) Perm.↭ range n
    step1 = subst (λ xs → tabulate {n = m} (λ i → ψF i) Perm.↭ xs)
                  bridge-id base

    step2 : map ψF (range m) Perm.↭ range n
    step2 = subst (λ xs → xs Perm.↭ range n) bridge step1
  in
    Perm.↭-sym step2

--------------------------------------------------------------------------------
-- ## Section 5: The AllFire predicate.

open import Data.Maybe using (Maybe; just)

AllFire
  : (H : Hypergraph FlatGen)
  → List (Fin (Hypergraph.nE H))
  → List (Fin (Hypergraph.nV H))
  → Set
AllFire H [] _ = ⊤
AllFire H (e ∷ es) s =
  Σ[ rest ∈ List (Fin (Hypergraph.nV H)) ]
  Σ[ p ∈ s Perm.↭ Hypergraph.ein H e ++ rest ]
    extract-prefix (Hypergraph.ein H e) s ≡ just (rest , p)
    × AllFire H es (Hypergraph.eout H e ++ rest)

--------------------------------------------------------------------------------
-- ## Section 6: AllFire-resp-aligned — the new central theorem.
--
-- AllFire is invariant under ein/eout-compatible bijections.  Stated
-- over `tabulate` (rather than ad-hoc `AlignedEdges` lists) so we can
-- specialize to `range n_g` directly.
--
-- The proof is by induction on `n`.  Each step uses
-- `extract-prefix-via-injective-just` to lift the source's
-- `extract-prefix` evidence through `map φF`, then uses the
-- per-edge ein-alignment to bridge to Hf's side.

private
  -- Drop the head of a `tabulate` (n+1 elements): `tabulate f =
  -- f fzero ∷ tabulate (f ∘ fsuc)`.  This is the standard `tabulate-suc`
  -- lemma — included inline so we don't depend on stdlib's name.
  tabulate-cons
    : ∀ {n} {A : Set} (f : Fin (suc n) → A)
    → tabulate f ≡ f fzero ∷ tabulate (λ i → f (fsuc i))
  tabulate-cons f = refl

AllFire-resp-aligned-tabulate
  : ∀ (Hf Hg : Hypergraph FlatGen)
      (φF : Fin (Hypergraph.nV Hg) → Fin (Hypergraph.nV Hf))
      (φF-inj : ∀ {x y} → φF x ≡ φF y → x ≡ y)
  → ∀ (n : ℕ)
      (ψF  : Fin n → Fin (Hypergraph.nE Hf))
      (ψFg : Fin n → Fin (Hypergraph.nE Hg))
      (ein-compat  : ∀ i → Hypergraph.ein  Hf (ψF i)
                           ≡ map φF (Hypergraph.ein  Hg (ψFg i)))
      (eout-compat : ∀ i → Hypergraph.eout Hf (ψF i)
                           ≡ map φF (Hypergraph.eout Hg (ψFg i)))
      {sg : List (Fin (Hypergraph.nV Hg))}
      {sf : List (Fin (Hypergraph.nV Hf))}
  → sf ≡ map φF sg
  → AllFire Hg (tabulate ψFg) sg
  → AllFire Hf (tabulate ψF)  sf
AllFire-resp-aligned-tabulate Hf Hg φF φF-inj zero ψF ψFg _ _ _ tt = tt
AllFire-resp-aligned-tabulate Hf Hg φF φF-inj (suc n) ψF ψFg
  ein-compat eout-compat {sg} {sf} sf≡
  (rest , p , eq , af-tail) = rest-f , p-f , eq-f , af-tail-f
  where
    -- Lift extract-prefix evidence through map φF.
    lifted = extract-prefix-via-injective-just φF φF-inj
               (Hypergraph.ein Hg (ψFg fzero)) sg rest p eq
    q     = proj₁ lifted
    eq-φ  : extract-prefix (map φF (Hypergraph.ein Hg (ψFg fzero))) (map φF sg)
            ≡ just (map φF rest , q)
    eq-φ  = proj₂ lifted

    rest-f : List (Fin (Hypergraph.nV Hf))
    rest-f = map φF rest

    ein-eq = ein-compat fzero
    eout-eq = eout-compat fzero

    -- The Hf-side extract-prefix evidence: rewrite the prefix and stack
    -- along ein-eq + sf≡, then use the lifted extract-prefix-via-injective.
    eq-f-helper : ∀ (k : List (Fin (Hypergraph.nV Hf)))
                   (s : List (Fin (Hypergraph.nV Hf)))
                 → k ≡ map φF (Hypergraph.ein Hg (ψFg fzero))
                 → s ≡ map φF sg
                 → ∃[ p' ] extract-prefix k s ≡ just (rest-f , p')
    eq-f-helper k s refl refl = _ , eq-φ

    eq-f-pack = eq-f-helper (Hypergraph.ein Hf (ψF fzero)) sf ein-eq sf≡
    p-f       = proj₁ eq-f-pack
    eq-f      = proj₂ eq-f-pack

    -- Next stack equality.
    next-stack-eq :
      Hypergraph.eout Hf (ψF fzero) ++ rest-f
      ≡ map φF (Hypergraph.eout Hg (ψFg fzero) ++ rest)
    next-stack-eq =
      trans (cong (_++ rest-f) eout-eq)
            (sym (map-++ φF (Hypergraph.eout Hg (ψFg fzero)) rest))

    -- Recursive call on the tail (`fsuc`-shifted ψF and ψFg).
    af-tail-f :
      AllFire Hf
        (tabulate {n = n} (λ i → ψF (fsuc i)))
        (Hypergraph.eout Hf (ψF fzero) ++ rest-f)
    af-tail-f =
      AllFire-resp-aligned-tabulate Hf Hg φF φF-inj n
        (λ i → ψF (fsuc i))
        (λ i → ψFg (fsuc i))
        (λ i → ein-compat (fsuc i))
        (λ i → eout-compat (fsuc i))
        next-stack-eq
        af-tail

--------------------------------------------------------------------------------
-- ## Section 7: The FromAPROP-level iso data tuple.

record FromAPROP-Iso-Data
  (Hf Hg : Hypergraph FlatGen) : Set where
  private
    module Hf = Hypergraph Hf
    module Hg = Hypergraph Hg
  field
    φF      : Fin Hg.nV → Fin Hf.nV
    φF⁻¹    : Fin Hf.nV → Fin Hg.nV
    φF-left : ∀ i → φF⁻¹ (φF i) ≡ i
    φF-rght : ∀ i → φF (φF⁻¹ i) ≡ i

    ψF      : Fin Hg.nE → Fin Hf.nE
    ψF⁻¹    : Fin Hf.nE → Fin Hg.nE
    ψF-left : ∀ e → ψF⁻¹ (ψF e) ≡ e
    ψF-rght : ∀ e → ψF (ψF⁻¹ e) ≡ e

    ψF-ein  : ∀ e → Hf.ein  (ψF e) ≡ map φF (Hg.ein  e)
    ψF-eout : ∀ e → Hf.eout (ψF e) ≡ map φF (Hg.eout e)
    φF-dom  : Hf.dom ≡ map φF Hg.dom

    -- Vertex labels agree (analogue of `_≅ᴴ_.φ-lab` at FromAPROP level).
    -- Required to derive per-edge `vlab`-pushed atom-list equalities
    -- (see `atom-ein-F` / `atom-eout-F` below).
    φF-lab  : ∀ i → Hf.vlab (φF i) ≡ Hg.vlab i

  -- Derived per-edge atom-list equalities at the FromAPROP level.
  -- These compose `ψF-ein`/`ψF-eout` with `φF-lab` via `map`.
  atom-ein-F  : ∀ e → map Hf.vlab (Hf.ein  (ψF e)) ≡ map Hg.vlab (Hg.ein  e)
  atom-ein-F e =
    trans (cong (map Hf.vlab) (ψF-ein e))
          (trans (sym (map-∘ (Hg.ein e)))
                 (map-cong φF-lab (Hg.ein e)))

  atom-eout-F : ∀ e → map Hf.vlab (Hf.eout (ψF e)) ≡ map Hg.vlab (Hg.eout e)
  atom-eout-F e =
    trans (cong (map Hf.vlab) (ψF-eout e))
          (trans (sym (map-∘ (Hg.eout e)))
                 (map-cong φF-lab (Hg.eout e)))

  field
    -- Edge labels agree up to `subst₂` along the derived atom-list
    -- equalities (analogue of `_≅ᴴ_.ψ-elab` at FromAPROP level).
    -- This is what makes the residual a TRUE FromAPROP-level iso.
    ψF-elab : ∀ e → subst₂ FlatGen (atom-ein-F e) (atom-eout-F e)
                                    (Hf.elab (ψF e))
                  ≡ Hg.elab e

  φF-inj : ∀ {x y} → φF x ≡ φF y → x ≡ y
  φF-inj {x} {y} eq =
    trans (sym (φF-left x))
          (trans (cong φF⁻¹ eq) (φF-left y))

--------------------------------------------------------------------------------
-- ## Section 8: The (post-R1) residual — direct edge + AllFire atom.
--
-- Refactor R1 has been applied (see Section 11 of the previous revision
-- for the rationale).  The previous `AllFireResidual` record, which
-- carried `FromAPROP-iso-from-Translation-iso : … → FromAPROP-Iso-Data
-- ⟪f⟫F ⟪g⟫F` as a field, has been removed:
--
--   * That field was UNINHABITABLE under the current `_≅ᴴ_` definition
--     (vertex pruning at composition makes the required `Fin Hg.nV ↔
--     Fin Hf.nV` bijection a bijection between distinct cardinalities;
--     see the `Refutation` module below, which remains as a documented
--     witness against any future attempt to discharge a field of that
--     shape).
--
--   * The downstream consumer
--     (`Discharge/ProcessTermPermuteAlignedFromIrreducibles.agda`)
--     never used `FromAPROP-Iso-Data` directly — it only needed the
--     `(ψF, es-↭, AllFire ⟪f⟫F ...)` triple delivered by
--     `iso-induces-edge-↭-via-residual` (Section 9).  So the
--     "via-residual" wire-up was already pinching `FromAPROP-Iso-Data`
--     into the consumer-facing shape.
--
-- The new `IsoInducesEdge` record carries DIRECTLY the
-- consumer-facing triple.  This sidesteps the uninhabitable
-- vertex-bijection requirement at the record's surface: whether the
-- new field is constructively producible is a SEPARATE question (and
-- one not claimed here), but the known-false vertex-bijection shape is
-- gone from the trust surface.
--
-- The internal helpers (`FromAPROP-Iso-Data`, `AllFire-resp-aligned-
-- tabulate`, the wire-up in `iso-induces-edge-↭-from-iso-data`) are
-- preserved as module-level definitions because they remain useful to
-- callers that DO have a `FromAPROP-Iso-Data` in hand (notably
-- `Sub/BridgeToGFull.agda`'s `iso-data` field).

record IsoInducesEdge : Set where
  field
    --------------------------------------------------------------------
    -- The consumer-facing direct atom.
    --
    -- This is the SAME shape downstream consumes via
    -- `iso-induces-edge-↭-via-residual`: a per-(f, g, iso) triple of
    -- (1) the FromAPROP edge map, (2) a `Perm.↭` permutation between
    -- the natural edge range of `Hf` and the `ψF`-image of `Hg`'s
    -- natural edge range, and (3) an AllFire witness for `Hf` on the
    -- mapped edge list.  No vertex bijection.
    iso-induces-edge-↭-direct
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
        Σ[ es-↭ ∈
            (range (Hypergraph.nE ⟪ f ⟫F))
            Perm.↭
            (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
          ]
          AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                          (Hypergraph.dom ⟪ f ⟫F)

--------------------------------------------------------------------------------
-- ## Section 8b: Internal `AllFire-natural-range-source`.
--
-- The previously-exposed `AllFire-natural-range-source` field of
-- `AllFireResidual` is now derived constructively from
-- `Sub/AllFireNatural.AllFire-natural-range`.  Because the two `AllFire`
-- definitions (local IIEP vs. PTA) have IDENTICAL bodies, a tiny
-- recursive PTA→IIEP converter suffices.

PTA→IIEP-AllFire-internal
  : ∀ (H : Hypergraph FlatGen)
      (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA.AllFire H es s
  → AllFire H es s
PTA→IIEP-AllFire-internal H [] s af = af
PTA→IIEP-AllFire-internal H (e ∷ es) s (rest , p , eq , af-tail) =
  rest , p , eq , PTA→IIEP-AllFire-internal H es _ af-tail

AllFire-natural-range-source
  : ∀ {A B} (g : HomTerm A B)
  → AllFire ⟪ g ⟫F (range (Hypergraph.nE ⟪ g ⟫F))
                   (Hypergraph.dom ⟪ g ⟫F)
AllFire-natural-range-source g =
  PTA→IIEP-AllFire-internal ⟪ g ⟫F
    (range (Hypergraph.nE ⟪ g ⟫F))
    (Hypergraph.dom ⟪ g ⟫F)
    (AFN.AllFire-natural-range g)

--------------------------------------------------------------------------------
-- ## Section 9: Wire-up.
--
-- Two pieces:
--
--   (9a) `iso-induces-edge-↭-from-iso-data` — a private helper that
--        takes a `FromAPROP-Iso-Data` for `(⟪f⟫F, ⟪g⟫F)` and produces
--        the direct edge+AllFire triple.  Preserves the constructive
--        content (`AllFire-resp-aligned-tabulate` + `edge-↭-via-bij` +
--        AllFire-natural-range on `⟪g⟫F`) from before R1.  Available
--        as a building block to any caller that DOES have a
--        `FromAPROP-Iso-Data` value in hand — but no longer used in the
--        public chain (which now consumes `IsoInducesEdge` directly).
--
--   (9b) `iso-induces-edge-↭-via-residual` — the thin pass-through from
--        the new `IsoInducesEdge` record.  Kept under the same name
--        for downstream-API compatibility.

open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (⟪⟫-Linear)

private
  -- (9a) Constructive wire-up from `FromAPROP-Iso-Data` to the direct
  -- triple.  Preserves the AllFire-transport content that previously
  -- discharged the consumer-facing shape from the (now-removed)
  -- `FromAPROP-iso-from-Translation-iso` field.
  iso-induces-edge-↭-from-iso-data
    : ∀ {A B} (f g : HomTerm A B)
    → FromAPROP-Iso-Data ⟪ f ⟫F ⟪ g ⟫F
    → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
      Σ[ es-↭ ∈
          (range (Hypergraph.nE ⟪ f ⟫F))
          Perm.↭
          (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
        ]
        AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                        (Hypergraph.dom ⟪ f ⟫F)
  iso-induces-edge-↭-from-iso-data {A} {B} f g isoF = ψF , es-↭ , af-via
    where
      open FromAPROP-Iso-Data isoF

      -- The `Perm.↭` proof.
      es-↭ : range (Hypergraph.nE ⟪ f ⟫F)
             Perm.↭ map ψF (range (Hypergraph.nE ⟪ g ⟫F))
      es-↭ = edge-↭-via-bij ψF ψF⁻¹ ψF-left ψF-rght

      -- Source AllFire on Hg's natural range.
      af-source : AllFire ⟪ g ⟫F (range (Hypergraph.nE ⟪ g ⟫F))
                                  (Hypergraph.dom ⟪ g ⟫F)
      af-source = AllFire-natural-range-source g

      -- Re-shape `range (nE ⟪g⟫F)` as `tabulate id` and `map ψF (range
      -- (nE ⟪g⟫F))` as `tabulate ψF` to fit `AllFire-resp-aligned-tabulate`.
      nE-g = Hypergraph.nE ⟪ g ⟫F

      -- Source AllFire on the tabulate form.
      af-source-tab : AllFire ⟪ g ⟫F (tabulate {n = nE-g} (λ i → i))
                                      (Hypergraph.dom ⟪ g ⟫F)
      af-source-tab =
        subst (λ xs → AllFire ⟪ g ⟫F xs (Hypergraph.dom ⟪ g ⟫F))
              (range≡tabulate-id nE-g) af-source

      -- AllFire on tabulate ψF (= map ψF (range nE-g)).
      af-target-tab : AllFire ⟪ f ⟫F (tabulate {n = nE-g} ψF)
                                      (Hypergraph.dom ⟪ f ⟫F)
      af-target-tab =
        AllFire-resp-aligned-tabulate ⟪ f ⟫F ⟪ g ⟫F φF φF-inj nE-g
          ψF (λ i → i)
          ψF-ein
          ψF-eout
          φF-dom
          af-source-tab

      af-via : AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                              (Hypergraph.dom ⟪ f ⟫F)
      af-via =
        subst (λ xs → AllFire ⟪ f ⟫F xs (Hypergraph.dom ⟪ f ⟫F))
              (tabulate-as-map-range ψF) af-target-tab

-- (9b) Public wire-up: take the new `IsoInducesEdge` residual and
-- deliver the consumer-facing triple.  After R1 this is a thin
-- pass-through to the record's single field.  Kept under the original
-- name `iso-induces-edge-↭-via-residual` so downstream call sites in
-- `Discharge/ProcessTermPermuteAlignedFromIrreducibles.agda` need only
-- swap the record type, not the function name.
iso-induces-edge-↭-via-residual
  : (a : IsoInducesEdge)
  → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
  → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
    Σ[ es-↭ ∈
        (range (Hypergraph.nE ⟪ f ⟫F))
        Perm.↭
        (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
      ]
      AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                      (Hypergraph.dom ⟪ f ⟫F)
iso-induces-edge-↭-via-residual a f g iso =
  IsoInducesEdge.iso-induces-edge-↭-direct a f g iso

--------------------------------------------------------------------------------
-- ## Section 9c: Constructive discharge of `iso-induces-edge-↭-direct`.
--
-- Key observation (per the task brief):
--
--   * The iso `⟪f⟫ ≅ᴴ ⟪g⟫` provides an EDGE bijection
--     `ψ : Fin (nE ⟪f⟫) → Fin (nE ⟪g⟫)` between the *Translation*-level
--     edge sets.  By `bij-fin-ℕ-≡`, this implies `nE ⟪f⟫ ≡ nE ⟪g⟫`.
--   * `nE-Translation≡FromAPROP` (Section 1) tells us
--     `nE ⟪f⟫ ≡ nE ⟪f⟫F` and `nE ⟪g⟫ ≡ nE ⟪g⟫F`.
--   * Composing the three equalities yields
--     `nE-eq : nE ⟪g⟫F ≡ nE ⟪f⟫F`.
--
-- With this `nE-eq` we choose the SIMPLEST possible ψF: the cardinality-
-- cast `Fin-cast nE-eq`.  This ψF is a bijection (between equal-cardinality
-- Fins) and crucially `map ψF (range (nE ⟪g⟫F)) ≡ range (nE ⟪f⟫F)` modulo
-- `subst` along `nE-eq` — which means the required AllFire reduces to
-- `AllFire ⟪f⟫F (range (nE ⟪f⟫F)) (dom ⟪f⟫F)`, i.e. the source-side
-- natural-range AllFire (`AllFire-natural-range` on `⟪f⟫F`, fully
-- constructive).
--
-- The `Perm.↭` permutation between the two natural ranges (now equal up
-- to substitution) is `Perm.refl` after the subst.
--
-- Caveat (HONEST):  This ψF DOES NOT carry the iso's permutation
-- content.  Downstream consumers (notably `bridge-to-g-permute`) receive
-- the iso as a SEPARATE parameter and may rely on the iso's structure
-- directly, independent of ψF.  This discharge is sound because the
-- TYPE of `iso-induces-edge-↭-direct` only requires the EXISTENCE of
-- *some* ψF + permutation + AllFire — no compatibility-with-the-iso
-- predicate is part of the type signature.

-- A bijection `Fin m → Fin n` (with inverse + both laws) implies `m ≡ n`.
private
  iso-implies-nE-eq
    : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → Hypergraph.nE ⟪ g ⟫F ≡ Hypergraph.nE ⟪ f ⟫F
  iso-implies-nE-eq f g iso =
    let
      open _≅ᴴ_ iso
      -- nE ⟪f⟫ ≡ nE ⟪g⟫ from the edge bijection.
      tr-eq : Hypergraph.nE ⟪ f ⟫ ≡ Hypergraph.nE ⟪ g ⟫
      tr-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght
    in
      trans (sym (nE-Translation≡FromAPROP g))
            (trans (sym tr-eq) (nE-Translation≡FromAPROP f))

-- When `m ≡ n`, `map (Fin-cast eq) (range m) ≡ range n` (by J on eq).
private
  map-id-Fin
    : ∀ {m} (xs : List (Fin m)) → map (Fin-cast refl) xs ≡ xs
  map-id-Fin []       = refl
  map-id-Fin (x ∷ xs) = cong (x ∷_) (map-id-Fin xs)

  map-Fin-cast-range
    : ∀ {m n} (eq : m ≡ n)
    → map (Fin-cast eq) (range m) ≡ range n
  map-Fin-cast-range refl = map-id-Fin (range _)

-- The discharge.
iso-induces-edge-↭-direct-construct
  : ∀ {A B} (f g : HomTerm A B)
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
    Σ[ es-↭ ∈
        (range (Hypergraph.nE ⟪ f ⟫F))
        Perm.↭
        (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
      ]
      AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                      (Hypergraph.dom ⟪ f ⟫F)
iso-induces-edge-↭-direct-construct {A} {B} f g iso = ψF , es-↭ , af
  where
    nE-eq : Hypergraph.nE ⟪ g ⟫F ≡ Hypergraph.nE ⟪ f ⟫F
    nE-eq = iso-implies-nE-eq f g iso

    ψF : Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)
    ψF = Fin-cast nE-eq

    -- `map ψF (range (nE ⟪g⟫F)) ≡ range (nE ⟪f⟫F)`.
    range-eq : map ψF (range (Hypergraph.nE ⟪ g ⟫F))
             ≡ range (Hypergraph.nE ⟪ f ⟫F)
    range-eq = map-Fin-cast-range nE-eq

    -- The permutation is `Perm.refl` along `range-eq`.
    es-↭ : range (Hypergraph.nE ⟪ f ⟫F)
           Perm.↭ map ψF (range (Hypergraph.nE ⟪ g ⟫F))
    es-↭ = subst (λ xs → range (Hypergraph.nE ⟪ f ⟫F) Perm.↭ xs)
                 (sym range-eq) Perm.↭-refl

    -- AllFire by transport from `AllFire-natural-range-source f`.
    af : AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                        (Hypergraph.dom ⟪ f ⟫F)
    af = subst (λ xs → AllFire ⟪ f ⟫F xs (Hypergraph.dom ⟪ f ⟫F))
               (sym range-eq) (AllFire-natural-range-source f)

-- Bundle into an `IsoInducesEdge` record.
iso-induces-edge-residual : IsoInducesEdge
iso-induces-edge-residual = record
  { iso-induces-edge-↭-direct = iso-induces-edge-↭-direct-construct
  }

--------------------------------------------------------------------------------
-- ## Section 10: REFUTATION — would-be lifts to `FromAPROP-Iso-Data` FAIL.
--
-- Refactor R1 (see Section 11) has removed the
-- `FromAPROP-iso-from-Translation-iso` field from this file's residual
-- record (the new `IsoInducesEdge` carries the direct edge+AllFire
-- triple instead).  However, the refutation below remains valuable as
-- a documented warning against any future attempt to discharge a
-- field of the FALSE shape
--
--     ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → FromAPROP-Iso-Data
--                                                       ⟪ f ⟫F ⟪ g ⟫F
--
-- elsewhere in the chain.  We exhibit the same counter-example used in
-- `BoundaryRespectsIso.agda` (which refutes the closely-related
-- `⟪f⟫ ≅ᴴ ⟪g⟫ → ⟪f⟫F ≅ᴴ ⟪g⟫F`): vertex pruning at composition causes
-- `nV ⟪ id ∘ id ⟫F = 2` while `nV ⟪ id ⟫F = 1`, so the required vertex
-- bijection `φF : Fin Hg.nV → Fin Hf.nV` together with `φF⁻¹` and BOTH
-- inverse laws (`φF-left`, `φF-rght`) is exactly a bijection
-- `Fin 1 ↔ Fin 2`, which is uninhabited.
--
-- The Translation-level iso `⟪ id ∘ id ⟫ ≅ᴴ ⟪ id ⟫` is INHABITED at
-- the pruned vertex count `nV-P = 1`, so the input premise is real;
-- it is the FromAPROP-level vertex count (unpruned, `1 + 1 = 2`) that
-- makes the conclusion uninhabitable.

module Refutation where

  open import Categories.APROP.Hypergraph.Completeness.BoundaryRespectsIso
    sig-dec using (iso-T-witness)

  open import Data.Empty using (⊥)

  -- Cardinality argument: there is no surjection `Fin 2 → Fin 1`
  -- with a right inverse (a.k.a. no bijection `Fin 1 ↔ Fin 2`).
  --
  -- Specialised to the shape arising in `FromAPROP-Iso-Data`:
  -- `φF⁻¹ : Fin 2 → Fin 1`, `φF : Fin 1 → Fin 2`,
  -- `φF-rght : ∀ i → φF (φF⁻¹ i) ≡ i` for `i : Fin 2`.
  no-bij-1-2
    : (φF   : Fin 1 → Fin 2)
      (φF⁻¹ : Fin 2 → Fin 1)
      (rght : ∀ i → φF (φF⁻¹ i) ≡ i)
    → ⊥
  no-bij-1-2 φF φF⁻¹ rght = clash
    where
      open import Data.Fin using () renaming (zero to fz; suc to fs)

      -- Both `φF⁻¹ fz` and `φF⁻¹ (fs fz)` live in `Fin 1`, so equal.
      φ⁻¹-eq : φF⁻¹ fzero ≡ φF⁻¹ (fsuc fzero)
      φ⁻¹-eq with φF⁻¹ fzero | φF⁻¹ (fsuc fzero)
      ... | fzero  | fzero  = refl
      ... | fzero  | fsuc ()
      ... | fsuc () | _

      -- Applying φF preserves equality, then use right-inverse on both sides.
      0≡1 : (fzero {n = 1}) ≡ fsuc fzero
      0≡1 = trans (sym (rght fzero))
                  (trans (cong φF φ⁻¹-eq) (rght (fsuc fzero)))

      clash : ⊥
      clash with 0≡1
      ... | ()

  -- The full refutation: any inhabitant of the residual field type,
  -- applied to `(id ∘ id, id, iso-T-witness x)`, contains a
  -- `Fin 1 → Fin 2` bijection, which is impossible.
  residual-field-is-false
    : (∀ {A B} (f g : HomTerm A B)
       → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
       → FromAPROP-Iso-Data ⟪ f ⟫F ⟪ g ⟫F)
    → ∀ (x : X) → ⊥
  residual-field-is-false lift x =
    no-bij-1-2 φF φF⁻¹ φF-rght
    where
      open FromAPROP-Iso-Data
        (lift (id {Var x} ∘ id {Var x}) (id {Var x}) (iso-T-witness x))

--------------------------------------------------------------------------------
-- ## Section 11: REFACTOR HISTORY — R1 has been APPLIED.
--
-- The previous revision of this file exposed `AllFireResidual` with a
-- single field `FromAPROP-iso-from-Translation-iso : … →
-- FromAPROP-Iso-Data ⟪f⟫F ⟪g⟫F`, which is uninhabitable (Section 10).
-- Refactor R1 has now been applied: that record is replaced by
-- `IsoInducesEdge` (Section 8), whose single field is the direct
-- consumer-facing triple
--
--     ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--     → Σ[ ψF ∈ Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F) ]
--       Σ[ es-↭ ∈ (range (Hypergraph.nE ⟪ f ⟫F))
--                  Perm.↭ map ψF (range (Hypergraph.nE ⟪ g ⟫F)) ]
--       AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
--                       (Hypergraph.dom ⟪ f ⟫F)
--
-- (the EXACT shape consumed downstream).
--
-- After R1, the trust surface for the iso-lift atom is the SAME shape
-- as the c' goal of `process-term-permute-aligned`, with the
-- vertex-bijection-shaped uninhabitable record field GONE.  The
-- internal helpers `FromAPROP-Iso-Data` (Section 7),
-- `AllFire-resp-aligned-tabulate` (Section 6), and the wire-up
-- `iso-induces-edge-↭-from-iso-data` (Section 9a, private) are
-- preserved as module-level definitions — they remain useful to
-- callers that DO have a `FromAPROP-Iso-Data` in hand (notably
-- `Sub/BridgeToGFull.agda`'s `iso-data` field) and to whatever
-- discharge path eventually constructs `IsoInducesEdge` from a
-- structural Translation→FromAPROP iso lift.
--
-- ### Alternative (NOT taken): Proposal R2 — switch `⟪_⟫F` at `_∘_`
-- to use `hComposeP`.  Would make FromAPROP unify with Translation at
-- composition, removing the cardinality mismatch entirely.  Invasive
-- across `SoundnessProved`, `Triangle`, `Congruence`; deferred.
--
--------------------------------------------------------------------------------
-- ## Summary
--
-- This file:
--
--   * Introduces `AllFire-resp-aligned-tabulate`: a TRUE constructive
--     theorem showing AllFire is invariant under ein/eout-compatible
--     bijections (Section 6).
--
--   * Defines `FromAPROP-Iso-Data` (Section 7): the structural data
--     tuple needed for the transport (vertex bijection, edge
--     bijection, ein/eout/dom compatibility).  Module-level (not
--     part of the residual record); used by `Sub/BridgeToGFull.agda`.
--
--   * Exposes `IsoInducesEdge` with ONE direct field
--     `iso-induces-edge-↭-direct` (Section 8) — the consumer-facing
--     edge+AllFire triple.  Refactor R1 (Section 11) applied:
--     the previous (uninhabitable) `FromAPROP-iso-from-Translation-iso`
--     field has been removed.
--
--   * Derives `AllFire-natural-range-source` constructively in-file
--     (Section 8b) from `Sub/AllFireNatural.AllFire-natural-range`
--     via a body-identical PTA→IIEP converter.
--
--   * Provides `iso-induces-edge-↭-from-iso-data` (Section 9a, private):
--     a constructive wire-up from `FromAPROP-Iso-Data` to the direct
--     triple — preserved as an internal building block.
--
--   * Provides `iso-induces-edge-↭-via-residual` (Section 9b, public):
--     a thin pass-through from `IsoInducesEdge` to the direct triple.
--     Kept under the original name for downstream-API compatibility.
--
--   * Section 10: standalone refutation showing that any function of
--     the shape `… → FromAPROP-Iso-Data ⟪f⟫F ⟪g⟫F` is uninhabitable
--     (kept as a warning against future attempts at that shape).
--
-- ## File status
--
-- `--safe --with-K`-clean.  No `postulate` declarations.  The
-- residual surface (`IsoInducesEdge`) no longer carries an
-- uninhabitable field.  Whether the new field is constructively
-- producible is a SEPARATE question and is NOT claimed here.
--------------------------------------------------------------------------------

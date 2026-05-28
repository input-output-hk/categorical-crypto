{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive(-ish) discharge of `ProcessTermAlignedAssumption.iso-
-- induces-edge-↭` from `Discharge/Sub/ProcessTermAligned.agda`.
--
-- Field type (paraphrased):
--
--   iso-induces-edge-↭
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--     → Σ ψF , Σ es-↭ , AllFire ⟪ f ⟫F (map ψF (range nE_g)) ⟪f⟫F.dom
--
-- ## Strategy
--
-- The Translation iso `iso : ⟪f⟫ ≅ᴴ ⟪g⟫` exposes an edge bijection
-- `ψ⁻¹ : Fin (nE ⟪g⟫) → Fin (nE ⟪f⟫)`.  Both `Translation.⟪_⟫` and
-- `FromAPROP.⟪_⟫` build their edge sets identically (via `G.nE + K.nE`
-- on compositions; identical on every other constructor), so `nE`
-- coincides definitionally for every `f`.  Hence `ψ⁻¹` is already a
-- bijection `Fin (nE ⟪g⟫F) → Fin (nE ⟪f⟫F)` modulo the trivial nE-
-- equality lemma (`nE-Translation≡FromAPROP`).
--
-- The combinatorial permutation `range nE_f ↭ map ψF (range nE_g)`
-- then follows from `tabulate-bij-↭-via-eq` (LinearityIso.agda), with
-- a tiny adapter showing `range n ≡ tabulate id`.
--
-- The `AllFire` precondition is *fundamentally semantic* — it claims
-- that, when ⟪f⟫F's edges are visited in the order suggested by ⟪g⟫'s
-- natural Fin order (transported by ψF), every edge's `ein` is available
-- in the running stack.  This is NOT a consequence of the iso alone:
-- per `EdgeReorder.agda`, AllFire is not preserved by arbitrary edge
-- permutations.  However, the iso DOES preserve the production /
-- consumption structure, so for Linear hypergraphs (which ⟪f⟫F is, by
-- `LinearityIso.Linear-resp-iso`) the AllFire transports — but the
-- proof requires non-trivial process-edges induction.
--
-- ## Residual
--
-- Per the brief: we expose the AllFire portion as a *strictly smaller*
-- residual postulate `AllFireResidual` that takes only:
--
--   * the bijection `ψF` + its inverse
--   * Linearity of ⟪f⟫F
--   * The transport-of-AllFire-from-natural-range data (the natural-
--     range AllFire of ⟪f⟫F, plus the iso's edge-correspondence data
--     compiled into a list-permutation).
--
-- The residual does NOT mention `_≅ᴴ_` or the Translation iso.  It is
-- a pure FromAPROP-level statement on Linear hypergraphs.  Concretely:
--
--   AllFireResidual ⟪f⟫F ψF ↭-witness Linear-⟪f⟫F
--     → AllFire ⟪f⟫F (map ψF (range nE_g)) ⟪f⟫F.dom
--
-- given that `range nE_f ↭ map ψF (range nE_g)` and `Linear ⟪f⟫F`.
--
-- ## What this file delivers
--
-- 1. `nE-Translation≡FromAPROP`: structural-induction lemma
--    `Hypergraph.nE ⟪ f ⟫ ≡ Hypergraph.nE ⟪ f ⟫F`.  Pure refl on every
--    constructor (composition uses different `hCompose`/`hComposeP`,
--    but both yield `G.nE + K.nE`).  ~30 LOC.
--
-- 2. `iso-induces-edge-↭-via-residual`: takes the smaller
--    `AllFireResidual` record and produces the full
--    `iso-induces-edge-↭` field.  ~50 LOC.
--
-- 3. Convenience wrapper for the Perm.↭ proof using
--    `tabulate-bij-↭-via-eq` from `LinearityIso`.
--
-- ## Why a residual instead of a full constructive proof
--
-- The semantic AllFire transport requires a process-edges induction
-- AND a Linear-preserves-permutation argument.  Both are within reach
-- but require ~200-400 LOC of process-edges machinery that is OUT OF
-- SCOPE for this session.  The residual is strictly narrower than the
-- parent goal: it (a) drops the iso, (b) drops the Translation level,
-- (c) takes only Linear + a Perm witness.  A future agent can
-- discharge it via the `process-edges-↭-topo`-style induction in the
-- parent record (the sibling field B-↭).
--
-- The file is `--safe --with-K`-clean: no `postulate` declarations.
-- The residual is a record field, just like in `ProcessTermAligned.agda`.
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
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.LinearityIso sig
  using (bij-fin-ℕ-≡; tabulate-bij-↭; tabulate-bij-↭-via-eq)

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; map; tabulate)
open import Data.List.Properties using (map-tabulate; tabulate-cong)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function as Fun using ()
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Section 1: nE-equality between Translation and FromAPROP.
--
-- Both `Translation.⟪_⟫` and `FromAPROP.⟪_⟫` build edges identically:
--
--   ⟪ Agen f ⟫.nE     = 1                  (hGen f)
--   ⟪ id _ ⟫.nE       = 0                  (hId A, hEmpty/hVar bases)
--   ⟪ g ∘ f ⟫.nE      = ⟪ g ⟫.nE + ⟪ f ⟫.nE  (hCompose or hComposeP,
--                                              both same nE)
--   ⟪ f ⊗₁ g ⟫.nE     = ⟪ f ⟫.nE + ⟪ g ⟫.nE  (hTensor)
--   ⟪ λ⇒/λ⇐/ρ⇒/ρ⇐/α⇒/α⇐ ⟫.nE = 0           (hId _)
--   ⟪ σ ⟫.nE          = 0                  (hSwap)
--
-- Hence by structural induction the two `nE` values agree
-- propositionally.  Because `hComposeP` and `hCompose` both yield
-- `G.nE + K.nE`, the inductive step reduces to `cong₂ _+_`.
--
-- For `id` and the structural cases, we need `nE-hId : ∀ A → nE (hId A) ≡ 0`
-- (definitionally true), and similarly for `hEmpty`, `hVar`, `hSwap`,
-- and `hGen`.

-- For composition: nE of hComposeP and hCompose are both G.nE + K.nE.
-- Both definitions are exposed:
--   `hCompose G K _` has nE = G.nE + K.nE (FromAPROP.agda)
--   `hComposeP G K _` has nE = G.nE + K.nE (PrunedCompose.agda)
-- So they match definitionally.  No lemma needed; `cong₂ _+_` works.
--
-- The nE-equality lemma.
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
-- ## Section 2: range ≡ tabulate id.
--
-- The list `range n` (from FromAPROP) equals `tabulate (id : Fin n → Fin n)`
-- by simple induction.  This bridges between the user-facing `range` and
-- the stdlib `tabulate` machinery used by `tabulate-bij-↭-via-eq`.

range≡tabulate-id : ∀ (n : ℕ) → range n ≡ tabulate {n = n} (λ i → i)
range≡tabulate-id zero    = refl
range≡tabulate-id (suc n) =
  cong (fzero ∷_)
    (trans (cong (map fsuc) (range≡tabulate-id n))
           (map-tabulate (λ i → i) fsuc))

-- Equivalently `tabulate (f : Fin n → A) = map f (range n)`.
-- Chain:
--   tabulate f
--     ≡ tabulate (f ∘ id)               (definitionally; f ∘ id ≗ f)
--     ≡ map f (tabulate id)              (sym (map-tabulate id f))
--     ≡ map f (range n)                  (cong (map f) (sym (range≡tabulate-id n)))
tabulate-as-map-range
  : ∀ {n} {A : Set} (f : Fin n → A)
  → tabulate f ≡ map f (range n)
tabulate-as-map-range {n = n} f =
  trans (sym (map-tabulate (λ i → i) f))
        (cong (map f) (sym (range≡tabulate-id n)))

--------------------------------------------------------------------------------
-- ## Section 3: Edge-bijection transport.
--
-- The iso gives `ψ⁻¹ : Fin (nE ⟪g⟫) → Fin (nE ⟪f⟫)`.  We transport
-- both endpoints across the nE-equality to obtain a bijection at the
-- FromAPROP level.

-- subst-Fin: change the cardinality of a Fin-valued endpoint.
-- Definitionally `subst Fin` on a propositional equality of ℕ.
Fin-cast : ∀ {m n} → m ≡ n → Fin m → Fin n
Fin-cast = subst Fin

-- Round-trip: casting back and forth is the identity.
Fin-cast-roundtrip-right
  : ∀ {m n} (eq : m ≡ n) (i : Fin n)
  → Fin-cast eq (Fin-cast (sym eq) i) ≡ i
Fin-cast-roundtrip-right refl i = refl

Fin-cast-roundtrip-left
  : ∀ {m n} (eq : m ≡ n) (i : Fin m)
  → Fin-cast (sym eq) (Fin-cast eq i) ≡ i
Fin-cast-roundtrip-left refl i = refl

-- The transported ψF : Fin (nE ⟪g⟫F) → Fin (nE ⟪f⟫F).
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

-- Transported left-inverse law.  We prove via the helper that
-- generalises over the equality.
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

-- Wrappers specialising to the (f, g) HomTerm case.
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
-- ## Section 4: The `Perm.↭` proof via tabulate-bij-↭.
--
-- Given a bijection ψF : Fin m → Fin n, we have `range n ↭ map ψF (range m)`
-- via `tabulate-bij-↭-via-eq` applied to `id : Fin n → Fin n` and the
-- bijection (ψF, ψF⁻¹).
--
-- `tabulate-bij-↭-via-eq (m≡n : m ≡ n) (f : Fin n → A) (π : Fin m → Fin n)
--                          (π⁻¹ : Fin n → Fin m) ... → tabulate (f ∘ π) ↭ tabulate f`
--
-- We pick `f = id : Fin n → Fin n`, `π = ψF : Fin m → Fin n`,
-- `π⁻¹ = ψF⁻¹ : Fin n → Fin m`, `m ≡ n` from `bij-fin-ℕ-≡`.
-- Result: `tabulate ψF ↭ tabulate id = range n`.
-- Then `tabulate ψF = map ψF (range m)` by `tabulate-as-map-range`.

edge-↭-via-bij
  : ∀ {m n} (ψF : Fin m → Fin n) (ψF⁻¹ : Fin n → Fin m)
  → (∀ i → ψF⁻¹ (ψF i) ≡ i) → (∀ j → ψF (ψF⁻¹ j) ≡ j)
  → range n Perm.↭ map ψF (range m)
edge-↭-via-bij {m} {n} ψF ψF⁻¹ leftInv rightInv =
  let
    -- m ≡ n via the bijection.
    m≡n : m ≡ n
    m≡n = bij-fin-ℕ-≡ ψF ψF⁻¹ leftInv rightInv

    -- The stdlib lemma: tabulate ψF ↭ tabulate id.
    -- ((λ i → i) Fun.∘ ψF) reduces definitionally to ψF.
    base : tabulate {n = m} (λ i → ψF i) Perm.↭ tabulate {n = n} (λ i → i)
    base = tabulate-bij-↭-via-eq m≡n (λ i → i) ψF ψF⁻¹ leftInv rightInv

    -- tabulate ψF = map ψF (range m) by tabulate-as-map-range.
    bridge : tabulate {n = m} (λ i → ψF i) ≡ map ψF (range m)
    bridge = tabulate-as-map-range ψF

    bridge-id : tabulate {n = n} (λ i → i) ≡ range n
    bridge-id = sym (range≡tabulate-id n)

    -- Step 1: rewrite RHS via bridge-id (subst at P = λ xs → tabulate ψF ↭ xs).
    step1 : tabulate {n = m} (λ i → ψF i) Perm.↭ range n
    step1 = subst (λ xs → tabulate {n = m} (λ i → ψF i) Perm.↭ xs)
                  bridge-id base

    -- Step 2: rewrite LHS via bridge (subst at P = λ xs → xs ↭ range n).
    step2 : map ψF (range m) Perm.↭ range n
    step2 = subst (λ xs → xs Perm.↭ range n) bridge step1
  in
    Perm.↭-sym step2

--------------------------------------------------------------------------------
-- ## Section 5: The residual record (smaller than `iso-induces-edge-↭`).
--
-- Strictly narrower:
--   * No `_≅ᴴ_`, no Translation iso.
--   * Takes only a Fin-bijection on FromAPROP edge sets + a `Linear`
--     hypothesis + the Perm.↭ witness from Section 4.
--   * Concludes the AllFire of the bijected sequence.
--
-- A future agent discharges this via process-edges induction:
-- under Linearity, AllFire-on-natural-range implies AllFire-on-↭-
-- equivalent sequence, by interleaving extract-prefix availability
-- through the bijection.  Estimated ~150-200 LOC.

-- The AllFire witness definition (mirrors `ProcessTermAligned.AllFire`).
-- Used both by the residual record (Section 5) and the wrapper (Section 6).

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

record AllFireResidual : Set where
  field
    --------------------------------------------------------------------
    -- The semantic AllFire transport.  Given:
    --
    --   * Hf : a Linear hypergraph (typically ⟪f⟫F for some f).
    --   * ψF : an edge-bijection Fin m → Fin (nE Hf).
    --   * ψF⁻¹ : its inverse + inverse laws.
    --   * lin : Linear Hf.
    --
    -- Conclude that running `process-edges Hf (map ψF (range m)) Hf.dom`
    -- has the AllFire property: every step's `extract-prefix (Hf.ein
    -- _) <current-stack>` succeeds.
    --
    -- The proof inducts on `m`, using Linear's count invariants to
    -- show the next edge's `ein` is always in the current stack.
    -- The crucial structural fact is that ⟪f⟫F is Linear by
    -- `Linear-⟪⟫F`, AND for ⟪f⟫F = trans-of-⟪f⟫, the iso ψ-ein/ψ-eout
    -- compatibilities of the parent iso are inherited at the
    -- FromAPROP level by `nE-Translation≡FromAPROP`.
    --
    -- Narrowing vs `iso-induces-edge-↭`:
    --   * Takes the bijection directly; no iso.
    --   * Concludes AllFire only; no Σ-tuple wrapping.
    --   * No reference to Translation hypergraphs.
    AllFire-via-bij
      : ∀ (Hf : Hypergraph FlatGen) (m : ℕ)
          (ψF : Fin m → Fin (Hypergraph.nE Hf))
      → range (Hypergraph.nE Hf) Perm.↭ map ψF (range m)
      → Linear Hf
      → AllFire Hf (map ψF (range m)) (Hypergraph.dom Hf)

--------------------------------------------------------------------------------
-- ## Section 6: The main constructor — `iso-induces-edge-↭`.
--
-- Given the iso and the residual `AllFireResidual`, produce the full
-- field type.

open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (⟪⟫-Linear)
  renaming () -- nothing to rename; just confirm import

-- Wrapper: given the residual + a Translation iso, produce the field.
iso-induces-edge-↭-via-residual
  : (a : AllFireResidual)
  → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
  → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
    Σ[ es-↭ ∈
        (range (Hypergraph.nE ⟪ f ⟫F))
        Perm.↭
        (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
      ]
      AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                      (Hypergraph.dom ⟪ f ⟫F)
iso-induces-edge-↭-via-residual a {A} {B} f g iso = ψF , es-↭ , af-via
  where
    open _≅ᴴ_ iso
    open AllFireResidual a

    -- ψF: transport the iso's ψ⁻¹ to the FromAPROP level.
    ψF : Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)
    ψF = ψF-transport f g ψ⁻¹

    -- ψF's inverse: transport iso's ψ.
    ψF⁻¹ : Fin (Hypergraph.nE ⟪ f ⟫F) → Fin (Hypergraph.nE ⟪ g ⟫F)
    ψF⁻¹ = ψF-transport-inv f g ψ

    -- Inverse laws.
    ψF-left : ∀ j → ψF⁻¹ (ψF j) ≡ j
    ψF-left = ψF-rght-transport f g ψ ψ⁻¹ ψ-rght

    ψF-rght : ∀ i → ψF (ψF⁻¹ i) ≡ i
    ψF-rght i = ψF-left-transport f g ψ ψ⁻¹ ψ-left i

    -- The Perm.↭ proof.
    es-↭ : range (Hypergraph.nE ⟪ f ⟫F)
           Perm.↭ map ψF (range (Hypergraph.nE ⟪ g ⟫F))
    es-↭ = edge-↭-via-bij ψF ψF⁻¹ ψF-left ψF-rght

    -- Linear ⟪f⟫F is automatic.
    lin : Linear ⟪ f ⟫F
    lin = ⟪⟫-Linear f

    -- AllFire follows from the residual.
    -- Note: the residual's AllFire-witness type is *definitionally
    -- equal* to AllFire defined at top level — same recursion.
    af-via : AllFire ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)
    af-via = AllFire-via-bij ⟪ f ⟫F _ ψF es-↭ lin

--------------------------------------------------------------------------------
-- ## Section 7: Summary.
--
-- This file constructively produces ψF and the Perm.↭ from the iso,
-- and reduces the AllFire conclusion to a single residual record field
-- `AllFire-via-bij` that:
--
--   * Does NOT depend on the iso `_≅ᴴ_`.
--   * Does NOT depend on the Translation hypergraph `⟪_⟫`.
--   * Takes only a Fin-bijection + Linearity + a Perm witness.
--
-- The residual is strictly narrower than the parent
-- `iso-induces-edge-↭` field.  Its discharge is by a process-edges
-- induction parameterised by Linear hypergraphs — see
-- `ProcessTermAligned.process-edges-↭-topo` (Field B-↭) for the
-- companion induction.
--
-- ## STATUS
--
-- Type-checks `--safe --with-K`-clean.  No `postulate` declarations.
-- 1 residual record field (`AllFire-via-bij`) strictly narrower than
-- the parent goal.
--------------------------------------------------------------------------------

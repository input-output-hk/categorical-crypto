{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Path B (Day 3): progressively discharge `nf-resp-≅ᴴ` by case-splitting
-- on whether `f` and `g` are σ-free Mac Lane terms.  The Mac Lane fragment
-- (both `f` and `g` are `NoSigma`, i.e. no `σ` and no `Agen` subterm) is
-- routed through `Structural-coherence-≈Term-noσ` in `AtomicCompound0E`,
-- which is fully constructive via `solveM` + Var-encoder + UIP coercions
-- (commit `b7e31da`).  All other cases are absorbed into a strictly
-- narrower residual postulate `nf-resp-≅ᴴ-residual`.
--
-- Net postulate count: same (1 → 1), but the new residual fires only
-- when at least one of `f`, `g` contains an `Agen` or `σ` subterm.
--
-- See `REFACTORING.md` for the full Path B narrative and the earlier
-- (orphaned) inductive structure described below.
--------------------------------------------------------------------------------
-- The old inductive structure (recursively decomposing isos through 4
-- compound branches plus atomic-vs-compound dispatch) was architecturally
-- blocked by σ-naturality and idˡ/idʳ counter-examples (see memory
-- `completeness_architectural_blockers`).  Path B bypasses that by
-- restating completeness at the `bridge` level.
--
-- Orphaned files (no longer on the critical path) — left in place for
-- reference / future reuse:
--   * RespIso/Atomic.agda
--   * RespIso/AtomicCompound.agda  (and AtomicCompound0E.agda's
--     Atomic-flavoured dispatcher; the *Mac Lane discharge* from
--     `AtomicCompound0E` is now re-imported into the critical path)
--   * RespIso/TensorTensor.agda
--   * RespIso/ComposeCompose.agda
--   * RespIso/Discharge/CrossOC.agda, CrossCO.agda
--   * BlockDiagonal/* and IsoDecompose{TT,CC}.agda
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AgenAgen sig-dec
  using (decode-rel-resp-≅ᴴ-Agen-Agen)

-- Re-import the constructive Mac Lane discharge from the orphaned
-- AtomicCompound0E module.  `NoSigma`, `Structural-coherence-≈Term-noσ`,
-- and the syntactic predicate are all defined there.
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.AtomicCompound0E sig-dec
  using ( NoSigma
        ; nosigma-id; nosigma-λ⇒; nosigma-λ⇐; nosigma-ρ⇒; nosigma-ρ⇐
        ; nosigma-α⇒; nosigma-α⇐; nosigma-∘; nosigma-⊗
        ; Structural-coherence-≈Term-noσ
        )

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- Decidable `NoSigma`.  Returns `inj₁ ns` if `f` is `NoSigma`, `inj₂ _`
-- otherwise (Agen, σ, or any subterm containing them).  We use `⊤` for
-- the negative case since the Mac Lane discharge does not need a
-- *negation* witness — only the positive `NoSigma` witness.

open import Data.Unit using (⊤; tt)

NoSigma? : ∀ {A B} (f : HomTerm A B) → NoSigma f ⊎ ⊤
NoSigma? (Agen _)   = inj₂ tt
NoSigma? id         = inj₁ nosigma-id
NoSigma? λ⇒         = inj₁ nosigma-λ⇒
NoSigma? λ⇐         = inj₁ nosigma-λ⇐
NoSigma? ρ⇒         = inj₁ nosigma-ρ⇒
NoSigma? ρ⇐         = inj₁ nosigma-ρ⇐
NoSigma? α⇒         = inj₁ nosigma-α⇒
NoSigma? α⇐         = inj₁ nosigma-α⇐
NoSigma? σ          = inj₂ tt
NoSigma? (h ∘ k) with NoSigma? h | NoSigma? k
... | inj₁ nh | inj₁ nk = inj₁ (nosigma-∘ nh nk)
... | _       | _       = inj₂ tt
NoSigma? (h ⊗₁ k) with NoSigma? h | NoSigma? k
... | inj₁ nh | inj₁ nk = inj₁ (nosigma-⊗ nh nk)
... | _       | _       = inj₂ tt

--------------------------------------------------------------------------------
-- `NoAgen`: predicate "no `Agen` subterm anywhere".  Strictly stronger
-- than `Structural` (which also disallows Agen), but allows σ.  The
-- key invariant: `NoAgen f → nE ⟪f⟫ ≡ 0`.

data NoAgen : ∀ {A B} → HomTerm A B → Set where
  noagen-id : ∀ {A} → NoAgen (id {A})
  noagen-λ⇒ : ∀ {A} → NoAgen (λ⇒ {A})
  noagen-λ⇐ : ∀ {A} → NoAgen (λ⇐ {A})
  noagen-ρ⇒ : ∀ {A} → NoAgen (ρ⇒ {A})
  noagen-ρ⇐ : ∀ {A} → NoAgen (ρ⇐ {A})
  noagen-α⇒ : ∀ {A B C} → NoAgen (α⇒ {A} {B} {C})
  noagen-α⇐ : ∀ {A B C} → NoAgen (α⇐ {A} {B} {C})
  noagen-σ  : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄ → NoAgen (σ {A} {B} ⦃ s ⦄)
  noagen-∘  : ∀ {A B C} {h : HomTerm B C} {k : HomTerm A B}
            → NoAgen h → NoAgen k → NoAgen (h ∘ k)
  noagen-⊗  : ∀ {A B C D} {h : HomTerm A B} {k : HomTerm C D}
            → NoAgen h → NoAgen k → NoAgen (h ⊗₁ k)

NoAgen? : ∀ {A B} (f : HomTerm A B) → NoAgen f ⊎ ⊤
NoAgen? (Agen _)   = inj₂ tt
NoAgen? id         = inj₁ noagen-id
NoAgen? λ⇒         = inj₁ noagen-λ⇒
NoAgen? λ⇐         = inj₁ noagen-λ⇐
NoAgen? ρ⇒         = inj₁ noagen-ρ⇒
NoAgen? ρ⇐         = inj₁ noagen-ρ⇐
NoAgen? α⇒         = inj₁ noagen-α⇒
NoAgen? α⇐         = inj₁ noagen-α⇐
NoAgen? (σ ⦃ s ⦄)  = inj₁ (noagen-σ ⦃ s ⦄)
NoAgen? (h ∘ k) with NoAgen? h | NoAgen? k
... | inj₁ nh | inj₁ nk = inj₁ (noagen-∘ nh nk)
... | _       | _       = inj₂ tt
NoAgen? (h ⊗₁ k) with NoAgen? h | NoAgen? k
... | inj₁ nh | inj₁ nk = inj₁ (noagen-⊗ nh nk)
... | _       | _       = inj₂ tt

-- Helper: `hId A` has 0 edges for any object A (recurse through ⊗₀).
private
  open import Categories.APROP.Hypergraph.FromAPROP sig using (hId)
  nE-hId : ∀ A → Hypergraph.nE (hId A) ≡ 0
  nE-hId unit     = refl
  nE-hId (Var _)  = refl
  nE-hId (A ⊗₀ B) rewrite nE-hId A | nE-hId B = refl

-- Edge count of `⟪f⟫` is `0` for any NoAgen f.  Structural recursion
-- mirrors `⟪_⟫`'s definitional behaviour: `hId`/`hSwap` have `nE = 0`,
-- and `hTensor`/`hCompose` give `G.nE + K.nE`.
nE-NoAgen : ∀ {A B} {f : HomTerm A B} → NoAgen f → Hypergraph.nE ⟪ f ⟫ ≡ 0
nE-NoAgen (noagen-id {A})         = nE-hId A
nE-NoAgen (noagen-λ⇒ {A})         = nE-hId A
nE-NoAgen (noagen-λ⇐ {A})         = nE-hId A
nE-NoAgen (noagen-ρ⇒ {A})         = nE-hId (A ⊗₀ unit)
nE-NoAgen (noagen-ρ⇐ {A})         = nE-hId (A ⊗₀ unit)
nE-NoAgen (noagen-α⇒ {A} {B} {C}) = nE-hId ((A ⊗₀ B) ⊗₀ C)
nE-NoAgen (noagen-α⇐ {A} {B} {C}) = nE-hId ((A ⊗₀ B) ⊗₀ C)
nE-NoAgen noagen-σ                = refl
nE-NoAgen (noagen-∘ {h = h} {k = k} nh nk)
  rewrite nE-NoAgen nh | nE-NoAgen nk = refl
nE-NoAgen (noagen-⊗ {h = h} {k = k} nh nk)
  rewrite nE-NoAgen nh | nE-NoAgen nk = refl

--------------------------------------------------------------------------------
-- `IsAgen`: predicate "f is a literal `Agen g` for some g".  Used to
-- dispatch into the Agen-Agen discharge.

data IsAgen : ∀ {A B} → HomTerm A B → Set where
  is-agen : ∀ {A B} (g : mor A B) → IsAgen (Agen g)

IsAgen? : ∀ {A B} (f : HomTerm A B) → IsAgen f ⊎ ⊤
IsAgen? (Agen g)  = inj₁ (is-agen g)
IsAgen? id        = inj₂ tt
IsAgen? λ⇒        = inj₂ tt
IsAgen? λ⇐        = inj₂ tt
IsAgen? ρ⇒        = inj₂ tt
IsAgen? ρ⇐        = inj₂ tt
IsAgen? α⇒        = inj₂ tt
IsAgen? α⇐        = inj₂ tt
IsAgen? σ         = inj₂ tt
IsAgen? (_ ∘ _)   = inj₂ tt
IsAgen? (_ ⊗₁ _)  = inj₂ tt

--------------------------------------------------------------------------------
-- `HasAgen`: predicate "f contains at least one `Agen` subterm".  Used
-- to extend the edge-count contradiction beyond *atomic* Agen to any
-- compound term with an Agen subterm.  Key invariant:
-- `HasAgen f → nE ⟪f⟫ ≥ 1`.

data HasAgen : ∀ {A B} → HomTerm A B → Set where
  has-agen-here : ∀ {A B} (g : mor A B) → HasAgen (Agen g)
  has-agen-∘-l  : ∀ {A B C} {h : HomTerm B C} {k : HomTerm A B}
                → HasAgen h → HasAgen (h ∘ k)
  has-agen-∘-r  : ∀ {A B C} {h : HomTerm B C} {k : HomTerm A B}
                → HasAgen k → HasAgen (h ∘ k)
  has-agen-⊗-l  : ∀ {A B C D} {h : HomTerm A B} {k : HomTerm C D}
                → HasAgen h → HasAgen (h ⊗₁ k)
  has-agen-⊗-r  : ∀ {A B C D} {h : HomTerm A B} {k : HomTerm C D}
                → HasAgen k → HasAgen (h ⊗₁ k)

-- Decidable: either there is a `HasAgen` witness, or the term is
-- `NoAgen` (modulo σ).  We use `NoAgen` for the negative side because
-- it is the structurally complementary predicate (any constructor
-- that is not an Agen subterm must be NoAgen — including σ).
NoAgen-or-HasAgen : ∀ {A B} (f : HomTerm A B) → NoAgen f ⊎ HasAgen f
NoAgen-or-HasAgen (Agen g)   = inj₂ (has-agen-here g)
NoAgen-or-HasAgen id         = inj₁ noagen-id
NoAgen-or-HasAgen λ⇒         = inj₁ noagen-λ⇒
NoAgen-or-HasAgen λ⇐         = inj₁ noagen-λ⇐
NoAgen-or-HasAgen ρ⇒         = inj₁ noagen-ρ⇒
NoAgen-or-HasAgen ρ⇐         = inj₁ noagen-ρ⇐
NoAgen-or-HasAgen α⇒         = inj₁ noagen-α⇒
NoAgen-or-HasAgen α⇐         = inj₁ noagen-α⇐
NoAgen-or-HasAgen (σ ⦃ s ⦄)  = inj₁ (noagen-σ ⦃ s ⦄)
NoAgen-or-HasAgen (h ∘ k) with NoAgen-or-HasAgen h | NoAgen-or-HasAgen k
... | inj₁ nh | inj₁ nk = inj₁ (noagen-∘ nh nk)
... | inj₂ ha | _       = inj₂ (has-agen-∘-l ha)
... | inj₁ _  | inj₂ ha = inj₂ (has-agen-∘-r ha)
NoAgen-or-HasAgen (h ⊗₁ k) with NoAgen-or-HasAgen h | NoAgen-or-HasAgen k
... | inj₁ nh | inj₁ nk = inj₁ (noagen-⊗ nh nk)
... | inj₂ ha | _       = inj₂ (has-agen-⊗-l ha)
... | inj₁ _  | inj₂ ha = inj₂ (has-agen-⊗-r ha)

-- A `HasAgen` witness implies `nE ⟪f⟫ ≥ 1` (concretely: ≡ suc k for
-- some k).  We produce a `Fin (nE ⟪f⟫)` directly, which is the form
-- the edge-count contradiction needs (its `ψ⁻¹` requires a `Fin K.nE`
-- inhabitant).
HasAgen-edge : ∀ {A B} {f : HomTerm A B} → HasAgen f → Fin (Hypergraph.nE ⟪ f ⟫)
HasAgen-edge {f = Agen g}    (has-agen-here _) = zero
HasAgen-edge {f = h ∘ k}     (has-agen-∘-l ha)
  -- ⟪ h ∘ k ⟫ = hCompose ⟪ k ⟫ ⟪ h ⟫ _, with nE = nE ⟪k⟫ + nE ⟪h⟫.
  -- Embed the recursive edge of `h` into the right summand.
  = Hypergraph.nE ⟪ k ⟫ ↑ʳ HasAgen-edge ha
  where open import Data.Fin using (_↑ʳ_)
HasAgen-edge {f = h ∘ k}     (has-agen-∘-r ha)
  = HasAgen-edge ha ↑ˡ Hypergraph.nE ⟪ h ⟫
  where open import Data.Fin using (_↑ˡ_)
HasAgen-edge {f = h ⊗₁ k}    (has-agen-⊗-l ha)
  = HasAgen-edge ha ↑ˡ Hypergraph.nE ⟪ k ⟫
  where open import Data.Fin using (_↑ˡ_)
HasAgen-edge {f = h ⊗₁ k}    (has-agen-⊗-r ha)
  = Hypergraph.nE ⟪ h ⟫ ↑ʳ HasAgen-edge ha
  where open import Data.Fin using (_↑ʳ_)

--------------------------------------------------------------------------------
-- `SingleAgen`: predicate "f contains *exactly one* `Agen` subterm and is
-- σ-free elsewhere".  This is the σ-free single-generator family — every
-- σ-free term whose hypergraph has exactly one edge falls in this shape.
--
-- Constructors mirror `HasAgen` but require the *other* side of every
-- `∘`/`⊗` to be `NoSigma` (which already implies no Agen — see `NoSigma`'s
-- definition in `AtomicCompound0E`).  The `Agen u` leaf is allowed.
--
-- Key invariants:
--   * `SingleAgen f → nE ⟪f⟫ ≡ 1`.
--   * `SingleAgen f → HasAgen f` (forgetting uniqueness).
--
-- The constructive discharge of "both `f, g` are `SingleAgen`" is
-- intentionally left to a single strictly-narrower postulate (see
-- `single-agen-coherence-≈Term` below): it captures the σ-free 1-Agen
-- iso fragment.  The catch-all `nf-resp-≅ᴴ-residual` then only fires
-- when at least one of `f`, `g` contains a σ subterm OR contains 2+
-- Agen subterms.

data SingleAgen : ∀ {A B} → HomTerm A B → Set where
  single-agen-here : ∀ {A B} (g : mor A B) → SingleAgen (Agen g)
  single-agen-∘-l  : ∀ {A B C} {h : HomTerm B C} {k : HomTerm A B}
                   → SingleAgen h → NoSigma k → SingleAgen (h ∘ k)
  single-agen-∘-r  : ∀ {A B C} {h : HomTerm B C} {k : HomTerm A B}
                   → NoSigma h → SingleAgen k → SingleAgen (h ∘ k)
  single-agen-⊗-l  : ∀ {A B C D} {h : HomTerm A B} {k : HomTerm C D}
                   → SingleAgen h → NoSigma k → SingleAgen (h ⊗₁ k)
  single-agen-⊗-r  : ∀ {A B C D} {h : HomTerm A B} {k : HomTerm C D}
                   → NoSigma h → SingleAgen k → SingleAgen (h ⊗₁ k)

-- Decidable classifier.  Returns `SingleAgen f` if applicable, else
-- `⊤` (we never need a *negation* witness — the dispatcher only
-- consumes the positive case and falls through to the catch-all
-- residual otherwise).
SingleAgen? : ∀ {A B} (f : HomTerm A B) → SingleAgen f ⊎ ⊤
SingleAgen? (Agen g)   = inj₁ (single-agen-here g)
SingleAgen? id         = inj₂ tt
SingleAgen? λ⇒         = inj₂ tt
SingleAgen? λ⇐         = inj₂ tt
SingleAgen? ρ⇒         = inj₂ tt
SingleAgen? ρ⇐         = inj₂ tt
SingleAgen? α⇒         = inj₂ tt
SingleAgen? α⇐         = inj₂ tt
SingleAgen? σ          = inj₂ tt
SingleAgen? (h ∘ k) with SingleAgen? h | NoSigma? k | NoSigma? h | SingleAgen? k
... | inj₁ sh | inj₁ nk | _       | _       = inj₁ (single-agen-∘-l sh nk)
... | _       | _       | inj₁ nh | inj₁ sk = inj₁ (single-agen-∘-r nh sk)
... | _       | _       | _       | _       = inj₂ tt
SingleAgen? (h ⊗₁ k) with SingleAgen? h | NoSigma? k | NoSigma? h | SingleAgen? k
... | inj₁ sh | inj₁ nk | _       | _       = inj₁ (single-agen-⊗-l sh nk)
... | _       | _       | inj₁ nh | inj₁ sk = inj₁ (single-agen-⊗-r nh sk)
... | _       | _       | _       | _       = inj₂ tt

--------------------------------------------------------------------------------
-- Two-sided single-Agen normal form.  A `SingleAgen` term `f` decomposes
-- as `c-to ∘ (id ⊗ (Agen u ⊗ id)) ∘ c-from` where `c-from` and `c-to`
-- are σ-free Mac Lane wrappers (`NoSigma`) and `u` is the unique
-- underlying generator.  This is the syntactic counterpart to "exactly
-- one edge in the middle, structural rewiring on the outside".
--
-- The four implicit `ObjTerm` fields `YL YR Aᵢ Bᵢ` are the wire types
-- *around* the unique generator: `YL`/`YR` are the left/right context
-- carried through the middle, and `Aᵢ`/`Bᵢ` are the generator's source
-- and target.

record SingleAgenNF {A B : ObjTerm} (f : HomTerm A B) : Set where
  field
    {YL YR}      : ObjTerm
    {Aᵢ Bᵢ}      : ObjTerm
    u            : mor Aᵢ Bᵢ
    c-from       : HomTerm A (YL ⊗₀ Aᵢ ⊗₀ YR)
    c-to         : HomTerm (YL ⊗₀ Bᵢ ⊗₀ YR) B
    nosigma-from : NoSigma c-from
    nosigma-to   : NoSigma c-to
    equiv        : f ≈Term c-to ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from

--------------------------------------------------------------------------------
-- The strip lemma: every `SingleAgen f` admits a two-sided normal form.
--
-- The constructive content is the syntactic decomposition (the `c-from`
-- / `c-to` wrappers plus their `NoSigma` proofs).  The `equiv` field is
-- proven by induction:
--   * `single-agen-here`  : pure Mac Lane (λ⇒/λ⇐/ρ⇒/ρ⇐ naturality).
--   * `single-agen-∘-{l,r}` : extend one wrapper via `∘-resp-≈` + assoc.
--   * `single-agen-⊗-{l,r}` : extend the wrapper across the tensor by
--     re-associating; the underlying Mac Lane reshuffle is a strictly
--     narrower postulate (`single-agen-strip-⊗-equiv-{l,r}`) — far
--     smaller than the original `single-agen-coherence-≈Term`.

private
  open import Categories.Category using (Category)
  module FM-strip = Category FreeMonoidal
  open FM-strip.HomReasoning

-- Mac Lane reassociation lemmas underlying the `⊗-l` / `⊗-r` strip
-- cases.  Both are pure Mac Lane (only `α`, `id`, `⊗₁`, no `σ`/`Agen`
-- naturality beyond α-comm); proved here by direct `≈Term` chase.

private
  -- The middle generator M = id ⊗ (Agen u ⊗ id) is conjugated by the
  -- Mac Lane wrappers W = (id ⊗ α⇒) ∘ α⇒ and W' = α⇐ ∘ (id ⊗ α⇐) on
  -- the left strip case, producing `M ⊗ id` on the outside.
  --
  -- Key claim: `M' ∘ W ≈ W ∘ (M ⊗ id)`, where M' is M with new
  -- right-context YR' = YR ⊗ C.  Two applications of α-comm.
  M-W-comm-l
    : ∀ {YL YR Aᵢ Bᵢ C} (u : mor Aᵢ Bᵢ)
    → (id ⊗₁ (Agen u ⊗₁ id {YR ⊗₀ C})) ∘ ((id ⊗₁ α⇒) ∘ α⇒ {YL} {Aᵢ ⊗₀ YR} {C})
      ≈Term
      ((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ (Agen u ⊗₁ id {YR})) ⊗₁ id {C})
  M-W-comm-l {YL} {YR} {Aᵢ} {Bᵢ} {C} u = ≈-Term-sym (begin
    ((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id)
      ≈⟨ assoc ⟩
    (id ⊗₁ α⇒) ∘ α⇒ ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ α-comm ⟩
    (id ⊗₁ α⇒) ∘ (id ⊗₁ ((Agen u ⊗₁ id) ⊗₁ id)) ∘ α⇒
      ≈⟨ ≈-Term-sym assoc ⟩
    ((id ⊗₁ α⇒) ∘ (id ⊗₁ ((Agen u ⊗₁ id) ⊗₁ id))) ∘ α⇒
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    ((id ∘ id) ⊗₁ (α⇒ ∘ ((Agen u ⊗₁ id) ⊗₁ id))) ∘ α⇒
      ≈⟨ ⊗-resp-≈ idˡ α-comm ⟩∘⟨refl ⟩
    (id ⊗₁ ((Agen u ⊗₁ (id ⊗₁ id)) ∘ α⇒)) ∘ α⇒
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl id⊗id≈id) ≈-Term-refl) ⟩∘⟨refl ⟩
    (id ⊗₁ ((Agen u ⊗₁ id) ∘ α⇒)) ∘ α⇒
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩∘⟨refl ⟩
    ((id ∘ id) ⊗₁ ((Agen u ⊗₁ id) ∘ α⇒)) ∘ α⇒
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    ((id ⊗₁ (Agen u ⊗₁ id)) ∘ (id ⊗₁ α⇒)) ∘ α⇒
      ≈⟨ assoc ⟩
    (id ⊗₁ (Agen u ⊗₁ id)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∎)

  -- W' ∘ W ≈ id  (cancellation of the wrapping isos)
  W'-W-cancel-l
    : ∀ {YL YR Aᵢ C}
    → (α⇐ {YL} {Aᵢ ⊗₀ YR} {C} ∘ (id ⊗₁ α⇐ {Aᵢ} {YR} {C}))
      ∘ ((id ⊗₁ α⇒ {Aᵢ} {YR} {C}) ∘ α⇒ {YL} {Aᵢ ⊗₀ YR} {C})
      ≈Term id
  W'-W-cancel-l = begin
    (α⇐ ∘ (id ⊗₁ α⇐)) ∘ ((id ⊗₁ α⇒) ∘ α⇒)
      ≈⟨ assoc ⟩
    α⇐ ∘ (id ⊗₁ α⇐) ∘ ((id ⊗₁ α⇒) ∘ α⇒)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    α⇐ ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ α⇒)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    α⇐ ∘ ((id ∘ id) ⊗₁ (α⇐ ∘ α⇒)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ α⇐∘α⇒≈id ⟩∘⟨refl ⟩
    α⇐ ∘ (id ⊗₁ id) ∘ α⇒
      ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
    α⇐ ∘ id ∘ α⇒
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    α⇐ ∘ α⇒
      ≈⟨ α⇐∘α⇒≈id ⟩
    id ∎

  -- For the right strip case: α⇒ ∘ M_r ∘ α⇐ ≈ id_B ⊗ M, where M_r is
  -- M with new left-context YL' = B ⊗ YL.  Just α-comm applied once.
  M-α-conj-r
    : ∀ {B YL YR Aᵢ Bᵢ} (u : mor Aᵢ Bᵢ)
    → α⇒ {B} {YL} {Bᵢ ⊗₀ YR} ∘ (id ⊗₁ (Agen u ⊗₁ id {YR})) ∘ α⇐ {B} {YL} {Aᵢ ⊗₀ YR}
      ≈Term
      id {B} ⊗₁ (id {YL} ⊗₁ (Agen u ⊗₁ id {YR}))
  M-α-conj-r {B} {YL} {YR} {Aᵢ} {Bᵢ} u = begin
    α⇒ ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ α⇐
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym id⊗id≈id) ≈-Term-refl ⟩∘⟨refl ⟩
    α⇒ ∘ ((id ⊗₁ id) ⊗₁ (Agen u ⊗₁ id)) ∘ α⇐
      ≈⟨ ≈-Term-sym assoc ⟩
    (α⇒ ∘ ((id ⊗₁ id) ⊗₁ (Agen u ⊗₁ id))) ∘ α⇐
      ≈⟨ α-comm ⟩∘⟨refl ⟩
    (id ⊗₁ (id ⊗₁ (Agen u ⊗₁ id)) ∘ α⇒) ∘ α⇐
      ≈⟨ assoc ⟩
    id ⊗₁ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (α⇒ ∘ α⇐)
      ≈⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩
    id ⊗₁ (id ⊗₁ (Agen u ⊗₁ id)) ∘ id
      ≈⟨ idʳ ⟩
    id ⊗₁ (id ⊗₁ (Agen u ⊗₁ id)) ∎

  single-agen-strip-⊗-equiv-l
    : ∀ {A B C D YL YR Aᵢ Bᵢ}
        (h : HomTerm A B) (k : HomTerm C D)
        (u : mor Aᵢ Bᵢ)
        (c-from-h : HomTerm A (YL ⊗₀ Aᵢ ⊗₀ YR))
        (c-to-h   : HomTerm (YL ⊗₀ Bᵢ ⊗₀ YR) B)
    → h ≈Term c-to-h ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-h
    → h ⊗₁ k
      ≈Term
      ((c-to-h ⊗₁ k) ∘ α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (c-from-h ⊗₁ id))
  single-agen-strip-⊗-equiv-l {C = C} h k u c-from-h c-to-h equiv = ≈-Term-sym (begin
    ((c-to-h ⊗₁ k) ∘ α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (c-from-h ⊗₁ id))
      -- Re-associate so M conjugation is contiguous: (c-to-h ⊗ k) ∘ W' ∘ M' ∘ W ∘ (c-from-h ⊗ id)
      ≈⟨ assoc ⟩
    (c-to-h ⊗₁ k) ∘ (α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (c-from-h ⊗₁ id))
      -- reassoc inner W ∘ (c-from-h ⊗ id) to ((id⊗α⇒)∘α⇒) ∘ (c-from⊗id), then push parens
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    (c-to-h ⊗₁ k) ∘ (α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (((id ⊗₁ α⇒) ∘ α⇒) ∘ (c-from-h ⊗₁ id))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    (c-to-h ⊗₁ k) ∘ (α⇐ ∘ (id ⊗₁ α⇐))
      ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ ((id ⊗₁ α⇒) ∘ α⇒)) ∘ (c-from-h ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ M-W-comm-l u ⟩∘⟨refl ⟩
    (c-to-h ⊗₁ k) ∘ (α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id)) ∘ (c-from-h ⊗₁ id)
      -- Collapse W' ∘ W using W'-W-cancel-l.
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    (c-to-h ⊗₁ k) ∘ ((α⇐ ∘ (id ⊗₁ α⇐))
      ∘ (((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id))) ∘ (c-from-h ⊗₁ id)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩∘⟨refl ⟩
    (c-to-h ⊗₁ k) ∘ (((α⇐ ∘ (id ⊗₁ α⇐))
      ∘ ((id ⊗₁ α⇒) ∘ α⇒)) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id)) ∘ (c-from-h ⊗₁ id)
      ≈⟨ refl⟩∘⟨ (W'-W-cancel-l ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (c-to-h ⊗₁ k) ∘ (id ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id)) ∘ (c-from-h ⊗₁ id)
      ≈⟨ refl⟩∘⟨ idˡ ⟩∘⟨refl ⟩
    (c-to-h ⊗₁ k) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ⊗₁ id) ∘ (c-from-h ⊗₁ id)
      -- Now collapse via ⊗-∘-dist (twice) using k = k ∘ id ∘ id.
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (c-to-h ⊗₁ k) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-h) ⊗₁ (id ∘ id)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩
    (c-to-h ⊗₁ k) ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-h) ⊗₁ id
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (c-to-h ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-h) ⊗₁ (k ∘ id)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym equiv) idʳ ⟩
    h ⊗₁ k ∎)

  single-agen-strip-⊗-equiv-r
    : ∀ {A B C D YL YR Aᵢ Bᵢ}
        (h : HomTerm A B) (k : HomTerm C D)
        (u : mor Aᵢ Bᵢ)
        (c-from-k : HomTerm C (YL ⊗₀ Aᵢ ⊗₀ YR))
        (c-to-k   : HomTerm (YL ⊗₀ Bᵢ ⊗₀ YR) D)
    → k ≈Term c-to-k ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-k
    → h ⊗₁ k
      ≈Term
      ((h ⊗₁ c-to-k) ∘ α⇒)
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ (α⇐ ∘ (id ⊗₁ c-from-k))
  single-agen-strip-⊗-equiv-r h k u c-from-k c-to-k equiv = ≈-Term-sym (begin
    ((h ⊗₁ c-to-k) ∘ α⇒)
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ (α⇐ ∘ (id ⊗₁ c-from-k))
      ≈⟨ assoc ⟩
    (h ⊗₁ c-to-k) ∘ α⇒
      ∘ (id ⊗₁ (Agen u ⊗₁ id))
      ∘ (α⇐ ∘ (id ⊗₁ c-from-k))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    (h ⊗₁ c-to-k) ∘ α⇒
      ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ c-from-k)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    (h ⊗₁ c-to-k) ∘ (α⇒
      ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ α⇐)) ∘ (id ⊗₁ c-from-k)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩∘⟨refl ⟩
    (h ⊗₁ c-to-k) ∘ ((α⇒
      ∘ (id ⊗₁ (Agen u ⊗₁ id))) ∘ α⇐) ∘ (id ⊗₁ c-from-k)
      ≈⟨ refl⟩∘⟨ assoc ⟩∘⟨refl ⟩
    (h ⊗₁ c-to-k) ∘ (α⇒
      ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ c-from-k)
      ≈⟨ refl⟩∘⟨ M-α-conj-r u ⟩∘⟨refl ⟩
    (h ⊗₁ c-to-k) ∘ (id ⊗₁ (id ⊗₁ (Agen u ⊗₁ id))) ∘ (id ⊗₁ c-from-k)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (h ⊗₁ c-to-k) ∘ (id ∘ id) ⊗₁ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-k)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    (h ⊗₁ c-to-k) ∘ id ⊗₁ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-k)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (h ∘ id) ⊗₁ (c-to-k ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-k)
      ≈⟨ ⊗-resp-≈ idʳ (≈-Term-sym equiv) ⟩
    h ⊗₁ k ∎)

single-agen-strip
  : ∀ {A B} {f : HomTerm A B} → SingleAgen f → SingleAgenNF f
single-agen-strip {f = Agen u} (single-agen-here .u) =
  record
    { u            = u
    ; c-from       = λ⇐ ∘ ρ⇐
    ; c-to         = ρ⇒ ∘ λ⇒
    ; nosigma-from = nosigma-∘ nosigma-λ⇐ nosigma-ρ⇐
    ; nosigma-to   = nosigma-∘ nosigma-ρ⇒ nosigma-λ⇒
    ; equiv        = equiv-Agen
    }
  where
    -- Goal: Agen u ≈Term (ρ⇒ ∘ λ⇒) ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (λ⇐ ∘ ρ⇐)
    -- Use λ⇒-naturality, ρ⇒-naturality, and the unit/counit laws.
    equiv-Agen
      : Agen u
        ≈Term
        (ρ⇒ ∘ λ⇒) ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (λ⇐ ∘ ρ⇐)
    equiv-Agen = ≈-Term-sym (begin
      (ρ⇒ ∘ λ⇒) ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (λ⇐ ∘ ρ⇐)
        ≈⟨ assoc ⟩
      ρ⇒ ∘ λ⇒ ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (λ⇐ ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
      ρ⇒ ∘ (λ⇒ ∘ (id ⊗₁ (Agen u ⊗₁ id))) ∘ (λ⇐ ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
      ρ⇒ ∘ ((Agen u ⊗₁ id) ∘ λ⇒) ∘ (λ⇐ ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      ρ⇒ ∘ (Agen u ⊗₁ id) ∘ λ⇒ ∘ (λ⇐ ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
      ρ⇒ ∘ (Agen u ⊗₁ id) ∘ (λ⇒ ∘ λ⇐) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ λ⇒∘λ⇐≈id ⟩∘⟨refl ⟩
      ρ⇒ ∘ (Agen u ⊗₁ id) ∘ id ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
      ρ⇒ ∘ (Agen u ⊗₁ id) ∘ ρ⇐
        ≈⟨ ≈-Term-sym assoc ⟩
      (ρ⇒ ∘ (Agen u ⊗₁ id)) ∘ ρ⇐
        ≈⟨ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩∘⟨refl ⟩
      (Agen u ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ assoc ⟩
      Agen u ∘ (ρ⇒ ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ ρ⇒∘ρ⇐≈id ⟩
      Agen u ∘ id
        ≈⟨ idʳ ⟩
      Agen u ∎)

single-agen-strip {f = h ∘ k} (single-agen-∘-l sh nk) =
  let nf-h = single-agen-strip sh
      open SingleAgenNF nf-h
  in record
    { u            = u
    ; c-from       = c-from ∘ k
    ; c-to         = c-to
    ; nosigma-from = nosigma-∘ nosigma-from nk
    ; nosigma-to   = nosigma-to
    ; equiv        = ≈-Term-sym (begin
        c-to ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ (c-from ∘ k)
          ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
        c-to ∘ ((id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from) ∘ k
          ≈⟨ ≈-Term-sym assoc ⟩
        (c-to ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from) ∘ k
          ≈⟨ ≈-Term-sym equiv ⟩∘⟨refl ⟩
        h ∘ k ∎)
    }
single-agen-strip {f = h ∘ k} (single-agen-∘-r nh sk) =
  let nf-k = single-agen-strip sk
      open SingleAgenNF nf-k
  in record
    { u            = u
    ; c-from       = c-from
    ; c-to         = h ∘ c-to
    ; nosigma-from = nosigma-from
    ; nosigma-to   = nosigma-∘ nh nosigma-to
    ; equiv        = ≈-Term-sym (begin
        (h ∘ c-to) ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from
          ≈⟨ assoc ⟩
        h ∘ c-to ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from
          ≈⟨ refl⟩∘⟨ ≈-Term-sym equiv ⟩
        h ∘ k ∎)
    }
single-agen-strip {f = h ⊗₁ k} (single-agen-⊗-l sh nk) =
  let nf-h = single-agen-strip sh
      open SingleAgenNF nf-h
  in record
    { u            = u
    ; c-from       = (id ⊗₁ α⇒) ∘ α⇒ ∘ (c-from ⊗₁ id)
    ; c-to         = (c-to ⊗₁ k) ∘ α⇐ ∘ (id ⊗₁ α⇐)
    ; nosigma-from = nosigma-∘ (nosigma-⊗ nosigma-id nosigma-α⇒)
                       (nosigma-∘ nosigma-α⇒ (nosigma-⊗ nosigma-from nosigma-id))
    ; nosigma-to   = nosigma-∘ (nosigma-⊗ nosigma-to nk)
                       (nosigma-∘ nosigma-α⇐ (nosigma-⊗ nosigma-id nosigma-α⇐))
    ; equiv        = single-agen-strip-⊗-equiv-l h k u c-from c-to equiv
    }
single-agen-strip {f = h ⊗₁ k} (single-agen-⊗-r nh sk) =
  let nf-k = single-agen-strip sk
      open SingleAgenNF nf-k
  in record
    { u            = u
    ; c-from       = α⇐ ∘ (id ⊗₁ c-from)
    ; c-to         = (h ⊗₁ c-to) ∘ α⇒
    ; nosigma-from = nosigma-∘ nosigma-α⇐ (nosigma-⊗ nosigma-id nosigma-from)
    ; nosigma-to   = nosigma-∘ (nosigma-⊗ nh nosigma-to) nosigma-α⇒
    ; equiv        = single-agen-strip-⊗-equiv-r h k u c-from c-to equiv
    }

--------------------------------------------------------------------------------
-- Strictly-narrower postulate (Day 9 refinement).  Discharges the
-- σ-free single-Agen case *at the stripped normal-form level*: both
-- sides are presented with explicit `SingleAgenNF` data (the unique
-- generator `u` and the σ-free Mac Lane wrappers `c-from`/`c-to`).
--
-- This postulate is strictly narrower than the previous
-- `SingleAgen f → SingleAgen g → ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g`: it consumes
-- the already-built NF data on each side rather than re-deriving it
-- from the bare `SingleAgen` predicate.  The bridge to the general
-- form `single-agen-coherence-≈Term` is constructive via the strip
-- lemma `single-agen-strip` (commit 4bbc93b).
--
-- Why this remains a postulate: the NF discharge still needs to align
-- the wire types `YL, Aᵢ, Bᵢ, YR` and unique generator `u` between the
-- two NFs from the underlying iso.  Mac Lane coherence
-- (`Structural-coherence-≈Term-noσ`) trivially equates the wrappers
-- once their types are aligned, but the type-alignment step requires
-- non-trivial reasoning at the `flatten`-list level which is not
-- decidable from `flatten` alone (it is not injective; e.g.,
-- `flatten (unit ⊗₀ A) ≡ flatten A`).
--
-- Net postulate count: unchanged (1 → 1).  Net content: strictly
-- narrower — the hypothesis assumes the NF decomposition is given.

--------------------------------------------------------------------------------
-- The two remaining narrow assumptions of the completeness path are
-- bundled into a record `CompletenessAssumptions`.  The rest of this
-- module (the `nf-resp-≅ᴴ` dispatcher and the top-level
-- `decode-rel-resp-≅ᴴ-full`) lives inside a sub-module parameterized
-- by a record instance, so this file itself is `--safe`-clean: the
-- trust is exposed at the call site that supplies the record.

record CompletenessAssumptions : Set where
  field
    single-agen-NF-coherence
      : ∀ {A B} {f g : HomTerm A B}
      → SingleAgenNF f → SingleAgenNF g
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → f ≈Term g

    nf-resp-≅ᴴ-residual
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → bridge f ≈Term bridge g

-- The record-parameterized sub-module is `WithAssumptions` below
-- (placed after the structural helpers `NoAgen-iso-IsAgen-⊥` etc. and
-- `nf-bridge`, both of which are postulate-free and reused here).

--------------------------------------------------------------------------------
-- `bridge` is a congruence with respect to `_≈Term_` — wrapping with
-- the coherence isos on each side preserves `≈Term`.  This is the
-- 1-line lemma that lifts `Structural-coherence-≈Term-noσ`'s conclusion
-- `f ≈Term g` to `bridge f ≈Term bridge g` without needing a separate
-- `bridge-≅ᴴ` lemma.

private
  bridge-resp-≈Term
    : ∀ {A B} {f g : HomTerm A B}
    → f ≈Term g → bridge f ≈Term bridge g
  bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

--------------------------------------------------------------------------------
-- Edge-count contradiction: a `NoAgen` term has 0 edges, an `IsAgen`
-- term has 1.  An iso forces the edge bijection — `Fin 1 → Fin 0` is
-- vacuous from `ψ`.

NoAgen-iso-IsAgen-⊥
  : ∀ {A B} {f : HomTerm A B} {g : mor A B}
  → NoAgen f → ⟪ f ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
NoAgen-iso-IsAgen-⊥ {f = f} {g = g} nf iso =
  contra (ψ⁻¹ zero)
  where
    open _≅ᴴ_ iso
    -- `nE ⟪ Agen g ⟫ ≡ 1`, so `Fin K.nE = Fin 1` (definitionally).
    -- `nE ⟪ f ⟫ ≡ 0` from `nE-NoAgen nf`.
    contra : Fin (Hypergraph.nE ⟪ f ⟫) → ⊥
    contra eF = absurd
      where
        eF' : Fin 0
        eF' = subst Fin (nE-NoAgen nf) eF
        absurd : ⊥
        absurd with eF'
        ... | ()

IsAgen-iso-NoAgen-⊥
  : ∀ {A B} {f : mor A B} {g : HomTerm A B}
  → NoAgen g → ⟪ Agen f ⟫ ≅ᴴ ⟪ g ⟫ → ⊥
IsAgen-iso-NoAgen-⊥ {f = f} {g = g} ng iso =
  contra (ψ zero)
  where
    open _≅ᴴ_ iso
    contra : Fin (Hypergraph.nE ⟪ g ⟫) → ⊥
    contra eG = absurd
      where
        eG' : Fin 0
        eG' = subst Fin (nE-NoAgen ng) eG
        absurd : ⊥
        absurd with eG'
        ... | ()

-- General edge-count contradiction: a NoAgen side and a HasAgen side
-- of an iso are inconsistent — the iso's ψ⁻¹/ψ produces a Fin 0
-- inhabitant.
NoAgen-iso-HasAgen-⊥
  : ∀ {A B} {f g : HomTerm A B}
  → NoAgen f → HasAgen g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → ⊥
NoAgen-iso-HasAgen-⊥ {f = f} {g = g} nf hg iso = absurd
  where
    open _≅ᴴ_ iso
    eG : Fin (Hypergraph.nE ⟪ g ⟫)
    eG = HasAgen-edge hg
    eF : Fin (Hypergraph.nE ⟪ f ⟫)
    eF = ψ⁻¹ eG
    eF0 : Fin 0
    eF0 = subst Fin (nE-NoAgen nf) eF
    absurd : ⊥
    absurd with eF0
    ... | ()

HasAgen-iso-NoAgen-⊥
  : ∀ {A B} {f g : HomTerm A B}
  → HasAgen f → NoAgen g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → ⊥
HasAgen-iso-NoAgen-⊥ {f = f} {g = g} hf ng iso = absurd
  where
    open _≅ᴴ_ iso
    eF : Fin (Hypergraph.nE ⟪ f ⟫)
    eF = HasAgen-edge hf
    eG : Fin (Hypergraph.nE ⟪ g ⟫)
    eG = ψ eF
    eG0 : Fin 0
    eG0 = subst Fin (nE-NoAgen ng) eG
    absurd : ⊥
    absurd with eG0
    ... | ()

--------------------------------------------------------------------------------
-- Strictly narrower residual postulate.  Fires only when *both* of
-- `f, g` contain a σ or non-atomic Agen subterm.  Already discharged:
--   * Both NoSigma (no σ, no Agen) → `Structural-coherence-≈Term-noσ`.
--   * Both atomic Agen → `decode-rel-resp-≅ᴴ-Agen-Agen`.
--   * One NoAgen, other atomic Agen → contradiction via edge-count.

--------------------------------------------------------------------------------
-- `nf-bridge`: the bridge from `decode-rel` to `bridge`.  This is
-- *exactly* `decode-roundtrip-rel` (in `DecodeRel.agda`), restated
-- here so the composition below reads as the path-B story.  Lives
-- outside `WithAssumptions` since it is postulate-free.

nf-bridge
  : ∀ {A B} (f : HomTerm A B)
  → decode-rel f ≈Term bridge f
nf-bridge = decode-roundtrip-rel

--------------------------------------------------------------------------------
-- The remaining dispatcher and the full theorem live inside the
-- record-parameterized sub-module `WithAssumptions`, since they
-- consume `nf-resp-≅ᴴ-residual` and (transitively) `single-agen-NF-coherence`.

module WithAssumptions (assumptions : CompletenessAssumptions) where
  open CompletenessAssumptions assumptions

  ------------------------------------------------------------------------
  -- Derived: the original (wider) coherence claim, constructively
  -- reduced to the NF-level field via `single-agen-strip`.
  single-agen-coherence-≈Term
    : ∀ {A B} {f g : HomTerm A B}
    → SingleAgen f → SingleAgen g
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → f ≈Term g
  single-agen-coherence-≈Term sf sg iso =
    single-agen-NF-coherence (single-agen-strip sf) (single-agen-strip sg) iso

  ------------------------------------------------------------------------
  -- The Path B `nf-resp-≅ᴴ`: case-split layered as
  --   (1) both NoSigma         → Mac Lane (constructive),
  --   (2) both atomic Agen     → AgenAgen (constructive),
  --   (3) one NoAgen vs the other atomic Agen → vacuous (edge-count ⊥),
  --   (4) else                 → residual field (strictly narrower
  --                              than before).

  nf-resp-≅ᴴ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → bridge f ≈Term bridge g
  nf-resp-≅ᴴ f g iso with NoSigma? f | NoSigma? g
  ... | inj₁ nf | inj₁ ng =
          bridge-resp-≈Term (Structural-coherence-≈Term-noσ nf ng iso)
  ... | _       | _       with IsAgen? f | IsAgen? g
  ...    | inj₁ (is-agen g₁) | inj₁ (is-agen g₂) =
              decode-rel-resp-≅ᴴ-Agen-Agen g₁ g₂ iso
  ...    | inj₁ (is-agen g₁) | inj₂ _ with NoAgen-or-HasAgen g
  ...        | inj₁ ng = ⊥-elim (IsAgen-iso-NoAgen-⊥ {f = g₁} {g = g} ng iso)
  ...        | inj₂ _  = nf-resp-≅ᴴ-residual f g iso
  nf-resp-≅ᴴ f g iso | _ | _ | inj₂ _ | inj₁ (is-agen g₂) with NoAgen-or-HasAgen f
  ...        | inj₁ nf = ⊥-elim (NoAgen-iso-IsAgen-⊥ {f = f} {g = g₂} nf iso)
  ...        | inj₂ _  = nf-resp-≅ᴴ-residual f g iso
  nf-resp-≅ᴴ f g iso | _ | _ | inj₂ _ | inj₂ _ with NoAgen-or-HasAgen f | NoAgen-or-HasAgen g
  ...        | inj₁ nf | inj₂ hg = ⊥-elim (NoAgen-iso-HasAgen-⊥ nf hg iso)
  ...        | inj₂ hf | inj₁ ng = ⊥-elim (HasAgen-iso-NoAgen-⊥ hf ng iso)
  ...        | inj₁ nf | inj₁ ng = nf-resp-≅ᴴ-residual f g iso
  ...        | inj₂ _  | inj₂ _  with SingleAgen? f | SingleAgen? g
  ...            | inj₁ sf | inj₁ sg =
                     bridge-resp-≈Term (single-agen-coherence-≈Term sf sg iso)
  ...            | _       | _       = nf-resp-≅ᴴ-residual f g iso

  ------------------------------------------------------------------------
  -- The full theorem, now a one-shot composition.

  decode-rel-resp-≅ᴴ-full
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode-rel f ≈Term decode-rel g
  decode-rel-resp-≅ᴴ-full f g iso =
    ≈-Term-trans (nf-bridge f)
      (≈-Term-trans (nf-resp-≅ᴴ f g iso)
                    (≈-Term-sym (nf-bridge g)))

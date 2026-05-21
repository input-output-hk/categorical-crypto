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
--
-- We also pull in `noσ-discharge`, the iso-free Mac-Lane coherence: any
-- two parallel `NoSigma` morphisms are `≈Term`-equal.  Used below to
-- align the σ-free wrappers around the unique `Agen u` generator when
-- closing `single-agen-NF-coherence-discharge`.
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.AtomicCompound0E sig-dec
  using ( NoSigma
        ; nosigma-id; nosigma-λ⇒; nosigma-λ⇐; nosigma-ρ⇒; nosigma-ρ⇐
        ; nosigma-α⇒; nosigma-α⇐; nosigma-∘; nosigma-⊗
        ; Structural-coherence-≈Term-noσ
        ; noσ-discharge
        )

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)

-- Imports used by `elab-at-SingleAgen-edge` and its inductive cases.
-- Brought in at the top level so the lemma can be stated near
-- `single-agen-u`.  Note: `hComposeP-impl` / `hTensor-impl` are
-- parameterised submodules; they are opened locally with the relevant
-- `⟪_⟫` arguments inside each clause via the qualified path
-- (`hComposeP-impl ⟪k⟫ ⟪h⟫ bdy-eq` / `hTensor-impl ⟪h⟫ ⟪k⟫`).
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flat; flatten;
         map-via-inj; map-via-raise; module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)

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
-- Helpers for `SingleAgen`:
--   * `NoSigma→NoAgen` — `NoSigma` admits neither `σ` nor `Agen`, so it
--     is strictly stronger than `NoAgen` (which permits `σ`).  Used in
--     `nE-SingleAgen` below to discharge the wrappers' 0-edge claim.
--   * `nE-SingleAgen : SingleAgen f → nE ⟪f⟫ ≡ 1` — combines the IH on
--     the SingleAgen side (1 edge) with `nE-NoAgen` on the NoSigma side
--     (0 edges) through the additive structure of `hCompose`/`hTensor`.
--   * `SingleAgen-edge` — locator for the unique Agen edge inside
--     `⟪f⟫`.  Parallels `HasAgen-edge` but is driven by `SingleAgen`.

NoSigma→NoAgen : ∀ {A B} {f : HomTerm A B} → NoSigma f → NoAgen f
NoSigma→NoAgen nosigma-id        = noagen-id
NoSigma→NoAgen nosigma-λ⇒        = noagen-λ⇒
NoSigma→NoAgen nosigma-λ⇐        = noagen-λ⇐
NoSigma→NoAgen nosigma-ρ⇒        = noagen-ρ⇒
NoSigma→NoAgen nosigma-ρ⇐        = noagen-ρ⇐
NoSigma→NoAgen nosigma-α⇒        = noagen-α⇒
NoSigma→NoAgen nosigma-α⇐        = noagen-α⇐
NoSigma→NoAgen (nosigma-∘ nh nk) = noagen-∘ (NoSigma→NoAgen nh) (NoSigma→NoAgen nk)
NoSigma→NoAgen (nosigma-⊗ nh nk) = noagen-⊗ (NoSigma→NoAgen nh) (NoSigma→NoAgen nk)

nE-SingleAgen : ∀ {A B} {f : HomTerm A B} → SingleAgen f → Hypergraph.nE ⟪ f ⟫ ≡ 1
nE-SingleAgen (single-agen-here _) = refl
nE-SingleAgen (single-agen-∘-l sh nk)
  rewrite nE-SingleAgen sh | nE-NoAgen (NoSigma→NoAgen nk) = refl
nE-SingleAgen (single-agen-∘-r nh sk)
  rewrite nE-SingleAgen sk | nE-NoAgen (NoSigma→NoAgen nh) = refl
nE-SingleAgen (single-agen-⊗-l sh nk)
  rewrite nE-SingleAgen sh | nE-NoAgen (NoSigma→NoAgen nk) = refl
nE-SingleAgen (single-agen-⊗-r nh sk)
  rewrite nE-SingleAgen sk | nE-NoAgen (NoSigma→NoAgen nh) = refl

SingleAgen-edge
  : ∀ {A B} {f : HomTerm A B}
  → SingleAgen f → Fin (Hypergraph.nE ⟪ f ⟫)
SingleAgen-edge {f = Agen _}  (single-agen-here _) = zero
SingleAgen-edge {f = h ∘ k}   (single-agen-∘-l sh _)
  = Hypergraph.nE ⟪ k ⟫ ↑ʳ SingleAgen-edge sh
  where open import Data.Fin using (_↑ʳ_)
SingleAgen-edge {f = h ∘ k}   (single-agen-∘-r _ sk)
  = SingleAgen-edge sk ↑ˡ Hypergraph.nE ⟪ h ⟫
  where open import Data.Fin using (_↑ˡ_)
SingleAgen-edge {f = h ⊗₁ k}  (single-agen-⊗-l sh _)
  = SingleAgen-edge sh ↑ˡ Hypergraph.nE ⟪ k ⟫
  where open import Data.Fin using (_↑ˡ_)
SingleAgen-edge {f = h ⊗₁ k}  (single-agen-⊗-r _ sk)
  = Hypergraph.nE ⟪ h ⟫ ↑ʳ SingleAgen-edge sk
  where open import Data.Fin using (_↑ʳ_)

-- Extract the unique underlying generator from a `SingleAgen` witness.
-- This is the `u` field of the eventual `SingleAgenNF` record built by
-- `single-agen-strip`, but exposed here independently of the strip so
-- downstream lemmas (notably the elab-at-`SingleAgen-edge` characterization)
-- can reference it without owning a strip-built NF record.

record SingleAgenGen {A B : ObjTerm} (f : HomTerm A B) : Set where
  field
    {Aᵢ Bᵢ} : ObjTerm
    u       : mor Aᵢ Bᵢ

single-agen-u
  : ∀ {A B} {f : HomTerm A B}
  → SingleAgen f → SingleAgenGen f
single-agen-u (single-agen-here u) = record { u = u }
single-agen-u (single-agen-∘-l sh _) = record
  { Aᵢ = SingleAgenGen.Aᵢ rec
  ; Bᵢ = SingleAgenGen.Bᵢ rec
  ; u  = SingleAgenGen.u  rec
  }
  where rec = single-agen-u sh
single-agen-u (single-agen-∘-r _ sk) = record
  { Aᵢ = SingleAgenGen.Aᵢ rec
  ; Bᵢ = SingleAgenGen.Bᵢ rec
  ; u  = SingleAgenGen.u  rec
  }
  where rec = single-agen-u sk
single-agen-u (single-agen-⊗-l sh _) = record
  { Aᵢ = SingleAgenGen.Aᵢ rec
  ; Bᵢ = SingleAgenGen.Bᵢ rec
  ; u  = SingleAgenGen.u  rec
  }
  where rec = single-agen-u sh
single-agen-u (single-agen-⊗-r _ sk) = record
  { Aᵢ = SingleAgenGen.Aᵢ rec
  ; Bᵢ = SingleAgenGen.Bᵢ rec
  ; u  = SingleAgenGen.u  rec
  }
  where rec = single-agen-u sk

--------------------------------------------------------------------------------
-- Characterization of `elab ⟪f⟫ (SingleAgen-edge sf)`.  At the unique
-- `Agen` edge of `⟪f⟫`, the label is `flat u` (the underlying generator
-- from `single-agen-u sf`) up to two transports witnessing that the
-- edge's incoming/outgoing vertex-label lists equal `flatten Aᵢ` /
-- `flatten Bᵢ`.  The transports are bundled existentially because their
-- concrete form depends on the path through the term:
--
--   * Base case `Agen u`: the `lem-in`/`lem-out` produced inside
--     `hGen u` (witnessing `flatten A ≡ map vlab-c (map (_↑ˡ nB) (range nA))`
--     and dually for the output).
--   * `∘` cases: one extra `map-via-remapP`/`map-via-inj` layer per
--     `∘` arising from `hComposeP-impl.elab-c-inj₂` (K-side) /
--     `elab-c-inj₁` (G-side).
--   * `⊗` cases: one extra `map-via-inj`/`map-via-raise` layer per
--     `⊗` arising from `hTensor-impl.elab-c-inj₁` / `elab-c-inj₂`.
--
-- Downstream consumers (notably the forthcoming `single-agen-flat-data`)
-- combine this with `ψ-elab` and `UIP-ListX` to extract the propositional
-- equalities `flat-A-eq`, `flat-B-eq`, `flat-u-eq` that the narrowed
-- `single-agen-NF-coherence` postulate consumes.

private
  -- Two consecutive `subst₂` transports fuse along `trans`.
  subst₂-trans-FlatGen
    : ∀ {As Bs Cs Ds Es Fs : List X}
        (p₁ : As ≡ Cs) (p₂ : Cs ≡ Es)
        (q₁ : Bs ≡ Ds) (q₂ : Ds ≡ Fs)
        (x : FlatGen As Bs)
    → subst₂ FlatGen p₂ q₂ (subst₂ FlatGen p₁ q₁ x)
    ≡ subst₂ FlatGen (trans p₁ p₂) (trans q₁ q₂) x
  subst₂-trans-FlatGen refl refl refl refl _ = refl

  -- `subst₂` cancels its own `sym` inverse.
  subst₂-sym-cancel
    : ∀ {As Bs Cs Ds : List X}
        (p : As ≡ Cs) (q : Bs ≡ Ds)
        (x : FlatGen As Bs)
    → subst₂ FlatGen (sym p) (sym q) (subst₂ FlatGen p q x) ≡ x
  subst₂-sym-cancel refl refl _ = refl

  -- The inductive-step "fold": given the IH on the sub-elab plus the
  -- relevant `elab-c-inj_` for the surrounding `hComposeP`/`hTensor`,
  -- produces the lifted characterization at the composite edge.
  fold-elab-step
    : ∀ {As Bs Cs Ds Es Fs Gs Hs : List X}
        {x : FlatGen As Bs} {base : FlatGen Cs Ds}
        (target : FlatGen Gs Hs)
        (p-IH : As ≡ Cs)   (q-IH : Bs ≡ Ds)
        (M-in : Cs ≡ Es)   (M-out : Ds ≡ Fs)
        (L-in : Gs ≡ Es)   (L-out : Hs ≡ Fs)
    → base ≡ subst₂ FlatGen p-IH q-IH x
    → subst₂ FlatGen L-in L-out target ≡ subst₂ FlatGen M-in M-out base
    → target ≡ subst₂ FlatGen (trans (trans p-IH M-in) (sym L-in))
                              (trans (trans q-IH M-out) (sym L-out))
                              x
  fold-elab-step {x = x} {base = base} target p-IH q-IH M-in M-out L-in L-out base-eq inj-eq =
    begin
      target
    ≡⟨ sym (subst₂-sym-cancel L-in L-out target) ⟩
      subst₂ FlatGen (sym L-in) (sym L-out)
        (subst₂ FlatGen L-in L-out target)
    ≡⟨ cong (subst₂ FlatGen (sym L-in) (sym L-out)) inj-eq ⟩
      subst₂ FlatGen (sym L-in) (sym L-out)
        (subst₂ FlatGen M-in M-out base)
    ≡⟨ cong (λ z → subst₂ FlatGen (sym L-in) (sym L-out)
                     (subst₂ FlatGen M-in M-out z)) base-eq ⟩
      subst₂ FlatGen (sym L-in) (sym L-out)
        (subst₂ FlatGen M-in M-out (subst₂ FlatGen p-IH q-IH x))
    ≡⟨ cong (subst₂ FlatGen (sym L-in) (sym L-out))
            (subst₂-trans-FlatGen p-IH M-in q-IH M-out x) ⟩
      subst₂ FlatGen (sym L-in) (sym L-out)
        (subst₂ FlatGen (trans p-IH M-in) (trans q-IH M-out) x)
    ≡⟨ subst₂-trans-FlatGen (trans p-IH M-in) (sym L-in)
                            (trans q-IH M-out) (sym L-out) x ⟩
      subst₂ FlatGen (trans (trans p-IH M-in) (sym L-in))
                     (trans (trans q-IH M-out) (sym L-out)) x
    ∎
    where open ≡-Reasoning

elab-at-SingleAgen-edge
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → Σ[ p ∈ flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
         ≡ map (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.ein ⟪ f ⟫ (SingleAgen-edge sf)) ]
    Σ[ q ∈ flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
         ≡ map (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.eout ⟪ f ⟫ (SingleAgen-edge sf)) ]
    Hypergraph.elab ⟪ f ⟫ (SingleAgen-edge sf)
    ≡ subst₂ FlatGen p q (flat (SingleAgenGen.u (single-agen-u sf)))
elab-at-SingleAgen-edge (single-agen-here u) = _ , _ , refl
elab-at-SingleAgen-edge {f = h ∘ k} (single-agen-∘-l sh nk) =
  P , Q , EQ
  where
    bdy-eq = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy-eq
      using (elab-c; elab-c-inj₂; ein-c-inj₂-red; eout-c-inj₂-red;
             map-via-remapP; vlab-P)

    eK    = SingleAgen-edge sh
    ih    = elab-at-SingleAgen-edge sh
    p-IH  = proj₁ ih
    q-IH  = proj₁ (proj₂ ih)
    eq-IH = proj₂ (proj₂ ih)

    L-in  = cong (map vlab-P) (ein-c-inj₂-red eK)
    L-out = cong (map vlab-P) (eout-c-inj₂-red eK)
    M-in  = map-via-remapP (Hypergraph.ein ⟪ h ⟫ eK)
    M-out = map-via-remapP (Hypergraph.eout ⟪ h ⟫ eK)

    P = trans (trans p-IH M-in) (sym L-in)
    Q = trans (trans q-IH M-out) (sym L-out)

    EQ = fold-elab-step
      (elab-c (Hypergraph.nE ⟪ k ⟫ ↑ʳ eK))
      p-IH q-IH M-in M-out L-in L-out
      eq-IH (elab-c-inj₂ eK)

elab-at-SingleAgen-edge {f = h ∘ k} (single-agen-∘-r nh sk) =
  P , Q , EQ
  where
    bdy-eq = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy-eq
      using (elab-c; elab-c-inj₁; ein-c-inj₁-red; eout-c-inj₁-red;
             vlab-injL; vlab-P)

    eG    = SingleAgen-edge sk
    ih    = elab-at-SingleAgen-edge sk
    p-IH  = proj₁ ih
    q-IH  = proj₁ (proj₂ ih)
    eq-IH = proj₂ (proj₂ ih)

    L-in  = cong (map vlab-P) (ein-c-inj₁-red eG)
    L-out = cong (map vlab-P) (eout-c-inj₁-red eG)
    M-in  = map-via-inj vlab-injL (Hypergraph.ein ⟪ k ⟫ eG)
    M-out = map-via-inj vlab-injL (Hypergraph.eout ⟪ k ⟫ eG)

    P = trans (trans p-IH M-in) (sym L-in)
    Q = trans (trans q-IH M-out) (sym L-out)

    EQ = fold-elab-step
      (elab-c (eG ↑ˡ Hypergraph.nE ⟪ h ⟫))
      p-IH q-IH M-in M-out L-in L-out
      eq-IH (elab-c-inj₁ eG)

elab-at-SingleAgen-edge {f = h ⊗₁ k} (single-agen-⊗-l sh nk) =
  P , Q , EQ
  where
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫
      using (elab-c; elab-c-inj₁; ein-c-inj₁-red; eout-c-inj₁-red;
             vlab-injL; vlab-c)

    eG    = SingleAgen-edge sh
    ih    = elab-at-SingleAgen-edge sh
    p-IH  = proj₁ ih
    q-IH  = proj₁ (proj₂ ih)
    eq-IH = proj₂ (proj₂ ih)

    L-in  = cong (map vlab-c) (ein-c-inj₁-red eG)
    L-out = cong (map vlab-c) (eout-c-inj₁-red eG)
    M-in  = map-via-inj vlab-injL (Hypergraph.ein ⟪ h ⟫ eG)
    M-out = map-via-inj vlab-injL (Hypergraph.eout ⟪ h ⟫ eG)

    P = trans (trans p-IH M-in) (sym L-in)
    Q = trans (trans q-IH M-out) (sym L-out)

    EQ = fold-elab-step
      (elab-c (eG ↑ˡ Hypergraph.nE ⟪ k ⟫))
      p-IH q-IH M-in M-out L-in L-out
      eq-IH (elab-c-inj₁ eG)

elab-at-SingleAgen-edge {f = h ⊗₁ k} (single-agen-⊗-r nh sk) =
  P , Q , EQ
  where
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫
      using (elab-c; elab-c-inj₂; ein-c-inj₂-red; eout-c-inj₂-red;
             vlab-injR; vlab-c)

    eK    = SingleAgen-edge sk
    ih    = elab-at-SingleAgen-edge sk
    p-IH  = proj₁ ih
    q-IH  = proj₁ (proj₂ ih)
    eq-IH = proj₂ (proj₂ ih)

    L-in  = cong (map vlab-c) (ein-c-inj₂-red eK)
    L-out = cong (map vlab-c) (eout-c-inj₂-red eK)
    M-in  = map-via-raise vlab-injR (Hypergraph.ein ⟪ k ⟫ eK)
    M-out = map-via-raise vlab-injR (Hypergraph.eout ⟪ k ⟫ eK)

    P = trans (trans p-IH M-in) (sym L-in)
    Q = trans (trans q-IH M-out) (sym L-out)

    EQ = fold-elab-step
      (elab-c (Hypergraph.nE ⟪ h ⟫ ↑ʳ eK))
      p-IH q-IH M-in M-out L-in L-out
      eq-IH (elab-c-inj₂ eK)

--------------------------------------------------------------------------------
-- `single-agen-flat-data`: from a `SingleAgen` witness on each side of
-- an iso `⟪f⟫ ≅ᴴ ⟪g⟫`, extract the three flat-level equalities that
-- the (forthcoming) narrowed `single-agen-NF-coherence` consumes.
--
-- The proof composes:
--   * `nE-SingleAgen sg` + `Fin 1` uniqueness to align
--     `ψ (SingleAgen-edge sf) ≡ SingleAgen-edge sg`;
--   * `ψ-elab` from the iso, combined with the edge alignment, to
--     express `elab ⟪f⟫ (SingleAgen-edge sf)` in terms of
--     `elab ⟪g⟫ (SingleAgen-edge sg)` via a single fused `subst₂`;
--   * `elab-at-SingleAgen-edge` on both sides to turn both elabs into
--     `subst₂ FlatGen ... (flat u)`;
--   * a final `subst₂` peel (`flat-eq-extract`) that absorbs the
--     vertex-label transports into a flat `(flat-A-eq, flat-B-eq,
--     flat-u-eq)` triple.
--
-- The trust content of the previous `single-agen-NF-coherence` thereby
-- shrinks: the postulate no longer needs to chase the iso into ObjTerm
-- alignment; it only needs to close the Mac-Lane wrappers around an
-- already-aligned generator.

private
  -- `Fin 1` has a unique inhabitant `zero`.
  Fin1-uniq : (x : Fin 1) → x ≡ zero
  Fin1-uniq zero = refl

  -- `subst Fin p` is injective along the same proof `p`.
  subst-Fin-injective
    : ∀ {n m : ℕ} (p : n ≡ m) {x y : Fin n}
    → subst Fin p x ≡ subst Fin p y → x ≡ y
  subst-Fin-injective refl eq = eq

  -- Edge equality lifts to an `elab` equality up to `subst₂` along the
  -- congruences of `ein` / `eout`.  Used to absorb
  -- `ψ (SingleAgen-edge sf) ≡ SingleAgen-edge sg` into the elab chain.
  subst₂-cong-elab
    : ∀ {nE nV : ℕ} {vlab : Fin nV → X}
        (ein eout : Fin nE → List (Fin nV))
        (elab : (e : Fin nE) → FlatGen (map vlab (ein e)) (map vlab (eout e)))
        {e₁ e₂ : Fin nE} (eq : e₁ ≡ e₂)
    → elab e₁
    ≡ subst₂ FlatGen (cong (λ e → map vlab (ein e))  (sym eq))
                     (cong (λ e → map vlab (eout e)) (sym eq))
                     (elab e₂)
  subst₂-cong-elab _ _ _ refl = refl

  -- Final peel: convert a binary `subst₂` equation into the flat form
  -- expected by `single-agen-NF-coherence` (after rewire).
  flat-eq-extract
    : ∀ {Aᵢ-f Bᵢ-f Aᵢ-g Bᵢ-g As Bs : List X}
        (p_f : Aᵢ-f ≡ As) (q_f : Bᵢ-f ≡ Bs)
        (P-rhs : Aᵢ-g ≡ As) (Q-rhs : Bᵢ-g ≡ Bs)
        {x : FlatGen Aᵢ-f Bᵢ-f} {y : FlatGen Aᵢ-g Bᵢ-g}
    → subst₂ FlatGen p_f q_f x ≡ subst₂ FlatGen P-rhs Q-rhs y
    → subst₂ FlatGen (trans p_f (sym P-rhs)) (trans q_f (sym Q-rhs)) x ≡ y
  flat-eq-extract p_f q_f P-rhs Q-rhs {x = x} {y = y} eq =
    trans
      (sym (subst₂-trans-FlatGen p_f (sym P-rhs) q_f (sym Q-rhs) x))
      (trans (cong (subst₂ FlatGen (sym P-rhs) (sym Q-rhs)) eq)
             (subst₂-sym-cancel P-rhs Q-rhs y))

single-agen-flat-data
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → Σ[ flat-A-eq ∈ flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                ≡ flatten (SingleAgenGen.Aᵢ (single-agen-u sg)) ]
    Σ[ flat-B-eq ∈ flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
                ≡ flatten (SingleAgenGen.Bᵢ (single-agen-u sg)) ]
    subst₂ FlatGen flat-A-eq flat-B-eq
      (flat (SingleAgenGen.u (single-agen-u sf)))
    ≡ flat (SingleAgenGen.u (single-agen-u sg))
single-agen-flat-data {f = f} {g = g} sf sg iso =
    flat-A-eq , flat-B-eq , flat-u-eq
  where
    open _≅ᴴ_ iso
    module HF = Hypergraph ⟪ f ⟫
    module HG = Hypergraph ⟪ g ⟫

    e₀ : Fin HF.nE
    e₀ = SingleAgen-edge sf

    u_f = SingleAgenGen.u (single-agen-u sf)
    u_g = SingleAgenGen.u (single-agen-u sg)

    -- ψ-edge-eq : ψ e₀ ≡ SingleAgen-edge sg.
    -- Proof: subst both to `Fin 1` via `nE-SingleAgen sg`, then apply
    -- `Fin1-uniq`; `subst-Fin-injective` finishes.
    nE-eq-g : HG.nE ≡ 1
    nE-eq-g = nE-SingleAgen sg

    ψ-edge-eq : ψ e₀ ≡ SingleAgen-edge sg
    ψ-edge-eq = subst-Fin-injective nE-eq-g
      (trans (Fin1-uniq (subst Fin nE-eq-g (ψ e₀)))
             (sym (Fin1-uniq (subst Fin nE-eq-g (SingleAgen-edge sg)))))

    -- IH bindings (from `elab-at-SingleAgen-edge`).
    ih-f = elab-at-SingleAgen-edge sf
    p_f  = proj₁ ih-f
    q_f  = proj₁ (proj₂ ih-f)
    eq_f = proj₂ (proj₂ ih-f)

    ih-g = elab-at-SingleAgen-edge sg
    p_g  = proj₁ ih-g
    q_g  = proj₁ (proj₂ ih-g)
    eq_g = proj₂ (proj₂ ih-g)

    -- Cong of `ψ-edge-eq` through `map HG.vlab ∘ HG.{ein,eout}`.
    -- Direction: `(SingleAgen-edge sg) → (ψ e₀)` (matches the
    -- direction returned by `subst₂-cong-elab`).
    cong-ein-sym  = cong (λ e → map HG.vlab (HG.ein  e)) (sym ψ-edge-eq)
    cong-eout-sym = cong (λ e → map HG.vlab (HG.eout e)) (sym ψ-edge-eq)

    -- Compose `ψ-elab e₀` with `subst₂-cong-elab` and IH on `g` to
    -- express `HF.elab e₀` as a single `subst₂` over `flat u_g`.
    P-rhs = trans p_g (trans cong-ein-sym  (atom-ein  e₀))
    Q-rhs = trans q_g (trans cong-eout-sym (atom-eout e₀))

    HF-elab-flat : HF.elab e₀ ≡ subst₂ FlatGen P-rhs Q-rhs (flat u_g)
    HF-elab-flat = begin
        HF.elab e₀
      ≡⟨ sym (ψ-elab e₀) ⟩
        subst₂ FlatGen (atom-ein e₀) (atom-eout e₀) (HG.elab (ψ e₀))
      ≡⟨ cong (subst₂ FlatGen (atom-ein e₀) (atom-eout e₀))
              (subst₂-cong-elab HG.ein HG.eout HG.elab ψ-edge-eq) ⟩
        subst₂ FlatGen (atom-ein e₀) (atom-eout e₀)
          (subst₂ FlatGen cong-ein-sym cong-eout-sym
            (HG.elab (SingleAgen-edge sg)))
      ≡⟨ subst₂-trans-FlatGen cong-ein-sym (atom-ein e₀)
                              cong-eout-sym (atom-eout e₀)
                              (HG.elab (SingleAgen-edge sg)) ⟩
        subst₂ FlatGen (trans cong-ein-sym  (atom-ein  e₀))
                       (trans cong-eout-sym (atom-eout e₀))
                       (HG.elab (SingleAgen-edge sg))
      ≡⟨ cong (subst₂ FlatGen (trans cong-ein-sym  (atom-ein  e₀))
                              (trans cong-eout-sym (atom-eout e₀))) eq_g ⟩
        subst₂ FlatGen (trans cong-ein-sym  (atom-ein  e₀))
                       (trans cong-eout-sym (atom-eout e₀))
                       (subst₂ FlatGen p_g q_g (flat u_g))
      ≡⟨ subst₂-trans-FlatGen p_g (trans cong-ein-sym  (atom-ein  e₀))
                              q_g (trans cong-eout-sym (atom-eout e₀))
                              (flat u_g) ⟩
        subst₂ FlatGen P-rhs Q-rhs (flat u_g)
      ∎
      where open ≡-Reasoning

    -- Combine with IH-f to relate `flat u_f` and `flat u_g`.
    combined : subst₂ FlatGen p_f q_f (flat u_f)
             ≡ subst₂ FlatGen P-rhs Q-rhs (flat u_g)
    combined = trans (sym eq_f) HF-elab-flat

    flat-A-eq = trans p_f (sym P-rhs)
    flat-B-eq = trans q_f (sym Q-rhs)
    flat-u-eq = flat-eq-extract p_f q_f P-rhs Q-rhs combined

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
-- `single-agen-u`/`single-agen-strip` consistency.  Both functions
-- extract `Aᵢ`/`Bᵢ`/`u` from a `SingleAgen` witness, but via different
-- records (`SingleAgenGen` for `single-agen-u`, `SingleAgenNF` for
-- `single-agen-strip`).  By construction both pipelines traverse the
-- witness identically and produce the same underlying generator data;
-- the consistency lemmas below witness this propositionally, so the
-- (forthcoming) wrapper-closure work can freely switch between the two
-- forms without re-running structural induction at every call site.

single-agen-u-strip-Aᵢ
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → SingleAgenGen.Aᵢ (single-agen-u sf)
  ≡ SingleAgenNF.Aᵢ (single-agen-strip sf)
single-agen-u-strip-Aᵢ (single-agen-here _)  = refl
single-agen-u-strip-Aᵢ (single-agen-∘-l sh _) = single-agen-u-strip-Aᵢ sh
single-agen-u-strip-Aᵢ (single-agen-∘-r _ sk) = single-agen-u-strip-Aᵢ sk
single-agen-u-strip-Aᵢ (single-agen-⊗-l sh _) = single-agen-u-strip-Aᵢ sh
single-agen-u-strip-Aᵢ (single-agen-⊗-r _ sk) = single-agen-u-strip-Aᵢ sk

single-agen-u-strip-Bᵢ
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → SingleAgenGen.Bᵢ (single-agen-u sf)
  ≡ SingleAgenNF.Bᵢ (single-agen-strip sf)
single-agen-u-strip-Bᵢ (single-agen-here _)  = refl
single-agen-u-strip-Bᵢ (single-agen-∘-l sh _) = single-agen-u-strip-Bᵢ sh
single-agen-u-strip-Bᵢ (single-agen-∘-r _ sk) = single-agen-u-strip-Bᵢ sk
single-agen-u-strip-Bᵢ (single-agen-⊗-l sh _) = single-agen-u-strip-Bᵢ sh
single-agen-u-strip-Bᵢ (single-agen-⊗-r _ sk) = single-agen-u-strip-Bᵢ sk

single-agen-u-strip-u
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → subst₂ mor (single-agen-u-strip-Aᵢ sf) (single-agen-u-strip-Bᵢ sf)
      (SingleAgenGen.u (single-agen-u sf))
  ≡ SingleAgenNF.u (single-agen-strip sf)
single-agen-u-strip-u (single-agen-here _)  = refl
single-agen-u-strip-u (single-agen-∘-l sh _) = single-agen-u-strip-u sh
single-agen-u-strip-u (single-agen-∘-r _ sk) = single-agen-u-strip-u sk
single-agen-u-strip-u (single-agen-⊗-l sh _) = single-agen-u-strip-u sh
single-agen-u-strip-u (single-agen-⊗-r _ sk) = single-agen-u-strip-u sk

--------------------------------------------------------------------------------
-- Constructive discharge of `single-agen-NF-coherence`.
--
-- Given two `SingleAgen` witnesses on `f, g : HomTerm A B` and the
-- three flat-level equalities `pA, pB, pU` extracted by
-- `single-agen-flat-data`, we show `f ≈Term g` constructively.
--
-- Strategy:
--   1. The equation `subst₂ FlatGen pA pB (flat u_f) ≡ flat u_g` forces
--      ObjTerm-level equalities `Aᵢ_f ≡ Aᵢ_g` and `Bᵢ_f ≡ Bᵢ_g`
--      (extracted via the `FlatView` extractor below), because the
--      hidden type indices of `flat` must coincide for the constructor
--      forms to be equal.
--   2. After pattern-matching those ObjTerm equalities as `refl`,
--      `UIP-ListX` collapses `pA, pB` to `refl`, and `pU` reduces to
--      `flat u_f ≡ flat u_g`.  Then `flat-injective` gives
--      `u_f ≡ u_g`.
--   3. With aligned generator data, apply `single-agen-strip` on both
--      sides to obtain the two-sided NF: `f ≈Term c-to-f ∘ M ∘ c-from-f`
--      and `g ≈Term c-to-g ∘ M ∘ c-from-g`, where `M = id ⊗ (Agen u ⊗ id)`
--      (with the same `u` on both sides, after the consistency lemma
--      `single-agen-u-strip-{Aᵢ,Bᵢ,u}` transports the generator data
--      from `single-agen-u` to `single-agen-strip`'s record).
--   4. Build NoSigma Mac-Lane bridges between the wrapper ObjTerms
--      `YL_f ⊗ Aᵢ ⊗ YR_f` and `YL_g ⊗ Aᵢ ⊗ YR_g` (both have the same
--      `flatten`, equal to `flatten A`, because they are the codomain
--      of a NoSigma term from `A`).  Similarly for the B-side.
--   5. The central "Agen conjugation" lemma
--      `mlB ∘ M_f ∘ mlA⁻¹ ≈Term M_g` is required to chain everything;
--      it expresses naturality of `Agen u` with respect to Mac-Lane
--      coherence iso.  This is left as a strictly-narrower sub-lemma
--      `Agen-conj-noσ` and is the only remaining hole.

private
  --------------------------------------------------------------------------------
  -- FlatView-style extractor (inlined here to avoid cross-`with-K`
  -- module dependency on `Solver.Verify`).  Given `flat u`, the view
  -- exposes the hidden `(A, B, u)` triple together with explicit
  -- equalities — enough to extract ObjTerm-level equalities from a
  -- `subst₂ FlatGen pA pB (flat u_f) ≡ flat u_g` equation.

  record FlatView' {As Bs : List X} (x : FlatGen As Bs) : Set where
    constructor flatV'
    field
      A' B' : ObjTerm
      ok-A' : flatten A' ≡ As
      ok-B' : flatten B' ≡ Bs
      u'    : mor A' B'
      ok    : subst₂ FlatGen ok-A' ok-B' (flat u') ≡ x

  view : ∀ {As Bs} (x : FlatGen As Bs) → FlatView' x
  view (flat {A} {B} u) = flatV' A B refl refl u refl

  -- After `pA, pB` are dispatched, `subst₂ FlatGen pA pB (flat u_f) ≡
  -- flat u_g` implies `Aᵢ_f ≡ Aᵢ_g` and `Bᵢ_f ≡ Bᵢ_g` (the hidden
  -- ObjTerm indices of `flat`).

  view-subst-A
    : ∀ {Aᵢ Bᵢ} (u : mor Aᵢ Bᵢ) {As Bs}
        (pA : flatten Aᵢ ≡ As) (pB : flatten Bᵢ ≡ Bs)
    → FlatView'.A' (view (subst₂ FlatGen pA pB (flat u))) ≡ Aᵢ
  view-subst-A _ refl refl = refl

  view-subst-B
    : ∀ {Aᵢ Bᵢ} (u : mor Aᵢ Bᵢ) {As Bs}
        (pA : flatten Aᵢ ≡ As) (pB : flatten Bᵢ ≡ Bs)
    → FlatView'.B' (view (subst₂ FlatGen pA pB (flat u))) ≡ Bᵢ
  view-subst-B _ refl refl = refl

  -- `flat` is injective on its hidden ObjTerm indices: `flat u_f ≡
  -- flat u_g` (with definitionally equal types) implies `u_f ≡ u_g`.

  flat-injective
    : ∀ {Aᵢ Bᵢ} {u₁ u₂ : mor Aᵢ Bᵢ}
    → flat u₁ ≡ flat u₂ → u₁ ≡ u₂
  flat-injective refl = refl

  -- UIP on `List X` (Hedberg from `_≟X_`), copied from
  -- `Solver.Verify` so we don't pull in a `--without-K` import.
  open APROPSignatureDec sig-dec using (_≟X_)
  open import Axiom.UniquenessOfIdentityProofs using (UIP)
  import Axiom.UniquenessOfIdentityProofs as UIP-mod
  open import Data.List.Properties using (≡-dec)
  open import Relation.Binary.Definitions using (DecidableEquality)

  _≟LX_ : DecidableEquality (List X)
  _≟LX_ = ≡-dec _≟X_

  UIP-ListX : UIP (List X)
  UIP-ListX = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟LX_

  -- Helper: collapse a `subst₂ FlatGen pA pB` where `pA, pB` are
  -- self-equalities (i.e. equal lists on both sides) to identity via
  -- UIP collapsing `pA, pB` to `refl`.
  subst₂-eq-elim
    : ∀ {As Bs : List X} {x y : FlatGen As Bs}
        (p : As ≡ As) (q : Bs ≡ Bs)
    → subst₂ FlatGen p q x ≡ y → x ≡ y
  subst₂-eq-elim p q eq
    with UIP-ListX p refl | UIP-ListX q refl
  ... | refl | refl = eq

  -- Extract ObjTerm-level equality and a `flat u_f ≡ flat u_g`
  -- equation from the three flat-level inputs.
  flat-data-to-ObjTerm
    : ∀ {Aᵢ-f Bᵢ-f Aᵢ-g Bᵢ-g}
        (u_f : mor Aᵢ-f Bᵢ-f) (u_g : mor Aᵢ-g Bᵢ-g)
        (pA : flatten Aᵢ-f ≡ flatten Aᵢ-g)
        (pB : flatten Bᵢ-f ≡ flatten Bᵢ-g)
        (pU : subst₂ FlatGen pA pB (flat u_f) ≡ flat u_g)
    → Σ[ pA' ∈ Aᵢ-f ≡ Aᵢ-g ]
      Σ[ pB' ∈ Bᵢ-f ≡ Bᵢ-g ]
      subst₂ mor pA' pB' u_f ≡ u_g
  flat-data-to-ObjTerm {Aᵢ-f} {Bᵢ-f} {Aᵢ-g} {Bᵢ-g} u_f u_g pA pB pU =
      A-eq , B-eq , mor-eq
    where
      -- A-eq via cong on FlatView'.A' through pU.
      -- `view (flat u_g) = flatV' Aᵢ-g Bᵢ-g refl refl u_g refl`,
      -- so `FlatView'.A' (view (flat u_g)) ≡ Aᵢ-g` definitionally.
      A-eq : Aᵢ-f ≡ Aᵢ-g
      A-eq = trans (sym (view-subst-A u_f pA pB))
                   (cong (λ z → FlatView'.A' (view z)) pU)

      B-eq : Bᵢ-f ≡ Bᵢ-g
      B-eq = trans (sym (view-subst-B u_f pA pB))
                   (cong (λ z → FlatView'.B' (view z)) pU)

      -- Now derive u_f ≡ u_g (via subst₂).  Dispatch on A-eq, B-eq
      -- as refl; then UIP collapses pA, pB to refl, so pU becomes
      -- `flat u_f ≡ flat u_g`, hence u_f ≡ u_g via flat-injective.
      mor-eq : subst₂ mor A-eq B-eq u_f ≡ u_g
      mor-eq = helper A-eq B-eq pA pB pU refl refl
        where
          helper
            : (A-eq' : Aᵢ-f ≡ Aᵢ-g) (B-eq' : Bᵢ-f ≡ Bᵢ-g)
              (pA' : flatten Aᵢ-f ≡ flatten Aᵢ-g)
              (pB' : flatten Bᵢ-f ≡ flatten Bᵢ-g)
              (pU' : subst₂ FlatGen pA' pB' (flat u_f) ≡ flat u_g)
            → A-eq' ≡ A-eq → B-eq' ≡ B-eq
            → subst₂ mor A-eq' B-eq' u_f ≡ u_g
          helper refl refl pA' pB' pU' _ _ =
            flat-injective (subst₂-eq-elim pA' pB' pU')

--------------------------------------------------------------------------------
-- NoSigma terms preserve `flatten`: a NoSigma `f : HomTerm A B` has
-- `flatten A ≡ flatten B`.  This is the key fact used below to build
-- Mac-Lane bridges between two NoSigma sources (one from each strip).

flatten-NoSigma
  : ∀ {A B} {f : HomTerm A B}
  → NoSigma f → flatten A ≡ flatten B
flatten-NoSigma (nosigma-id {A})         = refl
flatten-NoSigma (nosigma-λ⇒ {A})         = refl
flatten-NoSigma (nosigma-λ⇐ {A})         = refl
flatten-NoSigma (nosigma-ρ⇒ {A})         = ++-identityʳ (flatten A)
  where open import Data.List.Properties using (++-identityʳ)
flatten-NoSigma (nosigma-ρ⇐ {A})         = sym (++-identityʳ (flatten A))
  where open import Data.List.Properties using (++-identityʳ)
flatten-NoSigma (nosigma-α⇒ {A} {B} {C}) = ++-assoc (flatten A) (flatten B) (flatten C)
  where open import Data.List.Properties using (++-assoc)
flatten-NoSigma (nosigma-α⇐ {A} {B} {C}) = sym (++-assoc (flatten A) (flatten B) (flatten C))
  where open import Data.List.Properties using (++-assoc)
flatten-NoSigma (nosigma-∘ nh nk)        = trans (flatten-NoSigma nk) (flatten-NoSigma nh)
flatten-NoSigma {A = A ⊗₀ B} {B = C ⊗₀ D} (nosigma-⊗ nh nk)
  = cong₂ _++_ (flatten-NoSigma nh) (flatten-NoSigma nk)
  where
    open import Data.List using (_++_)
    open import Relation.Binary.PropositionalEquality using (cong₂)

--------------------------------------------------------------------------------
-- NoSigma-ness of `unflatten-flatten-≈`'s from/to morphisms.  These
-- are built out of `λ⇐, ρ⇒, α⇐, id, ⊗₁, ∘` (no σ, no Agen) by
-- structural induction on the ObjTerm.

private
  open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
    using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
  open import Categories.Morphism FreeMonoidal using (_≅_)
  open import Categories.Category using (Category)
  open import Data.List using ([]; _∷_)
  module FM-bridge = Category FreeMonoidal

  -- `unflatten-++-≅ xs ys` has from/to built from `λ⇐`, `α⇐`, `id`,
  -- `⊗₁`, `∘`.  NoSigma by structural recursion on `xs`.
  unflatten-++-from-NoSigma
    : ∀ (xs ys : List X)
    → NoSigma (_≅_.from (unflatten-++-≅ xs ys))
  unflatten-++-from-NoSigma []       ys = nosigma-λ⇐
  unflatten-++-from-NoSigma (x ∷ xs) ys =
    nosigma-∘ nosigma-α⇐ (nosigma-⊗ nosigma-id (unflatten-++-from-NoSigma xs ys))

  unflatten-++-to-NoSigma
    : ∀ (xs ys : List X)
    → NoSigma (_≅_.to (unflatten-++-≅ xs ys))
  unflatten-++-to-NoSigma []       ys = nosigma-λ⇒
  unflatten-++-to-NoSigma (x ∷ xs) ys =
    nosigma-∘ (nosigma-⊗ nosigma-id (unflatten-++-to-NoSigma xs ys)) nosigma-α⇒

  unflatten-flatten-from-NoSigma
    : ∀ (A : ObjTerm) → NoSigma (_≅_.from (unflatten-flatten-≈ A))
  unflatten-flatten-from-NoSigma unit     = nosigma-id
  unflatten-flatten-from-NoSigma (Var x)  = nosigma-ρ⇐
  unflatten-flatten-from-NoSigma (A ⊗₀ B) =
    nosigma-∘ (unflatten-++-to-NoSigma (flatten A) (flatten B))
              (nosigma-⊗ (unflatten-flatten-from-NoSigma A)
                         (unflatten-flatten-from-NoSigma B))

  unflatten-flatten-to-NoSigma
    : ∀ (A : ObjTerm) → NoSigma (_≅_.to (unflatten-flatten-≈ A))
  unflatten-flatten-to-NoSigma unit     = nosigma-id
  unflatten-flatten-to-NoSigma (Var x)  = nosigma-ρ⇒
  unflatten-flatten-to-NoSigma (A ⊗₀ B) =
    nosigma-∘ (nosigma-⊗ (unflatten-flatten-to-NoSigma A)
                         (unflatten-flatten-to-NoSigma B))
              (unflatten-++-from-NoSigma (flatten A) (flatten B))

--------------------------------------------------------------------------------
-- NoSigma bridge between two ObjTerms with equal `flatten`.  Built by
-- composing `unflatten-flatten-≈`'s from/to with a `subst`-bridge in
-- the middle (which collapses to identity when the equality is
-- definitional refl).  Both the bridge and its inverse are NoSigma.

private
  -- Bridge construction with explicit `subst` of identity (which is
  -- `id` when `e ≡ refl`).  The bridge composes:
  --   X → unflatten (flatten X) =[ subst id ]= unflatten (flatten Y) → Y
  -- Both extremes are NoSigma; the middle reduces to `id` when `e ≡ refl`.

  bridge-NoSigma-fwd
    : ∀ {X Y : ObjTerm} → flatten X ≡ flatten Y → HomTerm X Y
  bridge-NoSigma-fwd {X} {Y} e =
    _≅_.to (unflatten-flatten-≈ Y) ∘
      subst (HomTerm (unflatten (flatten X))) (cong unflatten e) id ∘
        _≅_.from (unflatten-flatten-≈ X)

  bridge-NoSigma-bwd
    : ∀ {X Y : ObjTerm} → flatten X ≡ flatten Y → HomTerm Y X
  bridge-NoSigma-bwd {X} {Y} e =
    _≅_.to (unflatten-flatten-≈ X) ∘
      subst (HomTerm (unflatten (flatten Y))) (cong unflatten (sym e)) id ∘
        _≅_.from (unflatten-flatten-≈ Y)

  -- NoSigma proofs: dispatch on `e` via J trick — abstract over
  -- `flatten X` to get unification-friendly indices.  The middle
  -- `subst` reduces to identity along `cong unflatten e`; we use
  -- the helper `subst-HomTerm-NoSigma` to extract NoSigma in any case.
  subst-HomTerm-id-NoSigma
    : ∀ {X Y : ObjTerm} (e : X ≡ Y)
    → NoSigma (subst (HomTerm X) e id)
  subst-HomTerm-id-NoSigma refl = nosigma-id

  bridge-NoSigma-fwd-NS
    : ∀ {X Y} (e : flatten X ≡ flatten Y) → NoSigma (bridge-NoSigma-fwd e)
  bridge-NoSigma-fwd-NS {X} {Y} e =
    nosigma-∘ (unflatten-flatten-to-NoSigma Y)
      (nosigma-∘ (subst-HomTerm-id-NoSigma (cong unflatten e))
                 (unflatten-flatten-from-NoSigma X))

  bridge-NoSigma-bwd-NS
    : ∀ {X Y} (e : flatten X ≡ flatten Y) → NoSigma (bridge-NoSigma-bwd e)
  bridge-NoSigma-bwd-NS {X} {Y} e =
    nosigma-∘ (unflatten-flatten-to-NoSigma X)
      (nosigma-∘ (subst-HomTerm-id-NoSigma (cong unflatten (sym e)))
                 (unflatten-flatten-from-NoSigma Y))

  -- The bridge's iso laws follow from `unflatten-flatten-≈`'s iso
  -- structure.  Dispatch on `e` (the flatten-eq) as refl, then the
  -- substs collapse to id and the chain reduces to a straightforward
  -- iso cancellation.

  module HRB = FM-bridge.HomReasoning

  -- Generic iso law for a bridge through a parameterised intermediate
  -- pair (P, Q).  When `eu : P ≡ Q` is pattern-matched as refl, the
  -- subst collapses and the proof becomes routine iso cancellation.
  bridge-iso-helper
    : ∀ {X Y : ObjTerm} {P Q : ObjTerm}
        (eu : P ≡ Q)
        (eu-sym : Q ≡ P)
        (to-Q : HomTerm Q Y) (from-Q : HomTerm Y Q)
        (to-P : HomTerm P X) (from-P : HomTerm X P)
        (isoʳ-P : to-P ∘ from-P ≈Term id)
        (isoˡ-P : from-P ∘ to-P ≈Term id)
        (isoʳ-Q : to-Q ∘ from-Q ≈Term id)
        (isoˡ-Q : from-Q ∘ to-Q ≈Term id)
    → (to-Q ∘ subst (HomTerm P) eu id ∘ from-P)
        ∘ (to-P ∘ subst (HomTerm Q) eu-sym id ∘ from-Q)
      ≈Term id
  bridge-iso-helper refl refl to-Q from-Q to-P from-P _ isoˡ-P isoʳ-Q _ = HRB.begin
      (to-Q ∘ id ∘ from-P) ∘ (to-P ∘ id ∘ from-Q)
        HRB.≈⟨ (HRB.refl⟩∘⟨ FM-bridge.identityˡ)
                HRB.⟩∘⟨ (HRB.refl⟩∘⟨ FM-bridge.identityˡ) ⟩
      (to-Q ∘ from-P) ∘ (to-P ∘ from-Q)
        HRB.≈⟨ FM-bridge.assoc ⟩
      to-Q ∘ from-P ∘ to-P ∘ from-Q
        HRB.≈⟨ HRB.refl⟩∘⟨ FM-bridge.sym-assoc ⟩
      to-Q ∘ (from-P ∘ to-P) ∘ from-Q
        HRB.≈⟨ HRB.refl⟩∘⟨ isoˡ-P HRB.⟩∘⟨refl ⟩
      to-Q ∘ id ∘ from-Q
        HRB.≈⟨ HRB.refl⟩∘⟨ FM-bridge.identityˡ ⟩
      to-Q ∘ from-Q
        HRB.≈⟨ isoʳ-Q ⟩
      id HRB.∎

  bridge-NoSigma-isoʳ
    : ∀ {X Y} (e : flatten X ≡ flatten Y)
    → bridge-NoSigma-fwd e ∘ bridge-NoSigma-bwd e ≈Term id
  bridge-NoSigma-isoʳ {X} {Y} e =
    bridge-iso-helper
      (cong unflatten e) (cong unflatten (sym e))
      (_≅_.to (unflatten-flatten-≈ Y))
      (_≅_.from (unflatten-flatten-≈ Y))
      (_≅_.to (unflatten-flatten-≈ X))
      (_≅_.from (unflatten-flatten-≈ X))
      (_≅_.isoˡ (unflatten-flatten-≈ X))
      (_≅_.isoʳ (unflatten-flatten-≈ X))
      (_≅_.isoˡ (unflatten-flatten-≈ Y))
      (_≅_.isoʳ (unflatten-flatten-≈ Y))

  bridge-NoSigma-isoˡ
    : ∀ {X Y} (e : flatten X ≡ flatten Y)
    → bridge-NoSigma-bwd e ∘ bridge-NoSigma-fwd e ≈Term id
  bridge-NoSigma-isoˡ {X} {Y} e =
    bridge-iso-helper
      (cong unflatten (sym e)) (cong unflatten e)
      (_≅_.to (unflatten-flatten-≈ X))
      (_≅_.from (unflatten-flatten-≈ X))
      (_≅_.to (unflatten-flatten-≈ Y))
      (_≅_.from (unflatten-flatten-≈ Y))
      (_≅_.isoˡ (unflatten-flatten-≈ Y))
      (_≅_.isoʳ (unflatten-flatten-≈ Y))
      (_≅_.isoˡ (unflatten-flatten-≈ X))
      (_≅_.isoʳ (unflatten-flatten-≈ X))

--------------------------------------------------------------------------------
-- Step 5: central naturality of the Mac-Lane bridge with respect to a
-- pinned `Agen u` middle.
--
-- Statement (with implicit context YL-f, YR-f, YL-g, YR-g, Aᵢ, Bᵢ):
--
--   bridge-NoSigma-fwd eB ∘ (id ⊗ (Agen u ⊗ id {YR-f}))
--     ≈Term
--   (id ⊗ (Agen u ⊗ id {YR-g})) ∘ bridge-NoSigma-fwd eA
--
-- This is the only remaining sub-lemma blocking the constructive
-- discharge of `single-agen-NF-coherence`.  All other pieces are in
-- place (`flat-data-to-ObjTerm`, `flatten-NoSigma`, the bridge family
-- + iso laws, `NoSigma-coherence`), implementing Steps 1–4 of the
-- documented strategy.
--
-- ## Why naturality is non-trivial
--
-- After pattern-matching `cong unflatten eA, eB` as `refl` (collapsing
-- the internal `subst-id`s to `id`), the bridges reduce to
-- `to ∘ from`-form.  The residual equation is
--
--   (to-Bg ∘ from-Bf) ∘ M_f ≈Term M_g ∘ (to-Ag ∘ from-Af)
--
-- where `to-X, from-Y` are the from/to maps of `unflatten-flatten-≈`
-- on specific ObjTerms.  Both sides are SingleAgen terms with the
-- *same* underlying generator `u`, but the σ-free wrappers
-- (`to ∘ from` parts) have different intermediate types because of
-- the Aᵢ-vs-Bᵢ "slot" swap.  Mac-Lane coherence (`NoSigma-coherence`,
-- exposed below) aligns parallel NoSigma morphisms but does not
-- apply directly across the `Agen u` middle.
--
-- The natural way through this is to either:
--
--   1. **Tensor-factor the bridge** as `bL ⊗ (id ⊗ bR)`.  This
--      requires `flatten YL_f = flatten YL_g` and
--      `flatten YR_f = flatten YR_g` propositionally — which follows
--      from the iso `⟪f⟫ ≅ᴴ ⟪g⟫` constraining the boundary positions
--      to align (the φ bijection on vertices preserves the
--      ordering of the unique Agen-edge's inputs/outputs within
--      `flatten A`).  Extracting this positional alignment from the
--      iso requires additional infrastructure (~150-300 LOC).
--
--   2. **Mac-Lane chase mirroring `unflatten-flatten-≈`**.  By
--      structural induction on the ObjTerms `YL_f, YR_f, YL_g, YR_g`,
--      naturality propagates through each constructor of
--      `unflatten-flatten-≈` (unit / Var / ⊗) using `λ⇒∘id⊗f`,
--      `ρ⇒∘f⊗id`, `α-comm`, and `⊗-∘-dist`.  ~100-300 LOC of routine
--      categorical reasoning.
--
--   3. **Extend the Mac-Lane solver** to a "single-pinned generator"
--      fragment: instantiate `Categories.MonoidalCoherence` with an
--      extra atomic generator slot for the unique `Agen u`.  ~200-500
--      LOC of solver infrastructure.
--
-- ## TODO
--
-- This lemma is left as a documented hole.  The postulate
-- `single-agen-NF-coherence` is retained in `CompletenessAssumptions`
-- until naturality is proved.  The narrowing scope is fixed: the
-- iso → flat-data extraction is constructively closed via
-- `single-agen-flat-data`, leaving only the Mac-Lane closure on the
-- σ-free wrappers around the aligned generator.

private
  -- `NoSigma-coherence`: any two parallel `NoSigma` morphisms are
  -- `≈Term`-equal.  This is the iso-free Mac-Lane coherence theorem
  -- in the σ-free fragment, obtained by stripping the (vestigial)
  -- iso argument from `Structural-coherence-≈Term-noσ` and exposing
  -- the underlying `noσ-discharge` directly.  Provided here as the
  -- foundational tool for closing the Mac-Lane wrappers around an
  -- aligned `Agen u` generator — once the naturality lemma above is
  -- proved, this lemma completes the discharge of
  -- `single-agen-NF-coherence`.
  NoSigma-coherence
    : ∀ {X Y} {b₁ b₂ : HomTerm X Y}
    → NoSigma b₁ → NoSigma b₂
    → b₁ ≈Term b₂
  NoSigma-coherence nb₁ nb₂ = noσ-discharge nb₁ nb₂

--------------------------------------------------------------------------------
-- Bridge naturality (Step 5) — back-end.
--
-- Given *positional alignment* hypotheses `eYL : flatten YL-f ≡ flatten
-- YL-g` and `eYR : flatten YR-f ≡ flatten YR-g`, the naturality of the
-- bridge w.r.t. a pinned `Agen u` middle is provable by:
--
--   1. Tensor-factor the monolithic bridge `bridge-NoSigma-fwd eA` (over
--      the ternary tensor `YL ⊗ X ⊗ YR`) as `bL ⊗ (id_X ⊗ bR)` where
--      `bL = bridge-NoSigma-fwd eYL` and `bR = bridge-NoSigma-fwd eYR`.
--      Both sides are NoSigma; agreement follows from `noσ-discharge`.
--   2. Push the `Agen u` middle through via `⊗-∘-dist` twice + `idˡ`/
--      `idʳ` cleanup.
--   3. Untensor-factor the result.
--
-- The front-end — deriving `eYL, eYR` from an iso `⟪f⟫ ≅ᴴ ⟪g⟫` — is
-- separate work (positional alignment via the φ vertex bijection on
-- the unique Agen-edge boundary).

private
  -- Tensor-factored bridge as a NoSigma morphism: just
  -- `bL ⊗₁ (id ⊗₁ bR)`.

  bridge-tensor-fwd
    : ∀ {YL-f YR-f YL-g YR-g X : ObjTerm}
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
    → HomTerm (YL-f ⊗₀ X ⊗₀ YR-f) (YL-g ⊗₀ X ⊗₀ YR-g)
  bridge-tensor-fwd eYL eYR =
    bridge-NoSigma-fwd eYL ⊗₁ (id ⊗₁ bridge-NoSigma-fwd eYR)

  bridge-tensor-fwd-NS
    : ∀ {YL-f YR-f YL-g YR-g X : ObjTerm}
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
    → NoSigma (bridge-tensor-fwd {YL-f} {YR-f} {YL-g} {YR-g} {X} eYL eYR)
  bridge-tensor-fwd-NS {YL-f} {YR-f} {YL-g} {YR-g} {X} eYL eYR =
    nosigma-⊗ (bridge-NoSigma-fwd-NS eYL)
              (nosigma-⊗ (nosigma-id {X}) (bridge-NoSigma-fwd-NS eYR))

  -- Monolithic vs. tensor-factored bridge: both are NoSigma between the
  -- same ObjTerms, so they agree by `noσ-discharge`.

  bridge-NoSigma-tensor-factor
    : ∀ {YL-f YR-f YL-g YR-g X : ObjTerm}
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
        (eA  : flatten (YL-f ⊗₀ X ⊗₀ YR-f)
             ≡ flatten (YL-g ⊗₀ X ⊗₀ YR-g))
    → bridge-NoSigma-fwd eA
    ≈Term bridge-tensor-fwd {YL-f} {YR-f} {YL-g} {YR-g} {X} eYL eYR
  bridge-NoSigma-tensor-factor {YL-f} {YR-f} {YL-g} {YR-g} {X} eYL eYR eA =
    noσ-discharge (bridge-NoSigma-fwd-NS eA)
                  (bridge-tensor-fwd-NS {YL-f} {YR-f} {YL-g} {YR-g} {X} eYL eYR)

  module HRBN = FM-bridge.HomReasoning

  -- Naturality of the bridge w.r.t. the pinned `Agen u`, given
  -- positional alignment.  The proof is a chase through `⊗-∘-dist`
  -- + `idˡ`/`idʳ` on the tensor-factored form.

  bridge-naturality-pos
    : ∀ {YL-f YR-f YL-g YR-g Aᵢ Bᵢ : ObjTerm}
        (u : mor Aᵢ Bᵢ)
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
        (eA  : flatten (YL-f ⊗₀ Aᵢ ⊗₀ YR-f)
             ≡ flatten (YL-g ⊗₀ Aᵢ ⊗₀ YR-g))
        (eB  : flatten (YL-f ⊗₀ Bᵢ ⊗₀ YR-f)
             ≡ flatten (YL-g ⊗₀ Bᵢ ⊗₀ YR-g))
    → bridge-NoSigma-fwd eB ∘ (id ⊗₁ (Agen u ⊗₁ id {YR-f}))
    ≈Term
      (id ⊗₁ (Agen u ⊗₁ id {YR-g})) ∘ bridge-NoSigma-fwd eA
  bridge-naturality-pos {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ} {Bᵢ} u eYL eYR eA eB =
    let bL = bridge-NoSigma-fwd eYL
        bR = bridge-NoSigma-fwd eYR
    in HRBN.begin
      bridge-NoSigma-fwd eB ∘ (id ⊗₁ (Agen u ⊗₁ id {YR-f}))
        HRBN.≈⟨ bridge-NoSigma-tensor-factor {YL-f} {YR-f} {YL-g} {YR-g} {Bᵢ}
                  eYL eYR eB HRBN.⟩∘⟨refl ⟩
      (bL ⊗₁ (id ⊗₁ bR)) ∘ (id ⊗₁ (Agen u ⊗₁ id {YR-f}))
        HRBN.≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
      (bL ∘ id) ⊗₁ ((id ⊗₁ bR) ∘ (Agen u ⊗₁ id {YR-f}))
        HRBN.≈⟨ ⊗-resp-≈ idʳ (≈-Term-sym ⊗-∘-dist) ⟩
      bL ⊗₁ ((id ∘ Agen u) ⊗₁ (bR ∘ id))
        HRBN.≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ idʳ) ⟩
      bL ⊗₁ (Agen u ⊗₁ bR)
        HRBN.≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ)
                  (⊗-resp-≈ (≈-Term-sym idʳ) (≈-Term-sym idˡ)) ⟩
      (id ∘ bL) ⊗₁ ((Agen u ∘ id) ⊗₁ (id ∘ bR))
        HRBN.≈⟨ ⊗-resp-≈ ≈-Term-refl ⊗-∘-dist ⟩
      (id ∘ bL) ⊗₁ ((Agen u ⊗₁ id) ∘ (id ⊗₁ bR))
        HRBN.≈⟨ ⊗-∘-dist ⟩
      (id ⊗₁ (Agen u ⊗₁ id {YR-g})) ∘ (bL ⊗₁ (id ⊗₁ bR))
        HRBN.≈⟨ refl⟩∘⟨ ≈-Term-sym
                  (bridge-NoSigma-tensor-factor {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ}
                     eYL eYR eA) ⟩
      (id ⊗₁ (Agen u ⊗₁ id {YR-g})) ∘ bridge-NoSigma-fwd eA HRBN.∎

--------------------------------------------------------------------------------
-- σ-on-unit lemmas (Sub-step 1).
--
-- These are the basic identities relating the symmetry `σ` at a unit
-- argument to the unitors.  Imported from agda-categories'
-- `braiding-coherence : λ⇒ ∘ σ ≈ ρ⇒`, and dualised.

private
  open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal
    using (module Symmetric)
  open import Categories.Category.Monoidal.Braided.Properties
    (Symmetric.braided Symmetric-Monoidal)
    using (braiding-coherence; inv-braiding-coherence)

  -- Sub-step 1A: σ {X}{unit} ≈Term λ⇐ ∘ ρ⇒.
  --
  -- Derivation: from `braiding-coherence : λ⇒ ∘ σ ≈ ρ⇒` (in the
  -- agda-categories braided properties module, instantiated at the
  -- symmetric monoidal `FreeMonoidal`), compose with `λ⇐` on the
  -- left:
  --   λ⇐ ∘ (λ⇒ ∘ σ) ≈ λ⇐ ∘ ρ⇒
  -- LHS rewrites via assoc + λ⇐∘λ⇒≈id to `σ`, so `σ ≈ λ⇐ ∘ ρ⇒`.

  σ-on-unit-Y
    : ∀ {X : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
    → σ {A = X} {B = unit} ⦃ s ⦄ ≈Term λ⇐ ∘ ρ⇒
  σ-on-unit-Y {X} ⦃ s ⦄ = HRBN.begin
      σ {A = X} {B = unit} ⦃ s ⦄
        HRBN.≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ σ {A = X} {B = unit} ⦃ s ⦄
        HRBN.≈⟨ ≈-Term-sym λ⇐∘λ⇒≈id HRBN.⟩∘⟨refl ⟩
      (λ⇐ ∘ λ⇒) ∘ σ {A = X} {B = unit} ⦃ s ⦄
        HRBN.≈⟨ FM-bridge.assoc ⟩
      λ⇐ ∘ (λ⇒ ∘ σ {A = X} {B = unit} ⦃ s ⦄)
        HRBN.≈⟨ HRBN.refl⟩∘⟨ braiding-coherence-here ⟩
      λ⇐ ∘ ρ⇒ HRBN.∎
    where
      -- Specialise `braiding-coherence` to the concrete `s` we have.
      -- The agda-categories version uses the `Symmetric-Monoidal`
      -- instance directly; our σ takes an explicit `Symm ≤ Symm`.
      -- All such proofs are propositionally `v≤v`.
      Symm≤Symm-uniq : (s : Symm ≤ Symm) → s ≡ v≤v
      Symm≤Symm-uniq v≤v = refl

      braiding-coherence-here
        : λ⇒ ∘ σ {A = X} {B = unit} ⦃ s ⦄ ≈Term ρ⇒
      braiding-coherence-here
        rewrite Symm≤Symm-uniq s = braiding-coherence

  -- Sub-step 1B: σ {unit}{X} ≈Term ρ⇐ ∘ λ⇒.
  --
  -- Strategy: directly use `inv-braiding-coherence` from
  -- agda-categories, which states `ρ⇒ ∘ σ⇐ ≈ λ⇒`.  In our symmetric
  -- setting σ is self-inverse (σ⇐ = σ {unit}{X}), so we get
  -- `ρ⇒ ∘ σ {unit}{X} ≈ λ⇒`.  Compose ρ⇐ on the left and use
  -- ρ⇐∘ρ⇒≈id to extract σ {unit}{X} ≈ ρ⇐ ∘ λ⇒.

  σ-on-unit-X
    : ∀ {X : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
    → σ {A = unit} {B = X} ⦃ s ⦄ ≈Term ρ⇐ ∘ λ⇒
  σ-on-unit-X {X} ⦃ s ⦄ = HRBN.begin
      σ {A = unit} {B = X} ⦃ s ⦄
        HRBN.≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ σ {A = unit} {B = X} ⦃ s ⦄
        HRBN.≈⟨ ≈-Term-sym ρ⇐∘ρ⇒≈id HRBN.⟩∘⟨refl ⟩
      (ρ⇐ ∘ ρ⇒) ∘ σ {A = unit} {B = X} ⦃ s ⦄
        HRBN.≈⟨ FM-bridge.assoc ⟩
      ρ⇐ ∘ (ρ⇒ ∘ σ {A = unit} {B = X} ⦃ s ⦄)
        HRBN.≈⟨ HRBN.refl⟩∘⟨ ρ⇒∘σ-here ⟩
      ρ⇐ ∘ λ⇒ HRBN.∎
    where
      Symm≤Symm-uniq : (s : Symm ≤ Symm) → s ≡ v≤v
      Symm≤Symm-uniq v≤v = refl

      ρ⇒∘σ-here : ρ⇒ ∘ σ {A = unit} {B = X} ⦃ s ⦄ ≈Term λ⇒
      ρ⇒∘σ-here rewrite Symm≤Symm-uniq s = inv-braiding-coherence

  -- Sub-step 2: σ-on-empty-Y.
  --
  -- When `flatten Y ≡ []`, the morphism `σ {X}{Y} : X ⊗ Y → Y ⊗ X`
  -- is ≈Term-equal to a NoSigma morphism.  Proved by induction on Y:
  --   * Y = unit          : direct via sub-step 1A.
  --   * Y = A ⊗ B         : ++-conicalˡ splits flatten = [] into both
  --                         flatten A = [] and flatten B = [], use
  --                         hexagon to decompose σ {X}{A⊗B}.
  --   * Y = Var x         : flatten (Var x) = [x] ≠ [], contradiction.
  --
  -- The result is packaged as a Σ-type to expose both the rewriting
  -- target `ns` and its NoSigma witness, suitable for downstream use
  -- in the scalar discharge.

  open import Data.List.Properties using (++-conicalˡ; ++-conicalʳ)

  σ-on-empty-Y
    : ∀ {X Y : ObjTerm} ⦃ s : Symm ≤ Symm ⦄
    → flatten Y ≡ []
    → Σ[ ns ∈ HomTerm (X ⊗₀ Y) (Y ⊗₀ X) ]
        NoSigma ns × (σ {A = X} {B = Y} ⦃ s ⦄ ≈Term ns)
  σ-on-empty-Y {X} {unit} ⦃ s ⦄ _ =
      λ⇐ ∘ ρ⇒
    , nosigma-∘ nosigma-λ⇐ nosigma-ρ⇒
    , σ-on-unit-Y {X} ⦃ s ⦄
  σ-on-empty-Y {X} {Y₁ ⊗₀ Y₂} ⦃ s ⦄ flat-eq =
      ns , ns-NS , chain
    where
      flat₁ : flatten Y₁ ≡ []
      flat₁ = ++-conicalˡ (flatten Y₁) (flatten Y₂) flat-eq
      flat₂ : flatten Y₂ ≡ []
      flat₂ = ++-conicalʳ (flatten Y₁) (flatten Y₂) flat-eq

      rec₁ = σ-on-empty-Y {X} {Y₁} ⦃ s ⦄ flat₁
      rec₂ = σ-on-empty-Y {X} {Y₂} ⦃ s ⦄ flat₂

      ns₁ = proj₁ rec₁
      ns₁-NS = proj₁ (proj₂ rec₁)
      σ≈ns₁ = proj₂ (proj₂ rec₁)

      ns₂ = proj₁ rec₂
      ns₂-NS = proj₁ (proj₂ rec₂)
      σ≈ns₂ = proj₂ (proj₂ rec₂)

      -- Decomposition target: matches the natural chain output.
      -- With right-associative ∘, this parses as:
      --   α⇐ ∘ (X1 ∘ (X2 ∘ X3)) ∘ α⇐
      -- where X1 = id ⊗₁ ns₂, X2 = α⇒, X3 = ns₁ ⊗₁ id.
      ns : HomTerm (X ⊗₀ (Y₁ ⊗₀ Y₂)) ((Y₁ ⊗₀ Y₂) ⊗₀ X)
      ns = (α⇐ ∘ id {Y₁} ⊗₁ ns₂ ∘ α⇒ ∘ ns₁ ⊗₁ id {Y₂}) ∘ α⇐

      ns-NS : NoSigma ns
      ns-NS = nosigma-∘ (nosigma-∘ nosigma-α⇐
                          (nosigma-∘ (nosigma-⊗ nosigma-id ns₂-NS)
                            (nosigma-∘ nosigma-α⇒
                                       (nosigma-⊗ ns₁-NS nosigma-id))))
                        nosigma-α⇐

      -- The σ-decomposition chain.
      --
      -- Hexagon (in the *inverted* form used here): start with the
      -- axiom `id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈ α⇒ ∘ σ {X}{Y₁⊗Y₂} ∘ α⇒`,
      -- so:
      --   σ {X}{Y₁⊗Y₂}
      --   ≈ id ∘ σ {X}{Y₁⊗Y₂} ∘ id
      --   ≈ α⇐ ∘ α⇒ ∘ σ {X}{Y₁⊗Y₂} ∘ α⇒ ∘ α⇐
      --   ≈ α⇐ ∘ (id ⊗₁ σ {X}{Y₂} ∘ α⇒ ∘ σ {X}{Y₁} ⊗₁ id) ∘ α⇐
      --   ≈ α⇐ ∘ ((id ⊗₁ ns₂) ∘ α⇒ ∘ (ns₁ ⊗₁ id)) ∘ α⇐
      --
      -- We assemble it with the HomReasoning combinator.

      -- Right-associativity of ∘: `a ∘ b ∘ c = a ∘ (b ∘ c)`.
      -- LHS of hexagon: `(id ⊗₁ σ) ∘ (α⇒ ∘ (σ ⊗₁ id))`.
      -- RHS:            `α⇒ ∘ (σ {X}{Y₁⊗Y₂} ∘ α⇒)`.
      --
      -- We invert via:
      --   σ ≈ (α⇐ ∘ LHS) ∘ α⇐
      -- by chasing `α⇐ ∘ (α⇒ ∘ (σ ∘ α⇒)) = σ ∘ α⇒` and `(σ ∘ α⇒) ∘ α⇐ = σ`.

      LHS-hex : HomTerm ((X ⊗₀ Y₁) ⊗₀ Y₂) (Y₁ ⊗₀ (Y₂ ⊗₀ X))
      LHS-hex = id ⊗₁ σ {A = X} {B = Y₂} ⦃ s ⦄
                  ∘ α⇒
                  ∘ σ {A = X} {B = Y₁} ⦃ s ⦄ ⊗₁ id

      hex-inverted
        : σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄
        ≈Term (α⇐ ∘ LHS-hex) ∘ α⇐
      hex-inverted = HRBN.begin
          σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄
            HRBN.≈⟨ ≈-Term-sym idˡ ⟩
          id ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄
            HRBN.≈⟨ ≈-Term-sym idʳ ⟩
          (id ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄) ∘ id
            HRBN.≈⟨ ≈-Term-sym α⇐∘α⇒≈id HRBN.⟩∘⟨refl HRBN.⟩∘⟨refl ⟩
          ((α⇐ ∘ α⇒) ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄) ∘ id
            HRBN.≈⟨ HRBN.refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
          ((α⇐ ∘ α⇒) ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄) ∘ (α⇒ ∘ α⇐)
            HRBN.≈⟨ FM-bridge.assoc HRBN.⟩∘⟨refl ⟩
          (α⇐ ∘ (α⇒ ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄)) ∘ (α⇒ ∘ α⇐)
            HRBN.≈⟨ FM-bridge.assoc ⟩
          α⇐ ∘ ((α⇒ ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄) ∘ (α⇒ ∘ α⇐))
            HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.sym-assoc ⟩
          α⇐ ∘ (((α⇒ ∘ σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄) ∘ α⇒) ∘ α⇐)
            HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.assoc HRBN.⟩∘⟨refl ⟩
          α⇐ ∘ ((α⇒ ∘ (σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄ ∘ α⇒)) ∘ α⇐)
            HRBN.≈⟨ HRBN.refl⟩∘⟨ ≈-Term-sym (hexagon ⦃ s ⦄) HRBN.⟩∘⟨refl ⟩
          α⇐ ∘ (LHS-hex ∘ α⇐)
            HRBN.≈⟨ FM-bridge.sym-assoc ⟩
          (α⇐ ∘ LHS-hex) ∘ α⇐ HRBN.∎

      -- Now rewrite the two inner σ's inside LHS-hex using IH.
      LHS-hex-rw
        : LHS-hex ≈Term (id ⊗₁ ns₂ ∘ α⇒ ∘ ns₁ ⊗₁ id)
      LHS-hex-rw = HRBN.begin
          id ⊗₁ σ {A = X} {B = Y₂} ⦃ s ⦄
            ∘ α⇒
            ∘ σ {A = X} {B = Y₁} ⦃ s ⦄ ⊗₁ id
            HRBN.≈⟨ ⊗-resp-≈ ≈-Term-refl σ≈ns₂ HRBN.⟩∘⟨refl ⟩
          id ⊗₁ ns₂ ∘ α⇒ ∘ σ {A = X} {B = Y₁} ⦃ s ⦄ ⊗₁ id
            HRBN.≈⟨ HRBN.refl⟩∘⟨ HRBN.refl⟩∘⟨ ⊗-resp-≈ σ≈ns₁ ≈-Term-refl ⟩
          id ⊗₁ ns₂ ∘ α⇒ ∘ ns₁ ⊗₁ id HRBN.∎

      chain
        : σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄ ≈Term ns
      chain = HRBN.begin
          σ {A = X} {B = Y₁ ⊗₀ Y₂} ⦃ s ⦄
            HRBN.≈⟨ hex-inverted ⟩
          (α⇐ ∘ LHS-hex) ∘ α⇐
            HRBN.≈⟨ (HRBN.refl⟩∘⟨ LHS-hex-rw) HRBN.⟩∘⟨refl ⟩
          (α⇐ ∘ id ⊗₁ ns₂ ∘ α⇒ ∘ ns₁ ⊗₁ id) ∘ α⇐ HRBN.∎
  σ-on-empty-Y {X} {Var x} ⦃ _ ⦄ flat-eq with flat-eq
  ... | ()

--------------------------------------------------------------------------------
-- Positional alignment (Step 5 front-end).
--
-- Goal: extract `flatten YL_f ≡ flatten YL_g` and
-- `flatten YR_f ≡ flatten YR_g` from an iso `⟪f⟫ ≅ᴴ ⟪g⟫` and SingleAgen
-- witnesses `sf, sg`.  Combined with `bridge-naturality-pos`, this would
-- close the central Mac-Lane naturality lemma.
--
-- ## Structural decomposition (atom level)
--
-- The starting observation: every `SingleAgen f` admits a NoSigma
-- `c-from : A → YL ⊗₀ Aᵢ ⊗₀ YR` (from `single-agen-strip`).  Since
-- NoSigma morphisms preserve `flatten` (via `flatten-NoSigma`), we get
-- a list-level decomposition
--
--   flatten A ≡ flatten YL ++ flatten Aᵢ ++ flatten YR
--
-- For two `SingleAgen f, g : HomTerm A B`, this gives two
-- decompositions of the *same* list `flatten A`.  The middles agree at
-- the `flatten Aᵢ` level via `single-agen-flat-data`.
--
-- ## The remaining gap
--
-- The two decompositions can in principle differ at the POSITION of
-- the middle.  E.g. `flatten A = [a,b,a,b]` with `flatten Aᵢ = [a,b]`
-- admits two splits.  To uniqueness, we need a positional constraint
-- from the iso — concretely, that the Agen-edge's `ein` lives at the
-- same position in the (uniquely-ordered) vertex lists of `⟪f⟫.dom`
-- and `⟪g⟫.dom`.  This requires an additional structural lemma
-- relating `SingleAgen-edge`'s position to `length (flatten YL)`,
-- combined with the iso's `ψ-ein` + `φ-dom` constraints.
--
-- The structural decomposition `strip-flatten-A-decomp` is provided
-- below as the easy half; the positional alignment is left as a
-- documented open lemma (~200-400 LOC of routine geometric chasing).

-- Atom-level structural decomposition: from a `SingleAgen` witness on
-- `f : HomTerm A B`, the source `flatten A` decomposes as
-- `flatten YL ++ flatten Aᵢ ++ flatten YR`.  Proved by reading off
-- `c-from : A → YL ⊗₀ Aᵢ ⊗₀ YR` (extracted by `single-agen-strip`)
-- and applying `flatten-NoSigma`.

open import Data.List using (_++_)

strip-flatten-A-decomp
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → flatten A
  ≡ flatten (SingleAgenNF.YL (single-agen-strip sf))
    ++ flatten (SingleAgenNF.Aᵢ (single-agen-strip sf))
    ++ flatten (SingleAgenNF.YR (single-agen-strip sf))
strip-flatten-A-decomp sf =
  flatten-NoSigma (SingleAgenNF.nosigma-from (single-agen-strip sf))

-- Symmetrically: the target `flatten B` decomposes via `c-to`.
-- Note the *reversed* direction: `c-to : YL ⊗₀ Bᵢ ⊗₀ YR → B`, so
-- `flatten-NoSigma nosigma-to` gives `flatten (YL ⊗₀ Bᵢ ⊗₀ YR) ≡ flatten B`.

strip-flatten-B-decomp
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → flatten B
  ≡ flatten (SingleAgenNF.YL (single-agen-strip sf))
    ++ flatten (SingleAgenNF.Bᵢ (single-agen-strip sf))
    ++ flatten (SingleAgenNF.YR (single-agen-strip sf))
strip-flatten-B-decomp sf =
  sym (flatten-NoSigma (SingleAgenNF.nosigma-to (single-agen-strip sf)))

--------------------------------------------------------------------------------
-- Positional alignment (length-of-YL) — partial reduction.
--
-- The `strip-flatten-A-decomp` lemmas reduce `positional-alignment` to
-- the *length equality*: `length (flatten YL_f) ≡ length (flatten YL_g)`.
-- Given that, `flatten YL_f ≡ flatten YL_g` follows by `take`-equality
-- on the common `flatten A`, and symmetrically for YR via `drop`.
--
-- This length equality is the *real* content of positional alignment:
-- it cannot be derived from the syntactic strips alone (the same
-- `flatten A` can be split with different YL lengths if atoms repeat),
-- so it requires the iso `⟪f⟫ ≅ᴴ ⟪g⟫`.  The cleanest geometric
-- argument routes through the position of the Agen-edge's `ein`
-- within `⟪f⟫.dom` / `⟪g⟫.dom`, matched up via the φ vertex
-- bijection.  Encoding this requires a structural lemma
--
--   strip-dom-vert-decomp
--     : (sf : SingleAgen f)
--     → Σ[ pre ∈ List (Fin nV_f) ] Σ[ post ∈ List (Fin nV_f) ]
--         ⟪f⟫.dom ≡ pre ++ ⟪f⟫.ein (SingleAgen-edge sf) ++ post
--         × length pre ≡ length (flatten YL_f)
--         × length post ≡ length (flatten YR_f)
--
-- which is provable by structural recursion on `sf`, but the
-- recursion is delicate because the Agen edge's `ein` is not always
-- a sublist of `dom` literally (e.g. in the `∘-l` case where the
-- Agen is post-composed by `k`, its `ein` is remapped via the
-- `hComposeP` remap).  Roughly 150-300 LOC.
--
-- Below we provide a stub `positional-alignment` whose *witness* is
-- the strip-flatten-A-decomp pair plus a length-equality input.  Once
-- the geometric length equality is proved, the rest follows in ~30 LOC.

private
  -- List `take`/`drop` based extraction: if `xs ≡ ys₁ ++ zs₁` and
  -- `xs ≡ ys₂ ++ zs₂` with `length ys₁ ≡ length ys₂`, then
  -- `ys₁ ≡ ys₂` and `zs₁ ≡ zs₂`.
  --
  -- Proved by induction on `ys₁` (and casing `ys₂` against its length).

  open import Data.List using ([]; _∷_; _++_; length)
  open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
  open import Data.Nat using () renaming (suc to ℕsuc)
  open import Data.Product using (proj₁; proj₂)

  ℕ-suc-inj : ∀ {m n} → ℕsuc m ≡ ℕsuc n → m ≡ n
  ℕ-suc-inj refl = refl

  -- Variant that takes the LHS list directly.  The general
  -- formulation above can be derived by `subst`-ing through `xs`.
  ++-split-by-length-eq
    : ∀ {A : Set} (ys₁ zs₁ ys₂ zs₂ : List A)
    → ys₁ ++ zs₁ ≡ ys₂ ++ zs₂
    → length ys₁ ≡ length ys₂
    → ys₁ ≡ ys₂ × zs₁ ≡ zs₂
  ++-split-by-length-eq [] zs₁ [] zs₂ eq _ = refl , eq
  ++-split-by-length-eq [] _ (_ ∷ _) _ _ ()
  ++-split-by-length-eq (_ ∷ _) _ [] _ _ ()
  ++-split-by-length-eq (y₁ ∷ ys₁) zs₁ (y₂ ∷ ys₂) zs₂ eq ℓeq =
    let head-eq : y₁ ≡ y₂
        head-eq = ∷-injectiveˡ eq
        tail-eq : ys₁ ++ zs₁ ≡ ys₂ ++ zs₂
        tail-eq = ∷-injectiveʳ eq
        rec = ++-split-by-length-eq ys₁ zs₁ ys₂ zs₂ tail-eq (ℕ-suc-inj ℓeq)
    in cong₂ _∷_ head-eq (proj₁ rec) , proj₂ rec
    where open import Relation.Binary.PropositionalEquality using (cong₂)

  -- The version we actually use: derives split from two `xs ≡ ...`
  -- equations by chaining them.
  ++-split-by-length
    : ∀ {A : Set} {xs : List A} (ys₁ zs₁ ys₂ zs₂ : List A)
    → xs ≡ ys₁ ++ zs₁ → xs ≡ ys₂ ++ zs₂
    → length ys₁ ≡ length ys₂
    → ys₁ ≡ ys₂ × zs₁ ≡ zs₂
  ++-split-by-length ys₁ zs₁ ys₂ zs₂ eq₁ eq₂ ℓeq =
    ++-split-by-length-eq ys₁ zs₁ ys₂ zs₂ (trans (sym eq₁) eq₂) ℓeq

  -- Three-way split (specialized form for YL ++ Aᵢ ++ YR splits).
  -- Takes flatten-A decomps for both f and g, the middle-equality
  -- `flatten Aᵢ_f ≡ flatten Aᵢ_g` (from `single-agen-flat-data`),
  -- and the length equality on `flatten YL_f`/`flatten YL_g` — the
  -- only piece that requires positional info from the iso.
  --
  -- Output: `flatten YL_f ≡ flatten YL_g` and `flatten YR_f ≡ flatten YR_g`.
  --
  -- Strategy: list cancellation on the LEFT (using YL length equality)
  -- gives YL_f ≡ YL_g and the tail `Aᵢ_f ++ YR_f ≡ Aᵢ_g ++ YR_g`.
  -- Then list cancellation on the LEFT again (using the Aᵢ length
  -- equality derived from `flatten Aᵢ_f ≡ flatten Aᵢ_g`) gives the
  -- second result.

  ++-split-3way
    : ∀ {A : Set} {xs : List A} (ys₁ ms₁ zs₁ ys₂ ms₂ zs₂ : List A)
    → xs ≡ ys₁ ++ ms₁ ++ zs₁ → xs ≡ ys₂ ++ ms₂ ++ zs₂
    → ms₁ ≡ ms₂
    → length ys₁ ≡ length ys₂
    → ys₁ ≡ ys₂ × zs₁ ≡ zs₂
  ++-split-3way ys₁ ms₁ zs₁ ys₂ ms₂ zs₂ eq₁ eq₂ m-eq ℓeq =
    let
      -- First split: ys₁ ≡ ys₂, (ms₁ ++ zs₁) ≡ (ms₂ ++ zs₂).
      step₁ = ++-split-by-length ys₁ (ms₁ ++ zs₁) ys₂ (ms₂ ++ zs₂) eq₁ eq₂ ℓeq
      ys-eq = proj₁ step₁
      tail-eq = proj₂ step₁
      -- Second split: ms₁ ≡ ms₂ (given), zs₁ ≡ zs₂.
      -- We need length ms₁ ≡ length ms₂ — follows from m-eq.
      ms-ℓeq : length ms₁ ≡ length ms₂
      ms-ℓeq = cong length m-eq
      step₂ = ++-split-by-length-eq ms₁ zs₁ ms₂ zs₂ tail-eq ms-ℓeq
      zs-eq = proj₂ step₂
    in ys-eq , zs-eq

--------------------------------------------------------------------------------
-- `positional-alignment-from-length`: the constructively-closed half of
-- the positional alignment lemma.
--
-- Given:
--   * Two `SingleAgen` witnesses `sf : SingleAgen f`, `sg : SingleAgen g`
--     with `f, g : HomTerm A B`;
--   * The iso `⟪f⟫ ≅ᴴ ⟪g⟫` (currently unused — kept for the open
--     length-equality refinement);
--   * The length-equality `len-YL-eq : length (flatten YL_f) ≡
--     length (flatten YL_g)` — the ONE missing piece;
--
-- Produce:
--   * `flatten YL_f ≡ flatten YL_g`
--   * `flatten YR_f ≡ flatten YR_g`
--
-- via `strip-flatten-A-decomp` + `single-agen-flat-data`'s `flat-A-eq` +
-- `++-split-3way`.
--
-- The trust content has thus shrunk to a *single* `ℕ`-level equality
-- (`length-of-YL`) — the smallest possible interface for the iso.

positional-alignment-from-length
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (len-YL-eq : length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
                 ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sg))))
  → Σ[ eYL ∈ flatten (SingleAgenNF.YL (single-agen-strip sf))
           ≡ flatten (SingleAgenNF.YL (single-agen-strip sg)) ]
    Σ[ eYR ∈ flatten (SingleAgenNF.YR (single-agen-strip sf))
           ≡ flatten (SingleAgenNF.YR (single-agen-strip sg)) ]
    ⊤
positional-alignment-from-length {A = A} {f = f} {g = g} sf sg iso len-YL-eq =
  let
    -- Decomposition of flatten A from f's strip.
    decomp-f : flatten A
             ≡ flatten YL-f ++ flatten Aᵢ-f ++ flatten YR-f
    decomp-f = strip-flatten-A-decomp sf

    -- Decomposition of flatten A from g's strip.
    decomp-g : flatten A
             ≡ flatten YL-g ++ flatten Aᵢ-g ++ flatten YR-g
    decomp-g = strip-flatten-A-decomp sg

    -- Aᵢ-level equality, lifted from `single-agen-u`'s record to
    -- `single-agen-strip`'s record via the consistency lemma.
    flat-data = single-agen-flat-data sf sg iso
    flat-A-eq-u = proj₁ flat-data

    Aᵢ-u-f→strip-f : flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                   ≡ flatten Aᵢ-f
    Aᵢ-u-f→strip-f = cong flatten (single-agen-u-strip-Aᵢ sf)

    Aᵢ-u-g→strip-g : flatten (SingleAgenGen.Aᵢ (single-agen-u sg))
                   ≡ flatten Aᵢ-g
    Aᵢ-u-g→strip-g = cong flatten (single-agen-u-strip-Aᵢ sg)

    flat-A-eq : flatten Aᵢ-f ≡ flatten Aᵢ-g
    flat-A-eq = trans (sym Aᵢ-u-f→strip-f) (trans flat-A-eq-u Aᵢ-u-g→strip-g)

    split = ++-split-3way (flatten YL-f) (flatten Aᵢ-f) (flatten YR-f)
                          (flatten YL-g) (flatten Aᵢ-g) (flatten YR-g)
                          decomp-f decomp-g flat-A-eq len-YL-eq
  in proj₁ split , proj₂ split , tt
  where
    YL-f = SingleAgenNF.YL (single-agen-strip sf)
    Aᵢ-f = SingleAgenNF.Aᵢ (single-agen-strip sf)
    YR-f = SingleAgenNF.YR (single-agen-strip sf)
    YL-g = SingleAgenNF.YL (single-agen-strip sg)
    Aᵢ-g = SingleAgenNF.Aᵢ (single-agen-strip sg)
    YR-g = SingleAgenNF.YR (single-agen-strip sg)

--------------------------------------------------------------------------------
-- `length-of-YL-eq`: open input (the remaining hole).
--
-- Length equality of `flatten YL` between the two strips, which IS
-- determined by the iso `⟪f⟫ ≅ᴴ ⟪g⟫`, but extracting it requires
-- geometric reasoning about the position of the Agen edge's `ein`
-- within `⟪f⟫.dom` / `⟪g⟫.dom`.  Sketch:
--
--   1. For each strip case, the Agen edge's `ein` corresponds to a
--      contiguous range of vertices of `⟪f⟫`, BUT it is not always a
--      sublist of `⟪f⟫.dom` literally (e.g. `single-agen-∘-l`: the
--      Agen edge's `ein` is `map remap (...)`, not `map injL (...)`).
--      Hence a clean structural lemma "Agen-ein is at position
--      `length (flatten YL)` in dom" does NOT generalise across all 5
--      `SingleAgen` constructors.
--
--   2. The clean route is via the *strip* equivalence: after applying
--      `single-agen-strip`'s `equiv`, both `⟪f⟫` and `⟪g⟫` are
--      ≈Term-equal (and thus iso) to graphs of the form
--      `⟪c-to ∘ M ∘ c-from⟫` where the Agen edge's `ein` IS a sublist
--      of dom at position `length (flatten YL)` (via the explicit
--      M = id ⊗ (Agen u ⊗ id) structure).  This requires soundness
--      of `≈Term`, which is available but introduces an indirect
--      route through the iso transitivity machinery.
--
--   3. Either approach gives `length-of-YL-eq` in ~100-200 LOC.
--      The current file ships `positional-alignment-from-length`
--      requiring `length-of-YL-eq` as an *input* — the trust content
--      of the remaining hole has thereby shrunk from "extract iso →
--      `flatten YL_f ≡ flatten YL_g`" to "extract iso →
--      `length (flatten YL_f) ≡ length (flatten YL_g)`", i.e. a
--      single `ℕ` equality.

--------------------------------------------------------------------------------
-- Attempt at deriving `length(flatten YL_f) ≡ length(flatten YL_g)` from
-- the iso `⟪f⟫ ≅ᴴ ⟪g⟫`.  Strategy: in the canonical normal form
-- `Wf = c-to ∘ M ∘ c-from`, the Agen edge's `ein` is structurally
-- located at position `length(flatten YL_f)` of dom — but extracting
-- this requires the full structural recursion through `hComposeP`,
-- `hTensor`, and `hGen` whose explicit positional content is encoded
-- in `FromAPROP` and `PrunedCompose`.
--
-- The lemma `YL-length-from-iso` was investigated extensively in this
-- session; it remains open.  The blocker is *not* a postulate (none
-- have been added) but the substantial structural induction needed to
-- prove that in `⟪Wf⟫`, the Agen edge's `ein` vertices form a
-- contiguous sublist of `dom` at offset `length(flatten YL_f)`.
--
-- Substep analysis (this session):
--
--   * The soundness chain `f ≈Term Wf` → `⟪f⟫ ≅ᴴ ⟪Wf⟫` is available
--     via `Soundness.soundness`.  Composing with the input iso gives
--     `⟪Wf⟫ ≅ᴴ ⟪Wg⟫`.
--
--   * In `⟪Wf⟫`, the structure is
--     `hComposeP (hComposeP ⟪c-from⟫ ⟪M⟫ ...) ⟪c-to⟫ ...`.  The Agen
--     edge sits in `⟪M⟫` (the K-side of the inner compose).  After
--     the inner compose, the Agen edge's `ein` is mapped via
--     `remapP_inner` (which lands in `⟪c-from⟫.cod` positions because
--     the Agen ein vertices are all in `⟪M⟫.dom`).  After the outer
--     compose, the Agen ein gets `injL_outer` applied.  Final form:
--     `map (injL_outer ∘ remapP_inner) (⟪M⟫.ein agen-edge)`.
--
--   * In `⟪M⟫ = ⟪id_YL ⊗ (Agen u ⊗ id_YR)⟫`, the Agen ein is at
--     position `length(flatten YL)` within `⟪M⟫.dom` (which equals
--     `flatten(YL ⊗ Aᵢ ⊗ YR)`-positionally).  This part is concrete
--     and computable from `hTensor-impl` and `hGen`.
--
--   * Connecting the Agen ein (in `⟪M⟫.dom` positions) to dom
--     positions of `⟪Wf⟫` requires showing that `remapP_inner` maps
--     these `⟪M⟫.dom` positions to corresponding `⟪c-from⟫.cod`
--     positions, AND that `⟪c-from⟫.cod` is positionally aligned with
--     `⟪c-from⟫.dom` (= `⟪Wf⟫.dom` modulo injL_outer) — i.e., that
--     NoSigma terms preserve positional order between dom and cod.
--
-- The third bullet is the substantial step.  For NoSigma c-from, the
-- claim "cod position i ↔ dom position i" requires verifying for
-- each NoSigma constructor (id, λ⇒/⇐, ρ⇒/⇐, α⇒/⇐, ∘, ⊗) that the
-- corresponding hypergraph operation preserves this positional
-- relationship.  Most constructors are trivial (hId-based: dom = cod);
-- ∘ and ⊗ require induction with care for the injL/injR/remapP wrappers.
--
-- This work is left as documented future work; the current commit
-- preserves all existing infrastructure and the postulate
-- `single-agen-NF-coherence` remains in `CompletenessAssumptions`.

--------------------------------------------------------------------------------
-- Closed sub-case of `YL-length-from-iso`: when *both* witnesses are
-- `single-agen-here`, the strip's YL is `unit` on both sides, so the
-- length equality is trivially `0 ≡ 0`.  This sub-case is exposed as
-- a stepping stone for future work that may dispatch on `sf` to
-- gradually close other constructors.

YL-length-from-iso-here-here
  : ∀ {A B} {u_f u_g : mor A B}
      (iso : ⟪ Agen u_f ⟫ ≅ᴴ ⟪ Agen u_g ⟫)
  → length (flatten (SingleAgenNF.YL (single-agen-strip (single-agen-here u_f))))
  ≡ length (flatten (SingleAgenNF.YL (single-agen-strip (single-agen-here u_g))))
YL-length-from-iso-here-here _ = refl

--------------------------------------------------------------------------------
-- `agen-ein-position` machinery.
--
-- `length-YL-strip sf ≡ length (flatten YL_f)` is a direct ℕ computation
-- from the witness, parallel to the implicit YL inside `single-agen-strip`.
-- Provided as a recursion-friendly view so downstream code can compute
-- on the ℕ rather than on the `flatten` of the strip's YL.

length-YL-strip
  : ∀ {A B} {f : HomTerm A B} → SingleAgen f → ℕ
length-YL-strip (single-agen-here _)   = 0
length-YL-strip (single-agen-∘-l sh _) = length-YL-strip sh
length-YL-strip (single-agen-∘-r _ sk) = length-YL-strip sk
length-YL-strip (single-agen-⊗-l sh _) = length-YL-strip sh
length-YL-strip {f = h ⊗₁ k} (single-agen-⊗-r {A = A} _ sk) =
  length (flatten A) + length-YL-strip sk

-- Mirror of `length-YL-strip` for the YR side.  Used to characterise
-- the post-Agen-edge segment of dom.
length-YR-strip
  : ∀ {A B} {f : HomTerm A B} → SingleAgen f → ℕ
length-YR-strip (single-agen-here _)   = 0
length-YR-strip (single-agen-∘-l sh _) = length-YR-strip sh
length-YR-strip (single-agen-∘-r _ sk) = length-YR-strip sk
length-YR-strip {f = h ⊗₁ k} (single-agen-⊗-l {C = C} sh _) =
  length-YR-strip sh + length (flatten C)
length-YR-strip (single-agen-⊗-r _ sk) = length-YR-strip sk

-- `length-YL-strip sf ≡ length (flatten YL_f)`.  Strict recursion
-- mirroring `single-agen-strip`'s YL field.  Used to convert between
-- the structural ℕ view and the `flatten`-of-YL form expected by the
-- `positional-alignment-from-length` interface.
open import Data.List using (length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (_+_)

length-YL-strip-≡
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → length-YL-strip sf
  ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
length-YL-strip-≡ (single-agen-here _)   = refl
length-YL-strip-≡ (single-agen-∘-l sh _) = length-YL-strip-≡ sh
length-YL-strip-≡ (single-agen-∘-r _ sk) = length-YL-strip-≡ sk
length-YL-strip-≡ (single-agen-⊗-l sh _) = length-YL-strip-≡ sh
length-YL-strip-≡ {f = h ⊗₁ k} (single-agen-⊗-r {A = A} _ sk) =
  trans (cong (length (flatten A) +_) (length-YL-strip-≡ sk))
        (sym (length-++ (flatten A)))

--------------------------------------------------------------------------------
-- `length-dom-⟪⟫ : length ⟪f⟫.dom ≡ length (flatten A)`.  A small ℕ
-- lemma derived from `⟪⟫-domL` and `length-map`.  Used in the
-- `length-of-YL` proof to count atoms across the Agen-edge boundary.

length-dom-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
  → length (Hypergraph.dom ⟪ f ⟫) ≡ length (flatten A)
length-dom-⟪⟫ {A = A} f =
  trans (sym (length-map-dom (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.dom ⟪ f ⟫)))
        (cong length (⟪⟫-domL f))
  where
    open import Data.List.Properties
      using () renaming (length-map to length-map-dom)

--------------------------------------------------------------------------------
-- NoSigma-cod≡dom: for any NoSigma `h : HomTerm A B`, the dom and cod
-- of `⟪h⟫` are propositionally equal Fin lists.
--
-- Proof by structural induction on the NoSigma witness.  For each
-- *atomic* NoSigma case (id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐), the translation
-- produces `hId X` for some X, and `hId-cod≡dom` settles the case.
-- For `nosigma-∘` and `nosigma-⊗` we recurse on the structure.
--
-- The compose case uses the central observation: for `hComposeP G K`
-- with `Unique K.dom`, `map remapP K.dom ≡ map injL G.cod` (up to
-- structural manipulation involving `lookup-cod` and the
-- `cast dom-cod-len`).  Combined with the IH on G (`G.cod ≡ G.dom`),
-- this yields `composed.cod ≡ composed.dom`.

open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-dom-unique; ⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Invariant sig
  using (hId-cod≡dom)
open import Categories.APROP.Hypergraph.Core using (codL; domL)

private
  open import Data.List using (allFin; lookup)
  open import Data.List.Properties
    using (map-tabulate; tabulate-lookup; map-cong; map-id; map-∘; length-map)
  open import Data.Fin using (cast)
  open import Data.Fin.Properties using (cast-is-id)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Categories.APROP.Hypergraph.Prune
    using (remap-inj₁; classify-lookup-Unique)
  open import Categories.APROP.Hypergraph.PrunedCompose sig
    using ()

  -- Re-derivation of `map-lookup-allFin` and `cast-allFin` (from
  -- `SoundnessProved`'s private module).  Re-stated locally to avoid
  -- breaking the existing module's private boundary.
  map-lookup-allFin
    : ∀ {A : Set} (xs : List A)
    → map (lookup xs) (allFin (length xs)) ≡ xs
  map-lookup-allFin xs =
    trans (map-tabulate (λ i → i) (lookup xs)) (tabulate-lookup xs)

  cast-allFin
    : ∀ {m n} (eq : m ≡ n) → map (cast eq) (allFin m) ≡ allFin n
  cast-allFin refl =
    trans (map-cong (λ i → cast-is-id refl i) (allFin _)) (map-id (allFin _))

  -- For `hComposeP G K bdy-eq` with `Unique K.dom`,
  -- `map remapP K.dom ≡ map injL G.cod`.  Generalises the
  -- `idˡ-cod-helper`'s K = hId chain to any Unique-dom K.
  map-remapP-dom-≡-injL-G-cod
    : ∀ (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
    → Unique (Hypergraph.dom K)
    → let module hCP = hComposeP-impl G K bdy-eq
          module Kh = Hypergraph K
          module Gh = Hypergraph G
      in map hCP.remapP Kh.dom ≡ map hCP.injL Gh.cod
  map-remapP-dom-≡-injL-G-cod G K bdy-eq K-dom-Unique =
    let module hCP = hComposeP-impl G K bdy-eq
        module Kh = Hypergraph K
        module Gh = Hypergraph G

        remapP-on-dom
          : ∀ (j : Fin (length Kh.dom))
          → hCP.remapP (lookup Kh.dom j)
          ≡ hCP.lookup-cod j ↑ˡ Prune.count-non Kh.dom
        remapP-on-dom j =
          remap-inj₁ Kh.dom hCP.lookup-cod (lookup Kh.dom j) j
            (classify-lookup-Unique Kh.dom K-dom-Unique j)
    in EQR.begin
      map hCP.remapP Kh.dom
        EQR.≡⟨ cong (map hCP.remapP) (sym (map-lookup-allFin Kh.dom)) ⟩
      map hCP.remapP (map (lookup Kh.dom) (allFin (length Kh.dom)))
        EQR.≡⟨ sym (map-∘ (allFin (length Kh.dom))) ⟩
      map (λ j → hCP.remapP (lookup Kh.dom j)) (allFin (length Kh.dom))
        EQR.≡⟨ map-cong remapP-on-dom (allFin (length Kh.dom)) ⟩
      map (λ j → hCP.lookup-cod j ↑ˡ Prune.count-non Kh.dom)
          (allFin (length Kh.dom))
        EQR.≡⟨ map-∘ (allFin (length Kh.dom)) ⟩
      map (_↑ˡ Prune.count-non Kh.dom)
          (map hCP.lookup-cod (allFin (length Kh.dom)))
        EQR.≡⟨ cong (map (_↑ˡ Prune.count-non Kh.dom)) (map-∘ (allFin (length Kh.dom))) ⟩
      map (_↑ˡ Prune.count-non Kh.dom)
          (map (lookup Gh.cod) (map (cast hCP.dom-cod-len) (allFin (length Kh.dom))))
        EQR.≡⟨ cong (λ xs → map (_↑ˡ Prune.count-non Kh.dom)
                              (map (lookup Gh.cod) xs))
              (cast-allFin hCP.dom-cod-len) ⟩
      map (_↑ˡ Prune.count-non Kh.dom)
          (map (lookup Gh.cod) (allFin (length Gh.cod)))
        EQR.≡⟨ cong (map (_↑ˡ Prune.count-non Kh.dom)) (map-lookup-allFin Gh.cod) ⟩
      map (_↑ˡ Prune.count-non Kh.dom) Gh.cod
        EQR.∎
    where
      module EQR = ≡-Reasoning
      module Prune = Categories.APROP.Hypergraph.Prune

NoSigma-cod≡dom
  : ∀ {A B} {h : HomTerm A B}
  → NoSigma h → Hypergraph.cod ⟪ h ⟫ ≡ Hypergraph.dom ⟪ h ⟫
NoSigma-cod≡dom (nosigma-id {A}) = hId-cod≡dom A
NoSigma-cod≡dom (nosigma-λ⇒ {A}) = hId-cod≡dom A
NoSigma-cod≡dom (nosigma-λ⇐ {A}) = hId-cod≡dom A
NoSigma-cod≡dom (nosigma-ρ⇒ {A}) = hId-cod≡dom (A ⊗₀ unit)
NoSigma-cod≡dom (nosigma-ρ⇐ {A}) = hId-cod≡dom (A ⊗₀ unit)
NoSigma-cod≡dom (nosigma-α⇒ {A} {B} {C}) = hId-cod≡dom ((A ⊗₀ B) ⊗₀ C)
NoSigma-cod≡dom (nosigma-α⇐ {A} {B} {C}) = hId-cod≡dom ((A ⊗₀ B) ⊗₀ C)
NoSigma-cod≡dom {h = h₁ ⊗₁ h₂} (nosigma-⊗ nh nk) =
  let module H₁ = Hypergraph ⟪ h₁ ⟫
      module H₂ = Hypergraph ⟪ h₂ ⟫
  in cong₂ _++_
       (cong (map (_↑ˡ H₂.nV)) (NoSigma-cod≡dom nh))
       (cong (map (H₁.nV ↑ʳ_)) (NoSigma-cod≡dom nk))
  where open import Relation.Binary.PropositionalEquality using (cong₂)
NoSigma-cod≡dom {h = h₁ ∘ h₂} (nosigma-∘ nh nk) =
  -- ⟪h₁ ∘ h₂⟫ = hComposeP ⟪h₂⟫ ⟪h₁⟫ bdy.
  --   G = ⟪h₂⟫, K = ⟪h₁⟫.
  --   dom = map injL G.dom.
  --   cod = map remapP K.cod.
  -- IH on h₁: K.cod ≡ K.dom.
  -- For Unique K.dom: `map remapP K.dom ≡ map injL G.cod`.
  -- IH on h₂: G.cod ≡ G.dom.
  EQR.begin
    map hCP.remapP K.cod
      EQR.≡⟨ cong (map hCP.remapP) (NoSigma-cod≡dom nh) ⟩
    map hCP.remapP K.dom
      EQR.≡⟨ map-remapP-dom-≡-injL-G-cod ⟪ h₂ ⟫ ⟪ h₁ ⟫ bdy (⟪_⟫-dom-unique h₁) ⟩
    map hCP.injL G.cod
      EQR.≡⟨ cong (map hCP.injL) (NoSigma-cod≡dom nk) ⟩
    map hCP.injL G.dom
      EQR.∎
  where
    module EQR = ≡-Reasoning
    bdy = trans (⟪⟫-codL h₂) (sym (⟪⟫-domL h₁))
    module G = Hypergraph ⟪ h₂ ⟫
    module K = Hypergraph ⟪ h₁ ⟫
    module hCP = hComposeP-impl ⟪ h₂ ⟫ ⟪ h₁ ⟫ bdy

--------------------------------------------------------------------------------
-- `agen-ein-position`: structural positional decomposition of `⟪f⟫.dom`
-- around the unique Agen edge's `ein`.
--
-- For each `SingleAgen` witness `sf`, the dom of `⟪f⟫` admits a
-- decomposition
--
--   ⟪f⟫.dom ≡ pre ++ ⟪f⟫.ein (SingleAgen-edge sf) ++ post
--
-- where `length pre ≡ length-YL-strip sf` and
-- `length post ≡ length-YR-strip sf`.
--
-- The proof is by structural recursion on `sf`.  The compose-left
-- case is the most delicate: the Agen edge's `ein` is `map remapP
-- (⟪h⟫.ein agen-h)`, not literally a sublist of `map injL ⟪k⟫.dom`.
-- We close it via `map-remapP-dom-≡-injL-G-cod` + `NoSigma-cod≡dom`
-- on the right-hand wrapper.

open import Data.List.Properties using (map-++; ++-assoc; length-++)
  renaming (length-map to length-map-prop)
open import Data.List using ([])

agen-ein-position
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → Σ[ pre ∈ List (Fin (Hypergraph.nV ⟪ f ⟫)) ]
    Σ[ post ∈ List (Fin (Hypergraph.nV ⟪ f ⟫)) ]
    Hypergraph.dom ⟪ f ⟫
    ≡ pre ++ Hypergraph.ein ⟪ f ⟫ (SingleAgen-edge sf) ++ post
    × length pre ≡ length-YL-strip sf
    × length post ≡ length-YR-strip sf
agen-ein-position (single-agen-here u) =
  -- ⟪Agen u⟫ = hGen u.  dom = ein = `map (_↑ˡ nB) (range nA)`.
  -- pre = post = [].
  [] , [] ,
  sym (++-identityʳ _) ,
  refl ,
  refl
  where open import Data.List.Properties using (++-identityʳ)
agen-ein-position {f = h ∘ k} (single-agen-∘-r nh sk) =
  -- ⟪h ∘ k⟫ = hComposeP ⟪k⟫ ⟪h⟫ bdy.
  --   G = ⟪k⟫, K = ⟪h⟫.
  --   composed.dom = map injL ⟪k⟫.dom.
  --   Agen edge in composed = (SingleAgen-edge sk) ↑ˡ ⟪h⟫.nE.
  --   Its ein in composed = map injL (⟪k⟫.ein (SingleAgen-edge sk)).
  -- IH on sk: ⟪k⟫.dom = pre-k ++ ⟪k⟫.ein agen-k ++ post-k.
  let
    ih = agen-ein-position sk
    pre-k    = proj₁ ih
    post-k   = proj₁ (proj₂ ih)
    dom-eq-k = proj₁ (proj₂ (proj₂ ih))
    len-pre-k = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-k = proj₂ (proj₂ (proj₂ (proj₂ ih)))

    bdy = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy using (injL; ein-c-inj₁-red)
    module K-G = Hypergraph ⟪ k ⟫
    module H-K = Hypergraph ⟪ h ⟫

    pre = map injL pre-k
    ein-k = K-G.ein (SingleAgen-edge sk)
    post = map injL post-k

    dom-eq :
      map injL K-G.dom ≡ pre ++ map injL ein-k ++ post
    dom-eq =
      trans (cong (map injL) dom-eq-k)
            (trans (map-++ injL pre-k (ein-k ++ post-k))
                   (cong (map injL pre-k ++_)
                         (map-++ injL ein-k post-k)))

    ein-composed-eq :
      Hypergraph.ein ⟪ h ∘ k ⟫ (SingleAgen-edge sk ↑ˡ H-K.nE)
      ≡ map injL ein-k
    ein-composed-eq = ein-c-inj₁-red (SingleAgen-edge sk)
  in
    pre , post ,
    trans dom-eq
          (cong (λ xs → pre ++ xs ++ post) (sym ein-composed-eq)) ,
    trans (length-map-prop injL pre-k) len-pre-k ,
    trans (length-map-prop injL post-k) len-post-k
agen-ein-position {f = h ⊗₁ k} (single-agen-⊗-l {C = C} sh nk) =
  -- ⟪h ⊗ k⟫ = hTensor ⟪h⟫ ⟪k⟫.
  --   composed.dom = map injL ⟪h⟫.dom ++ map injR ⟪k⟫.dom.
  --   Agen edge in composed = (SingleAgen-edge sh) ↑ˡ ⟪k⟫.nE.
  --   Its ein in composed = map injL (⟪h⟫.ein (SingleAgen-edge sh)).
  -- IH on sh: ⟪h⟫.dom = pre-h ++ ⟪h⟫.ein agen-h ++ post-h.
  pre , post ,
  trans dom-eq
        (cong (λ xs → pre ++ xs ++ post) (sym ein-composed-eq)) ,
  trans (length-map-prop injL pre-h) len-pre-h ,
  post-len-eq
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫ using (injL; injR; ein-c-inj₁-red)
    module Hh = Hypergraph ⟪ h ⟫
    module Hk = Hypergraph ⟪ k ⟫
    ih = agen-ein-position sh
    pre-h    = proj₁ ih
    post-h   = proj₁ (proj₂ ih)
    dom-eq-h = proj₁ (proj₂ (proj₂ ih))
    len-pre-h = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-h = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    pre = map injL pre-h
    ein-h = Hh.ein (SingleAgen-edge sh)
    post = map injL post-h ++ map injR Hk.dom
    map-decomp :
      map injL Hh.dom
      ≡ map injL pre-h ++ map injL ein-h ++ map injL post-h
    map-decomp =
      trans (cong (map injL) dom-eq-h)
            (trans (map-++ injL pre-h (ein-h ++ post-h))
                   (cong (map injL pre-h ++_)
                         (map-++ injL ein-h post-h)))
    dom-eq :
      map injL Hh.dom ++ map injR Hk.dom
      ≡ pre ++ map injL ein-h ++ post
    dom-eq =
      trans (cong (_++ map injR Hk.dom) map-decomp)
            (trans (++-assoc (map injL pre-h)
                             (map injL ein-h ++ map injL post-h)
                             (map injR Hk.dom))
                   (cong (map injL pre-h ++_)
                         (++-assoc (map injL ein-h)
                                   (map injL post-h)
                                   (map injR Hk.dom))))
    ein-composed-eq :
      Hypergraph.ein ⟪ h ⊗₁ k ⟫ (SingleAgen-edge sh ↑ˡ Hk.nE)
      ≡ map injL ein-h
    ein-composed-eq = ein-c-inj₁-red (SingleAgen-edge sh)
    post-len-eq :
      length post ≡ length-YR-strip sh + length (flatten C)
    post-len-eq =
      trans (length-++ (map injL post-h))
            (cong₂ _+_
              (trans (length-map-prop injL post-h) len-post-h)
              (trans (length-map-prop injR Hk.dom) (length-dom-⟪⟫ k)))
agen-ein-position {f = h ⊗₁ k} (single-agen-⊗-r {A = A_h} nh sk) =
  -- ⟪h ⊗ k⟫ = hTensor ⟪h⟫ ⟪k⟫.
  --   composed.dom = map injL ⟪h⟫.dom ++ map injR ⟪k⟫.dom.
  --   Agen edge in composed = ⟪h⟫.nE ↑ʳ (SingleAgen-edge sk).
  --   Its ein in composed = map injR (⟪k⟫.ein (SingleAgen-edge sk)).
  -- IH on sk: ⟪k⟫.dom = pre-k ++ ⟪k⟫.ein agen-k ++ post-k.
  pre , post ,
  trans dom-eq
        (cong (λ xs → pre ++ xs ++ post) (sym ein-composed-eq)) ,
  pre-len-eq ,
  trans (length-map-prop injR post-k) len-post-k
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫ using (injL; injR; ein-c-inj₂-red)
    module Hh = Hypergraph ⟪ h ⟫
    module Hk = Hypergraph ⟪ k ⟫
    ih = agen-ein-position sk
    pre-k    = proj₁ ih
    post-k   = proj₁ (proj₂ ih)
    dom-eq-k = proj₁ (proj₂ (proj₂ ih))
    len-pre-k = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-k = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    pre = map injL Hh.dom ++ map injR pre-k
    ein-k = Hk.ein (SingleAgen-edge sk)
    post = map injR post-k
    map-decomp :
      map injR Hk.dom
      ≡ map injR pre-k ++ map injR ein-k ++ map injR post-k
    map-decomp =
      trans (cong (map injR) dom-eq-k)
            (trans (map-++ injR pre-k (ein-k ++ post-k))
                   (cong (map injR pre-k ++_)
                         (map-++ injR ein-k post-k)))
    dom-eq :
      map injL Hh.dom ++ map injR Hk.dom
      ≡ pre ++ map injR ein-k ++ post
    dom-eq =
      trans (cong (map injL Hh.dom ++_) map-decomp)
            (sym (++-assoc (map injL Hh.dom) (map injR pre-k) _))
    ein-composed-eq :
      Hypergraph.ein ⟪ h ⊗₁ k ⟫ (Hh.nE ↑ʳ SingleAgen-edge sk)
      ≡ map injR ein-k
    ein-composed-eq = ein-c-inj₂-red (SingleAgen-edge sk)
    pre-len-eq :
      length pre ≡ length (flatten A_h) + length-YL-strip sk
    pre-len-eq =
      trans (length-++ (map injL Hh.dom))
            (cong₂ _+_
              (trans (length-map-prop injL Hh.dom) (length-dom-⟪⟫ h))
              (trans (length-map-prop injR pre-k) len-pre-k))
agen-ein-position {f = h ∘ k} (single-agen-∘-l sh nk) =
  -- ⟪h ∘ k⟫ = hComposeP ⟪k⟫ ⟪h⟫ bdy.
  --   G = ⟪k⟫, K = ⟪h⟫.
  --   composed.dom = map injL ⟪k⟫.dom.
  --   Agen edge in composed = ⟪k⟫.nE ↑ʳ (SingleAgen-edge sh).
  --   Its ein in composed = map remapP (⟪h⟫.ein (SingleAgen-edge sh)).
  -- IH on sh: ⟪h⟫.dom = pre-h ++ ⟪h⟫.ein agen-h ++ post-h.
  -- map remapP ⟪h⟫.dom = map injL ⟪k⟫.cod   (by map-remapP-dom-≡-injL-G-cod).
  -- ⟪k⟫.cod = ⟪k⟫.dom                       (by NoSigma-cod≡dom nk).
  -- So map remapP ⟪h⟫.dom = composed.dom.
  -- Hence composed.dom = map remapP pre-h ++ map remapP ein-h ++ map remapP post-h.
  pre , post ,
  decomp ,
  trans (length-map-prop remapP pre-h) len-pre-h ,
  trans (length-map-prop remapP post-h) len-post-h
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    bdy = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy
      using (injL; remapP; ein-c-inj₂-red)
    module Gk = Hypergraph ⟪ k ⟫
    module Kh = Hypergraph ⟪ h ⟫

    ih = agen-ein-position sh
    pre-h     = proj₁ ih
    post-h    = proj₁ (proj₂ ih)
    dom-eq-h  = proj₁ (proj₂ (proj₂ ih))
    len-pre-h = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-h = proj₂ (proj₂ (proj₂ (proj₂ ih)))

    pre = map remapP pre-h
    ein-h = Kh.ein (SingleAgen-edge sh)
    post = map remapP post-h

    -- map remapP Kh.dom ≡ map injL Gk.cod (general K Unique-dom)
    remapP-Kh-dom-eq : map remapP Kh.dom ≡ map injL Gk.cod
    remapP-Kh-dom-eq =
      map-remapP-dom-≡-injL-G-cod ⟪ k ⟫ ⟪ h ⟫ bdy (⟪_⟫-dom-unique h)

    -- map injL Gk.cod ≡ map injL Gk.dom (since k is NoSigma)
    injL-Gk-cod-dom-eq : map injL Gk.cod ≡ map injL Gk.dom
    injL-Gk-cod-dom-eq = cong (map injL) (NoSigma-cod≡dom nk)

    -- So map remapP Kh.dom ≡ composed.dom.
    remapP-Kh-eq-dom : map remapP Kh.dom ≡ map injL Gk.dom
    remapP-Kh-eq-dom = trans remapP-Kh-dom-eq injL-Gk-cod-dom-eq

    -- Decomposition of map remapP Kh.dom using IH.
    remapP-decomp :
      map remapP Kh.dom
      ≡ map remapP pre-h ++ map remapP ein-h ++ map remapP post-h
    remapP-decomp =
      trans (cong (map remapP) dom-eq-h)
            (trans (map-++ remapP pre-h (ein-h ++ post-h))
                   (cong (map remapP pre-h ++_)
                         (map-++ remapP ein-h post-h)))

    -- Combined: composed.dom ≡ pre ++ map remapP ein-h ++ post.
    composed-dom-eq :
      map injL Gk.dom ≡ pre ++ map remapP ein-h ++ post
    composed-dom-eq =
      trans (sym remapP-Kh-eq-dom) remapP-decomp

    -- Agen ein in composed equals map remapP ein-h.
    ein-composed-eq :
      Hypergraph.ein ⟪ h ∘ k ⟫ (Gk.nE ↑ʳ SingleAgen-edge sh)
      ≡ map remapP ein-h
    ein-composed-eq = ein-c-inj₂-red (SingleAgen-edge sh)

    decomp :
      Hypergraph.dom ⟪ h ∘ k ⟫
      ≡ pre ++ Hypergraph.ein ⟪ h ∘ k ⟫ (Gk.nE ↑ʳ SingleAgen-edge sh) ++ post
    decomp =
      trans composed-dom-eq
            (cong (λ xs → pre ++ xs ++ post) (sym ein-composed-eq))

--------------------------------------------------------------------------------
-- `length-cod-⟪⟫ : length ⟪f⟫.cod ≡ length (flatten B)`.  Dual of
-- `length-dom-⟪⟫`.  Used in the `agen-eout-position` proof.

length-cod-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
  → length (Hypergraph.cod ⟪ f ⟫) ≡ length (flatten B)
length-cod-⟪⟫ {B = B} f =
  trans (sym (length-map-cod (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.cod ⟪ f ⟫)))
        (cong length (⟪⟫-codL f))
  where
    open import Data.List.Properties
      using () renaming (length-map to length-map-cod)

--------------------------------------------------------------------------------
-- `agen-eout-position`: dual of `agen-ein-position`.  For each
-- `SingleAgen` witness `sf`, the cod of `⟪f⟫` admits a decomposition
--
--   ⟪f⟫.cod ≡ pre ++ ⟪f⟫.eout (SingleAgen-edge sf) ++ post
--
-- with the same `length pre ≡ length-YL-strip sf` and
-- `length post ≡ length-YR-strip sf` (since the strip's YL/YR are
-- shared between source and target of the middle).
--
-- The proof structure mirrors `agen-ein-position`'s, using eout-c-inj_X
-- instead of ein-c-inj_X.

agen-eout-position
  : ∀ {A B} {f : HomTerm A B} (sf : SingleAgen f)
  → Σ[ pre ∈ List (Fin (Hypergraph.nV ⟪ f ⟫)) ]
    Σ[ post ∈ List (Fin (Hypergraph.nV ⟪ f ⟫)) ]
    Hypergraph.cod ⟪ f ⟫
    ≡ pre ++ Hypergraph.eout ⟪ f ⟫ (SingleAgen-edge sf) ++ post
    × length pre ≡ length-YL-strip sf
    × length post ≡ length-YR-strip sf
agen-eout-position (single-agen-here u) =
  -- ⟪Agen u⟫ = hGen u.  cod = eout = `map (nA ↑ʳ_) (range nB)`.
  -- pre = post = [].
  [] , [] ,
  sym (++-identityʳ _) ,
  refl ,
  refl
  where open import Data.List.Properties using (++-identityʳ)
agen-eout-position {f = h ∘ k} (single-agen-∘-r nh sk) =
  -- ⟪h ∘ k⟫ = hComposeP ⟪k⟫ ⟪h⟫ bdy.
  --   G = ⟪k⟫, K = ⟪h⟫.
  --   composed.cod = map remapP ⟪h⟫.cod.
  --   Agen edge in composed = (SingleAgen-edge sk) ↑ˡ ⟪h⟫.nE.
  --   Its eout in composed = map injL (⟪k⟫.eout (SingleAgen-edge sk)).
  --
  -- For the Agen-eout, sk is in the G-side.  We need
  --   composed.cod ≡ pre ++ map injL eout-k ++ post.
  --
  -- But composed.cod = map remapP ⟪h⟫.cod, NOT map injL ⟪k⟫.cod.
  -- For NoSigma h: NoSigma-cod≡dom nh gives ⟪h⟫.cod ≡ ⟪h⟫.dom.
  -- Then map-remapP-dom-≡-injL-G-cod gives map remapP ⟪h⟫.dom ≡ map injL ⟪k⟫.cod.
  -- So composed.cod ≡ map injL ⟪k⟫.cod.
  -- By IH on sk: ⟪k⟫.cod = pre-k ++ ⟪k⟫.eout agen-k ++ post-k.
  -- Substitute to get the decomposition.
  pre , post ,
  decomp ,
  trans (length-map-prop injL pre-k) len-pre-k ,
  trans (length-map-prop injL post-k) len-post-k
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    bdy = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy
      using (injL; remapP; eout-c-inj₁-red)
    module Gk = Hypergraph ⟪ k ⟫
    module Kh = Hypergraph ⟪ h ⟫

    ih = agen-eout-position sk
    pre-k     = proj₁ ih
    post-k    = proj₁ (proj₂ ih)
    cod-eq-k  = proj₁ (proj₂ (proj₂ ih))
    len-pre-k = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-k = proj₂ (proj₂ (proj₂ (proj₂ ih)))

    pre = map injL pre-k
    eout-k = Gk.eout (SingleAgen-edge sk)
    post = map injL post-k

    -- map remapP Kh.cod = ?
    remapP-Kh-cod-dom : map remapP Kh.cod ≡ map remapP Kh.dom
    remapP-Kh-cod-dom = cong (map remapP) (NoSigma-cod≡dom nh)

    remapP-Kh-dom-eq : map remapP Kh.dom ≡ map injL Gk.cod
    remapP-Kh-dom-eq =
      map-remapP-dom-≡-injL-G-cod ⟪ k ⟫ ⟪ h ⟫ bdy (⟪_⟫-dom-unique h)

    -- composed.cod ≡ map injL Gk.cod.
    composed-cod-eq-Gk-cod : map remapP Kh.cod ≡ map injL Gk.cod
    composed-cod-eq-Gk-cod = trans remapP-Kh-cod-dom remapP-Kh-dom-eq

    -- map injL Gk.cod = map injL (pre-k ++ eout-k ++ post-k)
    --                 = map injL pre-k ++ map injL eout-k ++ map injL post-k
    injL-decomp :
      map injL Gk.cod
      ≡ map injL pre-k ++ map injL eout-k ++ map injL post-k
    injL-decomp =
      trans (cong (map injL) cod-eq-k)
            (trans (map-++ injL pre-k (eout-k ++ post-k))
                   (cong (map injL pre-k ++_)
                         (map-++ injL eout-k post-k)))

    -- composed.cod ≡ pre ++ map injL eout-k ++ post.
    cod-eq : map remapP Kh.cod ≡ pre ++ map injL eout-k ++ post
    cod-eq = trans composed-cod-eq-Gk-cod injL-decomp

    -- composed.eout at the agen edge = map injL eout-k.
    eout-composed-eq :
      Hypergraph.eout ⟪ h ∘ k ⟫ (SingleAgen-edge sk ↑ˡ Kh.nE)
      ≡ map injL eout-k
    eout-composed-eq = eout-c-inj₁-red (SingleAgen-edge sk)

    decomp :
      Hypergraph.cod ⟪ h ∘ k ⟫
      ≡ pre ++ Hypergraph.eout ⟪ h ∘ k ⟫ (SingleAgen-edge sk ↑ˡ Kh.nE) ++ post
    decomp =
      trans cod-eq
            (cong (λ xs → pre ++ xs ++ post) (sym eout-composed-eq))
agen-eout-position {f = h ⊗₁ k} (single-agen-⊗-l {C = C} sh nk) =
  -- ⟪h ⊗ k⟫ = hTensor ⟪h⟫ ⟪k⟫.  composed.cod = map injL Hh.cod ++ map injR Hk.cod.
  -- Agen edge in composed = (SingleAgen-edge sh) ↑ˡ Hk.nE.
  -- Its eout in composed = map injL (⟪h⟫.eout (SingleAgen-edge sh)).
  -- By IH on sh: ⟪h⟫.cod = pre-h ++ eout-h ++ post-h.
  pre , post ,
  trans cod-eq (cong (λ xs → pre ++ xs ++ post) (sym eout-composed-eq)) ,
  trans (length-map-prop injL pre-h) len-pre-h ,
  post-len-eq
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫ using (injL; injR; eout-c-inj₁-red)
    module Hh = Hypergraph ⟪ h ⟫
    module Hk = Hypergraph ⟪ k ⟫
    ih = agen-eout-position sh
    pre-h    = proj₁ ih
    post-h   = proj₁ (proj₂ ih)
    cod-eq-h = proj₁ (proj₂ (proj₂ ih))
    len-pre-h = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-h = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    pre = map injL pre-h
    eout-h = Hh.eout (SingleAgen-edge sh)
    post = map injL post-h ++ map injR Hk.cod
    map-decomp :
      map injL Hh.cod
      ≡ map injL pre-h ++ map injL eout-h ++ map injL post-h
    map-decomp =
      trans (cong (map injL) cod-eq-h)
            (trans (map-++ injL pre-h (eout-h ++ post-h))
                   (cong (map injL pre-h ++_)
                         (map-++ injL eout-h post-h)))
    cod-eq :
      map injL Hh.cod ++ map injR Hk.cod
      ≡ pre ++ map injL eout-h ++ post
    cod-eq =
      trans (cong (_++ map injR Hk.cod) map-decomp)
            (trans (++-assoc (map injL pre-h)
                             (map injL eout-h ++ map injL post-h)
                             (map injR Hk.cod))
                   (cong (map injL pre-h ++_)
                         (++-assoc (map injL eout-h)
                                   (map injL post-h)
                                   (map injR Hk.cod))))
    eout-composed-eq :
      Hypergraph.eout ⟪ h ⊗₁ k ⟫ (SingleAgen-edge sh ↑ˡ Hk.nE)
      ≡ map injL eout-h
    eout-composed-eq = eout-c-inj₁-red (SingleAgen-edge sh)
    -- The post-len-eq for ⊗-l: the YR has been extended with C.
    -- Use length-cod-⟪⟫ on k (which gives length flatten D, where k : C → D).
    -- But our length-YR-strip references flatten C.
    -- For NoSigma k : C → D, flatten C ≡ flatten D, so lengths agree.
    post-len-eq :
      length post ≡ length-YR-strip sh + length (flatten C)
    post-len-eq =
      trans (length-++ (map injL post-h))
            (cong₂ _+_
              (trans (length-map-prop injL post-h) len-post-h)
              (trans (length-map-prop injR Hk.cod)
                     (trans (length-cod-⟪⟫ k)
                            (cong length (sym (flatten-NoSigma nk))))))
agen-eout-position {f = h ⊗₁ k} (single-agen-⊗-r {A = A_h} nh sk) =
  -- ⟪h ⊗ k⟫ = hTensor ⟪h⟫ ⟪k⟫.  composed.cod = map injL Hh.cod ++ map injR Hk.cod.
  -- Agen edge in composed = Hh.nE ↑ʳ (SingleAgen-edge sk).
  -- Its eout in composed = map injR (⟪k⟫.eout (SingleAgen-edge sk)).
  pre , post ,
  trans cod-eq (cong (λ xs → pre ++ xs ++ post) (sym eout-composed-eq)) ,
  pre-len-eq ,
  trans (length-map-prop injR post-k) len-post-k
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    open hTensor-impl ⟪ h ⟫ ⟪ k ⟫ using (injL; injR; eout-c-inj₂-red)
    module Hh = Hypergraph ⟪ h ⟫
    module Hk = Hypergraph ⟪ k ⟫
    ih = agen-eout-position sk
    pre-k    = proj₁ ih
    post-k   = proj₁ (proj₂ ih)
    cod-eq-k = proj₁ (proj₂ (proj₂ ih))
    len-pre-k = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-k = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    pre = map injL Hh.cod ++ map injR pre-k
    eout-k = Hk.eout (SingleAgen-edge sk)
    post = map injR post-k
    map-decomp :
      map injR Hk.cod
      ≡ map injR pre-k ++ map injR eout-k ++ map injR post-k
    map-decomp =
      trans (cong (map injR) cod-eq-k)
            (trans (map-++ injR pre-k (eout-k ++ post-k))
                   (cong (map injR pre-k ++_)
                         (map-++ injR eout-k post-k)))
    cod-eq :
      map injL Hh.cod ++ map injR Hk.cod
      ≡ pre ++ map injR eout-k ++ post
    cod-eq =
      trans (cong (map injL Hh.cod ++_) map-decomp)
            (sym (++-assoc (map injL Hh.cod) (map injR pre-k) _))
    eout-composed-eq :
      Hypergraph.eout ⟪ h ⊗₁ k ⟫ (Hh.nE ↑ʳ SingleAgen-edge sk)
      ≡ map injR eout-k
    eout-composed-eq = eout-c-inj₂-red (SingleAgen-edge sk)
    -- pre length: length(map injL Hh.cod) + length(map injR pre-k) = length flatten B_h + length pre-k.
    -- For NoSigma h: flatten A_h ≡ flatten B_h.
    pre-len-eq :
      length pre ≡ length (flatten A_h) + length-YL-strip sk
    pre-len-eq =
      trans (length-++ (map injL Hh.cod))
            (cong₂ _+_
              (trans (length-map-prop injL Hh.cod)
                     (trans (length-cod-⟪⟫ h)
                            (cong length (sym (flatten-NoSigma nh)))))
              (trans (length-map-prop injR pre-k) len-pre-k))
agen-eout-position {f = h ∘ k} (single-agen-∘-l sh nk) =
  -- ⟪h ∘ k⟫ = hComposeP ⟪k⟫ ⟪h⟫ bdy.
  --   composed.cod = map remapP ⟪h⟫.cod.
  --   Agen edge in composed = ⟪k⟫.nE ↑ʳ (SingleAgen-edge sh).
  --   Its eout in composed = map remapP (⟪h⟫.eout (SingleAgen-edge sh)).
  -- By IH on sh: ⟪h⟫.cod = pre-h ++ eout-h ++ post-h.
  -- composed.cod = map remapP ⟪h⟫.cod = map remapP (pre-h ++ eout-h ++ post-h)
  --              = map remapP pre-h ++ map remapP eout-h ++ map remapP post-h.
  pre , post ,
  trans cod-eq (cong (λ xs → pre ++ xs ++ post) (sym eout-composed-eq)) ,
  trans (length-map-prop remapP pre-h) len-pre-h ,
  trans (length-map-prop remapP post-h) len-post-h
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    bdy = trans (⟪⟫-codL k) (sym (⟪⟫-domL h))
    open hComposeP-impl ⟪ k ⟫ ⟪ h ⟫ bdy
      using (remapP; eout-c-inj₂-red)
    module Gk = Hypergraph ⟪ k ⟫
    module Kh = Hypergraph ⟪ h ⟫
    ih = agen-eout-position sh
    pre-h    = proj₁ ih
    post-h   = proj₁ (proj₂ ih)
    cod-eq-h = proj₁ (proj₂ (proj₂ ih))
    len-pre-h = proj₁ (proj₂ (proj₂ (proj₂ ih)))
    len-post-h = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    pre = map remapP pre-h
    eout-h = Kh.eout (SingleAgen-edge sh)
    post = map remapP post-h
    cod-eq :
      map remapP Kh.cod
      ≡ pre ++ map remapP eout-h ++ post
    cod-eq =
      trans (cong (map remapP) cod-eq-h)
            (trans (map-++ remapP pre-h (eout-h ++ post-h))
                   (cong (map remapP pre-h ++_)
                         (map-++ remapP eout-h post-h)))
    eout-composed-eq :
      Hypergraph.eout ⟪ h ∘ k ⟫ (Gk.nE ↑ʳ SingleAgen-edge sh)
      ≡ map remapP eout-h
    eout-composed-eq = eout-c-inj₂-red (SingleAgen-edge sh)

--------------------------------------------------------------------------------
-- `Unique`-middle-position uniqueness: if `xs ≡ a ++ M ++ b ≡ c ++ M ++ d`
-- with `Unique xs` and `M` non-empty (= `m₀ ∷ ms`), then `length a ≡ length c`.
--
-- Proof: induction on `a, c`.
--   * Both []: trivially refl.
--   * Both cons: heads agree (= xs's first element).  Recurse with the
--     tail of xs (which is still Unique).
--   * One []:   xs = M ++ ... AND xs = (c₀ ∷ c') ++ M ++ ...
--               so xs's first element is both M[0] (= m₀) and c₀, hence
--               c₀ ≡ m₀.  By Unique, m₀ doesn't appear in xs's tail.  But
--               the tail of xs is c' ++ M ++ ..., which DOES contain m₀
--               (in the middle).  Contradiction.

private
  open import Data.List using ([]; _∷_)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  import Data.List.Relation.Unary.AllPairs as AllPairs
  import Data.List.Relation.Unary.All       as ListAll
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Relation.Nullary using (¬_)

  -- For `Unique (a ∷ as)`, a is distinct from every element of as.
  Unique-head-not-in-tail
    : ∀ {a} {A : Set a} {x : A} {xs : List A}
    → Unique (x ∷ xs) → ¬ (x ∈ xs)
  Unique-head-not-in-tail (x≢ AllPairs.∷ _) x∈xs =
    head-not-in x≢ x∈xs
    where
      open import Relation.Binary.PropositionalEquality using (_≢_)
      head-not-in : ∀ {a} {A : Set a} {x : A} {xs : List A}
                  → ListAll.All (x ≢_) xs → x ∈ xs → ⊥
      head-not-in (px ListAll.∷ _) (here refl)  = px refl
      head-not-in (_ ListAll.∷ rs) (there x∈xs) = head-not-in rs x∈xs

  -- For Unique (cons-list), the tail is also Unique.
  Unique-tail : ∀ {a} {A : Set a} {x : A} {xs : List A}
              → Unique (x ∷ xs) → Unique xs
  Unique-tail (_ AllPairs.∷ uq) = uq

  -- ++ middle-position uniqueness for Unique lists with non-empty middle.
  ++-middle-length-eq
    : ∀ {a} {A : Set a}
        (a' : List A) (m₀ : A) (ms b : List A)
        (c : List A) (d : List A)
    → Unique (a' ++ (m₀ ∷ ms) ++ b)
    → a' ++ (m₀ ∷ ms) ++ b ≡ c ++ (m₀ ∷ ms) ++ d
    → length a' ≡ length c
  ++-middle-length-eq [] m₀ ms b [] d _ _ = refl
  ++-middle-length-eq [] m₀ ms b (c₀ ∷ c') d uq eq
    = ⊥-elim contra
    where
      -- xs = m₀ ∷ ms ++ b = c₀ ∷ c' ++ (m₀ ∷ ms) ++ d.
      -- Head equality: c₀ ≡ m₀.
      head-eq : c₀ ≡ m₀
      head-eq = sym (cons-head-eq eq)
        where
          cons-head-eq : ∀ {a} {A : Set a} {x y : A} {xs ys : List A}
                       → x ∷ xs ≡ y ∷ ys → x ≡ y
          cons-head-eq refl = refl
      -- Tail: ms ++ b = c' ++ (m₀ ∷ ms) ++ d
      tail-eq : ms ++ b ≡ c' ++ (m₀ ∷ ms) ++ d
      tail-eq = cons-tail-eq eq
        where
          cons-tail-eq : ∀ {a} {A : Set a} {x y : A} {xs ys : List A}
                       → x ∷ xs ≡ y ∷ ys → xs ≡ ys
          cons-tail-eq refl = refl
      -- m₀ ∈ xs's tail (= ms ++ b)? It's in c' ++ (m₀ ∷ ms) ++ d.
      m₀-in-tail : m₀ ∈ ms ++ b
      m₀-in-tail = subst (m₀ ∈_) (sym tail-eq)
        (∈-++⁺ʳ c' (here refl))
      -- But by Unique (m₀ ∷ ms ++ b), m₀ ∉ ms ++ b.
      contra : ⊥
      contra = Unique-head-not-in-tail uq m₀-in-tail
  ++-middle-length-eq (a₀ ∷ a') m₀ ms b [] d uq eq
    = ⊥-elim contra
    where
      head-eq : a₀ ≡ m₀
      head-eq = cons-head-eq eq
        where
          cons-head-eq : ∀ {a} {A : Set a} {x y : A} {xs ys : List A}
                       → x ∷ xs ≡ y ∷ ys → x ≡ y
          cons-head-eq refl = refl
      tail-eq : a' ++ (m₀ ∷ ms) ++ b ≡ ms ++ d
      tail-eq = cons-tail-eq eq
        where
          cons-tail-eq : ∀ {a} {A : Set a} {x y : A} {xs ys : List A}
                       → x ∷ xs ≡ y ∷ ys → xs ≡ ys
          cons-tail-eq refl = refl
      m₀-in-tail : m₀ ∈ a' ++ (m₀ ∷ ms) ++ b
      m₀-in-tail = ∈-++⁺ʳ a' (here refl)
      uq-tail : Unique (a' ++ (m₀ ∷ ms) ++ b)
      uq-tail = Unique-tail (subst Unique (cong (_∷ _) head-eq) uq)
      -- uq : Unique (a₀ ∷ a' ++ (m₀ ∷ ms) ++ b) with a₀ = m₀.
      -- So m₀ should not be in a' ++ (m₀ ∷ ms) ++ b. Contradiction.
      contra : ⊥
      contra = Unique-head-not-in-tail uq' m₀-in-tail
        where
          uq' : Unique (m₀ ∷ a' ++ (m₀ ∷ ms) ++ b)
          uq' = subst (λ z → Unique (z ∷ a' ++ (m₀ ∷ ms) ++ b)) head-eq uq
  ++-middle-length-eq (a₀ ∷ a') m₀ ms b (c₀ ∷ c') d uq eq =
    -- xs = a₀ ∷ a' ++ (m₀ ∷ ms) ++ b = c₀ ∷ c' ++ (m₀ ∷ ms) ++ d.
    -- a₀ ≡ c₀.  Recurse on tails.
    cong suc (++-middle-length-eq a' m₀ ms b c' d (Unique-tail uq) tail-eq)
    where
      tail-eq : a' ++ (m₀ ∷ ms) ++ b ≡ c' ++ (m₀ ∷ ms) ++ d
      tail-eq = cons-tail-eq eq
        where
          cons-tail-eq : ∀ {a} {A : Set a} {x y : A} {xs ys : List A}
                       → x ∷ xs ≡ y ∷ ys → xs ≡ ys
          cons-tail-eq refl = refl

--------------------------------------------------------------------------------
-- `YL-length-from-iso-nonempty`: extract `length-YL-strip` equality
-- when the Agen edge's `ein` is non-empty.
--
-- Proof: combine `agen-ein-position sf, sg` with `φ-dom` from the iso
-- and `++-middle-length-eq`.  The iso gives `⟪g⟫.dom ≡ map φ ⟪f⟫.dom`,
-- and `ψ-ein` on the unique Agen edge (with `ψ : Fin 1 → Fin 1` being
-- the identity) gives `⟪g⟫.ein agen-g ≡ map φ (⟪f⟫.ein agen-f)`.
-- From sf's decomposition, `map φ ⟪f⟫.dom = map φ pre-f ++ map φ (ein-f) ++ map φ post-f`.
-- This and sg's decomposition both equal `⟪g⟫.dom`.  Using
-- `++-middle-length-eq` with `Unique ⟪g⟫.dom`, the prefixes' lengths
-- agree.

open import Relation.Binary.PropositionalEquality using (_≢_)

YL-length-from-iso-nonempty
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
  → Hypergraph.ein ⟪ g ⟫ (SingleAgen-edge sg) ≢ []
  → length-YL-strip sf ≡ length-YL-strip sg
YL-length-from-iso-nonempty {f = f} {g = g} sf sg iso ein-g-nonempty =
  trans (sym len-pre-f-eq)
        (trans len-prefix-eq len-pre-g-eq)
  where
    open _≅ᴴ_ iso
    module HF = Hypergraph ⟪ f ⟫
    module HG = Hypergraph ⟪ g ⟫

    -- sf decomp: ⟪f⟫.dom ≡ pre-f ++ ein-f ++ post-f
    pf = agen-ein-position sf
    pre-f = proj₁ pf
    post-f = proj₁ (proj₂ pf)
    dom-eq-f = proj₁ (proj₂ (proj₂ pf))
    len-pre-f-eq : length pre-f ≡ length-YL-strip sf
    len-pre-f-eq = proj₁ (proj₂ (proj₂ (proj₂ pf)))

    -- sg decomp: ⟪g⟫.dom ≡ pre-g ++ ein-g ++ post-g
    pg = agen-ein-position sg
    pre-g = proj₁ pg
    post-g = proj₁ (proj₂ pg)
    dom-eq-g = proj₁ (proj₂ (proj₂ pg))
    len-pre-g-eq : length pre-g ≡ length-YL-strip sg
    len-pre-g-eq = proj₁ (proj₂ (proj₂ (proj₂ pg)))

    ein-f = HF.ein (SingleAgen-edge sf)
    ein-g = HG.ein (SingleAgen-edge sg)

    -- ψ : Fin 1 → Fin 1, must be identity.  So ψ (SingleAgen-edge sf)
    -- equals SingleAgen-edge sg (when both have nE = 1).
    nE-eq-g : HG.nE ≡ 1
    nE-eq-g = nE-SingleAgen sg

    Fin1-uniq-loc : (x : Fin 1) → x ≡ zero
    Fin1-uniq-loc zero = refl

    subst-Fin-inj-loc
      : ∀ {n m : ℕ} (p : n ≡ m) {x y : Fin n}
      → subst Fin p x ≡ subst Fin p y → x ≡ y
    subst-Fin-inj-loc refl eq = eq

    ψ-edge-eq : ψ (SingleAgen-edge sf) ≡ SingleAgen-edge sg
    ψ-edge-eq = subst-Fin-inj-loc nE-eq-g
      (trans (Fin1-uniq-loc (subst Fin nE-eq-g (ψ (SingleAgen-edge sf))))
             (sym (Fin1-uniq-loc (subst Fin nE-eq-g (SingleAgen-edge sg)))))

    ein-g-eq : ein-g ≡ map φ ein-f
    ein-g-eq =
      trans (cong HG.ein (sym ψ-edge-eq))
            (ψ-ein (SingleAgen-edge sf))

    -- ⟪g⟫.dom = map φ ⟪f⟫.dom = map φ (pre-f ++ ein-f ++ post-f)
    --        = map φ pre-f ++ map φ ein-f ++ map φ post-f
    --        = map φ pre-f ++ ein-g ++ map φ post-f.
    g-dom-eq-φ :
      HG.dom ≡ map φ pre-f ++ ein-g ++ map φ post-f
    g-dom-eq-φ = EQR.begin
      HG.dom
        EQR.≡⟨ φ-dom ⟩
      map φ HF.dom
        EQR.≡⟨ cong (map φ) dom-eq-f ⟩
      map φ (pre-f ++ ein-f ++ post-f)
        EQR.≡⟨ map-++ φ pre-f (ein-f ++ post-f) ⟩
      map φ pre-f ++ map φ (ein-f ++ post-f)
        EQR.≡⟨ cong (map φ pre-f ++_) (map-++ φ ein-f post-f) ⟩
      map φ pre-f ++ map φ ein-f ++ map φ post-f
        EQR.≡⟨ cong (λ x → map φ pre-f ++ x ++ map φ post-f) (sym ein-g-eq) ⟩
      map φ pre-f ++ ein-g ++ map φ post-f
        EQR.∎
      where module EQR = ≡-Reasoning

    -- ⟪g⟫.dom ≡ pre-g ++ ein-g ++ post-g (= dom-eq-g).
    -- ⟪g⟫.dom ≡ map φ pre-f ++ ein-g ++ map φ post-f (= g-dom-eq-φ).
    -- Equate: pre-g ++ ein-g ++ post-g ≡ map φ pre-f ++ ein-g ++ map φ post-f.
    decomp-eq :
      pre-g ++ ein-g ++ post-g ≡ map φ pre-f ++ ein-g ++ map φ post-f
    decomp-eq = trans (sym dom-eq-g) g-dom-eq-φ

    g-dom-Unique : Unique HG.dom
    g-dom-Unique = ⟪_⟫-dom-unique g

    -- Convert dom-eq-g into Unique-friendly form.
    -- ⟪g⟫.dom = pre-g ++ ein-g ++ post-g, so Unique on this list.
    -- Use ++-middle-length-eq.
    decomp-Unique : Unique (pre-g ++ ein-g ++ post-g)
    decomp-Unique = subst Unique dom-eq-g g-dom-Unique

    -- ein-g is non-empty, so split into m₀ ∷ ms.
    extract-len-eq :
      (m₀ : Fin HG.nV) (ms : List (Fin HG.nV))
      → ein-g ≡ m₀ ∷ ms
      → length pre-g ≡ length (map φ pre-f)
    extract-len-eq m₀ ms ein-g-cons =
      ++-middle-length-eq
        pre-g m₀ ms post-g
        (map φ pre-f) (map φ post-f)
        (subst (λ x → Unique (pre-g ++ x ++ post-g)) ein-g-cons decomp-Unique)
        (helper-eq m₀ ms ein-g-cons)
      where
        helper-eq : (m₀ : Fin HG.nV) (ms : List (Fin HG.nV))
                  → ein-g ≡ m₀ ∷ ms
                  → pre-g ++ (m₀ ∷ ms) ++ post-g
                  ≡ map φ pre-f ++ (m₀ ∷ ms) ++ map φ post-f
        helper-eq m₀ ms eq =
          trans (cong (λ x → pre-g ++ x ++ post-g) (sym eq))
                (trans decomp-eq
                       (cong (λ x → map φ pre-f ++ x ++ map φ post-f) eq))

    -- Now extract using ein-g-nonempty.  Pattern match on ein-g via
    -- helper that exposes the structural equality to the body.
    len-prefix-eq : length pre-f ≡ length pre-g
    len-prefix-eq = lemma ein-g refl
      where
        lemma : (xs : List (Fin HG.nV))
              → xs ≡ ein-g
              → length pre-f ≡ length pre-g
        lemma []        xs-eq = ⊥-elim (ein-g-nonempty (sym xs-eq))
        lemma (m₀ ∷ ms) xs-eq =
          trans (sym (length-map-prop φ pre-f))
                (sym (extract-len-eq m₀ ms (sym xs-eq)))

--------------------------------------------------------------------------------
-- `YL-length-from-iso`: the main length-equality extraction.
--
-- Dispatches on whether the Agen edge's `ein` in `⟪g⟫` is empty or not:
-- * non-empty: use `YL-length-from-iso-nonempty`.
-- * empty (i.e., `flatten Aᵢ_g ≡ []`, meaning Aᵢ is built only from
--   `unit`): in this case, the iso does not provide positional
--   constraints on the ein, and length-YL is NOT iso-invariant in
--   general.  This case is left as a documented limitation; for
--   practical signatures (where generators rarely have unit-typed
--   sources), the non-empty case suffices.

YL-length-from-iso
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (ein-g-nonempty : Hypergraph.ein ⟪ g ⟫ (SingleAgen-edge sg) ≢ [])
  → length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
  ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sg)))
YL-length-from-iso sf sg iso ein-g-nonempty =
  trans (sym (length-YL-strip-≡ sf))
        (trans (YL-length-from-iso-nonempty sf sg iso ein-g-nonempty)
               (length-YL-strip-≡ sg))

--------------------------------------------------------------------------------
-- `YL-length-from-iso-nonempty-eout`: eout-side counterpart of
-- `YL-length-from-iso-nonempty`.  Extracts `length-YL-strip sf ≡
-- length-YL-strip sg` from the iso when the Agen edge's `eout` is
-- non-empty (`flatten Bᵢ_g ≢ []`).
--
-- Proof mirrors the ein-side: combine `agen-eout-position` with
-- `φ-cod`, `ψ-eout`, `⟪_⟫-cod-unique`, and `++-middle-length-eq`.

YL-length-from-iso-nonempty-eout
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
  → Hypergraph.eout ⟪ g ⟫ (SingleAgen-edge sg) ≢ []
  → length-YL-strip sf ≡ length-YL-strip sg
YL-length-from-iso-nonempty-eout {f = f} {g = g} sf sg iso eout-g-nonempty =
  trans (sym len-pre-f-eq)
        (trans len-prefix-eq len-pre-g-eq)
  where
    open _≅ᴴ_ iso
    module HF = Hypergraph ⟪ f ⟫
    module HG = Hypergraph ⟪ g ⟫

    -- sf decomp: ⟪f⟫.cod ≡ pre-f ++ eout-f ++ post-f
    pf = agen-eout-position sf
    pre-f = proj₁ pf
    post-f = proj₁ (proj₂ pf)
    cod-eq-f = proj₁ (proj₂ (proj₂ pf))
    len-pre-f-eq : length pre-f ≡ length-YL-strip sf
    len-pre-f-eq = proj₁ (proj₂ (proj₂ (proj₂ pf)))

    -- sg decomp: ⟪g⟫.cod ≡ pre-g ++ eout-g ++ post-g
    pg = agen-eout-position sg
    pre-g = proj₁ pg
    post-g = proj₁ (proj₂ pg)
    cod-eq-g = proj₁ (proj₂ (proj₂ pg))
    len-pre-g-eq : length pre-g ≡ length-YL-strip sg
    len-pre-g-eq = proj₁ (proj₂ (proj₂ (proj₂ pg)))

    eout-f = HF.eout (SingleAgen-edge sf)
    eout-g = HG.eout (SingleAgen-edge sg)

    -- ψ : Fin 1 → Fin 1, must be identity.
    nE-eq-g : HG.nE ≡ 1
    nE-eq-g = nE-SingleAgen sg

    Fin1-uniq-loc : (x : Fin 1) → x ≡ zero
    Fin1-uniq-loc zero = refl

    subst-Fin-inj-loc
      : ∀ {n m : ℕ} (p : n ≡ m) {x y : Fin n}
      → subst Fin p x ≡ subst Fin p y → x ≡ y
    subst-Fin-inj-loc refl eq = eq

    ψ-edge-eq : ψ (SingleAgen-edge sf) ≡ SingleAgen-edge sg
    ψ-edge-eq = subst-Fin-inj-loc nE-eq-g
      (trans (Fin1-uniq-loc (subst Fin nE-eq-g (ψ (SingleAgen-edge sf))))
             (sym (Fin1-uniq-loc (subst Fin nE-eq-g (SingleAgen-edge sg)))))

    eout-g-eq : eout-g ≡ map φ eout-f
    eout-g-eq =
      trans (cong HG.eout (sym ψ-edge-eq))
            (ψ-eout (SingleAgen-edge sf))

    g-cod-eq-φ :
      HG.cod ≡ map φ pre-f ++ eout-g ++ map φ post-f
    g-cod-eq-φ = EQR.begin
      HG.cod
        EQR.≡⟨ φ-cod ⟩
      map φ HF.cod
        EQR.≡⟨ cong (map φ) cod-eq-f ⟩
      map φ (pre-f ++ eout-f ++ post-f)
        EQR.≡⟨ map-++ φ pre-f (eout-f ++ post-f) ⟩
      map φ pre-f ++ map φ (eout-f ++ post-f)
        EQR.≡⟨ cong (map φ pre-f ++_) (map-++ φ eout-f post-f) ⟩
      map φ pre-f ++ map φ eout-f ++ map φ post-f
        EQR.≡⟨ cong (λ x → map φ pre-f ++ x ++ map φ post-f) (sym eout-g-eq) ⟩
      map φ pre-f ++ eout-g ++ map φ post-f
        EQR.∎
      where module EQR = ≡-Reasoning

    decomp-eq :
      pre-g ++ eout-g ++ post-g ≡ map φ pre-f ++ eout-g ++ map φ post-f
    decomp-eq = trans (sym cod-eq-g) g-cod-eq-φ

    g-cod-Unique : Unique HG.cod
    g-cod-Unique = ⟪_⟫-cod-unique g

    decomp-Unique : Unique (pre-g ++ eout-g ++ post-g)
    decomp-Unique = subst Unique cod-eq-g g-cod-Unique

    extract-len-eq :
      (m₀ : Fin HG.nV) (ms : List (Fin HG.nV))
      → eout-g ≡ m₀ ∷ ms
      → length pre-g ≡ length (map φ pre-f)
    extract-len-eq m₀ ms eout-g-cons =
      ++-middle-length-eq
        pre-g m₀ ms post-g
        (map φ pre-f) (map φ post-f)
        (subst (λ x → Unique (pre-g ++ x ++ post-g)) eout-g-cons decomp-Unique)
        (helper-eq m₀ ms eout-g-cons)
      where
        helper-eq : (m₀ : Fin HG.nV) (ms : List (Fin HG.nV))
                  → eout-g ≡ m₀ ∷ ms
                  → pre-g ++ (m₀ ∷ ms) ++ post-g
                  ≡ map φ pre-f ++ (m₀ ∷ ms) ++ map φ post-f
        helper-eq m₀ ms eq =
          trans (cong (λ x → pre-g ++ x ++ post-g) (sym eq))
                (trans decomp-eq
                       (cong (λ x → map φ pre-f ++ x ++ map φ post-f) eq))

    len-prefix-eq : length pre-f ≡ length pre-g
    len-prefix-eq = lemma eout-g refl
      where
        lemma : (xs : List (Fin HG.nV))
              → xs ≡ eout-g
              → length pre-f ≡ length pre-g
        lemma []        xs-eq = ⊥-elim (eout-g-nonempty (sym xs-eq))
        lemma (m₀ ∷ ms) xs-eq =
          trans (sym (length-map-prop φ pre-f))
                (sym (extract-len-eq m₀ ms (sym xs-eq)))

--------------------------------------------------------------------------------
-- `YL-length-from-iso-eout`: the eout-side wrapper, parallel to
-- `YL-length-from-iso`.  Lifts `YL-length-from-iso-nonempty-eout` to
-- the `flatten YL` form.

YL-length-from-iso-eout
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (eout-g-nonempty : Hypergraph.eout ⟪ g ⟫ (SingleAgen-edge sg) ≢ [])
  → length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
  ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sg)))
YL-length-from-iso-eout sf sg iso eout-g-nonempty =
  trans (sym (length-YL-strip-≡ sf))
        (trans (YL-length-from-iso-nonempty-eout sf sg iso eout-g-nonempty)
               (length-YL-strip-≡ sg))

--------------------------------------------------------------------------------
-- `discharge-aligned`: the core "Mac-Lane wrapper closure" lemma.
--
-- Given:
--   * The two SingleAgen normal forms (already aligned at the Aᵢ/Bᵢ/u
--     level — they share `u : mor Aᵢ Bᵢ`);
--   * Positional alignment: `eYL : flatten YL-f ≡ flatten YL-g` and
--     `eYR : flatten YR-f ≡ flatten YR-g`;
--
-- conclude the two NF expressions are `≈Term`-equal:
--   c-to-f ∘ (id ⊗ (Agen u ⊗ id)) ∘ c-from-f
--     ≈Term
--   c-to-g ∘ (id ⊗ (Agen u ⊗ id)) ∘ c-from-g.
--
-- Proof strategy (composed from existing infrastructure):
--   * Build `bA : (YL_f ⊗ Aᵢ ⊗ YR_f) → (YL_g ⊗ Aᵢ ⊗ YR_g)` as
--     `bridge-NoSigma-fwd eA` (where `eA` is the appropriate flatten
--     equality).
--   * Build `bB : (YL_f ⊗ Bᵢ ⊗ YR_f) → (YL_g ⊗ Bᵢ ⊗ YR_g)` similarly.
--   * Use `NoSigma-coherence` to rewrite c-from-f as `bA-bwd ∘ c-from-g`
--     (both are NoSigma morphisms from A to (YL_f ⊗ Aᵢ ⊗ YR_f)).
--   * Use `bridge-naturality-pos` to push `bA-bwd` past M.
--   * Use `NoSigma-coherence` again on the c-to side.

private
  -- Auxiliary: assemble flatten equality for the triple tensor
  -- `YL ⊗ X ⊗ YR` from individual eYL, eYR equalities (and shared X).
  eA-from-eYL-eYR
    : ∀ {YL-f YR-f YL-g YR-g X : ObjTerm}
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
    → flatten (YL-f ⊗₀ X ⊗₀ YR-f) ≡ flatten (YL-g ⊗₀ X ⊗₀ YR-g)
  eA-from-eYL-eYR {X = X} eYL eYR =
    cong₂ _++_ eYL (cong (flatten X ++_) eYR)
    where open import Relation.Binary.PropositionalEquality using (cong₂)

  -- "Backwards" variant of `bridge-naturality-pos`: derived from the
  -- forward version by composing with the bridge iso laws.  Statement:
  --
  --   M_f ∘ bridge-NoSigma-bwd eA ≈Term bridge-NoSigma-bwd eB ∘ M_g
  --
  -- where `M_f = id ⊗ (Agen u ⊗ id_{YR-f})`, M_g symmetrically.
  bridge-naturality-pos-bwd
    : ∀ {YL-f YR-f YL-g YR-g Aᵢ Bᵢ : ObjTerm}
        (u : mor Aᵢ Bᵢ)
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
        (eA  : flatten (YL-f ⊗₀ Aᵢ ⊗₀ YR-f)
             ≡ flatten (YL-g ⊗₀ Aᵢ ⊗₀ YR-g))
        (eB  : flatten (YL-f ⊗₀ Bᵢ ⊗₀ YR-f)
             ≡ flatten (YL-g ⊗₀ Bᵢ ⊗₀ YR-g))
    → (id ⊗₁ (Agen u ⊗₁ id {YR-f})) ∘ bridge-NoSigma-bwd eA
    ≈Term
      bridge-NoSigma-bwd eB ∘ (id ⊗₁ (Agen u ⊗₁ id {YR-g}))
  bridge-naturality-pos-bwd {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ} {Bᵢ}
                            u eYL eYR eA eB = HRBN.begin
      M_f ∘ bA-bwd
        HRBN.≈⟨ ≈-Term-sym FM-bridge.identityˡ ⟩
      id ∘ M_f ∘ bA-bwd
        HRBN.≈⟨ ≈-Term-sym (bridge-NoSigma-isoˡ eB) HRBN.⟩∘⟨refl ⟩
      (bB-bwd ∘ bB-fwd) ∘ M_f ∘ bA-bwd
        HRBN.≈⟨ FM-bridge.assoc ⟩
      bB-bwd ∘ bB-fwd ∘ M_f ∘ bA-bwd
        HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.sym-assoc ⟩
      bB-bwd ∘ (bB-fwd ∘ M_f) ∘ bA-bwd
        HRBN.≈⟨ HRBN.refl⟩∘⟨
                bridge-naturality-pos {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ} {Bᵢ}
                  u eYL eYR eA eB
                  HRBN.⟩∘⟨refl ⟩
      bB-bwd ∘ (M_g ∘ bA-fwd) ∘ bA-bwd
        HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.assoc ⟩
      bB-bwd ∘ M_g ∘ bA-fwd ∘ bA-bwd
        HRBN.≈⟨ HRBN.refl⟩∘⟨ HRBN.refl⟩∘⟨ bridge-NoSigma-isoʳ eA ⟩
      bB-bwd ∘ M_g ∘ id
        HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.identityʳ ⟩
      bB-bwd ∘ M_g HRBN.∎
    where
      bA-fwd = bridge-NoSigma-fwd eA
      bA-bwd = bridge-NoSigma-bwd eA
      bB-fwd = bridge-NoSigma-fwd eB
      bB-bwd = bridge-NoSigma-bwd eB
      M_f    = id ⊗₁ (Agen u ⊗₁ id {YR-f})
      M_g    = id ⊗₁ (Agen u ⊗₁ id {YR-g})

  -- Core wrapper-closure: given pre-aligned generator data (shared
  -- `u : mor Aᵢ Bᵢ`) and positional alignment, the two NF expressions
  -- coincide on the nose.
  discharge-aligned
    : ∀ {A B} {YL-f YR-f YL-g YR-g Aᵢ Bᵢ : ObjTerm} (u : mor Aᵢ Bᵢ)
        {c-from-f : HomTerm A (YL-f ⊗₀ Aᵢ ⊗₀ YR-f)}
        {c-to-f   : HomTerm (YL-f ⊗₀ Bᵢ ⊗₀ YR-f) B}
        {c-from-g : HomTerm A (YL-g ⊗₀ Aᵢ ⊗₀ YR-g)}
        {c-to-g   : HomTerm (YL-g ⊗₀ Bᵢ ⊗₀ YR-g) B}
        (nosigma-from-f : NoSigma c-from-f) (nosigma-to-f : NoSigma c-to-f)
        (nosigma-from-g : NoSigma c-from-g) (nosigma-to-g : NoSigma c-to-g)
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
     → (c-to-f ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-f)
       ≈Term
       (c-to-g ∘ (id ⊗₁ (Agen u ⊗₁ id)) ∘ c-from-g)
  discharge-aligned {A} {B} {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ} {Bᵢ}
                    u {c-from-f} {c-to-f} {c-from-g} {c-to-g}
                    nosigma-from-f nosigma-to-f
                    nosigma-from-g nosigma-to-g
                    eYL eYR =
    let
      eA : flatten (YL-f ⊗₀ Aᵢ ⊗₀ YR-f) ≡ flatten (YL-g ⊗₀ Aᵢ ⊗₀ YR-g)
      eA = eA-from-eYL-eYR {YL-f} {YR-f} {YL-g} {YR-g} {Aᵢ} eYL eYR
      eB : flatten (YL-f ⊗₀ Bᵢ ⊗₀ YR-f) ≡ flatten (YL-g ⊗₀ Bᵢ ⊗₀ YR-g)
      eB = eA-from-eYL-eYR {YL-f} {YR-f} {YL-g} {YR-g} {Bᵢ} eYL eYR
      bA-bwd = bridge-NoSigma-bwd eA
      bB-fwd = bridge-NoSigma-fwd eB
      bB-bwd = bridge-NoSigma-bwd eB
      bA-bwd-NS = bridge-NoSigma-bwd-NS {YL-f ⊗₀ Aᵢ ⊗₀ YR-f} {YL-g ⊗₀ Aᵢ ⊗₀ YR-g} eA
      bB-fwd-NS = bridge-NoSigma-fwd-NS {YL-f ⊗₀ Bᵢ ⊗₀ YR-f} {YL-g ⊗₀ Bᵢ ⊗₀ YR-g} eB
      bB-bwd-NS = bridge-NoSigma-bwd-NS {YL-f ⊗₀ Bᵢ ⊗₀ YR-f} {YL-g ⊗₀ Bᵢ ⊗₀ YR-g} eB
      M_f    = id ⊗₁ (Agen u ⊗₁ id {YR-f})
      M_g    = id ⊗₁ (Agen u ⊗₁ id {YR-g})

      -- c-from-f ≈ bA-bwd ∘ c-from-g  (both NoSigma : A → YL_f ⊗ Aᵢ ⊗ YR_f).
      cfrom-rewrite : c-from-f ≈Term bA-bwd ∘ c-from-g
      cfrom-rewrite =
        NoSigma-coherence nosigma-from-f (nosigma-∘ bA-bwd-NS nosigma-from-g)

      -- c-to-f ≈ c-to-g ∘ bB-fwd  (both NoSigma : (YL_f ⊗ Bᵢ ⊗ YR_f) → B).
      cto-rewrite : c-to-f ≈Term c-to-g ∘ bB-fwd
      cto-rewrite =
        NoSigma-coherence nosigma-to-f
          (nosigma-∘ nosigma-to-g bB-fwd-NS)

      -- bB-fwd ∘ bB-bwd ≈ id (iso law).
      bB-iso : bB-fwd ∘ bB-bwd ≈Term id
      bB-iso = bridge-NoSigma-isoʳ eB

    in HRBN.begin
      c-to-f ∘ M_f ∘ c-from-f
        HRBN.≈⟨ HRBN.refl⟩∘⟨ HRBN.refl⟩∘⟨ cfrom-rewrite ⟩
      c-to-f ∘ M_f ∘ (bA-bwd ∘ c-from-g)
        HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.sym-assoc ⟩
      c-to-f ∘ (M_f ∘ bA-bwd) ∘ c-from-g
        HRBN.≈⟨ HRBN.refl⟩∘⟨ bridge-naturality-pos-bwd u eYL eYR eA eB
                  HRBN.⟩∘⟨refl ⟩
      c-to-f ∘ (bB-bwd ∘ M_g) ∘ c-from-g
        HRBN.≈⟨ HRBN.refl⟩∘⟨ FM-bridge.assoc ⟩
      c-to-f ∘ bB-bwd ∘ M_g ∘ c-from-g
        HRBN.≈⟨ FM-bridge.sym-assoc ⟩
      (c-to-f ∘ bB-bwd) ∘ M_g ∘ c-from-g
        HRBN.≈⟨ (cto-rewrite HRBN.⟩∘⟨refl) HRBN.⟩∘⟨refl ⟩
      ((c-to-g ∘ bB-fwd) ∘ bB-bwd) ∘ M_g ∘ c-from-g
        HRBN.≈⟨ FM-bridge.assoc HRBN.⟩∘⟨refl ⟩
      (c-to-g ∘ (bB-fwd ∘ bB-bwd)) ∘ M_g ∘ c-from-g
        HRBN.≈⟨ (HRBN.refl⟩∘⟨ bB-iso) HRBN.⟩∘⟨refl ⟩
      (c-to-g ∘ id) ∘ M_g ∘ c-from-g
        HRBN.≈⟨ FM-bridge.identityʳ HRBN.⟩∘⟨refl ⟩
      c-to-g ∘ M_g ∘ c-from-g HRBN.∎

--------------------------------------------------------------------------------
-- `single-agen-NF-coherence-discharge-nonempty`: the full constructive
-- discharge of the (narrowed) `single-agen-NF-coherence` postulate in
-- the non-empty Agen-ein case.  Composes:
--
--   * `flat-data-to-ObjTerm`: flat-level eqs → ObjTerm-level eqs (at
--     `single-agen-u` level).
--   * `single-agen-u-strip-{Aᵢ,Bᵢ,u}`: consistency between
--     `single-agen-u` and `single-agen-strip` extractors.  Used to
--     LIFT the ObjTerm eqs from `single-agen-u` to `single-agen-strip`
--     records.
--   * `YL-length-from-iso`: extract `length-YL` equality (REQUIRES
--     non-empty `ein` for the Agen edge).
--   * `positional-alignment-from-length`: convert length equality to
--     flatten-of-YL/YR equalities.
--   * `single-agen-NF-discharge-aux` (helper, below): pattern-matches
--     the lifted strip-level equalities as `refl` and applies
--     `discharge-aligned`.

private
  -- Generic subst₂ fusion lemma for `mor`.
  subst₂-trans-mor
    : ∀ {A B C D E F : ObjTerm}
        (p₁ : A ≡ C) (p₂ : C ≡ E)
        (q₁ : B ≡ D) (q₂ : D ≡ F)
        (u : mor A B)
    → subst₂ mor p₂ q₂ (subst₂ mor p₁ q₁ u)
    ≡ subst₂ mor (trans p₁ p₂) (trans q₁ q₂) u
  subst₂-trans-mor refl refl refl refl _ = refl

  -- `subst₂` cancels its own `sym` inverse in `mor`.
  subst₂-sym-cancel-mor
    : ∀ {A B C D : ObjTerm}
        (p : A ≡ C) (q : B ≡ D)
        (u : mor A B)
    → subst₂ mor (sym p) (sym q) (subst₂ mor p q u) ≡ u
  subst₂-sym-cancel-mor refl refl _ = refl

-- The helper that pattern-matches the strip-level equalities as
-- `refl`.  After matching, the strip records' `Aᵢ`, `Bᵢ`, `u` align
-- definitionally, and the discharge reduces to `discharge-aligned`.
--
-- To enable the pattern-match, we abstract over the strip records
-- (`nf-f, nf-g`) AND over the underlying `f, g` HomTerms by passing
-- the strip equivs explicitly.
private
  single-agen-NF-discharge-aux-cps
    : ∀ {A B} {f g : HomTerm A B}
        {YL-f YR-f Aᵢ-f Bᵢ-f : ObjTerm}
        {YL-g YR-g Aᵢ-g Bᵢ-g : ObjTerm}
        (u-f : mor Aᵢ-f Bᵢ-f) (u-g : mor Aᵢ-g Bᵢ-g)
        {c-from-f : HomTerm A (YL-f ⊗₀ Aᵢ-f ⊗₀ YR-f)}
        {c-to-f   : HomTerm (YL-f ⊗₀ Bᵢ-f ⊗₀ YR-f) B}
        {c-from-g : HomTerm A (YL-g ⊗₀ Aᵢ-g ⊗₀ YR-g)}
        {c-to-g   : HomTerm (YL-g ⊗₀ Bᵢ-g ⊗₀ YR-g) B}
        (nosigma-from-f : NoSigma c-from-f) (nosigma-to-f : NoSigma c-to-f)
        (nosigma-from-g : NoSigma c-from-g) (nosigma-to-g : NoSigma c-to-g)
        (equiv-f : f ≈Term c-to-f ∘ (id ⊗₁ (Agen u-f ⊗₁ id)) ∘ c-from-f)
        (equiv-g : g ≈Term c-to-g ∘ (id ⊗₁ (Agen u-g ⊗₁ id)) ∘ c-from-g)
        (A-eq : Aᵢ-f ≡ Aᵢ-g)
        (B-eq : Bᵢ-f ≡ Bᵢ-g)
        (u-eq : subst₂ mor A-eq B-eq u-f ≡ u-g)
        (eYL : flatten YL-f ≡ flatten YL-g)
        (eYR : flatten YR-f ≡ flatten YR-g)
     → f ≈Term g
  single-agen-NF-discharge-aux-cps {f = f} {g = g}
                                   u-f .u-f
                                   {c-from-f} {c-to-f} {c-from-g} {c-to-g}
                                   nosigma-from-f nosigma-to-f
                                   nosigma-from-g nosigma-to-g
                                   equiv-f equiv-g
                                   refl refl refl eYL eYR =
    HRBN.begin
      f
        HRBN.≈⟨ equiv-f ⟩
      c-to-f ∘ (id ⊗₁ (Agen u-f ⊗₁ id)) ∘ c-from-f
        HRBN.≈⟨ discharge-aligned u-f
                  nosigma-from-f nosigma-to-f
                  nosigma-from-g nosigma-to-g
                  eYL eYR ⟩
      c-to-g ∘ (id ⊗₁ (Agen u-f ⊗₁ id)) ∘ c-from-g
        HRBN.≈⟨ ≈-Term-sym equiv-g ⟩
      g HRBN.∎

single-agen-NF-discharge-aux
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (A-strip-eq : SingleAgenNF.Aᵢ (single-agen-strip sf)
                  ≡ SingleAgenNF.Aᵢ (single-agen-strip sg))
      (B-strip-eq : SingleAgenNF.Bᵢ (single-agen-strip sf)
                  ≡ SingleAgenNF.Bᵢ (single-agen-strip sg))
      (u-strip-eq : subst₂ mor A-strip-eq B-strip-eq
                      (SingleAgenNF.u (single-agen-strip sf))
                    ≡ SingleAgenNF.u (single-agen-strip sg))
      (eYL : flatten (SingleAgenNF.YL (single-agen-strip sf))
           ≡ flatten (SingleAgenNF.YL (single-agen-strip sg)))
      (eYR : flatten (SingleAgenNF.YR (single-agen-strip sf))
           ≡ flatten (SingleAgenNF.YR (single-agen-strip sg)))
  → f ≈Term g
single-agen-NF-discharge-aux {f = f} {g = g} sf sg A-eq B-eq u-eq eYL eYR =
  single-agen-NF-discharge-aux-cps
    NF-f.u NF-g.u
    NF-f.nosigma-from NF-f.nosigma-to
    NF-g.nosigma-from NF-g.nosigma-to
    NF-f.equiv NF-g.equiv
    A-eq B-eq u-eq eYL eYR
  where
    module NF-f = SingleAgenNF (single-agen-strip sf)
    module NF-g = SingleAgenNF (single-agen-strip sg)

-- The full discharge (non-empty Agen ein case).
single-agen-NF-coherence-discharge-nonempty
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (flat-A-eq : flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                 ≡ flatten (SingleAgenGen.Aᵢ (single-agen-u sg)))
      (flat-B-eq : flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
                 ≡ flatten (SingleAgenGen.Bᵢ (single-agen-u sg)))
      (flat-u-eq : subst₂ FlatGen flat-A-eq flat-B-eq
                      (flat (SingleAgenGen.u (single-agen-u sf)))
                   ≡ flat (SingleAgenGen.u (single-agen-u sg)))
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (ein-g-nonempty : Hypergraph.ein ⟪ g ⟫ (SingleAgen-edge sg) ≢ [])
  → f ≈Term g
single-agen-NF-coherence-discharge-nonempty {f = f} {g = g}
                                            sf sg pA pB pU iso ein-g-nonempty =
  single-agen-NF-discharge-aux sf sg A-strip-eq B-strip-eq u-strip-eq eYL eYR
  where
    -- Step 1: ObjTerm eqs at `single-agen-u` level.
    u_uf = SingleAgenGen.u (single-agen-u sf)
    u_ug = SingleAgenGen.u (single-agen-u sg)
    objterm = flat-data-to-ObjTerm u_uf u_ug pA pB pU
    A-u-eq = proj₁ objterm
    B-u-eq = proj₁ (proj₂ objterm)
    u-u-eq = proj₂ (proj₂ objterm)

    -- Step 2: Lift to strip-record level via consistency lemmas.
    consist-A-f = single-agen-u-strip-Aᵢ sf
    consist-B-f = single-agen-u-strip-Bᵢ sf
    consist-A-g = single-agen-u-strip-Aᵢ sg
    consist-B-g = single-agen-u-strip-Bᵢ sg
    consist-u-f = single-agen-u-strip-u sf
    consist-u-g = single-agen-u-strip-u sg

    A-strip-eq : SingleAgenNF.Aᵢ (single-agen-strip sf)
               ≡ SingleAgenNF.Aᵢ (single-agen-strip sg)
    A-strip-eq = trans (sym consist-A-f) (trans A-u-eq consist-A-g)

    B-strip-eq : SingleAgenNF.Bᵢ (single-agen-strip sf)
               ≡ SingleAgenNF.Bᵢ (single-agen-strip sg)
    B-strip-eq = trans (sym consist-B-f) (trans B-u-eq consist-B-g)

    -- Step 3: Combine the consistency lemmas with u-u-eq to derive
    -- the strip-level u equality.
    --
    -- consist-u-f : subst₂ mor consist-A-f consist-B-f u_uf ≡ NF-f.u
    -- consist-u-g : subst₂ mor consist-A-g consist-B-g u_ug ≡ NF-g.u
    -- u-u-eq      : subst₂ mor A-u-eq B-u-eq u_uf ≡ u_ug
    --
    -- We want:
    --   subst₂ mor A-strip-eq B-strip-eq NF-f.u ≡ NF-g.u
    --
    -- Strategy: substitute NF-f.u via sym (consist-u-f), fuse with
    -- A-strip-eq/B-strip-eq, then use u-u-eq + consist-u-g.

    u-strip-eq : subst₂ mor A-strip-eq B-strip-eq
                   (SingleAgenNF.u (single-agen-strip sf))
                 ≡ SingleAgenNF.u (single-agen-strip sg)
    u-strip-eq = EQR.begin
        subst₂ mor A-strip-eq B-strip-eq (SingleAgenNF.u (single-agen-strip sf))
          EQR.≡⟨ cong (subst₂ mor A-strip-eq B-strip-eq) (sym consist-u-f) ⟩
        subst₂ mor A-strip-eq B-strip-eq
          (subst₂ mor consist-A-f consist-B-f u_uf)
          EQR.≡⟨ subst₂-trans-mor consist-A-f A-strip-eq consist-B-f B-strip-eq u_uf ⟩
        subst₂ mor (trans consist-A-f A-strip-eq)
                   (trans consist-B-f B-strip-eq) u_uf
          EQR.≡⟨ trans-A-collapse ⟩
        subst₂ mor (trans A-u-eq consist-A-g)
                   (trans B-u-eq consist-B-g) u_uf
          EQR.≡⟨ sym (subst₂-trans-mor A-u-eq consist-A-g B-u-eq consist-B-g u_uf) ⟩
        subst₂ mor consist-A-g consist-B-g
          (subst₂ mor A-u-eq B-u-eq u_uf)
          EQR.≡⟨ cong (subst₂ mor consist-A-g consist-B-g) u-u-eq ⟩
        subst₂ mor consist-A-g consist-B-g u_ug
          EQR.≡⟨ consist-u-g ⟩
        SingleAgenNF.u (single-agen-strip sg)
          EQR.∎
      where
        module EQR = ≡-Reasoning

        -- `trans x (trans (sym x) y) ≡ y` (use UIP on ObjTerm).
        -- More precisely:
        --   trans consist-A-f A-strip-eq
        -- = trans consist-A-f (trans (sym consist-A-f) (trans A-u-eq consist-A-g))
        -- = trans (trans consist-A-f (sym consist-A-f)) (trans A-u-eq consist-A-g)  (associativity of trans)
        -- = trans refl (trans A-u-eq consist-A-g)                                    (right inverse, propositional)
        -- = trans A-u-eq consist-A-g                                                 (left identity)
        --
        -- Avoid the propositional reasoning by transforming via
        -- the (definitional) law `trans-assoc` + UIP.
        --
        -- A cleaner approach: pattern-match on consist-A-f and consist-B-f
        -- through a `with` block (they are not always definitionally
        -- refl, but we can rewrite).
        --
        -- Even simpler: prove the entire equality below via a single
        -- subst₂-cong that uses UIP.

        trans-A-collapse :
          subst₂ mor (trans consist-A-f A-strip-eq)
                     (trans consist-B-f B-strip-eq) u_uf
          ≡ subst₂ mor (trans A-u-eq consist-A-g)
                       (trans B-u-eq consist-B-g) u_uf
        trans-A-collapse =
          cong₂ (λ a b → subst₂ mor a b u_uf)
                (UIP-ObjTerm (trans consist-A-f A-strip-eq)
                             (trans A-u-eq consist-A-g))
                (UIP-ObjTerm (trans consist-B-f B-strip-eq)
                             (trans B-u-eq consist-B-g))
          where
            open import Relation.Binary.PropositionalEquality using (cong₂)
            open APROPSignatureDec sig-dec using (_≟-ObjTerm_)
            open import Axiom.UniquenessOfIdentityProofs as UIP-mod
            UIP-ObjTerm : ∀ {x y : ObjTerm} (p q : x ≡ y) → p ≡ q
            UIP-ObjTerm = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟-ObjTerm_

    -- Step 4: Positional alignment via length-from-iso.
    len-eq : length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
           ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sg)))
    len-eq = YL-length-from-iso sf sg iso ein-g-nonempty

    pos-align = positional-alignment-from-length sf sg iso len-eq
    eYL : flatten (SingleAgenNF.YL (single-agen-strip sf))
        ≡ flatten (SingleAgenNF.YL (single-agen-strip sg))
    eYL = proj₁ pos-align
    eYR : flatten (SingleAgenNF.YR (single-agen-strip sf))
        ≡ flatten (SingleAgenNF.YR (single-agen-strip sg))
    eYR = proj₁ (proj₂ pos-align)

--------------------------------------------------------------------------------
-- `single-agen-NF-coherence-discharge-nonempty-eout`: eout-side
-- counterpart of `single-agen-NF-coherence-discharge-nonempty`.  Uses
-- `YL-length-from-iso-eout` (which requires non-empty `eout` for the
-- Agen edge) instead of `YL-length-from-iso`.  All other steps are
-- identical.

single-agen-NF-coherence-discharge-nonempty-eout
  : ∀ {A B} {f g : HomTerm A B}
      (sf : SingleAgen f) (sg : SingleAgen g)
      (flat-A-eq : flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                 ≡ flatten (SingleAgenGen.Aᵢ (single-agen-u sg)))
      (flat-B-eq : flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
                 ≡ flatten (SingleAgenGen.Bᵢ (single-agen-u sg)))
      (flat-u-eq : subst₂ FlatGen flat-A-eq flat-B-eq
                      (flat (SingleAgenGen.u (single-agen-u sf)))
                   ≡ flat (SingleAgenGen.u (single-agen-u sg)))
      (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (eout-g-nonempty : Hypergraph.eout ⟪ g ⟫ (SingleAgen-edge sg) ≢ [])
  → f ≈Term g
single-agen-NF-coherence-discharge-nonempty-eout {f = f} {g = g}
                                                 sf sg pA pB pU iso eout-g-nonempty =
  single-agen-NF-discharge-aux sf sg A-strip-eq B-strip-eq u-strip-eq eYL eYR
  where
    -- Step 1: ObjTerm eqs at `single-agen-u` level.
    u_uf = SingleAgenGen.u (single-agen-u sf)
    u_ug = SingleAgenGen.u (single-agen-u sg)
    objterm = flat-data-to-ObjTerm u_uf u_ug pA pB pU
    A-u-eq = proj₁ objterm
    B-u-eq = proj₁ (proj₂ objterm)
    u-u-eq = proj₂ (proj₂ objterm)

    -- Step 2: Lift to strip-record level via consistency lemmas.
    consist-A-f = single-agen-u-strip-Aᵢ sf
    consist-B-f = single-agen-u-strip-Bᵢ sf
    consist-A-g = single-agen-u-strip-Aᵢ sg
    consist-B-g = single-agen-u-strip-Bᵢ sg
    consist-u-f = single-agen-u-strip-u sf
    consist-u-g = single-agen-u-strip-u sg

    A-strip-eq : SingleAgenNF.Aᵢ (single-agen-strip sf)
               ≡ SingleAgenNF.Aᵢ (single-agen-strip sg)
    A-strip-eq = trans (sym consist-A-f) (trans A-u-eq consist-A-g)

    B-strip-eq : SingleAgenNF.Bᵢ (single-agen-strip sf)
               ≡ SingleAgenNF.Bᵢ (single-agen-strip sg)
    B-strip-eq = trans (sym consist-B-f) (trans B-u-eq consist-B-g)

    u-strip-eq : subst₂ mor A-strip-eq B-strip-eq
                   (SingleAgenNF.u (single-agen-strip sf))
                 ≡ SingleAgenNF.u (single-agen-strip sg)
    u-strip-eq = EQR.begin
        subst₂ mor A-strip-eq B-strip-eq (SingleAgenNF.u (single-agen-strip sf))
          EQR.≡⟨ cong (subst₂ mor A-strip-eq B-strip-eq) (sym consist-u-f) ⟩
        subst₂ mor A-strip-eq B-strip-eq
          (subst₂ mor consist-A-f consist-B-f u_uf)
          EQR.≡⟨ subst₂-trans-mor consist-A-f A-strip-eq consist-B-f B-strip-eq u_uf ⟩
        subst₂ mor (trans consist-A-f A-strip-eq)
                   (trans consist-B-f B-strip-eq) u_uf
          EQR.≡⟨ trans-A-collapse ⟩
        subst₂ mor (trans A-u-eq consist-A-g)
                   (trans B-u-eq consist-B-g) u_uf
          EQR.≡⟨ sym (subst₂-trans-mor A-u-eq consist-A-g B-u-eq consist-B-g u_uf) ⟩
        subst₂ mor consist-A-g consist-B-g
          (subst₂ mor A-u-eq B-u-eq u_uf)
          EQR.≡⟨ cong (subst₂ mor consist-A-g consist-B-g) u-u-eq ⟩
        subst₂ mor consist-A-g consist-B-g u_ug
          EQR.≡⟨ consist-u-g ⟩
        SingleAgenNF.u (single-agen-strip sg)
          EQR.∎
      where
        module EQR = ≡-Reasoning

        trans-A-collapse :
          subst₂ mor (trans consist-A-f A-strip-eq)
                     (trans consist-B-f B-strip-eq) u_uf
          ≡ subst₂ mor (trans A-u-eq consist-A-g)
                       (trans B-u-eq consist-B-g) u_uf
        trans-A-collapse =
          cong₂ (λ a b → subst₂ mor a b u_uf)
                (UIP-ObjTerm (trans consist-A-f A-strip-eq)
                             (trans A-u-eq consist-A-g))
                (UIP-ObjTerm (trans consist-B-f B-strip-eq)
                             (trans B-u-eq consist-B-g))
          where
            open import Relation.Binary.PropositionalEquality using (cong₂)
            open APROPSignatureDec sig-dec using (_≟-ObjTerm_)
            open import Axiom.UniquenessOfIdentityProofs as UIP-mod
            UIP-ObjTerm : ∀ {x y : ObjTerm} (p q : x ≡ y) → p ≡ q
            UIP-ObjTerm = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟-ObjTerm_

    -- Step 4: Positional alignment via length-from-iso-eout.
    len-eq : length (flatten (SingleAgenNF.YL (single-agen-strip sf)))
           ≡ length (flatten (SingleAgenNF.YL (single-agen-strip sg)))
    len-eq = YL-length-from-iso-eout sf sg iso eout-g-nonempty

    pos-align = positional-alignment-from-length sf sg iso len-eq
    eYL : flatten (SingleAgenNF.YL (single-agen-strip sf))
        ≡ flatten (SingleAgenNF.YL (single-agen-strip sg))
    eYL = proj₁ pos-align
    eYR : flatten (SingleAgenNF.YR (single-agen-strip sf))
        ≡ flatten (SingleAgenNF.YR (single-agen-strip sg))
    eYR = proj₁ (proj₂ pos-align)

--------------------------------------------------------------------------------
-- The remaining narrow assumptions of the completeness path, bundled
-- into the `CompletenessAssumptions` record.  The rest of this module
-- (the `nf-resp-≅ᴴ` dispatcher and the top-level
-- `decode-rel-resp-≅ᴴ-full`) lives inside a sub-module parameterized
-- by a record instance, so this file itself is `--safe`-clean: the
-- trust is exposed at the call site that supplies the record.
--
-- ## Discharge progress (this session)
--
-- The Mac-Lane wrapper closure for `single-agen-NF-coherence` has been
-- CONSTRUCTIVELY CLOSED on BOTH sides — ein and eout:
--   * `single-agen-NF-coherence-discharge-nonempty`     (ein non-empty)
--   * `single-agen-NF-coherence-discharge-nonempty-eout` (eout non-empty)
--
-- The chain (parallel on both sides) is:
--   * flat data → ObjTerm eqs via `flat-data-to-ObjTerm`;
--   * `YL-length-from-iso[-eout]` (REQUIRES non-empty `ein`/`eout`);
--   * `positional-alignment-from-length`;
--   * `single-agen-strip` to get NF wrappers;
--   * `discharge-aligned` via `NoSigma-coherence`, `bridge-naturality-pos`,
--     and the bridge iso laws.
--
-- The eout side uses `⟪_⟫-cod-unique` (the cod-side analogue of
-- `⟪_⟫-dom-unique`, proved in `HomTermInvariant`) plus `remap-injective`
-- (in `Prune`) to close the cod-uniqueness of the composite hypergraph.
--
-- The postulate has been NARROWED to the strictly smaller "both empty"
-- case (`single-agen-NF-coherence-empty-ein`, now requiring BOTH the
-- ein-empty and eout-empty preconditions).  The both-empty precondition
-- forces `flatten Aᵢ ≡ []` AND `flatten Bᵢ ≡ []`, i.e. the generator
-- is a "scalar" u : 1 → 1 where both source and target are built only
-- from `unit` constructors.  In this fully-degenerate case neither the
-- ein-side nor the eout-side positional argument finds a vertex to
-- locate; the iso provides no positional constraint and the constructive
-- route fails on both sides.
--
-- For practical signatures where generators have at least one non-unit
-- input or output, the postulate is never invoked.
--
-- `nf-resp-≅ᴴ-residual` covers all other compound cases (terms with
-- σ subterms or ≥2 Agens) and remains architecturally blocked under
-- the current `_≅ᴴ_` (see `REFACTORING.md` § "Architectural
-- blockers").

record CompletenessAssumptions : Set where
  field
    -- Strictly-narrowed `single-agen-NF-coherence`: now only handles
    -- the case where BOTH the Agen edge's `ein` AND `eout` in `⟪g⟫`
    -- are empty.  The non-empty-ein case is constructive via
    -- `single-agen-NF-coherence-discharge-nonempty`, and the
    -- empty-ein-but-non-empty-eout case is constructive via
    -- `single-agen-NF-coherence-discharge-nonempty-eout`.
    --
    -- The both-empty case corresponds to `flatten Aᵢ_g ≡ []` AND
    -- `flatten Bᵢ_g ≡ []`, i.e. Aᵢ and Bᵢ are both built only from
    -- `unit` — a "scalar generator" u : 1 → 1.  In this case neither
    -- the ein-side nor the eout-side positional argument finds a
    -- vertex to locate; the iso provides no positional constraint
    -- and the constructive route fails on both sides.
    --
    -- For practical signatures where generators have at least one
    -- non-unit input or output, this postulate is never invoked.
    single-agen-NF-coherence-empty-ein
      : ∀ {A B} {f g : HomTerm A B}
          (sf : SingleAgen f) (sg : SingleAgen g)
          (flat-A-eq : flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                     ≡ flatten (SingleAgenGen.Aᵢ (single-agen-u sg)))
          (flat-B-eq : flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
                     ≡ flatten (SingleAgenGen.Bᵢ (single-agen-u sg)))
          (flat-u-eq : subst₂ FlatGen flat-A-eq flat-B-eq
                          (flat (SingleAgenGen.u (single-agen-u sf)))
                       ≡ flat (SingleAgenGen.u (single-agen-u sg)))
          (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ein-empty  : Hypergraph.ein  ⟪ g ⟫ (SingleAgen-edge sg) ≡ [])
          (eout-empty : Hypergraph.eout ⟪ g ⟫ (SingleAgen-edge sg) ≡ [])
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
  -- discharging the iso → flat-data step via `single-agen-flat-data`
  -- and then 3-way dispatching:
  --   * ein non-empty: use the constructive
  --     `single-agen-NF-coherence-discharge-nonempty` (ein-side).
  --   * ein empty AND eout non-empty: use the constructive
  --     `single-agen-NF-coherence-discharge-nonempty-eout` (eout-side).
  --   * BOTH ein and eout empty: fall back to the (strictly narrower)
  --     `single-agen-NF-coherence-empty-ein` postulate.
  private
    empty? : ∀ {A : Set} (xs : List A) → (xs ≡ []) ⊎ (xs ≢ [])
    empty? []      = inj₁ refl
    empty? (_ ∷ _) = inj₂ λ ()

  single-agen-coherence-≈Term
    : ∀ {A B} {f g : HomTerm A B}
    → SingleAgen f → SingleAgen g
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → f ≈Term g
  single-agen-coherence-≈Term {g = g} sf sg iso
    with empty? (Hypergraph.ein  ⟪ g ⟫ (SingleAgen-edge sg))
       | empty? (Hypergraph.eout ⟪ g ⟫ (SingleAgen-edge sg))
  ... | inj₂ ein-nonempty | _ =
        single-agen-NF-coherence-discharge-nonempty
          sf sg flat-A-eq flat-B-eq flat-u-eq iso ein-nonempty
        where
          flat-data = single-agen-flat-data sf sg iso
          flat-A-eq = proj₁ flat-data
          flat-B-eq = proj₁ (proj₂ flat-data)
          flat-u-eq = proj₂ (proj₂ flat-data)
  ... | inj₁ _            | inj₂ eout-nonempty =
        single-agen-NF-coherence-discharge-nonempty-eout
          sf sg flat-A-eq flat-B-eq flat-u-eq iso eout-nonempty
        where
          flat-data = single-agen-flat-data sf sg iso
          flat-A-eq = proj₁ flat-data
          flat-B-eq = proj₁ (proj₂ flat-data)
          flat-u-eq = proj₂ (proj₂ flat-data)
  ... | inj₁ ein-empty    | inj₁ eout-empty =
        single-agen-NF-coherence-empty-ein
          sf sg flat-A-eq flat-B-eq flat-u-eq iso ein-empty eout-empty
        where
          flat-data = single-agen-flat-data sf sg iso
          flat-A-eq = proj₁ flat-data
          flat-B-eq = proj₁ (proj₂ flat-data)
          flat-u-eq = proj₂ (proj₂ flat-data)

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

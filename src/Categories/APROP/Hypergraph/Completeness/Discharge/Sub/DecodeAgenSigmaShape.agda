{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The σ-collapse of `agenSigmaResiduals`: `decode-σ-collapse`.
--
-- Target (= `DecodeRoundtrip.decode-roundtrip-σ`,
--          = `DecodeRoundtripAgenSigma.Residuals.decode-σ-collapse`):
--
--   ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
--     → decode (σ {A = A} {B = B}) ≈Term bridge (σ {A = A} {B = B})
--
-- where `σ` is the symmetric-braiding generator (EDGE-FREE, nE = 0), so the
-- algorithm output `decode (σ {A}{B})` reduces to a single `permute-via-vlab`
-- of the canonical append-commutativity permutation `(L ++ R) ↭ (R ++ L)`,
-- composed with `id`.
--
-- Proof chain (the recipe):
--   1. `decode-attempt-shape`-clone: expose
--        `proj₁ (decode-attempt-Linear σ) ≡ pvl-c perm-shape ∘ id`
--      (sig-level; cloned because `LinearExtracts` is `sig-dec`-parameterised).
--   2. KEYSTONE `permute-via-vlab-≈Term-coherence-K`: any two `↭`'s with the
--      same `Unique` codomain give equal `pvl`, so `pvl-c perm-shape ≈
--      pvl-c (++-comm L R)`.
--   3. `BNV.σ-block-comm` (reversed): `pvl (++-comm L R) ≈ to(uf++ R L) ∘ σ
--      ∘ from(uf++ L R)` (block braiding, `Aof L = unflatten (map vlab-c L)`).
--   4. Frame reconciliation: the BNV `uf++`/`Aof` frames are reconciled with
--      `bridge σ`'s `unflatten-flatten-≈ (A ⊗₀ B)` frames using
--      `lem-L : map vlab-c L ≡ flatten A`, `lem-R`, the boundary `subst₂`
--      peeling under `objUIP`, and the one-box braiding-naturality
--      `σ∘[f⊗g]≈[g⊗f]∘σ`.
--
-- Parameterised by `objUIP` + `K : FaithfulnessResidual` (the two K-inputs
-- the rest of the completeness chain threads), exactly like
-- `Sub/DecodeComposeShape.agda` / `Sub/DecodeTensorShape.agda`.
--
-- NO false-as-stated postulate.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeAgenSigmaShape
  (sig : APROPSignature) where

open APROP sig
open import Categories.FreeMonoidal using (v≤v)

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hSwap; hGen; domL-hSwap; codL-hSwap
        ; domL-hGen; codL-hGen; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL
        ; map-lookup-range; domL-hId; codL-hId)
open import Categories.APROP.Hypergraph.Invariant sig
  using (hSwap-cod-Unique; hGen-cod-Unique; hGen-dom-Unique)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈; _≅_; module ≅)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges; process-edges; edge-step; extract-exact; decode-attempt
        ; Agen-edge-aux; extract-prefix; ++-[]-↭)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-self)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of; box-of-cong
        ; edge-step-sound)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-Linear; decode-attempt-hId)

-- The PROVEN ⊗-shape residual (parameterised by `objUIP` + `K`), reused to
-- build `decode-id-is-id` for compound objects.  No new trust: it is the
-- SAME shape lemma the completeness chain already threads.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig as DTS

-- The constructive (`--safe --with-K`) Mac-Lane list machinery for the
-- associator collapse: `α⇒-form-list`, its `++-assoc`-transport `coh`
-- characterisations, `bridge-id-is-id`, and the `subst₂-refl-{cod,dom}`
-- bridges relating a one-sided `subst₂` to a `subst`.
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( α⇒-form-list; α⇐-form-list; α⇒-coh-list; α⇐-coh-list
        ; α⇒-α⇐-iso; bridge-∘; bridge-id-is-id
        ; subst₂-refl-cod; subst₂-refl-dom )
-- The constructive (`--safe --with-K`, postulate-free) well-founded worker
-- proving `bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list …` for EVERY object `A`.
import Categories.APROP.Hypergraph.Completeness.Discharge.BridgeAlphaFormCompound sig as BAFC

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  asFreeMonoidalData using (permute-via-vlab-≈Term-coherence-K)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  asFreeMonoidalData as BNV
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData as BNB

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal using (_⊗ᵢ_)
import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal as MonProp

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (map-++; map-∘; map-cong; ++-identityʳ; ++-assoc)
open import Data.Sum using ([_,_]′)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using ( ≡⇒≈Term; subst₂-resp-≈Term; subst₂-HomTerm-irrel; subst₂-HomTerm-∘
        ; decode-attempt-extract )

private
  -- The bare σ-block frame at `unflatten`-blocks (NO `map`-bridge):
  --   `to(uff++ r l) ∘ σ {unflatten l}{unflatten r} ∘ from(uff++ l r)`,
  -- a `HomTerm (unflatten (l ++ r)) (unflatten (r ++ l))`.
  bframe : (l r : List X)
         → HomTerm (unflatten (l ++ r)) (unflatten (r ++ l))
  bframe l r =
    _≅_.to (unflatten-++-≅ r l)
      ∘ (σ {unflatten l} {unflatten r})
      ∘ _≅_.from (unflatten-++-≅ l r)

  -- `bframe` is `subst₂`-natural in its two block-lists: along `pl : l ≡ l'`,
  -- `pr : r ≡ r'` it transports by `cong unflatten (cong₂ _++_ pl pr)` (dom)
  -- and `cong unflatten (cong₂ _++_ pr pl)` (cod).  Pure `refl`-match.
  bframe-subst₂
    : ∀ {l l' r r' : List X} (pl : l ≡ l') (pr : r ≡ r')
    → subst₂ HomTerm (cong unflatten (cong₂ _++_ pl pr))
                     (cong unflatten (cong₂ _++_ pr pl))
        (bframe l r)
      ≡ bframe l' r'
  bframe-subst₂ refl refl = refl

  -- Pull a codomain-`subst₂` on the outer-left factor and a domain-`subst₂`
  -- on the inner-rightmost factor of a right-associated triple composite out
  -- to a single boundary `subst₂` (the middle stays at fixed objects).  Pure
  -- `refl`-match on `p`, `q`.
  peel-∘-substs
    : ∀ {A A' B₀ B₁ C C'} (p : A ≡ A') (q : C ≡ C')
        (f : HomTerm B₁ C) (g : HomTerm B₀ B₁) (h : HomTerm A B₀)
    → subst₂ HomTerm refl q f ∘ (g ∘ subst₂ HomTerm p refl h)
      ≡ subst₂ HomTerm p q (f ∘ (g ∘ h))
  peel-∘-substs refl refl f g h = refl

  ------------------------------------------------------------------------
  -- ## The empty-residual box collapse (`nil-frame`).
  --
  -- A `box-of`-style framing on the EMPTY residual `[]`, i.e.
  -- `to(uff++ eoL []) ∘ (G ⊗₁ id {unit}) ∘ from(uff++ eiL [])`, collapses
  -- (modulo the `++-identityʳ` boundary subst) to the bare `G`.  The two
  -- right-unit isos `uff++ · []` ARE the right unitor up to the `++ []`
  -- transport (`uff-nil-from`/`uff-nil-to`, by list-induction with base case
  -- = the Kelly unit coherence `λ⇐ ≈ ρ⇐`), then `ρ⇒∘f⊗id≈f∘ρ⇒` slides `G`
  -- past the `⊗₁ id {unit}` and the `ρ⇒ ∘ ρ⇐` units cancel.

  -- `unflatten [] = unit`, recorded for the `uff++ · []` codomains.
  U[] : ObjTerm
  U[] = unflatten []

  -- The domain-side `++-identityʳ` cast `unflatten (xs ++ []) → unflatten xs`.
  dsub : (xs : List X) → HomTerm (unflatten (xs ++ [])) (unflatten xs)
  dsub xs = subst (λ z → HomTerm (unflatten (xs ++ [])) (unflatten z))
                  (++-identityʳ xs) id

  -- The codomain-side `++-identityʳ` cast `unflatten xs → unflatten (xs ++ [])`.
  csub : (xs : List X) → HomTerm (unflatten xs) (unflatten (xs ++ []))
  csub xs = subst (λ z → HomTerm (unflatten z) (unflatten (xs ++ [])))
                  (++-identityʳ xs) id

  -- `unflatten ((x ∷ xs) ++ []) = Var x ⊗₀ unflatten (xs ++ [])`, so the
  -- `dsub`/`csub` casts on a `Var x`-headed list factor as `id ⊗₁ ·`.
  -- These reduce (at `e = refl`) to `id ⊗₁ id ≈Term id` (`id⊗id≈id`).
  dsub-cons : ∀ (x : X) (xs : List X)
            → (id {Var x} ⊗₁ dsub xs) ≈Term dsub (x ∷ xs)
  dsub-cons x xs = lemma (++-identityʳ xs)
    where
      lemma : ∀ {ys} (e : xs ++ [] ≡ ys)
            → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten (xs ++ [])) (unflatten z)) e id)
              ≈Term subst (λ z → HomTerm (Var x ⊗₀ unflatten (xs ++ [])) (unflatten z))
                          (cong (x ∷_) e) id
      lemma refl = id⊗id≈id

  csub-cons : ∀ (x : X) (xs : List X)
            → (id {Var x} ⊗₁ csub xs) ≈Term csub (x ∷ xs)
  csub-cons x xs = lemma (++-identityʳ xs)
    where
      lemma : ∀ {ys} (e : xs ++ [] ≡ ys)
            → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten (xs ++ []))) e id)
              ≈Term subst (λ z → HomTerm (unflatten z) (Var x ⊗₀ unflatten (xs ++ [])))
                          (cong (x ∷_) e) id
      lemma refl = id⊗id≈id

  -- `≅.from (unflatten-++-≅ xs []) ≈Term ρ⇐ ∘ dsub xs`.  By induction:
  --   * `[]`:  `from (≅.sym unitorˡ) = λ⇐ ≈Term ρ⇐` (Kelly unit coherence),
  --            and `dsub [] = id`.
  --   * `x∷xs`: `from = α⇐ ∘ (id ⊗₁ from-IH)`; slide via `coherence-inv₂`
  --            (`α⇐ ∘ (id ⊗₁ ρ⇐) ≈ ρ⇐`) + `dsub-cons`.
  uff-nil-from
    : ∀ (xs : List X)
    → _≅_.from (unflatten-++-≅ xs []) ≈Term ρ⇐ ∘ dsub xs
  uff-nil-from [] = begin
    λ⇐ {U[]}      ≈⟨ MonProp.coherence-inv₃ ⟩
    ρ⇐ {U[]}      ≈⟨ ≈-Term-sym idʳ ⟩
    ρ⇐ ∘ id       ∎
  uff-nil-from (x ∷ xs) = begin
    α⇐ ∘ (id {Var x} ⊗₁ _≅_.from (unflatten-++-≅ xs []))
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (uff-nil-from xs) ⟩
    α⇐ ∘ (id {Var x} ⊗₁ (ρ⇐ ∘ dsub xs))
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    α⇐ ∘ ((id {Var x} ∘ id) ⊗₁ (ρ⇐ ∘ dsub xs))
      ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
    α⇐ ∘ ((id {Var x} ⊗₁ ρ⇐) ∘ (id {Var x} ⊗₁ dsub xs))
      ≈⟨ ≈-Term-sym assoc ⟩
    (α⇐ ∘ (id {Var x} ⊗₁ ρ⇐)) ∘ (id {Var x} ⊗₁ dsub xs)
      ≈⟨ ∘-resp-≈ MonProp.coherence-inv₂ (dsub-cons x xs) ⟩
    ρ⇐ ∘ dsub (x ∷ xs)
      ∎

  -- `≅.to (unflatten-++-≅ xs []) ≈Term csub xs ∘ ρ⇒` (the `.to` mirror).
  --   * `[]`:  `to (≅.sym unitorˡ) = λ⇒ ≈Term ρ⇒` (Kelly), `csub [] = id`.
  --   * `x∷xs`: `to = (id ⊗₁ to-IH) ∘ α⇒`; slide via `coherence₂`
  --            (`(id ⊗₁ ρ⇒) ∘ α⇒ ≈ ρ⇒`) + `csub-cons`.
  uff-nil-to
    : ∀ (xs : List X)
    → _≅_.to (unflatten-++-≅ xs []) ≈Term csub xs ∘ ρ⇒
  uff-nil-to [] = begin
    λ⇒ {U[]}      ≈⟨ MonProp.coherence₃ ⟩
    ρ⇒ {U[]}      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ ρ⇒       ∎
  uff-nil-to (x ∷ xs) = begin
    (id {Var x} ⊗₁ _≅_.to (unflatten-++-≅ xs [])) ∘ α⇒
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (uff-nil-to xs) ⟩∘⟨refl ⟩
    (id {Var x} ⊗₁ (csub xs ∘ ρ⇒)) ∘ α⇒
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩∘⟨refl ⟩
    ((id {Var x} ∘ id) ⊗₁ (csub xs ∘ ρ⇒)) ∘ α⇒
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    ((id {Var x} ⊗₁ csub xs) ∘ (id {Var x} ⊗₁ ρ⇒)) ∘ α⇒
      ≈⟨ assoc ⟩
    (id {Var x} ⊗₁ csub xs) ∘ ((id {Var x} ⊗₁ ρ⇒) ∘ α⇒)
      ≈⟨ ∘-resp-≈ (csub-cons x xs) MonProp.coherence₂ ⟩
    csub (x ∷ xs) ∘ ρ⇒
      ∎

  -- A `subst`-`id`-conjugation peels to a `subst₂`.  `csub`/`dsub` are the
  -- two conjugators; conjugating `G` by them = `subst₂ HomTerm` over the
  -- `++-identityʳ` casts (reversed on the domain side).
  -- A generic conjugation peeling.  `dd`/`cc` are the cast SOURCES (here
  -- `eiL ++ []` / `eoL ++ []`); `pi : dd ≡ eiL`, `po : cc ≡ eoL` are the
  -- `++-identityʳ` proofs.  The two `subst`-`id` conjugators collapse the
  -- composite to a single `subst₂` over `sym pi`/`sym po`.
  conj-peel
    : ∀ {eiL eoL dd cc : List X} (pi : dd ≡ eiL) (po : cc ≡ eoL)
        (G : HomTerm (unflatten eiL) (unflatten eoL))
    → subst (λ z → HomTerm (unflatten z) (unflatten cc)) po id
        ∘ G
        ∘ subst (λ z → HomTerm (unflatten dd) (unflatten z)) pi id
      ≈Term subst₂ HomTerm (cong unflatten (sym pi)) (cong unflatten (sym po)) G
  conj-peel refl refl G = begin
    id ∘ G ∘ id   ≈⟨ idˡ ⟩
    G ∘ id        ≈⟨ idʳ ⟩
    G             ∎

  conj-to-subst₂
    : ∀ {eiL eoL : List X} (G : HomTerm (unflatten eiL) (unflatten eoL))
    → csub eoL ∘ G ∘ dsub eiL
      ≈Term subst₂ HomTerm
              (cong unflatten (sym (++-identityʳ eiL)))
              (cong unflatten (sym (++-identityʳ eoL)))
              G
  conj-to-subst₂ {eiL} {eoL} G =
    conj-peel (++-identityʳ eiL) (++-identityʳ eoL) G

  -- ### `nil-frame` — the empty-residual box collapse.
  nil-frame
    : ∀ {eiL eoL : List X} (G : HomTerm (unflatten eiL) (unflatten eoL))
    → _≅_.to (unflatten-++-≅ eoL []) ∘ (G ⊗₁ id {U[]}) ∘ _≅_.from (unflatten-++-≅ eiL [])
      ≈Term subst₂ HomTerm
              (cong unflatten (sym (++-identityʳ eiL)))
              (cong unflatten (sym (++-identityʳ eoL)))
              G
  nil-frame {eiL} {eoL} G = begin
    _≅_.to (unflatten-++-≅ eoL []) ∘ (G ⊗₁ id {U[]}) ∘ _≅_.from (unflatten-++-≅ eiL [])
      ≈⟨ ∘-resp-≈ (uff-nil-to eoL) (refl⟩∘⟨ uff-nil-from eiL) ⟩
    (csub eoL ∘ ρ⇒) ∘ (G ⊗₁ id {U[]}) ∘ (ρ⇐ ∘ dsub eiL)
      ≈⟨ assoc ⟩
    csub eoL ∘ (ρ⇒ ∘ (G ⊗₁ id {U[]}) ∘ (ρ⇐ ∘ dsub eiL))
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    csub eoL ∘ ((ρ⇒ ∘ (G ⊗₁ id {U[]})) ∘ (ρ⇐ ∘ dsub eiL))
      ≈⟨ refl⟩∘⟨ (ρ⇒∘f⊗id≈f∘ρ⇒ ⟩∘⟨refl) ⟩
    csub eoL ∘ ((G ∘ ρ⇒) ∘ (ρ⇐ ∘ dsub eiL))
      ≈⟨ refl⟩∘⟨ assoc ⟩
    csub eoL ∘ (G ∘ (ρ⇒ ∘ (ρ⇐ ∘ dsub eiL)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    csub eoL ∘ (G ∘ ((ρ⇒ ∘ ρ⇐) ∘ dsub eiL))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (ρ⇒∘ρ⇐≈id ⟩∘⟨refl) ⟩
    csub eoL ∘ (G ∘ (id ∘ dsub eiL))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
    csub eoL ∘ G ∘ dsub eiL
      ≈⟨ conj-to-subst₂ G ⟩
    subst₂ HomTerm (cong unflatten (sym (++-identityʳ eiL))) (cong unflatten (sym (++-identityʳ eoL))) G
      ∎

  ------------------------------------------------------------------------
  -- ## Permute / subst₂ plumbing for the cap-collapse (cloned idioms).

  -- `subst₂ HomTerm` distributes over `∘` (= `FireMidEquivariant.subst₂-∘-distrib`).
  subst₂-∘-distrib
    : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
        (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
        (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
        (h : HomTerm (unflatten As₁) (unflatten Bs₁))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ h)
      ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
        ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) h
  subst₂-∘-distrib refl refl refl _ _ = refl

  -- `subst₂` on a `permute-via-vlab`, with block-frames of the form
  -- `cong (map vlab) a`, pushes onto the underlying `↭` (= `FireMidEquivariant`
  -- `permute-subst₂` specialised to `permute-via-vlab`).
  pvl-subst₂
    : ∀ {n} (vlab : Fin n → X) {xs xs' ys ys' : List (Fin n)}
        (a : xs ≡ xs') (b : ys ≡ ys') (r : xs Perm.↭ ys)
    → subst₂ HomTerm (cong unflatten (cong (map vlab) a))
                     (cong unflatten (cong (map vlab) b))
                     (permute-via-vlab vlab r)
      ≡ permute-via-vlab vlab (subst₂ Perm._↭_ a b r)
  pvl-subst₂ vlab refl refl r = refl

  -- `permute-via-vlab vlab ↭-refl ≈Term id` (`map⁺ f refl = refl`,
  -- `permute refl = id` — both definitional).
  pvl-refl
    : ∀ {n} (vlab : Fin n → X) (xs : List (Fin n))
    → permute-via-vlab vlab (Perm.↭-refl {x = xs}) ≈Term id
  pvl-refl vlab xs = ≈-Term-refl

  ------------------------------------------------------------------------
  -- ## `subst₂` cod/dom-`trans` split (cloned from `DecodeRoundtrip`,
  -- `--with-K`; TRUE for all instances).  Used to reduce `decode (α⇒/α⇐)`
  -- to the `++-assoc`-transport of `decode (id {(A ⊗₀ B) ⊗₀ C})`.

  -- A `subst₂` whose cod equation factors as `trans q r` splits as the
  -- outer `r`-transport of the inner `q`-transport.
  subst₂-cod-trans
    : ∀ {as as' bs bs' bs'' : List X}
        (p : as ≡ as') (q : bs ≡ bs') (r : bs' ≡ bs'')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten (trans q r)) x
      ≡ subst₂ HomTerm refl (cong unflatten r)
               (subst₂ HomTerm (cong unflatten p) (cong unflatten q) x)
  subst₂-cod-trans refl refl refl x = refl

  -- Symmetric: a `subst₂` whose dom equation factors as `trans q r`.
  subst₂-dom-trans
    : ∀ {as as' as'' bs bs' : List X}
        (q : as ≡ as') (r : as' ≡ as'') (p : bs ≡ bs')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten (trans q r)) (cong unflatten p) x
      ≡ subst₂ HomTerm (cong unflatten r) refl
               (subst₂ HomTerm (cong unflatten q) (cong unflatten p) x)
  subst₂-dom-trans refl refl refl x = refl

  -- The complete constructive `bridge`-form for `α⇒` at EVERY object `A`:
  -- `bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list (flatten A)(flatten B)(flatten C)`
  -- via the postulate-free well-founded worker in `BridgeAlphaFormCompound`.
  bridge-α⇒-form-full
    : ∀ A B C → bridge (α⇒ {A} {B} {C})
              ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)
  bridge-α⇒-form-full A B C = BAFC.Worker.work A B C (<-wellFounded _)

--------------------------------------------------------------------------------
-- ## Algorithm extraction (sig-level).
--
-- `decode-attempt-extract` now lives in the shared leaf `HomTermTransport`
-- (imported at the top of this module).

--------------------------------------------------------------------------------
-- ## Single-edge `process-all-edges` reduction (for `hGen g`).
--
-- `hGen g` has `nE = 1`, so `range 1 = zero ∷ []`; the single edge fires
-- (its `ein` = `dom` = `L`, so `extract-prefix L L` succeeds via
-- `extract-prefix-self` with empty residual).  `process-all-edges` collapses
-- to `id ∘ (fire-mid zero [] ∘ permute-via-vlab vlab perm-self)`.

module _ {A B : ObjTerm} (g : mor A B) where
  private
    H : Hypergraph FlatGen
    H = hGen g
    module H = Hypergraph H

  -- The self-prefix permutation `dom ↭ ein zero ++ []` (= `L ↭ L ++ []`).
  agen-self-perm : H.dom Perm.↭ H.ein zero ++ []
  agen-self-perm = proj₁ (extract-prefix-self H.dom)

  agen-self-eq : extract-prefix (H.ein zero) H.dom ≡ just ([] , agen-self-perm)
  agen-self-eq = proj₂ (extract-prefix-self H.dom)

  -- `edge-step H dom zero` IS the FIRE branch with empty residual.
  agen-edge-step
    : edge-step H H.dom zero
      ≡ (H.eout zero ++ [] , fire-term H zero H.dom [] agen-self-perm)
  agen-edge-step = edge-step-sound H (fireR [] agen-self-perm agen-self-eq)

  -- The full `process-all-edges` pair reduces (the `range 1 = zero ∷ []`
  -- single-edge walk: one FIRE edge, then the empty `process-edges []`
  -- prepends an `id`).  Stated as a Σ-pair equality so both the final
  -- stack AND the term land in one `rewrite agen-edge-step`.
  agen-process-pair
    : process-all-edges H H.dom
      ≡ ( H.eout zero ++ []
        , id ∘ fire-term H zero H.dom [] agen-self-perm )
  agen-process-pair rewrite agen-edge-step = refl

  -- The single edge's label is the `(sym (domL-hGen g))/(sym (codL-hGen g))`-
  -- transport of the literal `flat g` (definitional — `hGen`'s internal
  -- `lem-in`/`lem-out` are `sym (domL-hGen g)` / `sym (codL-hGen g)`).
  agen-elab-eq
    : H.elab zero
      ≡ subst₂ FlatGen (sym (domL-hGen g)) (sym (codL-hGen g)) (FlatGen.flat g)
  agen-elab-eq = refl

  -- The `box-of (flatten A)(flatten B) [] (flat g)`, reframed onto the
  -- `hGen` vlab-blocks `map vlab L`/`map vlab R` via `box-of-cong`.
  agen-box-cong
    : subst₂ HomTerm
        (cong unflatten (cong₂ _++_ (sym (domL-hGen g)) refl))
        (cong unflatten (cong₂ _++_ (sym (codL-hGen g)) refl))
        (box-of (flatten A) (flatten B) [] (FlatGen.flat g))
      ≡ box-of (map H.vlab (H.ein zero)) (map H.vlab (H.eout zero)) []
               (H.elab zero)
  agen-box-cong =
    box-of-cong (sym (domL-hGen g)) (sym (codL-hGen g)) refl
                (FlatGen.flat g) (H.elab zero) (sym agen-elab-eq)

--------------------------------------------------------------------------------
-- ## The main assembly.

module _
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (Kf : FaithfulnessResidual)
  where

  decode-σ-collapse
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)
  decode-σ-collapse {A} {B} ⦃ v≤v ⦄ = goal
    where
      σAB : HomTerm (A ⊗₀ B) (B ⊗₀ A)
      σAB = σ {A = A} {B = B}

      H : Hypergraph FlatGen
      H = hSwap A B
      module H = Hypergraph H

      -- The two front blocks (vertex-index lists).
      nA nB : ℕ
      nA = length (flatten A)
      nB = length (flatten B)
      L R : List (Fin (nA + nB))
      L = map (_↑ˡ nB) (range nA)
      R = map (nA ↑ʳ_) (range nB)

      -- `H.dom = L ++ R`, `H.cod = R ++ L`, `H.nE = 0`, `H.vlab = vlab-c`.
      vlab-c : Fin (nA + nB) → X
      vlab-c = H.vlab

      -- `vlab-c` resolves the two front blocks to `flatten A` / `flatten B`
      -- (the `lem-L` / `lem-R` of `domL-hSwap`, reconstructed here so they
      -- are usable in the frame reconciliation below).
      vlab-inL : ∀ (i : Fin nA) → vlab-c (i ↑ˡ nB) ≡ lookup (flatten A) i
      vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ˡ nA i nB)
      vlab-inR : ∀ (i : Fin nB) → vlab-c (nA ↑ʳ i) ≡ lookup (flatten B) i
      vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ʳ nA nB i)
      lem-L : map vlab-c L ≡ flatten A
      lem-L = trans (sym (map-∘ (range nA)))
                    (trans (map-cong vlab-inL (range nA)) (map-lookup-range (flatten A)))
      lem-R : map vlab-c R ≡ flatten B
      lem-R = trans (sym (map-∘ (range nB)))
                    (trans (map-cong vlab-inR (range nB)) (map-lookup-range (flatten B)))

      -- Extract the algorithm output of `decode-attempt-Linear σ`.
      ext : Σ[ perm ∈ proj₁ (process-all-edges H H.dom) Perm.↭ H.cod ]
              proj₁ (decode-attempt-Linear σAB)
              ≡ permute-via-vlab vlab-c perm
                  ∘ proj₂ (process-all-edges H H.dom)
      ext = decode-attempt-extract H
              (proj₁ (decode-attempt-Linear σAB))
              (proj₂ (decode-attempt-Linear σAB))

      perm-alg : proj₁ (process-all-edges H H.dom) Perm.↭ H.cod
      perm-alg = proj₁ ext

      pvl-c : {xs ys : List (Fin (nA + nB))}
            → xs Perm.↭ ys
            → HomTerm (unflatten (map vlab-c xs)) (unflatten (map vlab-c ys))
      pvl-c = permute-via-vlab vlab-c

      -- Boundary equations for `decode`.
      domEq : domL H ≡ flatten A ++ flatten B
      domEq = domL-hSwap A B
      codEq : codL H ≡ flatten B ++ flatten A
      codEq = codL-hSwap A B

      -- (1) `decode σAB` reduces to the boundary-substituted final permute,
      -- composed with the (trivial, nE = 0) `process-term = id`.
      step-decode
        : decode σAB
          ≈Term subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
                  (pvl-c perm-alg ∘ id)
      step-decode =
        subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq)
          (≡⇒≈Term (proj₂ ext))

      -- The canonical append-commutativity permutation (the one the
      -- braiding realises).
      comm-LR : L ++ R Perm.↭ R ++ L
      comm-LR = PermProp.++-comm L R

      -- `H.cod = R ++ L` is `Unique` (hSwap codomain interface).
      cod-uniq : Unique (R ++ L)
      cod-uniq = hSwap-cod-Unique A B

      -- (2) KEYSTONE: any two `↭`'s into the SAME `Unique` codomain give
      -- equal `permute-via-vlab` (faithfulness via `K`).  Collapse the
      -- algorithm's `perm-alg` onto the canonical `comm-LR`.
      step-keystone : pvl-c perm-alg ≈Term pvl-c comm-LR
      step-keystone =
        permute-via-vlab-≈Term-coherence-K Kf vlab-c cod-uniq perm-alg comm-LR

      -- BNV block-frame abbreviations at `vlab-c`.
      Aof : List (Fin (nA + nB)) → ObjTerm
      Aof = BNV.Aof vlab-c

      ufc : (As Bs : List (Fin (nA + nB)))
          → unflatten (map vlab-c (As ++ Bs)) ≅ Aof As ⊗₀ Aof Bs
      ufc = BNV.uf++ vlab-c

      -- (3) `BNV.σ-block-comm` (reversed): the canonical `pvl (++-comm L R)`
      -- IS the block-braiding `σ {Aof L}{Aof R}` conjugated by the
      -- `unflatten-++-≅` rebrackets.
      step-block
        : pvl-c comm-LR
          ≈Term _≅_.to (ufc R L) ∘ (σ {Aof L} {Aof R}) ∘ _≅_.from (ufc L R)
      step-block = ≈-Term-sym (BNV.σ-block-comm vlab-c L R)

      -- The `ufc` boundary `map-++` equalities.
      mLR : map vlab-c (L ++ R) ≡ map vlab-c L ++ map vlab-c R
      mLR = map-++ vlab-c L R
      mRL : map vlab-c (R ++ L) ≡ map vlab-c R ++ map vlab-c L
      mRL = map-++ vlab-c R L

      -- (3b) Peel the two `ufc` map-bridge `subst₂`'s out of the LHS interior,
      -- exposing `bframe (map vlab-c L)(map vlab-c R)` under a single boundary
      -- `subst₂` over `cong unflatten (sym mLR)` / `cong unflatten (sym mRL)`.
      step-peel
        : _≅_.to (ufc R L) ∘ (σ {Aof L} {Aof R}) ∘ _≅_.from (ufc L R)
          ≡ subst₂ HomTerm (cong unflatten (sym mLR)) (cong unflatten (sym mRL))
              (bframe (map vlab-c L) (map vlab-c R))
      step-peel =
        trans
          (cong₂ (λ x y → x ∘ ((σ {Aof L} {Aof R}) ∘ y))
            (BNB.to-subst₂-≅ (cong unflatten (sym mRL))
              (unflatten-++-≅ (map vlab-c R) (map vlab-c L)))
            (BNB.from-subst₂-≅ (cong unflatten (sym mLR))
              (unflatten-++-≅ (map vlab-c L) (map vlab-c R))))
          (peel-∘-substs (cong unflatten (sym mLR)) (cong unflatten (sym mRL))
            (_≅_.to (unflatten-++-≅ (map vlab-c R) (map vlab-c L)))
            (σ {Aof L} {Aof R})
            (_≅_.from (unflatten-++-≅ (map vlab-c L) (map vlab-c R))))

      ------------------------------------------------------------------
      -- (4) Frame reconciliation.  The `unflatten-flatten-≈` framing of the
      -- bridge unfolds, via braiding-naturality + the unit iso laws, to the
      -- SAME structural block-braid as the LHS but at the `flatten`-blocks.

      -- The per-side `unflatten-flatten-≈` isos.
      uffA = unflatten-flatten-≈ A
      uffB = unflatten-flatten-≈ B

      -- The two `unflatten-++-≅` block isos at the `flatten`-blocks.
      uff++AB : unflatten (flatten A) ⊗₀ unflatten (flatten B)
                ≅ unflatten (flatten A ++ flatten B)
      uff++AB = ≅.sym (unflatten-++-≅ (flatten A) (flatten B))
      uff++BA : unflatten (flatten B) ⊗₀ unflatten (flatten A)
                ≅ unflatten (flatten B ++ flatten A)
      uff++BA = ≅.sym (unflatten-++-≅ (flatten B) (flatten A))

      -- `bridge σAB` reduces (definitionally) to:
      --   `(≅.to uff++BA ∘ (from uffB ⊗₁ from uffA))
      --      ∘ σ {A}{B}
      --      ∘ ((to uffA ⊗₁ to uffB) ∘ ≅.from uff++AB)`.
      step-bridge
        : bridge σAB
          ≈Term _≅_.from uff++BA
                ∘ (σ {unflatten (flatten A)} {unflatten (flatten B)})
                ∘ _≅_.to uff++AB
      step-bridge = begin
        (_≅_.from uff++BA ∘ (_≅_.from uffB ⊗₁ _≅_.from uffA))
          ∘ σ {A} {B}
          ∘ ((_≅_.to uffA ⊗₁ _≅_.to uffB) ∘ _≅_.to uff++AB)
          ≈⟨ assoc ⟩
        _≅_.from uff++BA
          ∘ ((_≅_.from uffB ⊗₁ _≅_.from uffA)
          ∘ (σ {A} {B}
          ∘ ((_≅_.to uffA ⊗₁ _≅_.to uffB) ∘ _≅_.to uff++AB)))
          ≈⟨ refl⟩∘⟨ mid ⟩
        _≅_.from uff++BA
          ∘ (σ {unflatten (flatten A)} {unflatten (flatten B)} ∘ _≅_.to uff++AB)
          ∎
        where
          -- Slide `σ {A}{B}` past `(to uffA ⊗ to uffB)` by braiding
          -- naturality, then cancel the `from·to` units; the residual is
          -- `σ` on the unflattened blocks framed by `to uff++AB`.
          mid : (_≅_.from uffB ⊗₁ _≅_.from uffA)
                  ∘ (σ {A} {B}
                  ∘ ((_≅_.to uffA ⊗₁ _≅_.to uffB) ∘ _≅_.to uff++AB))
                ≈Term σ {unflatten (flatten A)} {unflatten (flatten B)}
                  ∘ _≅_.to uff++AB
          mid = begin
            (_≅_.from uffB ⊗₁ _≅_.from uffA)
              ∘ (σ {A} {B}
              ∘ ((_≅_.to uffA ⊗₁ _≅_.to uffB) ∘ _≅_.to uff++AB))
              ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
            (_≅_.from uffB ⊗₁ _≅_.from uffA)
              ∘ ((σ {A} {B} ∘ (_≅_.to uffA ⊗₁ _≅_.to uffB)) ∘ _≅_.to uff++AB)
              ≈⟨ refl⟩∘⟨ (σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl) ⟩
            (_≅_.from uffB ⊗₁ _≅_.from uffA)
              ∘ (((_≅_.to uffB ⊗₁ _≅_.to uffA)
                  ∘ σ {unflatten (flatten A)} {unflatten (flatten B)})
                  ∘ _≅_.to uff++AB)
              ≈⟨ ≈-Term-sym assoc ⟩
            ((_≅_.from uffB ⊗₁ _≅_.from uffA)
              ∘ ((_≅_.to uffB ⊗₁ _≅_.to uffA)
                  ∘ σ {unflatten (flatten A)} {unflatten (flatten B)}))
              ∘ _≅_.to uff++AB
              ≈⟨ (≈-Term-sym assoc) ⟩∘⟨refl ⟩
            (((_≅_.from uffB ⊗₁ _≅_.from uffA)
              ∘ (_≅_.to uffB ⊗₁ _≅_.to uffA))
              ∘ σ {unflatten (flatten A)} {unflatten (flatten B)})
              ∘ _≅_.to uff++AB
              ≈⟨ (units ⟩∘⟨refl) ⟩∘⟨refl ⟩
            (id ∘ σ {unflatten (flatten A)} {unflatten (flatten B)})
              ∘ _≅_.to uff++AB
              ≈⟨ idˡ ⟩∘⟨refl ⟩
            σ {unflatten (flatten A)} {unflatten (flatten B)} ∘ _≅_.to uff++AB
              ∎
            where
              units : (_≅_.from uffB ⊗₁ _≅_.from uffA)
                        ∘ (_≅_.to uffB ⊗₁ _≅_.to uffA)
                      ≈Term id
              units = begin
                (_≅_.from uffB ⊗₁ _≅_.from uffA)
                  ∘ (_≅_.to uffB ⊗₁ _≅_.to uffA)
                  ≈⟨ ⊗-∘-dist ⟨
                (_≅_.from uffB ∘ _≅_.to uffB) ⊗₁ (_≅_.from uffA ∘ _≅_.to uffA)
                  ≈⟨ ⊗-resp-≈ (_≅_.isoʳ uffB) (_≅_.isoʳ uffA) ⟩
                id ⊗₁ id
                  ≈⟨ id⊗id≈id ⟩
                id
                  ∎

      -- Compose the boundary `subst₂` of `decode` with the peeled `subst₂`
      -- of `step-peel`, collapse the two-step boundary to the single
      -- `lem-L`/`lem-R`-boundary under `objUIP`, then fire `bframe-subst₂`.
      step-frame
        : subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
            (subst₂ HomTerm (cong unflatten (sym mLR)) (cong unflatten (sym mRL))
              (bframe (map vlab-c L) (map vlab-c R)))
          ≈Term bframe (flatten A) (flatten B)
      step-frame = begin
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (subst₂ HomTerm (cong unflatten (sym mLR)) (cong unflatten (sym mRL))
            (bframe (map vlab-c L) (map vlab-c R)))
          ≈⟨ ≡⇒≈Term (subst₂-HomTerm-∘
                        (cong unflatten (sym mLR)) (cong unflatten domEq)
                        (cong unflatten (sym mRL)) (cong unflatten codEq)
                        (bframe (map vlab-c L) (map vlab-c R))) ⟩
        subst₂ HomTerm (trans (cong unflatten (sym mLR)) (cong unflatten domEq))
                       (trans (cong unflatten (sym mRL)) (cong unflatten codEq))
          (bframe (map vlab-c L) (map vlab-c R))
          ≈⟨ subst₂-HomTerm-irrel objUIP
               (trans (cong unflatten (sym mLR)) (cong unflatten domEq))
               (cong unflatten (cong₂ _++_ lem-L lem-R))
               (trans (cong unflatten (sym mRL)) (cong unflatten codEq))
               (cong unflatten (cong₂ _++_ lem-R lem-L))
               (bframe (map vlab-c L) (map vlab-c R)) ⟩
        subst₂ HomTerm (cong unflatten (cong₂ _++_ lem-L lem-R))
                       (cong unflatten (cong₂ _++_ lem-R lem-L))
          (bframe (map vlab-c L) (map vlab-c R))
          ≈⟨ ≡⇒≈Term (bframe-subst₂ lem-L lem-R) ⟩
        bframe (flatten A) (flatten B)
          ∎

      goal : decode σAB ≈Term bridge σAB
      goal = begin
        decode σAB
          ≈⟨ step-decode ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (pvl-c perm-alg ∘ id)
          ≈⟨ subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq) idʳ ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (pvl-c perm-alg)
          ≈⟨ subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq)
               (≈-Term-trans step-keystone step-block) ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (_≅_.to (ufc R L) ∘ (σ {Aof L} {Aof R}) ∘ _≅_.from (ufc L R))
          ≈⟨ subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq)
               (≡⇒≈Term step-peel) ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (subst₂ HomTerm (cong unflatten (sym mLR)) (cong unflatten (sym mRL))
            (bframe (map vlab-c L) (map vlab-c R)))
          ≈⟨ step-frame ⟩
        bframe (flatten A) (flatten B)
          ≈⟨ step-bridge ⟨
        bridge σAB
          ∎

  --------------------------------------------------------------------------
  -- ## `decode-Agen-collapse` (the Agen / single-edge case).
  --
  -- `decode (Agen g)` runs `hGen g` (one FIRE edge, no residual).  Its
  -- algorithmic interior is `pvl perm-alg ∘ (id ∘ (fire-mid zero [] ∘ pvl
  -- perm-self))`.  The empty-residual box `fire-mid zero []` collapses
  -- (via `box-of-cong` to the `flatten`-blocks + `nil-frame`) to the bare
  -- `Agen-edge-aux (flat g)`; the two `↭`-permutes collapse to the boundary
  -- coherence by the keystone (Unique codomains `L`/`R`).  Everything is
  -- reconciled with `bridge (Agen g) = Agen-edge-aux (flat g)` under
  -- `objUIP`.

  decode-Agen-collapse
    : ∀ {A B} (g : mor A B) → decode (Agen g) ≈Term bridge (Agen g)
  decode-Agen-collapse {A} {B} g = goal
    where
      H : Hypergraph FlatGen
      H = hGen g
      module H = Hypergraph H

      vlab-c : Fin H.nV → X
      vlab-c = H.vlab

      pvl-c : {xs ys : List (Fin H.nV)}
            → xs Perm.↭ ys
            → HomTerm (unflatten (map vlab-c xs)) (unflatten (map vlab-c ys))
      pvl-c = permute-via-vlab vlab-c

      Lblk Rblk : List (Fin H.nV)
      Lblk = H.ein zero
      Rblk = H.eout zero

      -- Boundary equations for `decode`.
      domEq : domL H ≡ flatten A
      domEq = domL-hGen g
      codEq : codL H ≡ flatten B
      codEq = codL-hGen g

      -- The single-edge process reduction (from the upstream helper).
      pp : process-all-edges H H.dom
           ≡ ( Rblk ++ []
             , id ∘ (fire-mid H zero []
                     ∘ permute-via-vlab vlab-c (agen-self-perm g)) )
      pp = agen-process-pair g

      perm-self : H.dom Perm.↭ Lblk ++ []
      perm-self = agen-self-perm g

      -- (1) `decode (Agen g)` exposes its boundary-substituted interior.
      ext : Σ[ perm ∈ proj₁ (process-all-edges H H.dom) Perm.↭ H.cod ]
              proj₁ (decode-attempt-Linear (Agen g))
              ≡ permute-via-vlab vlab-c perm
                  ∘ proj₂ (process-all-edges H H.dom)
      ext = decode-attempt-extract H
              (proj₁ (decode-attempt-Linear (Agen g)))
              (proj₂ (decode-attempt-Linear (Agen g)))

      perm-alg : proj₁ (process-all-edges H H.dom) Perm.↭ H.cod
      perm-alg = proj₁ ext

      step-decode
        : decode (Agen g)
          ≈Term subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
                  (permute-via-vlab vlab-c perm-alg
                    ∘ proj₂ (process-all-edges H H.dom))
      step-decode =
        subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq)
          (≡⇒≈Term (proj₂ ext))

      -- `Agen-edge-aux` framed onto the `flatten`-blocks (= the RHS of
      -- `interior`; equals `bridge (Agen g)` after the outer collapse).
      BoxCore : HomTerm (unflatten (map vlab-c Lblk)) (unflatten (map vlab-c Rblk))
      BoxCore = subst₂ HomTerm (cong unflatten (sym domEq)) (cong unflatten (sym codEq))
                       (Agen-edge-aux (FlatGen.flat g))

      -- `Agen-edge-aux`-naturality under `subst₂ FlatGen` (local clone).
      subst₂-Agen-edge-aux-nat
        : ∀ {ins₁ ins₂ outs₁ outs₂ : List X}
            (p : ins₁ ≡ ins₂) (q : outs₁ ≡ outs₂) (x : FlatGen ins₁ outs₁)
        → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (Agen-edge-aux x)
          ≡ Agen-edge-aux (subst₂ FlatGen p q x)
      subst₂-Agen-edge-aux-nat refl refl _ = refl

      -- The `_++ []` block-frames (list level).
      lf : map vlab-c Lblk ≡ map vlab-c (Lblk ++ [])
      lf = cong (map vlab-c) (sym (++-identityʳ Lblk))
      rf : map vlab-c Rblk ≡ map vlab-c (Rblk ++ [])
      rf = cong (map vlab-c) (sym (++-identityʳ Rblk))

      -- (2) The FIRE box collapses: `box-of-cong` reframes the box onto the
      -- `flatten`-blocks, `nil-frame` discharges the empty residual, and
      -- `subst₂-Agen-edge-aux-nat` pushes the `(sym domEq)/(sym codEq)`
      -- transport onto `Agen-edge-aux`.  All boundary `subst₂` merge under
      -- `objUIP` into the single `_++ []` block-frame.
      fire-eq
        : fire-mid H zero []
          ≈Term subst₂ HomTerm (cong unflatten lf) (cong unflatten rf) BoxCore
      fire-eq = begin
        -- `fire-mid H zero []` (definitionally the `map-++ · []`-framed box).
        subst₂ HomTerm
          (cong unflatten (sym (map-++ vlab-c Lblk [])))
          (cong unflatten (sym (map-++ vlab-c Rblk [])))
          (box-of (map vlab-c Lblk) (map vlab-c Rblk) [] (H.elab zero))
          ≈⟨ subst₂-resp-≈Term _ _ box-collapse ⟩
        subst₂ HomTerm
          (cong unflatten (sym (map-++ vlab-c Lblk [])))
          (cong unflatten (sym (map-++ vlab-c Rblk [])))
          (subst₂ HomTerm bcd bcc
            (subst₂ HomTerm nfd nfc (Agen-edge-aux (FlatGen.flat g))))
          ≈⟨ subst₂-resp-≈Term
                (cong unflatten (sym (map-++ vlab-c Lblk [])))
                (cong unflatten (sym (map-++ vlab-c Rblk [])))
                (≡⇒≈Term (subst₂-HomTerm-∘ nfd bcd nfc bcc
                            (Agen-edge-aux (FlatGen.flat g)))) ⟩
        subst₂ HomTerm
          (cong unflatten (sym (map-++ vlab-c Lblk [])))
          (cong unflatten (sym (map-++ vlab-c Rblk [])))
          (subst₂ HomTerm (trans nfd bcd) (trans nfc bcc)
            (Agen-edge-aux (FlatGen.flat g)))
          ≈⟨ ≡⇒≈Term (subst₂-HomTerm-∘ (trans nfd bcd)
                        (cong unflatten (sym (map-++ vlab-c Lblk [])))
                        (trans nfc bcc)
                        (cong unflatten (sym (map-++ vlab-c Rblk [])))
                        (Agen-edge-aux (FlatGen.flat g))) ⟩
        subst₂ HomTerm
          (trans (trans nfd bcd) (cong unflatten (sym (map-++ vlab-c Lblk []))))
          (trans (trans nfc bcc) (cong unflatten (sym (map-++ vlab-c Rblk []))))
          (Agen-edge-aux (FlatGen.flat g))
          ≈⟨ subst₂-HomTerm-irrel objUIP
               (trans (trans nfd bcd) (cong unflatten (sym (map-++ vlab-c Lblk []))))
               (trans (cong unflatten (sym domEq)) (cong unflatten lf))
               (trans (trans nfc bcc) (cong unflatten (sym (map-++ vlab-c Rblk []))))
               (trans (cong unflatten (sym codEq)) (cong unflatten rf))
               (Agen-edge-aux (FlatGen.flat g)) ⟩
        subst₂ HomTerm
          (trans (cong unflatten (sym domEq)) (cong unflatten lf))
          (trans (cong unflatten (sym codEq)) (cong unflatten rf))
          (Agen-edge-aux (FlatGen.flat g))
          ≈⟨ ≡⇒≈Term (sym (subst₂-HomTerm-∘
                        (cong unflatten (sym domEq)) (cong unflatten lf)
                        (cong unflatten (sym codEq)) (cong unflatten rf)
                        (Agen-edge-aux (FlatGen.flat g)))) ⟩
        subst₂ HomTerm (cong unflatten lf) (cong unflatten rf) BoxCore
          ∎
        where
          bcd = cong unflatten (cong₂ _++_ (sym domEq) refl)
          bcc = cong unflatten (cong₂ _++_ (sym codEq) refl)
          nfd = cong unflatten (sym (++-identityʳ (flatten A)))
          nfc = cong unflatten (sym (++-identityʳ (flatten B)))

          box-collapse
            : box-of (map vlab-c Lblk) (map vlab-c Rblk) [] (H.elab zero)
              ≈Term subst₂ HomTerm bcd bcc
                      (subst₂ HomTerm nfd nfc (Agen-edge-aux (FlatGen.flat g)))
          box-collapse = begin
            box-of (map vlab-c Lblk) (map vlab-c Rblk) [] (H.elab zero)
              ≈⟨ ≡⇒≈Term (sym (agen-box-cong g)) ⟩
            subst₂ HomTerm bcd bcc (box-of (flatten A) (flatten B) [] (FlatGen.flat g))
              ≈⟨ subst₂-resp-≈Term bcd bcc (nil-frame (Agen-edge-aux (FlatGen.flat g))) ⟩
            subst₂ HomTerm bcd bcc
              (subst₂ HomTerm nfd nfc (Agen-edge-aux (FlatGen.flat g)))
              ∎

      -- The two structural permutes `pvl-c perm-self` (`Lblk ↭ Lblk ++ []`)
      -- and `pvl-c perm-alg` (`Rblk ++ [] ↭ Rblk`) collapse against the
      -- `_++ []` block-frames of `fire-eq`, by the keystone (Unique `Lblk`
      -- / `Rblk` codomains), to leave the bare `BoxCore`.
      interior
        : permute-via-vlab vlab-c perm-alg
            ∘ proj₂ (process-all-edges H H.dom)
          ≈Term BoxCore
      interior = interior-gen (process-all-edges H H.dom) perm-alg pp
        where
          -- `q-LL : Lblk ↭ Lblk` — `perm-self` with its `++ []` codomain
          -- transported back; `pvl-c q-LL ≈ id` by the keystone (Unique Lblk).
          q-LL : Lblk Perm.↭ Lblk
          q-LL = subst₂ Perm._↭_ refl (++-identityʳ Lblk) perm-self

          -- `pvl-c perm-self` re-expressed with the `lf` block-frame extracted.
          pvl-self-eq
            : permute-via-vlab vlab-c perm-self
              ≡ subst₂ HomTerm refl (cong unflatten lf)
                  (permute-via-vlab vlab-c q-LL)
          pvl-self-eq =
            trans (cong (permute-via-vlab vlab-c) self-recon)
                  (sym (pvl-subst₂ vlab-c refl (sym (++-identityʳ Lblk)) q-LL))
            where
              -- `perm-self ≡ subst₂ ↭ refl (sym (++-id Lblk)) q-LL` (the
              -- `++ []`-codomain transport round-trips).
              self-recon
                : perm-self
                  ≡ subst₂ Perm._↭_ refl (sym (++-identityʳ Lblk)) q-LL
              self-recon = lemma (++-identityʳ Lblk)
                where
                  lemma : ∀ {w} (e : Lblk ++ [] ≡ w)
                        → perm-self
                          ≡ subst₂ Perm._↭_ refl (sym e)
                              (subst₂ Perm._↭_ refl e perm-self)
                  lemma refl = refl

          interior-gen
            : (pr : Σ[ s ∈ List (Fin H.nV) ]
                      HomTerm (unflatten (map vlab-c H.dom))
                              (unflatten (map vlab-c s)))
              (pa : proj₁ pr Perm.↭ H.cod)
            → pr ≡ ( Rblk ++ []
                   , id ∘ (fire-mid H zero []
                           ∘ permute-via-vlab vlab-c perm-self) )
            → permute-via-vlab vlab-c pa ∘ proj₂ pr ≈Term BoxCore
          interior-gen _ pa refl = begin
            permute-via-vlab vlab-c pa
              ∘ (id ∘ (fire-mid H zero [] ∘ permute-via-vlab vlab-c perm-self))
              ≈⟨ refl⟩∘⟨ idˡ ⟩
            permute-via-vlab vlab-c pa
              ∘ (fire-mid H zero [] ∘ permute-via-vlab vlab-c perm-self)
              ≈⟨ refl⟩∘⟨ (fire-eq ⟩∘⟨ ≡⇒≈Term pvl-self-eq) ⟩
            permute-via-vlab vlab-c pa
              ∘ (subst₂ HomTerm (cong unflatten lf) (cong unflatten rf) BoxCore
                  ∘ subst₂ HomTerm refl (cong unflatten lf)
                      (permute-via-vlab vlab-c q-LL))
              ≈⟨ refl⟩∘⟨ ≡⇒≈Term
                   (sym (subst₂-∘-distrib refl
                          (cong (map vlab-c) (sym (++-identityʳ Lblk)))
                          (cong (map vlab-c) (sym (++-identityʳ Rblk)))
                          BoxCore (permute-via-vlab vlab-c q-LL))) ⟩
            permute-via-vlab vlab-c pa
              ∘ subst₂ HomTerm refl (cong unflatten rf)
                  (BoxCore ∘ permute-via-vlab vlab-c q-LL)
              ≈⟨ refl⟩∘⟨ subst₂-resp-≈Term refl (cong unflatten rf)
                          (refl⟩∘⟨ keystone-L) ⟩
            permute-via-vlab vlab-c pa
              ∘ subst₂ HomTerm refl (cong unflatten rf) (BoxCore ∘ id)
              ≈⟨ refl⟩∘⟨ subst₂-resp-≈Term refl (cong unflatten rf) idʳ ⟩
            permute-via-vlab vlab-c pa
              ∘ subst₂ HomTerm refl (cong unflatten rf) BoxCore
              ≈⟨ (≡⇒≈Term pvl-alg-eq) ⟩∘⟨refl ⟩
            subst₂ HomTerm (cong unflatten rf) refl (permute-via-vlab vlab-c q-RR)
              ∘ subst₂ HomTerm refl (cong unflatten rf) BoxCore
              ≈⟨ ≡⇒≈Term
                   (sym (subst₂-∘-distrib refl
                          (cong (map vlab-c) (sym (++-identityʳ Rblk)))
                          refl
                          (permute-via-vlab vlab-c q-RR) BoxCore)) ⟩
            subst₂ HomTerm refl refl (permute-via-vlab vlab-c q-RR ∘ BoxCore)
              ≈⟨ ∘-resp-≈ keystone-R ≈-Term-refl ⟩
            id ∘ BoxCore
              ≈⟨ idˡ ⟩
            BoxCore
              ∎
            where
              -- `pvl-c q-LL ≈ id` (keystone @ Unique `Lblk` + `pvl-refl`).
              keystone-L : permute-via-vlab vlab-c q-LL ≈Term id
              keystone-L = ≈-Term-trans
                (permute-via-vlab-≈Term-coherence-K Kf vlab-c
                  (hGen-dom-Unique g) q-LL Perm.↭-refl)
                (pvl-refl vlab-c Lblk)

              -- `q-RR : Rblk ↭ Rblk` — `pa` with its `++ []` domain transported
              -- back; `pvl-c q-RR ≈ id` by the keystone (Unique Rblk).
              q-RR : Rblk Perm.↭ Rblk
              q-RR = subst₂ Perm._↭_ (++-identityʳ Rblk) refl pa

              keystone-R : permute-via-vlab vlab-c q-RR ≈Term id
              keystone-R = ≈-Term-trans
                (permute-via-vlab-≈Term-coherence-K Kf vlab-c
                  (hGen-cod-Unique g) q-RR Perm.↭-refl)
                (pvl-refl vlab-c Rblk)

              -- `pvl-c pa` with the `rf` domain block-frame extracted.
              pvl-alg-eq
                : permute-via-vlab vlab-c pa
                  ≡ subst₂ HomTerm (cong unflatten rf) refl
                      (permute-via-vlab vlab-c q-RR)
              pvl-alg-eq =
                trans (cong (permute-via-vlab vlab-c) alg-recon)
                      (sym (pvl-subst₂ vlab-c (sym (++-identityʳ Rblk)) refl q-RR))
                where
                  alg-recon
                    : pa ≡ subst₂ Perm._↭_ (sym (++-identityʳ Rblk)) refl q-RR
                  alg-recon = lemma (++-identityʳ Rblk)
                    where
                      lemma : ∀ {w} (e : Rblk ++ [] ≡ w)
                            → pa ≡ subst₂ Perm._↭_ (sym e) refl
                                     (subst₂ Perm._↭_ e refl pa)
                      lemma refl = refl

      -- Reconcile the boundary loop `subst₂ domEq codEq ∘ subst₂ (sym domEq)
      -- (sym codEq)` under `objUIP` (it is the identity transport).
      step-collapse
        : subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
            (subst₂ HomTerm (cong unflatten (sym domEq)) (cong unflatten (sym codEq))
              (Agen-edge-aux (FlatGen.flat g)))
          ≈Term Agen-edge-aux (FlatGen.flat g)
      step-collapse = begin
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (subst₂ HomTerm (cong unflatten (sym domEq)) (cong unflatten (sym codEq))
            (Agen-edge-aux (FlatGen.flat g)))
          ≈⟨ ≡⇒≈Term (subst₂-HomTerm-∘
                        (cong unflatten (sym domEq)) (cong unflatten domEq)
                        (cong unflatten (sym codEq)) (cong unflatten codEq)
                        (Agen-edge-aux (FlatGen.flat g))) ⟩
        subst₂ HomTerm (trans (cong unflatten (sym domEq)) (cong unflatten domEq))
                       (trans (cong unflatten (sym codEq)) (cong unflatten codEq))
          (Agen-edge-aux (FlatGen.flat g))
          ≈⟨ subst₂-HomTerm-irrel objUIP
               (trans (cong unflatten (sym domEq)) (cong unflatten domEq)) refl
               (trans (cong unflatten (sym codEq)) (cong unflatten codEq)) refl
               (Agen-edge-aux (FlatGen.flat g)) ⟩
        Agen-edge-aux (FlatGen.flat g)
          ∎

      goal : decode (Agen g) ≈Term bridge (Agen g)
      goal = begin
        decode (Agen g)
          ≈⟨ step-decode ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (permute-via-vlab vlab-c perm-alg ∘ proj₂ (process-all-edges H H.dom))
          ≈⟨ subst₂-resp-≈Term (cong unflatten domEq) (cong unflatten codEq) interior ⟩
        subst₂ HomTerm (cong unflatten domEq) (cong unflatten codEq)
          (subst₂ HomTerm (cong unflatten (sym domEq)) (cong unflatten (sym codEq))
            (Agen-edge-aux (FlatGen.flat g)))
          ≈⟨ step-collapse ⟩
        Agen-edge-aux (FlatGen.flat g)
          ∎

  --------------------------------------------------------------------------
  -- ## `decode (id {A}) ≈Term id` (all objects).
  --
  -- The `unit`/`Var` base cases reduce definitionally; the `⊗` case uses the
  -- PROVEN ⊗-shape residual `DTS.decode-⊗-shape-inner objUIP Kf` (the SAME
  -- shape lemma the chain already threads) + the IH + the `unflatten-++-≅`
  -- iso law.  This mirrors `DecodeRoundtrip.decode-id-is-id` but consumes the
  -- proven shape lemma in place of the `decode-⊗-shape` postulate.
  decode-id-is-id : ∀ A → decode (id {A}) ≈Term id
  decode-id-is-id unit = begin
    (id ∘ id) ∘ id   ≈⟨ idʳ ⟩
    id ∘ id          ≈⟨ idˡ ⟩
    id               ∎
  decode-id-is-id (Var x) = begin
    ((id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)) ∘ id
                                      ≈⟨ idʳ ⟩
    (id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)    ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
    id ∘ ((id ⊗₁ id) ∘ id)            ≈⟨ idˡ ⟩
    (id ⊗₁ id) ∘ id                   ≈⟨ idʳ ⟩
    id ⊗₁ id                          ≈⟨ id⊗id≈id ⟩
    id                                ∎
  decode-id-is-id (A ⊗₀ B) = begin
    decode (id {A ⊗₀ B})
      ≈⟨ DTS.decode-⊗-shape-inner objUIP Kf (id {A}) (id {B}) ⟩
    cAB-to ∘ (decode (id {A}) ⊗₁ decode (id {B})) ∘ cAB-from
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (decode-id-is-id A) (decode-id-is-id B) ⟩∘⟨refl ⟩
    cAB-to ∘ (id ⊗₁ id) ∘ cAB-from
      ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
    cAB-to ∘ id ∘ cAB-from
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    cAB-to ∘ cAB-from
      ≈⟨ _≅_.isoˡ (unflatten-++-≅ (flatten A) (flatten B)) ⟩
    id
      ∎
    where
      cAB-to   = _≅_.to   (unflatten-++-≅ (flatten A) (flatten B))
      cAB-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))

  --------------------------------------------------------------------------
  -- ## `decode-α⇒-collapse` / `decode-α⇐-collapse`.
  --
  -- `⟪ α⇒ {A}{B}{C} ⟫ = hId ((A ⊗₀ B) ⊗₀ C)`, so the algorithm interior is
  -- the SAME `decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)` as `decode (id {(A⊗B)⊗C})`;
  -- the two `decode`s differ ONLY in the codomain (α⇒) / domain (α⇐) boundary
  -- equation, which factors as `trans (codL-hId …) (++-assoc …)`.  Peeling
  -- that with `subst₂-cod-trans` (mirroring the PROVEN `rho⇒-shape`) gives
  --   `decode (α⇒) ≡ subst₂ refl (cong unflatten (++-assoc …)) (decode (id …))`.
  -- Then `decode-id-is-id` collapses the interior to `id`; `subst₂-refl-cod`
  -- turns the one-sided `subst₂` into a `subst`; `α⇒-coh-list` recognises it
  -- as the canonical `α⇒-form-list`; and `bridge-α⇒-form-full` (the PROVEN,
  -- postulate-free Mac-Lane worker) reconciles with `bridge α⇒`.  α⇐ is the
  -- domain-side mirror (`subst₂-dom-trans` + `subst₂-refl-dom` + `α⇐-coh-list`
  -- + `bridge-α⇐-form` derived from α⇒ via the `α⇒/α⇐`-iso).

  decode-α⇒-collapse
    : ∀ {A B C} → decode (α⇒ {A} {B} {C}) ≈Term bridge (α⇒ {A} {B} {C})
  decode-α⇒-collapse {A} {B} {C} = begin
    decode (α⇒ {A} {B} {C})
      ≈⟨ ≡⇒≈Term (subst₂-cod-trans (domL-hId D) (codL-hId D) assoc-eq
                    (proj₁ (decode-attempt-hId D))) ⟩
    subst₂ HomTerm refl (cong unflatten assoc-eq) (decode (id {D}))
      ≈⟨ subst₂-resp-≈Term refl (cong unflatten assoc-eq) (decode-id-is-id D) ⟩
    subst₂ HomTerm refl (cong unflatten assoc-eq) (id {unflatten (flatten D)})
      ≈⟨ ≡⇒≈Term (subst₂-refl-cod assoc-eq) ⟩
    subst (λ z → HomTerm (unflatten (flatten D)) (unflatten z)) assoc-eq id
      ≈⟨ α⇒-coh-list (flatten A) (flatten B) (flatten C) ⟩
    α⇒-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ bridge-α⇒-form-full A B C ⟨
    bridge (α⇒ {A} {B} {C})
      ∎
    where
      D : ObjTerm
      D = (A ⊗₀ B) ⊗₀ C
      assoc-eq : flatten D ≡ flatten A ++ flatten B ++ flatten C
      assoc-eq = ++-assoc (flatten A) (flatten B) (flatten C)

  -- `bridge (α⇐ {A}{B}{C}) ≈Term α⇐-form-list …`, derived from
  -- `bridge-α⇒-form-full` exactly as `BridgeAlphaFormCompound.derive-⇐`
  -- (re-proven inline so we do not need that module's private helper).
  private
    bridge-resp-≈Term
      : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → bridge f ≈Term bridge g
    bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

    bridge-α⇐-form-full
      : ∀ A B C → bridge (α⇐ {A} {B} {C})
                ≈Term α⇐-form-list (flatten A) (flatten B) (flatten C)
    bridge-α⇐-form-full A B C = begin
      bridge (α⇐ {A} {B} {C})
        ≈⟨ ≈-Term-sym idʳ ⟩
      bridge (α⇐ {A} {B} {C}) ∘ id
        ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇒-α⇐-iso (flatten A) (flatten B) (flatten C)) ⟩
      bridge (α⇐ {A} {B} {C}) ∘ (αF ∘ αB)
        ≈⟨ ≈-Term-sym assoc ⟩
      (bridge (α⇐ {A} {B} {C}) ∘ αF) ∘ αB
        ≈⟨ (refl⟩∘⟨ ≈-Term-sym (bridge-α⇒-form-full A B C)) ⟩∘⟨refl ⟩
      (bridge (α⇐ {A} {B} {C}) ∘ bridge (α⇒ {A} {B} {C})) ∘ αB
        ≈⟨ ≈-Term-sym (bridge-∘ (α⇐ {A} {B} {C}) (α⇒ {A} {B} {C})) ⟩∘⟨refl ⟩
      bridge (α⇐ {A} {B} {C} ∘ α⇒ {A} {B} {C}) ∘ αB
        ≈⟨ bridge-resp-≈Term α⇐∘α⇒≈id ⟩∘⟨refl ⟩
      bridge (id {(A ⊗₀ B) ⊗₀ C}) ∘ αB
        ≈⟨ bridge-id-is-id ((A ⊗₀ B) ⊗₀ C) ⟩∘⟨refl ⟩
      id ∘ αB
        ≈⟨ idˡ ⟩
      α⇐-form-list (flatten A) (flatten B) (flatten C)
        ∎
      where
        αF = α⇒-form-list (flatten A) (flatten B) (flatten C)
        αB = α⇐-form-list (flatten A) (flatten B) (flatten C)

  decode-α⇐-collapse
    : ∀ {A B C} → decode (α⇐ {A} {B} {C}) ≈Term bridge (α⇐ {A} {B} {C})
  decode-α⇐-collapse {A} {B} {C} = begin
    decode (α⇐ {A} {B} {C})
      ≈⟨ ≡⇒≈Term (subst₂-dom-trans (domL-hId D) assoc-eq (codL-hId D)
                    (proj₁ (decode-attempt-hId D))) ⟩
    subst₂ HomTerm (cong unflatten assoc-eq) refl (decode (id {D}))
      ≈⟨ subst₂-resp-≈Term (cong unflatten assoc-eq) refl (decode-id-is-id D) ⟩
    subst₂ HomTerm (cong unflatten assoc-eq) refl (id {unflatten (flatten D)})
      ≈⟨ ≡⇒≈Term (subst₂-refl-dom assoc-eq) ⟩
    subst (λ z → HomTerm (unflatten z) (unflatten (flatten D))) assoc-eq id
      ≈⟨ α⇐-coh-list (flatten A) (flatten B) (flatten C) ⟩
    α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ bridge-α⇐-form-full A B C ⟨
    bridge (α⇐ {A} {B} {C})
      ∎
    where
      D : ObjTerm
      D = (A ⊗₀ B) ⊗₀ C
      assoc-eq : flatten D ≡ flatten A ++ flatten B ++ flatten C
      assoc-eq = ++-assoc (flatten A) (flatten B) (flatten C)

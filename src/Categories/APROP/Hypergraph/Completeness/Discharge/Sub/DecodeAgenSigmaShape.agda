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
  using (FlatGen; flatten; range; hSwap; domL-hSwap; codL-hSwap; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL
        ; map-lookup-range)
open import Categories.APROP.Hypergraph.Invariant sig using (hSwap-cod-Unique)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈; _≅_; module ≅)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges; extract-exact; decode-attempt)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-Linear)

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

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (map-++; map-∘; map-cong)
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

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

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

  subst₂-resp-≈Term
    : ∀ {A A' B B'} (p : A ≡ A') (q : B ≡ B') {u v : HomTerm A B}
    → u ≈Term v → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
  subst₂-resp-≈Term refl refl u≈v = u≈v

  -- Under `objUIP`, `subst₂ HomTerm` only cares about endpoints.
  subst₂-HomTerm-irrel
    : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
      {A A' B B' : ObjTerm} (p p' : A ≡ A') (q q' : B ≡ B') (t : HomTerm A B)
    → subst₂ HomTerm p q t ≈Term subst₂ HomTerm p' q' t
  subst₂-HomTerm-irrel objUIP p p' q q' t =
    ≡⇒≈Term (cong₂ (λ x y → subst₂ HomTerm x y t) (objUIP p p') (objUIP q q'))

  -- Compose two boundary `subst₂ HomTerm` transports into one.
  subst₂-HomTerm-∘
    : ∀ {A₀ A₁ A₂ B₀ B₁ B₂}
        (p₁ : A₀ ≡ A₁) (p₂ : A₁ ≡ A₂) (q₁ : B₀ ≡ B₁) (q₂ : B₁ ≡ B₂)
        (t : HomTerm A₀ B₀)
    → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ t)
      ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) t
  subst₂-HomTerm-∘ refl refl refl refl t = refl

--------------------------------------------------------------------------------
-- ## Algorithm extraction (sig-level), VERBATIM from `DecodeComposeShape`.
--
-- From a successful `decode-attempt H` (the totality `decode-attempt-Linear`
-- provides at `H = ⟪·⟫`), expose the returned term AS
-- `permute-via-vlab vlab perm ∘ process-term` for the SAME `process-term =
-- proj₂ (process-all-edges H dom)` and SOME `perm : s_final ↭ cod`.  This is
-- the `sig`-only clone of `LinearExtracts.decode-attempt-shape` (that module
-- is `sig-dec`-parameterised, so cannot be imported into this `sig`-only
-- site — hence we clone the lemma content).

decode-attempt-extract
  : (H : Hypergraph FlatGen)
    (t : HomTerm (unflatten (domL H)) (unflatten (codL H)))
  → decode-attempt H ≡ just t
  → Σ[ perm ∈ proj₁ (process-all-edges H (Hypergraph.dom H)) Perm.↭ Hypergraph.cod H ]
      t ≡ permute-via-vlab (Hypergraph.vlab H) perm
            ∘ proj₂ (process-all-edges H (Hypergraph.dom H))
decode-attempt-extract H t eq
    with process-all-edges H (Hypergraph.dom H)
... | s_final , process-term
    with extract-exact (Hypergraph.cod H) s_final
...    | just perm with eq
...       | refl = perm , refl

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

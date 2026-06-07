{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic "separable-stack" factorization for the decoder's `process-edges`.
--
-- GOAL.  The *parallel analogue* of `process-edges-equivariant`
-- (StackEquivariance.agda): a "separability" statement.  If a block of edges
-- `es` touches ONLY a prefix `xs` of the running stack and leaves a fixed
-- suffix `R` of vertices untouched, then `process-edges H es (xs ++ R)`
-- factors as the run on `xs` alone, tensored with `id` on `R`:
--
--   process-edges H es (xs ++ R)
--     stack:  proj₁ (process-edges H es xs) ++ R           -- R untouched
--     term :  to(uf++ xs' R) ∘ ( proj₂ (process-edges H es xs) ⊗₁ id ) ∘ from(uf++ xs R)
--
-- proven by ONE induction on `es` (cf. the ~4300-line `BlockFactor` of
-- `DecodeTensorShape.agda`, which does an analogous factorization but per-edge
-- across `gblock-factor`/`Sin`/`Sout`/`kfac-*`, going through the `hTensor`
-- `injL`/`injR` embeddings).
--
-- This file PROVES (postulate-free, `--safe`):
--   * the structural invariant that firing stays inside the prefix
--     (`extract-elem-++ˡ`, `extract-prefix-++ˡ`, and their `nothing`-mirrors);
--   * the per-edge step factorization (`edge-step-term-sep`) over the
--     `EdgeStepR` relation view;
--   * the whole induction + final block-merge glue (`process-edges-separable`).
--
-- The hard per-edge box leaf (`fire-mid-suffix`) is discharged by importing the
-- machine-checked `BoxKernel.BlockBoxSuffix.box-suffix-framed` and
-- reframing it onto `fire-mid` (the box term is DEFINITIONALLY the `box-of`
-- subst in `box-suffix-framed`'s RHS, and the two LHS framings agree up to
-- `objUIP` collapse).  `frame-ext` (the `++⁺ʳ` permute-slide) comes from
-- `BlockNFBraid`.  `objUIP` is derived from `_≟X_` via Hedberg (`ObjUIP`).
--
-- NOTE.  The box leaf is taken from the lightweight `BoxKernel` leaf module
-- (NOT the heavyweight `DecodeTensorShape`), so this file does not depend on
-- `DecodeTensorShape` — the import cycle is broken.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SeparableSpike
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-edges; edge-step; extract-prefix; Agen-edge-aux)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of; edge-step-graph
        ; edge-step-sound)

-- The reusable `++⁺ʳ` permute-slide kernel (postulate-free, --safe in source).
-- Its `uf++`/`frame-ext` need Hedberg `uipX` from `DecidableEquality X`.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BlockNFBraid
  asFreeMonoidalData _≟X_ as BNB

-- The machine-checked per-edge box-suffix factorization (`box-suffix-framed`)
-- lives in the lightweight `BoxKernel` leaf module (extracted from
-- DecodeTensorShape), so this validation lemma no longer depends on it.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BoxKernel sig _≟X_
  as DTS

-- `objUIP` (UIP on `ObjTerm`) from Hedberg over `_≟X_`.
open import Categories.APROP.Hypergraph.Soundness.Discharge.ObjUIP using (module ObjUIP)

-- Transport algebra reused across the box-shape consumers.
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using (subst₂-HomTerm-∘; subst₂-resp-≈Term; subst₂-HomTerm-irrel
        ; subst₂-HomTerm-∘-dist; just≢nothing; ⊗id-∘)

-- `cancel-mid-iso` for the cons-merge / SKIP iso-cancellations.
open import Categories.APROP.Hypergraph.Soundness.UnflattenMonoidal sig
  using (cancel-mid-iso)

open import Categories.Hypergraph.ExtractPrefix using (extract-elem)

open import Categories.Category using (Category)

open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Properties using () renaming (≡-dec to List-≡-dec)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using (yes; no)
import Axiom.UniquenessOfIdentityProofs as UIPmod

private
  module FM = Category FreeMonoidal

-- UIP on `ObjTerm`, from `_≟X_` (Hedberg).  Used to collapse the
-- box-suffix-reframe index proofs.
objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
objUIP = ObjUIP.objUIP′ {Symm} _≟X_

--------------------------------------------------------------------------------
-- ## Structural invariant: firing stays inside the prefix.
--
-- `extract-elem`/`extract-prefix` walk the stack left-to-right and stop at the
-- FIRST occurrence.  Hence on `xs ++ R`, if the element/prefix is found within
-- `xs`, the suffix `R` is never inspected and is simply carried onto the
-- residual.  These two lemmas pin that: the residual on `xs ++ R` is
-- `(residual on xs) ++ R`, with the SAME firing decision.
--------------------------------------------------------------------------------

-- `extract-elem` on `xs ++ R`: if `k` is found in `xs` with residual `rest`
-- via the EXACT proof `p`, it is found in `xs ++ R` with residual `rest ++ R`
-- via the EXACT proof `++⁺ʳ R p` (the genuine `extract-elem` recursion on
-- `xs ++ R` literally rebuilds `p`'s constructor tree with `R` appended, so the
-- two proofs are *propositionally* equal — no faithfulness/coherence needed).
-- The cod `(k ∷ rest) ++ R` is definitionally `k ∷ (rest ++ R)`.  Induction on
-- `xs`.
extract-elem-++ˡ
  : ∀ {n} (k : Fin n) (xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ k ∷ rest}
  → extract-elem k xs ≡ just (rest , p)
  → extract-elem k (xs ++ R) ≡ just (rest ++ R , PermProp.++⁺ʳ R p)
extract-elem-++ˡ k []       R ()
extract-elem-++ˡ k (x ∷ xs) R eq with x ≟ k
extract-elem-++ˡ k (x ∷ xs) R {rest} {p} eq | yes refl with eq
... | refl = refl
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q with extract-elem k xs in eqxs
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q | just (rest' , q')
  with eq
... | refl rewrite extract-elem-++ˡ k xs R eqxs = refl

-- `extract-prefix` on `xs ++ R`: if `ks` is found in `xs` with residual `rest`
-- via `p`, it is found in `xs ++ R` with residual `rest ++ R` via the EXACT
-- proof `subst₂ _↭_ refl (assoc-of-cod) (++⁺ʳ R p)` — the genuine recursion
-- rebuilds `p`'s tree with `R` appended, then the cod rebrackets from
-- `(ks ++ rest) ++ R` to `ks ++ (rest ++ R)` by `++-assoc`.  Induction on `ks`,
-- threading `extract-elem-++ˡ` at each cons.
prefix-++ˡ-perm
  : ∀ {n} (ks : List (Fin n)) {xs R rest : List (Fin n)}
  → (xs ++ R) Perm.↭ (ks ++ rest) ++ R
  → (xs ++ R) Perm.↭ ks ++ (rest ++ R)
prefix-++ˡ-perm ks {xs} {R} {rest} q =
  subst (λ z → (xs ++ R) Perm.↭ z) (++-assoc ks rest R) q

extract-prefix-++ˡ
  : ∀ {n} (ks xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ ks ++ rest}
  → extract-prefix ks xs ≡ just (rest , p)
  → extract-prefix ks (xs ++ R)
    ≡ just (rest ++ R , prefix-++ˡ-perm ks (PermProp.++⁺ʳ R p))
extract-prefix-++ˡ []       xs R {rest} {p} eq with eq
... | refl = refl
extract-prefix-++ˡ (k ∷ ks) xs R eq with extract-elem k xs in eqe
extract-prefix-++ˡ (k ∷ ks) xs R eq | just (xs' , pe)
  with extract-prefix ks xs' in eqp
extract-prefix-++ˡ (k ∷ ks) xs R {rest} {p} eq | just (xs' , pe)
  | just (rest' , pp) with eq
... | refl
      rewrite extract-elem-++ˡ k xs R eqe
            | extract-prefix-++ˡ ks xs' R eqp =
      cong (λ z → just (rest' ++ R , z)) perm-eq
  where
    -- The genuine `extract-prefix (k ∷ ks) (xs ++ R)` proof, assembled from the
    -- head `++⁺ʳ R pe` and tail `prefix-++ˡ-perm ks (++⁺ʳ R pp)`, equals the
    -- claimed `prefix-++ˡ-perm (k ∷ ks) (++⁺ʳ R (trans pe (prep k pp)))`.
    -- `++⁺ʳ` distributes over `trans`/`prep`, and the cod assoc on the cons
    -- (`++-assoc (k ∷ ks) rest' R = cong (k ∷_) (++-assoc ks rest' R)`) slides
    -- through the leading `prep k`.
    perm-eq
      : Perm.trans (PermProp.++⁺ʳ R pe)
          (Perm.prep k (prefix-++ˡ-perm ks {xs'} {R} {rest'} (PermProp.++⁺ʳ R pp)))
        ≡ prefix-++ˡ-perm (k ∷ ks) {xs} {R} {rest'}
            (PermProp.++⁺ʳ R (Perm.trans pe (Perm.prep k pp)))
    perm-eq = gen (++-assoc ks rest' R) (PermProp.++⁺ʳ R pp)
      where
        -- Generalise the cod assoc `e` and the tail proof `Q`: the leading
        -- `trans (head)`/`prep k` slide through the `subst`, and the cons assoc
        -- is `cong (k ∷_)` of the tail assoc.  Proven by `J` on `e`.
        gen
          : ∀ {a b : List (Fin _)} (e : a ≡ b)
              (Q : (xs' ++ R) Perm.↭ a)
          → Perm.trans (PermProp.++⁺ʳ R pe)
              (Perm.prep k (subst (λ z → (xs' ++ R) Perm.↭ z) e Q))
            ≡ subst (λ z → (xs ++ R) Perm.↭ z) (cong (k ∷_) e)
                (Perm.trans (PermProp.++⁺ʳ R pe) (Perm.prep k Q))
        gen refl Q = refl

-- NOTHING-direction of `extract-elem-++ˡ`.  CAVEAT: this is NOT unconditionally
-- true — `extract-elem k (xs ++ R)` can be `just` even when `extract-elem k xs`
-- is `nothing`, namely when `k ∈ R`.  For the separability invariant the
-- hypothesis is that the edge block is DISJOINT from `R` (`ein e ∩ R = ∅`), so
-- we require `extract-elem k R ≡ nothing` as a side condition.  Induction on
-- `xs`.
extract-elem-++ˡ-nothing
  : ∀ {n} (k : Fin n) (xs R : List (Fin n))
  → extract-elem k xs ≡ nothing
  → extract-elem k R  ≡ nothing
  → extract-elem k (xs ++ R) ≡ nothing
extract-elem-++ˡ-nothing k []       R eqx eqR = eqR
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR with x ≟ k
... | yes refl with eqx
...   | ()
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR | no ¬q
  with extract-elem k xs in eqxs
... | nothing rewrite extract-elem-++ˡ-nothing k xs R eqxs eqR = refl

-- NOTHING-direction of `extract-prefix-++ˡ`.  Same disjointness side
-- condition, lifted to the prefix: as long as NO prefix element is found in
-- `R` alone, a `nothing` on `xs` stays `nothing` on `xs ++ R`.  We phrase the
-- side condition as "every cons step that fails on `xs` also fails on
-- `xs' ++ R`"; for the clean block case (`ks ∩ R = ∅`) it is discharged by
-- `extract-elem-++ˡ-nothing`.  For the spike, the only `nothing`-case we hit
-- is the FIRST prefix element failing, so we state exactly that.
extract-prefix-++ˡ-nothing-head
  : ∀ {n} (k : Fin n) (ks xs R : List (Fin n))
  → extract-elem k xs ≡ nothing
  → extract-elem k R  ≡ nothing
  → extract-prefix (k ∷ ks) (xs ++ R) ≡ nothing
extract-prefix-++ˡ-nothing-head k ks xs R eqx eqR
  rewrite extract-elem-++ˡ-nothing k xs R eqx eqR = refl

-- FULL `nothing`-transport for `extract-prefix`.  If `ks` fails to extract from
-- `xs` AND every element of `ks` is absent from `R` (the disjointness side
-- condition), then `ks` fails to extract from `xs ++ R`.  Induction on `ks`,
-- threading the per-step `extract-elem` transport: at each found element the
-- located residual on `xs ++ R` is `(residual on xs) ++ R` (`extract-elem-++ˡ`),
-- so the recursion stays on the `_ ++ R` shape.
extract-prefix-++ˡ-nothing
  : ∀ {n} (ks xs R : List (Fin n))
  → All (λ j → extract-elem j R ≡ nothing) ks
  → extract-prefix ks xs ≡ nothing
  → extract-prefix ks (xs ++ R) ≡ nothing
-- `extract-prefix [] xs ≡ just _`, so the `nothing` hypothesis is absurd.
extract-prefix-++ˡ-nothing []       xs R _          ()
extract-prefix-++ˡ-nothing (k ∷ ks) xs R (dk ∷ dks) eqn
  with extract-elem k xs in eqe
-- head not found in `xs`: by disjointness not in `R`, so not in `xs ++ R`.
... | nothing       = extract-prefix-++ˡ-nothing-head k ks xs R eqe dk
-- head found in `xs` with residual `xs'`: split on the tail.  `eqn` (whose type
-- reduces along the located head) forces the tail to fail; recurse on `ks` over
-- `xs'`, re-locating `k` in `xs ++ R` (`extract-elem-++ˡ`).
... | just (xs' , pe)
      with extract-prefix ks xs' in eqp
...     | nothing
          rewrite extract-elem-++ˡ k xs R eqe
                | extract-prefix-++ˡ-nothing ks xs' R dks eqp = refl
...     | just (_ , _) with eqn
...       | ()

--------------------------------------------------------------------------------
-- The decoder fixes `H`; we work `vlab`-relatively.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open FM.HomReasoning

  -- `BlockTensor`-style `uf++` framing, instantiated at `H.vlab`.
  uf++ : (As Bs : List (Fin H.nV))
       → unflatten (map H.vlab (As ++ Bs))
         ≅ unflatten (map H.vlab As) ⊗₀ unflatten (map H.vlab Bs)
  uf++ = BNB.uf++ H.vlab

  R-obj : List (Fin H.nV) → ObjTerm
  R-obj cs = unflatten (map H.vlab cs)

  pvl : {xs ys : List (Fin H.nV)} → xs Perm.↭ ys
      → HomTerm (unflatten (map H.vlab xs)) (unflatten (map H.vlab ys))
  pvl = permute-via-vlab H.vlab

  -- `frame-ext` — the reusable `++⁺ʳ` permute-slide (postulate-free kernel):
  --   to(uf++ fs cs) ∘ (pvl P ⊗₁ id) ∘ from(uf++ es cs) ≈ pvl (++⁺ʳ cs P).
  frame-ext
    : (es fs cs : List (Fin H.nV)) (P : es Perm.↭ fs)
    → _≅_.to (uf++ fs cs) ∘ (pvl P ⊗₁ id {A = R-obj cs}) ∘ _≅_.from (uf++ es cs)
      ≈Term pvl (PermProp.++⁺ʳ cs P)
  frame-ext = BNB.frame-ext H.vlab

  ------------------------------------------------------------------------
  -- ## Per-edge box leaf.  `fire-mid` suffix factorization.
  --
  -- The `fire-mid` box on the residual `rest ++ R` factors, modulo the
  -- `uf++` framing, as `(fire-mid on rest) ⊗₁ id {R}`.  This is the
  -- per-edge Mac-Lane coherence — the generator box `(Agen ⊗ id)` acting on
  -- a residual that splits as `rest ++ R` only acts on `rest`, so the far
  -- block `R` slides out as `⊗₁ id`.
  --
  -- DISCHARGED via the machine-checked
  -- `DecodeTensorShape.BlockBoxSuffix.box-suffix-framed H.vlab (ein e)
  -- (eout e) rest R (elab e)`.  Its RHS box is DEFINITIONALLY `fire-mid e rest`
  -- (both are the same `box-of` subst), and its `uf++`/`R-obj` framing IS the
  -- spike's (both are `BNB.uf++ H.vlab`), so `box-suffix-framed`'s RHS is
  -- definitionally `fire-mid-suffix`'s RHS.  The only work is bridging the two
  -- LHS framings: `box-suffix-framed`'s LHS frames `box-of … (map vlab rest ++
  -- map vlab R)` by `whole-eq`, while `fire-mid-suffix`'s LHS frames
  -- `fire-mid e (rest ++ R)` (= `box-of … (map vlab (rest ++ R))` modulo
  -- `map-++`) by `++-assoc`.  We compose the `fire-mid` `map-++` subst with the
  -- outer `++-assoc` subst, reindex the box residual along `map-++ vlab rest R`
  -- (`box-res`), and collapse the resulting index proofs to `box-suffix-framed`'s
  -- via `objUIP` (`subst₂-HomTerm-irrel`).
  fire-mid-suffix
    : ∀ (e : Fin H.nE) (rest R : List (Fin H.nV))
    → subst₂ HomTerm
        (cong unflatten (cong (map H.vlab) (sym (++-assoc (H.ein  e) rest R))))
        (cong unflatten (cong (map H.vlab) (sym (++-assoc (H.eout e) rest R))))
        (fire-mid H e (rest ++ R))
      ≈Term _≅_.to (uf++ (H.eout e ++ rest) R)
            ∘ (fire-mid H e rest ⊗₁ id {A = R-obj R})
            ∘ _≅_.from (uf++ (H.ein e ++ rest) R)
  fire-mid-suffix e rest R =
    ≈-Term-trans (≡⇒≈Term lhs-≡)
      (≈-Term-trans
        (subst₂-HomTerm-irrel objUIP _ _ _ _ (box-of einL eoutL (rgL ++ RL) g))
        (DTS.BlockBoxSuffix.box-suffix-framed H.vlab
           (H.ein e) (H.eout e) rest R (H.elab e)))
    where
      einL  = map H.vlab (H.ein  e)
      eoutL = map H.vlab (H.eout e)
      rgL   = map H.vlab rest
      RL    = map H.vlab R
      g     = H.elab e

      A-in  = cong unflatten (cong (map H.vlab) (sym (++-assoc (H.ein  e) rest R)))
      A-out = cong unflatten (cong (map H.vlab) (sym (++-assoc (H.eout e) rest R)))
      M-in  = cong unflatten (sym (map-++ H.vlab (H.ein  e) (rest ++ R)))
      M-out = cong unflatten (sym (map-++ H.vlab (H.eout e) (rest ++ R)))

      -- Reindex a `box-of`'s residual list along an equality `f`.
      box-res : ∀ {a b : List X} (f : a ≡ b)
              → subst₂ HomTerm
                  (cong unflatten (cong (einL ++_) f))
                  (cong unflatten (cong (eoutL ++_) f))
                  (box-of einL eoutL a g)
                ≡ box-of einL eoutL b g
      box-res refl = refl

      -- `box-of … (map vlab (rest ++ R))` re-expressed over the SPLIT residual
      -- `map vlab rest ++ map vlab R`, via `map-++ vlab rest R`.
      box-rR-≡ :
        box-of einL eoutL (map H.vlab (rest ++ R)) g
        ≡ subst₂ HomTerm
            (cong unflatten (cong (einL ++_) (sym (map-++ H.vlab rest R))))
            (cong unflatten (cong (eoutL ++_) (sym (map-++ H.vlab rest R))))
            (box-of einL eoutL (rgL ++ RL) g)
      box-rR-≡ = sym (box-res (sym (map-++ H.vlab rest R)))

      lhs-≡ :
        subst₂ HomTerm A-in A-out (fire-mid H e (rest ++ R))
        ≡ subst₂ HomTerm
            (trans (cong unflatten (cong (einL ++_) (sym (map-++ H.vlab rest R))))
                   (trans M-in A-in))
            (trans (cong unflatten (cong (eoutL ++_) (sym (map-++ H.vlab rest R))))
                   (trans M-out A-out))
            (box-of einL eoutL (rgL ++ RL) g)
      lhs-≡ =
        trans
          (subst₂-HomTerm-∘ M-in A-in M-out A-out
             (box-of einL eoutL (map H.vlab (rest ++ R)) g))
          (trans
            (cong (subst₂ HomTerm (trans M-in A-in) (trans M-out A-out)) box-rR-≡)
            (subst₂-HomTerm-∘
              (cong unflatten (cong (einL ++_) (sym (map-++ H.vlab rest R))))
              (trans M-in A-in)
              (cong unflatten (cong (eoutL ++_) (sym (map-++ H.vlab rest R))))
              (trans M-out A-out)
              (box-of einL eoutL (rgL ++ RL) g)))

  ------------------------------------------------------------------------
  -- ## Disjointness predicate.  For the SKIP case (an edge that does NOT fire
  -- on the prefix must also not fire on `prefix ++ R`) we need that no input
  -- vertex of any edge lives in `R`.  `extract-elem k R ≡ nothing` ⟺ `k ∉ R`,
  -- so we phrase disjointness vertex-wise.  Because edges only ever shuffle
  -- the `xs`-part (FIRE keeps the residual in the `xs`-part and prepends
  -- `eout e` to the front), the suffix `R` is literally fixed across the whole
  -- run, so this GLOBAL (stack-independent) hypothesis suffices for one
  -- induction.
  ------------------------------------------------------------------------

  -- `ein e` is disjoint from `R`.
  ein-disjoint : (e : Fin H.nE) (R : List (Fin H.nV)) → Set
  ein-disjoint e R = All (λ k → extract-elem k R ≡ nothing) (H.ein e)

  -- The whole block `es` is disjoint from `R`.
  block-disjoint : (es : List (Fin H.nE)) (R : List (Fin H.nV)) → Set
  block-disjoint es R = All (λ e → ein-disjoint e R) es

  -- The SKIP transport, specialised to `ks = H.ein e`: an edge that fails to
  -- fire on `xs` (and whose inputs are disjoint from `R`) still fails on
  -- `xs ++ R`.  This is exactly `extract-prefix-++ˡ-nothing` at `H.ein e`.
  skip-transport
    : ∀ (e : Fin H.nE) (xs R : List (Fin H.nV))
    → ein-disjoint e R
    → extract-prefix (H.ein e) xs ≡ nothing
    → extract-prefix (H.ein e) (xs ++ R) ≡ nothing
  skip-transport e xs R dis eqn =
    extract-prefix-++ˡ-nothing (H.ein e) xs R dis eqn

  ------------------------------------------------------------------------
  -- ## Stack-level separability (FULLY PROVEN, no postulates).
  --
  -- The output stack of `process-edges es (xs ++ R)` is `(run on xs) ++ R`:
  -- the suffix `R` is untouched.  This is the cheap, structural heart of the
  -- separability claim — it needs ONLY the firing-stays-in-prefix lemmas
  -- (`extract-prefix-++ˡ` for FIRE, `skip-transport` for SKIP) and `++-assoc`.
  --
  -- Proven by induction on `es`, threading `block-disjoint`.
  ------------------------------------------------------------------------

  edge-step-stack-sep
    : ∀ (e : Fin H.nE) (xs R : List (Fin H.nV))
    → ein-disjoint e R
    → proj₁ (edge-step H (xs ++ R) e) ≡ proj₁ (edge-step H xs e) ++ R
  edge-step-stack-sep e xs R dis
      with extract-prefix (H.ein e) xs in eqxs
  -- SKIP on `xs`: stack on `xs` is `xs`; on `xs ++ R`, also a SKIP (by
  -- `skip-transport`), stack `xs ++ R`.
  ... | nothing
      with extract-prefix (H.ein e) (xs ++ R) in eqxsR
  ...   | nothing = refl
  ...   | just (r , _) =
          ⊥-elim (just≢nothing
            (trans (sym eqxsR) (skip-transport e xs R dis eqxs)))
  -- FIRE on `xs`: residual `rest`, stack `eout e ++ rest`.  On `xs ++ R`,
  -- `extract-prefix-++ˡ` gives residual `rest ++ R`, stack
  -- `eout e ++ (rest ++ R)` = `(eout e ++ rest) ++ R` by `++-assoc`.
  edge-step-stack-sep e xs R dis | just (rest , perm)
      with extract-prefix (H.ein e) (xs ++ R) in eqxsR
  ...   | nothing =
          ⊥-elim (just≢nothing
            (trans (sym (extract-prefix-++ˡ (H.ein e) xs R eqxs)) eqxsR))
  ...   | just (rR , _)
          with trans (sym eqxsR) (extract-prefix-++ˡ (H.ein e) xs R eqxs)
  ...       | refl = sym (++-assoc (H.eout e) rest R)

  -- Whole-block stack separability.
  process-edges-stack-sep
    : ∀ (es : List (Fin H.nE)) (xs R : List (Fin H.nV))
    → block-disjoint es R
    → proj₁ (process-edges H es (xs ++ R)) ≡ proj₁ (process-edges H es xs) ++ R
  process-edges-stack-sep []       xs R _          = refl
  process-edges-stack-sep (e ∷ es) xs R (de ∷ des) =
    let stepEq : proj₁ (edge-step H (xs ++ R) e) ≡ proj₁ (edge-step H xs e) ++ R
        stepEq = edge-step-stack-sep e xs R de
        -- recurse on the tail with the updated prefix, using stepEq to rewrite
        -- the new stack `proj₁ (edge-step (xs++R) e)` to `xs1 ++ R`.
    in trans (cong (λ z → proj₁ (process-edges H es z)) stepEq)
             (process-edges-stack-sep es (proj₁ (edge-step H xs e)) R des)

  ------------------------------------------------------------------------
  -- ## Term-level separability (induction structure + glue; rests on
  -- `fire-mid-suffix`, `frame-ext`, and pure `subst₂` transport).
  --
  -- `coe` re-indexes the codomain of a step/run term along a stack equation,
  -- so the factored RHS and LHS share the same `HomTerm` boundary.
  ------------------------------------------------------------------------

  coe : ∀ {s s'} → s ≡ s'
      → HomTerm (unflatten (map H.vlab s)) (unflatten (map H.vlab s'))
      → HomTerm (unflatten (map H.vlab s)) (unflatten (map H.vlab s'))
  coe refl t = t

  -- Re-index the codomain only (the use site: the run-term's codomain stack
  -- changes by `stepEq`/`++-assoc`, dom stays the input).
  coe-cod : ∀ {a s s'} → s ≡ s'
          → HomTerm (unflatten (map H.vlab a)) (unflatten (map H.vlab s))
          → HomTerm (unflatten (map H.vlab a)) (unflatten (map H.vlab s'))
  coe-cod refl t = t

  -- UIP on `List (Fin H.nV)` (Hedberg, from `Fin`'s decidable equality).  Lets
  -- us replace the opaque stack-sep proof in `coe-cod` by any convenient proof
  -- of the same equation (`coe-cod-irrel`).
  uipFinList : ∀ {as bs : List (Fin H.nV)} (p q : as ≡ bs) → p ≡ q
  uipFinList = UIPmod.Decidable⇒UIP.≡-irrelevant (List-≡-dec _≟_)

  coe-cod-irrel : ∀ {a s s'} (p q : s ≡ s')
                  (t : HomTerm (unflatten (map H.vlab a)) (unflatten (map H.vlab s)))
                → coe-cod p t ≡ coe-cod q t
  coe-cod-irrel p q t = cong (λ z → coe-cod z t) (uipFinList p q)

  -- The factored target term.
  Factored : (es : List (Fin H.nE)) (xs R : List (Fin H.nV))
           → HomTerm (unflatten (map H.vlab (xs ++ R)))
                     (unflatten (map H.vlab (proj₁ (process-edges H es xs) ++ R)))
  Factored es xs R =
    _≅_.to (uf++ (proj₁ (process-edges H es xs)) R)
    ∘ (proj₂ (process-edges H es xs) ⊗₁ id {A = R-obj R})
    ∘ _≅_.from (uf++ xs R)

  -- `to(uf++ xs R) ∘ (id ⊗ id) ∘ from(uf++ xs R) ≈ id` — the empty-block base
  -- (used by the SKIP per-edge case and the empty-block run).
  id-block
    : ∀ (xs R : List (Fin H.nV))
    → _≅_.to (uf++ xs R)
      ∘ (id {A = R-obj xs} ⊗₁ id {A = R-obj R})
      ∘ _≅_.from (uf++ xs R)
      ≈Term id
  id-block xs R = begin
    _≅_.to (uf++ xs R) ∘ (id ⊗₁ id) ∘ _≅_.from (uf++ xs R)
      ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
    _≅_.to (uf++ xs R) ∘ id ∘ _≅_.from (uf++ xs R)
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    _≅_.to (uf++ xs R) ∘ _≅_.from (uf++ xs R)
      ≈⟨ _≅_.isoˡ (uf++ xs R) ⟩
    id ∎

  ------------------------------------------------------------------------
  -- ## Per-edge step term factorization.
  --
  -- The substantive per-edge term lemma: the edge-step term on `xs ++ R`,
  -- re-indexed along `edge-step-stack-sep`, equals the factored form
  -- `to(uf++ xs1 R) ∘ (step-term-on-xs ⊗₁ id) ∘ from(uf++ xs R)`.
  --
  -- Case-split via the green-slime-free `EdgeStepR` relation view
  -- (`edge-step-graph`), `edge-step-sound` to pin both edge-steps, and
  -- `coe-cod-irrel` (UIP on `List (Fin nV)`) to normalise the opaque
  -- stack-sep proof:
  --   * SKIP/SKIP: both terms `id`; `to(uf++ xs R) ∘ (id ⊗ id) ∘ from(uf++ xs R)
  --     ≈ id` by `id-block`.
  --   * FIRE/FIRE: `fire-term = fire-mid ∘ pvl perm`.  The genuine `xs ++ R`
  --     permutation is `prefix-++ˡ-perm (ein e) (++⁺ʳ R perm)` (`extract-prefix-++ˡ`,
  --     a PROPOSITIONAL `↭`-equality — no faithfulness/coherence), so:
  --       fire-mid on (rest ++ R) → `(fire-mid on rest) ⊗ id`  [`fire-mid-suffix`]
  --       pvl (++⁺ʳ R perm)       → `(pvl perm) ⊗ id`          [`frame-ext`]
  --     then the two `⊗ id` blocks join by middle iso-insertion (the reverse
  --     of `cancel-mid-iso`) + `⊗-∘-dist`, and the `coe-cod`/`++-assoc`
  --     transport on the LHS slides through to the SAME `MID-form`
  --     (`lhs-eq-gen`, a single `J`).
  -- Witnessed form: case-split on the two `EdgeStepR` views (for `xs` and
  -- `xs ++ R`), with their indices `s1`/`t1`/`sR`/`tR` and the stack equation
  -- `stepEq` as PARAMETERS — so matching `skipR`/`fireR` refines them without
  -- the occurs-check that a direct `with edge-step-graph` on the stuck
  -- `edge-step` projection would trigger.  The two SKIP/FIRE-mismatch cases are
  -- impossible (`skip-transport` / `extract-prefix-++ˡ`).
  edge-step-term-sep-R
    : ∀ (e : Fin H.nE) (xs R : List (Fin H.nV)) (dis : ein-disjoint e R)
        {s1 : List (Fin H.nV)} {t1 : HomTerm (R-obj xs) (R-obj s1)}
        {sR : List (Fin H.nV)} {tR : HomTerm (R-obj (xs ++ R)) (R-obj sR)}
        (stepEq : sR ≡ s1 ++ R)
    → EdgeStepR H xs e s1 t1
    → EdgeStepR H (xs ++ R) e sR tR
    → coe-cod stepEq tR
      ≈Term _≅_.to (uf++ s1 R) ∘ (t1 ⊗₁ id {A = R-obj R}) ∘ _≅_.from (uf++ xs R)
  -- SKIP/SKIP: both terms `id`, `stepEq : xs ++ R ≡ xs ++ R`.
  edge-step-term-sep-R e xs R dis stepEq (skipR eqxs) (skipR eqxsR) =
    ≈-Term-trans (≡⇒≈Term (coe-cod-irrel stepEq refl id))
                 (≈-Term-sym (id-block xs R))
  -- SKIP on `xs` but FIRE on `xs ++ R`: impossible by `skip-transport`.
  edge-step-term-sep-R e xs R dis stepEq (skipR eqxs) (fireR restR permR eqxsR) =
    ⊥-elim (just≢nothing (trans (sym eqxsR) (skip-transport e xs R dis eqxs)))
  -- FIRE on `xs` but SKIP on `xs ++ R`: impossible by `extract-prefix-++ˡ`.
  edge-step-term-sep-R e xs R dis stepEq (fireR rest perm eqxs) (skipR eqxsR) =
    ⊥-elim (just≢nothing
      (trans (sym (extract-prefix-++ˡ (H.ein e) xs R eqxs)) eqxsR))
  -- FIRE/FIRE: force `restR = rest ++ R`, `permR = qR` via `extract-prefix-++ˡ`,
  -- then factor.
  edge-step-term-sep-R e xs R dis stepEq (fireR rest perm eqxs)
                       (fireR restR permR eqxsR)
      with trans (sym eqxsR) (extract-prefix-++ˡ (H.ein e) xs R eqxs)
  ... | refl =
        ≈-Term-trans
          (≡⇒≈Term (trans (coe-cod-irrel stepEq
                            (sym (++-assoc (H.eout e) rest R))
                            (fire-mid H e (rest ++ R) ∘ pvl qR))
                          lhs-eq))
          (≈-Term-sym rhs-eq)
    where
      qR : (xs ++ R) Perm.↭ H.ein e ++ (rest ++ R)
      qR = prefix-++ˡ-perm (H.ein e) (PermProp.++⁺ʳ R perm)

      A-in  = cong unflatten (cong (map H.vlab) (sym (++-assoc (H.ein  e) rest R)))
      A-out = cong unflatten (cong (map H.vlab) (sym (++-assoc (H.eout e) rest R)))

      -- The shared `MID-form` both sides reduce to.
      MID : HomTerm (unflatten (map H.vlab (xs ++ R)))
                    (unflatten (map H.vlab ((H.eout e ++ rest) ++ R)))
      MID = subst₂ HomTerm A-in A-out (fire-mid H e (rest ++ R))
            ∘ pvl (PermProp.++⁺ʳ R perm)

      -- LHS → MID, by a single `J` over the two `++-assoc`s.  `coe-cod (sym e_o)`
      -- and `qR`'s `++-assoc (ein) rest R` `subst` slide onto the `subst₂`-framed
      -- `fire-mid` / `pvl`, collapsing to `MID` when both assocs are `refl`.
      lhs-eq-gen
        : ∀ {Bi Bo : List (Fin H.nV)}
            (e_i : (H.ein  e ++ rest) ++ R ≡ Bi)
            (e_o : (H.eout e ++ rest) ++ R ≡ Bo)
            (F : HomTerm (R-obj Bi) (R-obj Bo))
            (P : (xs ++ R) Perm.↭ (H.ein e ++ rest) ++ R)
        → coe-cod (sym e_o) (F ∘ pvl (subst (λ z → (xs ++ R) Perm.↭ z) e_i P))
          ≡ subst₂ HomTerm (cong unflatten (cong (map H.vlab) (sym e_i)))
                           (cong unflatten (cong (map H.vlab) (sym e_o))) F
            ∘ pvl P
      lhs-eq-gen refl refl F P = refl

      lhs-eq :
        coe-cod (sym (++-assoc (H.eout e) rest R))
          (fire-mid H e (rest ++ R) ∘ pvl qR)
        ≡ MID
      lhs-eq = lhs-eq-gen (++-assoc (H.ein e) rest R) (++-assoc (H.eout e) rest R)
                 (fire-mid H e (rest ++ R)) (PermProp.++⁺ʳ R perm)

      -- RHS → MID: expand `(fire-mid e rest ∘ pvl perm) ⊗₁ id`, insert the
      -- middle iso `from(uf++ (ein++rest) R) ∘ to(...) = id` (reverse of
      -- `cancel-mid-iso`), then apply `fire-mid-suffix` (box half) and
      -- `frame-ext` (permute half).
      rhs-eq :
        _≅_.to (uf++ (H.eout e ++ rest) R)
          ∘ ((fire-mid H e rest ∘ pvl perm) ⊗₁ id {A = R-obj R})
          ∘ _≅_.from (uf++ xs R)
        ≈Term MID
      rhs-eq = begin
        to-eorg ∘ ((fire-mid H e rest ∘ pvl perm) ⊗₁ id) ∘ from-xs
          ≈⟨ refl⟩∘⟨ ⊗id-∘ (fire-mid H e rest) (pvl perm) ⟩∘⟨refl ⟩
        to-eorg ∘ ((fire-mid H e rest ⊗₁ id) ∘ (pvl perm ⊗₁ id)) ∘ from-xs
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        to-eorg ∘ (fire-mid H e rest ⊗₁ id) ∘ (pvl perm ⊗₁ id) ∘ from-xs
          ≈⟨ ≈-Term-sym
               (cancel-mid-iso to-eorg (fire-mid H e rest ⊗₁ id) from-eirg
                 to-eirg (pvl perm ⊗₁ id) from-xs
                 (_≅_.isoʳ (uf++ (H.ein e ++ rest) R))) ⟩
        (to-eorg ∘ (fire-mid H e rest ⊗₁ id) ∘ from-eirg)
          ∘ (to-eirg ∘ (pvl perm ⊗₁ id) ∘ from-xs)
          ≈⟨ ∘-resp-≈ (≈-Term-sym (fire-mid-suffix e rest R))
                      (frame-ext xs (H.ein e ++ rest) R perm) ⟩
        subst₂ HomTerm A-in A-out (fire-mid H e (rest ++ R))
          ∘ pvl (PermProp.++⁺ʳ R perm) ∎
        where
          to-eorg  = _≅_.to   (uf++ (H.eout e ++ rest) R)
          from-eirg = _≅_.from (uf++ (H.ein  e ++ rest) R)
          to-eirg  = _≅_.to   (uf++ (H.ein  e ++ rest) R)
          from-xs  = _≅_.from (uf++ xs R)

  -- The per-edge step term factorization, dispatched to `edge-step-term-sep-R`
  -- over the two `edge-step-graph` views.
  edge-step-term-sep
    : ∀ (e : Fin H.nE) (xs R : List (Fin H.nV))
        (dis : ein-disjoint e R)
    → coe-cod (edge-step-stack-sep e xs R dis)
        (proj₂ (edge-step H (xs ++ R) e))
      ≈Term _≅_.to (uf++ (proj₁ (edge-step H xs e)) R)
            ∘ (proj₂ (edge-step H xs e) ⊗₁ id {A = R-obj R})
            ∘ _≅_.from (uf++ xs R)
  edge-step-term-sep e xs R dis =
    edge-step-term-sep-R e xs R dis (edge-step-stack-sep e xs R dis)
      (edge-step-graph H xs e) (edge-step-graph H (xs ++ R) e)

  ------------------------------------------------------------------------
  -- ## MAIN THEOREM — `process-edges-separable`.
  --
  -- The whole block run on `xs ++ R`, re-indexed along the stack
  -- separability `process-edges-stack-sep`, equals the factored form
  -- `Factored`.  ONE induction on `es`:
  --   * `[]`  : both runs are `id`; `to(uf++ xs R) ∘ (id ⊗ id) ∘ from(uf++ xs R)
  --             ≈ id`.  (`id-block`, proven below.)
  --   * `e∷es`: head factored by `edge-step-term-sep`, tail by the IH on the
  --             updated prefix, the two `(· ⊗₁ id)` blocks merging via
  --             middle iso-cancellation + `⊗-∘-dist` (exactly the
  --             `cancel-merge` of `gblock-factor.combine`, but here at
  --             `H.vlab` with no `injL`/`injR`).
  --
  -- The merge step is the SAME `cancel-mid-iso`+`⊗-∘-dist` pattern as the
  -- heavy proof; we POSTULATE the assembled cons-merge (POSTULATE 4) since it
  -- is pure category algebra identical to `gblock-factor.combine`'s
  -- `cancel-merge`, just re-stated at this framing.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- ## cons-merge — pure category algebra.
  --
  -- The cons step: given the head factored (`edge-step-term-sep`) and the
  -- tail factored (IH), the composite factors with the two `(· ⊗₁ id)` blocks
  -- merged.  This is verbatim `gblock-factor.combine`'s `cancel-merge`:
  --   (to(uf++ xs1' R) ∘ (T ⊗ id) ∘ from(uf++ xs1 R))
  --     ∘ (to(uf++ xs1 R) ∘ (S ⊗ id) ∘ from(uf++ xs R))
  --   ≈ to(uf++ xs1' R) ∘ ((T ∘ S) ⊗ id) ∘ from(uf++ xs R)
  -- via `cancel-mid-iso` (`isoʳ (uf++ xs1 R)`) + `sym-assoc` + `⊗-∘-dist` +
  -- `idˡ`.  Same pattern as `BlockTensor.pvv-block-tensor`'s `cancel-mid` +
  -- interchange.
  cons-merge
    : ∀ {xs xs1 xs1' R : List (Fin H.nV)}
        (T : HomTerm (R-obj xs1) (R-obj xs1'))
        (S : HomTerm (R-obj xs) (R-obj xs1))
    → (_≅_.to (uf++ xs1' R) ∘ (T ⊗₁ id {A = R-obj R}) ∘ _≅_.from (uf++ xs1 R))
      ∘ (_≅_.to (uf++ xs1 R) ∘ (S ⊗₁ id {A = R-obj R}) ∘ _≅_.from (uf++ xs R))
      ≈Term _≅_.to (uf++ xs1' R)
            ∘ ((T ∘ S) ⊗₁ id {A = R-obj R})
            ∘ _≅_.from (uf++ xs R)
  cons-merge {xs} {xs1} {xs1'} {R} T S = begin
    (to1' ∘ (T ⊗₁ id) ∘ from1) ∘ (to1 ∘ (S ⊗₁ id) ∘ from0)
      ≈⟨ cancel-mid-iso to1' (T ⊗₁ id) from1 to1 (S ⊗₁ id) from0
           (_≅_.isoʳ (uf++ xs1 R)) ⟩
    to1' ∘ (T ⊗₁ id) ∘ (S ⊗₁ id) ∘ from0
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    to1' ∘ ((T ⊗₁ id) ∘ (S ⊗₁ id)) ∘ from0
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    to1' ∘ ((T ∘ S) ⊗₁ (id ∘ id)) ∘ from0
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩∘⟨refl ⟩
    to1' ∘ ((T ∘ S) ⊗₁ id) ∘ from0 ∎
    where
      to1'  = _≅_.to   (uf++ xs1' R)
      to1   = _≅_.to   (uf++ xs1  R)
      from1 = _≅_.from (uf++ xs1  R)
      from0 = _≅_.from (uf++ xs   R)

  -- `coe-cod` (codomain transport) distributes over the cod factor of `∘`.
  coe-cod-∘ : ∀ {a m s s'} (eq : s ≡ s')
                (f : HomTerm (unflatten (map H.vlab m)) (unflatten (map H.vlab s)))
                (g : HomTerm (unflatten (map H.vlab a)) (unflatten (map H.vlab m)))
            → coe-cod {a} eq (f ∘ g) ≡ coe-cod {m} eq f ∘ g
  coe-cod-∘ refl f g = refl

  process-edges-separable
    : ∀ (es : List (Fin H.nE)) (xs R : List (Fin H.nV))
        (dis : block-disjoint es R)
    → coe-cod (process-edges-stack-sep es xs R dis)
        (proj₂ (process-edges H es (xs ++ R)))
      ≈Term Factored es xs R
  process-edges-separable [] xs R _ = ≈-Term-sym (id-block xs R)
  process-edges-separable (e ∷ es) xs R (de ∷ des) =
    combine (proj₁ (edge-step H (xs ++ R) e))
            (proj₂ (edge-step H (xs ++ R) e))
            (proj₂ (edge-step H xs e))
            (edge-step-stack-sep e xs R de)
            (process-edges-stack-sep (e ∷ es) xs R (de ∷ des))
            (edge-step-term-sep e xs R de)
    where
      xs1 = proj₁ (edge-step H xs e)
      Hd  = proj₂ (edge-step H xs e)

      open FM.HomReasoning

      -- The cons assembly, modelled on `gblock-factor`'s `goal`/`combine` (but
      -- without the `injL`/`injR` reconciliation — here the cons reconciliation
      -- is just `++`-associativity, already discharged in the stack-sep).
      -- Generalise the stuck `edge-step` projection `s1ᵍ`/head `Hdᵍ` so the
      -- step-stack-sep `stepEq : s1ᵍ ≡ xs1 ++ R` matches at `refl`, collapsing
      -- the `coe-cod` on the composite; then distribute (`coe-cod-∘`), apply the
      -- IH on the tail (over `xs1`, via `coe-cod-irrel`), and join the two
      -- `(· ⊗₁ id)` blocks via `cons-merge`.
      combine
        : ∀ (s1ᵍ : List (Fin H.nV))
            (Hdᵍ : HomTerm (R-obj (xs ++ R)) (R-obj s1ᵍ))
            (HdL : HomTerm (R-obj xs) (R-obj xs1))
            (stepEq : s1ᵍ ≡ xs1 ++ R)
            (wholeEq : proj₁ (process-edges H es s1ᵍ)
                       ≡ proj₁ (process-edges H es xs1) ++ R)
        → coe-cod stepEq Hdᵍ
          ≈Term _≅_.to (uf++ xs1 R)
                ∘ (HdL ⊗₁ id {A = R-obj R})
                ∘ _≅_.from (uf++ xs R)
        → coe-cod wholeEq (proj₂ (process-edges H es s1ᵍ) ∘ Hdᵍ)
          ≈Term _≅_.to (uf++ (proj₁ (process-edges H es xs1)) R)
                ∘ ((proj₂ (process-edges H es xs1) ∘ HdL) ⊗₁ id {A = R-obj R})
                ∘ _≅_.from (uf++ xs R)
      combine .(xs1 ++ R) Hdᵍ HdL refl wholeEq head = begin
        coe-cod wholeEq (proj₂ (process-edges H es (xs1 ++ R)) ∘ Hdᵍ)
          ≈⟨ ≡⇒≈Term (coe-cod-∘ wholeEq (proj₂ (process-edges H es (xs1 ++ R))) Hdᵍ) ⟩
        coe-cod wholeEq (proj₂ (process-edges H es (xs1 ++ R))) ∘ Hdᵍ
          ≈⟨ ∘-resp-≈
               (≡⇒≈Term (coe-cod-irrel wholeEq (process-edges-stack-sep es xs1 R des)
                          (proj₂ (process-edges H es (xs1 ++ R)))))
               ≈-Term-refl ⟩
        coe-cod (process-edges-stack-sep es xs1 R des)
          (proj₂ (process-edges H es (xs1 ++ R))) ∘ Hdᵍ
          ≈⟨ ∘-resp-≈ (process-edges-separable es xs1 R des) head ⟩
        (_≅_.to (uf++ (proj₁ (process-edges H es xs1)) R)
          ∘ (proj₂ (process-edges H es xs1) ⊗₁ id {A = R-obj R})
          ∘ _≅_.from (uf++ xs1 R))
          ∘ (_≅_.to (uf++ xs1 R)
             ∘ (HdL ⊗₁ id {A = R-obj R})
             ∘ _≅_.from (uf++ xs R))
          ≈⟨ cons-merge (proj₂ (process-edges H es xs1)) HdL ⟩
        _≅_.to (uf++ (proj₁ (process-edges H es xs1)) R)
          ∘ ((proj₂ (process-edges H es xs1) ∘ HdL) ⊗₁ id {A = R-obj R})
          ∘ _≅_.from (uf++ xs R) ∎

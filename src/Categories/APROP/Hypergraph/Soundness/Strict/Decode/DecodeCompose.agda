{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Strict decoder `∘`-SHAPE, Stage 1: block-level factoring of the strict run.
--
--   §0  permuteˢ-X   — cross-vertex-type permute bridge (a V-level strict
--                      permute equals, modulo a map-id boundary cast, the
--                      X-level permuteˣ of the label-pushed derivation).  The
--                      keystone letting the single-vertex-type residual
--                      discharge cross-hypergraph permute equalities.
--   §1  pe-*-++ˢ / run-split-atˢ — strict stack/term factoring of the run at
--                      `es ≡ gblk ++ kblk`.
--   TermEmbedˢ / Equivariantˢ — the per-edge relabelling twin
--                      (`process-edges-term-embˢ`) + the FIRE-box equivariance
--                      foundation (`pvv-transˢ`, `pvv-inverse-*ˢ`).
--
-- The ∘-shape assembly proper is `DecodeComposeAssembly.decodePˢ-∘-shape`,
-- kept a separate module to avoid a `StackEquiv` import cycle.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; subst₂-FlatGen-cancel; subst₂-FlatGen-cancel′)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (edge-step; process-edges; extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_ public

-- The single deferred Kelly residual, at the X-level (identity labelling).
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  using (module Support)

-- The eval-coincidence keystone (injective relabel ⇒ same evaluated bijection).
open import Categories.Hypergraph.ExtractPrefixEvalPhi using (eval-coincide)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.FinBijSubst using (≈-fb-of-≡)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-∘; map-cong; map-++; map-id)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## §0.  The cross-vertex-type permute bridge.
--
-- The strict Kelly residual `permˢ-K` is parameterised by a SINGLE vertex
-- type `V`.  The composition `∘`-shape, however, relates the run over the
-- relabelled composite (vertex type `Fin C.nV`) to the sub-decoder runs
-- (vertex types `Fin G.nV` / `Fin K.nV`).  To compare `permuteˢ` derivations
-- across vertex types we route both through the X-LEVEL permute (vertex type
-- `X`, label `id`): `permuteˢ {V} vlab p` and the X-level permute of
-- `map⁺ vlab p` build the SAME `HomS` term, modulo the `map-id`/`map-∘`
-- relabelling of the boundary lists.  Then `permˢ-K X id` (driven by
-- `eval-coincide`) identifies the two X-level permutes.

module XPerm where
  open Perm′ X (λ x → x) public renaming (permuteˢ to permuteˣ)

-- `permuteˢ` at a vertex type `V` equals (up to the `map-id ∘ map-∘`
-- boundary cast) the X-level permute of the label-pushed derivation.
module _ (V : Set) (vlab : V → X) where
  open Perm′ V vlab using (permuteˢ)
  open XPerm using (permuteˣ)

  -- boundary: map id (map vlab xs) ≡ map vlab xs
  mp : (xs : List V) → map (λ x → x) (map vlab xs) ≡ map vlab xs
  mp xs = map-id (map vlab xs)

  permuteˢ-X
    : ∀ {xs ys : List V} (p : xs Perm.↭ ys)
    → castˢ (mp xs) (mp ys) (permuteˣ (PermProp.map⁺ vlab p)) ≈ˢ permuteˢ p
  permuteˢ-X {xs} Perm.refl = cast-id (mp xs) (mp xs)
  permuteˢ-X (Perm.prep x p) =
    ≈-trans
      (cast-⊗-frame (idˢ {vlab x ∷ []}) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab p)) _ _)
      (⊗-resp ≈-refl (permuteˢ-X p))
  permuteˢ-X (Perm.swap x y p) =
    ≈-trans
      (cast-⊗-frame (σˢ (vlab x ∷ []) (vlab y ∷ [])) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab p)) _ _)
      (⊗-resp ≈-refl (permuteˢ-X p))
  permuteˢ-X (Perm.trans p q) =
    ≈-trans
      (∘-cast-split (mp _) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab q)) (permuteˣ (PermProp.map⁺ vlab p)))
      (∘-resp (permuteˢ-X q) (permuteˢ-X p))

--------------------------------------------------------------------------------
-- ## §1.  Per-hypergraph block factoring (strict).

module RunBlocks (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  ------------------------------------------------------------------------
  -- STACK factoring.  Running `ps ++ rest` from `s` leaves the same stack
  -- as running `rest` from the post-`ps` stack.  Refl-pure (same shape as
  -- the non-strict `pe-stack-++`); the per-edge term is irrelevant.

  pe-stack-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₁ (process-edgesˢ (ps ++ rest) s)
      ≡ proj₁ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
  pe-stack-++ˢ []       rest s = refl
  pe-stack-++ˢ (e ∷ ps) rest s = pe-stack-++ˢ ps rest (proj₁ (edge-stepˢ s e))

  ------------------------------------------------------------------------
  -- TERM factoring.  On the term level, the composite run is the `rest`-run
  -- precomposed with the `ps`-run, modulo a stack cast on the codomain.
  --
  -- The non-strict proof pays a `coe-cod`-transport + `assoc` per edge; in
  -- the strict world the cast is `castˢ refl (cong (map vl) …)` and the
  -- per-edge reassoc is `assocˢ`.

  coeCod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomS (map vl d) (map vl s)
    → HomS (map vl d) (map vl s')
  coeCod e = castˢ refl (cong (map vl) e)

  pe-term-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ (ps ++ rest) s)
      ≈ˢ coeCod (sym (pe-stack-++ˢ ps rest s))
           (proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
             ∘ˢ proj₂ (process-edgesˢ ps s))
  pe-term-++ˢ []       rest s = ≈-sym idʳ
  pe-term-++ˢ (e ∷ ps) rest s =
    ≈-trans (∘-resp (pe-term-++ˢ ps rest s') ≈-refl)
            (coeCod-reassoc E R G t)
    where
      s' = proj₁ (edge-stepˢ s e)
      t  = proj₂ (edge-stepˢ s e)
      G  = proj₂ (process-edgesˢ ps s')
      R  = proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s')))
      E  = sym (pe-stack-++ˢ ps rest s')

      -- coeCod E (R ∘ˢ G) ∘ˢ t ≈ coeCod E (R ∘ˢ (G ∘ˢ t))
      -- (the cast slides past ∘ˢ on the codomain, then re-associate).
      coeCod-reassoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (R0 : HomS (map vl (proj₁ (process-edgesˢ ps s'))) (map vl a))
            (G0 : HomS (map vl s') (map vl (proj₁ (process-edgesˢ ps s'))))
            (t0 : HomS (map vl s) (map vl s'))
        → coeCod eq (R0 ∘ˢ G0) ∘ˢ t0 ≈ˢ coeCod eq (R0 ∘ˢ (G0 ∘ˢ t0))
      coeCod-reassoc refl R0 G0 t0 = assocˢ

  ------------------------------------------------------------------------
  -- RUN at an arbitrary edge list `es` equal to `gblk ++ kblk`: the run
  -- term factors into the `kblk`-run on the post-`gblk` stack precomposed
  -- with the `gblk`-run.  `range C.nE` instantiates `es` via `range-++`.

  run-split-atˢ
    : ∀ {es : List (Fin H.nE)} (gblk kblk : List (Fin H.nE))
        (eq : es ≡ gblk ++ kblk) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ es s)
      ≈ˢ coeCod (trans (sym (pe-stack-++ˢ gblk kblk s))
                       (cong (λ z → proj₁ (process-edgesˢ z s)) (sym eq)))
           (proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk s)))
             ∘ˢ proj₂ (process-edgesˢ gblk s))
  run-split-atˢ gblk kblk refl s =
      ≈-trans (pe-term-++ˢ gblk kblk s)
        (≡⇒≈ˢ (cast-irrel
                 refl refl
                 (cong (map vl) (sym (pe-stack-++ˢ gblk kblk s)))
                 (cong (map vl) (trans (sym (pe-stack-++ˢ gblk kblk s)) refl))
                 (proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk s)))
                   ∘ˢ proj₂ (process-edgesˢ gblk s))))


--------------------------------------------------------------------------------
-- ## Local plumbing.

private
  -- The X-level Kelly residual (vertex type `X`, labelling `id`).
  permˢ-K-X : Support.PermK X (λ x → x)
  permˢ-K-X = PK.permˢ-K X _≟X_ (λ x → x)

  -- generator-cast: a `castˢ` of a `genˢ` is the `genˢ` of the `subst₂`-ed
  -- generator.  (`refl refl` matched.)
  gen-cast
    : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (g : FlatGen as bs)
    → castˢ p q (genˢ g) ≡ genˢ (subst₂ FlatGen p q g)
  gen-cast refl refl g = refl

  -- `eval-↭` of a two-sided `subst₂`-ed derivation is a `subst₂ FinBij`
  -- (re-proved locally, 1-liner; avoids a heavy `HomTermTransport` import).
  eval-subst₂-↭
    : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
        (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
    → eval-↭ (subst₂ Perm._↭_ p q r)
      ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
  eval-subst₂-↭ refl refl r = refl

  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

  -- split a `castˢ` across a `⊗ˢ` (all endpoint proofs given; UIP absorbs
  -- the supplied product proofs `P`/`Q`).
  cast-⊗-split
    : ∀ {xs xs' ys ys' us us' vs vs'}
        (px : xs ≡ xs') (py : ys ≡ ys') (pu : us ≡ us') (pv : vs ≡ vs')
        (f : HomS xs ys) (g : HomS us vs)
        (P : xs ++ us ≡ xs' ++ us') (Q : ys ++ vs ≡ ys' ++ vs')
    → castˢ P Q (f ⊗ˢ g) ≈ˢ castˢ px py f ⊗ˢ castˢ pu pv g
  cast-⊗-split refl refl refl refl f g P Q rewrite uipL P refl | uipL Q refl = ≈-refl

  open XPerm using (permuteˣ)

  -- two-sided subst on a derivation = a `castˢ` of the X-level permute.
  -- (`map id xs ≡ xs` definitionally, so `castˢ` lands on the bare lists.)
  permuteˣ-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → permuteˣ (subst₂ Perm._↭_ p q r)
      ≡ castˢ (cong (map (λ x → x)) p) (cong (map (λ x → x)) q) (permuteˣ r)
  permuteˣ-subst₂ refl refl r = refl

--------------------------------------------------------------------------------
-- ## Smart builder for the `atom-ein`/`atom-eout`/`ψ-elab` glue of `TermEmbedˢ`.
--
-- These three inputs are NOT independent data: given the raw endpoint
-- reductions (`ein-red`/`eout-red`), the label-pushed `map-via` cast (`mv`),
-- and the edge-label reduction (`elab-c`), all three are DERIVED uniformly.
-- The `ψ-elab` derivation is the two-cast cancellation `subst₂-FlatGen-cancel`
-- (+ `′`); previously each block-twin (G-side / K-side / braid) hand-rolled the
-- same construction with a locally-duplicated cancellation lemma.
module EmbedGlue
  {H J : Hypergraph FlatGen}
  (let module H = Hypergraph H)
  (let module J = Hypergraph J)
  (φ        : Fin H.nV → Fin J.nV)
  (ψ        : Fin H.nE → Fin J.nE)
  (ein-red  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
  (eout-red : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
  (mv       : ∀ (xs : List (Fin H.nV)) → map H.vlab xs ≡ map J.vlab (map φ xs))
  (elab-c   : ∀ e → subst₂ FlatGen (cong (map J.vlab) (ein-red e))
                                   (cong (map J.vlab) (eout-red e)) (J.elab (ψ e))
                  ≡ subst₂ FlatGen (mv (H.ein e)) (mv (H.eout e)) (H.elab e))
  where
  atom-ein : ∀ e → map J.vlab (J.ein (ψ e)) ≡ map H.vlab (H.ein e)
  atom-ein e = trans (cong (map J.vlab) (ein-red e)) (sym (mv (H.ein e)))

  atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e)
  atom-eout e = trans (cong (map J.vlab) (eout-red e)) (sym (mv (H.eout e)))

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e)) ≡ H.elab e
  ψ-elab e =
    trans (subst₂-FlatGen-cancel
             (cong (map J.vlab) (ein-red e)) (cong (map J.vlab) (eout-red e))
             (mv (H.ein e)) (mv (H.eout e)) (J.elab (ψ e)))
      (trans (cong (subst₂ FlatGen (sym (mv (H.ein e))) (sym (mv (H.eout e)))) (elab-c e))
             (subst₂-FlatGen-cancel′ (mv (H.ein e)) (mv (H.eout e)) (H.elab e)))

--------------------------------------------------------------------------------
-- ## (A)  The generic embedding-based per-edge + process-edges term-twins,
-- strict.  Parameterised by an injective, label-preserving vertex
-- embedding `(φ, ψ)`.

module TermEmbedˢ
  {H J : Hypergraph FlatGen}
  (let module H = Hypergraph H)
  (let module J = Hypergraph J)
  -- Injective, label-preserving vertex embedding.
  (φ      : Fin H.nV → Fin J.nV)
  (φ-inj  : ∀ {x y} → φ x ≡ φ y → x ≡ y)
  (φ-lab  : ∀ i → J.vlab (φ i) ≡ H.vlab i)
  -- Edge map with endpoints/labels mirroring H's under `map φ`.
  (ψ      : Fin H.nE → Fin J.nE)
  (ψ-ein  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
  (ψ-eout : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
  (atom-ein  : ∀ e → map J.vlab (J.ein  (ψ e)) ≡ map H.vlab (H.ein  e))
  (atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e))
  (ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e))
                ≡ H.elab e)
  where

  private
    module RH = Run H
    module RJ = Run J

  vlH = H.vlab
  vlJ = J.vlab

  -- `map vlJ (map φ s) ≡ map vlH s` (the label-pushed cast).
  vlab-φ : ∀ (s : List (Fin H.nV)) → map vlJ (map φ s) ≡ map vlH s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  ----------------------------------------------------------------------
  -- J-side extract-prefix lock-step with the H-side (term-free; copy of
  -- the non-strict `extract-prefix-J-{nothing,just}`).

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

  ----------------------------------------------------------------------
  -- FIRE box factor.  `genˢ (J.elab (ψe)) ⊗ˢ idˢ` casts to
  -- `genˢ (H.elab e) ⊗ˢ idˢ`, via `cast-⊗-split` + `gen-cast` + `ψ-elab`.

  box-emb
    : ∀ (e : Fin H.nE) (restH : List (Fin H.nV)) (restJ : List (Fin J.nV))
        (restJ≡ : restJ ≡ map φ restH)
        (rest-lab : map vlJ restJ ≡ map vlH restH)
        (P : map vlJ (J.ein  (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.ein  e) ++ map vlH restH)
        (Q : map vlJ (J.eout (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.eout e) ++ map vlH restH)
    → castˢ P Q (genˢ (J.elab (ψ e)) ⊗ˢ idˢ {map vlJ restJ})
      ≈ˢ genˢ (H.elab e) ⊗ˢ idˢ {map vlH restH}
  box-emb e restH restJ restJ≡ rest-lab P Q =
    ≈-trans
      (cast-⊗-split (atom-ein e) (atom-eout e) rest-lab rest-lab
        (genˢ (J.elab (ψ e))) (idˢ {map vlJ restJ}) P Q)
      (⊗-resp gen-side (cast-id rest-lab rest-lab))
    where
      gen-side : castˢ (atom-ein e) (atom-eout e) (genˢ (J.elab (ψ e)))
                 ≈ˢ genˢ (H.elab e)
      gen-side =
        ≡⇒≈ˢ (trans (gen-cast (atom-ein e) (atom-eout e) (J.elab (ψ e)))
                    (cong genˢ (ψ-elab e)))

  ----------------------------------------------------------------------
  -- FIRE permute factor.  `permuteˢ_J permJ` casts to `permuteˢ_H permH`.
  -- Route both through the X-LEVEL permute (§0 `permuteˢ-X`); the two
  -- X-permutes are identified by `permˢ-K-X`, whose evaluated-bijection
  -- premise is `eval-coincide` (transported by `eval-subst₂-↭`).

  perm-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (P : map vlJ (map φ sH) ≡ map vlH sH)
        (Q : map vlJ (J.ein (ψ e) ++ restJ) ≡ map vlH (H.ein e ++ restH))
    → castˢ P Q (RJ.permuteˢ permJ) ≈ˢ RH.permuteˢ permH
  perm-emb e sH restH permH eqH restJ permJ eqJ P Q =
    helper restJ permJ eqJ Q
      (just-injective-fst
        (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH))))
    where
      helper
        : (rJ : List (Fin J.nV))
          (pJ : map φ sH Perm.↭ J.ein (ψ e) ++ rJ)
          (eJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (rJ , pJ))
          (qq : map vlJ (J.ein (ψ e) ++ rJ) ≡ map vlH (H.ein e ++ restH))
        → rJ ≡ map φ restH
        → castˢ P qq (RJ.permuteˢ pJ) ≈ˢ RH.permuteˢ permH
      helper .(map φ restH) pJ eJ qq refl rewrite ψ-ein e =
        ≈-trans
          (cast-resp P qq (≈-sym (permuteˢ-X (Fin J.nV) vlJ pJ)))
          (≈-trans middle (permuteˢ-X (Fin H.nV) vlH permH))
        where
          mpJd = mp (Fin J.nV) vlJ (map φ sH)
          mpJc = mp (Fin J.nV) vlJ (map φ (H.ein e) ++ map φ restH)
          mpHd = mp (Fin H.nV) vlH sH
          mpHc = mp (Fin H.nV) vlH (H.ein e ++ restH)
          Xj = permuteˣ (PermProp.map⁺ vlJ pJ)
          Xh = permuteˣ (PermProp.map⁺ vlH permH)

          -- the evaluated-bijection equality, from `eval-coincide`.
          ev-mid : eval-↭ (subst₂ Perm._↭_ P qq (PermProp.map⁺ vlJ pJ))
                   ≈-fb subst₂ FinBij (cong length P) (cong length qq)
                          (eval-↭ (PermProp.map⁺ vlJ pJ))
          ev-mid = ≈-fb-of-≡ (eval-subst₂-↭ P qq (PermProp.map⁺ vlJ pJ))

          ev-coin : subst₂ FinBij (cong length P) (cong length qq)
                          (eval-↭ (PermProp.map⁺ vlJ pJ))
                    ≈-fb eval-↭ (PermProp.map⁺ vlH permH)
          ev-coin = eval-coincide {H.nV} {J.nV} {X} φ φ-inj vlJ vlH φ-lab
                      (H.ein e) sH restH permH pJ P qq eqH eJ

          ev : eval-↭ (subst₂ Perm._↭_ P qq (PermProp.map⁺ vlJ pJ))
               ≈-fb eval-↭ (PermProp.map⁺ vlH permH)
          ev i = trans (ev-mid i) (ev-coin i)

          -- the X-level identification: `Xh ≈ castˢ (cong(map id)P)(cong(map id)qq) Xj`.
          K-step : Xh ≈ˢ castˢ (cong (map (λ x → x)) P) (cong (map (λ x → x)) qq) Xj
          K-step =
            ≈-trans
              (≈-sym (permˢ-K-X (subst₂ Perm._↭_ P qq (PermProp.map⁺ vlJ pJ))
                                (PermProp.map⁺ vlH permH) ev))
              (≡⇒≈ˢ (permuteˣ-subst₂ P qq (PermProp.map⁺ vlJ pJ)))

          -- `castˢ P qq (castˢ mpJ Xj) ≈ castˢ mpH Xh`: both sides drop to the
          -- bare X-permute (`cast-≈̂`) and are identified by the `K-step`; the
          -- `_≈̂_` combinators absorb the former `cast-fuse`/`cast-irrel` nest.
          middle : castˢ P qq (castˢ mpJd mpJc Xj) ≈ˢ castˢ mpHd mpHc Xh
          middle =
            ≈̂⇒≈ˢ
              (≈̂-trans (≈̂-trans (cast-≈̂ {p = P} {q = qq})
                                (cast-≈̂ {p = mpJd} {q = mpJc}))
              (≈̂-trans (≈̂-sym (≈̂-trans (≈ˢ⇒≈̂ K-step)
                                        (cast-≈̂ {p = cong (map (λ x → x)) P}
                                                {q = cong (map (λ x → x)) qq})))
                       (≈̂-sym (cast-≈̂ {p = mpHd} {q = mpHc}))))


  ----------------------------------------------------------------------
  -- FIRE/FIRE per-edge term-twin, assembled from box-emb + perm-emb.

  edge-step-fire-embˢ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (restJ≡ : restJ ≡ map φ restH)
        (pDom : map vlJ (map φ sH) ≡ map vlH sH)
        (pCod : map vlJ (J.eout (ψ e) ++ restJ) ≡ map vlH (H.eout e ++ restH))
    → castˢ pDom pCod
        (castˢ refl (sym (map-++ vlJ (J.eout (ψ e)) restJ))
           ((genˢ (J.elab (ψ e)) ⊗ˢ idˢ {map vlJ restJ})
             ∘ˢ castˢ refl (map-++ vlJ (J.ein (ψ e)) restJ) (RJ.permuteˢ permJ)))
      ≈ˢ castˢ refl (sym (map-++ vlH (H.eout e) restH))
           ((genˢ (H.elab e) ⊗ˢ idˢ {map vlH restH})
             ∘ˢ castˢ refl (map-++ vlH (H.ein e) restH) (RH.permuteˢ permH))
  edge-step-fire-embˢ e sH restH permH eqH restJ permJ eqJ restJ≡ pDom pCod =
    -- Peel the outer/inner boundary casts off both sides (`cast-≈̂`), congruence
    -- the `∘ˢ` with the box- and perm-twins (`∘-resp-≈̂` threads the middle
    -- endpoint), and re-cast the H-side.  The former `cast-fuse`/`cast-irrel`/
    -- `∘-cast-split` reconciliation nest is absorbed by the `_≈̂_` combinators;
    -- the genuine `⊗`-frame content stays inside `box-emb`/`perm-emb`.
    ≈̂⇒≈ˢ
      (≈̂-trans (≈̂-trans (≈̂-trans (cast-≈̂ {p = pDom} {q = pCod})
                                  (cast-≈̂ {p = refl}
                                          {q = sym (map-++ vlJ (J.eout (ψ e)) restJ)}))
                         (∘-resp-≈̂ box-part jperm-part))
               (≈̂-sym (cast-≈̂ {p = refl} {q = sym (map-++ vlH (H.eout e) restH)})))
    where
      Jperm = castˢ refl (map-++ vlJ (J.ein (ψ e)) restJ) (RJ.permuteˢ permJ)
      Jbox  = genˢ (J.elab (ψ e)) ⊗ˢ idˢ {map vlJ restJ}
      Hbox  = genˢ (H.elab e) ⊗ˢ idˢ {map vlH restH}
      Hperm = castˢ refl (map-++ vlH (H.ein e) restH) (RH.permuteˢ permH)

      rest-lab : map vlJ restJ ≡ map vlH restH
      rest-lab = trans (cong (map vlJ) restJ≡) (vlab-φ restH)

      -- the box-input / perm-output interface (split form, both sides).
      Mmid : map vlJ (J.ein (ψ e)) ++ map vlJ restJ ≡ map vlH (H.ein e) ++ map vlH restH
      Mmid = trans (sym (map-++ vlJ (J.ein (ψ e)) restJ))
             (trans (cong (map vlJ) (cong₂ _++_ (ψ-ein e) restJ≡))
             (trans (cong (map vlJ) (sym (map-++ φ (H.ein e) restH)))
             (trans (vlab-φ (H.ein e ++ restH))
                    (map-++ vlH (H.ein e) restH))))

      Qbox : map vlJ (J.eout (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.eout e) ++ map vlH restH
      Qbox = cong₂ _++_ (atom-eout e) rest-lab

      Qp : map vlJ (J.ein (ψ e) ++ restJ) ≡ map vlH (H.ein e ++ restH)
      Qp = trans (map-++ vlJ (J.ein (ψ e)) restJ)
           (trans Mmid (sym (map-++ vlH (H.ein e) restH)))

      -- BOX twin: `Jbox ≈̂ Hbox` (the `⊗`-frame content is `box-emb`).
      box-part : Jbox ≈̂ Hbox
      box-part = ≈̂-trans (≈̂-sym (cast-≈̂ {p = Mmid} {q = Qbox}))
                         (≈ˢ⇒≈̂ (box-emb e restH restJ restJ≡ rest-lab Mmid Qbox))

      -- PERM twin: `Jperm ≈̂ Hperm` (the K-step content is `perm-emb`).
      jperm-part : Jperm ≈̂ Hperm
      jperm-part =
        ≈̂-trans (cast-≈̂ {p = refl} {q = map-++ vlJ (J.ein (ψ e)) restJ})
        (≈̂-trans (≈̂-trans (≈̂-sym (cast-≈̂ {p = pDom} {q = Qp}))
                           (≈ˢ⇒≈̂ (perm-emb e sH restH permH eqH restJ permJ eqJ pDom Qp)))
                 (≈̂-sym (cast-≈̂ {p = refl} {q = map-++ vlH (H.ein e) restH})))


  ----------------------------------------------------------------------
  -- Per-edge STACK agreement (term-free; lock-step on `extract-prefix`).

  edge-step-stack-embˢ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
    → proj₁ (RJ.edge-stepˢ (map φ sH) (ψ e))
      ≡ map φ (proj₁ (RH.edge-stepˢ sH e))
  edge-step-stack-embˢ e sH with extract-prefix (H.ein e) sH in eqH
  ... | nothing rewrite extract-prefix-J-nothing e sH eqH = refl
  ... | just (restH , permH)
        rewrite proj₂ (extract-prefix-J-just e sH restH permH eqH)
        = trans (cong (_++ map φ restH) (ψ-eout e))
                (sym (map-++ φ (H.eout e) restH))

  ----------------------------------------------------------------------
  -- Per-edge term-twin (dispatch on `extract-prefix`, both sides).

  edge-step-term-embˢ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (pDom : map vlJ (map φ sH) ≡ map vlH sH)
        (pCod : map vlJ (proj₁ (RJ.edge-stepˢ (map φ sH) (ψ e)))
              ≡ map vlH (proj₁ (RH.edge-stepˢ sH e)))
    → castˢ pDom pCod (proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
      ≈ˢ proj₂ (RH.edge-stepˢ sH e)
  edge-step-term-embˢ e sH pDom pCod
    with extract-prefix (H.ein e) sH in eqH
       | extract-prefix (J.ein (ψ e)) (map φ sH) in eqJ
  ... | nothing | nothing = cast-id pDom pCod
  ... | nothing | just (restJ , permJ) =
        ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
        where
          just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
          just≢nothing ()
  ... | just (restH , permH) | nothing =
        ⊥-elim (just≢nothing
          (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
        where
          just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
          just≢nothing ()
  ... | just (restH , permH) | just (restJ , permJ) =
        edge-step-fire-embˢ e sH restH permH eqH restJ permJ eqJ restJ≡ pDom pCod
        where
          restJ≡ : restJ ≡ map φ restH
          restJ≡ = just-injective-fst
                     (trans (sym eqJ)
                            (proj₂ (extract-prefix-J-just e sH restH permH eqH)))

  ----------------------------------------------------------------------
  -- Iterated STACK agreement (term-free).

  proc-stack-embˢ
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
    → proj₁ (RJ.process-edgesˢ (map ψ es) (map φ sH))
      ≡ map φ (proj₁ (RH.process-edgesˢ es sH))
  proc-stack-embˢ []       sH = refl
  proc-stack-embˢ (e ∷ es) sH
    rewrite edge-step-stack-embˢ e sH =
      proc-stack-embˢ es (proj₁ (RH.edge-stepˢ sH e))

  ----------------------------------------------------------------------
  -- Iterated term-twin, GENERALISED over the J-start stack `sJ`
  -- (`sJ ≡ map φ sH`), matched at refl.

  process-edges-term-embˢ-gen
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
        (sJ : List (Fin J.nV)) (sJ≡ : sJ ≡ map φ sH)
        (pDom : map vlJ sJ ≡ map vlH sH)
        (pCod : map vlJ (proj₁ (RJ.process-edgesˢ (map ψ es) sJ))
              ≡ map vlH (proj₁ (RH.process-edgesˢ es sH)))
    → castˢ pDom pCod (proj₂ (RJ.process-edgesˢ (map ψ es) sJ))
      ≈ˢ proj₂ (RH.process-edgesˢ es sH)
  process-edges-term-embˢ-gen [] sH sJ sJ≡ pDom pCod = cast-id pDom pCod
  process-edges-term-embˢ-gen (e ∷ es) sH .(map φ sH) refl pDom pCod = goal
    where
      s'H  = proj₁ (RH.edge-stepˢ sH e)
      s'J  = proj₁ (RJ.edge-stepˢ (map φ sH) (ψ e))

      stepStk : s'J ≡ map φ s'H
      stepStk = edge-step-stack-embˢ e sH

      pMid : map vlJ s'J ≡ map vlH s'H
      pMid = trans (cong (map vlJ) stepStk) (vlab-φ s'H)

      headTwin
        : castˢ pDom pMid (proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
          ≈ˢ proj₂ (RH.edge-stepˢ sH e)
      headTwin = edge-step-term-embˢ e sH pDom pMid

      recTwin
        : castˢ pMid pCod (proj₂ (RJ.process-edgesˢ (map ψ es) s'J))
          ≈ˢ proj₂ (RH.process-edgesˢ es s'H)
      recTwin = process-edges-term-embˢ-gen es s'H s'J stepStk pMid pCod

      goal
        : castˢ pDom pCod
            (proj₂ (RJ.process-edgesˢ (map ψ es) s'J)
             ∘ˢ proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
          ≈ˢ proj₂ (RH.process-edgesˢ es s'H)
             ∘ˢ proj₂ (RH.edge-stepˢ sH e)
      goal =
        ≈-trans
          (∘-cast-split pDom pMid pCod
            (proj₂ (RJ.process-edgesˢ (map ψ es) s'J))
            (proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e))))
          (∘-resp recTwin headTwin)

  ----------------------------------------------------------------------
  -- The headline iterated term-twin, at the canonical `sJ = map φ sH`.

  process-edges-term-embˢ
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
        (pCod : map vlJ (proj₁ (RJ.process-edgesˢ (map ψ es) (map φ sH)))
              ≡ map vlH (proj₁ (RH.process-edgesˢ es sH)))
    → castˢ (vlab-φ sH) pCod (proj₂ (RJ.process-edgesˢ (map ψ es) (map φ sH)))
      ≈ˢ proj₂ (RH.process-edgesˢ es sH)
  process-edges-term-embˢ es sH pCod =
    process-edges-term-embˢ-gen es sH (map φ sH) refl (vlab-φ sH) pCod

--------------------------------------------------------------------------------
-- ## (B)-foundation.  Strict equivariance keystones (the genuinely-new
-- part).  The per-hypergraph `permuteˢ` is a (weak) functor of `↭`: it
-- sends `trans` to `∘ˢ` (definitionally) and inverses to `≈ˢ`-inverses.
-- The inverse law is the strict analogue of `pvv-inverse-{left,right}`;
-- where the non-strict proof invokes `permute-self-loop-id-wide K`, the
-- strict one invokes the per-hypergraph `permˢ-K` on the SELF-LOOP whose
-- evaluated bijection is the identity (`eval-rigid`-free: direct).

open import Categories.PermuteCoherence.EvalSoundness using (eval-↭-sym)
open import Categories.PermuteCoherence.FinBij using (inv-fb)
import Data.Fin.Permutation as P
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)

module Equivariantˢ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  private
    _≟V_ : DecidableEquality (Fin H.nV)
    _≟V_ = _≟F_

    permˢ-K-H : Support.PermK (Fin H.nV) H.vlab
    permˢ-K-H = PK.permˢ-K (Fin H.nV) _≟V_ H.vlab

  -- `permuteˢ (trans p q) = permuteˢ q ∘ˢ permuteˢ p` (definitional).
  pvv-transˢ
    : ∀ {xs ys zs : List (Fin H.nV)} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → permuteˢ (Perm.trans p q) ≈ˢ permuteˢ q ∘ˢ permuteˢ p
  pvv-transˢ p q = ≈-refl

  -- self-loop `trans ρ (↭-sym ρ)` evaluates to the identity bijection.
  -- (Stated on the BARE `Fin H.nV` derivation, as `Support`'s `PermK`
  -- evaluates the vertex-level derivation directly.)
  private
    self-loop-evˡ
      : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
      → eval-↭ (Perm.trans ρ (Perm.↭-sym ρ)) ≈-fb eval-↭ (Perm.refl {xs = xs})
    self-loop-evˡ {xs} {ys} ρ i =
      trans (sym-eval (e P.⟨$⟩ʳ i)) (P.inverseˡ e)
      where
        e = eval-↭ ρ
        sym-eval : eval-↭ (Perm.↭-sym ρ) ≈-fb inv-fb e
        sym-eval = eval-↭-sym ρ

    self-loop-evʳ
      : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
      → eval-↭ (Perm.trans (Perm.↭-sym ρ) ρ) ≈-fb eval-↭ (Perm.refl {xs = ys})
    self-loop-evʳ {xs} {ys} ρ i =
      trans (cong (e P.⟨$⟩ʳ_) (sym-eval i)) (P.inverseʳ e)
      where
        e = eval-↭ ρ
        sym-eval : eval-↭ (Perm.↭-sym ρ) ≈-fb inv-fb e
        sym-eval = eval-↭-sym ρ

  -- `permuteˢ (↭-sym ρ) ∘ˢ permuteˢ ρ ≈ idˢ`.
  pvv-inverse-leftˢ
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permuteˢ (Perm.↭-sym ρ) ∘ˢ permuteˢ ρ ≈ˢ idˢ
  pvv-inverse-leftˢ {xs} {ys} ρ =
    ≈-trans (≈-sym (pvv-transˢ ρ (Perm.↭-sym ρ)))
            (permˢ-K-H (Perm.trans ρ (Perm.↭-sym ρ)) Perm.refl (self-loop-evˡ ρ))

  -- `permuteˢ ρ ∘ˢ permuteˢ (↭-sym ρ) ≈ idˢ`.
  pvv-inverse-rightˢ
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permuteˢ ρ ∘ˢ permuteˢ (Perm.↭-sym ρ) ≈ˢ idˢ
  pvv-inverse-rightˢ {xs} {ys} ρ =
    ≈-trans (≈-sym (pvv-transˢ (Perm.↭-sym ρ) ρ))
            (permˢ-K-H (Perm.trans (Perm.↭-sym ρ) ρ) Perm.refl (self-loop-evʳ ρ))

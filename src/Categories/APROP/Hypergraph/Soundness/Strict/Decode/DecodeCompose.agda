{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Strict decoder `∘`-SHAPE, Stage 1: block-level factoring of the strict run.
--
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
  using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_ public

-- The search's φ-naturality: the relabelled search PRODUCES `map⁺ φ permH`.
open import Categories.Combinatorics.ExtractPrefixEvalPhi using (extract-prefix-pin)
-- The cross-vertex-type permute relabel (functoriality of `map⁺` under
-- `permuteˢ`); it imports only `Strict.Decode.Decode`, so no cycle.
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorPVVRelabel sig _≟X_
  as PVV

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Properties.Ext using (map-∘-cong)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Ext using (just≢nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties.Ext
  using (subst₂-sym-flip; subst₂-trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

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

  -- Absorb a `coeCod` cast on the right factor's cod into the permutation.
  absorbˢ
    : ∀ {ys : List (Fin H.nV)} {s s' : List (Fin H.nV)} (eq : s ≡ s')
        (perm : s' Perm.↭ ys)
        (T : HomS (map vl H.dom) (map vl s))
    → permuteˢ perm ∘ˢ coeCod eq T
      ≈ˢ permuteˢ (subst (Perm._↭ ys) (sym eq) perm) ∘ˢ T
  absorbˢ refl perm T = ≈-refl

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
  -- generator-cast: a `castˢ` of a `genˢ` is the `genˢ` of the `subst₂`-ed
  -- generator.  (`refl refl` matched.)
  gen-cast
    : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (g : FlatGen as bs)
    → castˢ p q (genˢ g) ≡ genˢ (subst₂ FlatGen p q g)
  gen-cast refl refl g = refl

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

--------------------------------------------------------------------------------
-- ## Smart builder for the `atom-ein`/`atom-eout`/`ψ-elab` glue of `TermEmbedˢ`.
--
-- These three inputs are NOT independent data: given the raw endpoint
-- reductions (`ein-red`/`eout-red`), the label-pushed `map-via` cast (`mv`),
-- and the edge-label reduction (`elab-c`), all three are DERIVED uniformly.
-- The `ψ-elab` derivation is the two-cast cancellation `subst₂-trans` +
-- `subst₂-sym-flip`; previously each block-twin (G-side / K-side / braid)
-- hand-rolled the same construction with a locally-duplicated lemma.
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
    trans (sym (subst₂-trans (cong (map J.vlab) (ein-red e)) (sym (mv (H.ein e)))
                             (cong (map J.vlab) (eout-red e)) (sym (mv (H.eout e)))
                             (J.elab (ψ e))))
      (trans (cong (subst₂ FlatGen (sym (mv (H.ein e))) (sym (mv (H.eout e)))) (elab-c e))
             (subst₂-sym-flip (mv (H.ein e)) (mv (H.eout e)) refl))

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
  vlab-φ s = map-∘-cong φ-lab s

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
  --
  -- The search on the relabelled stack PRODUCES `map⁺ φ permH`
  -- (`extract-prefix-pin`), so the two derivations are not independent and no
  -- rigidity/`FinBij` machinery is needed: rewrite `permJ`, let
  -- `permuteˢ-subst` turn the transport into a cast, peel the casts in `_≈̂_`,
  -- and close with the cross-vertex-type relabel `pvv-relabelˢ` (pure
  -- functoriality of `map⁺`, proved by structural induction).

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
        ≈̂⇒castˢ
          (≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (trans (cong RJ.permuteˢ pinned)
                                       (RJ.permuteˢ-subst mpp lift))))
          (≈̂-trans cast-≈̂
                   (castˢ⇒≈̂ P Qφ (PVV.pvv-relabelˢ φ vlJ vlH φ-lab permH P Qφ))))
          P qq
        where
          mpp = map-++ φ (H.ein e) restH
          lift = PermProp.map⁺ φ permH

          -- `pvv-relabelˢ`'s codomain proof, at the UNSPLIT `map φ (ein ++ rest)`.
          Qφ : map vlJ (map φ (H.ein e ++ restH)) ≡ map vlH (H.ein e ++ restH)
          Qφ = trans (cong (map vlJ) mpp) qq

          pinned : pJ ≡ subst (λ z → map φ sH Perm.↭ z) mpp lift
          pinned = extract-prefix-pin φ φ-inj (H.ein e) sH restH permH pJ eqH eJ


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
    viâ (≈̂-trans (cast-≈̂ {p = pDom} {q = pCod})
                 (cast-≈̂ {p = refl} {q = sym (map-++ vlJ (J.eout (ψ e)) restJ)}))
        (∘-resp-≈̂ box-part jperm-part)
        (cast-≈̂ {p = refl} {q = sym (map-++ vlH (H.eout e) restH)})
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
      box-part = castˢ⇒≈̂ Mmid Qbox (box-emb e restH restJ restJ≡ rest-lab Mmid Qbox)

      -- PERM twin: `Jperm ≈̂ Hperm` (the K-step content is `perm-emb`).
      jperm-part : Jperm ≈̂ Hperm
      jperm-part =
        ≈̂-trans (cast-≈̂ {p = refl} {q = map-++ vlJ (J.ein (ψ e)) restJ})
        (≈̂-trans (castˢ⇒≈̂ pDom Qp (perm-emb e sH restH permH eqH restJ permJ eqJ pDom Qp))
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
  ... | just (restH , permH) | nothing =
        ⊥-elim (just≢nothing
          (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
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
      goal = ∘-cast-resp pDom pMid pCod recTwin headTwin

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

module Equivariantˢ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  -- `permuteˢ (trans p q) = permuteˢ q ∘ˢ permuteˢ p` (definitional).
  pvv-transˢ
    : ∀ {xs ys zs : List (Fin H.nV)} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → permuteˢ (Perm.trans p q) ≈ˢ permuteˢ q ∘ˢ permuteˢ p
  pvv-transˢ p q = ≈-refl

  -- The two inverse laws are K-FREE (`Perm′.permuteˢ-inv-left/right`,
  -- structural on the derivation); re-exported here under the names the
  -- interchange/tensor cone consumes.
  pvv-inverse-leftˢ
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permuteˢ (Perm.↭-sym ρ) ∘ˢ permuteˢ ρ ≈ˢ idˢ
  pvv-inverse-leftˢ = permuteˢ-inv-left

  pvv-inverse-rightˢ
    : ∀ {xs ys : List (Fin H.nV)} (ρ : xs Perm.↭ ys)
    → permuteˢ ρ ∘ˢ permuteˢ (Perm.↭-sym ρ) ≈ˢ idˢ
  pvv-inverse-rightˢ = permuteˢ-inv-right

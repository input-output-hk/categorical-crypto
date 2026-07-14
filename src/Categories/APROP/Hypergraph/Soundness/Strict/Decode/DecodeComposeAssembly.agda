{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict decoder `∘`-SHAPE (part (I)ˢ), Stage 3: the FULL assembly.
--
--   decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f      (modulo boundary casts)
--
-- This is the strict twin of `Discharge.Sub.DecodeComposePruned.decodeP-∘-shape`
-- (~650 LOC non-strict).  All foundations now exist:
--   * `TermEmbedˢ` (DecodeComposeS2): the block twins, at φ = injL / remapP;
--   * `process-edges-equivariantˢ` (StackEquiv): the K-side equivariance
--     keystone;
--   * `run-split-atˢ` (DecodeCompose §1): the run-split;
--   * `perm-rigidˢ` (PermSupport) on `Unique` cods + the strict `castˢ` kit.
--
-- The non-strict `subst₂ HomTerm`/`unflatten`/`coe-cod` plumbing collapses to
-- the strict `castˢ` kit (refl-matching + UIP), so the proof is materially
-- shorter than the non-strict original.
--
-- STATEMENT (boundary-cast form).  The headline `decodePˢ`-equation is stated
-- with abstract boundary-cast proofs (`dom≡`/`cod≡`/`mid≡`), exactly as the
-- caller's `Decoder`/`Decode` boundary casts: the boundary objects align
-- definitionally (`C.dom = map injL G.dom`, `C.cod = map remapP K.cod`,
-- `C.nE = G.nE + K.nE`), so the proof is unconditional in those proofs.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeComposeAssembly
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range; map-via-inj)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Util.Prune using (count-non)
import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv using (inject+-inj)
import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig as Lin

open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP; process-edges-↑ˡ-pure-L)
import Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP sig as LP

open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_ public

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig
  using (Linear⇒cod-Unique)
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  using (module Support)
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorPVVRelabel sig _≟X_ as PVV
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueProp
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## The assembly module.

module ComposeShape {A B C₀ : ObjTerm} (g : HomTerm B C₀) (f : HomTerm A B) where

  G K : Hypergraph FlatGen
  G = ⟪ f ⟫
  K = ⟪ g ⟫
  module G = Hypergraph G
  module K = Hypergraph K

  bdy : codL G ≡ domL K
  bdy = trans (⟪⟫-codL f) (sym (⟪⟫-domL g))

  Chg : Hypergraph FlatGen
  Chg = hComposeP G K bdy
  module C = Hypergraph Chg

  lin-G : Lin.Linear G
  lin-G = ⟪⟫-LinearP f
  lin-K : Lin.Linear K
  lin-K = ⟪⟫-LinearP g
  lin-C : Lin.Linear Chg
  lin-C = ⟪⟫-LinearP (g ∘ f)

  open hComposeP-impl G K bdy
    using ( injL; remapP; map-via-remapP; vlab-injL; remapP-vlab
          ; vlab-P
          ; ein-c-inj₁-red; eout-c-inj₁-red; elab-c-inj₁
          ; ein-c-inj₂-red; eout-c-inj₂-red; elab-c-inj₂ )

  cn : ℕ
  cn = count-non K.dom

  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = LP.remapP-injective G K bdy lin-G lin-K

  ----------------------------------------------------------------------
  -- Run modules.
  module RG = Run G
  module RK = Run K
  module RC = Run Chg
  module EC = EquivStep Chg

  ----------------------------------------------------------------------
  -- Edge blocks.  `range C.nE = gblk ++ kblk` (range-++).

  gblk kblk : List (Fin C.nE)
  gblk = map (_↑ˡ K.nE) (range G.nE)
  kblk = map (G.nE ↑ʳ_)  (range K.nE)

  range-eq : range C.nE ≡ gblk ++ kblk
  range-eq = Inv.range-++ G.nE K.nE

  ----------------------------------------------------------------------
  -- Local `subst₂ FlatGen` cancellation (refl-matched; avoids the heavy
  -- non-strict `HomTermTransport` import).

  private
    s2-cancel
      : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os')
          {is'' os'' : List X} (p' : is'' ≡ is') (q' : os'' ≡ os')
          (z : FlatGen is os)
      → subst₂ FlatGen (trans p (sym p')) (trans q (sym q')) z
        ≡ subst₂ FlatGen (sym p') (sym q') (subst₂ FlatGen p q z)
    s2-cancel refl refl refl refl z = refl

    s2-cancel′
      : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os') (z : FlatGen is os)
      → subst₂ FlatGen (sym p) (sym q) (subst₂ FlatGen p q z) ≡ z
    s2-cancel′ refl refl z = refl

  ----------------------------------------------------------------------
  -- ## Block-twin embedding data.

  -- ### G-side: φ = injL, ψ = _↑ˡ K.nE, H = G, J = C.

  atom-einG : ∀ eG → map C.vlab (C.ein (eG ↑ˡ K.nE)) ≡ map G.vlab (G.ein eG)
  atom-einG eG = trans (cong (map vlab-P) (ein-c-inj₁-red eG))
                       (sym (map-via-inj vlab-injL (G.ein eG)))

  atom-eoutG : ∀ eG → map C.vlab (C.eout (eG ↑ˡ K.nE)) ≡ map G.vlab (G.eout eG)
  atom-eoutG eG = trans (cong (map vlab-P) (eout-c-inj₁-red eG))
                        (sym (map-via-inj vlab-injL (G.eout eG)))

  ψ-elabG : ∀ eG → subst₂ FlatGen (atom-einG eG) (atom-eoutG eG) (C.elab (eG ↑ˡ K.nE))
                 ≡ G.elab eG
  ψ-elabG eG =
    trans (s2-cancel
             (cong (map vlab-P) (ein-c-inj₁-red eG))
             (cong (map vlab-P) (eout-c-inj₁-red eG))
             (map-via-inj vlab-injL (G.ein eG))
             (map-via-inj vlab-injL (G.eout eG))
             (C.elab (eG ↑ˡ K.nE)))
          (trans (cong (subst₂ FlatGen
                          (sym (map-via-inj vlab-injL (G.ein eG)))
                          (sym (map-via-inj vlab-injL (G.eout eG))))
                       (elab-c-inj₁ eG))
                 (s2-cancel′
                    (map-via-inj vlab-injL (G.ein eG))
                    (map-via-inj vlab-injL (G.eout eG))
                    (G.elab eG)))

  module TG = TermEmbedˢ {H = G} {J = Chg}
                injL (inject+-inj cn)
                vlab-injL
                (_↑ˡ K.nE) ein-c-inj₁-red eout-c-inj₁-red
                atom-einG atom-eoutG ψ-elabG

  -- ### K-side: φ = remapP, ψ = G.nE ↑ʳ_, H = K, J = C.

  atom-einK : ∀ eK → map C.vlab (C.ein (G.nE ↑ʳ eK)) ≡ map K.vlab (K.ein eK)
  atom-einK eK = trans (cong (map vlab-P) (ein-c-inj₂-red eK))
                       (sym (map-via-remapP (K.ein eK)))

  atom-eoutK : ∀ eK → map C.vlab (C.eout (G.nE ↑ʳ eK)) ≡ map K.vlab (K.eout eK)
  atom-eoutK eK = trans (cong (map vlab-P) (eout-c-inj₂-red eK))
                        (sym (map-via-remapP (K.eout eK)))

  ψ-elabK : ∀ eK → subst₂ FlatGen (atom-einK eK) (atom-eoutK eK) (C.elab (G.nE ↑ʳ eK))
                 ≡ K.elab eK
  ψ-elabK eK =
    trans (s2-cancel
             (cong (map vlab-P) (ein-c-inj₂-red eK))
             (cong (map vlab-P) (eout-c-inj₂-red eK))
             (map-via-remapP (K.ein eK))
             (map-via-remapP (K.eout eK))
             (C.elab (G.nE ↑ʳ eK)))
          (trans (cong (subst₂ FlatGen
                          (sym (map-via-remapP (K.ein eK)))
                          (sym (map-via-remapP (K.eout eK))))
                       (elab-c-inj₂ eK))
                 (s2-cancel′
                    (map-via-remapP (K.ein eK))
                    (map-via-remapP (K.eout eK))
                    (K.elab eK)))

  module TK = TermEmbedˢ {H = K} {J = Chg}
                remapP remapP-injective
                remapP-vlab
                (G.nE ↑ʳ_) ein-c-inj₂-red eout-c-inj₂-red
                atom-einK atom-eoutK ψ-elabK

  ----------------------------------------------------------------------
  -- ## Run-split + equivariance ingredients.

  -- The strict post-G stack.
  after-G : List (Fin C.nV)
  after-G = proj₁ (RC.process-edgesˢ gblk C.dom)

  s_G_final : List (Fin G.nV)
  s_G_final = proj₁ (RG.process-edgesˢ (range G.nE) G.dom)

  -- `after-G ≡ map injL s_G_final`.  The strict stack = the non-strict stack
  -- (`RC.stacks-agree` / `RG.stacks-agree`); the non-strict shape is
  -- `process-edges-↑ˡ-pure-L`.
  after-G-≡ : after-G ≡ map injL s_G_final
  after-G-≡ =
    trans (RC.stacks-agree gblk C.dom)
    (trans (cong proj₁ (proj₂ (process-edges-↑ˡ-pure-L G K bdy lin-G lin-K
                                 (range G.nE) G.dom)))
           (cong (map injL) (sym (RG.stacks-agree (range G.nE) G.dom))))

  -- The boundary permutation `after-G ↭ map remapP K.dom`.  Needs the
  -- final-stack permutation of `f` (`finalPermˢ f`) lifted through `injL`,
  -- then `map-remapP-K-dom`.
  perm-f : RG.s-finˢ Perm.↭ G.cod
  perm-f = finalPermˢ f

  after-G-↭ : after-G Perm.↭ map remapP K.dom
  after-G-↭ =
    Perm.↭-trans (Perm.↭-reflexive after-G-≡)
      (Perm.↭-trans (PermProp.map⁺ injL perm-f)
        (Perm.↭-reflexive (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))))

  -- Reservoir on the strict post-G stack (transported from non-strict).
  reservoir-K : SUR.Reservoir≤1 Chg kblk after-G
  reservoir-K =
    subst (SUR.Reservoir≤1 Chg kblk) (sym (RC.stacks-agree gblk C.dom))
      (SUR.reservoir-split Chg gblk kblk C.dom
        (SUR.dom-reservoir-prov Chg (proj₂ lin-C) (gblk ++ kblk)
          (Perm.↭-reflexive (sym (Inv.range-++ G.nE K.nE)))))

  -- The K-side equivariance: the K-block on `after-G` conjugates onto the
  -- canonical `map remapP K.dom` stack.
  equiv-K = EC.process-edges-equivariantˢ kblk after-G-↭ reservoir-K
  ρf-K = proj₁ equiv-K
  equiv-K-eq = proj₂ equiv-K

  -- `Unique` codomains for the perm-coherence steps.
  uCcod : Unique C.cod
  uCcod = Linear⇒cod-Unique Chg lin-C
  uRemapKdom : Unique (map remapP K.dom)
  uRemapKdom =
    subst Unique (sym (LP.map-remapP-K-dom G K bdy lin-G lin-K))
      (UniqueProp.map⁺ (λ {x} {y} → inject+-inj cn {x} {y})
                       (Linear⇒cod-Unique G lin-G))

  ----------------------------------------------------------------------
  -- ## Perm-coherence on `Fin C.nV` (the strict `permC-coh`/`permRemap-coh`).

  private
    permˢ-K-C : Support.PermK (Fin C.nV) C.vlab
    permˢ-K-C = PK.permˢ-K (Fin C.nV) _≟F_ C.vlab

    -- two derivations into the SAME `Unique` stack give `permuteˢ`-equal terms.
    permC-coh
      : ∀ {s : List (Fin C.nV)} → Unique C.cod
      → (p q : s Perm.↭ C.cod)
      → RC.permuteˢ p ≈ˢ RC.permuteˢ q
    permC-coh u p q = Support.perm-rigidˢ (Fin C.nV) C.vlab permˢ-K-C u p q

    permRemap-coh
      : ∀ {s : List (Fin C.nV)} → Unique (map remapP K.dom)
      → (p q : s Perm.↭ map remapP K.dom)
      → RC.permuteˢ p ≈ˢ RC.permuteˢ q
    permRemap-coh u p q = Support.perm-rigidˢ (Fin C.nV) C.vlab permˢ-K-C u p q

  ----------------------------------------------------------------------
  -- ## The strict cross-vertex-type relabel `pvv-relabelˢ` (strict twin of
  -- the non-strict `HomTermTransport.pvv-relabel`).  Routes a `Fin nJ`-level
  -- permute of `map⁺ φ p` onto the `Fin nH`-level permute of `p` via §0
  -- `permuteˢ-X` (both sides) + `permˢ-K-X`, whose evaluated-bijection
  -- premise is the `eval-map⁺`/`subst₂-FinBij-∘` chain.
  --
  -- This is the SAME relabel as the ⊗-shape's; it lives standalone in
  -- `Strict.Tensor.TensorPVVRelabel` (imported above as `PVV`) so both the
  -- `∘`-shape (here) and the ⊗-shape (`TensorBraid`/`TensorKBlockFinal`)
  -- consume the single copy.  Call sites below use `PVV.pvv-relabelˢ`.

  ----------------------------------------------------------------------
  -- ## Run-split (strict) + the cast-absorb lemma.

  module RB = RunBlocks Chg

  -- Term abbreviations.
  vlC : Fin C.nV → X
  vlC = C.vlab

  Pcomposite : HomS (map vlC C.dom) (map vlC RC.s-finˢ)
  Pcomposite = proj₂ (RC.process-edgesˢ (range C.nE) C.dom)

  gterm : HomS (map vlC C.dom) (map vlC after-G)
  gterm = proj₂ (RC.process-edgesˢ gblk C.dom)

  kterm-aG : HomS (map vlC after-G) (map vlC (proj₁ (RC.process-edgesˢ kblk after-G)))
  kterm-aG = proj₂ (RC.process-edgesˢ kblk after-G)

  kterm-canon : HomS (map vlC (map remapP K.dom))
                     (map vlC (proj₁ (RC.process-edgesˢ kblk (map remapP K.dom))))
  kterm-canon = proj₂ (RC.process-edgesˢ kblk (map remapP K.dom))

  PCˢ : HomS (map vlC RC.s-finˢ) (map vlC C.cod)
  PCˢ = RC.permuteˢ (finalPermˢ (g ∘ f))

  -- run-split: the composite run factors as `(kterm-aG ∘ˢ gterm)` under a cod
  -- cast `E₀` (the post-`kblk` stack equals the composite final stack).
  E₀ : proj₁ (RC.process-edgesˢ kblk after-G) ≡ RC.s-finˢ
  E₀ = trans (sym (RB.pe-stack-++ˢ gblk kblk C.dom))
             (cong (λ z → proj₁ (RC.process-edgesˢ z C.dom)) (sym range-eq))

  run-split : Pcomposite ≈ˢ RB.coeCod E₀ (kterm-aG ∘ˢ gterm)
  run-split = RB.run-split-atˢ gblk kblk range-eq C.dom

  -- absorb a `coeCod` cast on the right factor's cod into the permutation.
  private
    absorbˢ
      : ∀ {ys : List (Fin C.nV)} {s s' : List (Fin C.nV)} (eq : s ≡ s')
          (perm : s' Perm.↭ ys)
          (T : HomS (map vlC C.dom) (map vlC s))
      → RC.permuteˢ perm ∘ˢ RB.coeCod eq T
        ≈ˢ RC.permuteˢ (subst (Perm._↭ ys) (sym eq) perm) ∘ˢ T
    absorbˢ refl perm T = ≈-refl

  ----------------------------------------------------------------------
  -- ## The core composite equation (strict mirror of `Pcomp-eq`).

  -- The absorbed final permutation, on the post-`kblk` stack.
  perm-C2ˢ : proj₁ (RC.process-edgesˢ kblk after-G) Perm.↭ C.cod
  perm-C2ˢ = subst (Perm._↭ C.cod) (sym E₀) (finalPermˢ (g ∘ f))

  -- The conjugating permutation `permuteˢ after-G-↭`.
  permAG : HomS (map vlC after-G) (map vlC (map remapP K.dom))
  permAG = RC.permuteˢ after-G-↭

  -- `Xcˢ` / `Ycˢ` (will become the K-part / G-part decoders).
  Ycˢ : HomS (map vlC C.dom) (map vlC (map remapP K.dom))
  Ycˢ = permAG ∘ˢ gterm

  Xcˢ : HomS (map vlC (map remapP K.dom)) (map vlC C.cod)
  Xcˢ = RC.permuteˢ perm-C2ˢ ∘ˢ (RC.permuteˢ (Perm.↭-sym ρf-K) ∘ˢ kterm-canon)

  private
    -- reassoc: A ∘ ((B ∘ (Kt ∘ Ct)) ∘ Gt) ≈ (A ∘ (B ∘ Kt)) ∘ (Ct ∘ Gt).
    reassocˢ
      : ∀ {o1 o2 o2' o3 o4 o5 : List X}
          (Aᵗ : HomS o4 o5) (Bᵗ : HomS o3 o4) (Ktᵗ : HomS o2' o3)
          (Ctᵗ : HomS o2 o2') (Gtᵗ : HomS o1 o2)
      → Aᵗ ∘ˢ ((Bᵗ ∘ˢ (Ktᵗ ∘ˢ Ctᵗ)) ∘ˢ Gtᵗ)
        ≈ˢ (Aᵗ ∘ˢ (Bᵗ ∘ˢ Ktᵗ)) ∘ˢ (Ctᵗ ∘ˢ Gtᵗ)
    reassocˢ Aᵗ Bᵗ Ktᵗ Ctᵗ Gtᵗ =
      ≈-trans (∘-resp ≈-refl assocˢ)
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
               (≈-sym assocˢ)))

  Pcomp-eqˢ : PCˢ ∘ˢ Pcomposite ≈ˢ Xcˢ ∘ˢ Ycˢ
  Pcomp-eqˢ =
    ≈-trans (∘-resp ≈-refl run-split)
    -- PCˢ ∘ coeCod E₀ (kterm-aG ∘ gterm)
    (≈-trans (absorbˢ E₀ (finalPermˢ (g ∘ f)) (kterm-aG ∘ˢ gterm))
    -- permuteˢ perm-C2ˢ ∘ (kterm-aG ∘ gterm)
    (≈-trans (∘-resp ≈-refl (∘-resp equiv-K-eq ≈-refl))
    -- permuteˢ perm-C2ˢ ∘ ((permuteˢ(↭-sym ρf-K) ∘ (kterm-canon ∘ permAG)) ∘ gterm)
      (reassocˢ (RC.permuteˢ perm-C2ˢ)
                (RC.permuteˢ (Perm.↭-sym ρf-K))
                kterm-canon permAG gterm)))

  ----------------------------------------------------------------------
  -- ## Sub-decoder run-terms and final permutes.

  pterm-f : HomS (map G.vlab G.dom) (map G.vlab s_G_final)
  pterm-f = proj₂ (RG.process-edgesˢ (range G.nE) G.dom)

  s_K_final : List (Fin K.nV)
  s_K_final = proj₁ (RK.process-edgesˢ (range K.nE) K.dom)

  pterm-g : HomS (map K.vlab K.dom) (map K.vlab s_K_final)
  pterm-g = proj₂ (RK.process-edgesˢ (range K.nE) K.dom)

  perm-g : RK.s-finˢ Perm.↭ K.cod
  perm-g = finalPermˢ g

  PFˢ : HomS (map G.vlab s_G_final) (map G.vlab G.cod)
  PFˢ = RG.permuteˢ perm-f

  PGˢ : HomS (map K.vlab s_K_final) (map K.vlab K.cod)
  PGˢ = RK.permuteˢ perm-g

  private
    -- 2-sided `permuteˢ`-of-subst₂ (C-level); refl-matched.
    permuteˢ-subst₂-C
      : ∀ {xs xs' ys ys' : List (Fin C.nV)} (a : xs ≡ xs') (b : ys ≡ ys')
          (r : xs Perm.↭ ys)
      → RC.permuteˢ (subst₂ Perm._↭_ a b r)
        ≡ castˢ (cong (map vlC) a) (cong (map vlC) b) (RC.permuteˢ r)
    permuteˢ-subst₂-C refl refl r = refl

  -- Boundary equalities for the G-block.
  map-rKd : map remapP K.dom ≡ map injL G.cod
  map-rKd = LP.map-remapP-K-dom G K bdy lin-G lin-K

  M1G : map vlC after-G ≡ map G.vlab s_G_final
  M1G = trans (cong (map vlC) after-G-≡) (TG.vlab-φ s_G_final)

  midG-cod : map vlC (map remapP K.dom) ≡ map G.vlab G.cod
  midG-cod = trans (cong (map vlC) map-rKd) (TG.vlab-φ G.cod)

  -- the injL-lifted canonical perm for the G-block (strict `injf-↭`).
  injf-↭ : after-G Perm.↭ map remapP K.dom
  injf-↭ = subst₂ Perm._↭_ (sym after-G-≡) (sym map-rKd) (PermProp.map⁺ injL perm-f)

  ----------------------------------------------------------------------
  -- G-block permute: `castˢ M1G midG-cod permAG ≈ˢ PFˢ`.

  private
    gperm' : castˢ M1G midG-cod permAG ≈ˢ PFˢ
    gperm' =
      ≈-trans (cast-resp M1G midG-cod (permRemap-coh uRemapKdom after-G-↭ injf-↭))
      (≈-trans (≡⇒≈ˢ (cong (castˢ M1G midG-cod)
                        (permuteˢ-subst₂-C (sym after-G-≡) (sym map-rKd)
                           (PermProp.map⁺ injL perm-f))))
      (≈-trans (≡⇒≈ˢ (cast-fuse (cong (map vlC) (sym after-G-≡)) M1G
                                (cong (map vlC) (sym map-rKd)) midG-cod
                                (RC.permuteˢ (PermProp.map⁺ injL perm-f))))
      (≈-trans (≡⇒≈ˢ (cast-irrel
                        (trans (cong (map vlC) (sym after-G-≡)) M1G)
                        Pdom
                        (trans (cong (map vlC) (sym map-rKd)) midG-cod)
                        Pcod
                        (RC.permuteˢ (PermProp.map⁺ injL perm-f))))
        (PVV.pvv-relabelˢ injL vlC G.vlab vlab-injL perm-f Pdom Pcod))))
      where
        Pdom : map vlC (map injL s_G_final) ≡ map G.vlab s_G_final
        Pdom = TG.vlab-φ s_G_final
        Pcod : map vlC (map injL G.cod) ≡ map G.vlab G.cod
        Pcod = TG.vlab-φ G.cod

  ----------------------------------------------------------------------
  -- G-block twin: `castˢ (vlab-φ G.dom) M1G gterm ≈ˢ pterm-f`.

  private
    gtwin' : castˢ (TG.vlab-φ G.dom) M1G gterm ≈ˢ pterm-f
    gtwin' = TG.process-edges-term-embˢ (range G.nE) G.dom M1G

  -- Y-twin: `castˢ (vlab-φ G.dom) midG-cod Ycˢ ≈ˢ PFˢ ∘ˢ pterm-f`.
  Yc-twinˢ : castˢ (TG.vlab-φ G.dom) midG-cod Ycˢ ≈ˢ PFˢ ∘ˢ pterm-f
  Yc-twinˢ =
    ≈-trans (∘-cast-split (TG.vlab-φ G.dom) M1G midG-cod permAG gterm)
            (∘-resp gperm' gtwin')

  ----------------------------------------------------------------------
  -- ## The K-block.

  combPˢ : proj₁ (RC.process-edgesˢ kblk (map remapP K.dom)) Perm.↭ C.cod
  combPˢ = Perm.trans (Perm.↭-sym ρf-K) perm-C2ˢ

  -- `Xcˢ ≈ˢ permuteˢ combPˢ ∘ˢ kterm-canon`  (permuteˢ trans = ∘ˢ, reassoc).
  private
    Xc-assocˢ : Xcˢ ≈ˢ RC.permuteˢ combPˢ ∘ˢ kterm-canon
    Xc-assocˢ = ≈-sym assocˢ

  proc-stack-emb-K : proj₁ (RC.process-edgesˢ kblk (map remapP K.dom)) ≡ map remapP s_K_final
  proc-stack-emb-K = TK.proc-stack-embˢ (range K.nE) K.dom

  MK1 : map vlC (proj₁ (RC.process-edgesˢ kblk (map remapP K.dom))) ≡ map K.vlab s_K_final
  MK1 = trans (cong (map vlC) proc-stack-emb-K) (TK.vlab-φ s_K_final)

  remapg-↭ : proj₁ (RC.process-edgesˢ kblk (map remapP K.dom)) Perm.↭ C.cod
  remapg-↭ = subst₂ Perm._↭_ (sym proc-stack-emb-K) refl (PermProp.map⁺ remapP perm-g)

  ----------------------------------------------------------------------
  -- K-block permute: `castˢ MK1 (vlab-φ K.cod) (permuteˢ combPˢ) ≈ˢ PGˢ`.

  private
    kperm' : castˢ MK1 (TK.vlab-φ K.cod) (RC.permuteˢ combPˢ) ≈ˢ PGˢ
    kperm' =
      ≈-trans (cast-resp MK1 (TK.vlab-φ K.cod) (permC-coh uCcod combPˢ remapg-↭))
      (≈-trans (≡⇒≈ˢ (cong (castˢ MK1 (TK.vlab-φ K.cod))
                        (permuteˢ-subst₂-C (sym proc-stack-emb-K) refl
                           (PermProp.map⁺ remapP perm-g))))
      (≈-trans (≡⇒≈ˢ (cast-fuse (cong (map vlC) (sym proc-stack-emb-K)) MK1
                                (cong (map vlC) refl) (TK.vlab-φ K.cod)
                                (RC.permuteˢ (PermProp.map⁺ remapP perm-g))))
      (≈-trans (≡⇒≈ˢ (cast-irrel
                        (trans (cong (map vlC) (sym proc-stack-emb-K)) MK1)
                        Pdom
                        (trans (cong (map vlC) refl) (TK.vlab-φ K.cod))
                        Pcod
                        (RC.permuteˢ (PermProp.map⁺ remapP perm-g))))
        (PVV.pvv-relabelˢ remapP vlC K.vlab remapP-vlab perm-g Pdom Pcod))))
      where
        Pdom : map vlC (map remapP s_K_final) ≡ map K.vlab s_K_final
        Pdom = TK.vlab-φ s_K_final
        Pcod : map vlC (map remapP K.cod) ≡ map K.vlab K.cod
        Pcod = TK.vlab-φ K.cod

  ----------------------------------------------------------------------
  -- K-block twin: `castˢ (vlab-φ K.dom) MK1 kterm-canon ≈ˢ pterm-g`.

  private
    ktwin' : castˢ (TK.vlab-φ K.dom) MK1 kterm-canon ≈ˢ pterm-g
    ktwin' = TK.process-edges-term-embˢ (range K.nE) K.dom MK1

  -- X-twin: `castˢ (vlab-φ K.dom)(vlab-φ K.cod) Xcˢ ≈ˢ PGˢ ∘ˢ pterm-g`.
  Xc-twinˢ : castˢ (TK.vlab-φ K.dom) (TK.vlab-φ K.cod) Xcˢ ≈ˢ PGˢ ∘ˢ pterm-g
  Xc-twinˢ =
    ≈-trans (cast-resp (TK.vlab-φ K.dom) (TK.vlab-φ K.cod) Xc-assocˢ)
    (≈-trans (∘-cast-split (TK.vlab-φ K.dom) MK1 (TK.vlab-φ K.cod)
                (RC.permuteˢ combPˢ) kterm-canon)
             (∘-resp kperm' ktwin'))

  ----------------------------------------------------------------------
  -- ## The headline `decodePˢ` equation.
  --
  -- All boundary objects align definitionally:
  --   `C.dom = map injL G.dom`, `C.cod = map remapP K.cod`,
  --   `C.nE  = G.nE + K.nE`, and `domL H = map (vlab H) (dom H)`.

  domGF : map vlC C.dom ≡ flatten A
  domGF = ⟪⟫-domL (g ∘ f)

  codGF : map vlC C.cod ≡ flatten C₀
  codGF = ⟪⟫-codL (g ∘ f)

  -- the middle boundary (flatten B), routed through `G.cod`/`map-rKd`.
  midGFᵉ : map vlC (map remapP K.dom) ≡ flatten B
  midGFᵉ = trans (cong (map vlC) map-rKd) (trans (TG.vlab-φ G.cod) (⟪⟫-codL f))

  -- `decodePˢ` cores.
  private
    -- G-part: `castˢ domGF midGFᵉ Ycˢ ≈ˢ decodePˢ f`.
    Gpartˢ : castˢ domGF midGFᵉ Ycˢ ≈ˢ decodePˢ f
    Gpartˢ =
      ≈-trans (≡⇒≈ˢ (cast-irrel
                       domGF (trans (TG.vlab-φ G.dom) (⟪⟫-domL f))
                       midGFᵉ (trans midG-cod (⟪⟫-codL f)) Ycˢ))
      (≈-trans (≡⇒≈ˢ (sym (cast-fuse (TG.vlab-φ G.dom) (⟪⟫-domL f)
                                     midG-cod (⟪⟫-codL f) Ycˢ)))
      (≈-sym (cast-resp (⟪⟫-domL f) (⟪⟫-codL f) (≈-sym Yc-twinˢ))))

    -- K-part: `castˢ midGFᵉ codGF Xcˢ ≈ˢ decodePˢ g`.
    Kpartˢ : castˢ midGFᵉ codGF Xcˢ ≈ˢ decodePˢ g
    Kpartˢ =
      ≈-trans (≡⇒≈ˢ (cast-irrel
                       midGFᵉ (trans (TK.vlab-φ K.dom) (⟪⟫-domL g))
                       codGF (trans (TK.vlab-φ K.cod) (⟪⟫-codL g)) Xcˢ))
      (≈-trans (≡⇒≈ˢ (sym (cast-fuse (TK.vlab-φ K.dom) (⟪⟫-domL g)
                                     (TK.vlab-φ K.cod) (⟪⟫-codL g) Xcˢ)))
      (≈-sym (cast-resp (⟪⟫-domL g) (⟪⟫-codL g) (≈-sym Xc-twinˢ))))

  -- The full strict `∘`-shape.
  decodePˢ-∘-shape : decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
  decodePˢ-∘-shape =
    ≈-trans (cast-resp domGF codGF Pcomp-eqˢ)
    (≈-trans (∘-cast-split domGF midGFᵉ codGF Xcˢ Ycˢ)
             (∘-resp Kpartˢ Gpartˢ))

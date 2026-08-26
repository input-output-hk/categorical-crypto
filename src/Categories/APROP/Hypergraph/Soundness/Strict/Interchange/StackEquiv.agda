{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Strict decoder STACK-EQUIVARIANCE (the K-side relabelling keystone).
--
-- Running the strict decoder's `process-edgesˢ` on a PERMUTED input stack
-- equals the run on the original stack conjugated by `permuteˢ`:
--
--   pe-termˢ qs s'
--     ≈ˢ permuteˢ (↭-sym ρf) ∘ˢ ( pe-termˢ qs s ∘ˢ permuteˢ ρ )
--
-- This is the strict twin of the former non-strict `StackEquivariance`'s
-- `process-edges-equivariant`.  The genuinely-new strict content is the
-- per-edge FIRE-box naturality (`fire-mid-equivariantˢ`), discharged here
-- by a direct `interchangeᵛ` computation in the presented
-- strict SMC — NO `box-of`/`unflatten-++-≅` detour.
--
-- The term-FREE inputs (`fire-stable-*`, `residual-recon`, `fire-μ`,
-- the `extract-prefix` determinism) are REUSED verbatim from the
-- non-strict leaves: the strict and non-strict runs walk the SAME stacks
-- (`Run.stacks-agree`), so the reservoir / `Unique` plumbing transfers.
-- The derivation algebra uses `pvv-transˢ` / `pvv-inverse-{left,right}ˢ`
-- (the `Equivariantˢ` foundation in the strict `DecodeCompose`); the locating-permute
-- coherence is consumed by the vertex-level `permˢ-K-H` directly (the
-- strict `permuteˢ` is vertex-level, so the non-strict `map⁺-lift-≅↭` step
-- DISAPPEARS).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig _≟X_ public
open import Categories.Morphism.Reasoning SCat using (pullˡ; pullʳ)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig _≟X_
  using (module EdgeStepView)

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig as SU
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR

open import Categories.PermuteCoherence.Rigid using (_≅↭_)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Ext using (just≢nothing)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## The equivariance module, per hypergraph.

module EquivStep (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public
  open Equivariantˢ H public using (pvv-transˢ; pvv-inverse-leftˢ; pvv-inverse-rightˢ)

  open Restrict (Fin H.nV) vl
    using ( idᵛ; _∘ᵛ_; _⊗ᵛ_; _≈ᵛ_; permuteᵛ; permuteᵛ-frameˡ
          ; ⊗-respᵛ; interchangeᵛ )

  private
    _≟V_ : DecidableEquality (Fin H.nV)
    _≟V_ = _≟F_

    permˢ-K-H : PK.Support.PermK (Fin H.nV) H.vlab
    permˢ-K-H = PK.permˢ-K (Fin H.nV) _≟V_ H.vlab

  ----------------------------------------------------------------------
  -- The strict fired layer + `EdgeStepRˢ` graph view, shared with
  -- `Strict.Interchange.SwapCore` via the `EdgeStepRel` leaf.
  ----------------------------------------------------------------------

  open EdgeStepView H public

  ----------------------------------------------------------------------
  -- FIRING STABILITY under a stack permutation (term-free; reused
  -- verbatim from the former non-strict `StackEquivariance`).
  ----------------------------------------------------------------------

  fire-stable-just
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {restH : List (Fin H.nV)} (permH : s Perm.↭ H.ein e ++ restH)
    → extract-prefix (H.ein e) s ≡ just (restH , permH)
    → Σ[ restH' ∈ List (Fin H.nV) ]
      Σ[ permH' ∈ s' Perm.↭ H.ein e ++ restH' ]
        extract-prefix (H.ein e) s' ≡ just (restH' , permH')
        × restH Perm.↭ restH'
  fire-stable-just e {s} {s'} ρ {restH} permH eqH =
    let step = extract-prefix-↭-residual (H.ein e) s' restH (Perm.↭-trans ρ permH)
    in proj₁ step , proj₁ (proj₂ step)
       , proj₁ (proj₂ (proj₂ step)) , proj₂ (proj₂ (proj₂ step))

  fire-stable-nothing
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → extract-prefix (H.ein e) s ≡ nothing
    → extract-prefix (H.ein e) s' ≡ nothing
  fire-stable-nothing e {s} {s'} ρ eqH =
    extract-prefix-↭-nothing (H.ein e) s s' (Perm.↭-sym ρ) eqH

  ----------------------------------------------------------------------
  -- BOX-CORE NATURALITY (the genuine strict box-naturality content).
  -- The box `genˢ (elab e) ⊗ᵛ idᵛ {rest}` is natural in `rest` under a
  -- residual permutation `μ`: K-free (`interchangeᵛ` + `pvv-inverse-*ˢ`).
  ----------------------------------------------------------------------

  box-core-natᵛ
    : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → genˢ (H.elab e) ⊗ᵛ idᵛ {restH'}
      ≈ᵛ (idᵛ {H.eout e} ⊗ᵛ permuteᵛ μ)
           ∘ᵛ ( (genˢ (H.elab e) ⊗ᵛ idᵛ {restH})
                ∘ᵛ (idᵛ {H.ein e} ⊗ᵛ permuteᵛ (Perm.↭-sym μ)) )
  box-core-natᵛ e μ =
    ≈-sym
      -- (id{eout}⊗ᵛpermμ) ∘ᵛ ((genˢ⊗ᵛid{restH}) ∘ᵛ (id{ein}⊗ᵛpermute(↭μ)))
      (≈-trans (∘-resp ≈-refl interchangeᵛ)
      -- (id{eout}⊗ᵛpermμ) ∘ᵛ ((genˢ∘ᵛid{ein}) ⊗ᵛ (id{restH}∘ᵛpermute(↭μ)))
      (≈-trans (∘-resp ≈-refl (⊗-respᵛ idʳ idˡ))
      -- (id{eout}⊗ᵛpermμ) ∘ᵛ (genˢ ⊗ᵛ permute(↭μ))
      (≈-trans interchangeᵛ
      -- (id{eout}∘ᵛgenˢ) ⊗ᵛ (permμ ∘ᵛ permute(↭μ))
      (⊗-respᵛ idˡ (pvv-inverse-rightˢ μ)))))

  ----------------------------------------------------------------------
  -- The fire layer factors: box-only ∘ˢ locating permute.
  ----------------------------------------------------------------------

  fire-midˢ
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
    → HomS (map vl (H.ein e ++ rest)) (map vl (H.eout e ++ rest))
  fire-midˢ e rest = fire-termˢ e (H.ein e ++ rest) rest Perm.refl

  -- `fire-midˢ` collapsed to the `Restrict`-layer box `genˢ (elab e) ⊗ᵛ
  -- idᵛ {rest}`.  `fire-midˢ e rest` IS `fire-termˢ e _ rest Perm.refl`, so
  -- this is `edge-step-firedᵛ` at the identity wiring.
  fire-midˢ-cast
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
    → fire-midˢ e rest ≈ᵛ genˢ (H.elab e) ⊗ᵛ idᵛ {rest}
  fire-midˢ-cast e rest =
    ≈-trans (edge-step-firedᵛ e rest Perm.refl) idʳ

  -- `fire-termˢ` factors as the `rest`-box after the wiring.  Both sides are
  -- the `Restrict`-layer `firedᵛ e rest perm` (`Decoder.edge-step-firedᵛ`).
  fire-term-factorˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
        (perm : s Perm.↭ H.ein e ++ rest)
    → fire-termˢ e s rest perm ≈ˢ fire-midˢ e rest ∘ˢ permuteˢ perm
  fire-term-factorˢ e s rest perm =
    ≈-trans (edge-step-firedᵛ e rest perm)
            (≈-sym (∘-resp (fire-midˢ-cast e rest) ≈-refl))

  ----------------------------------------------------------------------
  -- FIRE-BOX naturality (the strict `fire-mid-equivariant` twin).  The
  -- residual permutes slide as `idᵛ ⊗ᵛ permuteᵛ` frames (`permuteᵛ-frameˡ`,
  -- cast-free at V level) and the central box commutes via `box-core-natᵛ`.
  -- K-FREE.
  ----------------------------------------------------------------------

  fire-mid-equivariantˢ
    : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → fire-midˢ e restH'
      ≈ᵛ permuteᵛ (PermProp.++⁺ˡ (H.eout e) μ)
           ∘ᵛ ( fire-midˢ e restH
                ∘ᵛ permuteᵛ (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)) )
  fire-mid-equivariantˢ e μ =
    ≈-trans (fire-midˢ-cast e _)
    (≈-trans (box-core-natᵛ e μ)
      (∘-resp (≈-sym (permuteᵛ-frameˡ (H.eout e) μ))
        (∘-resp (≈-sym (fire-midˢ-cast e _))
                (≈-sym (permuteᵛ-frameˡ (H.ein e) (Perm.↭-sym μ))))))

  ----------------------------------------------------------------------
  -- CANONICAL residual reshuffle `fire-μ` + the locating-permute
  -- coherence `locate-coherentˢ` (VERTEX-level; no `map⁺`-lift, since the
  -- strict `permuteˢ` is vertex-level and `permˢ-K-H` consumes a bare
  -- vertex `≅↭`).  Ported from the former non-strict `StackEquivariance`.
  ----------------------------------------------------------------------

  module _ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
           {restH restH' : List (Fin H.nV)}
           (permH  : s  Perm.↭ H.ein e ++ restH)
           (permH' : s' Perm.↭ H.ein e ++ restH')
           (eqH' : extract-prefix (H.ein e) s' ≡ just (restH' , permH'))
           (us' : Unique s')
           where
    private
      xpr = extract-prefix-↭-residual (H.ein e) s' restH (Perm.trans ρ permH)
      restHc  = proj₁ xpr
      permHc  = proj₁ (proj₂ xpr)
      eqHc    = proj₁ (proj₂ (proj₂ xpr))
      rpc     = proj₂ (proj₂ (proj₂ xpr))

      pair-eq : (restHc , permHc) ≡ (restH' , permH')
      pair-eq = just-injective (trans (sym eqHc) eqH')

      restHc≡ : restHc ≡ restH'
      restHc≡ = cong proj₁ pair-eq

    fire-μ : restH Perm.↭ restH'
    fire-μ = subst (restH Perm.↭_) restHc≡ rpc

    private
      recon-collapse
        : ∀ {rc} (pc : s' Perm.↭ H.ein e ++ rc) (rp : restH Perm.↭ rc)
            (req : rc ≡ restH')
            (peq : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) req pc)
        → Perm.trans permH'
            (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym (subst (restH Perm.↭_) req rp)))
          ≅↭ Perm.trans pc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rp))
      recon-collapse pc rp refl refl i = refl

      permHc≡ : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) restHc≡ permHc
      permHc≡ = sym (subst-pair-snd pair-eq)
        where
          subst-pair-snd
            : ∀ {rc : List (Fin H.nV)} {pc : s' Perm.↭ H.ein e ++ rc}
                (pe : (rc , pc) ≡ (restH' , permH'))
            → subst (λ r → s' Perm.↭ H.ein e ++ r) (cong proj₁ pe) pc ≡ permH'
          subst-pair-snd refl = refl

    locate-coherentˢ
      : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
        ≅↭ Perm.trans ρ permH
    locate-coherentˢ = chained
      where
        mid : s' Perm.↭ H.ein e ++ restH
        mid = Perm.trans permHc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rpc))

        half₁ : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)) ≅↭ mid
        half₁ = recon-collapse permHc rpc restHc≡ permHc≡

        half₂ : mid ≅↭ Perm.trans ρ permH
        half₂ = SU.residual-recon (H.ein e) s' restH (Perm.trans ρ permH)
                  (SU.Unique-resp-↭ (Perm.trans ρ permH) us')

        chained
          : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
            ≅↭ Perm.trans ρ permH
        chained i = trans (half₁ i) (half₂ i)

    ------------------------------------------------------------------
    -- The permute reconciliation consumed by the FIRE/FIRE step.
    ------------------------------------------------------------------
    perm-reconcileˢ
      : permuteˢ (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
          ∘ˢ permuteˢ permH'
        ≈ˢ permuteˢ permH ∘ˢ permuteˢ ρ
    perm-reconcileˢ =
      ≈-trans (≈-sym (pvv-transˢ permH'
                       (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))))
        (≈-trans
          (permˢ-K-H
            (Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)))
            (Perm.trans ρ permH)
            locate-coherentˢ)
          (pvv-transˢ ρ permH))

    ------------------------------------------------------------------
    -- FIRE/FIRE term equivariance.
    ------------------------------------------------------------------
    edge-step-fire-equivariantˢ
      : fire-termˢ e s' restH' permH'
        ≈ˢ permuteˢ (PermProp.++⁺ˡ (H.eout e) fire-μ)
              ∘ˢ ( fire-termˢ e s restH permH ∘ˢ permuteˢ ρ )
    edge-step-fire-equivariantˢ =
      ≈-trans (fire-term-factorˢ e s' restH' permH')
      -- fire-midˢ rest' ∘ permuteˢ perm'
      -- (permuteˢ(++eout μ) ∘ (fire-midˢ rest ∘ permuteˢ(++ein(↭μ)))) ∘ permuteˢ perm';
      -- `perm-reconcileˢ` is pulled into the second factor and the mid/perm
      -- pair back into `fire-termˢ`.
      (≈-trans (∘-resp (fire-mid-equivariantˢ e fire-μ) ≈-refl)
        (pullʳ (≈-trans (pullʳ perm-reconcileˢ)
                        (pullˡ (≈-sym (fire-term-factorˢ e s restH permH))))))

  ----------------------------------------------------------------------
  -- `++⁺ˡ` commutes with `↭-sym` (list-induction; from the former
  -- non-strict `StackEquivariance`).
  ----------------------------------------------------------------------
  private
    ++⁺ˡ-↭-sym
      : ∀ (xs : List (Fin H.nV)) {ys zs : List (Fin H.nV)} (p : ys Perm.↭ zs)
      → Perm.↭-sym (PermProp.++⁺ˡ xs p) ≡ PermProp.++⁺ˡ xs (Perm.↭-sym p)
    ++⁺ˡ-↭-sym []       p = refl
    ++⁺ˡ-↭-sym (x ∷ xs) p = cong (Perm.prep x) (++⁺ˡ-↭-sym xs p)

  ----------------------------------------------------------------------
  -- PER-EDGE-STEP equivariance, over the `EdgeStepRˢ` witnesses.
  ----------------------------------------------------------------------
  edge-step-equivariantˢ
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {s'H : List (Fin H.nV)} {tH : HomS (map vl s) (map vl s'H)}
        {s'H' : List (Fin H.nV)} {tH' : HomS (map vl s') (map vl s'H')}
        (wH  : EdgeStepRˢ s e s'H tH) (wH' : EdgeStepRˢ s' e s'H' tH')
        (us' : Unique s')
    → Σ[ ρf ∈ s'H' Perm.↭ s'H ]
        tH' ≈ˢ permuteˢ (Perm.↭-sym ρf) ∘ˢ ( tH ∘ˢ permuteˢ ρ )
  -- SKIP/SKIP.
  edge-step-equivariantˢ e ρ (skipRˢ eqH) (skipRˢ eqH') us' =
    ρ , ≈-sym (≈-trans (∘-resp ≈-refl idˡ) (pvv-inverse-leftˢ ρ))
  -- SKIP/FIRE & FIRE/SKIP: impossible by firing stability.
  edge-step-equivariantˢ e ρ (skipRˢ eqH) (fireRˢ restH' permH' eqH') us' =
    ⊥-elim (just≢nothing (trans (sym eqH') (fire-stable-nothing e ρ eqH)))
  edge-step-equivariantˢ e {s} {s'} ρ (fireRˢ restH permH eqH) (skipRˢ eqH') us' =
    ⊥-elim (just≢nothing
      (let fsj = fire-stable-just e ρ permH eqH
       in trans (sym (proj₁ (proj₂ (proj₂ fsj)))) eqH'))
  -- FIRE/FIRE.
  edge-step-equivariantˢ e {s} {s'} ρ
      (fireRˢ restH permH eqH) (fireRˢ restH' permH' eqH') us' =
        PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym μ)
      , subst (λ z → fire-termˢ e s' restH' permH'
                       ≈ˢ permuteˢ z
                            ∘ˢ ( fire-termˢ e s restH permH ∘ˢ permuteˢ ρ ))
              (sym (trans (++⁺ˡ-↭-sym (H.eout e) (Perm.↭-sym μ))
                          (cong (PermProp.++⁺ˡ (H.eout e))
                                (PermProp.↭-sym-involutive μ))))
              (edge-step-fire-equivariantˢ e ρ permH permH' eqH' us')
    where
      μ : restH Perm.↭ restH'
      μ = fire-μ e ρ permH permH' eqH' us'

  ----------------------------------------------------------------------
  -- MAIN THEOREM — `process-edges-equivariantˢ`.
  --
  -- Induction on `qs`.  Empty: ρf = ρ, terms are idˢ, `pvv-inverse-leftˢ`
  -- closes.  Cons: one `edge-step-equivariantˢ` on the head edge gives the
  -- per-step ρ1 + term relation; recurse on the tail with ρ1; compose the
  -- two sandwiches (the middle permutes telescope through ∘ˢ-reassoc,
  -- leaving the outer `ρ` / `↭-sym ρf` intact).  The `Reservoir≤1`
  -- freshness on the PERMUTED stack `s'` is sourced by the caller and
  -- advanced one strict `edge-stepˢ` per recursion (bridged to the
  -- non-strict `edge-step` via `edge-stack-agree`).
  ----------------------------------------------------------------------
  process-edges-equivariantˢ
    : ∀ (qs : List (Fin H.nE)) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → SUR.Reservoir≤1 H qs s'
    → Σ[ ρf ∈ pe-stackˢ qs s' Perm.↭ pe-stackˢ qs s ]
        pe-termˢ qs s'
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
                ∘ˢ ( pe-termˢ qs s ∘ˢ permuteˢ ρ )
  process-edges-equivariantˢ [] {s} {s'} ρ _ =
    ρ , ≈-sym (≈-trans (∘-resp ≈-refl idˡ) (pvv-inverse-leftˢ ρ))
  process-edges-equivariantˢ (e ∷ qs) {s} {s'} ρ inv
      with edge-step-equivariantˢ e ρ (edge-stepˢ-graph s e) (edge-stepˢ-graph s' e)
              (SUR.Reservoir≤1⇒Unique H (e ∷ qs) s' inv)
  ... | ρ1 , step-eq
      with process-edges-equivariantˢ qs
             {proj₁ (edge-stepˢ s e)} {proj₁ (edge-stepˢ s' e)} ρ1
             (subst (SUR.Reservoir≤1 H qs)
                    (sym (edge-stack-agree s' e))
                    (SUR.edge-step-Reservoir≤1 H e qs s' inv))
  ... | ρf , tail-eq =
        ρf , goal
    where
      s1  = proj₁ (edge-stepˢ s  e)
      s1' = proj₁ (edge-stepˢ s' e)
      tH  = proj₂ (edge-stepˢ s  e)
      tH' = proj₂ (edge-stepˢ s' e)

      mid-collapse : permuteˢ ρ1 ∘ˢ tH' ≈ˢ tH ∘ˢ permuteˢ ρ
      mid-collapse =
        ≈-trans (∘-resp ≈-refl step-eq)
          (≈-trans (≈-sym assocˢ)
            (≈-trans
              (∘-resp (pvv-inverse-rightˢ ρ1) ≈-refl)
              idˡ))

      goal
        : (pe-termˢ qs s1' ∘ˢ tH')
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
                ∘ˢ ( (pe-termˢ qs s1 ∘ˢ tH) ∘ˢ permuteˢ ρ )
      goal =
        ≈-trans (∘-resp tail-eq (≈-refl {f = tH'}))
                (pullʳ (≈-trans (pullʳ mid-collapse) (≈-sym assocˢ)))

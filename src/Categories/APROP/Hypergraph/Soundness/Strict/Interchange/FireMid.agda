{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- FINAL ASSEMBLY of part (II)ˢ — the UNCONDITIONAL `fire-mid-interchangeˢ` and
-- `run-interchange₀ˢ`.
--
-- This assembles the located normal-form pieces:
-- the per-order located normal forms `nf-genᵛ` (a single, block-symmetric
-- single-order chase), instantiated for the two firing orders, then threaded
-- through `cross-NFᵛ` with the proven `vin-cohᵛ`/`vout-cohᵛ` to give
-- the both-fire core
-- `fire-mid-interchangeˢ`.  Instantiating `SwapCoreRun.RunInterchange` with
-- it yields the UNCONDITIONAL `run-interchange₀ˢ`.  The whole assembly runs
-- in the `Restrict` layer (F7): the located block shapes `(A ++ A') ++ Rl`
-- ARE the vertex stacks the located derivations produce, so the block frames
-- carry no `map-++` transport.  The linearity-free bricks (kernel + located
-- coherences) live in submodule `FMS`; the capstone `fire-mid-interchangeˢ`,
-- which needs `Linear H`, is the final `module _ (H lin)`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.FireMid
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.Morphism.Reasoning SCat using (pullʳ)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCoreRun sig _≟X_ as SCR
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig _≟X_ as PC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_ as DSS

import Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb sig
  as FMIC
import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig
  as SU
open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using (++-cancelˡ)

open import Data.Fin using (Fin)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- ===== submodule FMS =====
--------------------------------------------------------------------------------

module FMS (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  open Restrict (Fin H.nV) vl
    using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; σᵛ; _≈ᵛ_; permuteᵛ
          ; ⊗-respᵛ; interchangeᵛ; ⊗id-distᵛ; σ-natᵛ; σ-σᵛ )

  ------------------------------------------------------------------------
  -- The LOCATED two-box interchange kernel.  Two boxes `g : A → B`,
  -- `g' : A' → B'` sitting side by side, framed by a residual `R`, commute
  -- through the block braidings on their (co)domains:
  --
  --   ((g' ⊗ᵛ g) ⊗ᵛ idᵛ{R})
  --     ≈ᵛ ((σᵛ B B' ⊗ᵛ idᵛ{R}) ∘ᵛ ((g ⊗ᵛ g') ⊗ᵛ idᵛ{R})) ∘ᵛ (σᵛ A' A ⊗ᵛ idᵛ{R})
  --
  -- This is the genuine N-content of the both-fire interchange, already
  -- located at the 3-block level; σ-conjugation lifted by `_⊗ᵛ idᵛ{R}`, and
  -- K-free.
  ------------------------------------------------------------------------

  box-crossᵛ
    : ∀ {A B A' B' : List (Fin H.nV)} (g : HomV A B) (g' : HomV A' B')
        (R : List (Fin H.nV))
    → (g' ⊗ᵛ g) ⊗ᵛ idᵛ {R}
      ≈ᵛ ((σᵛ B B' ⊗ᵛ idᵛ {R}) ∘ᵛ ((g ⊗ᵛ g') ⊗ᵛ idᵛ {R}))
           ∘ᵛ (σᵛ A' A ⊗ᵛ idᵛ {R})
  box-crossᵛ {A} {B} {A'} {B'} g g' R =
    ≈-trans (⊗-respᵛ conj ≈-refl)
      (≈-trans (⊗id-distᵛ (σᵛ B B') ((g ⊗ᵛ g') ∘ᵛ σᵛ A' A))
        (≈-trans (∘-resp ≈-refl (⊗id-distᵛ (g ⊗ᵛ g') (σᵛ A' A)))
          (≈-sym assocˢ)))
    where
      conj : g' ⊗ᵛ g ≈ᵛ σᵛ B B' ∘ᵛ ((g ⊗ᵛ g') ∘ᵛ σᵛ A' A)
      conj =
        ≈-sym
          (≈-trans (≈-sym assocˢ)
            (≈-trans (∘-resp σ-natᵛ ≈-refl)
              (≈-trans (pullʳ σ-σᵛ) idʳ)))

  ------------------------------------------------------------------------
  -- THE ABSTRACT LOCATED-INTERCHANGE CORE (the genuine N-content).
  --
  -- Two boxes `g , g'` sitting side by side over a residual `Rl`, located by
  -- the two firing orders' input frames `Lin₁ / Lin₂` and output frames
  -- `Lout₁ / Lout₂`, with the reshuffle `Pr` between the two codomains.
  -- Given the two coherence equations
  --     vin-cohᵛ  : Lin₁ ≈ᵛ (σᵛ ⊗ᵛ idᵛ) ∘ᵛ Lin₂
  --     vout-cohᵛ : Pr ∘ᵛ Lout₁ ≈ᵛ Lout₂ ∘ᵛ (σᵛ ⊗ᵛ idᵛ)
  -- the two located composites are equal up to `Pr`.  K-FREE, the σ-swap
  -- provided by `box-crossᵛ`.
  ------------------------------------------------------------------------

  cross-NFᵛ
    : ∀ {A B A' B' Rl sp Cod₁ Cod₂ : List (Fin H.nV)}
        (g : HomV A B) (g' : HomV A' B')
        (Lin₁  : HomV sp ((A ++ A') ++ Rl))
        (Lin₂  : HomV sp ((A' ++ A) ++ Rl))
        (Lout₁ : HomV ((B ++ B') ++ Rl) Cod₁)
        (Lout₂ : HomV ((B' ++ B) ++ Rl) Cod₂)
        (Pr    : HomV Cod₁ Cod₂)
      → Lin₁ ≈ᵛ (σᵛ A' A ⊗ᵛ idᵛ {Rl}) ∘ᵛ Lin₂
      → Pr ∘ᵛ Lout₁ ≈ᵛ Lout₂ ∘ᵛ (σᵛ B B' ⊗ᵛ idᵛ {Rl})
      → ( Lout₂ ∘ᵛ (((g' ⊗ᵛ g) ⊗ᵛ idᵛ {Rl}) ∘ᵛ Lin₂) )
        ≈ᵛ Pr ∘ᵛ ( Lout₁ ∘ᵛ (((g ⊗ᵛ g') ⊗ᵛ idᵛ {Rl}) ∘ᵛ Lin₁) )
  cross-NFᵛ {Rl = Rl} g g' Lin₁ Lin₂ Lout₁ Lout₂ Pr vinc voutc =
    -- (0) rewrite the box block by `box-crossᵛ`:
    --     (g' ⊗ᵛ g) ⊗ᵛ idᵛ  ≈  (Sout ∘ᵛ C) ∘ᵛ Sin
    --   with C = (g ⊗ᵛ g') ⊗ᵛ idᵛ, Sin = σᵛ A' A ⊗ᵛ idᵛ, Sout = σᵛ B B' ⊗ᵛ idᵛ.
    ≈-trans (∘-resp ≈-refl (∘-resp (box-crossᵛ g g' Rl) ≈-refl))
    -- (1) reassociate the inner block to  Sout ∘ᵛ (C ∘ᵛ (Sin ∘ᵛ Lin₂))
    (≈-trans (∘-resp ≈-refl assocˢ)
    (≈-trans (∘-resp ≈-refl assocˢ)
    (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (∘-resp ≈-refl (≈-sym vinc))))
    -- (2) Sin ∘ᵛ Lin₂ ≈ᵛ Lin₁  (vinc) :  Lout₂ ∘ᵛ (Sout ∘ᵛ (C ∘ᵛ Lin₁))
    (≈-trans (≈-sym assocˢ)
    -- (3) (Lout₂ ∘ᵛ Sout) ∘ᵛ (C ∘ᵛ Lin₁) ≈ᵛ (Pr ∘ᵛ Lout₁) ∘ᵛ (C ∘ᵛ Lin₁)
    (≈-trans (∘-resp (≈-sym voutc) ≈-refl)
      assocˢ)))))

  ------------------------------------------------------------------------
  -- THREE-FACTOR RESIDUAL RELOCATION of a fire box.  The residual identity
  -- `idᵛ {rest}` is conjugated by a relocation `q : rest ↭ C ++ Rl` into a
  -- pre-box permute, the relocated box `genˢ ⊗ᵛ idᵛ {C ++ Rl}`, and a
  -- post-box permute.  K-FREE (interchange + `permuteˢ-inv-left`).
  ------------------------------------------------------------------------

  box-resid3ᵛ
    : ∀ (e : Fin H.nE) {rest C Rl : List (Fin H.nV)}
        (q : rest Perm.↭ C ++ Rl)
    → genˢ (H.elab e) ⊗ᵛ idᵛ {rest}
      ≈ᵛ (idᵛ {H.eout e} ⊗ᵛ permuteᵛ (Perm.↭-sym q))
           ∘ᵛ ( (genˢ (H.elab e) ⊗ᵛ idᵛ {C ++ Rl})
                  ∘ᵛ (idᵛ {H.ein e} ⊗ᵛ permuteᵛ q) )
  box-resid3ᵛ e q =
    ≈-trans (⊗-respᵛ (≈-sym idˡ) (≈-sym (permuteˢ-inv-left q)))
    (≈-trans (≈-sym interchangeᵛ)
    (∘-resp ≈-refl
      (≈-trans (⊗-respᵛ (≈-sym idʳ) (≈-sym idˡ))
        (≈-sym interchangeᵛ))))

  ------------------------------------------------------------------------
  -- The `SwapCore` / `PermCalc` bricks the located coherences below use.
  ------------------------------------------------------------------------
  Incompˢ = Incomp H
  rigidᵛ  = perm-rigidˢ H

  -- The thin wiring-groupoid calculus (F11): ⟦bswap⟧ᵛ.
  open PC.Kit H using (⟦bswap⟧ᵛ)

  open DSS.Scr (Fin H.nV) H.vlab using (bswap)

  ------------------------------------------------------------------------
  -- The per-pair located frames + coherences.  `SimLoc` (from FMIC) is
  -- opened, and `Lin₁/Lin₂/Lout₁/Lout₂/Pr` are the located derivations
  -- themselves: at V level the block shape `(A ++ A') ++ Rl` IS the vertex
  -- stack the derivation lands in, so no frame cast is named.
  -- `vin-cohᵛ`/`vout-cohᵛ` discharge the two `cross-NFᵛ` hypotheses by
  -- rigidity + `⟦bswap⟧ᵛ`.
  ------------------------------------------------------------------------

  module Located
    {e e' : Fin H.nE} (inc : Incompˢ e e')
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    (us-sp : Unique sp)
    (us-cod : Unique (H.eout e ++ r₁'))
    where

    SL : FMIC.SimLoc H (proj₁ inc) (proj₂ inc) sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    SL = FMIC.sim-loc H (proj₁ inc) (proj₂ inc) sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    open FMIC.SimLoc SL public

    -- The located frames.
    Lin₁ : HomV sp ((H.ein e ++ H.ein e') ++ Rlist)
    Lin₁ = permuteᵛ loc₁
    Lin₂ : HomV sp ((H.ein e' ++ H.ein e) ++ Rlist)
    Lin₂ = permuteᵛ loc₂
    Lout₁ : HomV ((H.eout e ++ H.eout e') ++ Rlist) (H.eout e' ++ r₂)
    Lout₁ = permuteᵛ vout-loc₁
    Lout₂ : HomV ((H.eout e' ++ H.eout e) ++ Rlist) (H.eout e ++ r₁')
    Lout₂ = permuteᵛ vout-loc₂
    Pr : HomV (H.eout e' ++ r₂) (H.eout e ++ r₁')
    Pr = permuteᵛ r-stk

    private
      swp-in : (H.ein e' ++ H.ein e) ++ Rlist Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
      swp-in = PermProp.++⁺ʳ Rlist (bswap (H.ein e') (H.ein e))

      swp-out : (H.eout e ++ H.eout e') ++ Rlist Perm.↭ (H.eout e' ++ H.eout e) ++ Rlist
      swp-out = PermProp.++⁺ʳ Rlist (bswap (H.eout e) (H.eout e'))

    -- `Lin₁` and the RHS are two derivations into the SAME `Unique` codomain
    -- (`Unique-resp-↭ loc₁ us-sp`): the wiring is rigid, and `⟦bswap⟧ᵛ` turns
    -- `swp-in` into `σᵛ ⊗ᵛ idᵛ`.
    vin-cohᵛ : Lin₁ ≈ᵛ (σᵛ (H.ein e') (H.ein e) ⊗ᵛ idᵛ {Rlist}) ∘ᵛ Lin₂
    vin-cohᵛ =
      ≈-trans (rigidᵛ (SU.Unique-resp-↭ loc₁ us-sp) loc₁
                 (Perm.trans loc₂ swp-in))
              (∘-resp (⟦bswap⟧ᵛ (H.ein e') (H.ein e) Rlist) ≈-refl)

    -- The mirror: `trans vout-loc₁ r-stk` and `trans swp-out vout-loc₂` are
    -- two derivations into `Unique (eout e ++ r₁')` (`us-cod`).
    vout-cohᵛ
      : Pr ∘ᵛ Lout₁
        ≈ᵛ Lout₂ ∘ᵛ (σᵛ (H.eout e) (H.eout e') ⊗ᵛ idᵛ {Rlist})
    vout-cohᵛ =
      ≈-trans (rigidᵛ us-cod (Perm.trans vout-loc₁ r-stk)
                 (Perm.trans swp-out vout-loc₂))
              (∘-resp ≈-refl (⟦bswap⟧ᵛ (H.eout e) (H.eout e') Rlist))

--------------------------------------------------------------------------------
-- ===== top-level capstone =====
--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  -- SwapCore brick aliases.

  -- The thin wiring-groupoid calculus (F11): ⟦absorbˡ⟧/⟦absorbʳ⟧/⟦bswap⟧ᵛ +
  -- rigid-≈̂.
  open PC.Kit H
    using (⟦absorbˡ⟧; ⟦absorbʳ⟧; ⟦bswap⟧ᵛ; rigid-≈̂)

  open Restrict (Fin H.nV) vl
    using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; permuteᵛ-frameˡ
          ; castᵛ-≈̂; cast-respᵛ; ∘-castᵛ
          ; ⊗-respᵛ; interchangeᵛ; ⊗id-distᵛ; box-suffix-ᵛ; σ-natᵛ )

  cross-NFᵛ′   = FMS.cross-NFᵛ H
  box-resid3ᵛ′ = FMS.box-resid3ᵛ H

  open DSS.Scr (Fin H.nV) H.vlab using (bswap)

  FireMidInterchangeˢ : Set
  FireMidInterchangeˢ = SCR.FireMidInterchangeˢ H lin

  private
    -- Pure-SMC box merge: the back box `g'` brought to front by the block
    -- braid `σᵛ B A'`, applied after the front box `g`, equals the both-boxes
    -- morphism `g ⊗ᵛ g'` (front box on the LEFT) precomposed with the OUTPUT
    -- braid `σᵛ B B'`.  K-free (σ-naturality + interchange).
    box-merge-σᵛ
      : ∀ {A B A' B' : List (Fin H.nV)} (g : HomV A B) (g' : HomV A' B')
      → (g' ⊗ᵛ idᵛ {B}) ∘ᵛ (σᵛ B A' ∘ᵛ (g ⊗ᵛ idᵛ {A'}))
        ≈ᵛ σᵛ B B' ∘ᵛ (g ⊗ᵛ g')
    box-merge-σᵛ g g' =
      -- regroup to `((g'⊗ᵛid{B}) ∘ᵛ σᵛ B A') ∘ᵛ (g⊗ᵛid{A'})`
      ≈-trans (≈-sym assocˢ)
      -- σ-nat (flipped): (g'⊗ᵛid{B}) ∘ᵛ σᵛ B A' ≈ᵛ σᵛ B B' ∘ᵛ (id{B}⊗ᵛg')
      (≈-trans (∘-resp (≈-sym σ-natᵛ) ≈-refl)
      -- reassoc to σᵛ B B' ∘ᵛ ((id{B}⊗ᵛg') ∘ᵛ (g⊗ᵛid{A'}))
      (pullʳ (≈-trans interchangeᵛ (⊗-respᵛ idˡ idʳ))))

    -- A single located fire box: the fired layer of `e` on the residual
    -- `rest`, with `rest` relocated to `C ++ Rl` by `q`.
    fire-locatedᵛ
      : ∀ (e : Fin H.nE) (s rest C Rl : List (Fin H.nV))
          (perm : s Perm.↭ H.ein e ++ rest) (q : rest Perm.↭ C ++ Rl)
      → fire-termˢ e s rest perm
        ≈ᵛ (idᵛ {H.eout e} ⊗ᵛ permuteᵛ (Perm.↭-sym q))
             ∘ᵛ ( (genˢ (H.elab e) ⊗ᵛ idᵛ {C ++ Rl})
                    ∘ᵛ permuteᵛ (Perm.trans perm (PermProp.++⁺ˡ (H.ein e) q)) )
    fire-locatedᵛ e s rest C Rl perm q =
      ≈-trans (edge-step-firedᵛ e rest perm)
      (≈-trans (∘-resp (box-resid3ᵛ′ e {rest} {C} {Rl} q) ≈-refl)
      (pullʳ (pullʳ (∘-resp (≈-sym (permuteᵛ-frameˡ (H.ein e) q)) ≈-refl))))

    -- The block-bracketed box merge.  The two located boxes (front box `g`
    -- on residual `A' ++ Rl`, back box `g'` on residual `B ++ Rl`) with the
    -- mid block-swap `σᵛ B A' ⊗ᵛ idᵛ{Rl}` reassociated between them collapse
    -- to the side-by-side `(g ⊗ᵛ g') ⊗ᵛ idᵛ{Rl}` with the OUTPUT block-swap
    -- `σᵛ B B' ⊗ᵛ idᵛ{Rl}`.  The three `++-assoc` casts are the
    -- re-bracketings the located residuals (`A++(A'++Rl)`) and the block
    -- frame (`(A++A')++Rl`) differ by.  K-free.
    box-merge-Rᵛ
      : ∀ {A B A' B' : List (Fin H.nV)} (g : HomV A B) (g' : HomV A' B')
          (Rl : List (Fin H.nV))
      → (g' ⊗ᵛ idᵛ {B ++ Rl})
          ∘ᵛ ( castᵛ (++-assoc B A' Rl) (++-assoc A' B Rl)
                 (σᵛ B A' ⊗ᵛ idᵛ {Rl})
               ∘ᵛ (g ⊗ᵛ idᵛ {A' ++ Rl}) )
        ≈ᵛ castᵛ (++-assoc A A' Rl) (++-assoc B' B Rl)
            ( (σᵛ B B' ⊗ᵛ idᵛ {Rl}) ∘ᵛ ((g ⊗ᵛ g') ⊗ᵛ idᵛ {Rl}) )
    box-merge-Rᵛ {A} {B} {A'} {B'} g g' Rl =
      -- reframe the two outer boxes (box-suffix), so every factor is
      -- `(box ⊗ᵛ id{·}) ⊗ᵛ id{Rl}` at the uniform `(·)++Rl` bracketing, with
      -- the casts on each factor.
      ≈-trans (∘-resp (≈-sym (box-suffix-ᵛ g' B Rl)) ≈-refl)
      (≈-trans (∘-resp ≈-refl
                  (∘-resp ≈-refl (≈-sym (box-suffix-ᵛ g A' Rl))))
      -- inner composite: the σ-block's domain cast meets the g-box cast at
      -- `(B++A')++Rl`, giving the bare `σᵛ B A' ∘ᵛ (g⊗ᵛid{A'})` tensored
      -- with id{Rl}; then the outer box fuses the same way and the composite
      -- under the cast is the bare merge, redistributed.
      (≈-trans (∘-resp ≈-refl
        (≈-trans (∘-castᵛ (++-assoc A A' Rl) (++-assoc B A' Rl)
                    (++-assoc A' B Rl) (σᵛ B A' ⊗ᵛ idᵛ {Rl})
                    ((g ⊗ᵛ idᵛ {A'}) ⊗ᵛ idᵛ {Rl}))
          (cast-respᵛ (++-assoc A A' Rl) (++-assoc A' B Rl)
            (≈-sym (⊗id-distᵛ (σᵛ B A') (g ⊗ᵛ idᵛ {A'}))))))
      (≈-trans (∘-castᵛ (++-assoc A A' Rl) (++-assoc A' B Rl)
                  (++-assoc B' B Rl) ((g' ⊗ᵛ idᵛ {B}) ⊗ᵛ idᵛ {Rl})
                  ((σᵛ B A' ∘ᵛ (g ⊗ᵛ idᵛ {A'})) ⊗ᵛ idᵛ {Rl}))
        (cast-respᵛ (++-assoc A A' Rl) (++-assoc B' B Rl)
          (≈-trans (≈-sym (⊗id-distᵛ (g' ⊗ᵛ idᵛ {B})
                             (σᵛ B A' ∘ᵛ (g ⊗ᵛ idᵛ {A'}))))
            (≈-trans (⊗-respᵛ (box-merge-σᵛ g g') ≈-refl)
              (⊗id-distᵛ (σᵛ B B') (g ⊗ᵛ g'))))))))

  ----------------------------------------------------------------------
  -- The generic, block-symmetric single-order located normal form
  -- `nf-genᵛ`.
  --
  -- For two edges `a` (fired first) then `b`, located simultaneously by a
  -- shared residual `R` (the residual permutes `ρ₁ : s₁ ↭ ein b ++ R`,
  -- `ρ₂ : s₂ ↭ eout a ++ R`, and the block frames `loc`/`vout-loc`), the
  -- two-fire composite is the `cross-NFᵛ`-shaped located form.
  ----------------------------------------------------------------------

  module Gen
    (a b : Fin H.nE)
    (sp : List (Fin H.nV))
    (s₁ : List (Fin H.nV)) (q-first  : sp Perm.↭ H.ein a ++ s₁)
    (s₂ : List (Fin H.nV)) (q-second : H.eout a ++ s₁ Perm.↭ H.ein b ++ s₂)
    (R  : List (Fin H.nV))
    (ρ₁ : s₁ Perm.↭ H.ein b ++ R) (ρ₂ : s₂ Perm.↭ H.eout a ++ R)
    (loc      : sp Perm.↭ (H.ein a ++ H.ein b) ++ R)
    (vout-loc : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂)
    (us-in-a : Unique (H.ein a ++ s₁))
    (us-mid  : Unique (H.ein b ++ s₂))
    (us-cod  : Unique (H.eout b ++ s₂))
    where

    -- block abbreviations.
    A  = H.ein a  ; A' = H.ein b
    B  = H.eout a ; B' = H.eout b
    g  : HomV A B
    g  = genˢ (H.elab a)
    g' : HomV A' B'
    g' = genˢ (H.elab b)

    -- the two simultaneously-located firing permutes.
    loc1' : sp Perm.↭ A ++ (A' ++ R)
    loc1' = Perm.trans q-first (PermProp.++⁺ˡ A ρ₁)
    loc2' : B ++ s₁ Perm.↭ A' ++ (B ++ R)
    loc2' = Perm.trans q-second (PermProp.++⁺ˡ A' ρ₂)

    -- The block frames the `cross-NFᵛ` consumer expects: at V level the
    -- located derivations land in the block shape on the nose.
    Lin : HomV sp ((A ++ A') ++ R)
    Lin = permuteᵛ loc
    Lout : HomV ((B ++ B') ++ R) (B' ++ s₂)
    Lout = permuteᵛ vout-loc

    ------------------------------------------------------------------
    -- Named pieces of the two located firings, and (Step A) their
    -- composite regrouped so that the mid `IN2 ∘ᵛ OUT1` is a single factor.
    ------------------------------------------------------------------
    private
      OUT1 = idᵛ {B}  ⊗ᵛ permuteᵛ (Perm.↭-sym ρ₁)
      Boxa = g  ⊗ᵛ idᵛ {A' ++ R}
      IN1  = permuteᵛ loc1'
      OUT2 = idᵛ {B'} ⊗ᵛ permuteᵛ (Perm.↭-sym ρ₂)
      Boxb = g' ⊗ᵛ idᵛ {B ++ R}
      IN2  = permuteᵛ loc2'
      box-block = (g ⊗ᵛ g') ⊗ᵛ idᵛ {R}
      σ-out     = σᵛ B B' ⊗ᵛ idᵛ {R}

      phase
        : fire-termˢ b (B ++ s₁) s₂ q-second ∘ˢ fire-termˢ a sp s₁ q-first
          ≈ᵛ OUT2 ∘ᵛ ( Boxb ∘ᵛ ( (IN2 ∘ᵛ OUT1) ∘ᵛ ( Boxa ∘ᵛ IN1 ) ) )
      phase =
        ≈-trans (∘-resp (fire-locatedᵛ b (B ++ s₁) s₂ B R q-second ρ₂)
                        (fire-locatedᵛ a sp s₁ A' R q-first ρ₁))
        (pullʳ (pullʳ (≈-sym assocˢ)))

    ------------------------------------------------------------------
    -- The MID reconciliation: T2's input after T1's output relocate is the
    -- pure block-swap, i.e. the block braiding `σᵛ B A' ⊗ᵛ idᵛ{R}` at the
    -- located `·++(·++R)` bracketing.
    ------------------------------------------------------------------
    private
      mid-comp : B ++ (A' ++ R) Perm.↭ A' ++ (B ++ R)
      mid-comp = Perm.trans (PermProp.++⁺ˡ B (Perm.↭-sym ρ₁)) loc2'

      -- `Unique (A' ++ (B ++ R))` — the common mid codomain — from
      -- `us-mid : Unique (A' ++ s₂)` through the residual relocate `ρ₂`.
      us-mid-img : Unique (A' ++ (B ++ R))
      us-mid-img = SU.Unique-resp-↭ (PermProp.++⁺ˡ A' ρ₂) us-mid

      -- the mid block-swap, bracketed by the two reindexing derivations.
      bridgeD : B ++ (A' ++ R) Perm.↭ A' ++ (B ++ R)
      bridgeD =
        Perm.trans (Perm.↭-reflexive (sym (++-assoc B A' R)))
        (Perm.trans (PermProp.++⁺ʳ R (bswap B A'))
                    (Perm.↭-reflexive (++-assoc A' B R)))

      Mid : HomV (B ++ (A' ++ R)) (A' ++ (B ++ R))
      Mid = castᵛ (++-assoc B A' R) (++-assoc A' B R) (σᵛ B A' ⊗ᵛ idᵛ {R})

      MID-eq : IN2 ∘ᵛ OUT1 ≈ᵛ Mid
      MID-eq =
        ≈-trans (∘-resp ≈-refl (≈-sym (permuteᵛ-frameˡ B (Perm.↭-sym ρ₁))))
          (viâ (rigid-≈̂ us-mid-img mid-comp bridgeD)
            (≈̂-trans (⟦absorbʳ⟧ (sym (++-assoc B A' R)))
            (≈̂-trans (⟦absorbˡ⟧ (++-assoc A' B R))
                     (≈ˢ⇒≈̂ (⟦bswap⟧ᵛ B A' R))))
            (castᵛ-≈̂ (++-assoc B A' R) (++-assoc A' B R)
              (σᵛ B A' ⊗ᵛ idᵛ {R})))

    ------------------------------------------------------------------
    -- The central merge: the two located boxes around the mid block-swap
    -- collapse, via `box-merge-Rᵛ`, to the side-by-side block
    -- `(g ⊗ᵛ g') ⊗ᵛ idᵛ{R}` with the OUTPUT braid `σ-out`.
    ------------------------------------------------------------------
    private
      central-eq
        : Boxb ∘ᵛ ( (IN2 ∘ᵛ OUT1) ∘ᵛ Boxa )
          ≈ᵛ castᵛ (++-assoc A A' R) (++-assoc B' B R) (σ-out ∘ᵛ box-block)
      central-eq =
        ≈-trans (∘-resp ≈-refl (∘-resp MID-eq ≈-refl)) (box-merge-Rᵛ g g' R)

    ------------------------------------------------------------------
    -- INPUT reconciliation: the located input `IN1` re-bracketed through the
    -- central cast equals the block frame `Lin` precomposing the box block.
    -- (`rigid-≈̂` at the `us-in-a`-image, `⟦absorbˡ⟧` cancels the tail.)
    ------------------------------------------------------------------
    private
      loc-down : sp Perm.↭ A ++ (A' ++ R)
      loc-down = Perm.trans loc (Perm.↭-reflexive (++-assoc A A' R))

      us-down : Unique (A ++ (A' ++ R))
      us-down = SU.Unique-resp-↭ (PermProp.++⁺ˡ A ρ₁) us-in-a

      box-part : HomV (A ++ (A' ++ R)) ((B ++ B') ++ R)
      box-part = castᵛ (++-assoc A A' R) refl box-block

      in-eq : box-part ∘ᵛ IN1 ≈ᵛ box-block ∘ᵛ Lin
      in-eq = ≈̂⇒≈ˢ
        (∘-resp-≈̂ (castᵛ-≈̂ (++-assoc A A' R) refl box-block)
          (≈̂-trans (rigid-≈̂ us-down loc1' loc-down)
                   (⟦absorbˡ⟧ (++-assoc A A' R))))

    ------------------------------------------------------------------
    -- OUTPUT reconciliation: the located output `OUT2` together with the
    -- merge's output braid equals `Lout`.  (`⟦bswap⟧ᵛ` + `rigid-≈̂` at
    -- `us-cod`, mirroring `FMS.Located.vout-cohᵛ`.)
    ------------------------------------------------------------------
    private
      out-part : HomV ((B ++ B') ++ R) (B' ++ (B ++ R))
      out-part = castᵛ refl (++-assoc B' B R) σ-out

      out-reloc : B' ++ (B ++ R) Perm.↭ B' ++ s₂
      out-reloc = PermProp.++⁺ˡ B' (Perm.↭-sym ρ₂)

      swp-out : (B ++ B') ++ R Perm.↭ (B' ++ B) ++ R
      swp-out = PermProp.++⁺ʳ R (bswap B B')

      vout-comp : (B ++ B') ++ R Perm.↭ B' ++ s₂
      vout-comp =
        Perm.trans (Perm.trans swp-out (Perm.↭-reflexive (++-assoc B' B R)))
                   out-reloc

      out-eq : OUT2 ∘ᵛ out-part ≈ᵛ Lout
      out-eq = ≈̂⇒≈ˢ
        (≈̂-trans
          (∘-resp-≈̂ (≈̂-sym (≈ˢ⇒≈̂ (permuteᵛ-frameˡ B' (Perm.↭-sym ρ₂))))
            (≈̂-trans (castᵛ-≈̂ refl (++-assoc B' B R) σ-out)
              (≈̂-sym (≈̂-trans (⟦absorbˡ⟧ (++-assoc B' B R))
                              (≈ˢ⇒≈̂ (⟦bswap⟧ᵛ B B' R))))))
          (rigid-≈̂ us-cod vout-comp vout-loc))

    ------------------------------------------------------------------
    -- THE SINGLE-ORDER LOCATED NORMAL FORM.
    ------------------------------------------------------------------
    nf-genᵛ
      : fire-termˢ b (B ++ s₁) s₂ q-second ∘ˢ fire-termˢ a sp s₁ q-first
        ≈ᵛ Lout ∘ᵛ ( box-block ∘ᵛ Lin )
    nf-genᵛ =
      ≈-trans phase
      -- expose `(Boxb ∘ᵛ ((IN2∘ᵛOUT1) ∘ᵛ Boxa)) ∘ᵛ IN1` as the inner factor
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (≈-sym assocˢ)))
      (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
      -- central merge, then split its cast across `out-part`/`box-part`
      (≈-trans (∘-resp ≈-refl (∘-resp central-eq ≈-refl))
      (≈-trans (∘-resp ≈-refl (∘-resp split ≈-refl))
      (≈-trans (∘-resp ≈-refl assocˢ)
      (≈-trans (≈-sym assocˢ)
        (∘-resp out-eq in-eq)))))))
      where
        split : castᵛ (++-assoc A A' R) (++-assoc B' B R) (σ-out ∘ᵛ box-block)
                ≈ᵛ out-part ∘ᵛ box-part
        split =
          ≈-sym (∘-castᵛ (++-assoc A A' R) refl (++-assoc B' B R)
                   σ-out box-block)

  ----------------------------------------------------------------------
  -- THE BOTH-FIRE INTERCHANGE CORE — UNCONDITIONAL.
  --
  -- The two per-order located normal forms `nf-genᵛ` (instantiated for the
  -- `e`-first / `e'`-first orders at the shared `SimLoc` residual) are threaded
  -- through the proven `cross-NFᵛ` with `FMS`'s coherences
  -- `vin-cohᵛ`/`vout-cohᵛ`.
  ----------------------------------------------------------------------

  fire-mid-interchangeˢ : FireMidInterchangeˢ
  fire-mid-interchangeˢ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
                        us-sp us-mid₁ us-mid₂ us-cod =
    r-stk , goal
    where
      -- `Located` already built the `SimLoc` bundle and re-exports it, so the
      -- 12-argument `sim-loc` application is NOT respelled here.
      open FMS.Located H inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-cod

      -- The per-order residual relocates + `Unique` witnesses + `Gen`
      -- instantiation, factored once and instantiated for both orders below
      -- (only `us-cod-final` is asymmetric across orders — `Ord`'s CALLERS
      -- resolve that by pre-bridging it through `r-stk` where needed).
      module Ord
        (x y : Fin H.nE)
        (rx : List (Fin H.nV)) (px : sp Perm.↭ H.ein x ++ rx)
        (ry : List (Fin H.nV)) (py : H.eout x ++ rx Perm.↭ H.ein y ++ ry)
        (loc      : sp Perm.↭ (H.ein x ++ H.ein y) ++ Rlist)
        (vout-loc : (H.eout x ++ H.eout y) ++ Rlist Perm.↭ H.eout y ++ ry)
        (us-mid-src   : Unique (H.eout x ++ rx))
        (us-cod-final : Unique (H.eout y ++ ry))
        where
        ρ₁ : rx Perm.↭ H.ein y ++ Rlist
        ρ₁ = ++-cancelˡ (H.ein x)
               (Perm.trans (Perm.↭-sym px)
                 (Perm.trans loc
                   (Perm.↭-reflexive (++-assoc (H.ein x) (H.ein y) Rlist))))
        ρ₂ : ry Perm.↭ H.eout x ++ Rlist
        ρ₂ = ++-cancelˡ (H.ein y)
               (Perm.trans (Perm.↭-sym py)
                 (Perm.trans (PermProp.++⁺ˡ (H.eout x) ρ₁) eo-shift))
          where
            eo-shift : H.eout x ++ (H.ein y ++ Rlist) Perm.↭ H.ein y ++ (H.eout x ++ Rlist)
            eo-shift = PermProp.shifts (H.eout x) (H.ein y)

        us-in-a : Unique (H.ein x ++ rx)
        us-in-a = SU.Unique-resp-↭ px us-sp
        us-mid : Unique (H.ein y ++ ry)
        us-mid = SU.Unique-resp-↭ py us-mid-src

        module GG = Gen x y sp rx px ry py Rlist ρ₁ ρ₂ loc vout-loc us-in-a us-mid us-cod-final

      module O1 = Ord e  e' r₁  p₁  r₂  p₂  loc₁ vout-loc₁
                    us-mid₁ (SU.Unique-resp-↭ (Perm.↭-sym r-stk) us-cod)
      module O2 = Ord e' e  r₂' p₂' r₁' p₁' loc₂ vout-loc₂
                    us-mid₂ us-cod

      module G1 = O1.GG
      module G2 = O2.GG

      -- the two located normal forms (frames match `FMS`'s Lin/Lout).
      nf₁-eqᵛ
        : fire-termˢ e' (H.eout e ++ r₁) r₂ p₂ ∘ˢ fire-termˢ e sp r₁ p₁
          ≈ᵛ Lout₁ ∘ᵛ ( ((genˢ (H.elab e) ⊗ᵛ genˢ (H.elab e')) ⊗ᵛ idᵛ {Rlist})
                          ∘ᵛ Lin₁ )
      nf₁-eqᵛ = G1.nf-genᵛ

      nf₂-eqᵛ
        : fire-termˢ e (H.eout e' ++ r₂') r₁' p₁' ∘ˢ fire-termˢ e' sp r₂' p₂'
          ≈ᵛ Lout₂ ∘ᵛ ( ((genˢ (H.elab e') ⊗ᵛ genˢ (H.elab e)) ⊗ᵛ idᵛ {Rlist})
                          ∘ᵛ Lin₂ )
      nf₂-eqᵛ = G2.nf-genᵛ

      -- the cross-NFᵛ relation between the two orders.
      cross
        : ( Lout₂ ∘ᵛ ( ((genˢ (H.elab e') ⊗ᵛ genˢ (H.elab e)) ⊗ᵛ idᵛ {Rlist})
                         ∘ᵛ Lin₂ ) )
          ≈ᵛ Pr ∘ᵛ ( Lout₁ ∘ᵛ ( ((genˢ (H.elab e) ⊗ᵛ genˢ (H.elab e')) ⊗ᵛ idᵛ {Rlist})
                                  ∘ᵛ Lin₁ ) )
      cross = cross-NFᵛ′ (genˢ (H.elab e)) (genˢ (H.elab e'))
                Lin₁ Lin₂ Lout₁ Lout₂ Pr vin-cohᵛ vout-cohᵛ

      -- `goal` is `FireMidInterchangeˢ`'s second component at this
      -- instantiation, so it is NOT re-spelled here.
      goal = ≈-trans nf₂-eqᵛ (≈-trans cross (∘-resp ≈-refl (≈-sym nf₁-eqᵛ)))

  ----------------------------------------------------------------------
  -- THE UNCONDITIONAL EMPTY-TAIL TWO-EDGE INTERCHANGE `run-interchange₀ˢ`,
  -- obtained by instantiating `SwapCoreRun.RunInterchange` with the now-proven
  -- both-fire core `fire-mid-interchangeˢ`.
  ----------------------------------------------------------------------

  module RunInterchangeˢ =
    SCR.RunInterchange H lin fire-mid-interchangeˢ

  -- Re-export the headline result.
  open RunInterchangeˢ using (run-interchange₀ˢ) public


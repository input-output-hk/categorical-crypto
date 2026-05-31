{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Standalone discharge attempt for the `fire-mid-interchange` residual of
-- `Discharge/Sub/RunInterchangeEmptyTail.agda` — the both-fire two-edge
-- interchange.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchange
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (fire-term; fire-mid)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (¬_)

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open SS.PerHG H dih using (Incomp)
  open SS.FrontSwap H dih K uniq-cod using (box-interchange)

  ----------------------------------------------------------------------
  -- THE BLOCK-NORMAL-FORM RESIDUAL (M) — the genuine Mac-Lane bracketing.
  --
  -- For the two `Incomp` (disjoint-block) edges `e`, `e'`, fired in a
  -- given order from a common stack, the two framed boxes
  -- `(Agen-edge ⊗ id)` sit on disjoint tensor factors, so the composite
  -- brings to a common 3-block normal form `box-e ⊗ box-e' ⊗ id` framed by
  -- `permute`-built view isos.
  --
  -- We isolate this single bracketing residual: it provides, for the two
  -- orders, a common middle object `R` (the shared residual block) and the
  -- four `permute`-built frame morphisms, together with the factorisation
  -- of each order's box-composite into the 3-block form.  Everything else —
  -- the `box-interchange` (σ-naturality) application that swaps the two box
  -- orders and the `permute`/K reconciliation collapsing the frames into
  -- the existential reshuffle `r` — is PROVEN around it (`fire-mid-interchange`
  -- below).
  --
  -- The record's frame is stated so that the two orders share the SAME
  -- inner box-pair object `Ae ⊗₀ Ae' ⊗₀ R` / `Be ⊗₀ Be' ⊗₀ R` (where
  -- `Ae = unflatten (map vlab (ein e))` etc.), differing only in which box
  -- order (`box-e ⊗₁ box-e'` vs `box-e' ⊗₁ box-e`) sits in the middle — so
  -- `box-interchange` literally swaps them.
  ----------------------------------------------------------------------

  private
    Aein  : Fin H.nE → ObjTerm
    Aein  e = unflatten (map H.vlab (H.ein  e))
    Aeout : Fin H.nE → ObjTerm
    Aeout e = unflatten (map H.vlab (H.eout e))

    box-e : (e : Fin H.nE) → HomTerm (Aein e) (Aeout e)
    box-e e = Agen-edge H e

  -- The block-normal-form residual, per pair of disjoint edges and per the
  -- four locating permutes.  `R` is the shared residual block object.
  --
  -- The full box-composite of EACH order (`fire-mid ∘ permute ∘ fire-mid`,
  -- WITH its leading outer locating-permute folded in) factors as
  --
  --     Vout ∘ box-core ∘ Vin
  --
  -- where the two orders SHARE the same frame `(Vin , Vout)` (up to the
  -- braiding `σ` on the two box factors), `box-core` is `box-e ⊗₁ box-e'`
  -- resp. `box-e' ⊗₁ box-e` tensored with `id` on `R`, and `Vin`/`Vout`
  -- are `permute`-built isos from/to the actual stack objects.  Folding the
  -- outer locating-permutes into `Vin` and sharing one frame is exactly the
  -- combined `unflatten-++-≅` bracketing + K-reconciliation that even the
  -- `--with-K` development leaves open; it is the SOLE postulate here.
  --
  --   * `nf₁` : the `e ∷ e'` order (RHS box-composite + outer `permute p₁`).
  --   * `nf₂` : the `e' ∷ e` order (LHS box-composite + outer `permute p₂'`).
  --
  -- The frames are stated against the SAME inner object `(Aein e ⊗₀ Aein e')
  -- ⊗₀ R` (resp. out), so the two box cores are related by `box-interchange`,
  -- and the `σ`-conjugation collapses (`σ∘σ≈id`) — all PROVEN below.
  record BlockNF
    {e e' : Fin H.nE} (inc : Incomp e e')
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    : Set where
    field
      -- The shared residual block object.
      R    : ObjTerm
      -- Input frame for the `e ∷ e'` order: `e`-first orientation.
      vin₁ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e ⊗₀ Aein  e') ⊗₀ R)
      -- Input frame for the `e' ∷ e` order: `e'`-first orientation.
      vin₂ : HomTerm (unflatten (map H.vlab sp)) ((Aein  e' ⊗₀ Aein  e) ⊗₀ R)
      -- Output frames (one per final stack).
      vout₁ : HomTerm ((Aeout e ⊗₀ Aeout e') ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e' ++ r₂)))
      vout₂ : HomTerm ((Aeout e' ⊗₀ Aeout e) ⊗₀ R)
                      (unflatten (map H.vlab (H.eout e ++ r₁')))
      -- The reshuffle between the two final stacks.
      r-stk : (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁')
      -- The two input frames differ by the braiding on the two `Aein` factors.
      vin-coh  : vin₁ ≈Term (σ ⊗₁ id) ∘ vin₂
      -- The two output frames are reconciled by `r-stk` and the braiding on
      -- the two `Aeout` factors.
      vout-coh : permute-via-vlab H.vlab r-stk ∘ vout₁ ≈Term vout₂ ∘ (σ ⊗₁ id)
      -- Block normal form of the `e ∷ e'` order (RHS, incl. outer `permute p₁`).
      nf₁  : ( fire-mid H e' r₂ ∘ permute-via-vlab H.vlab p₂
                 ∘ fire-mid H e r₁ ∘ permute-via-vlab H.vlab p₁ )
             ≈Term vout₁ ∘ ((box-e e ⊗₁ box-e e') ⊗₁ id) ∘ vin₁
      -- Block normal form of the `e' ∷ e` order (LHS, incl. outer `permute p₂'`).
      nf₂  : ( fire-mid H e r₁' ∘ permute-via-vlab H.vlab p₁'
                 ∘ fire-mid H e' r₂' ∘ permute-via-vlab H.vlab p₂' )
             ≈Term vout₂ ∘ ((box-e e' ⊗₁ box-e e) ⊗₁ id) ∘ vin₂

  postulate
    block-nf
      : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
          (sp : List (Fin H.nV))
          (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
          (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
          (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
          (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
      → BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'

  fire-mid-interchange
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    → Σ[ r ∈ (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁') ]
        ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
            ∘ fire-term H e' sp r₂' p₂' )
        ≈Term permute-via-vlab H.vlab r
                ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                      ∘ fire-term H e sp r₁ p₁ )
  fire-mid-interchange {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' =
    BlockNF.r-stk nf , goal
    where
      nf : BlockNF inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
      nf = block-nf inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
      open BlockNF nf

      -- The locating permutes.
      P₁  = permute-via-vlab H.vlab p₁
      P₂  = permute-via-vlab H.vlab p₂
      P₂' = permute-via-vlab H.vlab p₂'
      P₁' = permute-via-vlab H.vlab p₁'
      Pr  = permute-via-vlab H.vlab r-stk

      bx  = box-e e
      bx' = box-e e'
      -- The (e-first) box core, the input braid `Sin` and the output braid
      -- `Sout` framing the box pair.
      C    = (bx ⊗₁ bx') ⊗₁ id {R}
      Sin  = σ {Aein  e'} {Aein  e} ⊗₁ id {R}
      Sout = σ {Aeout e} {Aeout e'} ⊗₁ id {R}

      ------------------------------------------------------------------
      -- (1)  Reassociate LHS / RHS to the `fire-mid ∘ permute ∘ …` shapes
      --      that `nf₂` / `nf₁` factor (recall `fire-term e s rest p =
      --      fire-mid e rest ∘ permute-via-vlab vlab p`, definitionally).
      ------------------------------------------------------------------
      -- LHS = (fire-mid e r₁' ∘ P₁') ∘ (fire-mid e' r₂' ∘ P₂')
      --     ≈ fire-mid e r₁' ∘ P₁' ∘ fire-mid e' r₂' ∘ P₂'   [reassoc]  = nf₂-LHS
      lhs-reassoc
        : ( fire-mid H e r₁' ∘ P₁' ) ∘ ( fire-mid H e' r₂' ∘ P₂' )
          ≈Term ( fire-mid H e r₁' ∘ P₁' ∘ fire-mid H e' r₂' ∘ P₂' )
      lhs-reassoc = assoc

      -- RHS-inner = (fire-mid e' r₂ ∘ P₂) ∘ (fire-mid e r₁ ∘ P₁)
      --           ≈ fire-mid e' r₂ ∘ P₂ ∘ fire-mid e r₁ ∘ P₁   [reassoc]  = nf₁-LHS
      rhs-reassoc
        : ( fire-mid H e' r₂ ∘ P₂ ) ∘ ( fire-mid H e r₁ ∘ P₁ )
          ≈Term ( fire-mid H e' r₂ ∘ P₂ ∘ fire-mid H e r₁ ∘ P₁ )
      rhs-reassoc = assoc

      ------------------------------------------------------------------
      -- (2)  Lift `box-interchange` through `_⊗₁ id`:
      --        (bx' ⊗₁ bx) ⊗₁ id  ≈  Sout ∘ (C ∘ Sin)
      ------------------------------------------------------------------
      bi : (bx' ⊗₁ bx) ≈Term σ ∘ ((bx ⊗₁ bx') ∘ σ)
      bi = box-interchange bx bx'

      -- (h ∘ k) ⊗₁ id ≈ (h ⊗₁ id) ∘ (k ⊗₁ id)
      ⊗id-∘ : ∀ {A B D} (h : HomTerm B D) (k : HomTerm A B)
            → (h ∘ k) ⊗₁ id {R} ≈Term (h ⊗₁ id) ∘ (k ⊗₁ id)
      ⊗id-∘ h k =
        ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

      core-swap : (bx' ⊗₁ bx) ⊗₁ id {R} ≈Term Sout ∘ (C ∘ Sin)
      core-swap =
        ≈-Term-trans (⊗-resp-≈ bi ≈-Term-refl)
          (≈-Term-trans (⊗id-∘ σ ((bx ⊗₁ bx') ∘ σ))
            (∘-resp-≈ ≈-Term-refl (⊗id-∘ (bx ⊗₁ bx') σ)))

      ------------------------------------------------------------------
      -- (3)  Collapse the e'-first normal form to `permute r-stk ∘ nf₁-RHS`.
      --
      --   nf₂-RHS = vout₂ ∘ ((bx'⊗bx)⊗id) ∘ vin₂
      --     ≈ vout₂ ∘ (Sout ∘ (C ∘ Sin)) ∘ vin₂                 [core-swap]
      --     ≈ vout₂ ∘ Sout ∘ C ∘ (Sin ∘ vin₂)                   [assoc]
      --     ≈ vout₂ ∘ Sout ∘ C ∘ vin₁                           [≈-sym vin-coh]
      --     ≈ (vout₂ ∘ Sout) ∘ (C ∘ vin₁)                       [assoc]
      --     ≈ (permute r-stk ∘ vout₁) ∘ (C ∘ vin₁)              [≈-sym vout-coh]
      --     ≈ permute r-stk ∘ (vout₁ ∘ (C ∘ vin₁))              [assoc]
      --     = permute r-stk ∘ nf₁-RHS
      ------------------------------------------------------------------
      nf₂-RHS = vout₂ ∘ ((bx' ⊗₁ bx) ⊗₁ id) ∘ vin₂
      nf₁-RHS = vout₁ ∘ C ∘ vin₁

      collapse : nf₂-RHS ≈Term Pr ∘ nf₁-RHS
      collapse =
        -- vout₂ ∘ ((bx'⊗bx)⊗id) ∘ vin₂ ≈ vout₂ ∘ (Sout ∘ (C ∘ Sin)) ∘ vin₂
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ core-swap ≈-Term-refl))
        -- ≈ vout₂ ∘ Sout ∘ (C ∘ (Sin ∘ vin₂))
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (≈-Term-trans assoc (∘-resp-≈ ≈-Term-refl assoc)))
        -- ≈ vout₂ ∘ Sout ∘ (C ∘ vin₁)
        (≈-Term-trans
          (∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ ≈-Term-refl (≈-Term-sym vin-coh))))
        -- ≈ (vout₂ ∘ Sout) ∘ (C ∘ vin₁)
        (≈-Term-trans
          (≈-Term-sym assoc)
        -- ≈ (permute r-stk ∘ vout₁) ∘ (C ∘ vin₁)
        (≈-Term-trans
          (∘-resp-≈ (≈-Term-sym vout-coh) ≈-Term-refl)
        -- ≈ permute r-stk ∘ (vout₁ ∘ (C ∘ vin₁))
          assoc))))

      ------------------------------------------------------------------
      -- (4)  Assemble `goal`.
      ------------------------------------------------------------------
      goal
        : ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
              ∘ fire-term H e' sp r₂' p₂' )
          ≈Term permute-via-vlab H.vlab r-stk
                  ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                        ∘ fire-term H e sp r₁ p₁ )
      goal =
        -- LHS = (fire-mid e r₁' ∘ P₁') ∘ (fire-mid e' r₂' ∘ P₂')
        ≈-Term-trans lhs-reassoc
        -- ≈ nf₂-LHS ≈ nf₂-RHS
        (≈-Term-trans nf₂
        -- ≈ Pr ∘ nf₁-RHS
        (≈-Term-trans collapse
        -- ≈ Pr ∘ nf₁-LHS
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym nf₁))
        -- ≈ Pr ∘ ((fire-mid e' r₂ ∘ P₂) ∘ (fire-mid e r₁ ∘ P₁))   [≈-sym rhs-reassoc]
          (∘-resp-≈ ≈-Term-refl (≈-Term-sym rhs-reassoc)))))

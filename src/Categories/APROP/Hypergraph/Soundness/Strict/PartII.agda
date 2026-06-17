{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The UNCONDITIONAL part (II)ˢ result `decodePˢ-resp-iso`.
--
--   decodePˢ-resp-iso : ⟪f⟫ ≅ᴴ ⟪g⟫ → decodePˢ f ≈ˢ decodePˢ g
--
-- This file is pure INTEGRATION PLUMBING.  It wires three now-complete pieces:
--
--   * the headline `DecodePRespIso.decodePˢ-resp-iso`, which factors the result
--     through TWO clearly-typed module parameters (the (N) `run-interchange-H`
--     witness and the cross-iso decoder agreement `decode-ordˢ-resp-iso`);
--   * the UNCONDITIONAL `run-interchange₀ˢ` (the empty-tail two-edge
--     interchange, from `Strict.FireMidDone`) lifted to an arbitrary suffix
--     `qs` by `Strict.RunInterchangeTailS.run-interchange-tailˢ` — assembled
--     here into `run-interchange-H` exactly as the NON-STRICT blueprint
--     `Discharge.DecodeRelRespIsoWired.run-interchange-⟪⟫` does;
--   * the FULLY DISCHARGED `Strict.IsoTransportS.decode-ordˢ-resp-iso`, fed the
--     SAME `run-interchange-H` we build.
--
-- {-# OPTIONS --safe --without-K #-}, zero postulates, zero holes.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.PartII
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)

open import Categories.APROP.Hypergraph.Soundness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig _≟X_ as SS
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodePRespIso sig _≟X_ as DP
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (RunInterchangeˢ; run-interchange-tailˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.FireMid sig _≟X_ as FMD
import Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoTransport sig _≟X_ as IT

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

------------------------------------------------------------------------
-- The (N) strict per-swap `RunInterchangeˢ` witness for `⟪f⟫`.
--
-- 1:1 port of the non-strict `DecodeRelRespIsoWired.run-interchange-⟪⟫`:
--   * the EMPTY-TAIL core `ri₀` is the UNCONDITIONAL `FireMidDone.run-interchange₀ˢ`
--     (packed into the empty-tail `RunInterchangeˢ` record);
--   * the tail extension to a suffix `qs` is `run-interchange-tailˢ`;
--   * the empty-tail reservoir freshness `res-empty-tail` descends from the
--     swap-site provenance via the term-free `SUR.dom-reservoir-prov` +
--     `SUR.reservoir-prefix` (re-bracketed by `++-assoc`).
------------------------------------------------------------------------

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    F   = ⟪ f ⟫
    dih = dep-irrefl-⟪⟫ f
    lin = DAL.⟪⟫-LinearP f

  run-interchange-H
    : ∀ (ps qs : SS.PerHG.Order F dih lin)
        {e e' : Fin (Hypergraph.nE F)}
        (inc : SS.PerHG.Incompˢ F dih lin e e')
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE F)
    → RunInterchangeˢ F dih lin ps qs inc
  run-interchange-H ps qs {e} {e'} inc prov =
    run-interchange-tailˢ F dih lin ps qs inc prov
      (record { reshuffle = proj₁ ri₀ ; run-eq = proj₂ ri₀ })
    where
      -- the full swap-order reservoir, from the swap-site provenance.
      res-full : SUR.Reservoir≤1 F (ps ++ e' ∷ e ∷ qs) (Hypergraph.dom F)
      res-full =
        SUR.dom-reservoir-prov F (proj₂ lin) (ps ++ e' ∷ e ∷ qs) prov

      assoc-eq : ps ++ e' ∷ e ∷ qs ≡ (ps ++ e' ∷ e ∷ []) ++ qs
      assoc-eq = sym (++-assoc ps (e' ∷ e ∷ []) qs)

      -- prefix drop of `qs`, after re-bracketing.
      res-empty-tail
        : SUR.Reservoir≤1 F (ps ++ e' ∷ e ∷ []) (Hypergraph.dom F)
      res-empty-tail =
        SUR.reservoir-prefix F (ps ++ e' ∷ e ∷ []) qs (Hypergraph.dom F)
          (subst (λ z → SUR.Reservoir≤1 F z (Hypergraph.dom F))
                 assoc-eq res-full)

      -- the empty-tail two-edge interchange (UNCONDITIONAL).
      ri₀ = FMD.run-interchange₀ˢ F dih lin ps inc res-empty-tail

------------------------------------------------------------------------
-- THE UNCONDITIONAL HEADLINE.  Feed both now-discharged inputs into
-- `DecodePRespIso`'s headline module (the `decode-ordˢ-resp-iso` parameter
-- is `IsoTransport.decode-ordˢ-resp-iso`, applied to the SAME
-- `run-interchange-H`).
------------------------------------------------------------------------

decodePˢ-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decodePˢ f ≈ˢ decodePˢ g
decodePˢ-resp-iso f g iso =
  DP.decodePˢ-resp-iso f g iso
    (run-interchange-H f)
    (IT.decode-ordˢ-resp-iso f g iso (run-interchange-H f))

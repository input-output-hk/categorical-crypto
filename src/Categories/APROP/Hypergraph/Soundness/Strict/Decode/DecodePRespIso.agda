{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The HEADLINE of part (II)ˢ: `decodePˢ-resp-iso` (strict twin of
-- `Discharge.DecodeRelRespIsoWired.decodeP-resp-iso`).
--
--   decodePˢ-resp-iso : ⟪f⟫ ≅ᴴ ⟪g⟫ → decodePˢ f ≈ˢ decodePˢ g
--
-- `decodePˢ f` IS `castˢ (⟪⟫-domL f) (⟪⟫-codL f) (decodeOrdˢ ⟪f⟫ (range nE)
-- (finalPermˢ f))` DEFINITIONALLY (the strict twin of
-- `decodeP-≡-decodeOrd-range` is `refl`), so the headline factors as:
--
--   * the boundary cast algebra — UIP-trivial in S (`List X` casts collapse
--     by `uipL` via `cast-fuse`/`cast-irrel`; the non-strict `objUIP`
--     `subst₂ HomTerm` calculus disappears);
--   * the (K₁) final-permute reconciliation `perm-rigidˢ` (both `finalPermˢ`
--     witnesses derive into the `Unique` codomain `cod ⟪f⟫`);
--   * the cross-iso decoder agreement `decode-ordˢ-resp-iso`, which assembles
--     `order-invariantˢ` (`IsoInvarianceConcrete`, BUILT) with the strict
--     cross-iso transport residual (`IsoTransport`ˢ, a LATER phase).
--
-- `decode-ordˢ-resp-iso` and the (N) `run-interchange` witness are exposed as
-- CLEARLY-TYPED module parameters, so this file is GREEN independent of the
-- still-unported strict `IsoTransport`/`FireMidInterchangeˢ` discharge.  The
-- order-theory core (`order-invariantˢ`) and the boundary are wired here in
-- full.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodePRespIso
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.HomTermInvariant sig using (⟪_⟫-cod-unique)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)
open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ; finalPermˢ; module Run)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig _≟X_ as SS
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (RunInterchangeˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; _∷_; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- Convenience: the strict per-HG decoder at the translation `⟪f⟫`.
------------------------------------------------------------------------

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    F   = ⟪ f ⟫
    dih = dep-irrefl-⟪⟫ f
    -- the pruned-translation Linearity witness; the pruned and main
    -- translations coincide where the decoder runs (as in Decode /
    -- DecodeRelRespIsoWired).
    lin : Linear F
    lin = DAL.⟪⟫-LinearP f

  open SS.PerHG F dih lin
    using (Order; Validˢ; decodeOrdˢ) public

  -- `decodePˢ f` exposed as a boundary cast of `decodeOrdˢ` at `range nE`.
  -- This is the strict twin of `decodeP-≡-decodeOrd-range`, holding `≡ refl`:
  -- `finalPermˢ f : pe-stackˢ (range nE) dom ↭ cod = Validˢ (range nE)`, and
  -- `Run.permuteˢ F (finalPermˢ f) ∘ˢ proj₂ (Run.runˢ F)` IS
  -- `decodeOrdˢ (range nE) (finalPermˢ f)`.
  vrangeˢ : Validˢ (range (Hypergraph.nE F))
  vrangeˢ = finalPermˢ f

  decodePˢ-≡-cast
    : decodePˢ f
      ≡ castˢ (⟪⟫-domL f) (⟪⟫-codL f) (decodeOrdˢ (range (Hypergraph.nE F)) vrangeˢ)
  decodePˢ-≡-cast = refl

------------------------------------------------------------------------
-- The boundary lemma: relate the two natural-order decodings of `⟪f⟫`/`⟪g⟫`
-- at the `flatten` boundary, GIVEN the cross-iso decoder agreement.  The
-- non-strict `objUIP` `subst₂ HomTerm` calculus collapses to the `List X`
-- `castˢ` kit (UIP-trivial via `cast-fuse`/`cast-irrel`); (K₁) is the
-- `perm-rigidˢ` final-permute reconciliation.
------------------------------------------------------------------------

module Boundary {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫) where
  private
    F = ⟪ f ⟫ ; G = ⟪ g ⟫
    dihF = dep-irrefl-⟪⟫ f ; dihG = dep-irrefl-⟪⟫ g
    linF : Linear F
    linF = DAL.⟪⟫-LinearP f
    linG : Linear G
    linG = DAL.⟪⟫-LinearP g
    module SF = SS.PerHG F dihF linF
    module SG = SS.PerHG G dihG linG

    permˢ-K-F : Support.PermK (Fin (Hypergraph.nV F)) (StrictDecoder.vl F)
    permˢ-K-F = PK.permˢ-K (Fin (Hypergraph.nV F)) _≟F_ (StrictDecoder.vl F)

    perm-rigidˢ-F
      : ∀ {xs ys} → Unique ys → (p q : xs Perm.↭ ys)
      → StrictDecoder.permuteˢ F p ≈ˢ StrictDecoder.permuteˢ F q
    perm-rigidˢ-F = Support.perm-rigidˢ (Fin (Hypergraph.nV F)) (StrictDecoder.vl F) permˢ-K-F

    rng-F = range (Hypergraph.nE F)
    rng-G = range (Hypergraph.nE G)

    -- the boundary `List X` equalities.
    df = ⟪⟫-domL f ; cf = ⟪⟫-codL f
    dg = ⟪⟫-domL g ; cg = ⟪⟫-codL g
    di = IW.domL-iso iso ; ci = IW.codL-iso iso

  -- (K₁) two `Validˢ (range)` witnesses for `⟪f⟫` give the same decoding.
  decodeOrdˢ-witness-coh
    : ∀ (v w : SF.Validˢ rng-F)
    → SF.decodeOrdˢ rng-F v ≈ˢ SF.decodeOrdˢ rng-F w
  decodeOrdˢ-witness-coh v w =
    ∘-resp (perm-rigidˢ-F (⟪ f ⟫-cod-unique) v w) ≈-refl

  -- The headline boundary lemma.  `wiring≈ : castˢ di ci (decodeOrdˢ-G vg)
  -- ≈ˢ decodeOrdˢ-F vH` is the cross-iso decoder agreement.
  decodeOrdˢ-boundary-resp-≈
    : ∀ (vf : SF.Validˢ rng-F) (vg : SG.Validˢ rng-G) (vH : SF.Validˢ rng-F)
    → castˢ di ci (SG.decodeOrdˢ rng-G vg) ≈ˢ SF.decodeOrdˢ rng-F vH
    → castˢ df cf (SF.decodeOrdˢ rng-F vf)
      ≈ˢ castˢ dg cg (SG.decodeOrdˢ rng-G vg)
  decodeOrdˢ-boundary-resp-≈ vf vg vH wiring≈ =
    -- step1 (K₁): swap `vf` for `vH`.
    ≈-trans (cast-resp df cf (decodeOrdˢ-witness-coh vf vH))
    -- step2 (wiring, reversed): `decodeOrdˢ-F vH ≈ castˢ di ci (decodeOrdˢ-G vg)`.
    (≈-trans (cast-resp df cf (≈-sym wiring≈))
    -- step3 (cast algebra): fuse the two casts; `trans di df ≡ dg`,
    -- `trans ci cf ≡ cg` by `uipL` (`List X` UIP), via `cast-fuse`+`cast-irrel`.
      (≡⇒≈ˢ (trans (cast-fuse di df ci cf (SG.decodeOrdˢ rng-G vg))
                   (cast-irrel (trans di df) dg (trans ci cf) cg
                               (SG.decodeOrdˢ rng-G vg)))))

------------------------------------------------------------------------
-- The HEADLINE.  Wires the order-theory core (`order-invariantˢ`, BUILT)
-- and the boundary, parameterised over the strict cross-iso decoder
-- agreement `decode-ordˢ-resp-iso` and the (N) `run-interchange-H` witness
-- (the residuals of the still-unported strict `IsoTransport` /
-- `FireMidInterchangeˢ` discharge).
------------------------------------------------------------------------

module _ {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
         -- (N) the strict per-swap RunInterchangeˢ witness for `⟪f⟫`.
         (run-interchange-H
           : ∀ (ps qs : SS.PerHG.Order ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f))
               {e e' : Fin (Hypergraph.nE ⟪ f ⟫)}
               (inc : SS.PerHG.Incompˢ ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f) e e')
             → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE ⟪ f ⟫)
             → RunInterchangeˢ ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f) ps qs inc)
         -- the cross-iso decoder agreement (the strict `IsoTransport`
         -- residual, fed `vrangeˢ g`).
         (decode-ordˢ-resp-iso
           : let module SF = SS.PerHG ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f)
                 module SG = SS.PerHG ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (DAL.⟪⟫-LinearP g)
             in (vJ : SG.Validˢ (range (Hypergraph.nE ⟪ g ⟫)))
              → Σ[ vH ∈ SF.Validˢ (range (Hypergraph.nE ⟪ f ⟫)) ]
                  castˢ (IW.domL-iso iso) (IW.codL-iso iso)
                        (SG.decodeOrdˢ (range (Hypergraph.nE ⟪ g ⟫)) vJ)
                  ≈ˢ SF.decodeOrdˢ (range (Hypergraph.nE ⟪ f ⟫)) vH)
         where
  private
    module B = Boundary f g iso

  decodePˢ-resp-iso : decodePˢ f ≈ˢ decodePˢ g
  decodePˢ-resp-iso =
    subst₂ (λ a b → a ≈ˢ b)
           (sym (decodePˢ-≡-cast f))
           (sym (decodePˢ-≡-cast g))
           (B.decodeOrdˢ-boundary-resp-≈ (vrangeˢ f) (vrangeˢ g) vH wiring≈)
    where
      res = decode-ordˢ-resp-iso (vrangeˢ g)
      vH      = proj₁ res
      wiring≈ = proj₂ res


{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The UNCONDITIONAL part (II)ˢ result `decodePˢ-resp-iso` (strict twin of the
-- former non-strict `DecodeRelRespIsoWired.decodeP-resp-iso`).
--
--   decodePˢ-resp-iso : ⟪f⟫ ≅ᴴ ⟪g⟫ → decodePˢ f ≈ˢ decodePˢ g
--
-- `decodePˢ f` IS `castˢ (⟪⟫-domL f) (⟪⟫-codL f) (decodeOrdˢ ⟪f⟫ (range nE)
-- (finalPermˢ f))` DEFINITIONALLY (the strict twin of
-- `decodeP-≡-decodeOrd-range` is `refl`), so the result factors as:
--
--   * the boundary cast algebra — UIP-trivial in S (`List X` casts collapse
--     by `uipL` via `cast-fuse`/`cast-irrel`; the non-strict `objUIP`
--     `subst₂ HomTerm` calculus disappears);
--   * the (K₁) final-permute reconciliation `perm-rigidˢ` (both `finalPermˢ`
--     witnesses derive into the `Unique` codomain `cod ⟪f⟫`);
--   * the cross-iso decoder agreement `IsoTransport.decode-ordˢ-resp-iso`,
--     which assembles the order-theory core `order-invariantˢ`
--     (now local to `IsoTransport`) with the strict cross-iso transport residual,
--     fed the (N) per-swap `RunInterchangeˢ` witness `run-interchange-H`
--     built below from the UNCONDITIONAL `FireMid.run-interchange₀ˢ` and
--     `Interchange.RunInterchangeTail.run-interchange-tailˢ` — exactly as the
--     former non-strict `DecodeRelRespIsoWired.run-interchange-⟪⟫` did.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.PartII
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (range)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.HomTermInvariant sig using (⟪_⟫-cod-unique)

open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig using (dep-irrefl-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (decodePˢ; finalPermˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig _≟X_ as SS
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (run-interchange-tailˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.FireMid sig _≟X_ as FMD
import Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoTransport sig _≟X_ as IT

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

------------------------------------------------------------------------
-- Per-`f` data: the strict per-HG decoder at the translation `⟪f⟫`, and the
-- (N) strict per-swap `RunInterchangeˢ` witness for `⟪f⟫`.
--
-- `run-interchange-H` is a 1:1 port of the former non-strict
-- `DecodeRelRespIsoWired.run-interchange-⟪⟫`:
--   * the EMPTY-TAIL core `ri₀` is the UNCONDITIONAL `FireMid.run-interchange₀ˢ`
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
    -- the pruned-translation Linearity witness; the pruned and main
    -- translations coincide where the decoder runs (as in Decode /
    -- the former `DecodeRelRespIsoWired`).
    lin : Linear F
    lin = DAL.⟪⟫-LinearP f

  open SS.PerHG F dih lin using (Order; Validˢ; decodeOrdˢ)

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

  run-interchange-H : SS.PerHG.RunInterchangeAt F dih lin
  run-interchange-H ps qs {e} {e'} inc prov =
    run-interchange-tailˢ F lin ps qs inc prov
      (record { reshuffle = proj₁ ri₀ ; run-eq = proj₂ ri₀ })
    where
      -- the full swap-order reservoir, from the swap-site provenance.
      res-full : SUR.Reservoir≤1 F (ps ++ e' ∷ e ∷ qs) (Hypergraph.dom F)
      res-full = SUR.dom-reservoir-prov F (proj₂ lin) (ps ++ e' ∷ e ∷ qs) prov

      assoc-eq : ps ++ e' ∷ e ∷ qs ≡ (ps ++ e' ∷ e ∷ []) ++ qs
      assoc-eq = sym (++-assoc ps (e' ∷ e ∷ []) qs)

      -- prefix drop of `qs`, after re-bracketing.
      res-empty-tail : SUR.Reservoir≤1 F (ps ++ e' ∷ e ∷ []) (Hypergraph.dom F)
      res-empty-tail =
        SUR.reservoir-prefix F (ps ++ e' ∷ e ∷ []) qs (Hypergraph.dom F)
          (subst (λ z → SUR.Reservoir≤1 F z (Hypergraph.dom F))
                 assoc-eq res-full)

      -- the empty-tail two-edge interchange (UNCONDITIONAL).
      ri₀ = FMD.run-interchange₀ˢ F dih lin ps inc res-empty-tail

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
  decodeOrdˢ-witness-coh v w = ∘-resp (perm-rigidˢ-F (⟪ f ⟫-cod-unique) v w) ≈-refl

  -- The headline boundary lemma.  `wiring≈ : castˢ di ci (decodeOrdˢ-G vg)
  -- ≈ˢ decodeOrdˢ-F vH` is the cross-iso decoder agreement.
  decodeOrdˢ-boundary-resp-≈
    : ∀ (vf : SF.Validˢ rng-F) (vg : SG.Validˢ rng-G) (vH : SF.Validˢ rng-F)
    → castˢ di ci (SG.decodeOrdˢ rng-G vg) ≈ˢ SF.decodeOrdˢ rng-F vH
    → castˢ df cf (SF.decodeOrdˢ rng-F vf)
      ≈ˢ castˢ dg cg (SG.decodeOrdˢ rng-G vg)
  decodeOrdˢ-boundary-resp-≈ vf vg vH wiring≈ =
    -- The whole chain is endpoint bookkeeping: drop the two boundary casts,
    -- swap `vf` for `vH` (K₁), reverse the wiring, and re-cast — the `_≈̂_`
    -- combinators absorb the `cast-fuse`/`cast-irrel` `List X`-UIP algebra.
    ≈̂⇒≈ˢ
      (≈̂-trans cast-≈̂                                -- drop `df`/`cf`
      (≈̂-trans (≈ˢ⇒≈̂ (decodeOrdˢ-witness-coh vf vH))  -- (K₁) `vf` → `vH`
      (≈̂-trans (≈̂-sym (≈ˢ⇒≈̂ wiring≈))                 -- reversed wiring
      (≈̂-trans (cast-≈̂ {p = di} {q = ci})            -- drop `di`/`ci` (pinned)
               (≈̂-sym cast-≈̂)))))                    -- re-cast `dg`/`cg`

------------------------------------------------------------------------
-- THE UNCONDITIONAL HEADLINE.  Wires the order-theory core
-- (`order-invariantˢ`, BUILT) and the boundary against the now-discharged
-- cross-iso decoder agreement `IT.decode-ordˢ-resp-iso`, fed the
-- `run-interchange-H` built above.
------------------------------------------------------------------------

decodePˢ-resp-iso : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decodePˢ f ≈ˢ decodePˢ g
decodePˢ-resp-iso f g iso =
  subst₂ (λ a b → a ≈ˢ b)
         (sym (decodePˢ-≡-cast f))
         (sym (decodePˢ-≡-cast g))
         (B.decodeOrdˢ-boundary-resp-≈ (vrangeˢ f) (vrangeˢ g) vH wiring≈)
  where
    module B = Boundary f g iso
    res = IT.decode-ordˢ-resp-iso f g iso (run-interchange-H f) (vrangeˢ g)
    vH      = proj₁ res
    wiring≈ = proj₂ res

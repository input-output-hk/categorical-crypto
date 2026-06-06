-- Discharges the `decodeOrd-boundary-resp-≈` residual of
-- `DecodeRelRespIsoWired`, GIVEN K.  It relates the two natural-order
-- decodings of `⟪f⟫` and `⟪g⟫` (at the `flatten` boundary), with content:
--
--   (K₁) The two `Valid ⟪f⟫ (range)` witnesses derive the same endpoints,
--        so their final `permute-via-vlab` factors agree by K
--        (`permute-resp-≅↭`); the `≅↭` hypothesis comes for free from
--        `eval-rigid` since the vertex-level `cod ⟪f⟫` is `Unique`.
--   (K₂) Pure `subst₂`-transport algebra for the boundary, needing UIP
--        on `ObjTerm`.
--
-- Both K-inputs are explicit parameters (`K`, `objUIP`).  The module is
-- `--without-K`, so the J-only `eval-rigid`/`eval-map⁺`/`subst₂-FinBij-≈`
-- helpers are imported from the shared K-free leaf.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeOrdBoundary
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig using (process-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map using (eval-map⁺; subst₂-FinBij-≈)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open import Data.List using (List; []; _∷_; map; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᵘ; _∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

------------------------------------------------------------------------
-- The lemma, GIVEN K (the Kelly residual + ObjTerm-UIP).
------------------------------------------------------------------------

module _ (K : FaithfulnessResidual)
         (objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q) where
  open FaithfulnessResidual K

  ----------------------------------------------------------------------
  -- (K₁) The two validity witnesses agree on their final permute, up to
  -- ≈Term.  Both derivations evaluate to the same FinBij (`eval-rigid`,
  -- since `cod ⟪f⟫` is `Unique`, transported through `eval-map⁺` +
  -- `subst₂-FinBij-≈`), which is the `≅↭` hypothesis K needs.
  ----------------------------------------------------------------------

  private
    permute-≅↭
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → eval-↭ (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) v)
        ≈-fb eval-↭ (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) w)
    permute-≅↭ {A} {B} f v w =
      subst (λ z → z ≈-fb eval-↭ (PermProp.map⁺ vlab w))
            (sym (eval-map⁺ vlab v))
        (subst (λ z → subst₂ FinBij (sym (length-map vlab stk))
                                    (sym (length-map vlab cod)) (eval-↭ v)
                      ≈-fb z)
               (sym (eval-map⁺ vlab w))
          (subst₂-FinBij-≈ (sym (length-map vlab stk)) (sym (length-map vlab cod))
            (eval-rigid (⟪ f ⟫-cod-unique) v w)))
      where
        vlab = Hypergraph.vlab ⟪ f ⟫
        stk  = proj₁ (process-edges ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))
                       (Hypergraph.dom ⟪ f ⟫))
        cod  = Hypergraph.cod ⟪ f ⟫

    permute-via-vlab-coh
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → permute-via-vlab (Hypergraph.vlab ⟪ f ⟫) v
        ≈Term permute-via-vlab (Hypergraph.vlab ⟪ f ⟫) w
    permute-via-vlab-coh f v w =
      permute-resp-≅↭
        (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) v)
        (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) w)
        (permute-≅↭ f v w)

    -- The two decodings differ only in the final-permute factor.
    decodeOrd-witness-coh
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) v
        ≈Term IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) w
    decodeOrd-witness-coh f v w =
      ∘-resp-≈ (permute-via-vlab-coh f v w) ≈-Term-refl

    ------------------------------------------------------------------
    -- (K₂) Pure subst₂-transport algebra for the boundary.

    subst₂-HomTerm-fuse
      : ∀ {a₁ a₂ a₃ : ObjTerm} {b₁ b₂ b₃ : ObjTerm}
          (pa : a₁ ≡ a₂) (pa' : a₂ ≡ a₃)
          (pb : b₁ ≡ b₂) (pb' : b₂ ≡ b₃)
          (t : HomTerm a₁ b₁)
      → subst₂ HomTerm pa' pb' (subst₂ HomTerm pa pb t)
        ≡ subst₂ HomTerm (trans pa pa') (trans pb pb') t
    subst₂-HomTerm-fuse refl refl refl refl t = refl

    subst₂-HomTerm-irr
      : ∀ {a₁ a₂ : ObjTerm} {b₁ b₂ : ObjTerm}
          (pa pa' : a₁ ≡ a₂) (pb pb' : b₁ ≡ b₂)
          (t : HomTerm a₁ b₁)
      → pa ≡ pa' → pb ≡ pb'
      → subst₂ HomTerm pa pb t ≡ subst₂ HomTerm pa' pb' t
    subst₂-HomTerm-irr pa pa' pb pb' t refl refl = refl

    subst₂-resp-≈
      : ∀ {a₁ a₂ : ObjTerm} {b₁ b₂ : ObjTerm}
          (pa : a₁ ≡ a₂) (pb : b₁ ≡ b₂) {s t : HomTerm a₁ b₁}
      → s ≈Term t → subst₂ HomTerm pa pb s ≈Term subst₂ HomTerm pa pb t
    subst₂-resp-≈ refl refl eq = eq

    ≈-of-≡ : ∀ {a b : ObjTerm} {s t : HomTerm a b} → s ≡ t → s ≈Term t
    ≈-of-≡ refl = ≈-Term-refl

  --------------------------------------------------------------------
  -- The headline lemma.
  --------------------------------------------------------------------

  decodeOrd-boundary-resp-≈
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (vf : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
        (vg : IW.PerHG.Valid ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)))
        (vH : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
    → ( subst₂ HomTerm (cong unflatten (IW.domL-iso iso)) (cong unflatten (IW.codL-iso iso))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg)
        ≈Term
        IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vH )
    → ( subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
          (IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vf)
        ≈Term
        subst₂ HomTerm (cong unflatten (⟪⟫-domL g)) (cong unflatten (⟪⟫-codL g))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg) )
  decodeOrd-boundary-resp-≈ {A} {B} f g iso vf vg vH wiring≈ =
    -- step1 (K₁), step2 (wiring≈), step3 (K₂).
    ≈-Term-trans step1 (≈-Term-trans step2 (≈-of-≡ step3))
    where
      df  = cong unflatten (⟪⟫-domL f)
      cf  = cong unflatten (⟪⟫-codL f)
      dg  = cong unflatten (⟪⟫-domL g)
      cg  = cong unflatten (⟪⟫-codL g)
      di  = cong unflatten (IW.domL-iso iso)
      ci  = cong unflatten (IW.codL-iso iso)

      dOrd-f-vr = IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vf
      dOrd-f-vH = IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vH
      dOrd-g    = IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg

      step1
        : subst₂ HomTerm df cf dOrd-f-vr ≈Term subst₂ HomTerm df cf dOrd-f-vH
      step1 = subst₂-resp-≈ df cf (decodeOrd-witness-coh f vf vH)

      step2
        : subst₂ HomTerm df cf dOrd-f-vH
          ≈Term subst₂ HomTerm df cf (subst₂ HomTerm di ci dOrd-g)
      step2 = subst₂-resp-≈ df cf (≈-Term-sym wiring≈)

      dom-uip : trans di df ≡ dg
      dom-uip = objUIP (trans di df) dg

      cod-uip : trans ci cf ≡ cg
      cod-uip = objUIP (trans ci cf) cg

      step3
        : subst₂ HomTerm df cf (subst₂ HomTerm di ci dOrd-g)
          ≡ subst₂ HomTerm dg cg dOrd-g
      step3 =
        trans (subst₂-HomTerm-fuse di df ci cf dOrd-g)
              (subst₂-HomTerm-irr (trans di df) dg (trans ci cf) cg dOrd-g
                                  dom-uip cod-uip)

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT Lemma 0: the cross-iso decoder agreement `decode-ordˢ-resp-iso`
-- (the last unported part-(II)ˢ piece — strict twin of
-- `Discharge.IsoInvarianceConcrete.decode-ord-resp-iso`, assembling the
-- strict `Discharge.IsoTransport.iso-transport`).
--
-- For a cross-iso `iso : ⟪f⟫ ≅ᴴ ⟪g⟫` we produce
--
--   decode-ordˢ-resp-iso
--     : (vJ : SG.Validˢ (range nE_g))
--     → Σ[ vH ∈ SF.Validˢ (range nE_f) ]
--         castˢ (IW.domL-iso iso) (IW.codL-iso iso)
--               (SG.decodeOrdˢ (range nE_g) vJ)
--         ≈ˢ SF.decodeOrdˢ (range nE_f) vH
--
-- — EXACTLY the parameter `Strict.DecodePRespIso`'s headline `module _`
-- consumes (lines 174-191).
--
-- Structure (strict twin of `IsoTransport` §1-§5 + the `order-invariant`
-- bridge):
--
--   * `iso-transportˢ`   transports the J=⟪g⟫-side natural-order decoding to
--     the H=⟪f⟫-side ψ-pullback order `τ = map ψ⁻¹ (range J.nE)`.  Its term
--     factor is the strict embedding engine `TermEmbedˢ.process-edges-term-embˢ`
--     (φ = iso's vertex map, ψ = iso's edge map) — the `subst₂ HomTerm` /
--     `subst₂-∘-distrib` / `map⁺`-lift mass of the non-strict §3 VANISHES into
--     `castˢ`; its permute factor is `permute-relabel-freeˢ` (§5b ported
--     verbatim at the FinBij level, routed through the X-level permute
--     `permuteˢ-X` and discharged by `permˢ-K-X`).
--   * `order-invariantˢ` (`IsoInvarianceConcreteS`, BUILT) bridges `τ` to the
--     natural order `range nE_f`.
--
-- The order-theory `NoInv`/`NoInv-τ`/`τ`/`τ↭range` are reused verbatim from
-- the term-free non-strict wiring (`IsoInvarianceWiring`, `WiringLemmas`).
-- The strict run-interchange residual `run-interchange-H` is threaded as a
-- module parameter (the same residual `DecodePRespIso`'s headline takes).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.IsoTransportS
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-cod-unique)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)
open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.WiringLemmas sig as WL
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Soundness.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
  using (module Run)
import Categories.APROP.Hypergraph.Soundness.Strict.SwapStepS sig _≟X_ as SS
import Categories.APROP.Hypergraph.Soundness.Strict.IsoInvarianceConcreteS sig _≟X_ as IC
import Categories.APROP.Hypergraph.Soundness.Strict.DecodeComposeS2 sig _≟X_ as DC2
open import Categories.APROP.Hypergraph.Soundness.Strict.RunInterchangeTailS sig _≟X_
  using (RunInterchangeˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.PermK sig _≟X_ as PK
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
  using (module Support)

open import Data.Fin.Base using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (map-∘; map-cong; map-id; map-++; map-injective; length-map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Function using (Injective)
import Data.Fin.Permutation as P
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Rigid
  using (lookup-injective-unique; lookup-sound)
open import Categories.PermuteCoherence.Map
  using ( eval-map⁺; lookup-map; subst₂-FinBij-as-subst; cast-irr
        ; subst-Fin-trans; lookup-subst-list; subst-Fin-roundtrip
        ; subst-Fin-roundtrip'; subst-Fin-sym-sym; ≈-fb-of-≡; eval-subst₂-↭ )

------------------------------------------------------------------------
-- The cross-iso module.  `H = ⟪f⟫`, `J = ⟪g⟫`.
------------------------------------------------------------------------

module _ {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
         (run-interchange-H
           : ∀ (ps qs : SS.PerHG.Order ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f))
               {e e' : Fin (Hypergraph.nE ⟪ f ⟫)}
               (inc : SS.PerHG.Incompˢ ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f) e e')
             → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE ⟪ f ⟫)
             → RunInterchangeˢ ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f) ps qs inc)
         where

  private
    H = ⟪ f ⟫ ; J = ⟪ g ⟫
    module H = Hypergraph H
    module J = Hypergraph J
    dihH = dep-irrefl-⟪⟫ f ; dihJ = dep-irrefl-⟪⟫ g
    linH : Linear H
    linH = DAL.⟪⟫-LinearP f
    linJ : Linear J
    linJ = DAL.⟪⟫-LinearP g
    module SF = SS.PerHG H dihH linH
    module SG = SS.PerHG J dihJ linJ
    module RH = Run H
    module RJ = Run J

  open _≅ᴴ_ iso
    using (φ; φ⁻¹; ψ; ψ⁻¹; φ-left; φ-rght; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod; ψ-ein; ψ-eout; atom-ein; atom-eout; ψ-elab)

  -- φ injectivity (from the left inverse).
  φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  φ-Injective : Injective _≡_ _≡_ φ
  φ-Injective = φ-inj

  -- The boundary list equalities (= `IW.domL-iso`/`codL-iso iso`).
  di : domL J ≡ domL H
  di = IW.domL-iso iso
  ci : codL J ≡ codL H
  ci = IW.codL-iso iso

  -- The ψ-pullback order.
  τ : SF.Order
  τ = IW.τ iso

  ------------------------------------------------------------------------
  -- The strict embedding engine, instantiated at the iso's (φ, ψ).
  ------------------------------------------------------------------------

  module TE = DC2.TermEmbedˢ {H} {J}
    φ φ-inj φ-lab ψ ψ-ein ψ-eout atom-ein atom-eout ψ-elab

  -- `map J.vlab (map φ s) ≡ map H.vlab s`.
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ = TE.vlab-φ

  ------------------------------------------------------------------------
  -- §1.  Bridge `RJ.process-edgesˢ (range J.nE) J.dom` to the
  -- `TermEmbedˢ`-canonical shape `RJ.process-edgesˢ (map ψ τ) (map φ H.dom)`.
  ------------------------------------------------------------------------

  -- `map ψ τ = range J.nE` (ψ⁻¹ then ψ collapses).
  mapψτ : map ψ τ ≡ range J.nE
  mapψτ =
    trans (sym (map-∘ (range J.nE)))
          (trans (map-cong ψ-rght (range J.nE)) (map-id (range J.nE)))

  -- `map φ H.dom = J.dom`.
  mapφdom : map φ H.dom ≡ J.dom
  mapφdom = sym φ-dom

  ------------------------------------------------------------------------
  -- §2.  Final-stack identification.  `sJ-final ≡ map φ sH-final`.
  ------------------------------------------------------------------------

  private
    sH-final : List (Fin H.nV)
    sH-final = proj₁ (RH.process-edgesˢ τ H.dom)

    sJ-final : List (Fin J.nV)
    sJ-final = proj₁ (RJ.process-edgesˢ (range J.nE) J.dom)

  -- From `proc-stack-embˢ τ H.dom` (`TermEmbedˢ`), J running `map ψ τ` from
  -- `map φ H.dom` lands on `map φ sH-final`; the bridge re-expresses the LHS
  -- at the canonical `range J.nE` / `J.dom`.
  fin-eq : sJ-final ≡ map φ sH-final
  fin-eq =
    trans (sym (cong₂ (λ es s → proj₁ (RJ.process-edgesˢ es s)) mapψτ mapφdom))
          (TE.proc-stack-embˢ τ H.dom)

  ------------------------------------------------------------------------
  -- §3.  Validity (stack) transport.  `map φ` reflects `↭` (φ injective),
  -- exactly the non-strict `iso-valid`.
  ------------------------------------------------------------------------

  map-φ-↭⁻ : ∀ {xs ys : List (Fin H.nV)} → map φ xs Perm.↭ map φ ys → xs Perm.↭ ys
  map-φ-↭⁻ {xs} {ys} p with PermProp.↭-map-inv φ p
  ... | ys' , mapφys≡mapφys' , xs↭ys' =
        subst (xs Perm.↭_)
              (sym (map-injective {f = φ} φ-Injective mapφys≡mapφys'))
              xs↭ys'

  -- The strict validity `SG.Validˢ (range J.nE) = sJ-final ↭ J.cod`.
  iso-validˢ : SG.Validˢ (range J.nE) → SF.Validˢ τ
  iso-validˢ vJ = map-φ-↭⁻ step
    where
      step : map φ sH-final Perm.↭ map φ H.cod
      step =
        subst (λ z → z Perm.↭ map φ H.cod)
              fin-eq
              (subst (λ z → sJ-final Perm.↭ z) φ-cod vJ)

  ------------------------------------------------------------------------
  -- §4.  The X-level permute kit + the FINAL-permute relabel-freeness.
  --
  -- The strict `permuteˢ` is vertex-level; to compare a J-vertex permute
  -- with an H-vertex permute under the `map vlab` boundary casts we route
  -- both through the X-level permute (`permuteˢ-X`) and discharge by the
  -- X-level Kelly residual `permˢ-K-X`.  The premise is the FinBij-level
  -- `≅↭` evidence `permute-relabel-free-≅↭` (§5b, ported verbatim).
  ------------------------------------------------------------------------

  private
    permˢ-K-X : Support.PermK X (λ x → x)
    permˢ-K-X = PK.permˢ-K X _≟X_ (λ x → x)

    open DC2.XPerm using (permuteˣ)
    -- the X-level permute boundary cast helper from §0.
    open DC2 using (permuteˢ-X; mp)

    -- The two final-permute derivations, lifted to the common X-level pair
    -- of `map _.vlab _` lists.
    permJ-↭ : (vJ : SG.Validˢ (range J.nE))
            → map J.vlab sJ-final Perm.↭ map J.vlab J.cod
    permJ-↭ vJ = PermProp.map⁺ J.vlab vJ

    -- the mid (final-stack) object-equality.
    mid-iso : map J.vlab sJ-final ≡ map H.vlab sH-final
    mid-iso = trans (cong (map J.vlab) fin-eq) (vlab-φ sH-final)

    permJ-↭' : (vJ : SG.Validˢ (range J.nE))
             → map H.vlab sH-final Perm.↭ map H.vlab H.cod
    permJ-↭' vJ = subst₂ Perm._↭_ mid-iso ci (permJ-↭ vJ)

    permH-↭ : (vJ : SG.Validˢ (range J.nE))
            → map H.vlab sH-final Perm.↭ map H.vlab H.cod
    permH-↭ vJ = PermProp.map⁺ H.vlab (iso-validˢ vJ)

    -- The length casts.
    cH-dom : length (map H.vlab sH-final) ≡ length sH-final
    cH-dom = length-map H.vlab sH-final
    cH-cod : length (map H.vlab H.cod) ≡ length H.cod
    cH-cod = length-map H.vlab H.cod

    cJH : length J.cod ≡ length H.cod
    cJH = trans (cong length φ-cod) (length-map φ H.cod)

    -- `lookup J.cod` factors as `φ ∘ lookup H.cod` after the `cJH` cast.
    lookup-Jcod-φ
      : (k : Fin (length J.cod))
      → φ (lookup H.cod (subst Fin cJH k)) ≡ lookup J.cod k
    lookup-Jcod-φ k =
      trans (sym (lookup-map φ H.cod (subst Fin cJH k)))
        (trans (cong (lookup (map φ H.cod)) reduce-idx)
               (lookup-subst-list φ-cod k))
      where
        reduce-idx
          : subst Fin (sym (length-map φ H.cod)) (subst Fin cJH k)
            ≡ subst Fin (cong length φ-cod) k
        reduce-idx =
          trans (cong (subst Fin (sym (length-map φ H.cod)))
                      (sym (subst-Fin-trans (cong length φ-cod) (length-map φ H.cod) k)))
                (subst-Fin-roundtrip (length-map φ H.cod)
                   (subst Fin (cong length φ-cod) k))

    cSJH : length sJ-final ≡ length sH-final
    cSJH = trans (cong length fin-eq) (length-map φ sH-final)

    lookup-sJ-φ
      : (k : Fin (length sJ-final))
      → φ (lookup sH-final (subst Fin cSJH k)) ≡ lookup sJ-final k
    lookup-sJ-φ k =
      trans (sym (lookup-map φ sH-final (subst Fin cSJH k)))
        (trans (cong (lookup (map φ sH-final)) reduce-idx)
               (lookup-subst-list fin-eq k))
      where
        reduce-idx
          : subst Fin (sym (length-map φ sH-final)) (subst Fin cSJH k)
            ≡ subst Fin (cong length fin-eq) k
        reduce-idx =
          trans (cong (subst Fin (sym (length-map φ sH-final)))
                      (sym (subst-Fin-trans (cong length fin-eq) (length-map φ sH-final) k)))
                (subst-Fin-roundtrip (length-map φ sH-final)
                   (subst Fin (cong length fin-eq) k))

  -- §5b.  φ-equivariant rigidity of the two final permutes, at the
  -- FinBij level (ported verbatim from the non-strict `IsoTransport`).
  permute-relabel-free-≅↭
    : (vJ : SG.Validˢ (range J.nE))
    → eval-↭ (permJ-↭' vJ) ≈-fb eval-↭ (permH-↭ vJ)
  permute-relabel-free-≅↭ vJ i = goal
    where
      kJ kH : Fin (length (map H.vlab H.cod))
      kJ = eval-↭ (permJ-↭' vJ) P.⟨$⟩ʳ i
      kH = eval-↭ (permH-↭ vJ) P.⟨$⟩ʳ i

      iH : Fin (length sH-final)
      iH = subst Fin cH-dom i

      kH≡ : subst Fin cH-cod kH ≡ eval-↭ (iso-validˢ vJ) P.⟨$⟩ʳ iH
      kH≡ =
        trans (cong (λ z → subst Fin cH-cod (z P.⟨$⟩ʳ i))
                    (eval-map⁺ H.vlab (iso-validˢ vJ)))
        (trans (cong (subst Fin cH-cod)
                     (subst₂-FinBij-as-subst (sym cH-dom) (sym cH-cod)
                        (eval-↭ (iso-validˢ vJ)) i))
        (trans (subst-Fin-roundtrip' cH-cod
                  (eval-↭ (iso-validˢ vJ) P.⟨$⟩ʳ subst Fin (sym (sym cH-dom)) i))
               (cong (eval-↭ (iso-validˢ vJ) P.⟨$⟩ʳ_)
                     (subst-Fin-sym-sym cH-dom i))))

      H-step : lookup H.cod (subst Fin cH-cod kH) ≡ lookup sH-final iH
      H-step =
        trans (cong (lookup H.cod) kH≡)
              (lookup-sound (iso-validˢ vJ) iH)

      iJ : Fin (length sJ-final)
      iJ = subst Fin (sym cSJH) iH

      jJ : Fin (length J.cod)
      jJ = eval-↭ vJ P.⟨$⟩ʳ iJ

      private-lmJd : length (map J.vlab sJ-final) ≡ length sJ-final
      private-lmJd = length-map J.vlab sJ-final
      private-lmJc : length (map J.vlab J.cod) ≡ length J.cod
      private-lmJc = length-map J.vlab J.cod

      kJ≡ : subst Fin cH-cod kJ ≡ subst Fin cJH jJ
      kJ≡ =
        trans (cong (λ z → subst Fin cH-cod (z P.⟨$⟩ʳ i))
                    (trans (eval-subst₂-↭ mid-iso ci (permJ-↭ vJ))
                           (cong (subst₂ FinBij (cong length mid-iso)
                                                 (cong length ci))
                                 (eval-map⁺ J.vlab vJ))))
        (trans (cong (subst Fin cH-cod)
                     (subst₂-FinBij-as-subst (cong length mid-iso) (cong length ci)
                        (subst₂ FinBij (sym private-lmJd) (sym private-lmJc) (eval-↭ vJ)) i))
        (trans (cong (λ z → subst Fin cH-cod (subst Fin (cong length ci) z))
                     (subst₂-FinBij-as-subst (sym private-lmJd) (sym private-lmJc) (eval-↭ vJ)
                        (subst Fin (sym (cong length mid-iso)) i)))
          (cod-collapse)))
        where
          DOM₀ : Fin (length sJ-final)
          DOM₀ = subst Fin (sym (sym private-lmJd))
                   (subst Fin (sym (cong length mid-iso)) i)

          IMG : Fin (length J.cod)
          IMG = eval-↭ vJ P.⟨$⟩ʳ DOM₀

          dom-eq : DOM₀ ≡ iJ
          dom-eq =
            trans (subst-Fin-trans (sym (cong length mid-iso)) (sym (sym private-lmJd)) i)
            (trans (cast-irr (trans (sym (cong length mid-iso)) (sym (sym private-lmJd)))
                             (trans cH-dom (sym cSJH)) i)
                   (sym (subst-Fin-trans cH-dom (sym cSJH) i)))

          cod-collapse
            : subst Fin cH-cod
                (subst Fin (cong length ci)
                   (subst Fin (sym private-lmJc) IMG))
              ≡ subst Fin cJH jJ
          cod-collapse =
            trans (cong (subst Fin cH-cod)
                        (subst-Fin-trans (sym private-lmJc) (cong length ci) IMG))
            (trans (subst-Fin-trans
                      (trans (sym private-lmJc) (cong length ci)) cH-cod IMG)
            (trans (cast-irr
                      (trans (trans (sym private-lmJc) (cong length ci)) cH-cod)
                      cJH IMG)
                   (cong (subst Fin cJH) (cong (eval-↭ vJ P.⟨$⟩ʳ_) dom-eq))))

      J-step : lookup H.cod (subst Fin cH-cod kJ) ≡ lookup sH-final iH
      J-step =
        φ-inj
          (trans
            (trans (cong (λ z → φ (lookup H.cod z)) kJ≡)
              (trans (lookup-Jcod-φ jJ)
                     (lookup-sound vJ iJ)))
            (trans (sym (lookup-sJ-φ iJ))
                   (cong (λ z → φ (lookup sH-final z))
                         (subst-Fin-roundtrip' cSJH iH))))

      goal : kJ ≡ kH
      goal =
        trans (sym (subst-Fin-roundtrip cH-cod kJ))
        (trans (cong (subst Fin (sym cH-cod))
                     (lookup-injective-unique (⟪ f ⟫-cod-unique)
                        (subst Fin cH-cod kJ) (subst Fin cH-cod kH)
                        (trans J-step (sym H-step))))
               (subst-Fin-roundtrip cH-cod kH))

  ------------------------------------------------------------------------
  -- §5.  The FINAL-permute relabel-free `≈ˢ`, from `permˢ-K-X` + §5b,
  -- routed through `permuteˢ-X`.
  ------------------------------------------------------------------------

  -- `permuteˢ` commutes with `subst₂` along list equalities (vertex level).
  private
    permuteˢ-subst₂H
      : ∀ {xs xs' ys ys' : List (Fin H.nV)} (p : xs ≡ xs') (q : ys ≡ ys')
          (r : xs Perm.↭ ys)
      → RH.permuteˢ (subst₂ Perm._↭_ p q r)
        ≡ castˢ (cong (map H.vlab) p) (cong (map H.vlab) q) (RH.permuteˢ r)
    permuteˢ-subst₂H refl refl r = refl

    -- `permuteˢ` commutes with `map⁺ vlab` routed through the X-level permute.
    -- (the §0 `permuteˢ-X` instance at the relevant vertex set.)
    pXJ : ∀ {xs ys : List (Fin J.nV)} (p : xs Perm.↭ ys)
        → castˢ (mp (Fin J.nV) J.vlab xs) (mp (Fin J.nV) J.vlab ys)
            (permuteˣ (PermProp.map⁺ J.vlab p)) ≈ˢ RJ.permuteˢ p
    pXJ = permuteˢ-X (Fin J.nV) J.vlab

    pXH : ∀ {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
        → castˢ (mp (Fin H.nV) H.vlab xs) (mp (Fin H.nV) H.vlab ys)
            (permuteˣ (PermProp.map⁺ H.vlab p)) ≈ˢ RH.permuteˢ p
    pXH = permuteˢ-X (Fin H.nV) H.vlab

  -- The strict final-permute relabel-free lemma.
  permute-relabel-freeˢ
    : (vJ : SG.Validˢ (range J.nE))
    → castˢ mid-iso ci (RJ.permuteˢ vJ) ≈ˢ RH.permuteˢ (iso-validˢ vJ)
  permute-relabel-freeˢ vJ =
    -- LHS: castˢ mid-iso ci (permuteˢ_J vJ)
    --   ≈  castˢ mid-iso ci (castˢ (mp .) (mp .) (permuteˣ (map⁺ vlJ vJ)))   [≈-sym pXJ]
    --   →  rebracket to a single castˢ of permuteˣ (map⁺ vlJ vJ);
    -- the X-level Kelly residual swaps `map⁺ vlJ vJ` for `map⁺ vlH (isoval)`;
    -- RHS: re-express via pXH.
    ≈-trans (cast-resp mid-iso ci (≈-sym (pXJ vJ)))
    (≈-trans middle (pXH (iso-validˢ vJ)))
    where
      mpJd = mp (Fin J.nV) J.vlab sJ-final
      mpJc = mp (Fin J.nV) J.vlab J.cod
      mpHd = mp (Fin H.nV) H.vlab sH-final
      mpHc = mp (Fin H.nV) H.vlab H.cod
      Xj = permuteˣ (PermProp.map⁺ J.vlab vJ)
      Xh = permuteˣ (PermProp.map⁺ H.vlab (iso-validˢ vJ))

      -- the FinBij identification: `permJ-↭' vJ` IS this `subst₂`, so §5b is it.
      ev : eval-↭ (subst₂ Perm._↭_ mid-iso ci (PermProp.map⁺ J.vlab vJ))
           ≈-fb eval-↭ (PermProp.map⁺ H.vlab (iso-validˢ vJ))
      ev = permute-relabel-free-≅↭ vJ

      -- the X-level identification:
      --   Xh ≈ castˢ (cong(map id)mid-iso)(cong(map id)ci) Xj
      private-permuteˣ-subst₂
        : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
            (r : xs Perm.↭ ys)
        → permuteˣ (subst₂ Perm._↭_ p q r)
          ≡ castˢ (cong (map (λ x → x)) p) (cong (map (λ x → x)) q) (permuteˣ r)
      private-permuteˣ-subst₂ refl refl r = refl

      K-step : Xh ≈ˢ castˢ (cong (map (λ x → x)) mid-iso) (cong (map (λ x → x)) ci) Xj
      K-step =
        ≈-trans
          (≈-sym (permˢ-K-X (subst₂ Perm._↭_ mid-iso ci (PermProp.map⁺ J.vlab vJ))
                            (PermProp.map⁺ H.vlab (iso-validˢ vJ)) ev))
          (≡⇒≈ˢ (private-permuteˣ-subst₂ mid-iso ci (PermProp.map⁺ J.vlab vJ)))

      -- `castˢ mid-iso ci (castˢ mpJ Xj) ≈ castˢ mpH Xh`, via cast-fuse on
      -- both sides + cast-irrel (endpoints coincide after K-step).
      middle
        : castˢ mid-iso ci (castˢ mpJd mpJc Xj) ≈ˢ castˢ mpHd mpHc Xh
      middle =
        ≈-trans (≡⇒≈ˢ (cast-fuse mpJd mid-iso mpJc ci Xj))
        (≈-trans (≡⇒≈ˢ (cast-irrel (trans mpJd mid-iso)
                          (trans (cong (map (λ x → x)) mid-iso) mpHd)
                          (trans mpJc ci)
                          (trans (cong (map (λ x → x)) ci) mpHc) Xj))
        (≈-trans (≡⇒≈ˢ (sym (cast-fuse (cong (map (λ x → x)) mid-iso) mpHd
                                       (cong (map (λ x → x)) ci) mpHc Xj)))
          (≈-sym (cast-resp mpHd mpHc K-step))))

  ------------------------------------------------------------------------
  -- §6.  `iso-transportˢ`: the J-side decoding at `range J.nE` casts to the
  -- H-side decoding at the pullback order `τ`.
  ------------------------------------------------------------------------

  -- The term factor: bridge `TermEmbedˢ.process-edges-term-embˢ` from the
  -- canonical `map ψ τ`/`map φ H.dom` shape to `range J.nE`/`J.dom`.
  private
    -- canonical pCod for `process-edges-term-embˢ τ H.dom`.
    pCod-can : map J.vlab (proj₁ (RJ.process-edgesˢ (map ψ τ) (map φ H.dom)))
             ≡ map H.vlab (proj₁ (RH.process-edgesˢ τ H.dom))
    pCod-can =
      trans (cong (map J.vlab) (TE.proc-stack-embˢ τ H.dom)) (vlab-φ sH-final)

  -- The process-edges term twin at the canonical shape.
  proc-twin-can
    : castˢ (vlab-φ H.dom) pCod-can
        (proj₂ (RJ.process-edgesˢ (map ψ τ) (map φ H.dom)))
      ≈ˢ proj₂ (RH.process-edgesˢ τ H.dom)
  proc-twin-can = TE.process-edges-term-embˢ τ H.dom pCod-can

  -- Re-express the J-run at `range J.nE`/`J.dom` (the bridge `subst`).  The
  -- whole `process-edgesˢ`-package is transported along `mapψτ`/`mapφdom`.
  private
    -- The bridged term twin: `castˢ di mid-iso (proj₂ (RJ.process-edgesˢ
    -- (range J.nE) J.dom)) ≈ proj₂ (RH.process-edgesˢ τ H.dom)`.
    bridge-pkg
      : ∀ (esJ : List (Fin J.nE)) (sJ : List (Fin J.nV))
          (es≡ : esJ ≡ map ψ τ) (s≡ : sJ ≡ map φ H.dom)
          (pD : map J.vlab sJ ≡ map H.vlab H.dom)
          (pC : map J.vlab (proj₁ (RJ.process-edgesˢ esJ sJ))
                ≡ map H.vlab (proj₁ (RH.process-edgesˢ τ H.dom)))
      → castˢ pD pC (proj₂ (RJ.process-edgesˢ esJ sJ))
        ≈ˢ proj₂ (RH.process-edgesˢ τ H.dom)
    bridge-pkg .(map ψ τ) .(map φ H.dom) refl refl pD pC =
      ≈-trans (≡⇒≈ˢ (cast-irrel pD (vlab-φ H.dom) pC pCod-can
                       (proj₂ (RJ.process-edgesˢ (map ψ τ) (map φ H.dom)))))
              proc-twin-can

  proc-twin
    : castˢ di mid-iso (proj₂ (RJ.process-edgesˢ (range J.nE) J.dom))
      ≈ˢ proj₂ (RH.process-edgesˢ τ H.dom)
  proc-twin = bridge-pkg (range J.nE) J.dom (sym mapψτ) (sym mapφdom) di mid-iso

  -- `iso-transportˢ`, assembled `∘-cast-split`-then-`∘-resp`.
  iso-transportˢ
    : (vJ : SG.Validˢ (range J.nE))
    → castˢ di ci (SG.decodeOrdˢ (range J.nE) vJ)
      ≈ˢ SF.decodeOrdˢ τ (iso-validˢ vJ)
  iso-transportˢ vJ =
    ≈-trans (∘-cast-split di mid-iso ci permJ procJ)
            (∘-resp (permute-relabel-freeˢ vJ) proc-twin)
    where
      procJ = proj₂ (RJ.process-edgesˢ (range J.nE) J.dom)
      permJ = RJ.permuteˢ vJ

  ------------------------------------------------------------------------
  -- §7.  Bridge `τ` to the natural order `range nE_f` via `order-invariantˢ`,
  -- and assemble the headline.
  ------------------------------------------------------------------------

  private
    module CPH = IC.PerHG H dihH linH (⟪ f ⟫-cod-unique) run-interchange-H
    module L4  = WL.Lemma4 iso dihH dihJ

  -- the natural-order no-inversion witnesses (`FinOrderNoInv`, BUILT).
  noInvH : SF.NoInv (range H.nE)
  noInvH = fin-order-NoInv-⟪⟫ f
  noInvJ : SG.NoInv (range J.nE)
  noInvJ = fin-order-NoInv-⟪⟫ g

  -- `NoInv-τ` (`WiringLemmas` Lemma 4), fed J's no-inversion.
  NoInv-τ : SF.NoInv τ
  NoInv-τ = L4.NoInv-τ noInvJ

  decode-ordˢ-resp-iso
    : (vJ : SG.Validˢ (range J.nE))
    → Σ[ vH ∈ SF.Validˢ (range H.nE) ]
        castˢ di ci (SG.decodeOrdˢ (range J.nE) vJ)
        ≈ˢ SF.decodeOrdˢ (range H.nE) vH
  decode-ordˢ-resp-iso vJ =
    let vτ            = iso-validˢ vJ
        transport≈    = iso-transportˢ vJ
        (vH , inv≈)   =
          CPH.order-invariantˢ τ (range H.nE) (IW.τ↭range iso) NoInv-τ
                               noInvH (IW.τ↭range iso) vτ
    in vH , ≈-trans transport≈ inv≈

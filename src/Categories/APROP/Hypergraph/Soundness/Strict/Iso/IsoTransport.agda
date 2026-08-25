{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT Lemma 0: the cross-iso decoder agreement `decode-ordˢ-resp-iso`
-- (assembling the strict order-invariance core with the cross-iso
-- transport residual `iso-transportˢ`).
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
-- — exactly the cross-iso agreement `Strict.PartII`'s headline consumes.
--
-- Structure (§0-§6):
--
--   * `order-invariantˢ` (§0, BUILT) bridges any two `NoInv` orders of one
--     hypergraph: PURE `≈ˢ`-transitivity plumbing over the adjacent-swap
--     closure, threading the strict validity witness `Validˢ` and the swap-site
--     `↭ range nE` provenance.  No Mac-Lane content.
--   * `iso-transportˢ`   transports the J=⟪g⟫-side natural-order decoding to
--     the H=⟪f⟫-side ψ-pullback order `τ = IW.τ iso` (which IS
--     `map ψ⁻¹ (range J.nE)`, but is taken from the wiring, not rebuilt
--     here).  Its term
--     factor is the strict embedding engine `TermEmbedˢ.term-emb-≈̂`
--     (φ = iso's vertex map, ψ = iso's edge map) — the `subst₂ HomTerm` /
--     `subst₂-∘-distrib` / `map⁺`-lift mass of the non-strict §3 VANISHES into
--     `castˢ`; its permute factor is `permute-relabel-freeˢ` (§4), the wiring
--     groupoid's RIGIDITY at the `Unique` codomain `J.cod` — the calculus's
--     `PermCalc.Kit.⟦relabel-rigid⟧` face, shared with the G- and K-blocks of
--     `DecodeComposeAssembly`.
--     `order-invariantˢ` then bridges `τ` to the natural order `range nE_f`.
--
-- The order-theory `NoInv`/`NoInv-τ`/`τ`/`τ↭range` are reused verbatim from
-- the term-free non-strict wiring (`IsoInvarianceWiring`).
-- The strict run-interchange residual `run-interchange-H` is threaded as a
-- module parameter (discharged by `PartII.run-interchange-H`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoTransport
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.HomTermInvariant sig using (⟪_⟫-cod-unique)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫; dep-irrefl-⟪⟫)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_ using (module Run)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig _≟X_ as SS
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig _≟X_ as DC2
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig _≟X_ as PC

open import Data.Fin.Base using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (map-injective)
open import Data.List.Properties.Ext using (map-∘-id)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Function using (Injective)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §0.  Per-hypergraph: the closure-lift and order-invariance.  Threads the
-- (N) residual `run-interchange` (the strict `RunInterchangeˢ` witness).
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             (uniq-cod : Unique (Hypergraph.cod H))
             (run-interchange : SS.PerHG.RunInterchangeAt H dih lin) where
  open SS.PerHG H dih lin
    using (Order; Validˢ; decodeOrdˢ; _↝_; _↝*_; NoInv; connectivity
          ; swap-step; swap-validityˢ)

  -- The per-swap analytic step (`SwapStep`), threaded the provenance.
  swap-≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
          → o₁ Perm.↭ range (Hypergraph.nE H)
          → (p₁ : Validˢ o₁) (p₂ : Validˢ o₂)
          → decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  swap-≈ˢ = SS.swap-≈ˢ H dih lin uniq-cod run-interchange

  -- An adjacent-independent swap IS a permutation (a transposition under
  -- the prefix `ps`), so it preserves the `↭ range nE` provenance.
  ↝⇒↭ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → o₁ Perm.↭ o₂
  ↝⇒↭ (swap-step ps {x} {y} qs _) = PermProp.++⁺ˡ ps (Perm.swap x y Perm.refl)

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- both the validity witness and the `↭ range nE` provenance.
  ↝*⇒≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂
        → o₁ Perm.↭ range (Hypergraph.nE H)
        → (p₁ : Validˢ o₁)
        → Σ[ p₂ ∈ Validˢ o₂ ] decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  ↝*⇒≈ˢ ε        o₁↭range p₁ = p₁ , ≈-refl
  ↝*⇒≈ˢ (s ◅ ss) o₁↭range p₁ =
    let p-mid          = swap-validityˢ s p₁
        o-mid↭range    = Perm.↭-trans (Perm.↭-sym (↝⇒↭ s)) o₁↭range
        (p₂ , mid≈rec) = ↝*⇒≈ˢ ss o-mid↭range p-mid
    in  p₂ , ≈-trans (swap-≈ˢ s o₁↭range p₁ p-mid) mid≈rec

  -- Order-invariance of the decoder, driven by `connectivity`.  The target
  -- order is the NATURAL one: `↝*⇒≈ˢ` needs the `↭ range nE` provenance
  -- anyway, and at `o₂ = range nE` that provenance IS the permutation
  -- `connectivity` consumes — so one hypothesis does both jobs.
  order-invariantˢ :
    ∀ (o₁ : Order) → o₁ Perm.↭ range (Hypergraph.nE H) →
    NoInv o₁ → NoInv (range (Hypergraph.nE H)) →
    (p₁ : Validˢ o₁) →
    Σ[ p₂ ∈ Validˢ (range (Hypergraph.nE H)) ]
      decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ (range (Hypergraph.nE H)) p₂
  order-invariantˢ o₁ p n₁ n₂ p₁ = ↝*⇒≈ˢ (connectivity p n₁ n₂) p p₁

------------------------------------------------------------------------
-- The cross-iso module.  `H = ⟪f⟫`, `J = ⟪g⟫`.
------------------------------------------------------------------------

module _ {A B : ObjTerm} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
         (run-interchange-H
           : SS.PerHG.RunInterchangeAt ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (DAL.⟪⟫-LinearP f))
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
    using (φ; φ⁻¹; ψ; φ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod; ψ-ein; ψ-eout; atom-ein; atom-eout; ψ-elab)

  -- φ injectivity (from the left inverse).  Stated at stdlib's `Injective`,
  -- which unfolds to the `∀ {x y} → φ x ≡ φ y → x ≡ y` the engine wants.
  φ-inj : Injective _≡_ _≡_ φ
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

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

  ------------------------------------------------------------------------
  -- §1.  Bridge `RJ.process-edgesˢ (range J.nE) J.dom` to the
  -- `TermEmbedˢ`-canonical shape `RJ.process-edgesˢ (map ψ τ) (map φ H.dom)`.
  ------------------------------------------------------------------------

  -- `map ψ τ = range J.nE` (ψ⁻¹ then ψ collapses).
  mapψτ : map ψ τ ≡ range J.nE
  mapψτ = map-∘-id ψ-rght (range J.nE)

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
              (sym (map-injective {f = φ} φ-inj mapφys≡mapφys'))
              xs↭ys'

  -- The strict validity `SG.Validˢ (range J.nE) = sJ-final ↭ J.cod`.
  iso-validˢ : SG.Validˢ (range J.nE) → SF.Validˢ τ
  iso-validˢ vJ = map-φ-↭⁻ step
    where
      step : map φ sH-final Perm.↭ map φ H.cod
      step = subst (λ z → z Perm.↭ map φ H.cod) fin-eq (subst (λ z → sJ-final Perm.↭ z) φ-cod vJ)

  ------------------------------------------------------------------------
  -- §4.  The FINAL-permute relabel-free `≈ˢ`.
  --
  -- Both derivations land on `J.cod`, which is `Unique`, so RIGIDITY of the
  -- wiring groupoid settles them.  That is the calculus's `⟦relabel-rigid⟧`
  -- face verbatim, at `φ = ` the iso's vertex map: it builds the φ-lift of the
  -- H-side derivation from `fin-eq`/`sym φ-cod` itself, absorbs both
  -- reindexings, and hands the residual to `pvv-≈̂`.  Shared with
  -- `DecodeComposeAssembly`'s `Yc-≈̂`/`Xc-≈̂` — no `eval-↭`, no `FinBij`,
  -- no `lookup`.
  ------------------------------------------------------------------------

  open PC.Kit J using (⟦relabel-rigid⟧)

  permute-relabel-freeˢ
    : (vJ : SG.Validˢ (range J.nE))
    → RJ.permuteˢ vJ ≈̂ RH.permuteˢ (iso-validˢ vJ)
  permute-relabel-freeˢ vJ =
    ⟦relabel-rigid⟧ H.vlab φ φ-lab (⟪ g ⟫-cod-unique) fin-eq (sym φ-cod)
                    vJ (iso-validˢ vJ)

  ------------------------------------------------------------------------
  -- §5.  `iso-transportˢ`: the J-side decoding at `range J.nE` casts to the
  -- H-side decoding at the pullback order `τ`.
  ------------------------------------------------------------------------

  -- The term factor: the embedding's canonical-endpoint face `term-emb-≈̂`,
  -- re-expressed at `range J.nE`/`J.dom`.  The J-run there IS the run at the
  -- `TermEmbedˢ`-canonical `map ψ τ`/`map φ H.dom` shape, so the bridge is a
  -- refl-match on `mapψτ`/`mapφdom` and carries no endpoint proof at all.
  proc-twin
    : ∀ (esJ : List (Fin J.nE)) (sJ : List (Fin J.nV))
    → esJ ≡ map ψ τ → sJ ≡ map φ H.dom
    → proj₂ (RJ.process-edgesˢ esJ sJ) ≈̂ proj₂ (RH.process-edgesˢ τ H.dom)
  proc-twin .(map ψ τ) .(map φ H.dom) refl refl = TE.term-emb-≈̂ τ H.dom

  -- `iso-transportˢ`, assembled `∘-resp-≈̂`-then-`≈̂⇒castˢ`: the mid object
  -- `map J.vlab sJ-final` is never named.
  iso-transportˢ
    : (vJ : SG.Validˢ (range J.nE))
    → castˢ di ci (SG.decodeOrdˢ (range J.nE) vJ)
      ≈ˢ SF.decodeOrdˢ τ (iso-validˢ vJ)
  iso-transportˢ vJ =
    ≈̂⇒castˢ (∘-resp-≈̂ (permute-relabel-freeˢ vJ)
                      (proc-twin (range J.nE) J.dom (sym mapψτ) (sym mapφdom)))
            di ci

  ------------------------------------------------------------------------
  -- §6.  Bridge `τ` to the natural order `range nE_f` via `order-invariantˢ`,
  -- and assemble the headline.
  ------------------------------------------------------------------------

  private
    module CPH = PerHG H dihH linH (⟪ f ⟫-cod-unique) run-interchange-H

  -- the natural-order no-inversion witnesses (`FinOrderNoInv`, BUILT).
  noInvH : SF.NoInv (range H.nE)
  noInvH = fin-order-NoInv-⟪⟫ f
  noInvJ : SG.NoInv (range J.nE)
  noInvJ = fin-order-NoInv-⟪⟫ g

  -- `NoInv-τ` (`IsoInvarianceWiring` Lemma 4), fed J's no-inversion.
  NoInv-τ : SF.NoInv τ
  NoInv-τ = IW.NoInv-τ iso noInvJ

  decode-ordˢ-resp-iso
    : (vJ : SG.Validˢ (range J.nE))
    → Σ[ vH ∈ SF.Validˢ (range H.nE) ]
        castˢ di ci (SG.decodeOrdˢ (range J.nE) vJ)
        ≈ˢ SF.decodeOrdˢ (range H.nE) vH
  decode-ordˢ-resp-iso vJ =
    let vτ            = iso-validˢ vJ
        transport≈    = iso-transportˢ vJ
        (vH , inv≈)   =
          CPH.order-invariantˢ τ (IW.τ↭range iso) NoInv-τ noInvH vτ
    in vH , ≈-trans transport≈ inv≈

{-# OPTIONS --safe --without-K #-}

-- Block factoring and relabelled term runs for the composition shape.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.Combinatorics.ExtractPrefix
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
  using (module StackLiftEmb)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig public

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermRelabel sig
  as PVV
open import Categories.Combinatorics.ExtractPrefixEvalPhi using (extract-prefix-pin)

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Ext
open import Relation.Binary.PropositionalEquality.Properties.Ext

--------------------------------------------------------------------------------
-- Block factoring
--------------------------------------------------------------------------------

module RunBlocks (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  coeCod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomS (map vl d) (map vl s)
    → HomS (map vl d) (map vl s')
  coeCod e = castˢ refl (cong (map vl) e)

  absorbˢ
    : ∀ {ys : List (Fin H.nV)} {s s' : List (Fin H.nV)} (eq : s ≡ s')
        (perm : s' Perm.↭ ys)
        (T : HomS (map vl H.dom) (map vl s))
    → permuteˢ perm ∘ˢ coeCod eq T
      ≈ˢ permuteˢ (subst (Perm._↭ ys) (sym eq) perm) ∘ˢ T
  absorbˢ refl perm T = ≈-refl

  pe-term-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ (ps ++ rest) s)
      ≈ˢ coeCod (sym (pe-stack-++ˢ ps rest s))
           (proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
             ∘ˢ proj₂ (process-edgesˢ ps s))
  pe-term-++ˢ []       rest s = ≈-sym idʳ
  pe-term-++ˢ (e ∷ ps) rest s =
    ≈-trans (∘-resp (pe-term-++ˢ ps rest s') ≈-refl)
            (coeCod-reassoc E R G t)
    where
      s' = proj₁ (edge-stepˢ s e)
      t  = proj₂ (edge-stepˢ s e)
      G  = proj₂ (process-edgesˢ ps s')
      R  = proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s')))
      E  = sym (pe-stack-++ˢ ps rest s')

      coeCod-reassoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (R0 : HomS (map vl (proj₁ (process-edgesˢ ps s'))) (map vl a))
            (G0 : HomS (map vl s') (map vl (proj₁ (process-edgesˢ ps s'))))
            (t0 : HomS (map vl s) (map vl s'))
        → coeCod eq (R0 ∘ˢ G0) ∘ˢ t0 ≈ˢ coeCod eq (R0 ∘ˢ (G0 ∘ˢ t0))
      coeCod-reassoc refl R0 G0 t0 = assocˢ

  run-split-atˢ
    : ∀ {es : List (Fin H.nE)} (gblk kblk : List (Fin H.nE))
        (eq : es ≡ gblk ++ kblk) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ es s)
      ≈ˢ coeCod (sym (trans (cong (λ z → proj₁ (process-edgesˢ z s)) eq)
                            (pe-stack-++ˢ gblk kblk s)))
           (proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk s)))
             ∘ˢ proj₂ (process-edgesˢ gblk s))
  -- This orientation of `trans` reduces at `eq = refl`.
  run-split-atˢ gblk kblk refl s = pe-term-++ˢ gblk kblk s

private
  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

  cast-⊗-split
    : ∀ {xs xs' ys ys' us us' vs vs'}
        (px : xs ≡ xs') (py : ys ≡ ys') (pu : us ≡ us') (pv : vs ≡ vs')
        (f : HomS xs ys) (g : HomS us vs)
        (P : xs ++ us ≡ xs' ++ us') (Q : ys ++ vs ≡ ys' ++ vs')
    → castˢ P Q (f ⊗ˢ g) ≈ˢ castˢ px py f ⊗ˢ castˢ pu pv g
  cast-⊗-split refl refl refl refl f g P Q rewrite uipL P refl | uipL Q refl = ≈-refl

module TermEmbedˢ
  {H J : Hypergraph FlatGen}
  (let module H = Hypergraph H)
  (let module J = Hypergraph J)
  (φ      : Fin H.nV → Fin J.nV)
  (φ-inj  : ∀ {x y} → φ x ≡ φ y → x ≡ y)
  (φ-lab  : ∀ i → J.vlab (φ i) ≡ H.vlab i)
  (ψ      : Fin H.nE → Fin J.nE)
  (ψ-ein  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
  (ψ-eout : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
  (atom-ein  : ∀ e → map J.vlab (J.ein  (ψ e)) ≡ map H.vlab (H.ein  e))
  (atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e))
  (ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e))
                ≡ H.elab e)
  where

  private
    module RH = Run H
    module RJ = Run J

  vlH = H.vlab
  vlJ = J.vlab

  vlab-φ : ∀ (s : List (Fin H.nV)) → map vlJ (map φ s) ≡ map vlH s
  vlab-φ = map-∘-cong φ-lab

  open StackLiftEmb J H ψ φ φ-inj ψ-ein ψ-eout public
    renaming ( hit  to extract-prefix-J-just
             ; miss to extract-prefix-J-nothing
             ; edge-step-lift     to edge-step-stack-embˢ
             ; process-edges-lift to proc-stack-embˢ )

  box-emb
    : ∀ (e : Fin H.nE) (restH : List (Fin H.nV)) (restJ : List (Fin J.nV))
        (restJ≡ : restJ ≡ map φ restH)
        (rest-lab : map vlJ restJ ≡ map vlH restH)
        (P : map vlJ (J.ein  (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.ein  e) ++ map vlH restH)
        (Q : map vlJ (J.eout (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.eout e) ++ map vlH restH)
    → castˢ P Q (genˢ (J.elab (ψ e)) ⊗ˢ idˢ {map vlJ restJ})
      ≈ˢ genˢ (H.elab e) ⊗ˢ idˢ {map vlH restH}
  box-emb e restH restJ restJ≡ rest-lab P Q =
    ≈-trans
      (cast-⊗-split (atom-ein e) (atom-eout e) rest-lab rest-lab
        (genˢ (J.elab (ψ e))) (idˢ {map vlJ restJ}) P Q)
      (⊗-resp gen-side (cast-id rest-lab rest-lab))
    where
      gen-side : castˢ (atom-ein e) (atom-eout e) (genˢ (J.elab (ψ e)))
                 ≈ˢ genˢ (H.elab e)
      gen-side =
        ≡⇒≈ˢ (trans (gen-cast (atom-ein e) (atom-eout e) (J.elab (ψ e)))
                    (cong genˢ (ψ-elab e)))

  -- Relabelled search fixes the derivation to `map⁺ φ permH`.

  perm-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (P : map vlJ (map φ sH) ≡ map vlH sH)
        (Q : map vlJ (J.ein (ψ e) ++ restJ) ≡ map vlH (H.ein e ++ restH))
    → castˢ P Q (RJ.permuteˢ permJ) ≈ˢ RH.permuteˢ permH
  perm-emb e sH restH permH eqH restJ permJ eqJ P Q =
    helper restJ permJ eqJ Q
      (just-injective-fst
        (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH))))
    where
      helper
        : (rJ : List (Fin J.nV))
          (pJ : map φ sH Perm.↭ J.ein (ψ e) ++ rJ)
          (eJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (rJ , pJ))
          (qq : map vlJ (J.ein (ψ e) ++ rJ) ≡ map vlH (H.ein e ++ restH))
        → rJ ≡ map φ restH
        → castˢ P qq (RJ.permuteˢ pJ) ≈ˢ RH.permuteˢ permH
      helper .(map φ restH) pJ eJ qq refl rewrite ψ-ein e =
        ≈̂⇒castˢ
          (≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (trans (cong RJ.permuteˢ pinned)
                                       (RJ.permuteˢ-subst mpp lift))))
          (≈̂-trans cast-≈̂ (PVV.pvv-≈̂ φ vlJ vlH φ-lab permH)))
          P qq
        where
          mpp = map-++ φ (H.ein e) restH
          lift = PermProp.map⁺ φ permH

          pinned : pJ ≡ subst (λ z → map φ sH Perm.↭ z) mpp lift
          pinned = extract-prefix-pin φ φ-inj (H.ein e) sH restH permH pJ eqH eJ

  edge-step-fire-embˢ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (restJ≡ : restJ ≡ map φ restH)
        (pDom : map vlJ (map φ sH) ≡ map vlH sH)
        (pCod : map vlJ (J.eout (ψ e) ++ restJ) ≡ map vlH (H.eout e ++ restH))
    → castˢ pDom pCod (RJ.fire-termˢ (ψ e) (map φ sH) restJ permJ)
      ≈ˢ RH.fire-termˢ e sH restH permH
  edge-step-fire-embˢ e sH restH permH eqH restJ permJ eqJ restJ≡ pDom pCod =
    viâ (≈̂-trans (cast-≈̂ {p = pDom} {q = pCod})
                 (cast-≈̂ {p = refl} {q = sym (map-++ vlJ (J.eout (ψ e)) restJ)}))
        (∘-resp-≈̂ box-part jperm-part)
        (cast-≈̂ {p = refl} {q = sym (map-++ vlH (H.eout e) restH)})
    where
      Jperm = castˢ refl (map-++ vlJ (J.ein (ψ e)) restJ) (RJ.permuteˢ permJ)
      Jbox  = genˢ (J.elab (ψ e)) ⊗ˢ idˢ {map vlJ restJ}
      Hbox  = genˢ (H.elab e) ⊗ˢ idˢ {map vlH restH}
      Hperm = castˢ refl (map-++ vlH (H.ein e) restH) (RH.permuteˢ permH)

      rest-lab : map vlJ restJ ≡ map vlH restH
      rest-lab = trans (cong (map vlJ) restJ≡) (vlab-φ restH)

      Mmid : map vlJ (J.ein (ψ e)) ++ map vlJ restJ ≡ map vlH (H.ein e) ++ map vlH restH
      Mmid = trans (sym (map-++ vlJ (J.ein (ψ e)) restJ))
             (trans (cong (map vlJ) (cong₂ _++_ (ψ-ein e) restJ≡))
             (trans (cong (map vlJ) (sym (map-++ φ (H.ein e) restH)))
             (trans (vlab-φ (H.ein e ++ restH))
                    (map-++ vlH (H.ein e) restH))))

      Qbox : map vlJ (J.eout (ψ e)) ++ map vlJ restJ
             ≡ map vlH (H.eout e) ++ map vlH restH
      Qbox = cong₂ _++_ (atom-eout e) rest-lab

      Qp : map vlJ (J.ein (ψ e) ++ restJ) ≡ map vlH (H.ein e ++ restH)
      Qp = trans (map-++ vlJ (J.ein (ψ e)) restJ)
           (trans Mmid (sym (map-++ vlH (H.ein e) restH)))

      box-part : Jbox ≈̂ Hbox
      box-part = castˢ⇒≈̂ Mmid Qbox (box-emb e restH restJ restJ≡ rest-lab Mmid Qbox)

      jperm-part : Jperm ≈̂ Hperm
      jperm-part =
        ≈̂-trans (cast-≈̂ {p = refl} {q = map-++ vlJ (J.ein (ψ e)) restJ})
        (≈̂-trans (castˢ⇒≈̂ pDom Qp (perm-emb e sH restH permH eqH restJ permJ eqJ pDom Qp))
                 (≈̂-sym (cast-≈̂ {p = refl} {q = map-++ vlH (H.ein e) restH})))

  edge-step-term-embˢ
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (pDom : map vlJ (map φ sH) ≡ map vlH sH)
        (pCod : map vlJ (proj₁ (RJ.edge-stepˢ (map φ sH) (ψ e)))
              ≡ map vlH (proj₁ (RH.edge-stepˢ sH e)))
    → castˢ pDom pCod (proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
      ≈ˢ proj₂ (RH.edge-stepˢ sH e)
  edge-step-term-embˢ e sH pDom pCod
    with extract-prefix (H.ein e) sH in eqH
       | extract-prefix (J.ein (ψ e)) (map φ sH) in eqJ
  ... | nothing | nothing = cast-id pDom pCod
  ... | nothing | just (restJ , permJ) =
        ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
  ... | just (restH , permH) | nothing =
        ⊥-elim (just≢nothing
          (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
  ... | just (restH , permH) | just (restJ , permJ) =
        edge-step-fire-embˢ e sH restH permH eqH restJ permJ eqJ restJ≡ pDom pCod
        where
          restJ≡ : restJ ≡ map φ restH
          restJ≡ = just-injective-fst
                     (trans (sym eqJ)
                            (proj₂ (extract-prefix-J-just e sH restH permH eqH)))

  process-edges-term-embˢ-gen
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
        (sJ : List (Fin J.nV)) (sJ≡ : sJ ≡ map φ sH)
        (pDom : map vlJ sJ ≡ map vlH sH)
        (pCod : map vlJ (proj₁ (RJ.process-edgesˢ (map ψ es) sJ))
              ≡ map vlH (proj₁ (RH.process-edgesˢ es sH)))
    → castˢ pDom pCod (proj₂ (RJ.process-edgesˢ (map ψ es) sJ))
      ≈ˢ proj₂ (RH.process-edgesˢ es sH)
  process-edges-term-embˢ-gen [] sH sJ sJ≡ pDom pCod = cast-id pDom pCod
  process-edges-term-embˢ-gen (e ∷ es) sH .(map φ sH) refl pDom pCod = goal
    where
      s'H  = proj₁ (RH.edge-stepˢ sH e)
      s'J  = proj₁ (RJ.edge-stepˢ (map φ sH) (ψ e))

      stepStk : s'J ≡ map φ s'H
      stepStk = edge-step-stack-embˢ e sH

      pMid : map vlJ s'J ≡ map vlH s'H
      pMid = trans (cong (map vlJ) stepStk) (vlab-φ s'H)

      headTwin
        : castˢ pDom pMid (proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
          ≈ˢ proj₂ (RH.edge-stepˢ sH e)
      headTwin = edge-step-term-embˢ e sH pDom pMid

      recTwin
        : castˢ pMid pCod (proj₂ (RJ.process-edgesˢ (map ψ es) s'J))
          ≈ˢ proj₂ (RH.process-edgesˢ es s'H)
      recTwin = process-edges-term-embˢ-gen es s'H s'J stepStk pMid pCod

      goal
        : castˢ pDom pCod
            (proj₂ (RJ.process-edgesˢ (map ψ es) s'J)
             ∘ˢ proj₂ (RJ.edge-stepˢ (map φ sH) (ψ e)))
          ≈ˢ proj₂ (RH.process-edgesˢ es s'H)
             ∘ˢ proj₂ (RH.edge-stepˢ sH e)
      goal = ∘-cast-resp pDom pMid pCod recTwin headTwin

  term-emb-≈̂
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
    → proj₂ (RJ.process-edgesˢ (map ψ es) (map φ sH))
      ≈̂ proj₂ (RH.process-edgesˢ es sH)
  term-emb-≈̂ es sH =
    castˢ⇒≈̂ (vlab-φ sH) pCod
      (process-edges-term-embˢ-gen es sH (map φ sH) refl (vlab-φ sH) pCod)
    where
      pCod : map vlJ (proj₁ (RJ.process-edgesˢ (map ψ es) (map φ sH)))
           ≡ map vlH (proj₁ (RH.process-edgesˢ es sH))
      pCod = trans (cong (map vlJ) (proc-stack-embˢ es sH))
                   (vlab-φ (proj₁ (RH.process-edgesˢ es sH)))

-- The edge-label proof cancels the two casts via `subst₂` groupoid laws.
module EmbedGlue
  {H J : Hypergraph FlatGen}
  (let module H = Hypergraph H)
  (let module J = Hypergraph J)
  (φ        : Fin H.nV → Fin J.nV)
  (φ-inj    : ∀ {x y} → φ x ≡ φ y → x ≡ y)
  (φ-lab    : ∀ i → J.vlab (φ i) ≡ H.vlab i)
  (ψ        : Fin H.nE → Fin J.nE)
  (ein-red  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
  (eout-red : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
  (mv       : ∀ (xs : List (Fin H.nV)) → map H.vlab xs ≡ map J.vlab (map φ xs))
  (elab-c   : ∀ e → subst₂ FlatGen (cong (map J.vlab) (ein-red e))
                                   (cong (map J.vlab) (eout-red e)) (J.elab (ψ e))
                  ≡ subst₂ FlatGen (mv (H.ein e)) (mv (H.eout e)) (H.elab e))
  where
  atom-ein : ∀ e → map J.vlab (J.ein (ψ e)) ≡ map H.vlab (H.ein e)
  atom-ein e = trans (cong (map J.vlab) (ein-red e)) (sym (mv (H.ein e)))

  atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e)
  atom-eout e = trans (cong (map J.vlab) (eout-red e)) (sym (mv (H.eout e)))

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e)) ≡ H.elab e
  ψ-elab e =
    trans (sym (subst₂-trans (cong (map J.vlab) (ein-red e)) (sym (mv (H.ein e)))
                             (cong (map J.vlab) (eout-red e)) (sym (mv (H.eout e)))
                             (J.elab (ψ e))))
      (trans (cong (subst₂ FlatGen (sym (mv (H.ein e))) (sym (mv (H.eout e)))) (elab-c e))
             (subst₂-sym-flip (mv (H.ein e)) (mv (H.eout e)) refl))

  open TermEmbedˢ {H} {J} φ φ-inj φ-lab ψ ein-red eout-red
                  atom-ein atom-eout ψ-elab public

--------------------------------------------------------------------------------
-- Permutation composition and inverses
--------------------------------------------------------------------------------

module Equivariantˢ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  private
    variable
      xs ys zs : List (Fin H.nV)

  pvv-transˢ
    : (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → permuteˢ (Perm.trans p q) ≈ˢ permuteˢ q ∘ˢ permuteˢ p
  pvv-transˢ p q = ≈-refl

  pvv-inverse-leftˢ : (ρ : xs Perm.↭ ys) → permuteˢ (Perm.↭-sym ρ) ∘ˢ permuteˢ ρ ≈ˢ idˢ
  pvv-inverse-leftˢ = permuteˢ-inv-left

  pvv-inverse-rightˢ : (ρ : xs Perm.↭ ys) → permuteˢ ρ ∘ˢ permuteˢ (Perm.↭-sym ρ) ≈ˢ idˢ
  pvv-inverse-rightˢ = permuteˢ-inv-right

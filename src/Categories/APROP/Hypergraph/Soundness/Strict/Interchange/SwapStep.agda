{-# OPTIONS --safe --without-K #-}

-- Decoder equality for orders differing by one adjacent incomparable swap.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Model.Dependency using (Dep)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.SwapValidity sig as SV
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig using (Linear⇒cod-Unique)
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig
  using (RunInterchangeˢ)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig
  using (module EquivStep; module RunBlocks)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig as SC

open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             where
  private module H = Hypergraph H

  open EquivStep H using (vl; permuteˢ; pe-stackˢ; pe-termˢ; pe-stack-++ˢ)

  module PH = IW.PerHG H
  open PH public using (Order; _↝_; _↝*_; NoInv; swap-step)

  connectivity : ∀ {L M : Order} → L Perm.↭ M → NoInv L → NoInv M → L ↝* M
  connectivity = PH.connectivity dih

  Incompˢ = SC.Incomp H

  RunInterchangeAt : Set
  RunInterchangeAt =
    ∀ (ps qs : Order) {e e' : Fin H.nE} (inc : Incompˢ e e')
    → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ qs) H.dom
    → RunInterchangeˢ H ps qs inc

  Validˢ : Order → Set
  Validˢ o = pe-stackˢ o H.dom Perm.↭ H.cod

  decodeOrdˢ : (o : Order) → Validˢ o → HomS (map vl H.dom) (map vl H.cod)
  decodeOrdˢ o p = permuteˢ p ∘ˢ pe-termˢ o H.dom

  swap-validityˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Validˢ o₁ → Validˢ o₂
  swap-validityˢ = SV.PerHG.swap-validity H lin

  open RunBlocks H using (coeCod; pe-term-++ˢ) public

  decodeOrdˢ-factor
    : ∀ (ps rest : Order) (p : Validˢ (ps ++ rest))
    → decodeOrdˢ (ps ++ rest) p
      ≈ˢ ( permuteˢ p
            ∘ˢ coeCod (sym (pe-stack-++ˢ ps rest H.dom))
                       (pe-termˢ rest (pe-stackˢ ps H.dom)) )
          ∘ˢ pe-termˢ ps H.dom
  decodeOrdˢ-factor ps rest p =
    ≈-trans
      (∘-resp ≈-refl (pe-term-++ˢ ps rest H.dom))
      (≈-trans
        (∘-resp ≈-refl
          (coeCod-∘ (sym (pe-stack-++ˢ ps rest H.dom))
                     (pe-termˢ rest (pe-stackˢ ps H.dom))
                     (pe-termˢ ps H.dom)))
        (≈-sym assocˢ))
    where
      coeCod-∘
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomS (map vl (pe-stackˢ ps H.dom)) (map vl a))
            (f : HomS (map vl H.dom) (map vl (pe-stackˢ ps H.dom)))
        → coeCod eq (g ∘ˢ f) ≈ˢ coeCod eq g ∘ˢ f
      coeCod-∘ refl g f = ≈-refl

module FrontSwap (H : Hypergraph FlatGen)
                 (dih : ∀ {e} → ¬ (Dep H e e))
                 (lin : Linear H)
                 where
  private module H = Hypergraph H
  open PerHG H dih lin
  open EquivStep H using (vl; permuteˢ; pe-stackˢ; pe-termˢ; pe-stack-++ˢ)

  final-permute-cohˢ
    : ∀ {a-stk b-stk : List (Fin H.nV)}
        (r  : a-stk Perm.↭ b-stk)
        (va : a-stk Perm.↭ H.cod)
        (vb : b-stk Perm.↭ H.cod)
    → permuteˢ va ≈ˢ permuteˢ vb ∘ˢ permuteˢ r
  final-permute-cohˢ r va vb =
    StrictDecoder.rigidˢ H (Linear⇒cod-Unique H lin) va (Perm.trans r vb)

  front-swap-≈ˢ
    : ∀ (ps qs : Order) {e e' : Fin H.nE}
        (inc : Incompˢ e e')
        (RI : RunInterchangeˢ H ps qs inc)
        (p₁ : Validˢ (ps ++ e ∷ e' ∷ qs))
        (p₂ : Validˢ (ps ++ e' ∷ e ∷ qs))
    → ( permuteˢ p₁
          ∘ˢ coeCod (sym (pe-stack-++ˢ ps (e ∷ e' ∷ qs) H.dom))
                     (pe-termˢ (e ∷ e' ∷ qs) (pe-stackˢ ps H.dom)) )
      ≈ˢ
      ( permuteˢ p₂
          ∘ˢ coeCod (sym (pe-stack-++ˢ ps (e' ∷ e ∷ qs) H.dom))
                     (pe-termˢ (e' ∷ e ∷ qs) (pe-stackˢ ps H.dom)) )
  front-swap-≈ˢ ps qs {e} {e'} inc RI p₁ p₂ =
    ≈-trans (coe-vanish (pe-stack-++ˢ ps (e ∷ e' ∷ qs) H.dom) p₁ run₁)
      (≈-trans assembled
        (≈-sym (coe-vanish (pe-stack-++ˢ ps (e' ∷ e ∷ qs) H.dom) p₂ run₂)))
    where
      open RunInterchangeˢ RI

      sp  = pe-stackˢ ps H.dom
      run₁ = pe-termˢ (e ∷ e' ∷ qs) sp
      run₂ = pe-termˢ (e' ∷ e ∷ qs) sp

      p₁' : pe-stackˢ (e ∷ e' ∷ qs) sp Perm.↭ H.cod
      p₁' = subst (Perm._↭ H.cod) (pe-stack-++ˢ ps (e ∷ e' ∷ qs) H.dom) p₁
      p₂' : pe-stackˢ (e' ∷ e ∷ qs) sp Perm.↭ H.cod
      p₂' = subst (Perm._↭ H.cod) (pe-stack-++ˢ ps (e' ∷ e ∷ qs) H.dom) p₂

      coe-vanish
        : ∀ {FS B : List (Fin H.nV)} (eq : FS ≡ B)
            (pv : FS Perm.↭ H.cod)
            (run : HomS (map vl sp) (map vl B))
        → permuteˢ pv ∘ˢ coeCod (sym eq) run
          ≈ˢ permuteˢ (subst (Perm._↭ H.cod) eq pv) ∘ˢ run
      coe-vanish refl pv run = ≈-refl

      assembled : permuteˢ p₁' ∘ˢ run₁ ≈ˢ permuteˢ p₂' ∘ˢ run₂
      assembled =
        ≈-trans
          (∘-resp (final-permute-cohˢ reshuffle p₁' p₂') ≈-refl)
          (≈-trans assocˢ
            (∘-resp ≈-refl (≈-sym run-eq)))

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  open PerHG H dih lin
  module FS = FrontSwap H dih lin
  open FS using (front-swap-≈ˢ)

  module _ (run-interchange : RunInterchangeAt) where

    swap-≈ˢ
      : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
      → o₁ Perm.↭ allFin (Hypergraph.nE H)
      → (p₁ : Validˢ o₁) (p₂ : Validˢ o₂)
      → decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
    swap-≈ˢ (swap-step ps {e} {e'} qs inc) o₁↭range p₁ p₂ =
      ≈-trans
        (decodeOrdˢ-factor ps (e ∷ e' ∷ qs) p₁)
        (≈-trans
          (∘-resp (front-swap-≈ˢ ps qs inc
                     (run-interchange ps qs inc res₂) p₁ p₂)
                  ≈-refl)
          (≈-sym (decodeOrdˢ-factor ps (e' ∷ e ∷ qs) p₂)))
      where
        o₂↭range : (ps ++ e' ∷ e ∷ qs) Perm.↭ allFin (Hypergraph.nE H)
        o₂↭range = Perm.↭-trans (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl)) o₁↭range

        res₂ : SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ qs) (Hypergraph.dom H)
        res₂ = SUR.dom-reservoir-prov H (proj₂ lin) (ps ++ e' ∷ e ∷ qs) o₂↭range

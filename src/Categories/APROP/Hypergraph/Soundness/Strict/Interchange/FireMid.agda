{-# OPTIONS --safe --without-K #-}

-- Both-fire interchange through shared located normal forms.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.FireMid
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.Combinatorics.FinCount
  using (++-cancelˡ)
import Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb sig
  as FMIC
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig
  as SU
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig as DSh
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig as PC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig

import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCoreRun sig as SCR
open import Categories.Morphism.Reasoning SCat

open import Data.Fin using (Fin)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

module FMS (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  open Restrict (Fin H.nV) vl

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
    ≈-trans (∘-resp ≈-refl (∘-resp (box-crossᵛ g g' Rl) ≈-refl))
    (≈-trans (∘-resp ≈-refl assocˢ)
    (≈-trans (∘-resp ≈-refl assocˢ)
    (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (∘-resp ≈-refl (≈-sym vinc))))
    (≈-trans (≈-sym assocˢ)
    (≈-trans (∘-resp (≈-sym voutc) ≈-refl)
      assocˢ)))))

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

  Incompˢ = Incomp H
  open PC.Kit H using (⟦bswap⟧ᵛ)
  open DSh.Scr (Fin H.nV) H.vlab using (bswap)

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

    vin-cohᵛ : Lin₁ ≈ᵛ (σᵛ (H.ein e') (H.ein e) ⊗ᵛ idᵛ {Rlist}) ∘ᵛ Lin₂
    vin-cohᵛ =
      ≈-trans (rigidˢ (SU.Unique-resp-↭ loc₁ us-sp) loc₁
                 (Perm.trans loc₂ swp-in))
              (∘-resp (⟦bswap⟧ᵛ (H.ein e') (H.ein e) Rlist) ≈-refl)

    vout-cohᵛ
      : Pr ∘ᵛ Lout₁
        ≈ᵛ Lout₂ ∘ᵛ (σᵛ (H.eout e) (H.eout e') ⊗ᵛ idᵛ {Rlist})
    vout-cohᵛ =
      ≈-trans (rigidˢ us-cod (Perm.trans vout-loc₁ r-stk)
                 (Perm.trans swp-out vout-loc₂))
              (∘-resp ≈-refl (⟦bswap⟧ᵛ (H.eout e) (H.eout e') Rlist))

module _ (H : Hypergraph FlatGen)
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  open PC.Kit H
    using (⟦absorbˡ⟧; ⟦absorbʳ⟧; ⟦bswap⟧ᵛ; rigid-≈̂)

  open Restrict (Fin H.nV) vl

  cross-NFᵛ′   = FMS.cross-NFᵛ H
  box-resid3ᵛ′ = FMS.box-resid3ᵛ H

  open DSh.Scr (Fin H.nV) H.vlab using (bswap)

  FireMidInterchangeˢ : Set
  FireMidInterchangeˢ = SCR.FireMidInterchangeˢ H lin

  private
    box-merge-σᵛ
      : ∀ {A B A' B' : List (Fin H.nV)} (g : HomV A B) (g' : HomV A' B')
      → (g' ⊗ᵛ idᵛ {B}) ∘ᵛ (σᵛ B A' ∘ᵛ (g ⊗ᵛ idᵛ {A'}))
        ≈ᵛ σᵛ B B' ∘ᵛ (g ⊗ᵛ g')
    box-merge-σᵛ g g' =
      ≈-trans (≈-sym assocˢ)
      (≈-trans (∘-resp (≈-sym σ-natᵛ) ≈-refl)
      (pullʳ (≈-trans interchangeᵛ (⊗-respᵛ idˡ idʳ))))

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

    -- Residuals use `A ++ (A' ++ Rl)`, while block frames use
    -- `(A ++ A') ++ Rl`; the associator casts reconcile these bracketings.
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
      ≈-trans (∘-resp (≈-sym (box-suffix-ᵛ g' B Rl)) ≈-refl)
      (≈-trans (∘-resp ≈-refl
                  (∘-resp ≈-refl (≈-sym (box-suffix-ᵛ g A' Rl))))
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
  -- Shared-residual normal form
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

    A  = H.ein a  ; A' = H.ein b
    B  = H.eout a ; B' = H.eout b
    g  : HomV A B
    g  = genˢ (H.elab a)
    g' : HomV A' B'
    g' = genˢ (H.elab b)

    loc1' : sp Perm.↭ A ++ (A' ++ R)
    loc1' = Perm.trans q-first (PermProp.++⁺ˡ A ρ₁)
    loc2' : B ++ s₁ Perm.↭ A' ++ (B ++ R)
    loc2' = Perm.trans q-second (PermProp.++⁺ˡ A' ρ₂)

    Lin : HomV sp ((A ++ A') ++ R)
    Lin = permuteᵛ loc
    Lout : HomV ((B ++ B') ++ R) (B' ++ s₂)
    Lout = permuteᵛ vout-loc

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

    private
      mid-comp : B ++ (A' ++ R) Perm.↭ A' ++ (B ++ R)
      mid-comp = Perm.trans (PermProp.++⁺ˡ B (Perm.↭-sym ρ₁)) loc2'

      us-mid-img : Unique (A' ++ (B ++ R))
      us-mid-img = SU.Unique-resp-↭ (PermProp.++⁺ˡ A' ρ₂) us-mid

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

    private
      central-eq
        : Boxb ∘ᵛ ( (IN2 ∘ᵛ OUT1) ∘ᵛ Boxa )
          ≈ᵛ castᵛ (++-assoc A A' R) (++-assoc B' B R) (σ-out ∘ᵛ box-block)
      central-eq =
        ≈-trans (∘-resp ≈-refl (∘-resp MID-eq ≈-refl)) (box-merge-Rᵛ g g' R)

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

    nf-genᵛ
      : fire-termˢ b (B ++ s₁) s₂ q-second ∘ˢ fire-termˢ a sp s₁ q-first
        ≈ᵛ Lout ∘ᵛ ( box-block ∘ᵛ Lin )
    nf-genᵛ =
      ≈-trans phase
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (≈-sym assocˢ)))
      (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
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

  fire-mid-interchangeˢ : FireMidInterchangeˢ
  fire-mid-interchangeˢ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
                        us-sp us-mid₁ us-mid₂ us-cod =
    r-stk , ≈-trans nf₂-eqᵛ (≈-trans cross (∘-resp ≈-refl (≈-sym nf₁-eqᵛ)))
    where
      open FMS.Located H inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-cod

      -- Only the final `Unique` witness is asymmetric: the first order
      -- transports it back through `r-stk`.
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
                 (Perm.trans (PermProp.++⁺ˡ (H.eout x) ρ₁)
                             (PermProp.shifts (H.eout x) (H.ein y))))

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

      cross
        : ( Lout₂ ∘ᵛ ( ((genˢ (H.elab e') ⊗ᵛ genˢ (H.elab e)) ⊗ᵛ idᵛ {Rlist})
                         ∘ᵛ Lin₂ ) )
          ≈ᵛ Pr ∘ᵛ ( Lout₁ ∘ᵛ ( ((genˢ (H.elab e) ⊗ᵛ genˢ (H.elab e')) ⊗ᵛ idᵛ {Rlist})
                                  ∘ᵛ Lin₁ ) )
      cross = cross-NFᵛ′ (genˢ (H.elab e)) (genˢ (H.elab e'))
                Lin₁ Lin₂ Lout₁ Lout₂ Pr vin-cohᵛ vout-cohᵛ

  module RunInterchangeˢ =
    SCR.RunInterchange H lin fire-mid-interchangeˢ

  open RunInterchangeˢ using (run-interchange₀ˢ) public

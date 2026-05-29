{-# OPTIONS --safe --with-K #-}

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEvalCoherence
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Discharge.StackPerm sig-dec
  using (process-edges-resp-iso-stack; stack-↭-flatten-B
        ; eval-stack-↭-flatten-B-rigid)

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Soundness
open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map
  using ( ≈-fb-of-≡; ∘-fb-cong; ∘-fb-assoc; inv-fb-cong
        ; ∘-fb-cancel-left; eval-subst-cod; eval-↭-reflexive
        ; cast-id-∘; inv-fb-cast-id; subst-cod-comp; subst-cod-irr)

open import Data.List using (List; map; length)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

private
  full-cod-eq : ∀ {A B} (f g : HomTerm A B)
              → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
  full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

stack-eval-coherence
  : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                Perm.↭ Hypergraph.cod ⟪ f ⟫F)
      (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
                Perm.↭ Hypergraph.cod ⟪ g ⟫F)
  → eval-↭ (Perm.trans (process-edges-resp-iso-stack f g iso)
                        (PermProp.map⁺ (Hypergraph.vlab ⟪ g ⟫F) perm-g))
    ≈-fb eval-↭ (subst (λ z →
                   map (Hypergraph.vlab ⟪ f ⟫F)
                       (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
                   Perm.↭ z)
                 (sym (full-cod-eq f g))
                 (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) perm-f))
stack-eval-coherence {A} {B} f g iso perm-f perm-g =
  ≈-fb-trans
    {π = eval-↭ (Perm.trans (process-edges-resp-iso-stack f g iso) MG)}
    {ρ = inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)}
    {σ = eval-↭ (subst (λ z → map vf sf Perm.↭ z) (sym (full-cod-eq f g)) MF)}
    lhs-reduced (≈-fb-of-≡ (sym rhs-reduced))
  where
    vf = Hypergraph.vlab ⟪ f ⟫F
    vg = Hypergraph.vlab ⟪ g ⟫F
    cf = Hypergraph.cod ⟪ f ⟫F
    cg = Hypergraph.cod ⟪ g ⟫F
    sf = proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
    sg = proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))

    Bf = stack-↭-flatten-B f
    Bg = stack-↭-flatten-B g
    MF = PermProp.map⁺ vf perm-f
    MG = PermProp.map⁺ vg perm-g
    RCf = Perm.↭-reflexive (⟪⟫F-codL f)
    RCg = Perm.↭-reflexive (⟪⟫F-codL g)

    -- Evaluated building blocks.
    eMF = eval-↭ MF
    eMG = eval-↭ MG
    eRCf = eval-↭ RCf
    eRCg = eval-↭ RCg

    -- The rigidity-exposed forms of the two side bridges.
    rf : eval-↭ Bf ≈-fb eval-↭ (Perm.trans MF RCf)
    rf = eval-stack-↭-flatten-B-rigid f perm-f

    rg : eval-↭ Bg ≈-fb eval-↭ (Perm.trans MG RCg)
    rg = eval-stack-↭-flatten-B-rigid g perm-g

    -- Note: eval (trans MF RCf) = eRCf ∘-fb eMF (definitional), etc.

    -- Step 1: expand LHS.  process-edges-resp-iso-stack = trans Bf (↭-sym Bg);
    -- the outer map⁺ perm-g is MG.  So
    --   LHS = eval (trans (trans Bf (↭-sym Bg)) MG)
    --       = eMG ∘-fb (eval (↭-sym Bg) ∘-fb eval Bf)         (definitional)
    --       ≈ eMG ∘-fb (inv-fb (eval Bg) ∘-fb eval Bf).
    lhs-step1
      : eval-↭ (Perm.trans (process-edges-resp-iso-stack f g iso) MG)
        ≈-fb eMG ∘-fb (inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf)
    lhs-step1 =
      ∘-fb-cong {g = eMG} {g′ = eMG}
                {f = eval-↭ (Perm.↭-sym Bg) ∘-fb eval-↭ Bf}
                {f′ = inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf}
                (≈-fb-of-≡ {π = eMG} refl)
                (∘-fb-cong {g = eval-↭ (Perm.↭-sym Bg)} {g′ = inv-fb (eval-↭ Bg)}
                           {f = eval-↭ Bf} {f′ = eval-↭ Bf}
                           (eval-↭-sym Bg) (≈-fb-of-≡ {π = eval-↭ Bf} refl))

    -- Step 2: substitute the rigid forms of eval Bf, eval Bg.
    lhs-step2
      : eMG ∘-fb (inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf)
        ≈-fb eMG ∘-fb (inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF))
    lhs-step2 =
      ∘-fb-cong {g = eMG} {g′ = eMG}
                {f = inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf}
                {f′ = inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF)}
                (≈-fb-of-≡ {π = eMG} refl)
                (∘-fb-cong {g = inv-fb (eval-↭ Bg)} {g′ = inv-fb (eRCg ∘-fb eMG)}
                           {f = eval-↭ Bf} {f′ = eRCf ∘-fb eMF}
                           (inv-fb-cong {f = eval-↭ Bg} {g = eRCg ∘-fb eMG} rg) rf)

    -- Step 3: distribute inv-fb over composition and re-associate, then
    -- cancel  eMG ∘-fb inv-fb eMG  to the identity.
    --   inv-fb (eRCg ∘-fb eMG) = inv-fb eMG ∘-fb inv-fb eRCg   (inv-fb-comp)
    lhs-step3
      : eMG ∘-fb (inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF))
        ≈-fb inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)
    lhs-step3 =
      ≈-fb-trans
        {π = eMG ∘-fb (inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF))}
        {ρ = eMG ∘-fb ((inv-fb eMG ∘-fb inv-fb eRCg) ∘-fb (eRCf ∘-fb eMF))}
        {σ = inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)}
        (∘-fb-cong {g = eMG} {g′ = eMG}
                   {f = inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF)}
                   {f′ = (inv-fb eMG ∘-fb inv-fb eRCg) ∘-fb (eRCf ∘-fb eMF)}
                   (≈-fb-of-≡ {π = eMG} refl)
                   (∘-fb-cong {g = inv-fb (eRCg ∘-fb eMG)}
                              {g′ = inv-fb eMG ∘-fb inv-fb eRCg}
                              {f = eRCf ∘-fb eMF} {f′ = eRCf ∘-fb eMF}
                              (inv-fb-comp eRCg eMG) (≈-fb-of-≡ {π = eRCf ∘-fb eMF} refl)))
      (≈-fb-trans
        {π = eMG ∘-fb ((inv-fb eMG ∘-fb inv-fb eRCg) ∘-fb (eRCf ∘-fb eMF))}
        {ρ = eMG ∘-fb (inv-fb eMG ∘-fb (inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)))}
        {σ = inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)}
        (∘-fb-cong {g = eMG} {g′ = eMG}
                   {f = (inv-fb eMG ∘-fb inv-fb eRCg) ∘-fb (eRCf ∘-fb eMF)}
                   {f′ = inv-fb eMG ∘-fb (inv-fb eRCg ∘-fb (eRCf ∘-fb eMF))}
                   (≈-fb-of-≡ {π = eMG} refl)
                   (∘-fb-assoc (inv-fb eMG) (inv-fb eRCg) (eRCf ∘-fb eMF)))
        (∘-fb-cancel-left eMG (inv-fb eRCg ∘-fb (eRCf ∘-fb eMF))))

    lhs-reduced
      : eval-↭ (Perm.trans (process-edges-resp-iso-stack f g iso) MG)
        ≈-fb inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)
    lhs-reduced =
      ≈-fb-trans
        {π = eval-↭ (Perm.trans (process-edges-resp-iso-stack f g iso) MG)}
        {ρ = eMG ∘-fb (inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf)}
        {σ = inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)}
        lhs-step1
        (≈-fb-trans
          {π = eMG ∘-fb (inv-fb (eval-↭ Bg) ∘-fb eval-↭ Bf)}
          {ρ = eMG ∘-fb (inv-fb (eRCg ∘-fb eMG) ∘-fb (eRCf ∘-fb eMF))}
          {σ = inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)}
          lhs-step2 lhs-step3)

    -- ------------------------------------------------------------------
    -- RHS reduction to the same bijection.
    --
    -- eMF : FinBij (length (map vf sf)) (length (map vf cf)).
    ef = cong length (⟪⟫F-codL f)   -- length (map vf cf) ≡ length (flatten B)
    eg = cong length (⟪⟫F-codL g)   -- length (map vg cg) ≡ length (flatten B)

    -- eRCf ∘-fb eMF transports the codomain of eMF along ef.
    rhs-RCf : eRCf ∘-fb eMF
            ≡ subst (λ k → FinBij (length (map vf sf)) k) ef eMF
    rhs-RCf =
      trans (cong (_∘-fb eMF) (eval-↭-reflexive (⟪⟫F-codL f)))
            (cast-id-∘ ef eMF)

    -- inv-fb eRCg = reversed cast-id.
    rhs-invRCg : inv-fb eRCg
               ≡ subst (λ k → FinBij (length (flatten B)) k) (sym eg) id-fb
    rhs-invRCg =
      trans (cong inv-fb (eval-↭-reflexive (⟪⟫F-codL g)))
            (inv-fb-cast-id eg)

    -- Compose:  inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)
    --   = subst (sym eg) id-fb ∘-fb subst ef eMF
    --   = subst (sym eg) (subst ef eMF)
    --   = subst (trans ef (sym eg)) eMF.
    rhs-reduced
      : eval-↭ (subst (λ z → map vf sf Perm.↭ z) (sym (full-cod-eq f g)) MF)
        ≡ inv-fb eRCg ∘-fb (eRCf ∘-fb eMF)
    rhs-reduced =
      trans (eval-subst-cod (sym (full-cod-eq f g)) MF)
      (trans (subst-cod-irr (cong length (sym (full-cod-eq f g)))
                            (trans ef (sym eg)) eMF cod-eq-proof)
      (trans (sym (subst-cod-comp ef (sym eg) eMF))
      (trans (cong (λ z → subst (λ k → FinBij (length (map vf sf)) k) (sym eg) z)
                   (sym rhs-RCf))
             (sym (trans (cong (_∘-fb (eRCf ∘-fb eMF)) rhs-invRCg)
                         (cast-id-∘ (sym eg) (eRCf ∘-fb eMF)))))))
      where
        -- cong length (sym (full-cod-eq f g)) ≡ trans ef (sym eg).
        -- full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f)).
        -- Proved by J on the two boundary equations.
        cod-eq-gen
          : ∀ {x y z : List X} (e₁ : y ≡ z) (e₂ : x ≡ z)
          → cong length (sym (trans e₁ (sym e₂)))
            ≡ trans (cong length e₂) (sym (cong length e₁))
        cod-eq-gen refl refl = refl
        cod-eq-proof
          : cong length (sym (full-cod-eq f g)) ≡ trans ef (sym eg)
        cod-eq-proof = cod-eq-gen (⟪⟫F-codL g) (⟪⟫F-codL f)

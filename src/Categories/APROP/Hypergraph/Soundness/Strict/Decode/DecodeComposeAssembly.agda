{-# OPTIONS --safe --without-K #-}

-- Composition shape of the strict decoder.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeComposeAssembly
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; map-via)
open FreeMonoidalHelper Symm X using (flatten)
import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as LP
import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig as Lin
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig
  using (Linear⇒cod-Unique)
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig as PC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig public
open import Categories.APROP.Hypergraph.Util.Prune using (count-non)
open import Categories.Tactic.Category
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueProp
open import Data.Nat using (ℕ)

open Inv using (inject+-inj)

module ComposeShape {A B C₀ : ObjTerm} (g : HomTerm B C₀) (f : HomTerm A B) where

  G K : Hypergraph FlatGen
  G = ⟪ f ⟫
  K = ⟪ g ⟫
  module G = Hypergraph G
  module K = Hypergraph K

  bdy : codL G ≡ domL K
  bdy = trans (⟪⟫-codL f) (sym (⟪⟫-domL g))

  Chg : Hypergraph FlatGen
  Chg = hComposeP G K bdy
  module C = Hypergraph Chg

  lin-G : Lin.Linear G
  lin-G = LP.⟪⟫-LinearP f
  lin-K : Lin.Linear K
  lin-K = LP.⟪⟫-LinearP g
  lin-C : Lin.Linear Chg
  lin-C = LP.⟪⟫-LinearP (g ∘ f)

  open hComposeP-impl G K bdy
    using ( injL; remapP; map-via-remapP; vlab-injL; remapP-vlab
          ; ein-c-inj₁-red; eout-c-inj₁-red; elab-c-inj₁
          ; ein-c-inj₂-red; eout-c-inj₂-red; elab-c-inj₂ )

  cn : ℕ
  cn = count-non K.dom

  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = LP.remapP-injective G K bdy lin-G lin-K

  module RG = Run G
  module RK = Run K
  module RC = Run Chg
  module EC = EquivStep Chg

  gblk kblk : List (Fin C.nE)
  gblk = map (_↑ˡ K.nE) (allFin G.nE)
  kblk = map (G.nE ↑ʳ_)  (allFin K.nE)

  allFin-eq : allFin C.nE ≡ gblk ++ kblk
  allFin-eq = allFin-++ G.nE K.nE

  module TG = EmbedGlue {H = G} {J = Chg}
                injL (inject+-inj cn) vlab-injL
                (_↑ˡ K.nE) ein-c-inj₁-red eout-c-inj₁-red
                (map-via vlab-injL) elab-c-inj₁

  module TK = EmbedGlue {H = K} {J = Chg}
                remapP remapP-injective remapP-vlab
                (G.nE ↑ʳ_) ein-c-inj₂-red eout-c-inj₂-red
                map-via-remapP elab-c-inj₂

  after-G : List (Fin C.nV)
  after-G = proj₁ (RC.process-edgesˢ gblk C.dom)

  s_G_final : List (Fin G.nV)
  s_G_final = proj₁ (RG.process-edgesˢ (allFin G.nE) G.dom)

  after-G-≡ : after-G ≡ map injL s_G_final
  after-G-≡ =
    LP.PureL.process-edges-lift G K bdy lin-G lin-K (allFin G.nE) G.dom

  perm-f : RG.s-finˢ Perm.↭ G.cod
  perm-f = finalPermˢ f

  map-rKd : map remapP K.dom ≡ map injL G.cod
  map-rKd = LP.map-remapP-K-dom G K bdy lin-G lin-K

  after-G-↭ : after-G Perm.↭ map remapP K.dom
  after-G-↭ =
    Perm.↭-trans (Perm.↭-reflexive after-G-≡)
      (Perm.↭-trans (PermProp.map⁺ injL perm-f)
        (Perm.↭-reflexive (sym map-rKd)))

  reservoir-K : SUR.Reservoir≤1 Chg kblk after-G
  reservoir-K =
    SUR.reservoir-split Chg gblk kblk C.dom
      (SUR.dom-reservoir-prov Chg (proj₂ lin-C) (gblk ++ kblk)
        (Perm.↭-reflexive (sym (allFin-++ G.nE K.nE))))

  equiv-K = EC.process-edges-equivariantˢ kblk after-G-↭ reservoir-K
  ρf-K = proj₁ equiv-K
  equiv-K-eq = proj₂ equiv-K

  uCcod : Unique C.cod
  uCcod = Linear⇒cod-Unique Chg lin-C
  uRemapKdom : Unique (map remapP K.dom)
  uRemapKdom =
    subst Unique (sym map-rKd)
      (UniqueProp.map⁺ (λ {x} {y} → inject+-inj cn {x} {y})
                       (Linear⇒cod-Unique G lin-G))

  open PC.Kit Chg using (⟦relabel-rigid⟧)

  module RB = RunBlocks Chg

  vlC : Fin C.nV → X
  vlC = C.vlab

  Pcomposite : HomS (map vlC C.dom) (map vlC RC.s-finˢ)
  Pcomposite = proj₂ (RC.process-edgesˢ (allFin C.nE) C.dom)

  gterm : HomS (map vlC C.dom) (map vlC after-G)
  gterm = proj₂ (RC.process-edgesˢ gblk C.dom)

  kterm-aG : HomS (map vlC after-G) (map vlC (proj₁ (RC.process-edgesˢ kblk after-G)))
  kterm-aG = proj₂ (RC.process-edgesˢ kblk after-G)

  kterm-canon : HomS (map vlC (map remapP K.dom))
                     (map vlC (proj₁ (RC.process-edgesˢ kblk (map remapP K.dom))))
  kterm-canon = proj₂ (RC.process-edgesˢ kblk (map remapP K.dom))

  PCˢ : HomS (map vlC RC.s-finˢ) (map vlC C.cod)
  PCˢ = RC.permuteˢ (finalPermˢ (g ∘ f))

  E₀ : proj₁ (RC.process-edgesˢ kblk after-G) ≡ RC.s-finˢ
  E₀ = sym (trans (cong (λ z → proj₁ (RC.process-edgesˢ z C.dom)) allFin-eq)
                  (RB.pe-stack-++ˢ gblk kblk C.dom))

  run-split : Pcomposite ≈ˢ RB.coeCod E₀ (kterm-aG ∘ˢ gterm)
  run-split = RB.run-split-atˢ gblk kblk allFin-eq C.dom

  perm-C2ˢ : proj₁ (RC.process-edgesˢ kblk after-G) Perm.↭ C.cod
  perm-C2ˢ = subst (Perm._↭ C.cod) (sym E₀) (finalPermˢ (g ∘ f))

  permAG : HomS (map vlC after-G) (map vlC (map remapP K.dom))
  permAG = RC.permuteˢ after-G-↭

  Ycˢ : HomS (map vlC C.dom) (map vlC (map remapP K.dom))
  Ycˢ = permAG ∘ˢ gterm

  Xcˢ : HomS (map vlC (map remapP K.dom)) (map vlC C.cod)
  Xcˢ = RC.permuteˢ perm-C2ˢ ∘ˢ (RC.permuteˢ (Perm.↭-sym ρf-K) ∘ˢ kterm-canon)

  private
    reassocˢ
      : ∀ {o1 o2 o2' o3 o4 o5 : List X}
          (Aᵗ : HomS o4 o5) (Bᵗ : HomS o3 o4) (Ktᵗ : HomS o2' o3)
          (Ctᵗ : HomS o2 o2') (Gtᵗ : HomS o1 o2)
      → Aᵗ ∘ˢ ((Bᵗ ∘ˢ (Ktᵗ ∘ˢ Ctᵗ)) ∘ˢ Gtᵗ)
        ≈ˢ (Aᵗ ∘ˢ (Bᵗ ∘ˢ Ktᵗ)) ∘ˢ (Ctᵗ ∘ˢ Gtᵗ)
    reassocˢ Aᵗ Bᵗ Ktᵗ Ctᵗ Gtᵗ = solve SCat

  Pcomp-eqˢ : PCˢ ∘ˢ Pcomposite ≈ˢ Xcˢ ∘ˢ Ycˢ
  Pcomp-eqˢ =
    ≈-trans (∘-resp ≈-refl run-split)
    (≈-trans (RB.absorbˢ E₀ (finalPermˢ (g ∘ f)) (kterm-aG ∘ˢ gterm))
    (≈-trans (∘-resp ≈-refl (∘-resp equiv-K-eq ≈-refl))
      (reassocˢ (RC.permuteˢ perm-C2ˢ)
                (RC.permuteˢ (Perm.↭-sym ρf-K))
                kterm-canon permAG gterm)))

  pterm-f : HomS (map G.vlab G.dom) (map G.vlab s_G_final)
  pterm-f = proj₂ (RG.process-edgesˢ (allFin G.nE) G.dom)

  s_K_final : List (Fin K.nV)
  s_K_final = proj₁ (RK.process-edgesˢ (allFin K.nE) K.dom)

  pterm-g : HomS (map K.vlab K.dom) (map K.vlab s_K_final)
  pterm-g = proj₂ (RK.process-edgesˢ (allFin K.nE) K.dom)

  perm-g : RK.s-finˢ Perm.↭ K.cod
  perm-g = finalPermˢ g

  PFˢ : HomS (map G.vlab s_G_final) (map G.vlab G.cod)
  PFˢ = RG.permuteˢ perm-f

  PGˢ : HomS (map K.vlab s_K_final) (map K.vlab K.cod)
  PGˢ = RK.permuteˢ perm-g

  Yc-≈̂ : Ycˢ ≈̂ PFˢ ∘ˢ pterm-f
  Yc-≈̂ =
    ∘-resp-≈̂ (⟦relabel-rigid⟧ G.vlab injL vlab-injL uRemapKdom after-G-≡
                              (sym map-rKd) after-G-↭ perm-f)
             (TG.term-emb-≈̂ (allFin G.nE) G.dom)

  combPˢ : proj₁ (RC.process-edgesˢ kblk (map remapP K.dom)) Perm.↭ C.cod
  combPˢ = Perm.trans (Perm.↭-sym ρf-K) perm-C2ˢ

  proc-stack-emb-K : proj₁ (RC.process-edgesˢ kblk (map remapP K.dom)) ≡ map remapP s_K_final
  proc-stack-emb-K = TK.proc-stack-embˢ (allFin K.nE) K.dom

  Xc-≈̂ : Xcˢ ≈̂ PGˢ ∘ˢ pterm-g
  Xc-≈̂ =
    ≈̂-trans (≈ˢ⇒≈̂ (≈-sym assocˢ))
            (∘-resp-≈̂ (⟦relabel-rigid⟧ K.vlab remapP remapP-vlab uCcod
                                       proc-stack-emb-K refl combPˢ perm-g)
                      (TK.term-emb-≈̂ (allFin K.nE) K.dom))

  domGF : map vlC C.dom ≡ flatten A
  domGF = ⟪⟫-domL (g ∘ f)

  codGF : map vlC C.cod ≡ flatten C₀
  codGF = ⟪⟫-codL (g ∘ f)

  midGFᵉ : map vlC (map remapP K.dom) ≡ flatten B
  midGFᵉ = trans (cong (map vlC) map-rKd) (trans (TG.vlab-φ G.cod) (⟪⟫-codL f))

  private
    Gpartˢ : castˢ domGF midGFᵉ Ycˢ ≈ˢ decodePˢ f
    Gpartˢ =
      viâ (cast-≈̂ {p = domGF} {q = midGFᵉ}) Yc-≈̂
          (cast-≈̂ {p = ⟪⟫-domL f} {q = ⟪⟫-codL f})

    Kpartˢ : castˢ midGFᵉ codGF Xcˢ ≈ˢ decodePˢ g
    Kpartˢ =
      viâ (cast-≈̂ {p = midGFᵉ} {q = codGF}) Xc-≈̂
          (cast-≈̂ {p = ⟪⟫-domL g} {q = ⟪⟫-codL g})

  decodePˢ-∘-shape : decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
  decodePˢ-∘-shape =
    ≈-trans (cast-resp domGF codGF Pcomp-eqˢ)
            (∘-cast-resp domGF midGFᵉ codGF Kpartˢ Gpartˢ)

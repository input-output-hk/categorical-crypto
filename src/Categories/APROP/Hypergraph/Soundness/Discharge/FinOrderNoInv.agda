{-# OPTIONS --safe --without-K #-}

-- Linearity and decoder validity do not imply a topological edge order.
-- With nV = nE = 2, dom = cod = [], and a two-cycle
-- e₀ : v₀ ↦ v₁, e₁ : v₁ ↦ v₀, each vertex is produced and consumed once.
-- Both edges skip, so the final stack is [] ↭ cod, yet e₁ ≺ e₀ inverts
-- allFin 2. Likewise the self-loop nV = nE = 1, ein = eout = v₀ ∷ [],
-- dom = cod = [] is Linear and Valid (the edge skips), but has Dep H e e.
-- Thus both NoInv and its diagonal require translation-specific proofs.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; hGen; hTensor; module hTensor-impl)
open FreeMonoidalHelper Symm (APROPSignature.X sig) using (flatten)
import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv using (inject+-inj; raise-inj; disj-L-R)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL; HomTermRec)

open import Categories.Combinatorics.FinCount
  using (++-bnd→disjoint)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP; remapP-injective)
open import Categories.APROP.Hypergraph.Model.Dependency using (Dep; Dep-reflect)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Util.Prune
  using (remap-↑ˡ→∈)
open import Data.Empty

open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties using (join-splitAt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁻; ∈-concat⁺′; ∈-tabulate⁺)
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.All using ([]; universal)
import Data.List.Relation.Unary.All.Properties as AllProp
open import Data.List.Relation.Unary.AllPairs as AP using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsProp
open import Data.Nat using (_+_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary


BelowH : (H : Hypergraph FlatGen)
       → Fin (Hypergraph.nE H) → Fin (Hypergraph.nE H) → Set
BelowH H a b = ¬ Dep H b a

NoInvH : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nE H)) → Set
NoInvH H = AllPairs (BelowH H)

-- AllPairs never pairs an element with itself, so the diagonal is extra content.
NoSelfDep : Hypergraph FlatGen → Set
NoSelfDep H = ∀ {e} → ¬ Dep H e e

splitE : ∀ {m n} (P : Fin (m + n) → Set)
       → (∀ a → P (a ↑ˡ n)) → (∀ b → P (m ↑ʳ b)) → ∀ e → P e
splitE {m} {n} P pl pr e = subst P (join-splitAt m n e) (go (splitAt m e))
  where
    go : ∀ s → P (join m n s)
    go (inj₁ a) = pl a
    go (inj₂ b) = pr b

NoSelfDep-hGen : ∀ {A B} (f : mor A B) → NoSelfDep (hGen f)
NoSelfDep-hGen {A} {B} f {zero} (v , v∈out , v∈in)
  with ∈-map⁻ (length (flatten A) ↑ʳ_) v∈out
     | ∈-map⁻ (_↑ˡ length (flatten B)) v∈in
... | jB , _ , v≡raise | iA , _ , v≡inject =
  Inv.↑ˡ≢↑ʳ iA jB (trans (sym v≡inject) v≡raise)

--------------------------------------------------------------------------------
-- Two-block orders
--------------------------------------------------------------------------------

-- Dependency reflections serve both the off-diagonal order and self-dependency.

module Assemble
  (G K H : Hypergraph FlatGen)
  (iL : Fin (Hypergraph.nE G) → Fin (Hypergraph.nE H))
  (iR : Fin (Hypergraph.nE K) → Fin (Hypergraph.nE H))
  (rL : ∀ {ea eb} → Dep H (iL eb) (iL ea) → Dep G eb ea)
  (rR : ∀ {ea eb} → Dep H (iR eb) (iR ea) → Dep K eb ea)
  (cross : ∀ {ea eb} → BelowH H (iL ea) (iR eb))
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  NoInvH-assemble : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                  → NoInvH G gs → NoInvH K ks
                  → NoInvH H (map iL gs ++ map iR ks)
  NoInvH-assemble gs ks noG noK =
    AllPairsProp.++⁺
      (AllPairsProp.map⁺ (AP.map (λ nd dep → nd (rL dep)) noG))
      (AllPairsProp.map⁺ (AP.map (λ nd dep → nd (rR dep)) noK))
      (AllProp.map⁺ (universal (λ _ → AllProp.map⁺ (universal (λ _ → cross) ks)) gs))

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module T = hTensor-impl G K

  H = hTensor G K

  injLE : Fin G.nE → Fin (G.nE + K.nE)
  injLE eG = eG ↑ˡ K.nE

  injRE : Fin K.nE → Fin (G.nE + K.nE)
  injRE eK = G.nE ↑ʳ eK

  tensor-GG-reflect : ∀ {ea eb : Fin G.nE} → Dep H (injLE eb) (injLE ea) → Dep G eb ea
  tensor-GG-reflect =
    Dep-reflect {sub = G} {H = H} T.injL (inject+-inj K.nV) injLE
      T.eout-c-inj₁-red T.ein-c-inj₁-red

  tensor-KK-reflect : ∀ {ea eb : Fin K.nE} → Dep H (injRE eb) (injRE ea) → Dep K eb ea
  tensor-KK-reflect =
    Dep-reflect {sub = K} {H = H} T.injR (raise-inj G.nV) injRE
      T.eout-c-inj₂-red T.ein-c-inj₂-red

  tensor-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                       → ¬ Dep H (injRE eb) (injLE ea)
  tensor-cross-acyclic {ea} {eb} (v , v∈out , v∈in) =
    disj-L-R (G.ein ea) (K.eout eb)
             ( subst (v ∈_) (T.ein-c-inj₁-red ea) v∈in
             , subst (v ∈_) (T.eout-c-inj₂-red eb) v∈out )

  NoInvH-tensor : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                → NoInvH G gs → NoInvH K ks
                → NoInvH H (map injLE gs ++ map injRE ks)
  NoInvH-tensor =
    Assemble.NoInvH-assemble G K H injLE injRE
      tensor-GG-reflect tensor-KK-reflect tensor-cross-acyclic

  NoSelfDep-tensor : NoSelfDep G → NoSelfDep K → NoSelfDep H
  NoSelfDep-tensor G-nd K-nd {e} =
    splitE {G.nE} {K.nE} (λ x → ¬ Dep H x x)
           (λ _ d → G-nd (tensor-GG-reflect d)) (λ _ d → K-nd (tensor-KK-reflect d)) e

  module _ (bdy : codL G ≡ domL K) (lin-G : Linear G) (lin-K : Linear K) where
    private module C = hComposeP-impl G K bdy

    Hc = hComposeP G K bdy

    compose-GG-reflect : ∀ {ea eb : Fin G.nE}
                       → Dep Hc (injLE eb) (injLE ea) → Dep G eb ea
    compose-GG-reflect =
      Dep-reflect {sub = G} {H = Hc} C.injL (inject+-inj _) injLE
        C.eout-c-inj₁-red C.ein-c-inj₁-red

    remapP-inj : ∀ {v v'} → C.remapP v ≡ C.remapP v' → v ≡ v'
    remapP-inj = remapP-injective G K bdy lin-G lin-K

    compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                       → Dep Hc (injRE eb) (injRE ea) → Dep K eb ea
    compose-KK-reflect =
      Dep-reflect {sub = K} {H = Hc} C.remapP remapP-inj injRE
        C.eout-c-inj₂-red C.ein-c-inj₂-red

    -- A K-output remapped into an injL slot must belong to K.dom.
    -- It then occurs twice in producedList K, contradicting the ≤1 bound.
    private
      dom-and-out→absurd
        : ∀ (k : Fin K.nV) (eb : Fin K.nE)
        → k ∈ K.dom → k ∈ K.eout eb → ⊥
      dom-and-out→absurd k eb k∈dom k∈out =
        ++-bnd→disjoint K.dom (concat (tabulate K.eout)) (proj₂ lin-K k)
                        k∈dom (∈-concat⁺′ k∈out (∈-tabulate⁺ eb))

    compose-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                          → ¬ Dep Hc (injRE eb) (injLE ea)
    compose-cross-acyclic {ea} {eb} (v , v∈out , v∈in)
      with subst (v ∈_) (C.eout-c-inj₂-red eb) v∈out
         | subst (v ∈_) (C.ein-c-inj₁-red ea) v∈in
    ... | v∈out' | v∈in' with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.injL v∈in'
    ... | k₀ , k₀∈out , v≡rk | i₀ , i₀∈in , v≡injL =
          dom-and-out→absurd k₀ eb
            (remap-↑ˡ→∈ K.dom C.lookup-cod k₀ i₀
              (trans (sym (C.remapP-≡ k₀)) (trans (sym v≡rk) v≡injL)))
            k₀∈out

    NoInvH-compose : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                   → NoInvH G gs → NoInvH K ks
                   → NoInvH Hc (map injLE gs ++ map injRE ks)
    NoInvH-compose =
      Assemble.NoInvH-assemble G K Hc injLE injRE
        compose-GG-reflect compose-KK-reflect compose-cross-acyclic

    NoSelfDep-compose : NoSelfDep G → NoSelfDep K → NoSelfDep Hc
    NoSelfDep-compose G-nd K-nd {e} =
      splitE {G.nE} {K.nE} (λ x → ¬ Dep Hc x x)
             (λ _ d → G-nd (compose-GG-reflect d)) (λ _ d → K-nd (compose-KK-reflect d)) e

--------------------------------------------------------------------------------
-- Translation invariants
--------------------------------------------------------------------------------
fin-order-NoInv-⟪⟫ : ∀ {A B} (f : HomTerm A B)
                → NoInvH ⟪ f ⟫ (allFin (Hypergraph.nE ⟪ f ⟫))

fin-order-NoInv-⟪⟫ =
  HomTermRec (λ H → NoInvH H (allFin (Hypergraph.nE H)))
    (λ _ → [] ∷ [])
    (λ _ → [])
    (λ f g nf ng →
      subst (NoInvH (hComposeP ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))))
            (sym (allFin-++ (Hypergraph.nE ⟪ f ⟫) (Hypergraph.nE ⟪ g ⟫)))
            (NoInvH-compose ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
              (⟪⟫-LinearP f) (⟪⟫-LinearP g) _ _ nf ng))
    (λ f g nf ng →
      subst (NoInvH (hTensor ⟪ f ⟫ ⟪ g ⟫))
            (sym (allFin-++ (Hypergraph.nE ⟪ f ⟫) (Hypergraph.nE ⟪ g ⟫)))
            (NoInvH-tensor ⟪ f ⟫ ⟪ g ⟫ _ _ nf ng))
    (λ _ _ → [])

dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) → NoSelfDep ⟪ f ⟫
dep-irrefl-⟪⟫ =
  HomTermRec NoSelfDep NoSelfDep-hGen (λ _ → λ { {()} })
    (λ f g nf ng → NoSelfDep-compose ⟪ f ⟫ ⟪ g ⟫
                     (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
                     (⟪⟫-LinearP f) (⟪⟫-LinearP g) nf ng)
    (λ f g → NoSelfDep-tensor ⟪ f ⟫ ⟪ g ⟫)
    (λ _ _ → λ { {()} })

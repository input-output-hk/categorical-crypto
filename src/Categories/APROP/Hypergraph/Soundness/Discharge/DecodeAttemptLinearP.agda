{-# OPTIONS --without-K --safe #-}

-- Pruning removes vertices, not edges, so atomic decode witnesses retain
-- the same Fin order. The composition case needs remapP injectivity.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig

open import Categories.APROP.Hypergraph.Model.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL
                    ; HomTermRec to HomTermRecₚ)

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefix.Properties

open import Categories.Combinatorics.FinCount
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig as Lin
  using (producedList; consumedList; Linear)
open import Categories.APROP.Hypergraph.Util.Prune

open import Data.Empty
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; cast; toℕ) renaming (splitAt to splitAtF)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; toℕ-cast; toℕ-injective)
  renaming (_≟_ to _≟F_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.Any using (any?)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Maybe using (nothing)
open import Data.Nat as Nat
import Data.Nat.Properties as Nat
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no)

private

  -- `cast eq` is injective (preserves `toℕ`).  Stdlib 2.3 lacks
  -- `cast-injective`; derived from `toℕ-cast` + `toℕ-injective`.
  cast-injective : ∀ {m n} (eq : m ≡ n) {i j : Fin m} → cast eq i ≡ cast eq j → i ≡ j
  cast-injective eq {i} {j} ci≡cj =
    toℕ-injective
      (trans (sym (toℕ-cast eq i))
             (trans (cong toℕ ci≡cj) (toℕ-cast eq j)))

  count-split3 : ∀ {n} (v : Fin n) (X : List (Fin n)) {C} (A B : List (Fin n))
               → C ≡ A ++ B → count v (X ++ C) ≡ count v X + count v A + count v B
  count-split3 v X A B refl = trans (count-++ v X (A ++ B))
    (trans (cong (count v X +_) (count-++ v A B)) (sym (Nat.+-assoc (count v X) _ _)))

module _
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Linear G) (lin-K : Linear K)
  where

  open hComposeP-impl G K bdy-eq

  private
    module G = Hypergraph G
    module K = Hypergraph K

    G-bal = proj₁ lin-G
    G-bnd = proj₂ lin-G
    K-bal = proj₁ lin-K
    K-bnd = proj₂ lin-K

    G-eb    = concat (tabulate G.eout)
    G-ein-b = concat (tabulate G.ein)
    K-eb    = concat (tabulate K.eout)
    K-ein-b = concat (tabulate K.ein)

    cn = count-non K.dom
  K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
  K-dom-bnd k = count-++-bndˡ k K.dom K-eb (K-bnd k)

  G-cod-bnd : ∀ v → count v G.cod Nat.≤ 1
  G-cod-bnd v =
    count-++-bndˡ v G.cod G-ein-b
      (Nat.≤-trans (Nat.≤-reflexive (sym (G-bal v))) (G-bnd v))

  K-dom-Unique : Unique K.dom
  K-dom-Unique = count≤1⇒Unique K-dom-bnd

  G-cod-Unique : Unique G.cod
  G-cod-Unique = count≤1⇒Unique G-cod-bnd

  lookup-cod-injective : ∀ {i j : Fin (length K.dom)} → lookup-cod i ≡ lookup-cod j → i ≡ j
  lookup-cod-injective {i} {j} eq =
    cast-injective dom-cod-len
      (lookup-injective-unique G-cod-Unique
        (cast dom-cod-len i) (cast dom-cod-len j) eq)

  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective {v} {v'} eq = remap-injective K.dom lookup-cod K-dom-Unique lookup-cod-injective
    (trans (sym (remapP-≡ v)) (trans eq (remapP-≡ v')))

  private
    remapP-on-dom : ∀ (idx : Fin (length K.dom)) → remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn
    remapP-on-dom idx =
      trans (remapP-≡ (lookup K.dom idx))
        (remap-inj₁ K.dom lookup-cod (lookup K.dom idx) idx
          (classify-lookup-Unique K.dom K-dom-Unique idx))

    map-ext-cast
      : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B) (g : C → B)
          (xs : List A) (ys : List C) (len : length xs ≡ length ys)
      → (∀ i → f (lookup xs i) ≡ g (lookup ys (cast len i)))
      → map f xs ≡ map g ys
    map-ext-cast f g []       []       _   _  = refl
    map-ext-cast f g []       (y ∷ ys) ()  _
    map-ext-cast f g (x ∷ xs) []       ()  _
    map-ext-cast f g (x ∷ xs) (y ∷ ys) len pt =
      cong₂ _∷_ (pt zero)
        (map-ext-cast f g xs ys (Nat.suc-injective len) (λ i → pt (suc i)))

  map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ cn) G.cod
  map-remapP-K-dom = map-ext-cast remapP (_↑ˡ cn) K.dom G.cod dom-cod-len remapP-on-dom

  count-map-remapP-K-dom-injL : ∀ (i : Fin G.nV) → count (i ↑ˡ cn) (map remapP K.dom) ≡ count i G.cod
  count-map-remapP-K-dom-injL i = trans (cong (count (i ↑ˡ cn)) map-remapP-K-dom) (count-map-↑ˡ cn i G.cod)

  count-map-remapP-K-dom-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (map remapP K.dom) ≡ 0
  count-map-remapP-K-dom-raise j =
    trans (cong (count (G.nV ↑ʳ j)) map-remapP-K-dom)
          (count-map-↑ˡ-mismatch G.nV j G.cod)

  ------------------------------------------------------------------------
  -- Composite linearity
  ------------------------------------------------------------------------

  eout-comp-eq : concat (tabulate eout-c) ≡ map injL G-eb ++ map remapP K-eb
  eout-comp-eq = concat-tabulate-blocks eout-c G.eout K.eout injL remapP
                   eout-c-inj₁-red eout-c-inj₂-red

  ein-comp-eq : concat (tabulate ein-c) ≡ map injL G-ein-b ++ map remapP K-ein-b
  ein-comp-eq = concat-tabulate-blocks ein-c G.ein K.ein injL remapP
                  ein-c-inj₁-red ein-c-inj₂-red

  count-prod
    : ∀ v
    → count v (producedList (hComposeP G K bdy-eq))
    ≡ count v (map injL G.dom)
    + count v (map injL G-eb)
    + count v (map remapP K-eb)
  count-prod v =
    count-split3 v (map injL G.dom) (map injL G-eb) (map remapP K-eb) eout-comp-eq

  count-cons
    : ∀ v
    → count v (consumedList (hComposeP G K bdy-eq))
    ≡ count v (map remapP K.cod)
    + count v (map injL G-ein-b)
    + count v (map remapP K-ein-b)
  count-cons v =
    count-split3 v (map remapP K.cod) (map injL G-ein-b) (map remapP K-ein-b) ein-comp-eq

  K-bal-via-remapP : ∀ v → count v (map remapP (K.dom ++ K-eb)) ≡ count v (map remapP (K.cod ++ K-ein-b))
  K-bal-via-remapP v = count-map-resp remapP (K.dom ++ K-eb) (K.cod ++ K-ein-b) K-bal v

  αβ≡εη
    : ∀ v
    → count v (map injL G.dom) + count v (map injL G-eb)
    ≡ count v (map injL G-ein-b) + count v (map remapP K.dom)
  αβ≡εη v with splitAtF G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl =
                  trans (cong₂ Nat._+_
                          (count-map-↑ˡ cn i G.dom)
                          (count-map-↑ˡ cn i G-eb))
                  (trans (sym (count-++ i G.dom G-eb))
                  (trans (G-bal i)
                  (trans (count-swap i G.cod G-ein-b)
                  (trans (count-++ i G-ein-b G.cod)
                         (cong₂ Nat._+_
                           (sym (count-map-↑ˡ cn i G-ein-b))
                           (sym (count-map-remapP-K-dom-injL i)))))))
  αβ≡εη v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl =
                       trans (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G.dom)
                               (count-map-↑ˡ-mismatch G.nV j G-eb))
                       (sym (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G-ein-b)
                               (count-map-remapP-K-dom-raise j)))

  balance : ∀ v → count v (producedList (hComposeP G K bdy-eq)) ≡ count v (consumedList (hComposeP G K bdy-eq))
  balance v =
    trans (count-prod v)
    (trans (cong (Nat._+ γ) (αβ≡εη v))
    (trans (Nat.+-assoc ε η γ)
    (trans (cong (ε Nat.+_)
                 (trans (sym (count-++ v (map remapP K.dom) (map remapP K-eb)))
                 (trans (sym (cong (count v) (map-++ remapP K.dom K-eb)))
                 (trans (K-bal-via-remapP v)
                 (trans (cong (count v) (map-++ remapP K.cod K-ein-b))
                        (count-++ v (map remapP K.cod) (map remapP K-ein-b)))))))
    (trans (sym (Nat.+-assoc ε δ ζ))
    (trans (cong (Nat._+ ζ) (Nat.+-comm ε δ))
           (sym (count-cons v)))))))
    where
      γ = count v (map remapP K-eb)
      δ = count v (map remapP K.cod)
      ε = count v (map injL G-ein-b)
      ζ = count v (map remapP K-ein-b)
      η = count v (map remapP K.dom)

  -- Only K.dom members route to injL slots. A K-eb preimage there would
  -- violate the bound on K.dom ++ K-eb, so its contribution must vanish.

  private
    K-eb-bnd : ∀ k → count k K-eb Nat.≤ 1
    K-eb-bnd k = count-++-bndʳ k K.dom K-eb (K-bnd k)

    count-remapP-K-eb-≤1 : ∀ v → count v (map remapP K-eb) Nat.≤ 1
    count-remapP-K-eb-≤1 v with any? (v ≟F_) (map remapP K-eb)
    ... | no  v∉ = Nat.≤-trans (Nat.≤-reflexive (∉→count-zero v∉)) z≤n
    ... | yes v∈ with ∈-map⁻ remapP v∈
    ...   | k , _ , v≡rk =
            Nat.≤-trans
              (Nat.≤-reflexive
                (subst (λ w → count w (map remapP K-eb) ≡ count k K-eb) (sym v≡rk)
                       (count-map-inj remapP remapP-injective k K-eb)))
              (K-eb-bnd k)

    count-injL-remapP-K-eb-zero : ∀ (i : Fin G.nV) → count (injL i) (map remapP K-eb) ≡ 0
    count-injL-remapP-K-eb-zero i with any? (injL i ≟F_) (map remapP K-eb)
    ... | no  i∉ = ∉→count-zero i∉
    ... | yes i∈ with ∈-map⁻ remapP i∈
    ...   | k , k∈ , i≡rk =
            ⊥-elim (++-bnd→disjoint K.dom K-eb (K-bnd k)
                      (remap-↑ˡ→∈ K.dom lookup-cod k i (trans (sym (remapP-≡ k)) (sym i≡rk))) k∈)

    bound-injL : ∀ (i : Fin G.nV) → count (injL i) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-injL i =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (i ↑ˡ cn))
              (trans (cong (Nat._+ count (injL i) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ cn i G.dom)
                             (count-map-↑ˡ cn i G-eb)))
                     (trans (cong (count i G.dom + count i G-eb Nat.+_)
                                  (count-injL-remapP-K-eb-zero i))
                            (trans (Nat.+-identityʳ _)
                                   (sym (count-++ i G.dom G-eb)))))))
        (G-bnd i)

    bound-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-raise j =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (G.nV ↑ʳ j))
              (trans (cong (Nat._+ count (G.nV ↑ʳ j) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ-mismatch G.nV j G.dom)
                             (count-map-↑ˡ-mismatch G.nV j G-eb)))
                     refl)))
        (count-remapP-K-eb-≤1 (G.nV ↑ʳ j))

  bound : ∀ v → count v (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
  bound v with splitAtF G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl = bound-injL i
  bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl = bound-raise j

  Linear-hComposeP : Linear (hComposeP G K bdy-eq)
  Linear-hComposeP = balance , bound

  ------------------------------------------------------------------------
  -- Composite totality
  ------------------------------------------------------------------------

  module PureL =
    StackLiftEmb (hComposeP G K bdy-eq) G (_↑ˡ K.nE) injL (Inv.inject+-inj cn)
                 ein-c-inj₁-red eout-c-inj₁-red

  private
    module ViaRemapP where
      out : List (Fin K.nV) → List (Fin nV-P)
      out = map remapP

      front : ∀ (e : Fin K.nE) (ys rest : List (Fin K.nV))
            → ys Perm.↭ K.ein e ++ rest
            → out ys Perm.↭ map remapP (K.ein e) ++ out rest
      front e ys rest p =
        Perm.↭-trans (PermProp.map⁺ remapP p)
                     (Perm.↭-reflexive (map-++ remapP (K.ein e) rest))

      fold : ∀ (e : Fin K.nE) (rest : List (Fin K.nV))
           → map remapP (K.eout e) ++ out rest Perm.↭ out (K.eout e ++ rest)
      fold e rest = Perm.↭-reflexive (sym (map-++ remapP (K.eout e) rest))

      miss : ∀ (e : Fin K.nE) (ys : List (Fin K.nV))
           → extract-prefix (K.ein e) ys ≡ nothing
           → extract-prefix (map remapP (K.ein e)) (out ys) ≡ nothing
      miss e ys eq =
        extract-prefix-via-injective-nothing remapP remapP-injective
                                              (K.ein e) ys eq

      open PermLift (hComposeP G K bdy-eq) K (G.nE ↑ʳ_) remapP out
             ein-c-inj₂-red eout-c-inj₂-red front fold miss public

  decode-attempt-hComposeP
    : process-all-edges G (Hypergraph.dom G) Perm.↭ Hypergraph.cod G
    → process-all-edges K (Hypergraph.dom K) Perm.↭ Hypergraph.cod K
    → process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))
        Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
  decode-attempt-hComposeP perm-G perm-K = perm-final
    where
      open Perm.PermutationReasoning

      s_G_final = process-all-edges G G.dom
      s_K_final = process-all-edges K K.dom

      proc = process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))

      after-G-stack = process-edges (hComposeP G K bdy-eq)
                        (map (_↑ˡ K.nE) (allFin G.nE))
                        (Hypergraph.dom (hComposeP G K bdy-eq))

      after-G-≡ : after-G-stack ≡ map injL s_G_final
      after-G-≡ = PureL.process-edges-lift (allFin G.nE) G.dom

      after-G-↭-remap-Kdom : after-G-stack Perm.↭ map remapP K.dom
      after-G-↭-remap-Kdom = begin
        after-G-stack
          ≡⟨ after-G-≡ ⟩
        map injL s_G_final
          ↭⟨ PermProp.map⁺ injL perm-G ⟩
        map injL G.cod
          ≡⟨ sym map-remapP-K-dom ⟩
        map remapP K.dom ∎

      K-lift : process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (allFin K.nE)) after-G-stack
                 Perm.↭ map remapP s_K_final
      K-lift = ViaRemapP.process-edges-lift
                 (allFin K.nE) after-G-stack K.dom after-G-↭-remap-Kdom

      proc-≡ : proc
               ≡ process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (allFin K.nE)) after-G-stack
      proc-≡ =
        trans (cong (λ es → process-edges (hComposeP G K bdy-eq) es
                              (Hypergraph.dom (hComposeP G K bdy-eq)))
                    (allFin-++ G.nE K.nE))
              (process-edges-++ (hComposeP G K bdy-eq)
                (map (_↑ˡ K.nE) (allFin G.nE))
                (map (G.nE ↑ʳ_) (allFin K.nE))
                (Hypergraph.dom (hComposeP G K bdy-eq)))

      perm-final : proc Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
      perm-final = begin
        proc
          ≡⟨ proc-≡ ⟩
        process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (allFin K.nE)) after-G-stack
          ↭⟨ K-lift ⟩
        map remapP s_K_final
          ↭⟨ PermProp.map⁺ remapP perm-K ⟩
        map remapP K.cod ∎

⟪⟫-LinearP : ∀ {A B} (f : HomTerm A B) → Lin.Linear ⟪ f ⟫ₚ
⟪⟫-LinearP =
  HomTermRecₚ Lin.Linear Lin.Linear-hGen Lin.Linear-hId
    (λ f g → Linear-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
               (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g))))
    (λ f g → Lin.Linear-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ)
    Lin.Linear-hSwap

decode-attempt-LinearP
  : ∀ {A B} (f : HomTerm A B)
  → process-all-edges ⟪ f ⟫ₚ (Hypergraph.dom ⟪ f ⟫ₚ) Perm.↭ Hypergraph.cod ⟪ f ⟫ₚ
decode-attempt-LinearP =
  HomTermRecₚ (λ H → process-all-edges H (Hypergraph.dom H) Perm.↭ Hypergraph.cod H)
    decode-attempt-hGen decode-attempt-hId
    (λ f g → decode-attempt-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
               (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
               (⟪⟫-LinearP f) (⟪⟫-LinearP g))
    (λ f g → decode-attempt-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ)
    decode-attempt-hSwap


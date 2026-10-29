{-# OPTIONS --safe --without-K #-}

-- The free SMC has neither duplication nor discarding: a vertex must be
-- produced and consumed once, or remain stranded and absent from the term.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Linearity.Linearity (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using ( FlatGen
        ; hId; hGen; hSwap; hTensor
        ; module hTensor-impl; module hGenSwap-impl)
open FreeMonoidalHelper Symm (APROPSignature.X sig) using (flatten)
open import Categories.Combinatorics.FinCount

open import Data.Empty
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (_≟_; suc-injective; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.Nat as Nat using (ℕ; zero; suc; s≤s; z≤n; _+_)
import Data.Nat.Properties as Nat
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no)

private variable n m nA nB : ℕ

private
  count-LL-RR-eq-1
    : ∀ (nA nB : ℕ) (v : Fin (nA + nB))
    → count v (map (_↑ˡ nB) (allFin nA) ++ map (nA ↑ʳ_) (allFin nB)) ≡ 1
  count-LL-RR-eq-1 nA nB v =
    trans (sym (cong (count v) (allFin-++ nA nB))) (count-allFin v)

producedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
producedList H = Hypergraph.dom H ++ concat (tabulate (Hypergraph.eout H))

consumedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
consumedList H = Hypergraph.cod H ++ concat (tabulate (Hypergraph.ein H))

Linear : Hypergraph FlatGen → Set
Linear H = (∀ v → count v (producedList H) ≡ count v (consumedList H))
         × (∀ v → count v (producedList H) Nat.≤ 1)

--------------------------------------------------------------------------------
-- Constructor linearity
--------------------------------------------------------------------------------
Linear-hTensor : (G K : Hypergraph FlatGen) → Linear G → Linear K → Linear (hTensor G K)
Linear-hTensor G K (G-bal , G-bnd) (K-bal , K-bnd) = balance , bound
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

    eout-tensor-eq
      : concat (tabulate eout-c)
      ≡ map injL (concat (tabulate G.eout))
        ++ map injR (concat (tabulate K.eout))
    eout-tensor-eq = concat-tabulate-blocks eout-c G.eout K.eout injL injR
                       eout-c-inj₁-red eout-c-inj₂-red

    ein-tensor-eq
      : concat (tabulate ein-c)
      ≡ map injL (concat (tabulate G.ein))
        ++ map injR (concat (tabulate K.ein))
    ein-tensor-eq = concat-tabulate-blocks ein-c G.ein K.ein injL injR
                      ein-c-inj₁-red ein-c-inj₂-red

    count-injL-mixed
      : ∀ (i : Fin G.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injL i) (map injL xs ++ map injR ys) ≡ count i xs
    count-injL-mixed i xs ys =
      trans (count-++ (injL i) (map injL xs) (map injR ys))
      (trans (cong₂ Nat._+_
                (count-map-↑ˡ K.nV i xs)
                (count-map-↑ʳ-mismatch K.nV i ys))
             (Nat.+-identityʳ (count i xs)))

    count-injR-mixed
      : ∀ (j : Fin K.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injR j) (map injL xs ++ map injR ys) ≡ count j ys
    count-injR-mixed j xs ys =
      trans (count-++ (injR j) (map injL xs) (map injR ys))
            (cong₂ Nat._+_
              (count-map-↑ˡ-mismatch G.nV j xs)
              (count-map-↑ʳ G.nV j ys))

    count-face
      : ∀ {nZ} {v : Fin (G.nV + K.nV)} {z : Fin nZ}
          (pick : List (Fin G.nV) → List (Fin K.nV) → List (Fin nZ))
      → (∀ xs ys → count v (map injL xs ++ map injR ys) ≡ count z (pick xs ys))
      → ∀ (Bg : List (Fin G.nV)) (Bk : List (Fin K.nV))
          {Ec : List (Fin (G.nV + K.nV))}
          {Eg : List (Fin G.nV)} {Ek : List (Fin K.nV)}
      → Ec ≡ map injL Eg ++ map injR Ek
      → count v ((map injL Bg ++ map injR Bk) ++ Ec)
        ≡ count z (pick Bg Bk ++ pick Eg Ek)
    count-face {v = v} {z} pick mixed Bg Bk {Ec} {Eg} {Ek} eq =
      trans (count-++ v (map injL Bg ++ map injR Bk) Ec)
      (trans (cong₂ Nat._+_
                (mixed Bg Bk)
                (trans (cong (count v) eq) (mixed Eg Ek)))
             (sym (count-++ z (pick Bg Bk) (pick Eg Ek))))

    count-injL-prod
      : ∀ (i : Fin G.nV)
      → count (injL i) (producedList (hTensor G K)) ≡ count i (producedList G)
    count-injL-prod i =
      count-face (λ xs _ → xs) (count-injL-mixed i) G.dom K.dom eout-tensor-eq

    count-injL-cons
      : ∀ (i : Fin G.nV)
      → count (injL i) (consumedList (hTensor G K)) ≡ count i (consumedList G)
    count-injL-cons i =
      count-face (λ xs _ → xs) (count-injL-mixed i) G.cod K.cod ein-tensor-eq

    count-injR-prod
      : ∀ (j : Fin K.nV)
      → count (injR j) (producedList (hTensor G K)) ≡ count j (producedList K)
    count-injR-prod j =
      count-face (λ _ ys → ys) (count-injR-mixed j) G.dom K.dom eout-tensor-eq

    count-injR-cons
      : ∀ (j : Fin K.nV)
      → count (injR j) (consumedList (hTensor G K)) ≡ count j (consumedList K)
    count-injR-cons j =
      count-face (λ _ ys → ys) (count-injR-mixed j) G.cod K.cod ein-tensor-eq

    balance : ∀ v → count v (producedList (hTensor G K)) ≡ count v (consumedList (hTensor G K))
    balance v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl = trans (count-injL-prod i) (trans (G-bal i) (sym (count-injL-cons i)))
    balance v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                  | refl = trans (count-injR-prod j) (trans (K-bal j) (sym (count-injR-cons j)))

    bound : ∀ v → count v (producedList (hTensor G K)) Nat.≤ 1
    bound v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl rewrite count-injL-prod i = G-bnd i
    bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                | refl rewrite count-injR-prod j = K-bnd j

Linear-hSwap : ∀ A B → Linear (hSwap A B)
Linear-hSwap A B = balance , bound
  where
    open hGenSwap-impl A B using (Lblk; Rblk) renaming (nA to nA₀; nB to nB₀)

    balance : ∀ v → count v ((Lblk ++ Rblk) ++ []) ≡ count v ((Rblk ++ Lblk) ++ [])
    balance v rewrite ++-identityʳ (Lblk ++ Rblk) | ++-identityʳ (Rblk ++ Lblk) =
      count-swap v Lblk Rblk

    bound : ∀ v → count v ((Lblk ++ Rblk) ++ []) Nat.≤ 1
    bound v rewrite ++-identityʳ (Lblk ++ Rblk) | count-LL-RR-eq-1 nA₀ nB₀ v = s≤s z≤n

Linear-hGen : ∀ {A B} (g : mor A B) → Linear (hGen g)
Linear-hGen {A} {B} _ = balance , bound
  where
    open hGenSwap-impl A B using (Lblk; Rblk) renaming (nA to nA₀; nB to nB₀)

    balance : ∀ v → count v (Lblk ++ (Rblk ++ [])) ≡ count v (Rblk ++ (Lblk ++ []))
    balance v rewrite ++-identityʳ Rblk | ++-identityʳ Lblk = count-swap v Lblk Rblk

    bound : ∀ v → count v (Lblk ++ (Rblk ++ [])) Nat.≤ 1
    bound v rewrite ++-identityʳ Rblk | count-LL-RR-eq-1 nA₀ nB₀ v = s≤s z≤n

Linear-hId : ∀ A → Linear (hId A)
Linear-hId A = (λ _ → refl) , bound
  where
    bound : ∀ v → count v (allFin (length (flatten A)) ++ []) Nat.≤ 1
    bound v rewrite ++-identityʳ (allFin (length (flatten A))) | count-allFin v = s≤s z≤n

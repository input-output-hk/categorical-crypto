{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Linearity invariant on translated hypergraphs.
--
-- A hypergraph `H` is *linear* when every vertex's "production" count
-- (appearances in `dom ++ concat (tabulate eout)`) matches its
-- "consumption" count (appearances in `cod ++ concat (tabulate ein)`)
-- and both are at most 1.
--
-- This is the side condition under which the cospan-form decoder can
-- build a `HomTerm`: the free symmetric monoidal category has no
-- duplication or discarding, so each vertex must be produced and
-- consumed exactly once (or 0 times for *stranded* vertices, which do
-- not show up in the decoded term).
--
-- The pruned translation always satisfies linearity
-- (`DecodeAttemptLinearP.⟪⟫-LinearP`), by structural induction using
-- `Linear-hTensor` here and `DecodeAttemptLinearP.Linear-hComposeP`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Linearity.Linearity (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using ( FlatGen; flatten; range
        ; hId; hGen; hSwap; hTensor
        ; module hTensor-impl; module hGenSwap-impl)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (↑ˡ≢↑ʳ; range-++)
-- `count v xs` (occurrences of `v` in `xs`) and its `_++_` distribution law
-- live in the signature-free count leaf `Discharge.CountCombinatorics`.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics
  using (count; count-++)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using
  (_≟_; suc-injective; ↑ˡ-injective; ↑ʳ-injective; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List.Properties using
  (++-identityʳ; tabulate-cong; map-tabulate; concat-map; concat-++)
import Function as Fun
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no)

-- Generic `count` behaviour under `map f`: an injective `f` preserves the
-- count of any preimage, and a value with no `f`-preimage has count 0.  All
-- the per-injection lemmas below are instances, and `count-map-inj` is also
-- applied directly at `f = remapP` (after a `subst` rewriting the counted
-- value to its fiber) in `Discharge.DecodeAttemptLinearP`.

count-map-inj : ∀ {n m} (f : Fin n → Fin m) → (∀ {a b} → f a ≡ f b → a ≡ b)
              → (v : Fin n) (xs : List (Fin n)) → count (f v) (map f xs) ≡ count v xs
count-map-inj f f-inj v []       = refl
count-map-inj f f-inj v (x ∷ xs) with f v ≟ f x | v ≟ x
... | yes _ | yes _ = cong suc (count-map-inj f f-inj v xs)
... | yes p | no  q = ⊥-elim (q (f-inj p))
... | no  q | yes p = ⊥-elim (q (cong f p))
... | no  _ | no  _ = count-map-inj f f-inj v xs

count-map-miss : ∀ {n m} (f : Fin n → Fin m) {w : Fin m} → (∀ x → f x ≢ w)
               → (xs : List (Fin n)) → count w (map f xs) ≡ 0
count-map-miss f miss []       = refl
count-map-miss f {w} miss (x ∷ xs) with w ≟ f x
... | yes p = ⊥-elim (miss x (sym p))
... | no  _ = count-map-miss f miss xs

-- count of `v` in `range n`: every Fin appears exactly once.

private
  count-zero-map-suc : ∀ {n} (xs : List (Fin n)) → count (zero {n = n}) (map suc xs) ≡ 0
  count-zero-map-suc = count-map-miss suc (λ _ ())

  count-suc-map-suc : ∀ {n} (i : Fin n) (xs : List (Fin n)) → count (suc i) (map suc xs) ≡ count i xs
  count-suc-map-suc = count-map-inj suc suc-injective

count-range : ∀ {n} (v : Fin n) → count v (range n) ≡ 1
count-range {n = suc n} zero    with zero {n = n} ≟ zero
... | yes _ = cong suc (count-zero-map-suc {n = n} (range n))
... | no  q = ⊥-elim (q refl)
count-range {n = suc n} (suc i) with suc i ≟ zero
... | no  _ = trans (count-suc-map-suc i (range n)) (count-range i)

--------------------------------------------------------------------------------
-- Counting along the disjoint injections `_↑ˡ_` and `_↑ʳ_`.

-- The "matching" cases: `count`-preservation along the injections
-- `_↑ˡ nB` / `nA ↑ʳ_` (instances of `count-map-inj`).
count-map-↑ˡ : ∀ {nA} nB (i : Fin nA) (xs : List (Fin nA))
             → count (i ↑ˡ nB) (map (_↑ˡ nB) xs) ≡ count i xs
count-map-↑ˡ nB = count-map-inj (_↑ˡ nB) (λ {a} {b} → ↑ˡ-injective nB a b)

count-map-↑ʳ : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nB))
             → count (nA ↑ʳ j) (map (nA ↑ʳ_) xs) ≡ count j xs
count-map-↑ʳ nA = count-map-inj (nA ↑ʳ_) (λ {a} {b} → ↑ʳ-injective nA a b)

-- The "mismatch" cases: a `nA ↑ʳ j` never appears in an `_↑ˡ_` image,
-- and vice versa (instances of `count-map-miss`).

count-map-↑ˡ-mismatch : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA))
                      → count (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ 0
count-map-↑ˡ-mismatch nA {nB} j = count-map-miss (_↑ˡ nB) (λ x → ↑ˡ≢↑ʳ x j)

count-map-↑ʳ-mismatch : ∀ {nA} nB (i : Fin nA) (xs : List (Fin nB))
                      → count (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ 0
count-map-↑ʳ-mismatch {nA} nB i = count-map-miss (nA ↑ʳ_) (λ x q → ↑ˡ≢↑ʳ i x (sym q))

-- count is invariant under swapping the two sides of a `_++_`.

count-swap : ∀ {n} (v : Fin n) (xs ys : List (Fin n)) → count v (xs ++ ys) ≡ count v (ys ++ xs)
count-swap v xs ys =
  trans (count-++ v xs ys)
        (trans (Nat.+-comm (count v xs) (count v ys))
               (sym (count-++ v ys xs)))

-- `tabulate` over `Fin (m + n)` splits along the `↑ˡ`/`↑ʳ` boundary.

tabulate-+ : ∀ {m n} {A : Set} (f : Fin (m + n) → A)
           → tabulate f
           ≡ tabulate (λ i → f (i ↑ˡ n)) ++ tabulate (λ j → f (m ↑ʳ j))
tabulate-+ {m = zero}              f = refl
tabulate-+ {m = suc m} {n = n}     f = cong (f zero ∷_) (tabulate-+ {m = m} {n = n} (f Fun.∘ suc))

-- A block-indexed `concat ∘ tabulate` splits into its two relabelled blocks.
-- `fc` is a family over `Fin (m + n)` that reduces, on each side of the
-- `↑ˡ`/`↑ʳ` boundary, to a relabelling (`gL` / `gR`) of a family over that
-- side alone.  Used at all four `{eout,ein}-{tensor,comp}-eq` sites.
-- (public: also reused by Discharge.DecodeAttemptLinearP)
concat-tabulate-blocks
  : ∀ {m n} {A B C : Set}
      (fc : Fin (m + n) → List C) (fG : Fin m → List A) (fK : Fin n → List B)
      (gL : A → C) (gR : B → C)
  → (∀ e → fc (e ↑ˡ n) ≡ map gL (fG e))
  → (∀ e → fc (m ↑ʳ e) ≡ map gR (fK e))
  → concat (tabulate fc)
    ≡ map gL (concat (tabulate fG)) ++ map gR (concat (tabulate fK))
concat-tabulate-blocks {m} {n} fc fG fK gL gR redL redR =
  trans (cong concat (tabulate-+ {m = m} {n = n} fc))
  (trans (cong concat
            (cong₂ _++_ (trans (tabulate-cong redL) (sym (map-tabulate fG (map gL))))
                        (trans (tabulate-cong redR) (sym (map-tabulate fK (map gR))))))
  (trans (sym (concat-++ (map (map gL) (tabulate fG)) (map (map gR) (tabulate fK))))
         (cong₂ _++_ (concat-map (tabulate fG)) (concat-map (tabulate fK)))))

-- The combined `LL ++ RR` list contains every Fin (nA + nB) exactly once —
-- because it IS `range (nA + nB)`, split along the `↑ˡ`/`↑ʳ` boundary by
-- `Invariant.range-++`.  No case analysis on `splitAt nA v` is needed: the
-- per-side count bookkeeping is already inside `count-range`.

private
  count-LL-RR-eq-1
    : ∀ (nA nB : ℕ) (v : Fin (nA + nB))
    → count v (map (_↑ˡ nB) (range nA) ++ map (nA ↑ʳ_) (range nB)) ≡ 1
  count-LL-RR-eq-1 nA nB v =
    trans (sym (cong (count v) (range-++ nA nB))) (count-range v)

-- Production / consumption lists of a hypergraph.

producedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
producedList H = Hypergraph.dom H ++ concat (tabulate (Hypergraph.eout H))

consumedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
consumedList H = Hypergraph.cod H ++ concat (tabulate (Hypergraph.ein H))

-- Linearity: matching production / consumption counts, each ≤ 1.

Linear : Hypergraph FlatGen → Set
Linear H = (∀ v → count v (producedList H) ≡ count v (consumedList H))
         × (∀ v → count v (producedList H) Nat.≤ 1)

--------------------------------------------------------------------------------
-- Tensor preserves linearity.
--
-- For `v = injL i`, `count v ≡ count i` on G's lists; for `v = injR j`,
-- `count v ≡ count j` on K's lists.  Both sides match by `Linear G`/
-- `Linear K`, and the bound transfers.

Linear-hTensor : (G K : Hypergraph FlatGen) → Linear G → Linear K → Linear (hTensor G K)
Linear-hTensor G K (G-bal , G-bnd) (K-bal , K-bnd) = balance , bound
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

    -- Decompose `concat (tabulate {ein,eout}-c)` into the L/R-side blocks.

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

    -- `count (injL i)` of the composite's lists equals `count i` of G's;
    -- `count (injR j)` equals `count j` of K's.  Four faces, ONE proof
    -- (`count-face`) at two independent binary choices: the BOUNDARY axis
    -- (`dom`/`eout` vs `cod`/`ein`), which enters as the two blocks plus the
    -- decomposition of the composite's edge list, and the SIDE axis
    -- (`injL`/G vs `injR`/K), which enters as that side's own `mixed` lemma
    -- plus the block selector `pick` it is stated at.

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

--------------------------------------------------------------------------------
-- Base cases.

-- Symmetry: `dom = Lblk ++ Rblk`, `cod = Rblk ++ Lblk`, no edges.  Both sides
-- count `Lblk`/`Rblk` once each, just permuted; bound by `count-LL-RR-eq-1`.
Linear-hSwap : ∀ A B → Linear (hSwap A B)
Linear-hSwap A B = balance , bound
  where
    open hGenSwap-impl A B using (nA; nB; Lblk; Rblk)

    balance : ∀ v → count v ((Lblk ++ Rblk) ++ []) ≡ count v ((Rblk ++ Lblk) ++ [])
    balance v rewrite ++-identityʳ (Lblk ++ Rblk) | ++-identityʳ (Rblk ++ Lblk) =
      count-swap v Lblk Rblk

    bound : ∀ v → count v ((Lblk ++ Rblk) ++ []) Nat.≤ 1
    bound v rewrite ++-identityʳ (Lblk ++ Rblk) | count-LL-RR-eq-1 nA nB v = s≤s z≤n

-- Generator edge: `dom = Lblk`, `cod = Rblk`; the single edge has
-- `ein _ = Lblk`, `eout _ = Rblk`.  Reduces to the same `Lblk ⊕ Rblk` story
-- as hSwap.
Linear-hGen : ∀ {A B} (g : mor A B) → Linear (hGen g)
Linear-hGen {A} {B} _ = balance , bound
  where
    open hGenSwap-impl A B using (nA; nB; Lblk; Rblk)

    balance : ∀ v → count v (Lblk ++ (Rblk ++ [])) ≡ count v (Rblk ++ (Lblk ++ []))
    balance v rewrite ++-identityʳ Rblk | ++-identityʳ Lblk = count-swap v Lblk Rblk

    bound : ∀ v → count v (Lblk ++ (Rblk ++ [])) Nat.≤ 1
    bound v rewrite ++-identityʳ Rblk | count-LL-RR-eq-1 nA nB v = s≤s z≤n

-- Identity: no edges, `dom = cod = range (length (flatten A))`, in which
-- every vertex occurs exactly once (`count-range`).
Linear-hId : ∀ A → Linear (hId A)
Linear-hId A = (λ _ → refl) , bound
  where
    bound : ∀ v → count v (range (length (flatten A)) ++ []) Nat.≤ 1
    bound v rewrite ++-identityʳ (range (length (flatten A))) | count-range v = s≤s z≤n


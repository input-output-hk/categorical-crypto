{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Shared base for the type-A exchange condition (`bring-to-front`): the
-- action of a generator on value-positions, the descent ⇔ position
-- characterisation, the Far/Adj decision, and `inv ≤ length`.
------------------------------------------------------------------------
module Categories.PermuteCoherence.BringToFrontBase where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n; s<s)
open import Data.Nat.Properties
  using (<-cmp; <-trans; <-irrefl; 1+n≢n; suc-injective; ≤-trans; n≤1+n; 1+n≰n)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc; zero to fz)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; _∘-fb_; id-fb; inv-fb)
open import Categories.PermuteCoherence.Word
  using (Word; evalW; genFB; _~ʷ_; ~refl; ~sym; ~trans; ∷c; c1; c2; c3; Far; far0ˡ; far0ʳ; farS; Adj; adj0; adjS; ∷-cong; genFB-involutive; ~ʷ⇒≈)
open import Categories.PermuteCoherence.Inversions using (inv)
open import Categories.PermuteCoherence.InversionsCong using (inv-resp-≈)
open import Categories.PermuteCoherence.ExchangeBase
  using (Reduced; descent; inv-di; inv≤length)
open import Categories.PermuteCoherence.InversionsDichotomy
  using (inj; suc-pos; toℕ-inj; toℕ-suc-pos; swapℕ; swapℕ-k; swapℕ-sk; genFB-toℕ; invS-dichotomy)
open import Categories.PermuteCoherence.InversionsRec using (invS≡inv)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Elementary `≤`/`<` plumbing.

2+n≢n : (m : ℕ) → suc (suc m) ≢ m
2+n≢n zero    ()
2+n≢n (suc m) e = 2+n≢n m (suc-injective e)

------------------------------------------------------------------------
-- `genFB k` is an involution, so its backward and forward actions agree
-- pointwise.

genFB-ˡ≡ʳ : (k : Fin (suc n)) (z : Fin (suc (suc n)))
          → genFB k P.⟨$⟩ˡ z ≡ genFB k P.⟨$⟩ʳ z
genFB-ˡ≡ʳ k z =
  sym (trans (cong (genFB k P.⟨$⟩ʳ_) (sym (P.inverseʳ (genFB k) {z})))
             (genFB-involutive k (genFB k P.⟨$⟩ˡ z)))

------------------------------------------------------------------------
-- `swapℕ k` fixes any value outside `{k, suc k}`.

swapℕ-fix-val : (k a : ℕ) → a ≢ k → a ≢ suc k → swapℕ k a ≡ a
swapℕ-fix-val zero    zero          a≢k _   = ⊥-elim (a≢k refl)
swapℕ-fix-val zero    (suc zero)    _   a≢sk = ⊥-elim (a≢sk refl)
swapℕ-fix-val zero    (suc (suc m)) _   _    = refl
swapℕ-fix-val (suc k) zero          _   _    = refl
swapℕ-fix-val (suc k) (suc a)       a≢k a≢sk =
  cong suc (swapℕ-fix-val k a (λ e → a≢k (cong suc e)) (λ e → a≢sk (cong suc e)))

------------------------------------------------------------------------
-- The action of a generator on the value-positions (`toℕ`): `genFB k`
-- swaps the values `k` and `k+1` and fixes every other value.

genFB-on-inj : (k : Fin (suc n))
             → toℕ (genFB k P.⟨$⟩ʳ inj k) ≡ suc (toℕ k)
genFB-on-inj k =
  trans (genFB-toℕ k (inj k))
        (trans (cong (swapℕ (toℕ k)) (toℕ-inj k)) (swapℕ-k (toℕ k)))

genFB-on-suc-pos : (k : Fin (suc n))
                 → toℕ (genFB k P.⟨$⟩ʳ suc-pos k) ≡ toℕ k
genFB-on-suc-pos k =
  trans (genFB-toℕ k (suc-pos k))
        (trans (cong (swapℕ (toℕ k)) (toℕ-suc-pos k)) (swapℕ-sk (toℕ k)))

-- Fixing at a value `z` with `toℕ z` outside `{toℕ k, suc (toℕ k)}`.
genFB-fix-val : (k : Fin (suc n)) (z : Fin (suc (suc n)))
              → toℕ z ≢ toℕ k → toℕ z ≢ suc (toℕ k)
              → toℕ (genFB k P.⟨$⟩ʳ z) ≡ toℕ z
genFB-fix-val k z h₁ h₂ =
  trans (genFB-toℕ k z) (swapℕ-fix-val (toℕ k) (toℕ z) h₁ h₂)

------------------------------------------------------------------------
-- The position characterization of `descent`:
--   descent i b  ⟺  toℕ (b ⟨$⟩ˡ suc-pos i) < toℕ (b ⟨$⟩ˡ inj i)
-- i.e. `i` is a left descent exactly when value `i+1` sits at an earlier
-- position than value `i`.  Both directions come from `invS-dichotomy`.

posᵢ : (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n))) → ℕ
posᵢ i b = toℕ (b P.⟨$⟩ˡ inj i)

posᵢ₊₁ : (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n))) → ℕ
posᵢ₊₁ i b = toℕ (b P.⟨$⟩ˡ suc-pos i)

-- (⇐) The position inequality gives a descent.
pos→descent : (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n)))
            → posᵢ₊₁ i b < posᵢ i b → descent i b
pos→descent i b lt =
  trans (cong suc (sym (invS≡inv (genFB i ∘-fb b))))
        (trans (proj₂ (invS-dichotomy i b) lt) (invS≡inv b))

-- (⇒) A descent gives the position inequality.  The equality and ascent
-- branches are impossible (injectivity of `b ⟨$⟩ˡ`; count can't both rise
-- and fall).
descent→pos : (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n)))
            → descent i b → posᵢ₊₁ i b < posᵢ i b
descent→pos i b dsc with <-cmp (posᵢ i b) (posᵢ₊₁ i b)
... | tri< asc _ _ =
  ⊥-elim (2+n≢n (inv b) (trans (sym (cong suc up)) dsc))
  where
  up : inv (genFB i ∘-fb b) ≡ suc (inv b)
  up = trans (sym (invS≡inv (genFB i ∘-fb b)))
             (trans (proj₁ (invS-dichotomy i b) asc) (cong suc (invS≡inv b)))
... | tri≈ _ eq _ = ⊥-elim (inj≢suc (⟨$⟩ˡ-inj (toℕ-injective eq)))
  where
  ⟨$⟩ˡ-inj : b P.⟨$⟩ˡ inj i ≡ b P.⟨$⟩ˡ suc-pos i → inj i ≡ suc-pos i
  ⟨$⟩ˡ-inj e =
    trans (sym (P.inverseʳ b)) (trans (cong (b P.⟨$⟩ʳ_) e) (P.inverseʳ b))
  inj≢suc : ¬ (inj i ≡ suc-pos i)
  inj≢suc e =
    1+n≢n (sym (trans (sym (toℕ-inj i)) (trans (cong toℕ e) (toℕ-suc-pos i))))
... | tri> _ _ gt = gt

------------------------------------------------------------------------
-- `Reduced` of a one-letter-shorter `~ʷ`-witness: if `w` is reduced and
-- `i` is a left descent, any `w′` with `(i ∷ w′) ~ʷ w` and
-- `suc (length w′) ≡ length w` is itself reduced.

reduced-of-witness :
    {w w′ : Word (suc n)} {i : Fin (suc n)}
  → Reduced w → descent i (evalW w)
  → suc (length w′) ≡ length w → (i ∷ w′) ~ʷ w
  → Reduced w′
reduced-of-witness {w = w} {w′} {i} red dsc lenEq rel =
  sym (suc-injective
        (trans (cong suc invw′≡invigb)
               (trans dsc (trans (sym red) (sym lenEq)))))
  where
  evalw≈ : evalW (i ∷ w′) ≈-fb evalW w
  evalw≈ = ~ʷ⇒≈ rel
  evalw′≈ : evalW w′ ≈-fb (genFB i ∘-fb evalW w)
  evalw′≈ p =
    trans (sym (genFB-involutive i (evalW w′ P.⟨$⟩ʳ p)))
          (cong (genFB i P.⟨$⟩ʳ_) (evalw≈ p))
  invw′≡invigb : inv (evalW w′) ≡ inv (genFB i ∘-fb evalW w)
  invw′≡invigb = inv-resp-≈ {b = evalW w′} {b′ = genFB i ∘-fb evalW w} evalw′≈

-- From `(i ∷ u) ~ʷ rest` we get `evalW u ≈-fb genFB i ∘-fb evalW rest`
-- (apply `genFB i` to both sides of `genFB i ∘-fb evalW u ≈ evalW rest`).
evalW-tail≈ : {i : Fin (suc n)} {u rest : Word (suc n)}
            → (i ∷ u) ~ʷ rest
            → evalW u ≈-fb (genFB i ∘-fb evalW rest)
evalW-tail≈ {i = i} {u} {rest} rel p =
  trans (sym (genFB-involutive i (evalW u P.⟨$⟩ʳ p)))
        (cong (genFB i P.⟨$⟩ʳ_) (~ʷ⇒≈ rel p))

------------------------------------------------------------------------
-- Every pair of distinct generators is `Far` or `Adj`, decided
-- structurally (deeper pairs recurse under `farS`/`adjS`).

data FarAdj {n : ℕ} (i j : Fin n) : Set where
  is-far-ij : Far i j → FarAdj i j
  is-far-ji : Far j i → FarAdj i j
  is-adj-ij : Adj i j → FarAdj i j
  is-adj-ji : Adj j i → FarAdj i j

fsuc-FarAdj : {i j : Fin n} → FarAdj i j → FarAdj (fsuc i) (fsuc j)
fsuc-FarAdj (is-far-ij f) = is-far-ij (farS f)
fsuc-FarAdj (is-far-ji f) = is-far-ji (farS f)
fsuc-FarAdj (is-adj-ij a) = is-adj-ij (adjS a)
fsuc-FarAdj (is-adj-ji a) = is-adj-ji (adjS a)

decide-FA : (i j : Fin (suc (suc n))) → i ≢ j → FarAdj i j
decide-FA 0F             0F             i≢j = ⊥-elim (i≢j refl)
decide-FA 0F             (fsuc 0F)      _   = is-adj-ij adj0
decide-FA 0F             (fsuc (fsuc j)) _  = is-far-ij far0ˡ
decide-FA (fsuc 0F)      0F             _   = is-adj-ji adj0
decide-FA (fsuc (fsuc i)) 0F            _   = is-far-ij far0ʳ
decide-FA {zero}  (fsuc 0F) (fsuc 0F) i≢j = ⊥-elim (i≢j refl)
decide-FA {suc n} (fsuc i) (fsuc j) i≢j =
  fsuc-FarAdj (decide-FA i j (λ e → i≢j (cong fsuc e)))

-- Over `Fin (suc n)`: distinct elements need `suc n ≥ 2`, so `n = suc _`.
decide-FA1 : (i j : Fin (suc n)) → i ≢ j → FarAdj i j
decide-FA1 {zero}  0F       0F       i≢j = ⊥-elim (i≢j refl)
decide-FA1 {suc n} i        j        i≢j = decide-FA i j i≢j

------------------------------------------------------------------------
-- `Far` gives a `toℕ`-gap of ≥ 2, so `genFB j` fixes both value-positions
-- `inj i` and `suc-pos i`.

Far→gap : {m : ℕ} {i j : Fin m} → Far i j
        → (suc (toℕ i) < toℕ j) ⊎ (suc (toℕ j) < toℕ i)
Far→gap (far0ˡ {j = j}) = inj₁ (s<s (s≤s z≤n))
Far→gap (far0ʳ {j = j}) = inj₂ (s<s (s≤s z≤n))
Far→gap (farS f) with Far→gap f
... | inj₁ lt = inj₁ (s<s lt)
... | inj₂ gt = inj₂ (s<s gt)

private
  <⇒≢ : {a b : ℕ} → a < b → a ≢ b
  <⇒≢ a<b refl = <-irrefl refl a<b

  >⇒≢ : {a b : ℕ} → a < b → b ≢ a
  >⇒≢ a<b e = <⇒≢ a<b (sym e)

  a<sa : (a : ℕ) → a < suc a
  a<sa a = s≤s (≤-of a)
    where
    ≤-of : (a : ℕ) → a ≤ a
    ≤-of zero    = z≤n
    ≤-of (suc a) = s≤s (≤-of a)

Gap : (i j : Fin (suc n)) → Set
Gap i j = (suc (toℕ i) < toℕ j) ⊎ (suc (toℕ j) < toℕ i)

-- The four disequalities the fixing lemma needs, derived from a gap.
private
  gap-a≢b : {i j : Fin (suc n)} → Gap i j → toℕ i ≢ toℕ j
  gap-a≢b {i = i} {j} (inj₁ lt) = <⇒≢ (<-trans (a<sa (toℕ i)) lt)
  gap-a≢b {i = i} {j} (inj₂ gt) = >⇒≢ (<-trans (a<sa (toℕ j)) gt)

  gap-a≢sb : {i j : Fin (suc n)} → Gap i j → toℕ i ≢ suc (toℕ j)
  gap-a≢sb {i = i} {j} (inj₁ lt) =
    <⇒≢ (<-trans (a<sa (toℕ i)) (<-trans lt (a<sa (toℕ j))))
  gap-a≢sb {i = i} {j} (inj₂ gt) = >⇒≢ gt

  gap-sa≢b : {i j : Fin (suc n)} → Gap i j → suc (toℕ i) ≢ toℕ j
  gap-sa≢b {i = i} {j} (inj₁ lt) = <⇒≢ lt
  gap-sa≢b {i = i} {j} (inj₂ gt) =
    >⇒≢ (<-trans (a<sa (toℕ j)) (<-trans gt (a<sa (toℕ i))))

  gap-sa≢sb : {i j : Fin (suc n)} → Gap i j → suc (toℕ i) ≢ suc (toℕ j)
  gap-sa≢sb {i = i} {j} (inj₁ lt) = <⇒≢ (<-trans lt (a<sa (toℕ j)))
  gap-sa≢sb {i = i} {j} (inj₂ gt) = >⇒≢ (<-trans gt (a<sa (toℕ i)))

-- `genFB j` fixes the value `inj i` (`toℕ ≡ toℕ i`).
genFB-fixes-inj : {i j : Fin (suc n)} → Gap i j
                → toℕ (genFB j P.⟨$⟩ʳ inj i) ≡ toℕ (inj i)
genFB-fixes-inj {i = i} {j} g =
  genFB-fix-val j (inj i)
    (subst (λ z → z ≢ toℕ j)       (sym (toℕ-inj i)) (gap-a≢b g))
    (subst (λ z → z ≢ suc (toℕ j)) (sym (toℕ-inj i)) (gap-a≢sb g))

-- `genFB j` fixes the value `suc-pos i` (`toℕ ≡ suc (toℕ i)`).
genFB-fixes-suc-pos : {i j : Fin (suc n)} → Gap i j
                    → toℕ (genFB j P.⟨$⟩ʳ suc-pos i) ≡ toℕ (suc-pos i)
genFB-fixes-suc-pos {i = i} {j} g =
  genFB-fix-val j (suc-pos i)
    (subst (λ z → z ≢ toℕ j)       (sym (toℕ-suc-pos i)) (gap-sa≢b g))
    (subst (λ z → z ≢ suc (toℕ j)) (sym (toℕ-suc-pos i)) (gap-sa≢sb g))

------------------------------------------------------------------------
-- Descent transfer for the `Far` case: `genFB j` does not move `i`'s
-- value-positions, so `descent i (genFB j ∘-fb b) → descent i b`.

genFB-ˡ-fixes-inj : {i j : Fin (suc n)} → Gap i j
                  → genFB j P.⟨$⟩ˡ inj i ≡ inj i
genFB-ˡ-fixes-inj {i = i} {j} g =
  trans (genFB-ˡ≡ʳ j (inj i)) (toℕ-injective (genFB-fixes-inj g))

genFB-ˡ-fixes-suc-pos : {i j : Fin (suc n)} → Gap i j
                      → genFB j P.⟨$⟩ˡ suc-pos i ≡ suc-pos i
genFB-ˡ-fixes-suc-pos {i = i} {j} g =
  trans (genFB-ˡ≡ʳ j (suc-pos i)) (toℕ-injective (genFB-fixes-suc-pos g))

descent-far : {i j : Fin (suc n)} {b : FinBij (suc (suc n)) (suc (suc n))}
            → Gap i j → descent i (genFB j ∘-fb b) → descent i b
descent-far {i = i} {j} {b} g dsc =
  pos→descent i b (subst₂ _<_ posᵢ₊₁-eq posᵢ-eq (descent→pos i (genFB j ∘-fb b) dsc))
  where
  posᵢ-eq : posᵢ i (genFB j ∘-fb b) ≡ posᵢ i b
  posᵢ-eq = cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (genFB-ˡ-fixes-inj g)
  posᵢ₊₁-eq : posᵢ₊₁ i (genFB j ∘-fb b) ≡ posᵢ₊₁ i b
  posᵢ₊₁-eq = cong (λ z → toℕ (b P.⟨$⟩ˡ z)) (genFB-ˡ-fixes-suc-pos g)

------------------------------------------------------------------------
-- Suffix-reducedness and the head-descent fact.  (`inv (evalW w) ≤
-- length w` is `ExchangeBase.inv≤length`.)

-- A suffix of a reduced word is reduced.
Reduced-tail : {j : Fin (suc n)} {rest : Word (suc n)}
             → Reduced (j ∷ rest) → Reduced rest
Reduced-tail {j = j} {rest} red with inv-di j (evalW rest)
... | inj₁ up = suc-injective (trans red up)
... | inj₂ dsc =
  ⊥-elim (1+n≰n (≤-trans bound (inv≤length rest)))
  where
  inv-b≡ : inv (evalW rest) ≡ suc (suc (length rest))
  inv-b≡ = trans (sym dsc) (sym (cong suc red))
  bound : suc (length rest) ≤ inv (evalW rest)
  bound = subst (suc (length rest) ≤_) (sym inv-b≡) (n≤1+n (suc (length rest)))

-- The head of a reduced word is a left descent.
head-descent : {j : Fin (suc n)} {rest : Word (suc n)}
             → Reduced (j ∷ rest) → descent j (evalW (j ∷ rest))
head-descent {j = j} {rest} red =
  trans (cong suc inv-jjb≡invb)
        (trans (cong suc (sym (Reduced-tail {j = j} {rest = rest} red))) red)
  where
  inv-jjb≡invb : inv (genFB j ∘-fb (genFB j ∘-fb evalW rest)) ≡ inv (evalW rest)
  inv-jjb≡invb =
    inv-resp-≈ {b = genFB j ∘-fb (genFB j ∘-fb evalW rest)} {b′ = evalW rest}
      (λ p → genFB-involutive j (evalW rest P.⟨$⟩ʳ p))

------------------------------------------------------------------------
-- `Adj` gives a `toℕ`-step of one.

Adj→suc : {m : ℕ} {j i : Fin m} → Adj j i → toℕ i ≡ suc (toℕ j)
Adj→suc adj0     = refl
Adj→suc (adjS a) = cong suc (Adj→suc a)

-- The backward action on `toℕ`.
genFB-ˡ-toℕ : (k : Fin (suc n)) (v : Fin (suc (suc n)))
            → toℕ (genFB k P.⟨$⟩ˡ v) ≡ swapℕ (toℕ k) (toℕ v)
genFB-ˡ-toℕ k v = trans (cong toℕ (genFB-ˡ≡ʳ k v)) (genFB-toℕ k v)

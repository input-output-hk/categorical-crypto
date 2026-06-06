{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- An explicit *word* model for finite permutations: sequences of
-- adjacent-transposition generators (Coxeter generators of `Sₙ`).
--
-- Deliberately PARAMETER-FREE: it lives entirely over `Fin`/`ℕ` and
-- `FinBij`, with no reference to `FreeMonoidalData`.  That sidesteps the
-- phantom-instance issue of the `↭`-indexed development and isolates the
-- combinatorial kernel — the symmetric-group word problem.
--
-- Indexing convention.  A `Word n` is a list of generator indices
-- (`Fin n`) acting on positions `Fin (suc n)`; generator `i` swaps the
-- adjacent positions `i, suc i`.  A word evaluates by RIGHT-TO-LEFT
-- composition, so `evalW (g ∷ w) = genFB g ∘-fb evalW w` (the HEAD
-- generator is applied LAST) — the `Transposition.List.eval` convention.
--
-- See `docs/word-model.typ` for the design rationale.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Word where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀; remove)

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; trans; subst)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Soundness as Snd
-- `residual-pw-cong`: `remove 0F` respects pointwise (`≈-fb`) equality.
open import Categories.PermuteCoherence.CanonicalProps using (residual-pw-cong)

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- 1. Generators.

-- `genFB i : FinBij (suc n) (suc n)` is the adjacent transposition that
-- swaps positions `i, suc i` of `Fin (suc n)`.

genFB : {n : ℕ} → Fin n → FinBij (suc n) (suc n)
genFB {suc n} 0F       = swap-fb n
genFB {suc n} (fsuc j) = cons-fb (genFB j)

------------------------------------------------------------------------
-- 2. Words and their evaluation.

Word : ℕ → Set
Word n = List (Fin n)

evalW : Word n → FinBij (suc n) (suc n)
evalW []      = id-fb
evalW (i ∷ w) = genFB i ∘-fb evalW w

------------------------------------------------------------------------
-- 3. Pointwise-congruence helpers for `_∘-fb_` and `cons-fb`.

∘-fb-cong : {g g′ : FinBij m k} {f f′ : FinBij n m} →
            g ≈-fb g′ → f ≈-fb f′ → (g ∘-fb f) ≈-fb (g′ ∘-fb f′)
∘-fb-cong {g = g} {g′} {f} {f′} g≈ f≈ i
  rewrite f≈ i = g≈ (f′ P.⟨$⟩ʳ i)

cons-fb-cong : {f f′ : FinBij n m} →
               f ≈-fb f′ → cons-fb f ≈-fb cons-fb f′
cons-fb-cong eq 0F       = refl
cons-fb-cong eq (fsuc i) = cong fsuc (eq i)

-- Associativity of `_∘-fb_` (definitional).
∘-fb-assoc : ∀ {p} (h : FinBij m k) (g : FinBij n m) (f : FinBij p n) →
             ((h ∘-fb g) ∘-fb f) ≈-fb (h ∘-fb (g ∘-fb f))
∘-fb-assoc h g f _ = refl

-- Left/right unit.
∘-fb-idˡ : (f : FinBij n m) → (id-fb ∘-fb f) ≈-fb f
∘-fb-idˡ f _ = refl

∘-fb-idʳ : (f : FinBij n m) → (f ∘-fb id-fb) ≈-fb f
∘-fb-idʳ f _ = refl

genFB-cong : {n : ℕ} {i j : Fin n} → i ≡ j → genFB i ≈-fb genFB j
genFB-cong refl _ = refl

------------------------------------------------------------------------
-- 4. The concatenation homomorphism and lifting.

-- `evalW` is a monoid homomorphism (Word, ++) → (FinBij, ∘-fb).
evalW-++ : (v w : Word n) → evalW (v ++ w) ≈-fb (evalW v ∘-fb evalW w)
evalW-++ []      w i = refl
evalW-++ (g ∷ v) w i = cong (genFB g P.⟨$⟩ʳ_) (evalW-++ v w i)

-- Lift every generator one level (`i ↦ suc i`); acts on the tail.
liftW : Word n → Word (suc n)
liftW []      = []
liftW (i ∷ w) = fsuc i ∷ liftW w

-- `evalW (liftW w) ≈ cons-fb (evalW w)`.
eval-liftW : (w : Word n) → evalW (liftW w) ≈-fb cons-fb (evalW w)
eval-liftW []      0F       = refl
eval-liftW []      (fsuc i) = refl
eval-liftW (g ∷ w) i =
  trans (cong (cons-fb (genFB g) P.⟨$⟩ʳ_) (eval-liftW w i))
        (sym (Snd.cons-fb-functor-comp (genFB g) (evalW w) i))

------------------------------------------------------------------------
-- 5. The head-bubbling rotation (the cycle `ρ_m`).
--
-- `rotate-fb m` is the finite bijection that brings position `m` to the
-- front: `rotate-fb m ⟨$⟩ʳ m ≡ 0`, while `0,…,m-1` each shift up by one.
-- It is the cycle `(m  m-1  …  1  0)` written as a product of adjacent
-- transpositions.

rotate-fb : {n : ℕ} → Fin (suc n) → FinBij (suc n) (suc n)
rotate-fb {n}     0F       = id-fb
rotate-fb {suc n} (fsuc m) = swap-fb n ∘-fb cons-fb (rotate-fb m)

-- The word realising the rotation.
rotateW : {n : ℕ} → Fin (suc n) → Word n
rotateW {n}     0F       = []
rotateW {suc n} (fsuc m) = 0F ∷ liftW (rotateW m)

-- `rotateW` realises `rotate-fb`.
rotateW-sound : {n : ℕ} (m : Fin (suc n)) → evalW (rotateW m) ≈-fb rotate-fb m
rotateW-sound {n}     0F       i = refl
rotateW-sound {suc n} (fsuc m) i =
  ∘-fb-cong {g = swap-fb n} {g′ = swap-fb n}
            {f = evalW (liftW (rotateW m))} {f′ = cons-fb (rotate-fb m)}
            (λ _ → refl)
            (λ j → trans (eval-liftW (rotateW m) j)
                         (cons-fb-cong (rotateW-sound m) j))
            i

-- The defining property: the rotation brings `m` to the front.
rotate-fb-front : {n : ℕ} (m : Fin (suc n)) → rotate-fb m P.⟨$⟩ʳ m ≡ 0F
rotate-fb-front {n}     0F       = refl
rotate-fb-front {suc n} (fsuc m) =
  trans (cong (λ z → swap-fb n P.⟨$⟩ʳ fsuc z) (rotate-fb-front m)) refl

-- The inverse rotation sends `0F` back to `m`.
inv-rotate-fb-0 : {n : ℕ} (m : Fin (suc n)) → inv-fb (rotate-fb m) P.⟨$⟩ʳ 0F ≡ m
inv-rotate-fb-0 m =
  trans (cong (rotate-fb m P.⟨$⟩ˡ_) (sym (rotate-fb-front m)))
        (P.inverseˡ (rotate-fb m))

------------------------------------------------------------------------
-- 6. The bubble-sort canonical word `canonW` and its soundness.
--
-- `canonW b` is the canonical/normal word for the bijection `b`,
-- obtained by repeatedly bubbling the element destined for the front
-- (position `m = b ⟨$⟩ˡ 0F`) to position 0 with the rotation word, then
-- recursing on the residual.  This mirrors stdlib's
-- `Data.Fin.Permutation.Transposition.List.decompose`, but with the
-- single head transposition replaced by an adjacent-swap rotation, so
-- the result is a genuine Coxeter word.

canonW : {n : ℕ} → FinBij (suc n) (suc n) → Word n
canonW {zero}  b = []
canonW {suc n} b =
  let m    = b P.⟨$⟩ˡ 0F
      rest = remove 0F (b ∘-fb inv-fb (rotate-fb m))
  in liftW (canonW rest) ++ rotateW m

-- Every element of `Fin 1` is `0F`.
fin1-unique : (j : Fin 1) → j ≡ 0F
fin1-unique 0F = refl

-- Roundtrip soundness:  `evalW (canonW b) ≈-fb b`.
eval-canonW : {n : ℕ} (b : FinBij (suc n) (suc n)) → evalW (canonW b) ≈-fb b
eval-canonW {zero}  b 0F = sym (fin1-unique (b P.⟨$⟩ʳ 0F))
eval-canonW {suc n} b i =
  let m    = b P.⟨$⟩ˡ 0F
      ρ    = rotate-fb m
      bρ⁻¹ = b ∘-fb inv-fb ρ
      rest = remove 0F bρ⁻¹

      -- The fixing condition for `lift₀-remove`: `bρ⁻¹ ⟨$⟩ʳ 0F ≡ 0F`.
      fix0 : bρ⁻¹ P.⟨$⟩ʳ 0F ≡ 0F
      fix0 = trans (cong (b P.⟨$⟩ʳ_) (inv-rotate-fb-0 m)) (P.inverseʳ b)

      -- A: factor `evalW (canonW b)` over `_++_` (`evalW-++`).
      stepA : evalW (canonW b) P.⟨$⟩ʳ i
            ≡ (evalW (liftW (canonW rest)) ∘-fb evalW (rotateW m)) P.⟨$⟩ʳ i
      stepA = evalW-++ (liftW (canonW rest)) (rotateW m) i

      -- B: rewrite both inner factors by their soundness lemmas
      -- (`rotateW-sound`, `eval-liftW` + IH).
      stepB : (evalW (liftW (canonW rest)) ∘-fb evalW (rotateW m)) P.⟨$⟩ʳ i
            ≡ (cons-fb rest ∘-fb ρ) P.⟨$⟩ʳ i
      stepB =
        ∘-fb-cong
          {g = evalW (liftW (canonW rest))} {g′ = cons-fb rest}
          {f = evalW (rotateW m)}           {f′ = ρ}
          (λ j → trans (eval-liftW (canonW rest) j)
                       (cons-fb-cong (eval-canonW rest) j))
          (rotateW-sound m)
          i

      -- C: collapse `cons-fb rest ≈ bρ⁻¹` via `lift₀-remove fix0`.
      stepC : (cons-fb rest ∘-fb ρ) P.⟨$⟩ʳ i ≡ (bρ⁻¹ ∘-fb ρ) P.⟨$⟩ʳ i
      stepC = ∘-fb-cong
                {g = cons-fb rest} {g′ = bρ⁻¹}
                {f = ρ} {f′ = ρ}
                (P.lift₀-remove bρ⁻¹ fix0)
                (λ _ → refl)
                i

      -- D: cancel `inv-fb ρ ∘ ρ = id`.
      stepD : (bρ⁻¹ ∘-fb ρ) P.⟨$⟩ʳ i ≡ b P.⟨$⟩ʳ i
      stepD = cong (b P.⟨$⟩ʳ_) (P.inverseˡ ρ)
  in trans stepA (trans stepB (trans stepC stepD))

------------------------------------------------------------------------
-- 7. The word equivalence `_~ʷ_` (the Coxeter relations on words).
--
-- `_~ʷ_` is the least congruence on words generated by the three Coxeter
-- relations of `Sₙ`, presented AT THE FRONT only and propagated to
-- arbitrary depth by the `lift~` congruence (so the generator set is
-- minimal).  This is the word-level shadow of `_≅↭ⁱ_`.
--
--   * `c1` involution (σ² = id), `c2` far-commutativity (|i−j| ≥ 2),
--     `c3` braid (Yang–Baxter).
--
-- Soundness (`~ʷ⇒≈`) is proved below from the corresponding three
-- `Soundness.agda` identities.

-- `Far i j` witnesses that generators `i` and `j` act on disjoint
-- position pairs (`|i − j| ≥ 2`), so they commute.  It is structural,
-- hence trivially closed under simultaneous `fsuc` (the `farS` rule),
-- which is what makes `_~ʷ_` closed under `lift~`.
data Far : {n : ℕ} → Fin n → Fin n → Set where
  far0ˡ : {n : ℕ} {j : Fin n} → Far {suc (suc n)} 0F (fsuc (fsuc j))
  far0ʳ : {n : ℕ} {j : Fin n} → Far {suc (suc n)} (fsuc (fsuc j)) 0F
  farS  : {n : ℕ} {i j : Fin n} → Far i j → Far (fsuc i) (fsuc j)

-- `Adj i k` witnesses that `k` is the generator immediately above `i`
-- (`k = i + 1`), so the braid relation applies to the triple `i k i`.
data Adj : {n : ℕ} → Fin n → Fin n → Set where
  adj0 : {n : ℕ} → Adj {suc (suc n)} 0F (fsuc 0F)
  adjS : {n : ℕ} {i k : Fin n} → Adj i k → Adj (fsuc i) (fsuc k)

infix 4 _~ʷ_

data _~ʷ_ : {n : ℕ} → Word n → Word n → Set where

  ~refl  : {n : ℕ} {w : Word n} → w ~ʷ w
  ~sym   : {n : ℕ} {v w : Word n} → v ~ʷ w → w ~ʷ v
  ~trans : {n : ℕ} {u v w : Word n} → u ~ʷ v → v ~ʷ w → u ~ʷ w

  -- congruence under `_∷_`, with an index equation (doubles as a
  -- generator-index rewrite).
  ∷c   : {n : ℕ} {i j : Fin n} {v w : Word n}
       → i ≡ j → v ~ʷ w → (i ∷ v) ~ʷ (j ∷ w)

  -- (C1) involution at any position.
  c1 : {n : ℕ} (i : Fin n) {w : Word n} → (i ∷ i ∷ w) ~ʷ w

  -- (C2) far-commutativity.
  c2 : {n : ℕ} {i j : Fin n} {w : Word n}
     → Far i j → (i ∷ j ∷ w) ~ʷ (j ∷ i ∷ w)

  -- (C3) braid (Yang–Baxter).
  c3 : {n : ℕ} {i k : Fin n} {w : Word n}
     → Adj i k → (i ∷ k ∷ i ∷ w) ~ʷ (k ∷ i ∷ k ∷ w)

------------------------------------------------------------------------
-- 8. Derived congruences for `_~ʷ_`.

-- Plain cons-congruence (same head index).
∷-cong : {n : ℕ} (i : Fin n) {v w : Word n} → v ~ʷ w → (i ∷ v) ~ʷ (i ∷ w)
∷-cong i = ∷c refl

-- Lift congruence `v ~ʷ w ⇒ liftW v ~ʷ liftW w` — the engine that
-- propagates the front-only `c2`/`c3` to all depths.
lift~ : {n : ℕ} {v w : Word n} → v ~ʷ w → liftW v ~ʷ liftW w
lift~ ~refl          = ~refl
lift~ (~sym r)       = ~sym (lift~ r)
lift~ (~trans r₁ r₂) = ~trans (lift~ r₁) (lift~ r₂)
lift~ (∷c eq r)      = ∷c (cong fsuc eq) (lift~ r)
lift~ (c1 i)         = c1 (fsuc i)
lift~ (c2 far)       = c2 (farS far)
lift~ (c3 adj)       = c3 (adjS adj)

-- Right-concatenation congruence:  v ~ʷ v′ ⇒ v ++ w ~ʷ v′ ++ w.
++c-r : {n : ℕ} {v v′ : Word n} (w : Word n) → v ~ʷ v′ → (v ++ w) ~ʷ (v′ ++ w)
++c-r w ~refl          = ~refl
++c-r w (~sym r)       = ~sym (++c-r w r)
++c-r w (~trans r₁ r₂) = ~trans (++c-r w r₁) (++c-r w r₂)
++c-r w (∷c eq r)      = ∷c eq (++c-r w r)
++c-r w (c1 i)         = c1 i
++c-r w (c2 far)       = c2 far
++c-r w (c3 adj)       = c3 adj

------------------------------------------------------------------------
-- 9. Soundness of `_~ʷ_`: it is `evalW`-preserving.  Each Coxeter
-- generator follows from the corresponding `Soundness.agda` identity,
-- lifted to its position by induction through the `cons-fb` functor laws.

-- (C1) involution at any position:  genFB i ∘-fb genFB i ≈ id-fb.
genFB-involutive : {n : ℕ} (i : Fin n) → (genFB i ∘-fb genFB i) ≈-fb id-fb
genFB-involutive {suc n} 0F       = Snd.swap-fb-involutive
genFB-involutive {suc n} (fsuc j) =
  λ p → trans (sym (Snd.cons-fb-functor-comp (genFB j) (genFB j) p))
        (trans (cons-fb-cong (genFB-involutive j) p)
               (Snd.cons-fb-functor-id p))

genFB∘genFB : {n : ℕ} (i : Fin n) (x : FinBij (suc n) (suc n))
            → (genFB i ∘-fb (genFB i ∘-fb x)) ≈-fb x
genFB∘genFB i x j = genFB-involutive i (x P.⟨$⟩ʳ j)

-- `genFB i` is left-cancellable.
genFB-cancelˡ : {n : ℕ} (i : Fin n) {b b′ : FinBij (suc n) (suc n)}
              → (genFB i ∘-fb b) ≈-fb (genFB i ∘-fb b′) → b ≈-fb b′
genFB-cancelˡ i {b} {b′} h j =
  trans (sym (genFB-involutive i (b P.⟨$⟩ʳ j)))
        (trans (cong (genFB i P.⟨$⟩ʳ_) (h j))
               (genFB-involutive i (b′ P.⟨$⟩ʳ j)))

-- (C2) far generators commute.
genFB-far : {n : ℕ} {i j : Fin n} → Far i j
          → (genFB i ∘-fb genFB j) ≈-fb (genFB j ∘-fb genFB i)
genFB-far (far0ˡ {j = j}) = Snd.swap-fb-natural (genFB j)
genFB-far (far0ʳ {j = j}) = λ p → sym (Snd.swap-fb-natural (genFB j) p)
genFB-far (farS {i = i} {j = j} far) =
  λ p → trans (sym (Snd.cons-fb-functor-comp (genFB i) (genFB j) p))
        (trans (cons-fb-cong (genFB-far far) p)
               (Snd.cons-fb-functor-comp (genFB j) (genFB i) p))

-- (C3) the braid:  Adj i k ⇒ the two reduced words for ⟨gᵢ, gₖ⟩ agree.
genFB-braid : {n : ℕ} {i k : Fin n} → Adj i k
            → (genFB i ∘-fb genFB k ∘-fb genFB i)
              ≈-fb (genFB k ∘-fb genFB i ∘-fb genFB k)
genFB-braid (adj0 {n = n}) = Snd.yang-baxter
genFB-braid (adjS {i = i} {k = k} adj) =
  -- Push the `cons-fb` out of all three factors, apply the IH, push back.
  λ p → trans (push-out-lhs p)
        (trans (cons-fb-cong (genFB-braid adj) p)
               (sym (push-out-rhs p)))
  where
  push-out-lhs
    : (cons-fb (genFB i) ∘-fb cons-fb (genFB k) ∘-fb cons-fb (genFB i))
      ≈-fb cons-fb (genFB i ∘-fb genFB k ∘-fb genFB i)
  push-out-lhs p =
    trans (cong (cons-fb (genFB i) P.⟨$⟩ʳ_)
                (sym (Snd.cons-fb-functor-comp (genFB k) (genFB i) p)))
          (sym (Snd.cons-fb-functor-comp (genFB i) (genFB k ∘-fb genFB i) p))
  push-out-rhs
    : (cons-fb (genFB k) ∘-fb cons-fb (genFB i) ∘-fb cons-fb (genFB k))
      ≈-fb cons-fb (genFB k ∘-fb genFB i ∘-fb genFB k)
  push-out-rhs p =
    trans (cong (cons-fb (genFB k) P.⟨$⟩ʳ_)
                (sym (Snd.cons-fb-functor-comp (genFB i) (genFB k) p)))
          (sym (Snd.cons-fb-functor-comp (genFB k) (genFB i ∘-fb genFB k) p))

-- The soundness theorem:  related words evaluate to the same bijection.
~ʷ⇒≈ : {n : ℕ} {v w : Word n} → v ~ʷ w → evalW v ≈-fb evalW w
~ʷ⇒≈ ~refl          _ = refl
~ʷ⇒≈ (~sym r)       p = sym (~ʷ⇒≈ r p)
~ʷ⇒≈ (~trans r₁ r₂) p = trans (~ʷ⇒≈ r₁ p) (~ʷ⇒≈ r₂ p)
~ʷ⇒≈ (∷c {i = i} {j = j} {v = v} {w = w} eq r) =
  ∘-fb-cong {g = genFB i} {g′ = genFB j} {f = evalW v} {f′ = evalW w}
            (genFB-cong eq) (~ʷ⇒≈ r)
~ʷ⇒≈ (c1 i {w = w}) =
  ∘-fb-cong {g = genFB i ∘-fb genFB i} {g′ = id-fb}
            {f = evalW w} {f′ = evalW w}
            (genFB-involutive i) (λ _ → refl)
~ʷ⇒≈ (c2 {i = i} {j = j} {w = w} far) =
  ∘-fb-cong {g = genFB i ∘-fb genFB j} {g′ = genFB j ∘-fb genFB i}
            {f = evalW w} {f′ = evalW w}
            (genFB-far far) (λ _ → refl)
~ʷ⇒≈ (c3 {i = i} {k = k} {w = w} adj) =
  ∘-fb-cong {g = genFB i ∘-fb genFB k ∘-fb genFB i}
            {g′ = genFB k ∘-fb genFB i ∘-fb genFB k}
            {f = evalW w} {f′ = evalW w}
            (genFB-braid adj) (λ _ → refl)

------------------------------------------------------------------------
-- 10. The Insertion Lemma (the Sₙ word problem kernel) is `_~ʷ_`-derived
-- and proved as `InsertProof.insert-thm` (downstream of `Word`, via the
-- type-A exchange condition + Matsumoto).  `straightenW` lives there too,
-- as it is the only thing that needed `insert`.

------------------------------------------------------------------------
-- 11. `canonW` congruence + identity (straightening support).
--
-- `canonW` sends pointwise-equal bijections to `~ʷ`-equal words
-- (`canonW-resp-≈`, the word-model analogue of `nf-cong`).  Proved
-- directly into `_~ʷ_`, so no funext is needed.

-- `≈-fb` (about `_⟨$⟩ʳ_`) also equates `_⟨$⟩ˡ_`, since the backward map
-- is determined by the forward one.
≈ˡ : {N M : ℕ} {f g : FinBij N M} → f ≈-fb g → ∀ j → f P.⟨$⟩ˡ j ≡ g P.⟨$⟩ˡ j
≈ˡ {f = f} {g} eq j =
  trans (sym (P.inverseˡ g {f P.⟨$⟩ˡ j}))
        (cong (g P.⟨$⟩ˡ_) (trans (sym (eq (f P.⟨$⟩ˡ j))) (P.inverseʳ f {j})))

-- The head datum `b ⟨$⟩ˡ 0F` is matched by `≈ˡ`; the residual is `≈-fb`
-- by `residual-pw-cong`, so the recursive words are `~ʷ` (IH under
-- `lift~`), glued by `++c-r`.
canonW-resp-≈ : {n : ℕ} {b b′ : FinBij (suc n) (suc n)}
              → b ≈-fb b′ → canonW b ~ʷ canonW b′
canonW-resp-≈ {zero}      eq = ~refl
canonW-resp-≈ {suc n} {b} {b′} eq =
  subst (λ z → canonW b ~ʷ (liftW (canonW rest′) ++ rotateW z)) m≡
        (++c-r (rotateW (b P.⟨$⟩ˡ 0F)) (lift~ rec))
  where
  -- (`≈-fb` is non-injective, so implicit bijection arguments are pinned.)
  m≡ : b P.⟨$⟩ˡ 0F ≡ b′ P.⟨$⟩ˡ 0F
  m≡ = ≈ˡ {f = b} {g = b′} eq 0F

  restb rest′ : FinBij (suc n) (suc n)
  restb = remove 0F (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
  rest′ = remove 0F (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))

  rest≈ : restb ≈-fb rest′
  rest≈ = residual-pw-cong (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
                           (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))
            (∘-fb-cong {g = b} {g′ = b′}
                       {f = inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F))}
                       {f′ = inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F))}
                       eq (λ i → cong (λ z → inv-fb (rotate-fb z) P.⟨$⟩ʳ i) m≡))

  rec : canonW restb ~ʷ canonW rest′
  rec = canonW-resp-≈ {b = restb} {b′ = rest′} rest≈

-- `cons-fb` reflects the identity:  if `cons-fb f ≈ id-fb` then `f ≈ id-fb`.
cons-fb-reflects-id : {n : ℕ} {f : FinBij n n}
                    → cons-fb f ≈-fb id-fb → f ≈-fb id-fb
cons-fb-reflects-id {f = f} h j = suc-injective (h (fsuc j))
  where
  suc-injective : {a b : Fin _} → fsuc a ≡ fsuc b → a ≡ b
  suc-injective refl = refl

-- `remove 0F X ≈ id-fb` whenever `X ≈ id-fb`, via `lift₀-remove`.
remove-0-of-≈id : {n : ℕ} (X : FinBij (suc n) (suc n))
                → X ≈-fb id-fb → remove 0F X ≈-fb id-fb
remove-0-of-≈id X h =
  cons-fb-reflects-id (λ j → trans (P.lift₀-remove X (h 0F) j) (h j))

-- The canonical word of the identity is empty (up to `~ʷ`).
canonW-id : {n : ℕ} → canonW (id-fb {n = suc n}) ~ʷ []
canonW-id {zero}  = ~refl
canonW-id {suc n} =
  -- `m = id ⟨$⟩ˡ 0F = 0F` so `rotateW m = []`; the residual is `≈ id`,
  -- so `lift~` of (`canonW-resp-≈`; IH) collapses to `[]`.
  subst (_~ʷ []) (sym (++-identityʳ (liftW (canonW _))))
    (~trans (lift~ (canonW-resp-≈ {b = remove 0F (id-fb ∘-fb inv-fb id-fb)}
                                  {b′ = id-fb {n = suc n}}
                                  (remove-0-of-≈id (id-fb ∘-fb inv-fb id-fb) (λ _ → refl))))
            (lift~ canonW-id))

-- Straightening (every word is `~ʷ` its canonical form) needs the
-- Insertion Lemma, so it lives in `InsertProof` (`straightenW`).

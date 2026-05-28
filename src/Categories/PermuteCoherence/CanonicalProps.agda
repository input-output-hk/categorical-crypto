{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Propositional invariants of the canonical decoder
-- (`Canonical.canonical-go`) specialised at `id-fb`.
--
-- The blocker for closing the canonical-bridge refl case was that
-- `canonical-target xs id-fb` does NOT definitionally equal `xs`,
-- because stdlib's `P.id = ↔-id _` is opaque enough that `residual
-- id-fb` is not definitionally `id-fb` (only pointwise so).  Here we
-- prove the *propositional* invariant `canonical-target xs id-fb ≡ xs`
-- (and several supporting facts).  The proof uses
-- `canonical-go-suc-unfold` from `Canonical.agda` to expose the
-- with-block structure of `canonical-go` propositionally.
------------------------------------------------------------------------

module Categories.PermuteCoherence.CanonicalProps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀; remove)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- 1. Ground reductions: head-target / residual on `id-fb`.

head-target-id-fb : ∀ {n} → head-target {n} id-fb ≡ 0F
head-target-id-fb = refl

residual-id-fb : ∀ {n} → residual {n} id-fb ≈-fb id-fb
residual-id-fb i = refl

-- Pointwise: residual id-fb ⟨$⟩ʳ i ≡ i.
residual-id-fb-pw : ∀ {n} (i : Fin n) → (residual id-fb P.⟨$⟩ʳ i) ≡ i
residual-id-fb-pw i = refl

-- A residual chain: arbitrarily many `residual`s applied to `id-fb`
-- remain pointwise the identity.

------------------------------------------------------------------------
-- 2. cons-fb invariants.

head-target-cons-fb : ∀ {n} (b : FinBij n n) → head-target (cons-fb b) ≡ 0F
head-target-cons-fb _ = refl

residual-cons-fb : ∀ {n} (b : FinBij n n) → residual (cons-fb b) ≈-fb b
residual-cons-fb _ _ = refl

------------------------------------------------------------------------
-- 3. bubble-to-front at position 0F.

bubble-to-front-zero
  : ∀ (x : A) (xs : List A)
  → bubble-to-front {n = length xs} (x ∷ xs) refl 0F
    ≡ (xs , refl , Perm.refl)
bubble-to-front-zero x xs = refl

------------------------------------------------------------------------
-- 4. canonical-go on `id-fb` and arbitrary `residual^k id-fb`.
--
-- The key strengthened invariant: `canonical-go` returns `xs`
-- whenever its bijection argument is *pointwise* the identity.
--
-- We prove this by induction on the list, using the unfolding
-- equation `canonical-go-suc-unfold` (which is `refl`) to expose
-- the structure of `canonical-go` propositionally.  At each
-- step we need:
--   (a) `head-target b ≡ 0F`  -- follows from `b ≈-fb id-fb`.
--   (b) `bubble-to-front (x ∷ xs) refl 0F ≡ (xs , refl , refl)`
--   (c) `residual b ≈-fb id-fb`  -- follows from `b ≈-fb id-fb`
--                                  WHEN `b` is `id-fb` or a chain of
--                                  `residual`s thereof, since each
--                                  is *pointwise* identity (proved by
--                                  refl-level reduction).

-- Auxiliary congruence: bubble-to-front at a position depends only
-- on the position, not on the bijection (it does not see b).  But
-- the position is `head-target b`, which DOES depend on b.  We
-- bridge by propositional equality of `head-target`.

-- Pointwise-identity is preserved by `residual`.
--
-- This is the only fact about stdlib's `remove` we need: under
-- `c ⟨$⟩ʳ (suc i) ≡ suc i`, `remove 0F c ⟨$⟩ʳ i ≡ i`.
-- Postulating this would defeat the purpose; we prove it below
-- using stdlib's API.

open import Data.Fin.Properties using (suc-injective)

-- Pointwise-identity preservation under `residual`.
--
-- Proof via `P.lift₀-remove`: under `c ⟨$⟩ʳ 0F ≡ 0F`,
-- `lift₀ (remove 0F c) ≈ c`.  In particular at `suc i`:
--    lift₀ (residual c) ⟨$⟩ʳ (suc i)  ≡  c ⟨$⟩ʳ (suc i)  ≡  suc i.
-- But by def of `lift₀`, the lhs is `suc (residual c ⟨$⟩ʳ i)`.
-- Hence `suc (residual c ⟨$⟩ʳ i) ≡ suc i`, and by suc-injectivity
-- the result follows.

residual-pw-id
  : ∀ {m} (c : FinBij (suc m) (suc m))
  → (∀ i → c P.⟨$⟩ʳ i ≡ i)
  → ∀ i → residual c P.⟨$⟩ʳ i ≡ i
residual-pw-id c c-id i =
  suc-injective
    (trans (P.lift₀-remove c (c-id 0F) (suc i)) (c-id (suc i)))

-- The strengthened invariant: `canonical-go` returns `xs` whenever
-- its bijection argument is *pointwise* the identity.
canonical-go-pw-id
  : ∀ (n : ℕ) (ys : List A) (ys-len : length ys ≡ n)
    (b : FinBij n n) (b-id : ∀ i → b P.⟨$⟩ʳ i ≡ i)
  → proj₁ (canonical-go n ys ys-len b) ≡ ys
canonical-go-pw-id zero    []       _    _ _    = refl
canonical-go-pw-id zero    (_ ∷ _)  ()
canonical-go-pw-id (suc n) []       ()
canonical-go-pw-id (suc n) (y ∷ ys) refl b b-id =
  trans (canonical-go-suc-unfold y ys b) (goal-with-ht (head-target b) (b-id 0F))
  where
  goal-with-ht
    : ∀ (k : Fin (suc n)) (eq : k ≡ 0F)
    → lookup (y ∷ ys) k
        ∷ proj₁ (canonical-go n
                              (proj₁ (bubble-to-front (y ∷ ys) refl k))
                              (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                              (residual b))
      ≡ y ∷ ys
  goal-with-ht .0F refl =
    cong (y ∷_) (canonical-go-pw-id n ys refl (residual b) (residual-pw-id b b-id))

canonical-go-id-fb-target
  : ∀ (n : ℕ) (xs : List A) (xs-len : length xs ≡ n)
  → proj₁ (canonical-go n xs xs-len id-fb) ≡ xs
canonical-go-id-fb-target n xs xs-len =
  canonical-go-pw-id n xs xs-len id-fb (λ _ → refl)

------------------------------------------------------------------------
-- 5. Public lemma: `canonical-target xs id-fb ≡ xs`.

canonical-target-id-fb : ∀ (xs : List A) → canonical-target xs id-fb ≡ xs
canonical-target-id-fb xs = canonical-go-id-fb-target (length xs) xs refl

------------------------------------------------------------------------
-- 6. Pointwise-congruence: `canonical-go` agrees on pointwise-equal
-- bijections (target list).
--
-- This is needed for the prep case of the canonical bridge: at the
-- recursion we have `residual (cons-fb (eval-↭ p))` which is only
-- *pointwise* equal to `eval-↭ p` (not propositionally).

open import Data.Fin.Properties using (punchOut-cong)
open import Data.Fin.Base using (punchOut)

-- `punchOut` is congruent in BOTH the punching position `i` and the
-- punched-out argument `j` (stdlib provides only the `j` half).
private
  punchOut-cong-both
    : ∀ {n} (i i' j j' : Fin (suc n))
        (ei : i ≡ i') (ej : j ≡ j')
        (p : i ≢ j) (p' : i' ≢ j')
    → punchOut p ≡ punchOut p'
  punchOut-cong-both i .i j j' refl ej _ _ = punchOut-cong i ej

-- Pointwise equality is preserved by `residual`.
residual-pw-cong
  : ∀ {n} (b b' : FinBij (suc n) (suc n))
  → (∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → ∀ i → residual b P.⟨$⟩ʳ i ≡ residual b' P.⟨$⟩ʳ i
residual-pw-cong b b' eq i =
  punchOut-cong-both _ _ _ _ (eq 0F) (eq (suc i)) _ _

open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Properties using (n<1+n)
open import Level using (0ℓ)

-- Pointwise-congruence of `canonical-go .proj₁` (target list).
--
-- Structural recursion on `n` fails Agda's termination check because
-- the list argument at the recursive site (`proj₁ (bubble-to-front
-- ...)`) is not a subterm of the outer list, and the natural-number
-- argument's decrease is masked by the implicit substitution
-- `n := length ys` after the `refl` pattern.  We use well-founded
-- recursion on `n` instead.
private
  P-pw-cong : ∀ {a} (A : Set a) → ℕ → Set a
  P-pw-cong A n = ∀ (xs : List A) (xs-len : length xs ≡ n)
                    (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
                → proj₁ (canonical-go n xs xs-len b)
                  ≡ proj₁ (canonical-go n xs xs-len b')

  go-pw-cong
    : ∀ {a} (A : Set a) (n : ℕ)
    → (∀ {m} → m Data.Nat.Base.< n → P-pw-cong A m)
    → P-pw-cong A n
  go-pw-cong A zero    rec []       _    _ _  _ = refl
  go-pw-cong A zero    rec (_ ∷ _)  ()
  go-pw-cong A (suc n) rec []       ()
  go-pw-cong A (suc n) rec (y ∷ ys) refl b b' eq =
    trans (canonical-go-suc-unfold y ys b)
      (trans (cong-with-k (head-target b) (head-target b') (eq 0F))
             (sym (canonical-go-suc-unfold y ys b')))
    where
    cong-with-k
      : ∀ (k k' : Fin (suc n)) (ek : k ≡ k')
      → lookup (y ∷ ys) k
          ∷ proj₁ (canonical-go n
                    (proj₁ (bubble-to-front (y ∷ ys) refl k))
                    (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                    (residual b))
        ≡ lookup (y ∷ ys) k'
          ∷ proj₁ (canonical-go n
                    (proj₁ (bubble-to-front (y ∷ ys) refl k'))
                    (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k')))
                    (residual b'))
    cong-with-k k .k refl =
      cong (lookup (y ∷ ys) k ∷_)
           (rec {n} (n<1+n n)
              (proj₁ (bubble-to-front (y ∷ ys) refl k))
              (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
              (residual b) (residual b')
              (residual-pw-cong b b' eq))

canonical-go-pw-cong-target
  : ∀ (n : ℕ) (xs : List A) (xs-len : length xs ≡ n)
      (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → proj₁ (canonical-go n xs xs-len b)
    ≡ proj₁ (canonical-go n xs xs-len b')
canonical-go-pw-cong-target {A = A} = <-rec _ (go-pw-cong A)

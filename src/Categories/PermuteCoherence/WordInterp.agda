{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Interpreting `Word`s as `↭`-derivations  (the Word↔derivation bridge,
-- list-level layer).
--
-- `Categories.PermuteCoherence.Word` is a *position-level* model: words
-- in adjacent transpositions over `Fin`, with a Coxeter congruence
-- `_~ʷ_`.  To connect it to the `↭`/`≅↭ⁱ` world (where `complete`
-- lives) we interpret a word as an actual list permutation:
--
--   * `swapAt i`  swaps list positions `i, i+1` (identity if the list is
--     too short — a harmless junk case, never hit for valid lengths);
--   * `applyW w`  applies the whole word (tail first, matching `evalW`'s
--     right-to-left convention `evalW (i ∷ w) = genFB i ∘-fb evalW w`);
--   * `⟦ w ⟧↭ xs : xs ↭ applyW w xs`  is the derivation.
--
-- This module is `--without-K` and generic in the carrier `X`; it uses
-- NO `≅↭ⁱ` (that lives in `FaithfulnessInductive`, which imports this).
-- Here we establish the *list-level* facts: length preservation, and
-- the Coxeter relations C1 (involution) and C2 (far-commutativity) as
-- propositional equalities on the acted-upon list.  C3 (braid) is only
-- valid for lists of the matching length, so it is stated with a length
-- hypothesis.
------------------------------------------------------------------------

module Categories.PermuteCoherence.WordInterp {a} {X : Set a} where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Binary.PropositionalEquality using (subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (trans-assoc)

import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.Word
  using ( Word; Far; far0ˡ; far0ʳ; farS; Adj; adj0; adjS
        ; _~ʷ_; ~refl; ~sym; ~trans; ∷c; c1; c2; c3
        ; genFB; evalW; ∘-fb-cong; cons-fb-cong )

open import Categories.PermuteCoherence.FinBij
  using ( FinBij; _≈-fb_; _∘-fb_; id-fb; cons-fb; swap-fb )

open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Categories.PermuteCoherence.Soundness
  using ( cons-fb-functor-id )

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 1. The interpretation.

-- Swap list positions `i` and `i+1`.  Identity if the list is too short
-- for the requested position (junk; unreachable when `length xs ≡ suc n`).
swapAt : {n : ℕ} → Fin n → List X → List X
swapAt _        []              = []
swapAt 0F       (a ∷ [])        = a ∷ []
swapAt 0F       (a ∷ b ∷ rest)  = b ∷ a ∷ rest
swapAt (fsuc i) (a ∷ xs)        = a ∷ swapAt i xs

-- The single-generator derivation `xs ↭ swapAt i xs`.
swapAt-↭ : (i : Fin n) (xs : List X) → xs ↭ swapAt i xs
swapAt-↭ _        []              = Perm.refl
swapAt-↭ 0F       (a ∷ [])        = Perm.refl
swapAt-↭ 0F       (a ∷ b ∷ rest)  = Perm.swap a b Perm.refl
swapAt-↭ (fsuc i) (a ∷ xs)        = Perm.prep a (swapAt-↭ i xs)

swapAt-length : (i : Fin n) (xs : List X) → length (swapAt i xs) ≡ length xs
swapAt-length _        []              = refl
swapAt-length 0F       (a ∷ [])        = refl
swapAt-length 0F       (a ∷ b ∷ rest)  = refl
swapAt-length (fsuc i) (a ∷ xs)        = cong suc (swapAt-length i xs)

-- Apply a whole word.  Tail first (right-to-left), matching `evalW`.
applyW : Word n → List X → List X
applyW []      xs = xs
applyW (i ∷ w) xs = swapAt i (applyW w xs)

applyW-length : (w : Word n) (xs : List X) → length (applyW w xs) ≡ length xs
applyW-length []      xs = refl
applyW-length (i ∷ w) xs = trans (swapAt-length i (applyW w xs)) (applyW-length w xs)

-- The derivation interpreting a word.
⟦_⟧↭ : (w : Word n) (xs : List X) → xs ↭ applyW w xs
⟦ []    ⟧↭ xs = Perm.refl
⟦ i ∷ w ⟧↭ xs = Perm.trans (⟦ w ⟧↭ xs) (swapAt-↭ i (applyW w xs))

------------------------------------------------------------------------
-- 2. List-level Coxeter relations (propositional, on the acted list).

-- (C1) Involution — unconditional (junk cases are honestly identities).
swapAt-invol : (i : Fin n) (xs : List X) → swapAt i (swapAt i xs) ≡ xs
swapAt-invol _        []              = refl
swapAt-invol 0F       (a ∷ [])        = refl
swapAt-invol 0F       (a ∷ b ∷ rest)  = refl
swapAt-invol (fsuc i) (a ∷ xs)        = cong (a ∷_) (swapAt-invol i xs)

-- (C2) Far-commutativity — unconditional (the two swaps touch disjoint
-- positions, and short lists make both into the same junk identity).
swapAt-far : {i j : Fin n} → Far i j → (xs : List X)
           → swapAt i (swapAt j xs) ≡ swapAt j (swapAt i xs)
swapAt-far far0ˡ    []              = refl
swapAt-far far0ˡ    (a ∷ [])        = refl
swapAt-far far0ˡ    (a ∷ b ∷ rest)  = refl
swapAt-far far0ʳ    []              = refl
swapAt-far far0ʳ    (a ∷ [])        = refl
swapAt-far far0ʳ    (a ∷ b ∷ rest)  = refl
swapAt-far (farS f) []              = refl
swapAt-far (farS f) (a ∷ xs)        = cong (a ∷_) (swapAt-far f xs)

-- (C3) Braid (Yang–Baxter) — only valid when the list is long enough,
-- so it carries the matching-length hypothesis `length xs ≡ suc n`
-- (this rules out the short junk lists, on which the braid would fail).
swapAt-braid : {i k : Fin n} → Adj i k → (xs : List X) → length xs ≡ suc n
             → swapAt i (swapAt k (swapAt i xs)) ≡ swapAt k (swapAt i (swapAt k xs))
swapAt-braid adj0       (a ∷ b ∷ c ∷ rest) _   = refl
swapAt-braid adj0       []                 ()
swapAt-braid adj0       (a ∷ [])           ()
swapAt-braid adj0       (a ∷ b ∷ [])       ()
swapAt-braid (adjS adj) []                 ()
swapAt-braid (adjS adj) (a ∷ xs)           len =
  cong (a ∷_) (swapAt-braid adj xs (suc-injective len))

------------------------------------------------------------------------
-- 3. The endpoint lemma:  `~ʷ`-equal words act the same on a list (of
-- the matching length).  This is what makes `⟦ w ⟧↭ xs` and `⟦ w′ ⟧↭ xs`
-- have the *same* target, a prerequisite for relating them in `≅↭ⁱ`.
applyW-~ : {w w′ : Word n} → w ~ʷ w′ → (xs : List X) → length xs ≡ suc n
         → applyW w xs ≡ applyW w′ xs
applyW-~ ~refl          xs len = refl
applyW-~ (~sym r)       xs len = sym (applyW-~ r xs len)
applyW-~ (~trans r₁ r₂) xs len = trans (applyW-~ r₁ xs len) (applyW-~ r₂ xs len)
applyW-~ (∷c eq r)      xs len = cong₂ swapAt eq (applyW-~ r xs len)
applyW-~ (c1 i {w})     xs len = swapAt-invol i (applyW w xs)
applyW-~ (c2 {w = w} f) xs len = swapAt-far f (applyW w xs)
applyW-~ (c3 {w = w} adj) xs len =
  swapAt-braid adj (applyW w xs) (trans (applyW-length w xs) len)

------------------------------------------------------------------------
-- 4. `eval-respect`:  the list-level derivation `⟦ w ⟧↭ xs` evaluates
-- (via `eval-↭`) to the SAME finite bijection as the position-level word
-- `w` (via `evalW`), once both are cast to `FinBij (suc n) (suc n)` using
-- the length hypothesis `length xs ≡ suc n`.
--
-- This is the keystone connecting the list-permutation evaluation
-- (`Eval.eval-↭`) with the abstract word evaluation (`Word.evalW`).

-- The cast: transport a `FinBij p q` to `FinBij (suc n) (suc n)` given
-- `p ≡ suc n` and `q ≡ suc n`.
castFB : {p q : ℕ} → p ≡ suc n → q ≡ suc n
       → FinBij p q → FinBij (suc n) (suc n)
castFB e₁ e₂ b = subst₂ P.Permutation e₁ e₂ b

-- Pushing the forward action through the `subst₂` cast.  With both
-- endpoint proofs `refl`, the cast is the identity.
cast-push : {p q : ℕ} (e₁ : p ≡ suc n) (e₂ : q ≡ suc n)
            (b : FinBij p q) (k : Fin (suc n))
          → castFB e₁ e₂ b P.⟨$⟩ʳ k
            ≡ subst Fin e₂ (b P.⟨$⟩ʳ subst Fin (sym e₁) k)
cast-push refl refl b k = refl

-- The cast is irrelevant in its endpoint proofs (here only the codomain
-- proof varies); proved by transporting along the proof-of-proofs equality.
cast-recod : {p q : ℕ} (e₁ : p ≡ suc n) {e₂ e₂′ : q ≡ suc n} → e₂ ≡ e₂′
           → (b : FinBij p q) → castFB e₁ e₂ b ≈-fb castFB e₁ e₂′ b
cast-recod e₁ {e₂} refl b _ = refl

-- `cons-fb` commutes with the cast:  casting then lifting equals lifting
-- then casting.  (Both endpoint proofs `refl` ⇒ identity on both sides.)
cons-cast : {p q : ℕ} (e₁ : p ≡ suc n) (e₂ : q ≡ suc n) (b : FinBij p q)
          → castFB (cong suc e₁) (cong suc e₂) (cons-fb b)
            ≈-fb cons-fb (castFB e₁ e₂ b)
cons-cast refl refl b k = refl

-- The cast is a (contravariant-in-domain) functor:  it distributes over
-- composition, with the chosen middle proof `e₂`.
comp-cast : {p q r : ℕ} (e₁ : p ≡ suc n) (e₂ : q ≡ suc n) (e₃ : r ≡ suc n)
            (g : FinBij q r) (f : FinBij p q)
          → castFB e₁ e₃ (g ∘-fb f)
            ≈-fb (castFB e₂ e₃ g ∘-fb castFB e₁ e₂ f)
comp-cast refl refl refl g f k = refl

-- Recode the domain proof (companion to `cast-recod`).
cast-redom : {p q : ℕ} {e₁ e₁′ : p ≡ suc n} → e₁ ≡ e₁′ → (e₂ : q ≡ suc n)
           → (b : FinBij p q) → castFB e₁ e₂ b ≈-fb castFB e₁′ e₂ b
cast-redom refl e₂ b _ = refl

-- Casting the identity (with equal endpoint proofs) is the identity.
cast-id : {p : ℕ} (e : p ≡ suc n) → castFB e e (id-fb {n = p}) ≈-fb id-fb
cast-id refl _ = refl

------------------------------------------------------------------------
-- Tiny `cong suc` / `trans` bookkeeping (for the `cong suc`-shaped length
-- proofs that arise in the inductive step).

cong-suc-inj : {p q : ℕ} (e : suc p ≡ suc q) → cong suc (suc-injective e) ≡ e
cong-suc-inj refl = refl

cong-suc-trans : {p q r : ℕ} (e₁ : p ≡ q) (e₂ : q ≡ r)
               → trans (cong suc e₁) (cong suc e₂) ≡ cong suc (trans e₁ e₂)
cong-suc-trans refl e₂ = refl

------------------------------------------------------------------------
-- Helper:  the single-generator case.
--
--   eval-↭ (swapAt-↭ i ys)  cast to FinBij (suc n)(suc n)  ≈-fb  genFB i

gen-eval : {n : ℕ} (i : Fin n) (ys : List X) (len : length ys ≡ suc n)
         → castFB len (trans (swapAt-length i ys) len)
                  (eval-↭ (swapAt-↭ i ys))
           ≈-fb genFB i
-- `0F` on a two-or-more list:  swapAt-↭ 0F (a∷b∷rest) = swap a b refl, so
-- eval-↭ = swap-fb _ ∘-fb cons-fb (cons-fb id-fb) ≈ swap-fb _ = genFB 0F.
gen-eval {suc n} 0F (a ∷ b ∷ rest) len k =
  -- `swapAt-length 0F (a∷b∷rest) = refl`, so the codomain proof is `len`.
  trans (cast-push {n = suc n} len len
                   (eval-↭ (swapAt-↭ {n = suc n} 0F (a ∷ b ∷ rest))) k)
        (aux len k)
  where
    -- Generalise `len : suc (suc (length rest)) ≡ suc m` and match it to
    -- `refl`; that collapses both `subst`s and exposes the FinBij identity
    --   eval-↭ (swap a b refl) = swap-fb _ ∘-fb cons-fb (cons-fb id-fb)
    --                          ≈ swap-fb _ = genFB 0F.
    aux : {m : ℕ} (e : suc (suc (length rest)) ≡ suc (suc m)) (j : Fin (suc (suc m)))
        → subst Fin e
            (eval-↭ (Perm.swap a b (Perm.refl {xs = rest}))
             P.⟨$⟩ʳ subst Fin (sym e) j)
          ≡ swap-fb m P.⟨$⟩ʳ j
    aux refl j =
      ∘-fb-cong {g = swap-fb (length rest)} {g′ = swap-fb (length rest)}
                {f = cons-fb (cons-fb (id-fb {n = length rest}))}
                {f′ = id-fb {n = suc (suc (length rest))}}
                (λ _ → refl)
                -- cons-fb (cons-fb id-fb) ≈ id-fb, chained pointwise.
                (λ p → trans (cons-fb-cong (cons-fb-functor-id {n = length rest}) p)
                             (cons-fb-functor-id {n = suc (length rest)} p))
                j
-- `fsuc i` on `a ∷ xs`:  swapAt-↭ (fsuc i) (a∷xs) = prep a (swapAt-↭ i xs),
-- so eval-↭ = cons-fb (eval-↭ (swapAt-↭ i xs)) ≈ cons-fb (genFB i) = genFB (fsuc i).
-- We move the cast through `cons-fb` (the cast is `cons`-natural, `cons-cast`)
-- after recoding the `cong suc`-shaped length proofs, then apply the IH.
gen-eval {suc n} (fsuc i) (a ∷ xs) len k =
  -- chained pointwise (at the index `k`) to keep the intermediate
  -- bijections concrete and avoid non-injective `≈-fb` middle-term metas.
  trans (cast-redom {n = suc n} (sym (cong-suc-inj len)) cod
                    (cons-fb (eval-↭ (swapAt-↭ i xs))) k)
  (trans (cast-recod {n = suc n} (cong suc lenTail) codEq
                     (cons-fb (eval-↭ (swapAt-↭ i xs))) k)
  (trans (cons-cast {n = n} lenTail (trans (swapAt-length i xs) lenTail)
                    (eval-↭ (swapAt-↭ i xs)) k)
         (cons-fb-cong (gen-eval i xs lenTail) k)))
  where
    lenTail : length xs ≡ suc n
    lenTail = suc-injective len
    -- the codomain proof appearing in the goal (`swapAt-length (fsuc i) (a∷xs)`
    -- reduces to `cong suc (swapAt-length i xs)`).
    cod : suc (length (swapAt i xs)) ≡ suc (suc n)
    cod = trans (cong suc (swapAt-length i xs)) len
    -- after recoding the domain proof to `cong suc lenTail`, the codomain
    -- proof must be recoded to `cong suc (trans (swapAt-length i xs) lenTail)`.
    codEq : cod ≡ cong suc (trans (swapAt-length i xs) lenTail)
    codEq =
      trans (cong (trans (cong suc (swapAt-length i xs))) (sym (cong-suc-inj len)))
            (cong-suc-trans (swapAt-length i xs) lenTail)

------------------------------------------------------------------------
-- The main lemma.

eval-respect : {n : ℕ} (w : Word n) (xs : List X) (len : length xs ≡ suc n)
             → castFB len (trans (applyW-length w xs) len)
                      (eval-↭ (⟦ w ⟧↭ xs))
               ≈-fb evalW w
-- `w = []`:  ⟦[]⟧↭ xs = refl, eval-↭ refl = id-fb, evalW [] = id-fb,
-- so the goal is `castFB len len id-fb ≈-fb id-fb`.
eval-respect [] xs len = cast-id len
-- `w = i ∷ w′`:  ⟦i∷w′⟧↭ xs = trans (⟦w′⟧↭ xs) (swapAt-↭ i (applyW w′ xs)),
-- so eval-↭ = eval-↭ (swapAt-↭ i (applyW w′ xs)) ∘-fb eval-↭ (⟦w′⟧↭ xs)
--           ≈ genFB i ∘-fb evalW w′ = evalW (i ∷ w′)
-- via gen-eval (head) and the IH eval-respect w′ (tail).
-- We split the cast over the composition (`comp-cast`), recoding the
-- middle/codomain length proof via associativity of `trans`, then apply
-- `gen-eval` to the head factor and the IH `eval-respect w` to the tail.
eval-respect {n} (i ∷ w) xs len k =
  -- chained pointwise (at the index `k`), as in `gen-eval`.
  trans (comp-cast {n = n} len lenMid lenCod
                   (eval-↭ (swapAt-↭ i (applyW w xs)))
                   (eval-↭ (⟦ w ⟧↭ xs)) k)
        (∘-fb-cong {g = castFB lenMid lenCod
                              (eval-↭ (swapAt-↭ i (applyW w xs)))}
                   {g′ = genFB i}
                   {f = castFB len lenMid (eval-↭ (⟦ w ⟧↭ xs))}
                   {f′ = evalW w}
                   headFactor
                   (eval-respect w xs len)
                   k)
  where
    lenMid : length (applyW w xs) ≡ suc n
    lenMid = trans (applyW-length w xs) len
    lenCod : length (applyW (i ∷ w) xs) ≡ suc n
    lenCod = trans (applyW-length (i ∷ w) xs) len
    -- The head factor:  recode `lenCod` to the `gen-eval`-shaped codomain
    -- proof `trans (swapAt-length i (applyW w xs)) lenMid` (associativity),
    -- then it is exactly `gen-eval i (applyW w xs) lenMid`.
    headFactor : castFB lenMid lenCod (eval-↭ (swapAt-↭ i (applyW w xs)))
                 ≈-fb genFB i
    headFactor j =
      trans (cast-recod {n = n} lenMid
               (trans-assoc (swapAt-length i (applyW w xs))
                            {applyW-length w xs} {len})
               (eval-↭ (swapAt-↭ i (applyW w xs))) j)
            (gen-eval i (applyW w xs) lenMid j)

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- WORKED EXAMPLE: defeating "green slime" by modelling a `with`-defined
-- function as an inductive relation (its graph).
--
-- This is the technique used to discharge `edge-step-term-φ` (Lemma 0b of the
-- APROP soundness proof): see `Categories.APROP.Hypergraph.Soundness.
-- Discharge.EdgeStepRelation` / `EdgeStepNaturality`.  Here it is distilled to
-- toy types (ℕ and `List ℕ`) so the pattern is visible in isolation.
--
-- "Green slime" (Conor McBride's term) = a *defined function* appearing in a
-- goal type in a position where Agda's unifier / `with`-abstraction can't make
-- progress.  It bites hardest with `with`-defined functions: once `f` is
-- defined by `with (decide …)`, a call `f a` is a STUCK neutral, and you cannot
-- reduce it by `with`/`rewrite` from the outside, because the scrutinee it
-- matches on lives *inside* the call and isn't shared with your own `with`.
--------------------------------------------------------------------------------

module Categories.Examples.RelationViewGreenSlime where

open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

--------------------------------------------------------------------------------
-- §1.  A `with`-defined function — the "fire / skip" shape, exactly like
-- `edge-step` (which fires when `extract-prefix` finds the inputs, else skips).
--
-- `pop k xs` drops the head of `xs` when it equals `k` ("fire"), otherwise
-- leaves `xs` unchanged ("skip").  `pop-tag` records which branch was taken.

pop : ℕ → List ℕ → List ℕ
pop k []       = []
pop k (x ∷ xs) with x ≟ k
... | yes _ = xs            -- fire
... | no  _ = x ∷ xs        -- skip

pop-tag : ℕ → List ℕ → Bool
pop-tag k []       = false
pop-tag k (x ∷ xs) with x ≟ k
... | yes _ = true
... | no  _ = false

--------------------------------------------------------------------------------
-- §2.  THE PROBLEM (green slime).
--
-- Say we want to prove a property that mentions BOTH `pop k xs` and
-- `pop-tag k xs` and needs them to agree on which branch ran — e.g.
--
--     fired⊎skip : ∀ k xs → (pop-tag k xs ≡ true) ⊎ (pop k xs ≡ xs)
--
-- The naive proof case-splits on `x ≟ k`:
--
--     fired⊎skip k []       = inj₂ refl
--     fired⊎skip k (x ∷ xs) with x ≟ k
--     ... | yes _ = inj₁ refl
--     ... | no  _ = inj₂ refl
--
-- Here it happens to work because both functions appear *directly*.  But the
-- moment one of them is wrapped in ANOTHER `with`-defined function whose result
-- sits in the goal — the situation in the real proof, where `edge-step` was
-- buried inside the goal via `edge-step-stack-φ` (itself `with`-defined) — the
-- abstraction `with x ≟ k` becomes ILL-TYPED:
--
--     …error: [SplitError.UnificationStuck] / "ill-typed with-abstraction"…
--
-- because Agda rewrites the buried call to `g … | w` (a with-stuck form) that
-- no longer typechecks.  `rewrite` doesn't help either: the scrutinee is not a
-- syntactic subterm of the stuck call, so there's nothing to rewrite.

--------------------------------------------------------------------------------
-- §3.  THE FIX — model the function's behaviour as an inductive relation (its
-- GRAPH).  Each constructor corresponds to one clause of the function, and
-- *carries the evidence* (`x ≡ k` / `x ≢ k`) that selected it.

data PopR (k : ℕ) : List ℕ → Bool → List ℕ → Set where
  []R   :                              PopR k []       false []
  fireR : ∀ x xs → x ≡ k →             PopR k (x ∷ xs) true  xs
  skipR : ∀ x xs → x ≢ k →             PopR k (x ∷ xs) false (x ∷ xs)

--------------------------------------------------------------------------------
-- §4.  The functions REALISE the relation (the "cover" lemma).
--
-- This is the ONE place we case-split on `x ≟ k`.  It works cleanly because
-- `pop`/`pop-tag` appear *directly* applied to `x ∷ xs`: the `x ≟ k` we
-- abstract IS the scrutinee inside them, so after matching they reduce.
-- (This is the analogue of `edge-step-graph`.)

pop-graph : ∀ k xs → PopR k xs (pop-tag k xs) (pop k xs)
pop-graph k []       = []R
pop-graph k (x ∷ xs) with x ≟ k
... | yes e  = fireR x xs e
... | no  ¬e = skipR x xs ¬e

--------------------------------------------------------------------------------
-- §5.  Soundness — the relation PINS the function values (the other half of
-- "the function computes a value iff the relation holds").  Analogue of
-- `edge-step-sound`.

pop-sound : ∀ {k xs t ys} → PopR k xs t ys
          → pop-tag k xs ≡ t × pop k xs ≡ ys
pop-sound []R                = refl , refl
pop-sound {k} (fireR x xs e) with x ≟ k
... | yes _  = refl , refl
... | no  ¬e = ⊥-elim (¬e e)
pop-sound {k} (skipR x xs ¬e) with x ≟ k
... | yes e  = ⊥-elim (¬e e)
... | no  _  = refl , refl

--------------------------------------------------------------------------------
-- §6.  THE PAYOFF — downstream proofs are done by case analysis on the
-- relation's CONSTRUCTORS, never on `x ≟ k` and never with the functions
-- buried in the goal.  No green slime.
--
-- First state the property over the relation (trivial: one line per
-- constructor), then transport to the functions via the cover `pop-graph`.

-- Over the relation: in every branch, either it fired (`t ≡ true`) or the list
-- is unchanged (`ys ≡ xs`).
fired-or-skip : ∀ {k xs t ys} → PopR k xs t ys → (t ≡ true) ⊎ (ys ≡ xs)
fired-or-skip []R            = inj₂ refl
fired-or-skip (fireR x xs e) = inj₁ refl
fired-or-skip (skipR x xs _) = inj₂ refl

-- The function-level corollary follows immediately from the cover — note there
-- is NO `with` here, so the stuck calls `pop-tag k xs` / `pop k xs` never need
-- to be reduced from the outside.
fired-or-skip-fn : ∀ k xs → (pop-tag k xs ≡ true) ⊎ (pop k xs ≡ xs)
fired-or-skip-fn k xs = fired-or-skip (pop-graph k xs)

--------------------------------------------------------------------------------
-- §7.  The same trick scales to NATURALITY (the actual shape of Lemma 0b):
-- relating `pop` on a relabelled input to `pop` on the original.  We case on
-- the relation witness for the original run, and use the cover at the
-- relabelled input — the injectivity of the relabel lines the branches up,
-- and we never case on the *neutral* test `f x ≟ f k` (which would also hit a
-- `--without-K` wall on the reflexive `f x ≡ f x`).

open import Data.List using (map)

pop-natural
  : ∀ (f : ℕ → ℕ) (f-inj : ∀ {a b} → f a ≡ f b → a ≡ b)
      (k : ℕ) (xs : List ℕ)
  → pop (f k) (map f xs) ≡ map f (pop k xs)
pop-natural f f-inj k xs = go xs (pop-graph k xs)
  where
    -- `xs` is made an explicit argument so the constructor match can refine it.
    go : ∀ (xs : List ℕ) {t ys} → PopR k xs t ys
       → pop (f k) (map f xs) ≡ map f ys
    go .[]        []R            = refl
    go .(x ∷ xs') (fireR x xs' e) with f x ≟ f k
    ... | yes _  = refl
    ... | no ¬fe = ⊥-elim (¬fe (cong f e))
    go .(x ∷ xs') (skipR x xs' ¬e) with f x ≟ f k
    ... | yes fe = ⊥-elim (¬e (f-inj fe))
    ... | no  _  = refl

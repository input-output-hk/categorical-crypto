{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Rigidity of `eval-↭` on `Unique` codomains.
--
-- If `ys` is `Unique` (no duplicate elements), then ANY two
-- list-permutation derivations `p, q : xs ↭ ys` evaluate to the SAME
-- finite bijection.  Intuitively: with distinct elements there is only
-- one way to rearrange `xs` into `ys`, so the underlying position
-- bijection is forced.
--
-- This is the key lemma that lets the APROP completeness consumer
-- discharge the `≅↭` (equal-evaluated-bijection) hypothesis of the
-- Kelly `FaithfulnessResidual`/`TransSelfLoopResidual` purely from the
-- `Unique`-ness of the decoder stacks — no label-injectivity of `vlab`
-- is needed (the X-level lists may have duplicate labels; rigidity is
-- applied at the Fin-index level where the stacks ARE `Unique`).
--
-- Proof: `eval-↭` is "lookup-sound" — `lookup ys (eval-↭ p ⟨$⟩ʳ i) ≡
-- lookup xs i` — so for `Unique ys` (hence injective `lookup ys`) the
-- forward map of `eval-↭ p` is determined pointwise.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Rigid where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.List.Base using (List; []; _∷_; length; lookup)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.Fin.Permutation as P

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Level using (Level)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- `Unique` lists have injective `lookup`.  (Inlined to keep this module
-- self-contained; identical to
-- `Categories.APROP.Hypergraph.Prune.lookup-injective-unique`.)

private
  All-lookup : ∀ {p} {Q : A → Set p} {xs : List A}
             → All Q xs → (i : Fin (length xs)) → Q (lookup xs i)
  All-lookup (q ∷ _)  zero    = q
  All-lookup (_ ∷ qs) (suc i) = All-lookup qs i

  lookup-injective-unique
    : ∀ {xs : List A}
    → Unique xs → (i j : Fin (length xs))
    → lookup xs i ≡ lookup xs j
    → i ≡ j
  lookup-injective-unique (_  ∷ _ ) zero    zero    _  = refl
  lookup-injective-unique (x≢ ∷ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
  lookup-injective-unique (x≢ ∷ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
  lookup-injective-unique (_  ∷ uq) (suc i) (suc j) eq = cong suc (lookup-injective-unique uq i j eq)

------------------------------------------------------------------------
-- Lookup-soundness of `eval-↭`:  `eval-↭ p` carries position `i` of
-- `xs` to a position of `ys` holding the SAME element.

lookup-sound
  : {xs ys : List A} (p : xs ↭ ys) (i : Fin (length xs))
  → lookup ys (eval-↭ p P.⟨$⟩ʳ i) ≡ lookup xs i
lookup-sound Perm.refl         i             = refl
lookup-sound (Perm.prep x p)   0F            = refl
lookup-sound (Perm.prep x p)   (suc i)       = lookup-sound p i
lookup-sound (Perm.swap x y p) 0F            = refl
lookup-sound (Perm.swap x y p) (suc 0F)      = refl
lookup-sound (Perm.swap x y p) (suc (suc i)) = lookup-sound p i
lookup-sound (Perm.trans p q)  i             =
  trans (lookup-sound q (eval-↭ p P.⟨$⟩ʳ i)) (lookup-sound p i)

------------------------------------------------------------------------
-- Rigidity: with a `Unique` codomain, `eval-↭` is determined.

eval-rigid
  : {xs ys : List A} → Unique ys
  → (p q : xs ↭ ys)
  → eval-↭ p ≈-fb eval-↭ q
eval-rigid uniq p q i =
  lookup-injective-unique uniq _ _
    (trans (lookup-sound p i) (sym (lookup-sound q i)))

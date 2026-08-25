{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Connectivity of linear extensions of a finite poset.
--
-- Pure finite-order-theory combinatorics, independent of any
-- application.  We prove:
--
--   Any two linear extensions of a finite strict poset are connected
--   by a finite sequence of transpositions of adjacent, incomparable
--   elements.
--
-- A "linear extension" is represented concretely as a `List` of carrier
-- elements that is R-inversion-free (`NoInv`).  `NoInv` is exactly an
-- `AllPairs` predicate: `AllPairs (λ a b → ¬ R b a)` says that for every
-- `a` occurring before `b`, `¬ R b a` — i.e. no later element is
-- strictly below an earlier one.  Phrasing it as `AllPairs` makes the
-- two key bookkeeping lemmas fall out as clean `All`/`AllPairs`
-- manipulations (see `NoInv-─` and `bubble`).
--
-- Two lists are extensions of "the same poset" when they are
-- permutations of each other (`_↭_`); finiteness of the carrier is
-- captured by working with the concrete finite list and inducting on
-- it structurally.
--
-- An "adjacent-incomparable swap" `_↝_` rewrites
--     ps ++ x ∷ y ∷ qs   to   ps ++ y ∷ x ∷ qs
-- when `x` and `y` are incomparable.  `_↝*_` is its reflexive-transitive
-- closure (the standard library `Star`).
--
--   Main theorem:  connectivity :  (∀ {x} → ¬ R x x)
--                                → L ↭ M → NoInv L → NoInv M → L ↝* M
--
--   (on the irreflexivity hypothesis, see the NOTE below the imports.)
--
-- This module is now postulate-free and `--safe`.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (∈-resp-↭)
open import Level using (_⊔_)

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.All.Properties using (─⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  renaming (head to NoInv-head; tail to NoInv-tail)
open import Data.List.Relation.Unary.Any using (here; there; _─_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans; prep; swap)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (drop-∷; ↭-empty-inv)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅◅_; gmap; return; reverse)

-- NOTE: the connectivity theorem needs only *irreflexivity* of `R`
-- (used to see that the head of `L` is R-minimal); transitivity is never
-- required.  Irreflexivity is an explicit argument of
-- `connectivity` alone — the predicates (`Incomp`/`Below`/`NoInv`/`_↝_`)
-- are irreflexivity-free, so instantiating THEM requires no proof about
-- `R` at all.  This lets the result be instantiated at the *immediate*
-- dependency relation of a hypergraph (which is neither transitive nor
-- provably irreflexive in general) without extra hypotheses.
module Categories.Combinatorics.LinearExtension
  {a r} (A : Set a) (R : A → A → Set r)
  where

private
  variable
    x y : A
    xs L M L′ : List A

------------------------------------------------------------------------
-- Comparability / incomparability
------------------------------------------------------------------------

-- `x` and `y` are incomparable when neither is strictly below the other.
Incomp : A → A → Set r
Incomp x y = (¬ R x y) × (¬ R y x)

Incomp-sym : Incomp x y → Incomp y x
Incomp-sym (¬xy , ¬yx) = (¬yx , ¬xy)

------------------------------------------------------------------------
-- The no-inversion predicate ("is a linear extension"), as `AllPairs`.
--
-- `Below b a := ¬ R b a`.  Then `AllPairs Below L` says: whenever `a`
-- occurs before `b` in `L`, `¬ R b a` — no later element is strictly
-- below an earlier one.  (`AllPairs Below (x ∷ xs)` unfolds to
-- `All (Below x) xs × AllPairs Below xs`, matching the previous
-- hand-rolled definition.)
------------------------------------------------------------------------

-- `Below x y` holds when `y` is *not* strictly below `x`; used so that
-- `AllPairs Below` is the no-inversion predicate.
Below : A → A → Set r
Below x y = ¬ R y x

NoInv : List A → Set (a ⊔ r)
NoInv = AllPairs Below

-- (`NoInv-head`/`NoInv-tail`, the two `AllPairs._∷_` field projections,
-- are stdlib's `AllPairs.head`/`AllPairs.tail` under those names.)

------------------------------------------------------------------------
-- The adjacent-incomparable swap step and its closure
------------------------------------------------------------------------

-- One step: swap an adjacent incomparable pair sitting after prefix `ps`.
data _↝_ : List A → List A → Set (a ⊔ r) where
  swap-step : ∀ (ps : List A) {x y} (qs : List A) →
              Incomp x y →
              (ps ++ x ∷ y ∷ qs) ↝ (ps ++ y ∷ x ∷ qs)

-- Reflexive-transitive closure.
_↝*_ : List A → List A → Set (a ⊔ r)
_↝*_ = Star _↝_

infix 4 _↝_ _↝*_

↝*-trans : L ↝* M → M ↝* L′ → L ↝* L′
↝*-trans = _◅◅_

-- A single swap is symmetric: swapping the pair back is also an
-- adjacent-incomparable swap.  Hence so is the closure, by `Star.reverse`
-- (which accumulates, so the reversal stays linear in the chain length).
↝-sym : L ↝ M → M ↝ L
↝-sym (swap-step ps qs inc) = swap-step ps qs (Incomp-sym inc)

↝*-sym : L ↝* M → M ↝* L
↝*-sym = reverse ↝-sym

------------------------------------------------------------------------
-- Congruence: `↝` (hence `↝*`) survives prepending a head element.
-- Only a one-element prefix is ever needed, and there the new head is
-- absorbed by `swap-step`'s own prefix argument definitionally
-- (`(x ∷ ps) ++ qs = x ∷ (ps ++ qs)`), so no associativity transport
-- appears at all.
------------------------------------------------------------------------

↝-cons : ∀ x → L ↝ M → (x ∷ L) ↝ (x ∷ M)
↝-cons x (swap-step ps qs inc) = swap-step (x ∷ ps) qs inc

↝*-cons : ∀ x → L ↝* M → (x ∷ L) ↝* (x ∷ M)
↝*-cons x = gmap (x ∷_) (↝-cons x)

------------------------------------------------------------------------
-- Removing the element pointed to by a membership witness: `M ─ i` is
-- stdlib's `Any._─_`, i.e. `M` with the occurrence located by `i` deleted
-- and every other element left in place.
------------------------------------------------------------------------

-- `M` is a permutation of `x ∷ (M ─ i)`.
remove-↭ : (M : List A) (i : x ∈ M) → M ↭ x ∷ (M ─ i)
remove-↭ (w ∷ rest) (here refl) = ↭-refl
remove-↭ (w ∷ rest) (there i)   =
  ↭-trans (prep w (remove-↭ rest i)) (swap w _ ↭-refl)

-- Deletion preserves the no-inversion property: `AllPairs`'s pairs of
-- `M ─ i` are a sub-collection of `M`'s, so each `All` field shrinks by
-- stdlib's `All.─⁺` — the same recursion on `i` that `_─_` itself runs.
NoInv-─ : (M : List A) (i : x ∈ M) → NoInv M → NoInv (M ─ i)
NoInv-─ (w ∷ rest) (here refl) noM       = NoInv-tail noM
NoInv-─ (w ∷ rest) (there i)   (h ∷ noM) = ─⁺ i h ∷ NoInv-─ rest i noM

------------------------------------------------------------------------
-- The bubble lemma: an R-minimal `x` can be bubbled to the front of any
-- inversion-free `M` that contains it.
--
-- The recursion on the membership witness `i : x ∈ M` reads the two halves
-- of each swap's incomparability straight off its two hypotheses: `¬ R x m`
-- off the head field of `NoInv` at that level, and `¬ R m x` off
-- R-minimality.  No pre-pass over `i` is needed: collecting the halves
-- ahead of time would just be a second recursion over the same witness.
------------------------------------------------------------------------

bubble : (M : List A) (i : x ∈ M) → NoInv M →
         (∀ {z} → z ∈ M → ¬ R z x) → M ↝* (x ∷ (M ─ i))
bubble (m ∷ rest) (here refl) _    _     = ε
bubble {x = x} (m ∷ rest) (there i) noM xmin =
  -- recurse inside `rest`, prepend `m`, then one final swap of (m x).
  ↝*-trans (↝*-cons m (bubble rest i (NoInv-tail noM)
                              (λ z∈rest → xmin (there z∈rest))))
           (return head-swap)
  where
  -- `m ∷ x ∷ (rest ─ i) ↝ x ∷ m ∷ (rest ─ i)`, valid since m,x are
  -- incomparable: `¬ R m x` from minimality, `¬ R x m` from `NoInv`.
  head-swap : (m ∷ x ∷ (rest ─ i)) ↝ (x ∷ m ∷ (rest ─ i))
  head-swap = swap-step [] (rest ─ i)
                (xmin (here refl) , lookup (NoInv-head noM) i)

------------------------------------------------------------------------
-- Main theorem.
--
-- Direct structural recursion on the list `L`: the only recursive call is
-- on the tail of a cons, so the termination checker accepts it without any
-- well-founded/`Acc` machinery.
--
-- Cross-reference: `connectivity` bubbles `x` to the front by adjacent
-- swaps and recurses on the tail — the same bubble-to-front recursion
-- shape as `PermuteCoherence.Coxeter.Word.canonW` (`canonW` rotates the
-- destined-front element via a rotation word and recurses on the
-- residual). The carriers (linear extensions of a poset here vs.
-- `FinBij`/words there) and side-conditions (`NoInv`-guarded swaps vs.
-- unconditional rotation) differ enough that a shared formalization was
-- examined and declined as not worth the cost: the `_∈_`/`NoInv`-guarded step
-- here and `remove`/`rotate` there do not align at the type level.
------------------------------------------------------------------------

connectivity : (∀ {x} → ¬ R x x) → L ↭ M → NoInv L → NoInv M → L ↝* M
connectivity {L = []} R-irrefl perm _ noM =
  -- A permutation of [] is []; so M = [] and L = M reflexively.
  subst ([] ↝*_) (sym (↭-empty-inv (↭-sym perm))) ε
connectivity {L = x ∷ L′} {M = M} R-irrefl perm noL noM =
  -- (1) locate x in M, (2) bubble it to the front, (3) recurse on tails.
  bubbled-then-tail
  where
  i : x ∈ M
  i = ∈-resp-↭ perm (here refl)

  M′ : List A
  M′ = M ─ i

  -- `x` is strictly below nothing in `M`: `↭-sym perm` moves into
  -- `x ∷ L′`, where the head field of `NoInv (x ∷ L′)` gives `¬ R z x` for
  -- every `z ∈ L′`, and `R-irrefl` covers `z ≡ x`.
  x-min : ∀ {z} → z ∈ M → ¬ R z x
  x-min z∈M with ∈-resp-↭ (↭-sym perm) z∈M
  ... | here  z≡x  = subst (λ u → ¬ R u x) (sym z≡x) R-irrefl
  ... | there z∈L′ = lookup (NoInv-head noL) z∈L′

  -- M ↝* x ∷ M′
  M↝*xM′ : M ↝* (x ∷ M′)
  M↝*xM′ = bubble M i noM x-min

  -- M ↭ x ∷ M′, hence x ∷ L′ ↭ x ∷ M′, hence L′ ↭ M′ by cancellation.
  M↭xM′ : M ↭ (x ∷ M′)
  M↭xM′ = remove-↭ M i

  L′↭M′ : L′ ↭ M′
  L′↭M′ = drop-∷ (↭-trans perm M↭xM′)

  noM′ : NoInv M′
  noM′ = NoInv-─ M i noM

  noL′ : NoInv L′
  noL′ = NoInv-tail noL

  -- IH on the structural subterm `L′` (the tail of `x ∷ L′`).
  tails : L′ ↝* M′
  tails = connectivity R-irrefl L′↭M′ noL′ noM′

  -- x ∷ L′ ↝* x ∷ M′, then ←↝* M  (reverse of bubbling).
  bubbled-then-tail : (x ∷ L′) ↝* M
  bubbled-then-tail = ↝*-trans (↝*-cons x tails) (↝*-sym M↝*xM′)

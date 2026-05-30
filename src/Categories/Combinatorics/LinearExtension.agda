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
-- manipulations (see `↝-preserves-NoInv` and `before-incomparable`).
--
-- Two lists are extensions of "the same poset" when they are
-- permutations of each other (`_↭_`); finiteness of the carrier is
-- captured by working with the concrete finite list and inducting on
-- its length.
--
-- An "adjacent-incomparable swap" `_↝_` rewrites
--     ps ++ x ∷ y ∷ qs   to   ps ++ y ∷ x ∷ qs
-- when `x` and `y` are incomparable.  `_↝*_` is its reflexive-transitive
-- closure (the standard library `Star`).
--
--   Main theorem:  connectivity :  L ↭ M → NoInv L → NoInv M → L ↝* M
--
-- This module is now postulate-free and `--safe`.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (∈-resp-↭)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Level using (Level; _⊔_)

open import Data.List.Base using (List; []; _∷_; _++_; length; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans; prep; swap)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (drop-∷; ↭-length)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_; gmap)

-- NOTE: the connectivity theorem needs only *irreflexivity* of `R`
-- (used in `before-incomparable`); transitivity is never required, so it
-- is not a parameter.  This lets the result be instantiated at the
-- *immediate* dependency relation of a hypergraph (which is not
-- transitive) without forming its transitive closure.
module Categories.Combinatorics.LinearExtension
  {a r} (A : Set a) (R : A → A → Set r)
  (R-irrefl : ∀ {x} → ¬ R x x)
  where

private
  variable
    x y z w : A
    xs ys ps qs L M L′ : List A

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

NoInv-[] : NoInv []
NoInv-[] = []

-- Destructors for the cons case (the two `AllPairs._∷_` fields).
NoInv-head : NoInv (x ∷ xs) → All (Below x) xs
NoInv-head (h ∷ _) = h

NoInv-tail : NoInv (x ∷ xs) → NoInv xs
NoInv-tail (_ ∷ t) = t

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

↝*-refl : L ↝* L
↝*-refl = ε

↝*-trans : L ↝* M → M ↝* L′ → L ↝* L′
↝*-trans = _◅◅_

-- Embed a single step.
step : L ↝ M → L ↝* M
step s = s ◅ ε

-- A single swap is symmetric: swapping the pair back is also an
-- adjacent-incomparable swap.
↝-sym : L ↝ M → M ↝ L
↝-sym (swap-step ps qs inc) = swap-step ps qs (Incomp-sym inc)

-- Hence the closure is symmetric.
↝*-sym : L ↝* M → M ↝* L
↝*-sym ε        = ε
↝*-sym (s ◅ ss) = ↝*-trans (↝*-sym ss) (step (↝-sym s))

------------------------------------------------------------------------
-- Congruence: `↝` (hence `↝*`) is preserved under a fixed prefix.
------------------------------------------------------------------------

↝-prefix : ∀ (rs : List A) → L ↝ M → (rs ++ L) ↝ (rs ++ M)
↝-prefix rs (swap-step ps qs inc) =
  subst₂ _↝_ (++-assoc rs ps _) (++-assoc rs ps _) (swap-step (rs ++ ps) qs inc)

-- Hence on the closure, by mapping the step relation under `rs ++_`.
↝*-prefix : ∀ (rs : List A) → L ↝* M → (rs ++ L) ↝* (rs ++ M)
↝*-prefix rs = gmap (rs ++_) (↝-prefix rs)

-- Special case used in the induction: prepend a single head element.
↝*-cons : ∀ x → L ↝* M → (x ∷ L) ↝* (x ∷ M)
↝*-cons x = ↝*-prefix (x ∷ [])

------------------------------------------------------------------------
-- `↝*` preserves the no-inversion property.
--
-- Now a real proof.  A single swap touches exactly one adjacency: the
-- pair `x , y`.  As `AllPairs`, the only field that changes is the one
-- recording the relation between `x` and `y`, and incomparability
-- (`¬ R x y`) supplies the replacement.  An `All` predicate over a list
-- is unaffected by swapping two of its elements.
------------------------------------------------------------------------

-- An `All` predicate is invariant under swapping one adjacent pair.
All-swap : ∀ {ℓ} {P : A → Set ℓ} (ps : List A) {x y qs} →
           All P (ps ++ x ∷ y ∷ qs) → All P (ps ++ y ∷ x ∷ qs)
All-swap []       (px ∷ py ∷ pqs) = py ∷ px ∷ pqs
All-swap (p ∷ ps) (pp ∷ rest)     = pp ∷ All-swap ps rest

↝-preserves-NoInv : L ↝ M → NoInv L → NoInv M
↝-preserves-NoInv (swap-step ps {x} {y} qs inc) = go ps
  where
  go : ∀ (ps′ : List A) →
       NoInv (ps′ ++ x ∷ y ∷ qs) → NoInv (ps′ ++ y ∷ x ∷ qs)
  -- ps = [] : the swapped pair sits at the front.  `proj₁ inc : ¬ R x y`
  -- is exactly the `Below y x` field needed after the swap; the three
  -- remaining `AllPairs`/`All` fields are reused verbatim.
  go []        ((_ ∷ allBx) ∷ (allBy ∷ noqs)) =
                 (proj₁ inc ∷ allBy) ∷ (allBx ∷ noqs)
  -- ps = p ∷ ps′ : the head `p` relates to the same multiset of later
  -- elements (only their order changed), so its `All` field survives
  -- via `All-swap`; recurse on the tail.
  go (p ∷ ps′) (allBp ∷ noinv) = All-swap ps′ allBp ∷ go ps′ noinv

↝*-preserves-NoInv : L ↝* M → NoInv L → NoInv M
↝*-preserves-NoInv ε        noL = noL
↝*-preserves-NoInv (s ◅ ss) noL =
  ↝*-preserves-NoInv ss (↝-preserves-NoInv s noL)

------------------------------------------------------------------------
-- Removing the element pointed to by a membership witness.
------------------------------------------------------------------------

-- `remove M i` is `M` with the occurrence located by `i` deleted,
-- keeping all other elements in order.
remove : (M : List A) → x ∈ M → List A
remove (w ∷ rest) (here _)  = rest
remove (w ∷ rest) (there i) = w ∷ remove rest i

-- `M` is a permutation of `x ∷ remove M i`.
remove-↭ : (M : List A) (i : x ∈ M) → M ↭ x ∷ remove M i
remove-↭ (w ∷ rest) (here refl) = ↭-refl
remove-↭ (w ∷ rest) (there i)   =
  ↭-trans (prep w (remove-↭ rest i)) (swap w _ ↭-refl)

------------------------------------------------------------------------
-- `AllBefore x M i` (as a `data` type): every element occurring strictly
-- before the located occurrence of `x` is incomparable to `x`.
------------------------------------------------------------------------

data AllBefore (x : A) : (M : List A) → x ∈ M → Set (a ⊔ r) where
  ab-here  : ∀ {rest} → AllBefore x (x ∷ rest) (here refl)
  ab-there : ∀ {w rest} {i : x ∈ rest} →
             Incomp x w → AllBefore x rest i →
             AllBefore x (w ∷ rest) (there i)

------------------------------------------------------------------------
-- Sub-lemma (a): the head of an inversion-free list is R-minimal.
------------------------------------------------------------------------

head-minimal : NoInv (x ∷ xs) → ∀ {z} → z ∈ xs → ¬ R z x
head-minimal (h ∷ _) z∈xs = lookup h z∈xs

------------------------------------------------------------------------
-- Sub-lemma (b): every element before `x` in `M` is incomparable to `x`.
--
-- Now a real proof.  We first establish, once, that `x` is R-minimal
-- across the whole carrier (`x-min`): nothing in `M` is strictly below
-- `x`.  This uses `↭-sym perm` to move into `x ∷ L′`, where the head
-- field of `NoInv (x ∷ L′)` gives `¬ R z x` for every `z ∈ L′` and
-- `R-irrefl` covers `z ≡ x`.  Then we induct on the membership witness
-- `i : x ∈ M`, reading `¬ R x w` off the head field of `NoInv` at each
-- level and `¬ R w x` off `x-min`.
------------------------------------------------------------------------

before-incomparable :
  ∀ (x : A) (L′ : List A) (M : List A) →
  (x ∷ L′) ↭ M →
  NoInv (x ∷ L′) →
  NoInv M →
  (i : x ∈ M) →
  AllBefore x M i
before-incomparable x L′ M perm noL noM i = go M i noM x-min
  where
  -- `x` is strictly below nothing in `M`.
  x-min : ∀ {z} → z ∈ M → ¬ R z x
  x-min z∈M with ∈-resp-↭ (↭-sym perm) z∈M
  ... | here  z≡x  = subst (λ u → ¬ R u x) (sym z≡x) R-irrefl
  ... | there z∈L′ = lookup (NoInv-head noL) z∈L′

  go : (M′ : List A) (j : x ∈ M′) →
       NoInv M′ → (∀ {z} → z ∈ M′ → ¬ R z x) → AllBefore x M′ j
  go (m ∷ rest) (here refl) _    _     = ab-here
  go (m ∷ rest) (there j)   noM′ xmin′ =
    ab-there (lookup (NoInv-head noM′) j , xmin′ (here refl))
             (go rest j (NoInv-tail noM′) (λ z∈rest → xmin′ (there z∈rest)))

------------------------------------------------------------------------
-- Sub-lemma (c): the bubble lemma.
--   If every element before `x` in `M` is incomparable to `x`, then we
--   can bubble `x` to the front: M ↝* x ∷ remove M i.
------------------------------------------------------------------------

bubble : (M : List A) (i : x ∈ M) → AllBefore x M i → M ↝* (x ∷ remove M i)
bubble (w ∷ rest) (here refl) ab-here = ε
bubble {x = x} (w ∷ rest) (there i) (ab-there incx-w before) =
  -- recurse inside `rest`, prepend `w`, then one final swap of (w x).
  ↝*-trans (↝*-cons w (bubble rest i before))
           (step head-swap)
  where
  -- `w ∷ x ∷ remove rest i ↝ x ∷ w ∷ remove rest i`, valid since w,x
  -- are incomparable.
  head-swap : (w ∷ x ∷ remove rest i) ↝ (x ∷ w ∷ remove rest i)
  head-swap = swap-step [] (remove rest i) (Incomp-sym incx-w)

------------------------------------------------------------------------
-- Locating `x` and the empty-permutation fact.
------------------------------------------------------------------------

x∈-self : ∀ (x : A) (L′ : List A) (M : List A) → (x ∷ L′) ↭ M → x ∈ M
x∈-self x L′ M perm = ∈-resp-↭ perm (here refl)

-- A permutation of `[]` is `[]` (length 0 forces the empty list).
↭[]⇒≡[] : [] ↭ M → [] ≡ M
↭[]⇒≡[] {M = []}    _ = refl
↭[]⇒≡[] {M = _ ∷ _} p with ↭-length p
... | ()

------------------------------------------------------------------------
-- Main theorem.
--
-- We use well-founded recursion on `length L`.
------------------------------------------------------------------------

-- Worker: connectivity given an accessibility certificate on the length.
connectivity-acc :
  ∀ (L M : List A) →
  Acc _<_ (length L) →
  L ↭ M → NoInv L → NoInv M → L ↝* M
connectivity-acc [] M _ perm _ noM =
  -- A permutation of [] is []; so M = [] and L = M reflexively.
  subst (Star _↝_ []) (↭[]⇒≡[] perm) ε
connectivity-acc (x ∷ L′) M (acc rec) perm noL noM =
  -- (1) locate x in M, (2) bubble it to the front, (3) recurse on tails.
  bubbled-then-tail
  where
  i : x ∈ M
  i = x∈-self x L′ M perm

  M′ : List A
  M′ = remove M i

  before : AllBefore x M i
  before = before-incomparable x L′ M perm noL noM i

  -- M ↝* x ∷ M′
  M↝*xM′ : M ↝* (x ∷ M′)
  M↝*xM′ = bubble M i before

  -- M ↭ x ∷ M′, hence x ∷ L′ ↭ x ∷ M′, hence L′ ↭ M′ by cancellation.
  M↭xM′ : M ↭ (x ∷ M′)
  M↭xM′ = remove-↭ M i

  L′↭M′ : L′ ↭ M′
  L′↭M′ = drop-∷ (↭-trans perm M↭xM′)

  -- `x ∷ M′` is inversion-free: reachable from inversion-free M by
  -- adjacent *incomparable* swaps, which preserve NoInv.
  noxM′ : NoInv (x ∷ M′)
  noxM′ = ↝*-preserves-NoInv M↝*xM′ noM

  noM′ : NoInv M′
  noM′ = NoInv-tail noxM′

  noL′ : NoInv L′
  noL′ = NoInv-tail noL

  -- IH on the strictly shorter tail L′ (length L′ < length (x ∷ L′)).
  tails : L′ ↝* M′
  tails = connectivity-acc L′ M′ (rec ≤-refl) L′↭M′ noL′ noM′

  -- x ∷ L′ ↝* x ∷ M′, then ←↝* M  (reverse of bubbling).
  bubbled-then-tail : (x ∷ L′) ↝* M
  bubbled-then-tail = ↝*-trans (↝*-cons x tails) (↝*-sym M↝*xM′)

------------------------------------------------------------------------
-- The theorem, with finiteness/induction wiring discharged.
------------------------------------------------------------------------

connectivity : L ↭ M → NoInv L → NoInv M → L ↝* M
connectivity {L = L} {M = M} perm noL noM =
  connectivity-acc L M (<-wellFounded (length L)) perm noL noM

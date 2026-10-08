{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Linear extensions are connected by adjacent incomparable swaps.
-- `NoInv` uses `AllPairs`: no later element is strictly below an earlier one.
-- Finiteness is captured by the list, not a finite-carrier hypothesis.
------------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans; prep; swap)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.All.Properties using (─⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  renaming (head to NoInv-head; tail to NoInv-tail)
open import Data.List.Relation.Unary.Any using (here; there; _─_)
open import Data.Product using (_×_; _,_)
open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Only irreflexivity is needed, not transitivity: the result also applies
-- to immediate dependency relations.
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

Incomp : A → A → Set r
Incomp x y = (¬ R x y) × (¬ R y x)

Incomp-sym : Incomp x y → Incomp y x
Incomp-sym (¬xy , ¬yx) = (¬yx , ¬xy)

------------------------------------------------------------------------
-- No inversions
------------------------------------------------------------------------
Below : A → A → Set r
Below x y = ¬ R y x

NoInv : List A → Set (a ⊔ r)
NoInv = AllPairs Below

------------------------------------------------------------------------
-- The adjacent-incomparable swap step and its closure
------------------------------------------------------------------------

data _↝_ : List A → List A → Set (a ⊔ r) where
  swap-step : ∀ (ps : List A) {x y} (qs : List A) →
              Incomp x y →
              (ps ++ x ∷ y ∷ qs) ↝ (ps ++ y ∷ x ∷ qs)

_↝*_ : List A → List A → Set (a ⊔ r)
_↝*_ = Star _↝_

infix 4 _↝_ _↝*_

↝*-trans : L ↝* M → M ↝* L′ → L ↝* L′
↝*-trans = _◅◅_

-- `Star.reverse` accumulates, so reversal is linear in the chain length.
↝-sym : L ↝ M → M ↝ L
↝-sym (swap-step ps qs inc) = swap-step ps qs (Incomp-sym inc)

↝*-sym : L ↝* M → M ↝* L
↝*-sym = reverse ↝-sym

------------------------------------------------------------------------
-- Prepending
------------------------------------------------------------------------

↝-cons : ∀ x → L ↝ M → (x ∷ L) ↝ (x ∷ M)
↝-cons x (swap-step ps qs inc) = swap-step (x ∷ ps) qs inc

↝*-cons : ∀ x → L ↝* M → (x ∷ L) ↝* (x ∷ M)
↝*-cons x = gmap (x ∷_) (↝-cons x)

------------------------------------------------------------------------
-- Deletion and connectivity
------------------------------------------------------------------------
remove-↭ : (M : List A) (i : x ∈ M) → M ↭ x ∷ (M ─ i)
remove-↭ (w ∷ rest) (here refl) = ↭-refl
remove-↭ (w ∷ rest) (there i)   =
  ↭-trans (prep w (remove-↭ rest i)) (swap w _ ↭-refl)

NoInv-─ : (M : List A) (i : x ∈ M) → NoInv M → NoInv (M ─ i)
NoInv-─ (w ∷ rest) (here refl) noM       = NoInv-tail noM
NoInv-─ (w ∷ rest) (there i)   (h ∷ noM) = ─⁺ i h ∷ NoInv-─ rest i noM

-- Each swap's incomparability comes from `NoInv` and minimality,
-- without a second recursion over the membership witness.

bubble : (M : List A) (i : x ∈ M) → NoInv M →
         (∀ {z} → z ∈ M → ¬ R z x) → M ↝* (x ∷ (M ─ i))
bubble (m ∷ rest) (here refl) _    _     = ε
bubble {x = x} (m ∷ rest) (there i) noM xmin =
  ↝*-trans (↝*-cons m (bubble rest i (NoInv-tail noM)
                              (λ z∈rest → xmin (there z∈rest))))
           (return (swap-step [] (rest ─ i)
             (xmin (here refl) , lookup (NoInv-head noM) i)))

connectivity : (∀ {x} → ¬ R x x) → L ↭ M → NoInv L → NoInv M → L ↝* M
connectivity {L = []} R-irrefl perm _ noM =
  subst ([] ↝*_) (sym (↭-empty-inv (↭-sym perm))) ε
connectivity {L = x ∷ L′} {M = M} R-irrefl perm noL noM =
  ↝*-trans
    (↝*-cons x (connectivity R-irrefl (drop-∷ (↭-trans perm (remove-↭ M i)))
      (NoInv-tail noL) (NoInv-─ M i noM)))
    (↝*-sym (bubble M i noM x-min))
  where
  i : x ∈ M
  i = ∈-resp-↭ perm (here refl)

  -- Irreflexivity covers the head; `NoInv` covers the tail.
  x-min : ∀ {z} → z ∈ M → ¬ R z x
  x-min z∈M with ∈-resp-↭ (↭-sym perm) z∈M
  ... | here  z≡x  = subst (λ u → ¬ R u x) (sym z≡x) R-irrefl
  ... | there z∈L′ = lookup (NoInv-head noL) z∈L′


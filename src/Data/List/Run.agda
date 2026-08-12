{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Runs of a partial labelled transition system along a list of labels.
------------------------------------------------------------------------

module Data.List.Run where

open import Data.List.Base using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-reverse; reverse-involutive; unfold-reverse)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

private variable
  v ℓ : Level

module _ {V : Set v} {L : Set ℓ} (step : V → L → Maybe V) where

  -- Follow the labels from a source vertex, failing as soon as a step is undefined.
  runPath : V → List L → Maybe V
  runPath v []       = just v
  runPath v (l ∷ ls) with step v l
  ... | just w  = runPath w ls
  ... | nothing = nothing

  runPath-single : ∀ r l → runPath r (l ∷ []) ≡ step r l
  runPath-single r l with step r l
  ... | just w  = refl
  ... | nothing = refl

  -- Fixing the head transition unfolds one step.
  runPath-step : ∀ v l w ls → step v l ≡ just w → runPath v (l ∷ ls) ≡ runPath w ls
  runPath-step v l w ls eq with step v l | eq
  ... | just w' | refl = refl

  runPath-nothing : ∀ v l ls → step v l ≡ nothing → runPath v (l ∷ ls) ≡ nothing
  runPath-nothing v l ls eq with step v l | eq
  ... | nothing | refl = refl

  -- Head decomposition of a successful run.
  runPath-cons-inv : ∀ r l ls t → runPath r (l ∷ ls) ≡ just t
                   → Σ V λ w → (step r l ≡ just w) × (runPath w ls ≡ just t)
  runPath-cons-inv r l ls t e with step r l | e
  ... | just w | e' = w , refl , e'

  -- The last step of a snoc-run.
  runPath-snoc-inv : ∀ r ls l t → runPath r (ls ++ (l ∷ [])) ≡ just t
                   → Σ V λ w → (runPath r ls ≡ just w) × (step w l ≡ just t)
  runPath-snoc-inv r []        l t e = r , refl , trans (sym (runPath-single r l)) e
  runPath-snoc-inv r (l0 ∷ ls) l t e =
    let c = runPath-cons-inv r l0 (ls ++ (l ∷ [])) t e
        s = runPath-snoc-inv (proj₁ c) ls l t (proj₂ (proj₂ c))
    in proj₁ s
     , trans (runPath-step r l0 (proj₁ c) ls (proj₁ (proj₂ c))) (proj₁ (proj₂ s))
     , proj₂ (proj₂ s)

  -- In a CO-DETERMINISTIC system (in-degree ≤ 1: a transition's target
  -- determines its source and its label), equal-length runs from the same
  -- source to the same target carry the same labels.
  module _ (codet : ∀ {v l v' l' w} → step v l ≡ just w → step v' l' ≡ just w
                  → (v , l) ≡ (v' , l')) where

    private
      -- Co-determinism identifies the LAST label, so the induction is driven by
      -- the REVERSED label lists.
      rev : ∀ {r t} (rs rs' : List L) → length rs ≡ length rs'
          → runPath r (reverse rs) ≡ just t → runPath r (reverse rs') ≡ just t
          → rs ≡ rs'
      rev []      []       _ _ _ = refl
      rev []      (_ ∷ _)  ()
      rev (_ ∷ _) []       ()
      rev {r} {t} (x ∷ xs) (y ∷ ys) len e e' = cong₂ _∷_ (cong proj₂ last)
        (rev xs ys (suc-injective len) ru (trans ru' (cong just (sym (cong proj₁ last)))))
        where
        unsnoc : ∀ (z : L) (zs : List L) → runPath r (reverse (z ∷ zs)) ≡ just t
               → Σ V λ w → (runPath r (reverse zs) ≡ just w) × (step w z ≡ just t)
        unsnoc z zs eq = runPath-snoc-inv r (reverse zs) z t
          (subst (λ ls → runPath r ls ≡ just t) (unfold-reverse z zs) eq)

        u  = unsnoc x xs e
        u' = unsnoc y ys e'
        ru  = proj₁ (proj₂ u)
        ru' = proj₁ (proj₂ u')
        last = codet (proj₂ (proj₂ u)) (proj₂ (proj₂ u'))

    unique-run : ∀ {r t} (ls ls' : List L) → length ls ≡ length ls'
               → runPath r ls ≡ just t → runPath r ls' ≡ just t → ls ≡ ls'
    unique-run {r} {t} ls ls' len e e' =
      trans (sym (reverse-involutive ls))
            (trans (cong reverse (rev (reverse ls) (reverse ls')
                      (trans (length-reverse ls) (trans len (sym (length-reverse ls'))))
                      (unrev ls e) (unrev ls' e')))
                   (reverse-involutive ls'))
      where
      unrev : ∀ zs → runPath r zs ≡ just t → runPath r (reverse (reverse zs)) ≡ just t
      unrev zs = subst (λ ws → runPath r ws ≡ just t) (sym (reverse-involutive zs))

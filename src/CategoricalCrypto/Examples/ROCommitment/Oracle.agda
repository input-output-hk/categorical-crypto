{-# OPTIONS --safe --without-K #-}

-- The lazily sampled oracle the two closed `F_com` games run on.
--
-- A tabulated point is answered from the table; a fresh one draws a uniform
-- digest and keeps it.  The two games hold that table inside different states,
-- so the kernel takes the embedding `g` of the post-table into the game's own
-- state: `fetchT id` is the bare table `Hiding.Game` reads, `fetchT (_, m)` the
-- table-plus-ancilla `Game` does.  Taking `g` rather than mapping the result
-- afterwards is what keeps the kernel REDUCING under the games' `E-bind`
-- rewrites — a `Dmap` in front of it would not.
--
-- `fetchT-hit`/`fetchT-miss` are the two shapes it reduces to once the lookup
-- is known, and `fetchT-sup` is what one query leaves behind, for a hop that
-- has to know which of the two happened at a point of the support.

open import Data.List.Base using (_∷_)
open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Vec)

module CategoricalCrypto.Examples.ROCommitment.Oracle (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k

fetchT : {A : Set} → (Tbl → A) → Tbl → Pt → Dist-ℚ (A × Dig)
fetchT g t x with lookupPt t x
... | just d  = return-ℚ (g t , d)
... | nothing = uniform-Vec k >>=ᴹ λ h → return-ℚ (g ((x , h) ∷ t) , h)

fetchT-hit : {A : Set} (g : Tbl → A) (t : Tbl) (x : Pt) (d : Dig)
           → lookupPt t x ≡ just d → fetchT g t x ≡ return-ℚ (g t , d)
fetchT-hit g t x d eq rewrite eq = refl

fetchT-miss : {A : Set} (g : Tbl → A) (t : Tbl) (x : Pt) → lookupPt t x ≡ nothing
            → fetchT g t x ≡ (uniform-Vec k >>=ᴹ λ h → return-ℚ (g ((x , h) ∷ t) , h))
fetchT-miss g t x eq rewrite eq = refl

-- Either the point was tabulated and nothing moved, or it was fresh and the
-- post-table is the old one plus it.
fetchT-sup : (t : Tbl) (x : Pt)
           → OnSupport (λ u → (proj₁ u ≡ t × lookupPt t x ≡ just (proj₂ u))
                            ⊎ (proj₁ u ≡ (x , proj₂ u) ∷ t × lookupPt t x ≡ nothing))
                       (fetchT id t x)
fetchT-sup t x with lookupPt t x
... | just d  = OnSupport-return (inj₁ (refl , refl))
... | nothing = OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k)
                  (λ h → return-ℚ ((x , h) ∷ t , h))
                  (ListAll.universal (λ _ → tt) (NE.toList (entries (uniform-Vec k))))
                  (λ h _ → OnSupport-return (inj₂ (refl , refl)))

{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Matsumoto: reduced words with equal value are `~ʷ`-equal (induction on
-- the first word, using the exchange engine `bring-to-front`).
------------------------------------------------------------------------
module Categories.PermuteCoherence.InsertProofMatsumoto where

open import Data.Nat.Base using (ℕ; suc; _≤_; _<_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using ([]; _∷_)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; ≈-fb-sym; ≈-fb-trans)
open import Categories.PermuteCoherence.Word
  using (Word; evalW; _~ʷ_; ~refl; ~trans; ∷c; ~ʷ⇒≈; genFB-cancelˡ)
open import Categories.PermuteCoherence.Inversions using (inv)
open import Categories.PermuteCoherence.InversionsCong using (inv-resp-≈; inv-id)
open import Categories.PermuteCoherence.ExchangeBase
  using (Reduced; descent; descent-resp-≈; inv-di)
open import Categories.PermuteCoherence.BringToFront using (bring-to-front)
open import Categories.PermuteCoherence.InsertProofBase

private
  variable
    n : ℕ

matsumoto : (v w : Word n) → Reduced v → Reduced w → evalW v ≈-fb evalW w → v ~ʷ w
matsumoto {n} []   w rv rw he =
  subst (λ z → [] ~ʷ z)
        (sym (len≡0→[] w (trans rw (trans (inv-resp-≈ {b = evalW w} {b′ = evalW {n} []}
                                                      (≈-fb-sym {b = evalW {n} []} {b′ = evalW w} he))
                                          (inv-id {n})))))
        ~refl
matsumoto {suc n} (i ∷ v′) w rv rw he =
  ~trans (∷c refl (matsumoto v′ w′ rv′ rw′
                            (≈-fb-sym {b = evalW w′} {b′ = evalW v′} he′))) i∷w′~ʷw
  where
  dr : descent i (evalW (i ∷ v′)) × Reduced v′
  dr = reduced-head i v′ rv
  bf : Σ[ w′ ∈ Word _ ] ((i ∷ w′) ~ʷ w) × Reduced w′
  bf = bring-to-front w i rw
         (descent-resp-≈ {j = i} {x = evalW (i ∷ v′)} {y = evalW w} he (proj₁ dr))
  w′       = proj₁ bf
  i∷w′~ʷw  = proj₁ (proj₂ bf)
  rw′      = proj₂ (proj₂ bf)
  rv′      = proj₂ dr
  -- evalW w′ ≈ evalW v′, cancelling `genFB i` on the left.
  he′ : evalW w′ ≈-fb evalW v′
  he′ = genFB-cancelˡ i {b = evalW w′} {b′ = evalW v′}
          (≈-fb-trans {b = evalW (i ∷ w′)} {b′ = evalW w} {b″ = evalW (i ∷ v′)}
                   (~ʷ⇒≈ i∷w′~ʷw) (≈-fb-sym {b = evalW (i ∷ v′)} {b′ = evalW w} he))


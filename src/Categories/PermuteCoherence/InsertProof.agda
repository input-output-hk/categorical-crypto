{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The Insertion Lemma, from the exchange condition + Matsumoto:
--   insert-thm : canonW (genFB i ∘-fb b) ~ʷ i ∷ canonW b
-- Also hosts `straightenW` (it needs `insert-thm`), which is what lets
-- `Word` drop the `insert` postulate.
------------------------------------------------------------------------
module Categories.PermuteCoherence.InsertProof where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using ([]; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; _∘-fb_; ≈-fb-sym; ≈-fb-trans)
open import Categories.PermuteCoherence.Word
  using (Word; canonW; evalW; eval-canonW; genFB; genFB∘genFB; _~ʷ_; ~sym; ~trans; ∷c; c1; ~ʷ⇒≈; canonW-id; ∷-cong)
open import Categories.PermuteCoherence.InversionsCong using (inv-resp-≈)
open import Categories.PermuteCoherence.ExchangeBase
  using (Reduced; descent; descent-resp-≈; inv-di; canonW-reduced)
open import Categories.PermuteCoherence.BringToFront using (bring-to-front)
open import Categories.PermuteCoherence.InsertProofMatsumoto using (matsumoto)

private
  variable
    n : ℕ

insert-thm : (i : Fin n) (b : FinBij (suc n) (suc n))
           → canonW (genFB i ∘-fb b) ~ʷ i ∷ canonW b
insert-thm {zero} ()
insert-thm {suc n} i b with inv-di i b
... | inj₁ asc =
  matsumoto (canonW (genFB i ∘-fb b)) (i ∷ canonW b)
            (canonW-reduced (genFB i ∘-fb b))
            (trans (cong suc (trans (canonW-reduced b)
                                    (inv-resp-≈ {b = evalW (canonW b)} {b′ = b}
                                                (eval-canonW b))))
                   (sym (trans (inv-resp-≈ {b = genFB i ∘-fb evalW (canonW b)}
                                           {b′ = genFB i ∘-fb b}
                                           (λ p → cong (genFB i P.⟨$⟩ʳ_) (eval-canonW b p)))
                               asc)))
            (≈-fb-trans {b = evalW (canonW (genFB i ∘-fb b))} {b′ = genFB i ∘-fb b}
                     {b″ = genFB i ∘-fb evalW (canonW b)}
                     (eval-canonW (genFB i ∘-fb b))
                     (≈-fb-sym {b = genFB i ∘-fb evalW (canonW b)} {b′ = genFB i ∘-fb b}
                            (λ p → cong (genFB i P.⟨$⟩ʳ_) (eval-canonW b p))))
... | inj₂ dsc = ~sym
  (~trans (~trans (∷c refl (~sym i∷w′~ʷcb)) (c1 i))
          (matsumoto w′ (canonW (genFB i ∘-fb b)) rw′
                     (canonW-reduced (genFB i ∘-fb b))
                     (≈-fb-trans {b = evalW w′} {b′ = genFB i ∘-fb b}
                              {b″ = evalW (canonW (genFB i ∘-fb b))}
                              evalw′≈
                              (≈-fb-sym {b = evalW (canonW (genFB i ∘-fb b))} {b′ = genFB i ∘-fb b}
                                     (eval-canonW (genFB i ∘-fb b))))))
  where
  bf : Σ[ w′ ∈ Word _ ] ((i ∷ w′) ~ʷ canonW b) × Reduced w′
  bf = bring-to-front (canonW b) i (canonW-reduced b)
                      (descent-resp-≈ {j = i} {x = b} {y = evalW (canonW b)}
                                    (≈-fb-sym {b = evalW (canonW b)} {b′ = b} (eval-canonW b)) dsc)
  w′        = proj₁ bf
  i∷w′~ʷcb  = proj₁ (proj₂ bf)
  rw′       = proj₂ (proj₂ bf)
  -- evalW w′ ≈ genFB i ∘-fb b
  evalw′≈ : evalW w′ ≈-fb (genFB i ∘-fb b)
  evalw′≈ = ≈-fb-trans {b = evalW w′} {b′ = genFB i ∘-fb (genFB i ∘-fb evalW w′)}
                    {b″ = genFB i ∘-fb b}
                    (≈-fb-sym {b = genFB i ∘-fb (genFB i ∘-fb evalW w′)} {b′ = evalW w′}
                           (genFB∘genFB i (evalW w′)))
                    (λ p → cong (genFB i P.⟨$⟩ʳ_)
                                (≈-fb-trans {b = evalW (i ∷ w′)} {b′ = evalW (canonW b)} {b″ = b}
                                         (~ʷ⇒≈ i∷w′~ʷcb) (eval-canonW b) p))

------------------------------------------------------------------------
-- Straightening: every word is `~ʷ` its bubble-sort canonical form, by
-- induction on the word using `insert-thm` at the head.

straightenW : (w : Word n) → w ~ʷ canonW (evalW w)
straightenW []      = ~sym canonW-id
straightenW (i ∷ w) =
  ~trans (∷-cong i (straightenW w))
         (~sym (insert-thm i (evalW w)))

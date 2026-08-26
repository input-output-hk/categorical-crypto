{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The Insertion Lemma, by a direct Lehmer peel:
--   insert-thm : canonW (genFB i ∘-fb b) ~ʷ i ∷ canonW b
--
-- Proved by the peel machinery of `LehmerStaircase` + `LehmerRotate`:
-- recurse on the ambient size, casing the generator index `i`:
--
--   * `i = fsuc i′`: structural, uses the induction hypothesis.
--   * `i = 0F`:      IH-free, closed by `crux-core` (whose combinatorial
--                    core are the staircase identities).
--
-- Also hosts `straightenW` (its sole consumer is `FaithfulnessInductive`).
------------------------------------------------------------------------
module Categories.PermuteCoherence.Coxeter.InsertProof where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
open import Data.List.Base using ([]; _∷_; _++_)
import Data.Fin.Permutation as P
open P using (remove)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Coxeter.EvalSoundness
  using (cons-fb-functor-comp; cons-fb-functor-id)
open import Categories.PermuteCoherence.Coxeter.Word
open import Categories.PermuteCoherence.Coxeter.LehmerRotate

private
  variable
    n N : ℕ

------------------------------------------------------------------------
-- Base building blocks.

-- `cons-fb X ≈ id` for `X : FinBij 1 1`: `Fin 1` is a singleton, so `X`
-- is the identity, and `cons-fb` preserves that.
cons-fin1-id : (X : FinBij 1 1) → cons-fb X ≈-fb id-fb
cons-fin1-id X = ≈-fb-trans {b = cons-fb X} {b′ = cons-fb id-fb} {b″ = id-fb}
                   (cons-fb-cong fin1-id) cons-fb-functor-id
  where
  fin1-unique : (k : Fin 1) → k ≡ 0F
  fin1-unique 0F = refl
  fin1-id : X ≈-fb id-fb
  fin1-id j = trans (fin1-unique (X P.⟨$⟩ʳ j)) (sym (fin1-unique j))

------------------------------------------------------------------------
-- The `i = 0F` crux.
--
-- `crux1 X m` peels `X` (via `Word.peel`) and dispatches to `crux-core`;
-- the size-0 base is a direct computation.

crux1 : (X : FinBij (suc N) (suc N)) (m : Fin (suc (suc N)))
      → canonW (swap-fb N ∘-fb (cons-fb X ∘-fb rotate-fb m))
        ~ʷ (0F ∷ (liftW (canonW X) ++ rotateW m))
crux1 {zero} X m =
  ~trans (canonW-resp-≈
            {b = swap-fb 0 ∘-fb (cons-fb X ∘-fb rotate-fb m)}
            {b′ = swap-fb 0 ∘-fb rotate-fb m}
            (λ j → cong (swap-fb 0 P.⟨$⟩ʳ_) (cons-fin1-id X (rotate-fb m P.⟨$⟩ʳ j))))
         (base m)
  where
  base : (k : Fin 2) → canonW (swap-fb 0 ∘-fb rotate-fb k) ~ʷ (0F ∷ rotateW k)
  base 0F = ~refl
  base (fsuc 0F) =
    ~trans (canonW-resp-≈
              {b = swap-fb 0 ∘-fb rotate-fb (fsuc 0F)} {b′ = id-fb {n = 2}}
              eq-id)
           (~trans canonW-id (~sym (c1 0F)))
    where
    -- swap ∘ rotate-fb 1 ≈ id (concrete `Fin 2` computation).
    eq-id : (swap-fb 0 ∘-fb rotate-fb (fsuc 0F)) ≈-fb id-fb {n = 2}
    eq-id 0F       = refl
    eq-id (fsuc 0F) = refl
crux1 {suc n} X m =
  ~trans (canonW-resp-≈
            {b = swap-fb (suc n) ∘-fb (cons-fb X ∘-fb rotate-fb m)}
            {b′ = swap-fb (suc n) ∘-fb (cons-fb (cons-fb Z ∘-fb rotate-fb r)
                                        ∘-fb rotate-fb m)}
            (λ j → cong (swap-fb (suc n) P.⟨$⟩ʳ_)
                        (cons-fb-cong (peel X) (rotate-fb m P.⟨$⟩ʳ j))))
         (crux-core Z r m (mkGlue r m))
  where
  r = X P.⟨$⟩ˡ 0F
  Z = remove 0F (X ∘-fb inv-fb (rotate-fb r))

------------------------------------------------------------------------
-- The Insertion Lemma.  The `0F` clause is stated only here: `genFB 0F`
-- IS `swap-fb`, so a separately named `crux` would just restate this
-- clause's own goal.

insert-thm : (i : Fin n) (b : FinBij (suc n) (suc n))
           → canonW (genFB i ∘-fb b) ~ʷ i ∷ canonW b
insert-thm {suc n} 0F        b =
  ~trans (canonW-resp-≈
            {b = swap-fb n ∘-fb b}
            {b′ = swap-fb n ∘-fb (cons-fb rest-b ∘-fb rotate-fb m)}
            (λ j → cong (swap-fb n P.⟨$⟩ʳ_) (peel b j)))
         (crux1 rest-b m)
  where
  m      = b P.⟨$⟩ˡ 0F
  rest-b = remove 0F (b ∘-fb inv-fb (rotate-fb m))
insert-thm {suc n} (fsuc i′) b =
  ~trans (canonW-resp-≈
            {b = cons-fb (genFB i′) ∘-fb b}
            {b′ = cons-fb (genFB i′ ∘-fb rest-b) ∘-fb rotate-fb m}
            fac)
    (~trans (canonW-cons-rotate (genFB i′ ∘-fb rest-b) m)
            (++c-r (rotateW m) (lift~ (insert-thm i′ rest-b))))
  where
  m      = b P.⟨$⟩ˡ 0F
  rest-b = remove 0F (b ∘-fb inv-fb (rotate-fb m))
  -- genFB (fsuc i′) ∘ b ≈ cons-fb (genFB i′ ∘ rest-b) ∘ rotate-fb m.
  fac : (cons-fb (genFB i′) ∘-fb b)
        ≈-fb (cons-fb (genFB i′ ∘-fb rest-b) ∘-fb rotate-fb m)
  fac j =
    trans (cong (cons-fb (genFB i′) P.⟨$⟩ʳ_) (peel b j))
          (sym (cons-fb-functor-comp (genFB i′) rest-b
                  (rotate-fb m P.⟨$⟩ʳ j)))

------------------------------------------------------------------------
-- Straightening: every word is `~ʷ` its bubble-sort canonical form, by
-- induction on the word using `insert-thm` at the head.

straightenW : (w : Word n) → w ~ʷ canonW (evalW w)
straightenW []      = ~sym canonW-id
straightenW (i ∷ w) =
  ~trans (∷-cong i (straightenW w))
         (~sym (insert-thm i (evalW w)))

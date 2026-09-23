{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Interchange stress benchmark for the monoidal coherence solver.
--
-- For each size `n`, over an arbitrary monoidal category `C` with `n` object
-- atoms and `n` endo-generators `gᵢ : Aᵢ → Aᵢ`, this pins
--
--     solveMor! revStack fwdStack
--
-- where `fwdStack` composes the `n` one-box layers `id ⊗ … ⊗ gᵢ ⊗ … ⊗ id` in
-- ascending order and `revStack` in descending order.  The boxes are pairwise
-- disjoint and ranked `rank (genᵢ) = i`, so ascending is the canonical order and
-- normalising `revStack` fires ~n(n−1)/2 genuine adjacent interchange swaps —
-- no ambiguous / equal-rank pairs.
--
-- The pin goes through the public entry point, so it elaborates the transport
-- of the witness into `C`; the explicit `{_}` is what forces `decide?F` itself
-- to run, and that cost is the thing under test.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.InterchangeStress where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; lookup; tabulate)

open import Data.Fin
open import Data.Vec using (Vec; lookup; tabulate)

open import Categories.Category using (_[_,_])
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core
import Categories.Coherence.Monoidal as Coh

------------------------------------------------------------------------
-- Size n = 6: 6 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~15 interchange swaps;
-- `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size6 {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (vars : Vec (C .MonoidalCategory.Obj) 6)
  (gᴹ : (i : Fin 6) → C .MonoidalCategory.U [ lookup vars i , lookup vars i ])
  where

  open Coh.MorAtoms C vars
  open Coh.MorSolve C vars (tabulate {n = 6} λ i → (V i , V i) , gᴹ i)

  W : ObjTerm
  W = (V zero ⊗ᵒ (V (suc zero) ⊗ᵒ (V (suc (suc zero)) ⊗ᵒ (V (suc (suc (suc zero))) ⊗ᵒ (V (suc (suc (suc (suc zero)))) ⊗ᵒ V (suc (suc (suc (suc (suc zero))))))))))

  fwdStack : S.HomTerm W W
  fwdStack = (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc zero))))))))))

  revStack : S.HomTerm W W
  revStack = (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc zero))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))
            S.∘ (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))

  -- the pin: ≈15 swaps decided, and the witness transported into `C`.
  _ = solveMor! revStack fwdStack {_}

------------------------------------------------------------------------
-- Size n = 10: 10 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~45 interchange swaps;
-- `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size10 {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (vars : Vec (C .MonoidalCategory.Obj) 10)
  (gᴹ : (i : Fin 10) → C .MonoidalCategory.U [ lookup vars i , lookup vars i ])
  where

  open Coh.MorAtoms C vars
  open Coh.MorSolve C vars (tabulate {n = 10} λ i → (V i , V i) , gᴹ i)

  W : ObjTerm
  W = (V zero ⊗ᵒ (V (suc zero) ⊗ᵒ (V (suc (suc zero)) ⊗ᵒ (V (suc (suc (suc zero))) ⊗ᵒ (V (suc (suc (suc (suc zero)))) ⊗ᵒ (V (suc (suc (suc (suc (suc zero))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc zero)))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc zero))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⊗ᵒ V (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))

  fwdStack : S.HomTerm W W
  fwdStack = (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc zero))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc zero)))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc zero))))))) S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))

  revStack : S.HomTerm W W
  revStack = (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc zero))))))) S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc zero)))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc zero))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))
            S.∘ (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))

  -- the pin: ≈45 swaps decided, and the witness transported into `C`.
  _ = solveMor! revStack fwdStack {_}

------------------------------------------------------------------------
-- Size n = 14: 14 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~91 interchange swaps;
-- `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size14 {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (vars : Vec (C .MonoidalCategory.Obj) 14)
  (gᴹ : (i : Fin 14) → C .MonoidalCategory.U [ lookup vars i , lookup vars i ])
  where

  open Coh.MorAtoms C vars
  open Coh.MorSolve C vars (tabulate {n = 14} λ i → (V i , V i) , gᴹ i)

  W : ObjTerm
  W = (V zero ⊗ᵒ (V (suc zero) ⊗ᵒ (V (suc (suc zero)) ⊗ᵒ (V (suc (suc (suc zero))) ⊗ᵒ (V (suc (suc (suc (suc zero)))) ⊗ᵒ (V (suc (suc (suc (suc (suc zero))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc zero)))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc zero))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ⊗ᵒ (V (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ⊗ᵒ V (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))

  fwdStack : S.HomTerm W W
  fwdStack = (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc zero))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc zero)))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc zero))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))

  revStack : S.HomTerm W W
  revStack = (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc (suc zero))))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc (suc zero)))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc (suc zero))))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc (suc zero)))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc (suc zero))) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ (gen (suc (suc zero)) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))
            S.∘ (gen zero S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ (S.id S.⊗₁ S.id)))))))))))))

  -- the pin: ≈91 swaps decided, and the witness transported into `C`.
  _ = solveMor! revStack fwdStack {_}

------------------------------------------------------------------------
-- Correctness negative: `fwdStack` vs `fwdStack ∘ layer₀` (g₀ applied
-- twice) is a genuine non-equation, soundly rejected (`≡ nothing`).
--
-- This one stays on the internal front-end: `≡ nothing` is a statement about
-- `decide?F`, which no public solver exposes.
------------------------------------------------------------------------

module Neg where

  open FreeMonoidalHelper Mon (Fin 3)

  arity : Fin 3 → ObjTerm × ObjTerm
  arity i = Var i , Var i

  private module FS = FinSig {Fin 3} arity
  open FS
  open Frontend {Fin 3} GenS
  open Decide rankS

  W : ObjTerm
  W = (Var zero ⊗₀ (Var (suc zero) ⊗₀ Var (suc (suc zero))))

  layer₀ : S.HomTerm W W
  layer₀ = (gen zero S.⊗₁ (S.id S.⊗₁ S.id))

  fwdStack : S.HomTerm W W
  fwdStack = (gen zero S.⊗₁ (S.id S.⊗₁ S.id))
            S.∘ (S.id S.⊗₁ (gen (suc zero) S.⊗₁ S.id))
            S.∘ (S.id S.⊗₁ (S.id S.⊗₁ gen (suc (suc zero))))

  neg-extra-g₀ : decide?F fwdStack (fwdStack S.∘ layer₀) ≡ nothing
  neg-extra-g₀ = refl

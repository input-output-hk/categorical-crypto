{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Interchange STRESS benchmark for the monoidal coherence solver front-end.
--
-- For each size `n` this pins a positive decision
--
--     revStack ≈ fwdStack
--
-- where `fwdStack` composes the `n` one-box layers `id ⊗ … ⊗ gᵢ ⊗ … ⊗ id`
-- (each `gᵢ : Var i → Var i`, so ALL boxes are pairwise disjoint) in ASCENDING
-- order and `revStack` in DESCENDING order.  Because the generators are ranked
-- `rank (genᵢ) = i`, ascending IS the canonical order, so normalising the
-- descending `revStack` fires ~n(n−1)/2 genuine adjacent interchange swaps —
-- no ambiguous / equal-rank pairs.
--
-- The pin is `IsJust (decide?F revStack fwdStack)`, `_ = _`; the `IsJust`
-- forces the whole decision procedure to run at typecheck time.  THAT is the
-- benchmark.  Drives the internal decision kernel (`FinSig` / `Frontend` /
-- `Decide`) directly, wired from a `FinSig` signature exactly as
-- `Test/Limitations.agda` does it — the kernel's typecheck cost is the thing
-- under test.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.InterchangeStress where

open import categorical-crypto.Prelude
  hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin
open import Data.Maybe.Ext

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Core

------------------------------------------------------------------------
-- Size n = 6: 6 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~15 interchange swaps
-- inside `decide?F`.  `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size6 where

  open FreeMonoidalHelper Mon (Fin 6)

  arity : Fin 6 → ObjTerm × ObjTerm
  arity i = Var i , Var i

  private module FS = FinSig Mon {Fin 6} arity
  open FS
  open Frontend {Fin 6} GenS
  open Decide rankS

  W : ObjTerm
  W = (Var zero ⊗₀ (Var (suc zero) ⊗₀ (Var (suc (suc zero)) ⊗₀ (Var (suc (suc (suc zero))) ⊗₀ (Var (suc (suc (suc (suc zero)))) ⊗₀ Var (suc (suc (suc (suc (suc zero))))))))))

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

  -- POSITIVE PIN: forces the whole decision (≈15 swaps) at typecheck time.
  _ : IsJust (decide?F revStack fwdStack)
  _ = _

------------------------------------------------------------------------
-- Size n = 10: 10 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~45 interchange swaps
-- inside `decide?F`.  `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size10 where

  open FreeMonoidalHelper Mon (Fin 10)

  arity : Fin 10 → ObjTerm × ObjTerm
  arity i = Var i , Var i

  private module FS = FinSig Mon {Fin 10} arity
  open FS
  open Frontend {Fin 10} GenS
  open Decide rankS

  W : ObjTerm
  W = (Var zero ⊗₀ (Var (suc zero) ⊗₀ (Var (suc (suc zero)) ⊗₀ (Var (suc (suc (suc zero))) ⊗₀ (Var (suc (suc (suc (suc zero)))) ⊗₀ (Var (suc (suc (suc (suc (suc zero))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc zero)))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc zero))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⊗₀ Var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))

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

  -- POSITIVE PIN: forces the whole decision (≈45 swaps) at typecheck time.
  _ : IsJust (decide?F revStack fwdStack)
  _ = _

------------------------------------------------------------------------
-- Size n = 14: 14 pairwise-disjoint endo-boxes.  `revStack` (descending)
-- sorts into ascending canonical order, firing ~91 interchange swaps
-- inside `decide?F`.  `fwdStack` (ascending) is already canonical.
------------------------------------------------------------------------

module Size14 where

  open FreeMonoidalHelper Mon (Fin 14)

  arity : Fin 14 → ObjTerm × ObjTerm
  arity i = Var i , Var i

  private module FS = FinSig Mon {Fin 14} arity
  open FS
  open Frontend {Fin 14} GenS
  open Decide rankS

  W : ObjTerm
  W = (Var zero ⊗₀ (Var (suc zero) ⊗₀ (Var (suc (suc zero)) ⊗₀ (Var (suc (suc (suc zero))) ⊗₀ (Var (suc (suc (suc (suc zero)))) ⊗₀ (Var (suc (suc (suc (suc (suc zero))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc zero)))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc zero))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) ⊗₀ (Var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) ⊗₀ Var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))

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

  -- POSITIVE PIN: forces the whole decision (≈91 swaps) at typecheck time.
  _ : IsJust (decide?F revStack fwdStack)
  _ = _

------------------------------------------------------------------------
-- Correctness negative: `fwdStack` vs `fwdStack ∘ layer₀` (g₀ applied
-- twice) is a genuine non-equation, soundly rejected (`≡ nothing`).
------------------------------------------------------------------------

module Neg where

  open FreeMonoidalHelper Mon (Fin 3)

  arity : Fin 3 → ObjTerm × ObjTerm
  arity i = Var i , Var i

  private module FS = FinSig Mon {Fin 3} arity
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


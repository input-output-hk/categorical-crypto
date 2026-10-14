{-# OPTIONS --safe --without-K --guardedness #-}

-- Force/step clauses specialize CSP/Operators.agda:474–634 at
-- input-output-hk/agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e.
-- ExtI's used tags are reindexed constructively; B itself remains arbitrary.
-- Outside-sync overlap retains the source's post-event internal commitment.
open import Data.Bool.Base
module CategoricalCrypto.CSP.NativeOperators (E B : Set) (sync : E → Bool) where

open import Data.Maybe.Base
open import Data.Unit.Base

open import CategoricalCrypto.CSP.NativeIndex E B public
import CategoricalCrypto.CSP.Process as P

open P E Index ⊤
open Tree

viewV : Node → E → Maybe Tree
viewV (react v _) = v
viewV _ _ = nothing

viewT : Node → Index → Maybe Tree
viewT (react _ b) = b
viewT (sil t) silence = just t
viewT (sil _) _ = nothing
viewT (ret _) _ = nothing

mutual
  par-choice : Tree → Tree → Tree → Tree → Index → Maybe Tree
  par-choice p q p′ q′ (commitment false) = just (Par p′ q)
  par-choice p q p′ q′ (commitment true) = just (Par p q′)
  par-choice p q p′ q′ _ = nothing

  par-visible-result : Bool → Maybe Tree → Maybe Tree → Tree → Tree → Maybe Tree
  par-visible-result true (just p′) (just q′) p q = just (Par p′ q′)
  par-visible-result true _ _ p q = nothing
  par-visible-result false (just p′) (just q′) p q = just (ptree (react (λ _ → nothing) (par-choice p q p′ q′)))
  par-visible-result false (just p′) nothing p q = just (Par p′ q)
  par-visible-result false nothing (just q′) p q = just (Par p q′)
  par-visible-result false nothing nothing p q = nothing

  par-visible : Node → Node → Tree → Tree → E → Maybe Tree
  par-visible np nq p q e = par-visible-result (sync e) (viewV np e) (viewV nq e) p q

  par-map-left : Tree → Maybe Tree → Maybe Tree
  par-map-left q nothing = nothing
  par-map-left q (just p′) = just (Par p′ q)

  par-map-right : Tree → Maybe Tree → Maybe Tree
  par-map-right p nothing = nothing
  par-map-right p (just q′) = just (Par p q′)

  par-silent : Node → Node → Tree → Tree → Index → Maybe Tree
  par-silent np nq p q (left i) = par-map-left q (viewT np i)
  par-silent np nq p q (right i) = par-map-right p (viewT nq i)
  par-silent np nq p q _ = nothing

  par-ret-left-visible : Tree → (E → Maybe Tree) → E → Maybe Tree
  par-ret-left-visible p v e with sync e | v e
  ... | false | just q′ = just (Par p q′)
  ... | _ | _ = nothing

  par-ret-left-silent : Tree → (Index → Maybe Tree) → Index → Maybe Tree
  par-ret-left-silent p b i = par-map-right p (b i)

  par-ret-right-visible : (E → Maybe Tree) → Tree → E → Maybe Tree
  par-ret-right-visible v q e with sync e | v e
  ... | false | just p′ = just (Par p′ q)
  ... | _ | _ = nothing

  par-ret-right-silent : (Index → Maybe Tree) → Tree → Index → Maybe Tree
  par-ret-right-silent b q i = par-map-left q (b i)

  par-force : Node → Node → Tree → Tree → Node
  par-force (ret tt) (ret tt) p q = ret tt
  par-force (ret tt) (sil q′) p q = sil (Par p q′)
  par-force (sil p′) (ret tt) p q = sil (Par p′ q)
  par-force (ret tt) (react v b) p q = react (par-ret-left-visible p v) (par-ret-left-silent p b)
  par-force (react v b) (ret tt) p q = react (par-ret-right-visible v q) (par-ret-right-silent b q)
  par-force np nq p q = react (par-visible np nq p q) (par-silent np nq p q)

  Par : Tree → Tree → Tree
  force (Par p q) = par-force (force p) (force q) p q


mutual
  hide-map : (E → Bool) → Maybe Tree → Maybe Tree
  hide-map hide nothing = nothing
  hide-map hide (just p′) = just (Hide hide p′)

  hide-result : (E → Bool) → Bool → Maybe Tree → Maybe Tree
  hide-result hide true t = hide-map hide t
  hide-result hide false t = nothing

  hide-visible : (E → Bool) → Node → E → Maybe Tree
  hide-visible hide node e = hide-result hide (not (hide e)) (viewV node e)

  hide-silent : (E → Bool) → Node → Index → Maybe Tree
  hide-silent hide node (left i) = hide-map hide (viewT node i)
  hide-silent hide node (right (concealed e)) = hide-result hide (hide e) (viewV node e)
  hide-silent hide node _ = nothing

  hide-force : (E → Bool) → Node → Node
  hide-force hide (ret tt) = ret tt
  hide-force hide (sil p′) = sil (Hide hide p′)
  hide-force hide node@(react _ _) = react (hide-visible hide node) (hide-silent hide node)

  Hide : (E → Bool) → Tree → Tree
  force (Hide hide p) = hide-force hide (force p)

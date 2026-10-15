{-# OPTIONS --safe --without-K --guardedness #-}

-- Process permits countably infinite root branching into finite paths of
-- unbounded length. Raw observation inclusion does not imply hiding
-- congruence. No compactness or choice principle is used here.
module CategoricalCrypto.CSP.RawHidingBoundary where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.NativeRefinement as Native

module N = Native ⊤ ℕ (λ _ → true)
open N.O
open N.L
open N.L.Tree

rank : Index → ℕ
rank (raw n) = n
rank _ = zero

loop : Tree
force loop = react (λ _ → just loop) (λ _ → nothing)

walk : ℕ → Tree
walk zero = stop
force (walk (suc n)) = react (λ _ → just (walk n)) (λ _ → nothing)

finite-choice : Tree
finite-choice = menu (λ _ → nothing) (λ i → just (walk (rank i)))

word : ℕ → List Visible
word zero = []
word (suc n) = event tt ∷ word n

loop-noτ : ∀ {t} → loop ─[ τ ]→ t → ⊥
loop-noτ (sSil ())
loop-noτ (sTau refl ())

walk-noτ : ∀ n {t} → walk n ─[ τ ]→ t → ⊥
walk-noτ zero = stop-no-step
walk-noτ (suc n) (sSil ())
walk-noτ (suc n) (sTau refl ())

loop-path : ∀ {xs t} → Executes loop xs t → xs ≡ word (length xs)
loop-path done = refl
loop-path (silent-step step rest) = ⊥-elim (loop-noτ step)
loop-path (visible-step (sRet ()) rest)
loop-path (visible-step {e = event tt} (sVis refl refl) rest) = cong (event tt ∷_) (loop-path rest)

walk-path : ∀ n {xs t} → Executes (walk n) xs t → xs ≡ word (length xs)
walk-path zero done = refl
walk-path zero (silent-step step rest) = ⊥-elim (stop-no-step step)
walk-path zero (visible-step step rest) = ⊥-elim (stop-no-step step)
walk-path (suc n) done = refl
walk-path (suc n) (silent-step step rest) = ⊥-elim (walk-noτ (suc n) step)
walk-path (suc n) (visible-step (sRet ()) rest)
walk-path (suc n) (visible-step {e = event tt} (sVis refl refl) rest) = cong (event tt ∷_) (walk-path n rest)

choice-path : ∀ {xs t} → Executes finite-choice xs t → xs ≡ word (length xs)
choice-path done = refl
choice-path (silent-step (sSil ()) rest)
choice-path (silent-step (sTau {i = i} refl refl) rest) = walk-path (rank i) rest
choice-path (visible-step (sRet ()) rest)
choice-path (visible-step (sVis refl ()) rest)

walk-executes : ∀ n → Executes (walk n) (word n) stop
walk-executes zero = done
walk-executes (suc n) = visible-step (sVis refl refl) (walk-executes n)

loop-executes : ∀ n → Executes loop (word n) loop
loop-executes zero = done
loop-executes (suc n) = visible-step (sVis refl refl) (loop-executes n)

choice-executes : ∀ n → Executes finite-choice (word n) stop
choice-executes n = silent-step (sTau {i = raw n} refl refl) (walk-executes n)

same-traces : ∀ xs → (Trace finite-choice xs → Trace loop xs) × (Trace loop xs → Trace finite-choice xs)
same-traces xs =
  (λ { (t , path) → loop , subst (λ ys → Executes loop ys loop) (sym (choice-path path)) (loop-executes (length xs)) }) ,
  (λ { (t , path) → stop , subst (λ ys → Executes finite-choice ys stop) (sym (loop-path path)) (choice-executes (length xs)) })

failure-inclusion : ∀ xs refusal → Failure loop xs refusal → Failure finite-choice xs refusal
failure-inclusion xs refusal (t , path , refused) = stop ,
  subst (λ ys → Executes finite-choice ys stop) (sym (loop-path path)) (choice-executes (length xs)) ,
  stable-stop , (λ _ _ _ → stop-no-step)

walk-no-divergence : ∀ n {xs} → ¬ (Divergence (walk n) xs)
walk-no-divergence zero (_ , done , d) = stop-not-divergent d
walk-no-divergence zero (_ , silent-step step rest , d) = stop-no-step step
walk-no-divergence zero (_ , visible-step step rest , d) = stop-no-step step
walk-no-divergence (suc n) (_ , done , d) = walk-noτ (suc n) (Diverges.step d)
walk-no-divergence (suc n) (_ , silent-step step rest , d) = walk-noτ (suc n) step
walk-no-divergence (suc n) (_ , visible-step (sRet ()) rest , d)
walk-no-divergence (suc n) (_ , visible-step (sVis refl refl) rest , d) = walk-no-divergence n (_ , rest , d)

loop-no-divergence : ∀ {xs} → ¬ (Divergence loop xs)
loop-no-divergence (_ , done , d) = loop-noτ (Diverges.step d)
loop-no-divergence (_ , silent-step step rest , d) = loop-noτ step
loop-no-divergence (_ , visible-step (sRet ()) rest , d)
loop-no-divergence (_ , visible-step (sVis refl refl) rest , d) = loop-no-divergence (_ , rest , d)

choice-no-diverges : ¬ (Diverges finite-choice)
choice-no-diverges d = reject (Diverges.step d) (Diverges.rest d)
  where
  reject : ∀ {t} → finite-choice ─[ τ ]→ t → Diverges t → ⊥
  reject (sSil ()) tail
  reject (sTau {i = i} refl refl) tail = walk-noτ (rank i) (Diverges.step tail)

choice-no-divergence : ∀ {xs} → ¬ (Divergence finite-choice xs)
choice-no-divergence (_ , done , d) = choice-no-diverges d
choice-no-divergence (_ , silent-step (sSil ()) rest , d)
choice-no-divergence (_ , silent-step (sTau {i = i} refl refl) rest , d) = walk-no-divergence (rank i) (_ , rest , d)
choice-no-divergence (_ , visible-step (sRet ()) rest , d)
choice-no-divergence (_ , visible-step (sVis refl ()) rest , d)

divergence-inclusion : ∀ xs → Divergence loop xs → Divergence finite-choice xs
divergence-inclusion xs divergence = ⊥-elim (loop-no-divergence divergence)

hide-all : Tree → Tree
hide-all = Hide (λ _ → true)

hidden-loop-diverges : Diverges (hide-all loop)
Diverges.next hidden-loop-diverges = hide-all loop
Diverges.step hidden-loop-diverges = N.P.hide-hidden (λ _ → true) refl (sVis refl refl)
Diverges.rest hidden-loop-diverges = hidden-loop-diverges

hidden-walk-no-diverges : ∀ n → ¬ (Diverges (hide-all (walk n)))
hidden-walk-no-diverges n d = reject (N.P.hide-silent-invert (λ _ → true) (Diverges.step d)) (Diverges.rest d)
  where
  reject : ∀ {t} → N.P.HideSilent (λ _ → true) (walk n) t → Diverges t → ⊥
  reject (N.P.original step) tail = walk-noτ n step
  reject (N.P.concealed-event inside step) tail = finite n step tail
    where
    finite : ∀ n {e t} → walk n ─[ visible (event e) ]→ t → Diverges (hide-all t) → ⊥
    finite zero step tail = stop-no-step step
    finite (suc n) (sVis refl refl) tail = hidden-walk-no-diverges n tail

hidden-choice-no-diverges : ¬ (Diverges (hide-all finite-choice))
hidden-choice-no-diverges d = reject (N.P.hide-silent-invert (λ _ → true) (Diverges.step d)) (Diverges.rest d)
  where
  reject : ∀ {t} → N.P.HideSilent (λ _ → true) finite-choice t → Diverges t → ⊥
  reject (N.P.original (sSil ())) tail
  reject (N.P.original (sTau {i = i} refl refl)) tail = hidden-walk-no-diverges (rank i) tail
  reject (N.P.concealed-event inside (sVis refl ())) tail

hidden-choice-no-exact-divergence : ¬ (Divergence (hide-all finite-choice) [])
hidden-choice-no-exact-divergence (t , path , d) = hidden-choice-no-diverges (N.R.silent-prefix-diverges path d)

hiding-breaks-raw-inclusion : ¬ (∀ xs → Divergence (hide-all loop) xs → Divergence (hide-all finite-choice) xs)
hiding-breaks-raw-inclusion inclusion = hidden-choice-no-exact-divergence
  (inclusion [] (hide-all loop , done , hidden-loop-diverges))

-- Failure of the stronger ready rule is deliberate: the finite-choice root
-- enables τ, whereas loop does not. The raw inclusion above cannot replace it.
not-ready-refinement : ¬ (N.R._⊑_ finite-choice loop)
not-ready-refinement ref = let t , step = N.R._⊑_.ready ref (walk zero , sTau {i = raw zero} refl refl)
  in loop-noτ step

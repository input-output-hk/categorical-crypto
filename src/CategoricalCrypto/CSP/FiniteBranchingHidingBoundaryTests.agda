{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.FiniteBranchingHidingBoundaryTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (finite; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base
open import Data.Product.Base hiding (map)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles using (_↣_; mk↣)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.FiniteBranching as Branching
open import CategoricalCrypto.CSP.FiniteBranchingHidingBoundary
import CategoricalCrypto.CSP.FloodedObservation as Flooding
import CategoricalCrypto.CSP.RawHidingBoundary as Old

open L
open L.Tree
open F
module Flood = Flooding Event O.Index ⊤
open Flood

visible-alphabet : List Visible
visible-alphabet = event a ∷ event b ∷ √ tt ∷ []

visible-alphabet-covers : ∀ e → e ∈ visible-alphabet
visible-alphabet-covers (event a) = here refl
visible-alphabet-covers (event b) = there (here refl)
visible-alphabet-covers (√ tt) = there (there (here refl))

binary-selector-size : ∀ n → length (FiniteSteps.successors (select-finite n)) ≡ 2
binary-selector-size n = refl

both-processes-totally-finitely-branching : FinitelyBranching spec × FinitelyBranching impl
both-processes-totally-finitely-branching = spec-branching , impl-branching

tick-enumeration : FiniteSteps (return tt)
FiniteSteps.successors tick-enumeration = (visible (√ tt) , stop) ∷ []
FiniteSteps.sound tick-enumeration (here refl) = sRet refl
FiniteSteps.sound tick-enumeration (there ())
FiniteSteps.cover tick-enumeration (sRet refl) = here refl
FiniteSteps.cover tick-enumeration (sSil ())
FiniteSteps.cover tick-enumeration (sVis () offered)
FiniteSteps.cover tick-enumeration (sTau () offered)

tick-is-covered : (visible (√ tt) , stop) ∈ FiniteSteps.successors tick-enumeration
tick-is-covered = FiniteSteps.cover tick-enumeration (sRet refl)

raw-traces : ∀ xs → Trace impl xs → Trace spec xs
raw-traces = trace-inclusion

raw-failures : ∀ xs refusal → Failure impl xs refusal → Failure spec xs refusal
raw-failures = failure-inclusion

raw-divergences : ∀ xs → Divergence impl xs → Divergence spec xs
raw-divergences = divergence-inclusion

hidden-exact-divergence-distinction : Divergence (hidden impl) (event b ∷ [])
  × ¬ (Divergence (hidden spec) (event b ∷ []))
hidden-exact-divergence-distinction = hidden-impl-exact-b , hidden-spec-no-exact-b

source-diverges-only-before-b : Divergence spec [] × (∀ n → ¬ (Divergence spec (event b ∷ word n)))
source-diverges-only-before-b = spec-diverges-at-empty , spec-no-exact-b-prefix

finite-branching-does-not-preserve-exact-hiding :
  ¬ (∀ xs → Divergence (hidden impl) xs → Divergence (hidden spec) xs)
finite-branching-does-not-preserve-exact-hiding = hiding-breaks-exact-divergence-inclusion

flooded-traces : ∀ xs → FloodedTrace impl xs → FloodedTrace spec xs
flooded-traces = flooded-trace-inclusion trace-inclusion divergence-inclusion

flooded-failures : ∀ xs refusal → FloodedFailure impl xs refusal → FloodedFailure spec xs refusal
flooded-failures = flooded-failure-inclusion failure-inclusion divergence-inclusion

flooded-divergences : ∀ xs → FloodedDivergence impl xs → FloodedDivergence spec xs
flooded-divergences = flooded-divergence-inclusion divergence-inclusion

hidden-select-diverges : ∀ n → Diverges (hidden (select n))
Diverges.next (hidden-select-diverges n) = hidden (select (suc n))
Diverges.step (hidden-select-diverges n) = P.hide-silent-step hide-a (sTau {i = O.raw false} refl refl)
Diverges.rest (hidden-select-diverges n) = hidden-select-diverges (suc n)

hidden-empty-divergence : Divergence (hidden spec) []
hidden-empty-divergence = hidden spec , done , hidden-select-diverges zero

-- The same [b] used to refute exact inclusion is admitted by flooding from [].
empty-divergence-floods-b : FloodedDivergence (hidden spec) (event b ∷ [])
empty-divergence-floods-b = flooded-divergence-extend
  (raw-divergence hidden-empty-divergence) (event-tail empty)

exact-counterexample-does-not-separate-flooded-b :
  ¬ (Divergence (hidden spec) (event b ∷ [])) × FloodedDivergence (hidden spec) (event b ∷ [])
exact-counterexample-does-not-separate-flooded-b = hidden-spec-no-exact-b , empty-divergence-floods-b

private
  div-no-visible : ∀ {e t} → ¬ (div ─[ visible e ]→ t)
  div-no-visible (sRet ())
  div-no-visible (sVis () offered)

  div-no-nonempty-path : ∀ {e xs t} → ¬ (Executes div (e ∷ xs) t)
  div-no-nonempty-path (silent-step (sSil refl) rest) = div-no-nonempty-path rest
  div-no-nonempty-path (silent-step (sTau () offered) rest)
  div-no-nonempty-path (visible-step step rest) = div-no-visible step

  flooded-div-b : FloodedDivergence div (event b ∷ [])
  flooded-div-b = flooded-divergence-extend
    (raw-divergence (div , done , divergent-div)) (event-tail empty)

flooding-strictly-adds-divergence : FloodedDivergence div (event b ∷ []) × ¬ (Divergence div (event b ∷ []))
flooding-strictly-adds-divergence = flooded-div-b , λ { (_ , path , _) → div-no-nonempty-path path }

flooding-strictly-adds-traces : FloodedTrace div (event b ∷ []) × ¬ (Trace div (event b ∷ []))
flooding-strictly-adds-traces = inj₂ flooded-div-b , λ { (_ , path) → div-no-nonempty-path path }

flooding-strictly-adds-failures : ∀ refusal → FloodedFailure div (event b ∷ []) refusal
  × ¬ (Failure div (event b ∷ []) refusal)
flooding-strictly-adds-failures refusal = inj₂ flooded-div-b , λ { (_ , path , _) → div-no-nonempty-path path }

legal-tick-flooding : FloodedDivergence div (√ tt ∷ [])
legal-tick-flooding = flooded-divergence-extend (raw-divergence (div , done , divergent-div)) tick-last

tick-forbids-further-flooded-events : ¬ (FloodedDivergence div (√ tt ∷ event b ∷ []))
tick-forbids-further-flooded-events = no-flooding-after-tick

tick-forbids-further-flooded-traces : ¬ (FloodedTrace div (√ tt ∷ event b ∷ []))
tick-forbids-further-flooded-traces trace = no-event-after-tick (flooded-trace-legal trace)

tick-forbids-further-flooded-failures : ∀ refusal → ¬ (FloodedFailure div (√ tt ∷ event b ∷ []) refusal)
tick-forbids-further-flooded-failures refusal failure = no-event-after-tick (flooded-failure-legal failure)

tick-cannot-be-repeated : ¬ (FloodedDivergence div (√ tt ∷ √ tt ∷ []))
tick-cannot-be-repeated (_ , _ , _ , _ , ())

flooding-twice-adds-no-divergences : ∀ p xs →
  DivergenceClosure (FloodedDivergence p) xs → FloodedDivergence p xs
flooding-twice-adds-no-divergences p xs = closure-idempotent

flooded-divergence-survives-reclosure : ∀ p xs →
  FloodedDivergence p xs → DivergenceClosure (FloodedDivergence p) xs
flooded-divergence-survives-reclosure p xs d = closure-embed d (flooded-divergence-legal d)

hidden-flooding-is-total-on-legal-words : ∀ xs → Legal xs → FloodedDivergence (hidden spec) xs
hidden-flooding-is-total-on-legal-words xs legal =
  flooded-divergence-extend (raw-divergence hidden-empty-divergence) legal

hidden-flooded-traces-still-included : ∀ xs → FloodedTrace (hidden impl) xs → FloodedTrace (hidden spec) xs
hidden-flooded-traces-still-included xs trace =
  inj₂ (hidden-flooding-is-total-on-legal-words xs (flooded-trace-legal trace))

hidden-flooded-failures-still-included : ∀ xs refusal →
  FloodedFailure (hidden impl) xs refusal → FloodedFailure (hidden spec) xs refusal
hidden-flooded-failures-still-included xs refusal failure =
  inj₂ (hidden-flooding-is-total-on-legal-words xs (flooded-failure-legal failure))

hidden-flooded-divergences-still-included : ∀ xs →
  FloodedDivergence (hidden impl) xs → FloodedDivergence (hidden spec) xs
hidden-flooded-divergences-still-included xs d =
  hidden-flooding-is-total-on-legal-words xs (flooded-divergence-legal d)

module OL = Old.N.L
module OO = Old.N.O
module OldBranching = Branching ⊤ OO.Index ⊤

old-visible-alphabet : List OL.Visible
old-visible-alphabet = OL.event tt ∷ OL.√ tt ∷ []

old-visible-alphabet-covers : ∀ e → e ∈ old-visible-alphabet
old-visible-alphabet-covers (OL.event tt) = here refl
old-visible-alphabet-covers (OL.√ tt) = there (here refl)

private
  observe : OL.Tree → Maybe OL.Tree
  observe p = OO.viewV (OL.Tree.force p) tt

  old-walk-injective : ∀ {n m} → Old.walk n ≡ Old.walk m → n ≡ m
  old-walk-injective {zero} {zero} eq = refl
  old-walk-injective {zero} {suc m} eq with cong observe eq
  ... | ()
  old-walk-injective {suc n} {zero} eq with cong observe eq
  ... | ()
  old-walk-injective {suc n} {suc m} eq = cong suc (old-walk-injective (just-injective (cong observe eq)))

  old-walk-injection : ℕ ↣ OL.Tree
  old-walk-injection = mk↣ old-walk-injective

old-root-no-finite-tau-cover : ¬ (Σ (List OL.Tree) λ targets →
  ∀ {t} → OL._─[_]→_ Old.finite-choice OL.τ t → t ∈ targets)
old-root-no-finite-tau-cover (targets , cover) = finite old-walk-injection targets
  (λ n → cover (OL.sTau {i = OO.raw n} refl refl))

old-root-not-totally-finite : ¬ (OldBranching.FiniteSteps Old.finite-choice)
old-root-not-totally-finite certificate = old-root-no-finite-tau-cover
  (Data.List.Base.map proj₂ (OldBranching.FiniteSteps.successors certificate) ,
    λ step → ∈-map⁺ proj₂ (OldBranching.FiniteSteps.cover certificate step))

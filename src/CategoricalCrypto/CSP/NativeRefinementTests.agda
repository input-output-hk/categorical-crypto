{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeRefinementTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes)

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → ⊤)
open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → ⊤)
open import CategoricalCrypto.CSP.ObservationRefinement ⊤ (λ _ → ⊤) using (_⊑ᴼ_)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → ⊤)
open import CategoricalCrypto.CSP.Plugging ⊤ (λ _ → ⊤)
import CategoricalCrypto.CSP.NativeContextRefinement as Context
import CategoricalCrypto.CSP.NativeInterchangeRefinement as Interchange
import CategoricalCrypto.CSP.ReadyRefinementTests as Strict
import CategoricalCrypto.CSP.RawHidingBoundary as Boundary
import CategoricalCrypto.CSP.Testing as Testing
open import CategoricalCrypto.UC.Core using (Evaluation)

module C = Context ⊤ Bool
module L = C.C.L
module R = C.F.R
module N = C.F.F.N
module Verdict = Testing ⊤ (λ _ → ⊤) (λ { tt tt → yes refl }) I
open L
open L.Tree
open R

communicate : Tree
communicate = menu (λ _ → just (return tt)) (λ _ → nothing)

specification implementation : Tree
specification = menu (λ _ → nothing) choose
  where
  choose : C.C.O.Index → Maybe Tree
  choose (C.C.O.raw false) = just communicate
  choose (C.C.O.raw true) = just div
  choose _ = nothing
implementation = silent communicate

branch-elimination : specification ⊑ implementation
_⊑_.match branch-elimination (sSil refl) = communicate , sTau {i = C.C.O.raw false} refl refl , reflexive
_⊑_.ready branch-elimination (t , sRet ())
_⊑_.ready branch-elimination (t , sSil ())
_⊑_.ready branch-elimination (t , sVis refl ())
_⊑_.ready branch-elimination (t , sTau refl offered) = communicate , sSil refl

actual-test : Verdict.Test C.out
actual-test = C.consumer communicate

contextual-refinement : observations (actual-test ∘ C.producer specification)
  ⊑ᴼ observations (actual-test ∘ C.producer implementation)
contextual-refinement = C.consumer-refinement branch-elimination communicate

module Pair = C.Plugged communicate communicate
module View = C.A.View Pair.family
module K = Execution Pair.network
module O = Observe Pair.network

hidden-handshake : Pair.Closed.native Pair.family ─[ τ ]→ C.C.O.Hide (λ _ → true) (C.C.O.Par (return tt) (return tt))
hidden-handshake = N.P.hide-hidden (λ _ → true) refl (N.P.par-sync refl (sVis refl refl) (sVis refl refl))

native-success : Trace (Pair.Closed.native Pair.family) (√ tt ∷ [])
native-success = stop , silent-step hidden-handshake (visible-step (N.P.hide-return (λ _ → true) refl) done)

actual-hidden-communication-success : NativeObservation.traces
  (Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer communicate) actual-test)) (K.√ ∷ [])
actual-hidden-communication-success = proj₁ (_≈ᴼ_.traces Pair.flattening-observations (K.√ ∷ []))
  (View.trace-to-network (K.√ ∷ []) native-success)

actual-terminal-refusal : ∀ refusal → NativeObservation.failures
  (Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer communicate) actual-test)) (K.√ ∷ []) refusal
actual-terminal-refusal refusal = proj₁ (_≈ᴼ_.failures Pair.flattening-observations (K.√ ∷ []) refusal)
  (View.failure-to-network (K.√ ∷ []) refusal
    (stop , proj₂ native-success , stable-stop , (λ _ _ _ → stop-no-step)))

pull-is-plugging : Verdict.pull (C.producer communicate) actual-test ≡ Pair.network
pull-is-plugging = refl

blocked-test : Verdict.Test C.out
blocked-test = C.consumer stop

blocked-contextual-refinement : Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer specification) blocked-test)
  ⊑ᴼ Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer implementation) blocked-test)
blocked-contextual-refinement = C.consumer-refinement branch-elimination stop

module BlockedSpec = C.Plugged specification stop
module BlockedImpl = C.Plugged implementation stop
module SpecView = C.A.View BlockedSpec.family
module ImplView = C.A.View BlockedImpl.family

spinning : Diverges (C.C.O.Hide (λ _ → true) (C.C.O.Par div stop))
Diverges.next spinning = C.C.O.Hide (λ _ → true) (C.C.O.Par div stop)
Diverges.step spinning = N.P.hide-silent-step (λ _ → true) (N.P.par-left-silent (sSil refl))
Diverges.rest spinning = spinning

spec-context-diverges : NativeObservation.divergences
  (observations BlockedSpec.network) []
spec-context-diverges = proj₁ (_≈ᴼ_.divergences BlockedSpec.flattening-observations [])
  (SpecView.divergence-to-network []
    (_ , silent-step (N.P.hide-silent-step (λ _ → true) (N.P.par-left-silent
      (sTau {i = C.C.O.raw true} refl refl))) done , spinning))

blocked-noτ : ∀ {t} → C.C.O.Hide (λ _ → true) (C.C.O.Par communicate stop) ─[ τ ]→ t → ⊥
blocked-noτ step = reject (N.P.hide-silent-invert (λ _ → true) step)
  where
  original : ∀ {t} → N.P.SilentMove communicate stop t → ⊥
  original (N.P.left-silent (sSil ()))
  original (N.P.left-silent (sTau refl ()))
  original (N.P.right-silent step) = stop-no-step step
  hidden : ∀ {e t} → N.P.VisibleMove communicate stop e t → ⊥
  hidden (N.P.together inside sp sq) = stop-no-step sq
  hidden (N.P.only-left () sp)
  hidden (N.P.only-right () sq)
  reject : ∀ {t} → N.P.HideSilent (λ _ → true) (C.C.O.Par communicate stop) t → ⊥
  reject (N.P.original move) = original (N.P.par-silent-invert move)
  reject (N.P.concealed-event inside move) = hidden (N.P.par-visible-invert (λ ()) move)

impl-context-no-diverges : ¬ (Diverges (BlockedImpl.Closed.native BlockedImpl.family))
impl-context-no-diverges d = reject (N.P.hide-silent-invert (λ _ → true) (Diverges.step d)) (Diverges.rest d)
  where
  original : ∀ {t} → N.P.SilentMove implementation stop t → Diverges (C.C.O.Hide (λ _ → true) t) → ⊥
  original (N.P.left-silent (sSil refl)) tail = blocked-noτ (Diverges.step tail)
  original (N.P.right-silent step) tail = stop-no-step step
  hidden : ∀ {e t} → N.P.VisibleMove implementation stop e t → ⊥
  hidden (N.P.together inside sp sq) = stop-no-step sq
  hidden (N.P.only-left () sp)
  hidden (N.P.only-right () sq)
  reject : ∀ {t} → N.P.HideSilent (λ _ → true) (C.C.O.Par implementation stop) t → Diverges t → ⊥
  reject (N.P.original move) tail = original (N.P.par-silent-invert move) tail
  reject (N.P.concealed-event inside move) tail = hidden (N.P.par-visible-invert (λ ()) move)

impl-context-no-divergence : ¬ (NativeObservation.divergences (observations BlockedImpl.network) [])
impl-context-no-divergence divergence =
  let t , path , d = ImplView.divergence-to-native []
        (proj₂ (_≈ᴼ_.divergences BlockedImpl.flattening-observations []) divergence)
  in impl-context-no-diverges (silent-prefix-diverges path d)

strict-actual-context-inequality : ¬
  (Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer specification) blocked-test)
    ≈ᴼ Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer implementation) blocked-test))
strict-actual-context-inequality equality = impl-context-no-divergence
  (proj₁ (_≈ᴼ_.divergences equality []) spec-context-diverges)

module Quad = Interchange ⊤ Bool

supported-quad-refinement : ∀ (f g : Quad.I.Quad)
  → Quad.A.R._⊑_ (Quad.I.Quad.p₁ f) (Quad.I.Quad.p₁ g)
  → Quad.A.R._⊑_ (Quad.I.Quad.p₂ f) (Quad.I.Quad.p₂ g)
  → Quad.A.R._⊑_ (Quad.I.Quad.q₁ f) (Quad.I.Quad.q₁ g)
  → Quad.A.R._⊑_ (Quad.I.Quad.q₂ f) (Quad.I.Quad.q₂ g)
  → Quad.A.R._⊑_
      (Quad.I.A.Hide (λ _ → true) (Quad.I.left-source f))
      (Quad.I.A.Hide (λ _ → true) (Quad.I.right-source g))
supported-quad-refinement f g = Quad.hidden-link-refines {f} {g}

strict-one-way-is-not-raw-equality : ¬ (Strict.R.RawAgreement Strict.spec Strict.impl)
strict-one-way-is-not-raw-equality = Strict.not-raw-equality

raw-inclusion-is-not-hiding-congruence : ¬ (∀ xs → Boundary.N.L.Divergence (Boundary.hide-all Boundary.loop) xs
  → Boundary.N.L.Divergence (Boundary.hide-all Boundary.finite-choice) xs)
raw-inclusion-is-not-hiding-congruence = Boundary.hiding-breaks-raw-inclusion

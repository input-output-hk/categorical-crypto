{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ExtensionalHidingTests where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes)

import CategoricalCrypto.CSP.ExtensionalHiding as Extensional
import CategoricalCrypto.CSP.InfiniteObservation as Infinite
import CategoricalCrypto.CSP.NativeContextRefinement as Context
import CategoricalCrypto.CSP.NativeExtensionalHiding as Native
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Core
import CategoricalCrypto.CSP.Testing as Testing
open import CategoricalCrypto.UC.Core using (Evaluation)

-- Existing closed readout hides every communication. Productive external events
-- therefore have a separate selective-hide consumer, without extending that bridge.
module Productive where
  module O = Operators Bool ⊤ (λ _ → true)
  module L = Core Bool O.Index ⊤
  module H = Extensional Bool ⊤ (λ _ → true)
  module J = Infinite Bool ⊤ (λ _ → true)
  module M = H.Mask (λ b → b)
  open O
  open L
  open Tree

  mutual
    public-cycle hidden-cycle : Tree
    force public-cycle = react (λ { false → just hidden-cycle; true → nothing }) (λ _ → nothing)
    force hidden-cycle = react (λ { false → nothing; true → just public-cycle }) (λ _ → nothing)

  data Inv : Tree → Set where
    public-state : Inv public-cycle
    hidden-state : Inv hidden-cycle

  closed : ∀ {p q l} → Inv p → p ─[ l ]→ q → Inv q
  closed public-state (sRet ())
  closed public-state (sSil ())
  closed public-state (sTau refl ())
  closed public-state (sVis {e = false} refl refl) = hidden-state
  closed public-state (sVis {e = true} refl ())
  closed hidden-state (sRet ())
  closed hidden-state (sSil ())
  closed hidden-state (sTau refl ())
  closed hidden-state (sVis {e = false} refl ())
  closed hidden-state (sVis {e = true} refl refl) = public-state

  rank : ∀ {p} → Inv p → ℕ
  rank public-state = 0
  rank hidden-state = 1

  decreases : ∀ {p q l} (i : Inv p) (step : p ─[ l ]→ q)
    → M.Silent l → rank (closed i step) < rank i
  decreases public-state (sRet ()) inside
  decreases public-state (sSil ()) inside
  decreases public-state (sTau refl ()) inside
  decreases public-state (sVis {e = false} refl refl) ()
  decreases public-state (sVis {e = true} refl ()) inside
  decreases hidden-state (sRet ()) inside
  decreases hidden-state (sSil ()) inside
  decreases hidden-state (sTau refl ()) inside
  decreases hidden-state (sVis {e = false} refl ()) inside
  decreases hidden-state (sVis {e = true} refl refl) inside = s≤s z≤n

  progress : M.Progress public-cycle
  progress = record { Inv = Inv; starts = public-state; closed = closed; rank = rank; decreases = decreases }

  delayed-inclusion : H.RawInclusion (silent public-cycle) public-cycle
  H.RawInclusion.traces delayed-inclusion (q , path) = q , silent-step (sSil refl) path
  H.RawInclusion.failures delayed-inclusion (q , path , refusal) = q , silent-step (sSil refl) path , refusal
  H.RawInclusion.divergences delayed-inclusion (q , path , d) = q , silent-step (sSil refl) path , d

  selective-raw : H.RawInclusion (Hide (λ b → b) (silent public-cycle)) (Hide (λ b → b) public-cycle)
  selective-raw = M.ranked-hiding delayed-inclusion progress

  productive-labels : J.Labels
  J.Labels.head productive-labels = visible (event false)
  J.Labels.head (J.Labels.tail productive-labels) = visible (event true)
  J.Labels.tail (J.Labels.tail productive-labels) = productive-labels

  productive-run : J.Run public-cycle productive-labels
  J.Run.next productive-run = hidden-cycle
  J.Run.step productive-run = sVis refl refl
  J.Run.next (J.Run.rest productive-run) = public-cycle
  J.Run.step (J.Run.rest productive-run) = sVis refl refl
  J.Run.rest (J.Run.rest productive-run) = productive-run

  selective-labels : J.Labels
  J.Labels.head selective-labels = visible (event false)
  J.Labels.head (J.Labels.tail selective-labels) = τ
  J.Labels.tail (J.Labels.tail selective-labels) = selective-labels

  selective-productive-run : J.Run (Hide (λ b → b) public-cycle) selective-labels
  J.Run.next selective-productive-run = Hide (λ b → b) hidden-cycle
  J.Run.step selective-productive-run = H.P.hide-keep (λ b → b) refl (sVis refl refl)
  J.Run.next (J.Run.rest selective-productive-run) = Hide (λ b → b) public-cycle
  J.Run.step (J.Run.rest selective-productive-run) = H.P.hide-hidden (λ b → b) refl (sVis refl refl)
  J.Run.rest (J.Run.rest selective-productive-run) = selective-productive-run

  visible-resets-rank : rank (closed public-state (sVis {e = false} refl refl)) ≡ 1
  visible-resets-rank = refl

  no-exact-hidden-divergence : ∀ {xs} → ¬ (Divergence (Hide (λ b → b) public-cycle) xs)
  no-exact-hidden-divergence = M.Ranked.no-exact-divergence progress

module ResidualLoop where
  module O = Operators ⊤ ⊤ (λ _ → true)
  module L = Core ⊤ O.Index ⊤
  module H = Extensional ⊤ ⊤ (λ _ → true)
  module J = Infinite ⊤ ⊤ (λ _ → true)
  open O
  open L
  open Tree

  loop : Tree
  force loop = react (λ _ → just loop) (λ _ → nothing)

  finite : H.RawInclusion (silent loop) loop
  H.RawInclusion.traces finite (q , path) = q , silent-step (sSil refl) path
  H.RawInclusion.failures finite (q , path , refusal) = q , silent-step (sSil refl) path , refusal
  H.RawInclusion.divergences finite (q , path , d) = q , silent-step (sSil refl) path , d

  residual : ∀ {xs u} → J.Residual loop xs u → J.Residual (silent loop) xs u
  residual (q , path , run) = q , silent-step (sSil refl) path , run

  enriched-raw : H.RawInclusion (Hide (λ _ → true) (silent loop)) (Hide (λ _ → true) loop)
  enriched-raw = J.Mask.residual-hiding (λ _ → true) (H.RawInclusion.traces finite) (H.RawInclusion.failures finite) residual

  hidden-diverges : Diverges (Hide (λ _ → true) loop)
  Diverges.next hidden-diverges = Hide (λ _ → true) loop
  Diverges.step hidden-diverges = sTau {i = right (concealed tt)} refl refl
  Diverges.rest hidden-diverges = hidden-diverges

  transported-exact-divergence : Divergence (Hide (λ _ → true) (silent loop)) []
  transported-exact-divergence = H.RawInclusion.divergences enriched-raw (_ , done , hidden-diverges)

module Represented where
  open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → ⊤)
  open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → ⊤)
  open import CategoricalCrypto.CSP.ObservationRefinement ⊤ (λ _ → ⊤) using (_⊑ᴼ_)
  open import CategoricalCrypto.CSP.Plugging ⊤ (λ _ → ⊤)
  module C = Context ⊤ ⊤
  module N = Native ⊤ ⊤
  module H = N.H
  module M = N.M
  module L = N.C.L
  module P = N.C.P
  module O = N.C.O
  module Verdict = Testing ⊤ (λ _ → ⊤) (λ { tt tt → yes refl }) I
  open L
  open Tree

  communicate : Tree
  communicate = menu (λ _ → just (return tt)) (λ _ → nothing)

  spec impl finished : Tree
  spec = O.Par (silent communicate) communicate
  impl = O.Par communicate communicate
  finished = O.Par (return tt) (return tt)

  advance : spec ─[ τ ]→ impl
  advance = P.par-left-silent (sSil refl)

  before-hiding : H.RawInclusion spec impl
  H.RawInclusion.traces before-hiding (q , path) = q , silent-step advance path
  H.RawInclusion.failures before-hiding (q , path , refusal) = q , silent-step advance path , refusal
  H.RawInclusion.divergences before-hiding (q , path , d) = q , silent-step advance path , d

  impl-noτ : ∀ {q} → ¬ (impl ─[ τ ]→ q)
  impl-noτ step with P.par-silent-invert step
  ... | P.left-silent (sSil ())
  ... | P.left-silent (sTau refl ())
  ... | P.right-silent (sSil ())
  ... | P.right-silent (sTau refl ())

  not-ready : ¬ (C.F.R._⊑_ spec impl)
  not-ready ref = let q , move = C.F.R._⊑_.ready ref (impl , advance) in impl-noτ move

  data Inv : Tree → Set where
    initial-state : Inv impl
    finished-state : Inv finished
    stopped-state : Inv stop

  closed : ∀ {p q l} → Inv p → p ─[ l ]→ q → Inv q
  closed initial-state (sRet ())
  closed initial-state (sSil ())
  closed initial-state (sVis {e = tt , tt} refl refl) = finished-state
  closed initial-state step@(sTau _ _) = ⊥-elim (impl-noτ step)
  closed finished-state (sRet refl) = stopped-state
  closed finished-state (sSil ())
  closed finished-state (sVis () _)
  closed finished-state (sTau () _)
  closed stopped-state step = ⊥-elim (stop-no-step step)

  rank : ∀ {p} → Inv p → ℕ
  rank initial-state = 1
  rank finished-state = 0
  rank stopped-state = 0

  decreases : ∀ {p q l} (i : Inv p) (step : p ─[ l ]→ q)
    → M.Silent l → rank (closed i step) < rank i
  decreases initial-state (sRet ()) inside
  decreases initial-state (sSil ()) inside
  decreases initial-state (sVis {e = tt , tt} refl refl) inside = s≤s z≤n
  decreases initial-state step@(sTau _ _) inside = ⊥-elim (impl-noτ step)
  decreases finished-state (sRet refl) ()
  decreases finished-state (sSil ()) inside
  decreases finished-state (sVis () _) inside
  decreases finished-state (sTau () _) inside
  decreases stopped-state step inside = ⊥-elim (stop-no-step step)

  progress : M.Progress impl
  progress = record { Inv = Inv; starts = initial-state; closed = closed; rank = rank; decreases = decreases }

  module Spec = C.Plugged (silent communicate) communicate
  module Impl = C.Plugged communicate communicate
  module A = N.Admissible (N.C.one N.C.∙ N.C.one) C.pol (inj₁ tt) (inj₂ tt) refl C.only-producer refl (λ ())
  module SpecView = A.View Spec.family
  module ImplView = A.View Impl.family

  closed-refinement : observations Spec.Closed.network ⊑ᴼ observations Impl.Closed.network
  closed-refinement = A.ranked-refinement before-hiding progress

  actual-test : Verdict.Test C.out
  actual-test = C.consumer communicate

  actual-refinement : Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer (silent communicate)) actual-test)
    ⊑ᴼ Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer communicate) actual-test)
  actual-refinement = record
    { traces = λ xs path → proj₁ (_≈ᴼ_.traces Spec.flattening-observations xs)
        (_⊑ᴼ_.traces closed-refinement xs (proj₂ (_≈ᴼ_.traces Impl.flattening-observations xs) path))
    ; failures = λ xs refusal failure → proj₁ (_≈ᴼ_.failures Spec.flattening-observations xs refusal)
        (_⊑ᴼ_.failures closed-refinement xs refusal (proj₂ (_≈ᴼ_.failures Impl.flattening-observations xs refusal) failure))
    ; divergences = λ xs divergence → proj₁ (_≈ᴼ_.divergences Spec.flattening-observations xs)
        (_⊑ᴼ_.divergences closed-refinement xs (proj₂ (_≈ᴼ_.divergences Impl.flattening-observations xs) divergence)) }

  native-handshake : O.Hide (λ _ → true) impl ─[ τ ]→ O.Hide (λ _ → true) finished
  native-handshake = P.hide-hidden (λ _ → true) refl (P.par-sync refl (sVis refl refl) (sVis refl refl))

  native-success : Trace (O.Hide (λ _ → true) impl) (√ tt ∷ [])
  native-success = stop , silent-step native-handshake (visible-step (P.hide-return (λ _ → true) refl) done)

  actual-success : NativeObservation.traces
    (Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer (silent communicate)) actual-test)) (ImplView.K.√ ∷ [])
  actual-success = _⊑ᴼ_.traces actual-refinement (ImplView.K.√ ∷ [])
    (proj₁ (_≈ᴼ_.traces Impl.flattening-observations (ImplView.K.√ ∷ []))
      (ImplView.trace-to-network (ImplView.K.√ ∷ []) native-success))

  actual-terminal-refusals : ∀ refusal → NativeObservation.failures
    (Evaluation.read Verdict.evaluationᶜˢᵖ (Verdict.pull (C.producer (silent communicate)) actual-test)) (ImplView.K.√ ∷ []) refusal
  actual-terminal-refusals refusal = _⊑ᴼ_.failures actual-refinement (ImplView.K.√ ∷ []) refusal
    (proj₁ (_≈ᴼ_.failures Impl.flattening-observations (ImplView.K.√ ∷ []) refusal)
      (ImplView.failure-to-network (ImplView.K.√ ∷ []) refusal
        (stop , proj₂ native-success , stable-stop , (λ _ _ _ → stop-no-step))))

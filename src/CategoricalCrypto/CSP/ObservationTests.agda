{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ObservationTests where

open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.Tests as Kernel
open import CategoricalCrypto.CSP.Interface Bool Kernel.payload
open import CategoricalCrypto.CSP.Network Bool Kernel.payload
open import CategoricalCrypto.CSP.Observation Bool Kernel.payload
open import CategoricalCrypto.CSP.Operational Bool Kernel.payload
open import CategoricalCrypto.CSP.SingleBox Bool Kernel.payload
open import CategoricalCrypto.CSP.Testing Bool Kernel.payload _≟_ Kernel.out
open import CategoricalCrypto.UC.Core using (Evaluation)

source-visible : Labels.Visible I Kernel.out → Kernel.O.Visible
source-visible (Labels.event (inj₁ () , _))
source-visible (Labels.event (inj₂ i , x)) = Kernel.O.event (i , x)
source-visible Labels.√ = Kernel.O.√ tt

-- These lift source executions through the public single-box correspondence;
-- the readouts below are the actual Evaluation readouts, not mock predicates.
module Single (p₀ : Kernel.O.Tree) where
  module C = Embed.Correspondence Kernel.out ℕ p₀
  module V = C.Converse _≟_
  module E = Execution (Embed.network Kernel.out ℕ p₀)
  module O = Observe (Embed.network Kernel.out ℕ p₀)
  module P = Kernel.O

  visible : P.Visible → E.Visible
  visible (P.event (i , x)) = E.event (inj₂ i , x)
  visible (P.√ tt) = E.√

  native-visible : E.Visible → P.Visible
  native-visible = source-visible

  visible-label : ∀ e → C.step-label (P.visible e) ≡ E.visible (visible e)
  visible-label (P.event _) = refl
  visible-label (P.√ tt) = refl

  native-visible-label : ∀ e → C.native-label (E.visible e) ≡ P.visible (native-visible e)
  native-visible-label (E.event (inj₁ () , _))
  native-visible-label (E.event (inj₂ _ , _)) = refl
  native-visible-label E.√ = refl

  visible-roundtrip : ∀ xs → map visible (map native-visible xs) ≡ xs
  visible-roundtrip [] = refl
  visible-roundtrip (E.event (inj₁ () , _) ∷ xs)
  visible-roundtrip (E.event (inj₂ i , x) ∷ xs) = cong (_ ∷_) (visible-roundtrip xs)
  visible-roundtrip (E.√ ∷ xs) = cong (_ ∷_) (visible-roundtrip xs)

  native-step : ∀ {p q r l} → C.Related p q → P._─[_]→_ p l r
    → Σ E.Configuration (λ q′ → E._─[_]→_ q (C.step-label l) q′ × C.Related r q′)
  native-step (C.live _) (P.sRet eq) = _ , C.native-step (P.sRet eq) , C.settled
  native-step (C.live _) (P.sSil eq) = _ , C.native-step (P.sSil eq) , C.live _
  native-step (C.live _) (P.sVis eq offered) = _ , C.native-step (P.sVis eq offered) , C.live _
  native-step (C.live _) (P.sTau eq offered) = _ , C.native-step (P.sTau eq offered) , C.live _
  native-step C.settled step = ⊥-elim (P.stop-no-step step)

  network-step : ∀ {p q q′ l} → C.Related p q → E._─[_]→_ q l q′
    → Σ P.Tree (λ p′ → P._─[_]→_ p (C.native-label l) p′ × C.Related p′ q′)
  network-step (C.live _) step = V.network-step step
  network-step C.settled step = ⊥-elim (E.completed-no-step step)

  execute-native : ∀ {p q p′ xs} → C.Related p q → P.Executes p xs p′
    → Σ E.Configuration (λ q′ → O.Executes q (map visible xs) q′ × C.Related p′ q′)
  execute-native related P.done = _ , O.done , related
  execute-native related (P.silent-step step rest) =
    let q′ , matched , related′ = native-step related step
        q″ , path , final = execute-native related′ rest
    in q″ , O.silent-step matched path , final
  execute-native {q = q} related (P.visible-step {e = e} step rest) =
    let q′ , matched , related′ = native-step related step
        q″ , path , final = execute-native related′ rest
    in q″ , O.visible-step (subst (λ l → E._─[_]→_ q l q′) (visible-label e) matched) path , final

  execute-network : ∀ {p q q′ xs} → C.Related p q → O.Executes q xs q′
    → Σ P.Tree (λ p′ → P.Executes p (map native-visible xs) p′ × C.Related p′ q′)
  execute-network related O.done = _ , P.done , related
  execute-network related (O.silent-step step rest) =
    let p′ , matched , related′ = network-step related step
        p″ , path , final = execute-network related′ rest
    in p″ , P.silent-step matched path , final
  execute-network {p = p} related (O.visible-step {e = e} step rest) =
    let p′ , matched , related′ = network-step related step
        p″ , path , final = execute-network related′ rest
    in p″ , P.visible-step (subst (λ l → P._─[_]→_ p l p′) (native-visible-label e) matched) path , final

  trace-native : ∀ xs → P.Trace p₀ (map native-visible xs) → O.Trace E.initial-configuration xs
  trace-native xs (p , source) =
    let q , path , _ = execute-native (C.live p₀) source
    in q , subst (λ ys → O.Executes E.initial-configuration ys q) (visible-roundtrip xs) path

  trace-network : ∀ xs → O.Trace E.initial-configuration xs → P.Trace p₀ (map native-visible xs)
  trace-network xs (q , path) =
    let p , source , _ = execute-network (C.live p₀) path in p , source

  stable-network : ∀ {p q} → C.Related p q → P.Stable p → O.Stable q
  stable-network related (noτ , no√) =
    (λ q′ step → let p′ , matched , _ = network-step related step in noτ p′ matched) ,
    (λ q′ step → let p′ , matched , _ = network-step related step in no√ tt p′ matched)

  stable-native : ∀ {p q} → C.Related p q → O.Stable q → P.Stable p
  stable-native related (noτ , no√) =
    (λ p′ step → let q′ , matched , _ = native-step related step in noτ q′ matched) ,
    (λ { tt p′ step → let q′ , matched , _ = native-step related step in no√ q′ matched })

  stop-refuses : ∀ {q} → C.Related P.stop q → ∀ refusal → O.Refuses q refusal
  stop-refuses related refusal = stable-network related P.stable-stop ,
    (λ e member q′ step → let p′ , matched , _ = network-step related step in P.stop-no-step matched)

  divergence-native : ∀ {p q} → C.Related p q → P.Diverges p → E.Diverges q
  E.Diverges.next (divergence-native related d) = proj₁ (native-step related (P.Diverges.step d))
  E.Diverges.step (divergence-native related d) = proj₁ (proj₂ (native-step related (P.Diverges.step d)))
  E.Diverges.rest (divergence-native related d) = divergence-native
    (proj₂ (proj₂ (native-step related (P.Diverges.step d)))) (P.Diverges.rest d)

module P = Kernel.O

ready choice : P.Tree
ready = P.menu (λ _ → just P.stop) (λ _ → nothing)
choice = P.menu (λ _ → just P.stop) (λ _ → just P.stop)

ready-network choice-network deadlock-network divergence-network : Network I Kernel.out
ready-network = Embed.network Kernel.out ℕ ready
choice-network = Embed.network Kernel.out ℕ choice
deadlock-network = Embed.network Kernel.out ℕ P.stop
divergence-network = Embed.network Kernel.out ℕ P.div

module Ready = Single ready
module Choice = Single choice
module Deadlock = Single P.stop
module Divergence = Single P.div

stop-execution : ∀ {xs p} → P.Executes P.stop xs p → xs ≡ []
stop-execution P.done = refl
stop-execution (P.silent-step step rest) = ⊥-elim (P.stop-no-step step)
stop-execution (P.visible-step step rest) = ⊥-elim (P.stop-no-step step)

ready-no-silent : ∀ {q} → ¬ (P._─[_]→_ ready P.τ q)
ready-no-silent (P.sSil ())
ready-no-silent (P.sTau refl ())

ready-empty-execution : ∀ {p} → P.Executes ready [] p → p ≡ ready
ready-empty-execution P.done = refl
ready-empty-execution (P.silent-step step rest) = ⊥-elim (ready-no-silent step)

one-offer : List P.Visible → Set
one-offer xs = xs ≡ [] ⊎ Σ (Event Kernel.out) (λ e → xs ≡ P.event e ∷ [])

ready-traces : ∀ {xs p} → P.Executes ready xs p → one-offer xs
ready-traces P.done = inj₁ refl
ready-traces (P.silent-step step rest) = ⊥-elim (ready-no-silent step)
ready-traces (P.visible-step (P.sRet ()) rest)
ready-traces (P.visible-step (P.sVis {e = e} refl refl) rest) = inj₂ (e , cong (_ ∷_) (stop-execution rest))

choice-traces : ∀ {xs p} → P.Executes choice xs p → one-offer xs
choice-traces P.done = inj₁ refl
choice-traces (P.silent-step (P.sSil ()) rest)
choice-traces (P.silent-step (P.sTau refl refl) rest) = inj₁ (stop-execution rest)
choice-traces (P.visible-step (P.sRet ()) rest)
choice-traces (P.visible-step (P.sVis {e = e} refl refl) rest) = inj₂ (e , cong (_ ∷_) (stop-execution rest))

ready-realizes : ∀ {xs} → one-offer xs → P.Trace ready xs
ready-realizes (inj₁ refl) = ready , P.done
ready-realizes (inj₂ (e , refl)) = P.stop , P.visible-step (P.sVis refl refl) P.done

choice-realizes : ∀ {xs} → one-offer xs → P.Trace choice xs
choice-realizes (inj₁ refl) = choice , P.done
choice-realizes (inj₂ (e , refl)) = P.stop , P.visible-step (P.sVis refl refl) P.done

identical-traces : ∀ xs → (NativeObservation.traces (observations ready-network) xs
  → NativeObservation.traces (observations choice-network) xs)
  × (NativeObservation.traces (observations choice-network) xs
  → NativeObservation.traces (observations ready-network) xs)
identical-traces xs =
  (λ trace → let p , path = Ready.trace-network xs trace
             in Choice.trace-native xs (choice-realizes {xs = map Choice.native-visible xs}
               (ready-traces {xs = map Ready.native-visible xs} path))) ,
  (λ trace → let p , path = Choice.trace-network xs trace
             in Ready.trace-native xs (ready-realizes {xs = map Ready.native-visible xs}
               (choice-traces {xs = map Choice.native-visible xs} path)))

refuse-offer : Labels.Visible I Kernel.out → Set
refuse-offer e = e ≡ Labels.event (inj₂ tt , tt)

choice-refusal : NativeObservation.failures (observations choice-network) [] refuse-offer
choice-refusal =
  let q , step , related = Choice.native-step (Choice.C.live choice) (P.sTau {i = zero} refl refl)
  in q , Choice.O.silent-step step Choice.O.done , Choice.stop-refuses related refuse-offer

ready-not-refusal : ¬ (NativeObservation.failures (observations ready-network) [] refuse-offer)
ready-not-refusal (q , path , stable , refusal) =
  let p , source , related = Ready.execute-network (Ready.C.live ready) path
      eq = ready-empty-execution source
      q′ , step , _ = Ready.native-step related
        (subst (λ t → P._─[_]→_ t (P.visible (P.event (tt , tt))) P.stop) (sym eq) (P.sVis refl refl))
  in refusal (Labels.event (inj₂ tt , tt)) refl q′ step

different-stable-failures : ¬ (observations ready-network ≈ᴼ observations choice-network)
different-stable-failures eq = ready-not-refusal (proj₂ (_≈ᴼ_.failures eq [] refuse-offer) choice-refusal)

visible-trace : NativeObservation.traces (observations ready-network) (Labels.event (inj₂ tt , tt) ∷ [])
visible-trace = Ready.trace-native _ (P.stop , P.visible-step (P.sVis refl refl) P.done)

deadlock-no-visible-trace : ¬ (NativeObservation.traces (observations deadlock-network)
  (Labels.event (inj₂ tt , tt) ∷ []))
deadlock-no-visible-trace trace with Deadlock.trace-network _ trace
... | p , path with stop-execution path
... | ()

different-visible-traces : ¬ (observations ready-network ≈ᴼ observations deadlock-network)
different-visible-traces eq = deadlock-no-visible-trace (proj₁ (_≈ᴼ_.traces eq _) visible-trace)

div-execution : ∀ {xs p} → P.Executes P.div xs p → p ≡ P.div
div-execution P.done = refl
div-execution (P.silent-step (P.sSil refl) rest) = div-execution rest
div-execution (P.silent-step (P.sTau () _) rest)
div-execution (P.visible-step (P.sRet ()) rest)
div-execution (P.visible-step (P.sVis () _) rest)

divergence-observation : NativeObservation.divergences (observations divergence-network) []
divergence-observation = Divergence.E.initial-configuration , Divergence.O.done ,
  Divergence.divergence-native (Divergence.C.live P.div) P.divergent-div

deadlock-not-divergent : ¬ (NativeObservation.divergences (observations deadlock-network) [])
deadlock-not-divergent (q , path , d) =
  let p , source , related = Deadlock.execute-network (Deadlock.C.live P.stop) path
  in no-divergence source related d
  where
  no-divergence : ∀ {xs p q} → P.Executes P.stop xs p → Deadlock.C.Related p q → Deadlock.E.Diverges q → ⊥
  no-divergence P.done related d =
    let p′ , step , _ = Deadlock.network-step related (Deadlock.E.Diverges.step d) in P.stop-no-step step
  no-divergence (P.silent-step step rest) related d = P.stop-no-step step
  no-divergence (P.visible-step step rest) related d = P.stop-no-step step

different-divergence : ¬ (observations divergence-network ≈ᴼ observations deadlock-network)
different-divergence eq = deadlock-not-divergent (proj₁ (_≈ᴼ_.divergences eq []) divergence-observation)

deadlock-refusal : NativeObservation.failures (observations deadlock-network) [] (λ _ → ⊤)
deadlock-refusal = Deadlock.E.initial-configuration , Deadlock.O.done ,
  Deadlock.stop-refuses (Deadlock.C.live P.stop) (λ _ → ⊤)

divergence-no-refusal : ¬ (NativeObservation.failures (observations divergence-network) [] (λ _ → ⊤))
divergence-no-refusal (q , path , stable , refusal) =
  let p , source , related = Divergence.execute-network (Divergence.C.live P.div) path
      native-stable = Divergence.stable-native related stable
  in P.div-not-stable (subst P.Stable (div-execution source) native-stable)

evaluated-ready : Evaluation.read evaluationᶜˢᵖ ready-network ≡ observations ready-network
evaluated-ready = refl

evaluated-choice : Evaluation.read evaluationᶜˢᵖ choice-network ≡ observations choice-network
evaluated-choice = refl

evaluation-failure-separator : ¬ (Evaluation.read evaluationᶜˢᵖ ready-network ≈ᴼ Evaluation.read evaluationᶜˢᵖ choice-network)
evaluation-failure-separator = different-stable-failures

evaluation-trace-separator : ¬ (Evaluation.read evaluationᶜˢᵖ ready-network ≈ᴼ Evaluation.read evaluationᶜˢᵖ deadlock-network)
evaluation-trace-separator = different-visible-traces

evaluation-divergence-separator : ¬ (Evaluation.read evaluationᶜˢᵖ divergence-network ≈ᴼ Evaluation.read evaluationᶜˢᵖ deadlock-network)
evaluation-divergence-separator = different-divergence

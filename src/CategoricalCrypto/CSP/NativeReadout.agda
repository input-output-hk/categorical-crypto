{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeReadout (X B : Set) where

open import Data.Empty
open import Data.List.Base
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X) using (module Labels)
import CategoricalCrypto.CSP.NativeCorrespondence as Common

module C = Common X B
open C using (Nonempty; shape+; Family)
open C.L

module ClosedLabels = Labels I I

closed-decode : ClosedLabels.Visible → Visible
closed-decode ClosedLabels.√ = √ tt
closed-decode (ClosedLabels.event (inj₁ () , _))
closed-decode (ClosedLabels.event (inj₂ () , _))

module ClosedReadout (s : Nonempty) (pol : ⟨ shape+ s ⟩ → Polarity)
  (producer listener : ⟨ shape+ s ⟩) (producer-output : pol producer ≡ output)
  (only-producer : ∀ k → pol k ≡ output → k ≡ producer)
  (listener-input : pol listener ≡ input) (distinct : listener ≢ producer)
  (initial : Family s) where

  module Q = C.Closed s pol producer listener producer-output only-producer listener-input distinct initial
  module K = Q.K
  module O = Observe Q.network
  open Q using (Related; live; settled)

  encode : Visible → K.Visible
  encode _ = K.√

  decode : K.Visible → Visible
  decode = closed-decode

  roundtrip : ∀ xs → map encode (map decode xs) ≡ xs
  roundtrip [] = refl
  roundtrip (K.√ ∷ xs) = cong (K.√ ∷_) (roundtrip xs)
  roundtrip (K.event (inj₁ () , _) ∷ xs)
  roundtrip (K.event (inj₂ () , _) ∷ xs)

  encode-label : Label → K.Label
  encode-label τ = K.τ
  encode-label (visible e) = K.visible (encode e)

  decode-label : K.Label → Label
  decode-label K.τ = τ
  decode-label (K.visible e) = visible (decode e)

  native-step : ∀ {p c l t} → Related p c → p ─[ l ]→ t
    → Σ K.Configuration (λ c′ → K._─[_]→_ c (encode-label l) c′ × Related t c′)
  native-step related step = extract (Q.related-native-step related step)
    where
    extract : ∀ {c l t} → Σ K.Label (λ kl → Σ K.Configuration
      (λ c′ → Q.Matching l kl × K._─[_]→_ c kl c′ × Related t c′))
      → Σ K.Configuration (λ c′ → K._─[_]→_ c (encode-label l) c′ × Related t c′)
    extract (_ , c′ , Q.silent-label , move , next) = c′ , move , next
    extract (_ , c′ , Q.return-label , move , next) = c′ , move , next

  network-step : ∀ {p c kl c′} → Related p c → K._─[_]→_ c kl c′
    → Σ Tree (λ t → p ─[ decode-label kl ]→ t × Related t c′)
  network-step related step = extract (Q.related-network-step related step)
    where
    extract : ∀ {p kl c′} → Σ Label (λ l → Σ Tree
      (λ t → Q.Matching l kl × p ─[ l ]→ t × Related t c′))
      → Σ Tree (λ t → p ─[ decode-label kl ]→ t × Related t c′)
    extract (_ , t , Q.silent-label , move , next) = t , move , next
    extract (_ , t , Q.return-label , move , next) = t , move , next

  execute-native : ∀ {p c t xs} → Related p c → Executes p xs t
    → Σ K.Configuration (λ c′ → O.Executes c (map encode xs) c′ × Related t c′)
  execute-native related done = _ , O.done , related
  execute-native related (silent-step move rest) =
    let c′ , matched , next = native-step related move
        c″ , path , final = execute-native next rest
    in c″ , O.silent-step matched path , final
  execute-native related (visible-step move rest) =
    let c′ , matched , next = native-step related move
        c″ , path , final = execute-native next rest
    in c″ , O.visible-step matched path , final

  execute-network : ∀ {p c c′ xs} → Related p c → O.Executes c xs c′
    → Σ Tree (λ t → Executes p (map decode xs) t × Related t c′)
  execute-network related O.done = _ , done , related
  execute-network related (O.silent-step move rest) =
    let t , matched , next = network-step related move
        u , path , final = execute-network next rest
    in u , silent-step matched path , final
  execute-network related (O.visible-step move rest) =
    let t , matched , next = network-step related move
        u , path , final = execute-network next rest
    in u , visible-step matched path , final

  stable-native : ∀ {p c} → Related p c → O.Stable c → Stable p
  stable-native related (noτ , no√) =
    (λ t move → let c′ , matched , _ = native-step related move in noτ c′ matched) ,
    (λ { tt t move → let c′ , matched , _ = native-step related move in no√ c′ matched })

  stable-network : ∀ {p c} → Related p c → Stable p → O.Stable c
  stable-network related (noτ , no√) =
    (λ c′ move → let t , matched , _ = network-step related move in noτ t matched) ,
    (λ c′ move → let t , matched , _ = network-step related move in no√ tt t matched)

  refuses-native : ∀ {p c refusal} → Related p c → O.Refuses c refusal
    → Refuses p (λ e → refusal (encode e))
  refuses-native related (st , absent) = stable-native related st ,
    λ e member t move → let c′ , matched , _ = native-step related move in absent (encode e) member c′ matched

  refuses-network : ∀ {p c refusal} → Related p c → Refuses p (λ e → refusal (encode e)) → O.Refuses c refusal
  refuses-network related (st , absent) = stable-network related st , reject
    where
    reject : ∀ e → _ → ∀ c′ → _ → ⊥
    reject K.√ member c′ move = let t , matched , _ = network-step related move in absent (√ tt) member t matched
    reject (K.event (inj₁ () , _)) member c′ move
    reject (K.event (inj₂ () , _)) member c′ move

  trace-to-native : ∀ xs → O.Trace K.initial-configuration xs → Trace (Q.native initial) (map decode xs)
  trace-to-native xs (c , path) = let t , path′ , _ = execute-network (live initial) path in t , path′

  trace-to-network : ∀ xs → Trace (Q.native initial) (map decode xs) → O.Trace K.initial-configuration xs
  trace-to-network xs (t , path) =
    let c , path′ , _ = execute-native (live initial) path
    in c , subst (λ ys → O.Executes K.initial-configuration ys c) (roundtrip xs) path′

  failure-to-native : ∀ xs refusal → O.Failure K.initial-configuration xs refusal
    → Failure (Q.native initial) (map decode xs) (λ e → refusal (encode e))
  failure-to-native xs refusal (c , path , refused) =
    let t , path′ , related = execute-network (live initial) path
    in t , path′ , refuses-native related refused

  failure-to-network : ∀ xs refusal → Failure (Q.native initial) (map decode xs) (λ e → refusal (encode e))
    → O.Failure K.initial-configuration xs refusal
  failure-to-network xs refusal (t , path , refused) =
    let c , path′ , related = execute-native (live initial) path
    in c , subst (λ ys → O.Executes K.initial-configuration ys c) (roundtrip xs) path′ , refuses-network related refused

  divergence-to-native : ∀ xs → O.Divergence K.initial-configuration xs → Divergence (Q.native initial) (map decode xs)
  divergence-to-native xs (c , path , divergent) =
    let t , path′ , related = execute-network (live initial) path
    in t , path′ , Q.network-divergence related divergent

  divergence-to-network : ∀ xs → Divergence (Q.native initial) (map decode xs) → O.Divergence K.initial-configuration xs
  divergence-to-network xs (t , path , divergent) =
    let c , path′ , related = execute-native (live initial) path
    in c , subst (λ ys → O.Executes K.initial-configuration ys c) (roundtrip xs) path′ , Q.native-divergence related divergent

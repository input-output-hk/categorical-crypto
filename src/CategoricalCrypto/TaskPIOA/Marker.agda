{-# OPTIONS --safe --without-K #-}

-- A delimiter after each activation recovers silent replies from ordinary
-- source traces. Input-forwarding names close any interface but never fire.
module CategoricalCrypto.TaskPIOA.Marker where

open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.AdaptiveFinite
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
import CategoricalCrypto.TaskPIOA.Setup as Source
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

markerSignature : Signature → Signature
markerSignature S = record
  { inputs = empty ; outputs = inputs S ⊕ one ; hidden = empty ; tasks = one
  ; taskOf = λ _ → tt ; task-inhabited = λ _ → inj₁ (inj₂ tt) , refl }

markerAutomaton : (S : Signature) → Automaton (markerSignature S)
markerAutomaton S = record
  { states = one ; initial = tt ; input = λ ()
  ; choose = λ _ _ → just (inj₁ (inj₂ tt))
  ; owns = λ _ _ _ _ → refl ; kernel = λ _ _ → return-ℚ tt }

markerEnvironment : (S : Signature) → Environment S
markerEnvironment S = record
  { signature = markerSignature S ; automaton = markerAutomaton S
  ; wiring = record
    { left = record
      { name = λ i → inj₂ (inj₁ i)
      ; find = λ where
          (inj₁ ())
          (inj₂ (inj₁ i)) → just i
          (inj₂ (inj₂ _)) → nothing
      ; complete = λ _ → refl
      ; sound = λ where
          (inj₁ ())
          (inj₂ (inj₁ i)) _ refl → refl
          (inj₂ (inj₂ _)) _ () }
    ; right = record
      { name = λ () ; find = λ _ → nothing
      ; complete = λ () ; sound = λ _ _ () }
    ; boundary-live = λ () } }

module _ {S : Signature} where
  private
    Joint = productSignature S (markerSignature S) empty
    mark : Output Joint
    mark = inj₂ (inj₂ tt)

  markedSchedule : Schedule S → Schedule Joint
  markedSchedule [] = []
  markedSchedule (t ∷ ρ) = inj₁ t ∷ inj₂ tt ∷ markedSchedule ρ

  encodeReplies : List (Maybe (Output S)) → List (Output Joint)
  encodeReplies [] = []
  encodeReplies (nothing ∷ xs) = mark ∷ encodeReplies xs
  encodeReplies (just o ∷ xs) = inj₁ o ∷ mark ∷ encodeReplies xs

  decodeReplies : List (Output Joint) → List (Maybe (Output S))
  decodeReplies (inj₁ o ∷ inj₂ (inj₂ _) ∷ xs) = just o ∷ decodeReplies xs
  decodeReplies (inj₂ (inj₂ _) ∷ xs) = nothing ∷ decodeReplies xs
  decodeReplies _ = []

  decode-encode : ∀ xs → decodeReplies (encodeReplies xs) ≡ xs
  decode-encode [] = refl
  decode-encode (nothing ∷ xs) = cong (nothing ∷_) (decode-encode xs)
  decode-encode (just o ∷ xs) = cong (just o ∷_) (decode-encode xs)

  module _ (M : Automaton S) where
    private
      joint = product (wiring (markerEnvironment S)) M (markerAutomaton S)
      liftReply : Maybe (Output S) × State M → Maybe (Output Joint) × State joint
      liftReply (o , q) = Maybe.map inj₁ o , (q , tt)

      lifted-step : (o : Maybe (Output S)) (μ : Dist-ℚ (State M))
        → Dmap (Maybe.map inj₁ o ,_) (independent μ (return-ℚ tt))
          ≈Mℚ Dmap liftReply (Dmap (o ,_) μ)
      lifted-step o μ P = trans
        (lookupᴰℚ-Dmap (Maybe.map inj₁ o ,_) (independent μ (return-ℚ tt)) P)
        (trans (independent-eval μ (return-ℚ tt) (λ qr → P (Maybe.map inj₁ o , qr)))
          (trans (lookupᴰℚ-cong-P (entries μ) λ q →
            lookupᴰℚ-return tt (λ r → P (Maybe.map inj₁ o , (q , r))))
            (sym (trans (lookupᴰℚ-Dmap liftReply (Dmap (o ,_) μ) P)
              (lookupᴰℚ-Dmap (o ,_) μ (P ∘ liftReply))))))

      tick-left : ∀ t q → tick joint (inj₁ t) (q , tt) ≈Mℚ Dmap liftReply (tick M t q)
      tick-left t q with choose M q t
      ... | nothing = λ P → trans (lookupᴰℚ-return (nothing , (q , tt)) P)
        (sym (trans (lookupᴰℚ-Dmap liftReply (return-ℚ (nothing , q)) P)
          (lookupᴰℚ-return (nothing , q) (P ∘ liftReply))))
      ... | just (inj₁ o) = lifted-step (just o) (kernel M (inj₁ o) q)
      ... | just (inj₂ h) = lifted-step nothing (kernel M (inj₂ h) q)

      tick-marker : ∀ q → tick joint (inj₂ tt) (q , tt)
        ≈Mℚ return-ℚ (just mark , (q , tt))
      tick-marker q P = trans
        (lookupᴰℚ-Dmap (just mark ,_) (independent (return-ℚ q) (return-ℚ tt)) P)
        (trans (independent-eval (return-ℚ q) (return-ℚ tt) (λ qr → P (just mark , qr)))
          (trans (lookupᴰℚ-return q (λ q′ →
            lookupᴰℚ (entries (return-ℚ tt)) (λ r → P (just mark , (q′ , r)))))
            (trans (lookupᴰℚ-return tt (λ r → P (just mark , (q , r))))
              (sym (lookupᴰℚ-return (just mark , (q , tt)) P)))))

      marker-run : ∀ ρ q P → lookupᴰℚ (entries (runFrom joint (inj₂ tt ∷ ρ) (q , tt))) P
        ≡ lookupᴰℚ (entries (runFrom joint ρ (q , tt))) (P ∘ (mark ∷_))
      marker-run ρ q P = trans (lookupᴰℚ-bind (entries (tick joint (inj₂ tt) (q , tt)))
          (λ (o , qr) → entries (Dmap (prepend o) (runFrom joint ρ qr))) P)
        (trans (tick-marker q continuation)
          (trans (lookupᴰℚ-return (just mark , (q , tt)) continuation)
            (lookupᴰℚ-Dmap (mark ∷_) (runFrom joint ρ (q , tt)) P)))
        where
        continuation : Maybe (Output Joint) × State joint → ℚ
        continuation (o , qr) = lookupᴰℚ (entries (Dmap (prepend o) (runFrom joint ρ qr))) P

    marked-run : ∀ ρ q P → lookupᴰℚ (entries (runFrom joint (markedSchedule ρ) (q , tt))) P
      ≡ lookupᴰℚ (entries (paddedReplyRun M ρ q)) (P ∘ encodeReplies)
    marked-run [] q P = trans (lookupᴰℚ-return [] P)
      (sym (lookupᴰℚ-return [] (P ∘ encodeReplies)))
    marked-run (t ∷ ρ) q P = trans (lookupᴰℚ-bind (entries (tick joint (inj₁ t) (q , tt))) _ P)
      (trans (tick-left t q _)
        (trans (lookupᴰℚ-Dmap liftReply (tick M t q) _)
          (trans (lookupᴰℚ-cong-P (entries (tick M t q)) inner)
            (sym (trans (lookupᴰℚ-bind (entries (tick M t q)) _ (P ∘ encodeReplies))
              (lookupᴰℚ-cong-P (entries (tick M t q)) λ (o , q′) →
                lookupᴰℚ-Dmap (o ∷_) (paddedReplyRun M ρ q′) (P ∘ encodeReplies)))))))
      where
      inner : ∀ p → lookupᴰℚ (entries (Dmap (prepend (proj₁ (liftReply p)))
          (runFrom joint (inj₂ tt ∷ markedSchedule ρ) (proj₂ (liftReply p))))) P
        ≡ lookupᴰℚ (entries (paddedReplyRun M ρ (proj₂ p)))
          (λ xs → P (encodeReplies (proj₁ p ∷ xs)))
      inner (nothing , q′) = trans (lookupᴰℚ-Dmap (λ xs → xs)
          (runFrom joint (inj₂ tt ∷ markedSchedule ρ) (q′ , tt)) P)
        (trans (marker-run (markedSchedule ρ) q′ P)
          (marked-run ρ q′ (P ∘ (mark ∷_))))
      inner (just o , q′) = trans (lookupᴰℚ-Dmap (inj₁ o ∷_)
          (runFrom joint (inj₂ tt ∷ markedSchedule ρ) (q′ , tt)) P)
        (trans (marker-run (markedSchedule ρ) q′ (P ∘ (inj₁ o ∷_)))
          (marked-run ρ q′ (P ∘ (inj₁ o ∷_) ∘ (mark ∷_))))

    marker-extraction : ∀ ρ q → Dmap decodeReplies
        (runFrom joint (markedSchedule ρ) (q , tt)) ≈Mℚ paddedReplyRun M ρ q
    marker-extraction ρ q P = trans
      (lookupᴰℚ-Dmap decodeReplies (runFrom joint (markedSchedule ρ) (q , tt)) P)
      (trans (marked-run ρ q (P ∘ decodeReplies))
        (lookupᴰℚ-cong-P (entries (paddedReplyRun M ρ q)) λ xs → cong P (decode-encode xs)))

  markerTest : Schedule S → (List (Maybe (Output S)) → ℚ) → Source.Test (Source.Syntax.Var S)
  markerTest ρ P = Source.nativeTest (markerEnvironment S) (markedSchedule ρ) (P ∘ decodeReplies)

  marker-test-agreement : (M : Automaton S) → ∀ ρ P
    → Source.evaluate (markerTest ρ P) M
      ≡ lookupᴰℚ (entries (paddedReplyRun M ρ (initial M))) P
  marker-test-agreement M ρ P = trans (marked-run M ρ (initial M) (P ∘ decodeReplies))
    (lookupᴰℚ-cong-P (entries (paddedReplyRun M ρ (initial M))) λ xs → cong P (decode-encode xs))

  source-tests-imply-padded : (M N : Automaton S)
    → (∀ (T : Source.Test (Source.Syntax.Var S)) → Source.evaluate T M ≡ Source.evaluate T N)
    → ∀ ρ → paddedReplyRun M ρ (initial M) ≈Mℚ paddedReplyRun N ρ (initial N)
  source-tests-imply-padded M N equal ρ P = trans (sym (marker-test-agreement M ρ P))
    (trans (equal (markerTest ρ P)) (marker-test-agreement N ρ P))

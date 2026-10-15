{-# OPTIONS --safe --without-K #-}

-- A scheduler may branch on the public reply, never on the resource state.
-- Instrumentation is justified one activation at a time; finite-testing
-- completeness is inherited from FiniteTesting, including failure mass.
module CategoricalCrypto.SSP.Dist.SchedulerInformation where

open import Class.DecEq
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.SSP.Dist.FiniteTesting as F
open import CategoricalCrypto.SSP.Dist.Kernel using
  (Oracle; ⟦_⟧; Samples; sample-⟦⟧; _>>=ᶜ_; _·_; second; regroup)
open import CategoricalCrypto.SSP.Iface using (Iface)
import CategoricalCrypto.SSP.Protocol as P
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.RationalDist.Partial

private variable
  T R V Q A X Y Symbol : Set
  I B : Iface

viewKernel : (T → R → V) → F.TotalKernel T R Q → F.TotalKernel T V Q
viewKernel view K t q = Dmap (map₁ (view t)) (K t q)

-- Legal trees are precisely Calls over the viewed interface. Their lowering
-- cannot pass a raw reply (or a successor state) to a public continuation.
lower : ∀ {dec} (view : T → R → V)
  → P.Calls (F.Uniform T V dec) X → P.Calls (F.Uniform T R dec) X
lower view (P.ret x) = P.ret x
lower view (P.call t tt k) = P.call t tt λ r → lower view (k (view t r))
lower view (P.coin μ k) = P.coin μ λ b → lower view (k b)
lower view P.dead = P.dead

lower-bind : ∀ {dec} (view : T → R → V) (c : P.Calls (F.Uniform T V dec) X)
  (k : X → P.Calls (F.Uniform T V dec) Y)
  → lower view (c >>=ᶜ k) P.≈ᶜ (lower view c >>=ᶜ (lower view ∘ k))
lower-bind view (P.ret x) k = P.≈ᶜ-refl
lower-bind view (P.call t tt f) k = P.call λ r → lower-bind view (f (view t r)) k
lower-bind view (P.coin μ f) k = P.coin λ b → lower-bind view (f b) k
lower-bind view P.dead k = P.dead

lower-value : ∀ {dec} (view : T → R → V) (K : F.TotalKernel T R Q)
  (c : P.Calls (F.Uniform T V dec) X) q ξ
  → F.value K (lower view c) q ξ ≡ F.value (viewKernel view K) c q ξ
lower-value view K (P.ret x) q ξ = refl
lower-value view K (P.call t tt k) q ξ = trans
  (lookupᴰℚ-cong-P (entries (K t q)) (λ { (r , q′) → lower-value view K (k (view t r)) q′ ξ }))
  (sym (lookupᴰℚ-Dmap (map₁ (view t)) (K t q)
    (λ (v , q′) → F.value (viewKernel view K) (k v) q′ ξ)))
lower-value view K (P.coin μ k) q ξ = lookupᴰℚ-cong-P (entries μ)
  (λ b → lower-value view K (k b) q ξ)
lower-value view K P.dead q ξ = refl

lower-observe : ∀ {dec} (view : T → R → V) (K : F.TotalKernel T R Q)
  (c : P.Calls (F.Uniform T V dec) X) q
  → F.observe K (lower view c) q ≈Mℚ F.observe (viewKernel view K) c q
lower-observe view K c q ξ = trans (F.observe-value K (lower view c) q ξ)
  (trans (lower-value view K c q ξ) (sym (F.observe-value (viewKernel view K) c q ξ)))

encodeWord : (R → List Symbol) → List R → List Symbol
encodeWord block [] = []
encodeWord block (r ∷ rs) = block r ++ encodeWord block rs

record Codec (R Symbol : Set) : Set where
  field encodeReply : R → List Symbol
        decode : List Symbol → List R
        decode-encode : ∀ rs → decode (encodeWord encodeReply rs) ≡ rs
open Codec public

record Instrumentation {T R Q Symbol : Set} (K : F.TotalKernel T R Q)
  (codec : Codec R Symbol) : Set₁ where
  field Context : Set
        emptyContext : Context
        extendContext : T → Context → Context
        execute : Context → Q → Dist-ℚ (List Symbol)
        empty-law : ∀ q → execute emptyContext q ≈Mℚ return-ℚ []
        extend-law : ∀ t c q → execute (extendContext t c) q
          ≈Mℚ (K t q >>=ᴹ λ (r , q′) → Dmap (encodeReply codec r ++_) (execute c q′))
open Instrumentation public

compileWord : ∀ {K : F.TotalKernel T R Q} {codec : Codec R Symbol}
  (instrument : Instrumentation K codec) → List T → Context instrument
compileWord instrument [] = emptyContext instrument
compileWord instrument (t ∷ ts) = extendContext instrument t (compileWord instrument ts)

encoded-execution : ∀ {K : F.TotalKernel T R Q} {codec : Codec R Symbol}
  (instrument : Instrumentation K codec) ts q
  → execute instrument (compileWord instrument ts) q
    ≈Mℚ Dmap (encodeWord (encodeReply codec)) (F.word K ts q)
encoded-execution {codec = codec} instrument [] q ξ = trans (empty-law instrument q ξ)
  (sym (trans (lookupᴰℚ-Dmap (encodeWord (encodeReply codec)) (return-ℚ []) ξ)
    (trans (lookupᴰℚ-return [] (ξ ∘ encodeWord (encodeReply codec)))
      (sym (lookupᴰℚ-return [] ξ)))))
encoded-execution {K = K} {codec} instrument (t ∷ ts) q ξ = trans
  (extend-law instrument t (compileWord instrument ts) q ξ)
  (trans (E-bind (K t q) (λ (r , q′) →
    Dmap (encodeReply codec r ++_) (execute instrument (compileWord instrument ts) q′)) ξ)
    (trans (lookupᴰℚ-cong-P (entries (K t q)) (λ { (r , q′) → trans
      (lookupᴰℚ-Dmap (encodeReply codec r ++_) (execute instrument (compileWord instrument ts) q′) ξ)
      (trans (encoded-execution instrument ts q′ (ξ ∘ (encodeReply codec r ++_)))
        (lookupᴰℚ-Dmap (encodeWord (encodeReply codec)) (F.word K ts q′)
          (ξ ∘ (encodeReply codec r ++_)))) }))
      (sym (trans (lookupᴰℚ-Dmap (encodeWord (encodeReply codec)) (F.word K (t ∷ ts) q) ξ)
        (trans (E-bind (K t q) (λ (r , q′) → Dmap (r ∷_) (F.word K ts q′))
          (ξ ∘ encodeWord (encodeReply codec)))
          (lookupᴰℚ-cong-P (entries (K t q)) (λ { (r , q′) →
            lookupᴰℚ-Dmap (r ∷_) (F.word K ts q′) (ξ ∘ encodeWord (encodeReply codec)) })))))))

extraction : ∀ {K : F.TotalKernel T R Q} {codec : Codec R Symbol}
  (instrument : Instrumentation K codec) ts q
  → Dmap (decode codec) (execute instrument (compileWord instrument ts) q) ≈Mℚ F.word K ts q
extraction {K = K} {codec} instrument ts q ξ = trans
  (lookupᴰℚ-Dmap (decode codec) (execute instrument (compileWord instrument ts) q) ξ)
  (trans (encoded-execution instrument ts q (ξ ∘ decode codec))
    (trans (lookupᴰℚ-Dmap (encodeWord (encodeReply codec)) (F.word K ts q) (ξ ∘ decode codec))
      (lookupᴰℚ-cong-P (entries (F.word K ts q)) (λ rs → cong ξ (decode-encode codec rs)))))

information-to-words : ∀ {K : F.TotalKernel T R Q} {H : F.TotalKernel T R A}
  {codec : Codec R Symbol} (left : Instrumentation K codec) (right : Instrumentation H codec) q r
  → (∀ ts → execute left (compileWord left ts) q ≈Mℚ execute right (compileWord right ts) r)
  → ∀ ts → F.word K ts q ≈Mℚ F.word H ts r
information-to-words {codec = codec} left right q r equal ts ξ = trans
  (sym (extraction left ts q ξ))
  (trans (lookupᴰℚ-Dmap (decode codec) (execute left (compileWord left ts) q) ξ)
    (trans (equal ts (ξ ∘ decode codec))
      (trans (sym (lookupᴰℚ-Dmap (decode codec) (execute right (compileWord right ts) r) ξ))
        (extraction right ts r ξ))))

fixed-information-to-calls : ∀ {dec} (_≟_ : DecidableEquality R)
  {K : F.TotalKernel T R Q} {H : F.TotalKernel T R A} {codec : Codec R Symbol}
  (left : Instrumentation K codec) (right : Instrumentation H codec) q r
  → (∀ ts → execute left (compileWord left ts) q ≈Mℚ execute right (compileWord right ts) r)
  → (c : P.Calls (F.Uniform T R dec) X) → F.observe K c q ≈Mℚ F.observe H c r
fixed-information-to-calls _≟_ left right q r equal =
  F.Cylinders.fixed-to-calls _≟_ _ q _ r (information-to-words left right q r equal)

-- A local receiving/step square, not standalone fixed-word equality, is
-- required when a linked native context may inject boundary inputs.
observeOracle : Oracle I Q → P.Calls I X → Q → Dist⊥ X
observeOracle O c q = Dmap (Maybe.map proj₁) (⟦ c ⟧ O q)

sample-result : {ρ : Q → Dist-ℚ A} {O : Oracle I Q} {O′ : Oracle I A}
  → Samples {A = I} ρ O O′ → (c : P.Calls I X) (q : Q)
  → (ρ q >>=ᴹ λ r → observeOracle O′ c r) ≈Mℚ observeOracle O c q
sample-result {Q = Q} {A = A} {ρ = ρ} {O = O} {O′} square c q ξ = trans
  (E-bind (ρ q) (λ r → observeOracle O′ c r) ξ)
  (trans (lookupᴰℚ-cong-P (entries (ρ q)) (λ r →
    lookupᴰℚ-Dmap (Maybe.map proj₁) (⟦ c ⟧ O′ r) ξ))
    (trans (sym (E-bind (ρ q) (⟦ c ⟧ O′) (F.lift ξ)))
      (trans (sample-⟦⟧ square c q (F.lift ξ))
        (trans (E-bind (⟦ c ⟧ O q)
          (kmaybe (λ p → ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u))) (F.lift ξ))
          (trans (lookupᴰℚ-cong-P (entries (⟦ c ⟧ O q)) point)
            (sym (lookupᴰℚ-Dmap (Maybe.map proj₁) (⟦ c ⟧ O q) ξ)))))))
  where
  point : ∀ z → E (kmaybe (λ p → ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u)) z) (F.lift ξ)
    ≡ F.lift {Q = Q} ξ z
  point nothing = lookupᴰℚ-return nothing (F.lift {Q = A} ξ)
  point (just (x , s)) = trans (E-bind (ρ s) (λ u → return⊥ (x , u)) (F.lift ξ))
    (trans (lookupᴰℚ-cong-P (entries (ρ s)) (λ u → lookupᴰℚ-return (just (x , u)) (F.lift ξ)))
      (lookupᴰℚ-const (ρ s) (ξ (just x))))

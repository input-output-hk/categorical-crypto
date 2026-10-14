{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.IPDL.Tests where

open import Data.Bool.Base
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import CategoricalCrypto.IPDL.Native
open import CategoricalCrypto.IPDL.SSP
open import CategoricalCrypto.IPDL.Syntax
open import CategoricalCrypto.SSP.Iface using (unitᴵ; Ωᴵ)
open import CategoricalCrypto.SSP.Observation
import CategoricalCrypto.SSP.Protocol as P

Bit : Ctx
Bit = bit ∷ []

copy : Net Bit Bit
copy = record { H = [] ; def = (1 , read zero ret) , tt }

constant : Net [] Bit
constant = record { H = [] ; def = (0 , ret true) , tt }

delayed : Strategy Bit Bit (Maybe Bool × Maybe Bool × Maybe Bool)
delayed = ask Step tt λ _ → ask (Get zero) tt λ a →
  ask (Input zero) false λ _ → ask (Get zero) tt λ b →
  ask (Input zero) true λ _ → ask (Get zero) tt λ c → finish (a , b , c)

delayed-readiness : entries (Experiment.run copy delayed)
                 ≡ entries (return-ℚ (nothing , just false , just false))
delayed-readiness = refl

first-get : Strategy [] Bit (Maybe Bool × Maybe Bool)
first-get = ask (Get zero) tt λ a → ask (Get zero) tt λ b → finish (a , b)

get-before-quiescence : entries (Experiment.run constant first-get)
                     ≡ entries (return-ℚ (nothing , just true))
get-before-quiescence = refl

shared : Net [] (bit ⊠ bit ∷ [])
shared = record
  { H = Bit
  ; def = (2 , read (suc zero) λ a → read (suc zero) λ b → ret (a , b)) ,
          (1 , coin uniform-Bool ret) , tt }

read-twice : Strategy [] (bit ⊠ bit ∷ []) (Maybe (Bool × Bool) × Maybe (Bool × Bool))
read-twice = ask Step tt λ _ → ask (Get zero) tt λ a → ask (Get zero) tt λ b → finish (a , b)

shared-sample-persistent : entries (Experiment.run shared read-twice)
                        ≡ entries (uniform-Bool >>=ᴹ λ b → return-ℚ (just (b , b) , just (b , b)))
shared-sample-persistent = refl

Both : Ctx
Both = bit ∷ bit ∷ []

correlated independent : Net Bit Both
correlated = record
  { H = Bit
  ; def = (2 , read (suc (suc (suc zero))) λ b →
                 if b then ret false else read zero λ _ → ret false) ,
          (2 , read zero λ _ → read (suc (suc (suc zero))) ret) ,
          (1 , coin uniform-Bool ret) , tt }
independent = record
  { H = Bit
  ; def = (2 , read (suc (suc (suc zero))) λ b →
                 if b then ret false else read zero λ _ → ret false) ,
          (2 , read zero λ _ → coin uniform-Bool ret) ,
          (1 , coin uniform-Bool ret) , tt }

feedback-test : Strategy Bit Both (Maybe Bool)
feedback-test = ask Step tt λ _ → ask (Get zero) tt λ where
  nothing → ask (Get (suc zero)) tt finish
  (just _) → ask (Input zero) false λ _ → ask (Get (suc zero)) tt finish

correlated-feedback : entries (Experiment.run correlated feedback-test)
                    ≡ entries (uniform-Bool >>=ᴹ λ b → return-ℚ (if b then just true else nothing))
correlated-feedback = refl

independent-feedback : entries (Experiment.run independent feedback-test)
                     ≡ entries (uniform-Bool >>=ᴹ λ b →
                         if b then uniform-Bool >>=ᴹ (return-ℚ ∘ just) else return-ℚ nothing)
independent-feedback = refl

maybe-indicator : Maybe Bool → ℚ
maybe-indicator (just true) = 1ℚ
maybe-indicator _ = 0ℚ

correlated-true : lookupᴰℚ (entries (Experiment.run correlated feedback-test)) maybe-indicator ≡ + 1 / 2
correlated-true = refl

independent-true : lookupᴰℚ (entries (Experiment.run independent feedback-test)) maybe-indicator ≡ + 1 / 4
independent-true = refl

false-indicator undefined-indicator : Maybe Bool → ℚ
false-indicator (just false) = 1ℚ
false-indicator _ = 0ℚ
undefined-indicator nothing = 1ℚ
undefined-indicator _ = 0ℚ

correlated-false : lookupᴰℚ (entries (Experiment.run correlated feedback-test)) false-indicator ≡ 0ℚ
correlated-false = refl

independent-false : lookupᴰℚ (entries (Experiment.run independent feedback-test)) false-indicator ≡ + 1 / 4
independent-false = refl

correlated-undefined : lookupᴰℚ (entries (Experiment.run correlated feedback-test)) undefined-indicator ≡ + 1 / 2
correlated-undefined = refl

independent-undefined : lookupᴰℚ (entries (Experiment.run independent feedback-test)) undefined-indicator ≡ + 1 / 2
independent-undefined = refl

without-input : Strategy Bit Both (Maybe Bool)
without-input = ask Step tt λ _ → ask (Get (suc zero)) tt finish

correlated-needs-input : entries (Experiment.run correlated without-input)
                       ≡ entries (uniform-Bool >>=ᴹ λ _ → return-ℚ nothing)
correlated-needs-input = refl

independent-needs-input : entries (Experiment.run independent without-input)
                        ≡ entries (uniform-Bool >>=ᴹ λ _ → return-ℚ nothing)
independent-needs-input = refl

separator : Strategy Bit Both Bool
separator = ask Step tt λ _ → ask (Get zero) tt λ where
  nothing → finish false
  (just _) → ask (Input zero) false λ _ → ask (Get (suc zero)) tt λ where
    (just true) → finish true
    _ → finish false

correlated-compiled : runᵖ (tester separator P.∘ᵖ resource correlated)
                   ≈Mℚ (Experiment.run correlated separator >>=ᴹ return⊥)
correlated-compiled = Correspondence.agreement correlated separator

independent-compiled : runᵖ (tester separator P.∘ᵖ resource independent)
                    ≈Mℚ (Experiment.run independent separator >>=ᴹ return⊥)
independent-compiled = Correspondence.agreement independent separator

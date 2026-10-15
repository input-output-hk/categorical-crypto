{-# OPTIONS --safe --without-K #-}

-- Fixed instrumentation executes the Fig. 9 interface, including successful
-- absence replies. Residual cells never enter a scheduler continuation.
module CategoricalCrypto.IPDL.SchedulerInformation where

open import Class.DecEq
open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base as List hiding (lookup; take)
open import Data.Maybe.Base
open import Data.Rational.Base using (ℚ)
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁; map₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.IPDL.Native
import CategoricalCrypto.IPDL.SSP as SSP
open import CategoricalCrypto.IPDL.Syntax hiding (value)
import CategoricalCrypto.SSP.Dist.FiniteTesting as F
open import CategoricalCrypto.SSP.Dist.Kernel using (sample)
import CategoricalCrypto.SSP.Dist.SchedulerInformation as Information
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

private variable
  I O : Ctx
  X Y : Set

val-dec : (τ : Ty) → DecEq (Val τ)
val-dec unit = DecEq-⊤
val-dec bit = DecEq-Bool
val-dec (σ ⊠ τ) = DecEq-× ⦃ val-dec σ ⦄ ⦃ val-dec τ ⦄

Payload : (Ty → Set) → Ctx → Set
Payload A [] = ⊥
Payload A (τ ∷ Γ) = A τ ⊎ Payload A Γ

payload-dec : ∀ {A} → (∀ τ → DecEq (A τ)) → (Γ : Ctx) → DecEq (Payload A Γ)
payload-dec d [] = DecEq-⊥
payload-dec d (τ ∷ Γ) = DecEq-⊎ ⦃ d τ ⦄ ⦃ payload-dec d Γ ⦄

Command : Ctx → Ctx → Set
Command I O = Payload Val I ⊎ (Ref O ⊎ ⊤)

Response : Ctx → Set
Response O = ⊤ ⊎ Payload (Maybe ∘ Val) O

command-dec : (I O : Ctx) → DecEq (Command I O)
command-dec I O = DecEq-⊎ ⦃ payload-dec val-dec I ⦄
  ⦃ DecEq-⊎ ⦃ DecEq-Fin ⦄ ⦃ DecEq-⊤ ⦄ ⦄

response-dec : (O : Ctx) → DecEq (Response O)
response-dec O = DecEq-⊎ ⦃ DecEq-⊤ ⦄
  ⦃ payload-dec (λ τ → DecEq-Maybe ⦃ val-dec τ ⦄) O ⦄

input-command : (I : Ctx) → Payload Val I → Σ (Ref I) (λ c → Val (ty I c))
input-command (τ ∷ I) (inj₁ v) = zero , v
input-command (τ ∷ I) (inj₂ p) = suc (proj₁ v) , proj₂ v
  where v = input-command I p

decodeCommand : Command I O → Σ (Port I O) (Query I O)
decodeCommand {I} (inj₁ p) = Input (proj₁ v) , proj₂ v
  where v = input-command I p
decodeCommand (inj₂ (inj₁ c)) = Get c , tt
decodeCommand (inj₂ (inj₂ tt)) = Step , tt

inputPayload : (I : Ctx) → (c : Ref I) → Val (ty I c) → Payload Val I
inputPayload (τ ∷ I) zero v = inj₁ v
inputPayload (τ ∷ I) (suc c) v = inj₂ (inputPayload I c v)

input-roundtrip : ∀ I c v → input-command I (inputPayload I c v) ≡ (c , v)
input-roundtrip (τ ∷ I) zero v = refl
input-roundtrip (τ ∷ I) (suc c) v =
  cong (λ p → suc (proj₁ p) , proj₂ p) (input-roundtrip I c v)

encodeCommand : (c : Port I O) → Query I O c → Command I O
encodeCommand {I} (Input c) v = inj₁ (inputPayload I c v)
encodeCommand (Get c) _ = inj₂ (inj₁ c)
encodeCommand Step _ = inj₂ (inj₂ tt)

command-roundtrip : ∀ {I O} (c : Port I O) q
  → decodeCommand {I} {O} (encodeCommand {I} {O} c q) ≡ (c , q)
command-roundtrip {I} (Input c) v =
  cong (λ p → Input (proj₁ p) , proj₂ p) (input-roundtrip I c v)
command-roundtrip (Get c) tt = refl
command-roundtrip Step tt = refl

result : (O : Ctx) → (c : Ref O) → Maybe (Val (ty O c)) → Payload (Maybe ∘ Val) O
result (τ ∷ O) zero v = inj₁ v
result (τ ∷ O) (suc c) v = inj₂ (result O c v)

encodeResponse : (c : Port I O) → Reply I O c → Response O
encodeResponse (Input c) _ = inj₁ tt
encodeResponse {O = O} (Get c) v = inj₂ (result O c v)
encodeResponse Step _ = inj₁ tt

readResult : (O : Ctx) → (c : Ref O) → Payload (Maybe ∘ Val) O → Maybe (Val (ty O c))
readResult (τ ∷ O) zero (inj₁ v) = v
readResult (τ ∷ O) zero (inj₂ _) = nothing
readResult (τ ∷ O) (suc c) (inj₁ _) = nothing
readResult (τ ∷ O) (suc c) (inj₂ r) = readResult O c r

read-result : ∀ O c v → readResult O c (result O c v) ≡ v
read-result (τ ∷ O) zero v = refl
read-result (τ ∷ O) (suc c) v = read-result O c v

decodeResponse : (c : Port I O) → Response O → Reply I O c
decodeResponse (Input c) _ = tt
decodeResponse (Get c) (inj₁ _) = nothing
decodeResponse {O = O} (Get c) (inj₂ r) = readResult O c r
decodeResponse Step _ = tt

response-roundtrip : ∀ {I O} (c : Port I O) r
  → decodeResponse {I} {O} c (encodeResponse {I} {O} c r) ≡ r
response-roundtrip (Input c) tt = refl
response-roundtrip {O = O} (Get c) r = read-result O c r
response-roundtrip Step tt = refl

recoverResult : (O : Ctx) → (c : Ref O) → Payload (Maybe ∘ Val) O
  → Maybe (Maybe (Val (ty O c)))
recoverResult (τ ∷ O) zero (inj₁ v) = just v
recoverResult (τ ∷ O) zero (inj₂ _) = nothing
recoverResult (τ ∷ O) (suc c) (inj₁ _) = nothing
recoverResult (τ ∷ O) (suc c) (inj₂ r) = recoverResult O c r

recover-result : ∀ O c v → recoverResult O c (result O c v) ≡ just v
recover-result (τ ∷ O) zero v = refl
recover-result (τ ∷ O) (suc c) v = recover-result O c v

-- The outer Maybe rejects a wrong reply tag; just nothing is a successful Get.
recoverResponse : (c : Port I O) → Response O → Maybe (Reply I O c)
recoverResponse (Input c) (inj₁ _) = just tt
recoverResponse (Input c) (inj₂ _) = nothing
recoverResponse (Get c) (inj₁ _) = nothing
recoverResponse {O = O} (Get c) (inj₂ r) = recoverResult O c r
recoverResponse Step (inj₁ _) = just tt
recoverResponse Step (inj₂ _) = nothing

recover-response : ∀ {I O} (c : Port I O) r
  → recoverResponse {I} {O} c (encodeResponse {I} {O} c r) ≡ just r
recover-response (Input c) tt = refl
recover-response {O = O} (Get c) r = recover-result O c r
recover-response Step tt = refl

compileNative : Strategy I O X
  → P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) X
compileNative (finish x) = P.ret x
compileNative {I} {O} (ask c q k) = P.call (encodeCommand {I} {O} c q) tt
  λ r → compileNative (k (decodeResponse {I} {O} c r))
compileNative (random μ k) = P.coin μ (compileNative ∘ k)

mapStrategy : (X → Y) → Strategy I O X → Strategy I O Y
mapStrategy f (finish x) = finish (f x)
mapStrategy f (ask c q k) = ask c q (mapStrategy f ∘ k)
mapStrategy f (random μ k) = random μ (mapStrategy f ∘ k)

module Model {I O} (N : Net I O) where
  open Residual N
  open Experiment N

  command : Command I O → Σ (Port I O) (Query I O)
  command = decodeCommand {I} {O}

  response : (c : Port I O) → Reply I O c → Response O
  response = encodeResponse {I} {O}

  kernel : F.TotalKernel (Command I O) (Response O) State
  kernel t s = sample (Interaction.turn N s c q) >>=ᴹ λ (s′ , r) → return-ℚ (response c r , s′)
    where c = proj₁ (command t); q = proj₂ (command t)

  Context : Set
  Context = Strategy I O (List (Response O))

  emptyContext : Context
  emptyContext = finish []

  extendContext : Command I O → Context → Context
  extendContext t a = ask c q λ r → mapStrategy (response c r ∷_) a
    where c = proj₁ (command t); q = proj₂ (command t)

  logger : List (Command I O) → Context
  logger [] = emptyContext
  logger (t ∷ ts) = extendContext t (logger ts)

  execute : Context → State → Dist-ℚ (List (Response O))
  execute = runWith return-ℚ

  map-execution : ∀ (f : X → Y) (a : Strategy I O X) s
    → runWith return-ℚ (mapStrategy f a) s ≈Mℚ Dmap f (runWith return-ℚ a s)
  map-execution f (finish x) s ξ = sym (>>=ᴹ-identityˡ x (return-ℚ ∘ f) ξ)
  map-execution f (ask c q k) s ξ = trans
    (>>=ᴹ-congˡ (sample (Interaction.turn N s c q))
      (λ (s′ , r) → runWith return-ℚ (mapStrategy f (k r)) s′)
      (λ (s′ , r) → Dmap f (runWith return-ℚ (k r) s′))
      (λ (s′ , r) → map-execution f (k r) s′) ξ)
    (sym (>>=ᴹ-assoc (sample (Interaction.turn N s c q))
      (λ (s′ , r) → runWith return-ℚ (k r) s′) (return-ℚ ∘ f) ξ))
  map-execution f (random μ k) s ξ = trans
    (>>=ᴹ-congˡ μ (λ b → runWith return-ℚ (mapStrategy f (k b)) s)
      (λ b → Dmap f (runWith return-ℚ (k b) s)) (λ b → map-execution f (k b) s) ξ)
    (sym (>>=ᴹ-assoc μ (λ b → runWith return-ℚ (k b) s) (return-ℚ ∘ f) ξ))

  kernel-expect : ∀ (t : Command I O) s (f : Response O × State → ℚ)
    → E (kernel t s) f ≡ E (sample (Interaction.turn N s (proj₁ (command t)) (proj₂ (command t))))
      (λ (s′ , r) → f (response (proj₁ (command t)) r , s′))
  kernel-expect t s f = trans
    (E-bind (sample (Interaction.turn N s c q)) (λ (s′ , r) → return-ℚ (response c r , s′)) f)
    (lookupᴰℚ-cong-P (entries (sample (Interaction.turn N s c q)))
      (λ (s′ , r) → lookupᴰℚ-return (response c r , s′) f))
    where c = proj₁ (command t); q = proj₂ (command t)

  extension-law : ∀ t a s → execute (extendContext t a) s ≈Mℚ
    (kernel t s >>=ᴹ λ (r , s′) → Dmap (r ∷_) (execute a s′))
  extension-law t a s ξ = trans
    (>>=ᴹ-congˡ (sample (Interaction.turn N s c q))
      (λ (s′ , r) → execute (mapStrategy (response c r ∷_) a) s′)
      (λ (s′ , r) → Dmap (response c r ∷_) (execute a s′))
      (λ (s′ , r) → map-execution (response c r ∷_) a s′) ξ)
    (sym (trans (E-bind (kernel t s) (λ (r , s′) → Dmap (r ∷_) (execute a s′)) ξ)
      (trans (kernel-expect t s (λ (r , s′) → E (Dmap (r ∷_) (execute a s′)) ξ))
        (sym (E-bind (sample (Interaction.turn N s c q))
          (λ (s′ , r) → Dmap (response c r ∷_) (execute a s′)) ξ)))))
    where c = proj₁ (command t); q = proj₂ (command t)

  legal : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) X → Strategy I O (Maybe X)
  legal (P.ret x) = finish (just x)
  legal (P.call t tt k) = ask c q λ r → legal (k (response c r))
    where c = proj₁ (command t); q = proj₂ (command t)
  legal (P.coin μ k) = random μ (legal ∘ k)
  legal P.dead = finish nothing

  legal-value : ∀ (a : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) X) s ξ
    → E (runWith return-ℚ (legal a) s) ξ ≡ F.value kernel a s ξ
  legal-value (P.ret x) s ξ = lookupᴰℚ-return (just x) ξ
  legal-value (P.call t tt k) s ξ = trans
    (E-bind (sample (Interaction.turn N s c q))
      (λ (s′ , r) → runWith return-ℚ (legal (k (response c r))) s′) ξ)
    (trans (lookupᴰℚ-cong-P (entries (sample (Interaction.turn N s c q)))
      (λ (s′ , r) → legal-value (k (response c r)) s′ ξ))
      (sym (kernel-expect t s (λ (r , s′) → F.value kernel (k r) s′ ξ))))
    where c = proj₁ (command t); q = proj₂ (command t)
  legal-value (P.coin μ k) s ξ = trans
    (E-bind μ (λ b → runWith return-ℚ (legal (k b)) s) ξ)
    (lookupᴰℚ-cong-P (entries μ) (λ b → legal-value (k b) s ξ))
  legal-value P.dead s ξ = lookupᴰℚ-return nothing ξ

  legal-execution : ∀ (a : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) X) s
    → runWith return-ℚ (legal a) s ≈Mℚ F.observe kernel a s
  legal-execution a s ξ = trans (legal-value a s ξ) (sym (F.observe-value kernel a s ξ))

  typed-kernel-expect : ∀ c q s (f : Response O × State → ℚ)
    → E (kernel (encodeCommand {I} {O} c q) s) f
      ≡ E (sample (Interaction.turn N s c q)) (λ (s′ , r) → f (response c r , s′))
  typed-kernel-expect c q s f rewrite command-roundtrip {I} {O} c q = trans
    (E-bind (sample (Interaction.turn N s c q)) (λ (s′ , r) → return-ℚ (response c r , s′)) f)
    (lookupᴰℚ-cong-P (entries (sample (Interaction.turn N s c q)))
      (λ (s′ , r) → lookupᴰℚ-return (response c r , s′) f))

  kernel-issued-port : ∀ c q s
    → Dmap (λ (r , s′) → recoverResponse {I} {O} c r , s′)
        (kernel (encodeCommand {I} {O} c q) s)
      ≈Mℚ Dmap (λ (s′ , r) → just r , s′) (sample (Interaction.turn N s c q))
  kernel-issued-port c q s ξ = trans
    (lookupᴰℚ-Dmap (λ (r , s′) → recoverResponse {I} {O} c r , s′)
      (kernel (encodeCommand {I} {O} c q) s) ξ)
    (trans (typed-kernel-expect c q s (λ (r , s′) → ξ (recoverResponse {I} {O} c r , s′)))
      (trans (lookupᴰℚ-cong-P (entries (sample (Interaction.turn N s c q)))
        (λ (s′ , r) → cong (λ v → ξ (v , s′)) (recover-response {I} {O} c r)))
        (sym (lookupᴰℚ-Dmap (λ (s′ , r) → just r , s′) (sample (Interaction.turn N s c q)) ξ))))

  native-value : ∀ (a : Strategy I O X) s ξ
    → F.value kernel (compileNative a) s ξ ≡ E (runWith return⊥ a s) ξ
  native-value (finish x) s ξ = sym (lookupᴰℚ-return (just x) ξ)
  native-value (ask c q k) s ξ = trans
    (typed-kernel-expect c q s (λ (r , s′) →
      F.value kernel (compileNative (k (decodeResponse {I} {O} c r))) s′ ξ))
    (trans (lookupᴰℚ-cong-P (entries (sample (Interaction.turn N s c q)))
      (λ (s′ , r) → trans
        (cong (λ v → F.value kernel (compileNative (k v)) s′ ξ) (response-roundtrip {I} {O} c r))
        (native-value (k r) s′ ξ)))
      (sym (E-bind (sample (Interaction.turn N s c q))
        (λ (s′ , r) → runWith return⊥ (k r) s′) ξ)))
  native-value (random μ k) s ξ = trans
    (lookupᴰℚ-cong-P (entries μ) (λ b → native-value (k b) s ξ))
    (sym (E-bind μ (λ b → runWith return⊥ (k b) s) ξ))

  native-execution : ∀ (a : Strategy I O X) s
    → F.observe kernel (compileNative a) s ≈Mℚ runWith return⊥ a s
  native-execution a s ξ = trans (F.observe-value kernel (compileNative a) s ξ) (native-value a s ξ)

singleton-codec : (O : Ctx) → Information.Codec (Response O) (Response O)
singleton-codec O = record { encodeReply = _∷ [] ; decode = λ xs → xs ; decode-encode = law }
  where
  law : ∀ xs → Information.encodeWord (_∷ []) xs ≡ xs
  law [] = refl
  law (x ∷ xs) = cong (x ∷_) (law xs)

instrumentation : (N : Net I O) → Information.Instrumentation (Model.kernel N) (singleton-codec O)
instrumentation N = record
  { Context = Model.Context N
  ; emptyContext = Model.emptyContext N
  ; extendContext = Model.extendContext N
  ; execute = Model.execute N
  ; empty-law = λ _ _ → refl
  ; extend-law = Model.extension-law N }

fixed-information-to-native : (N M : Net I O) (s : Residual.State N) (t : Residual.State M)
  → (∀ ts → Model.execute N (Information.compileWord (instrumentation N) ts) s
    ≈Mℚ Model.execute M (Information.compileWord (instrumentation M) ts) t)
  → (a : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) X)
  → Experiment.runWith N return-ℚ (Model.legal N a) s
    ≈Mℚ Experiment.runWith M return-ℚ (Model.legal M a) t
fixed-information-to-native {O = O} N M s t equal a ξ = trans (Model.legal-execution N a s ξ)
  (trans (Information.fixed-information-to-calls (DecEq._≟_ (response-dec O))
    (instrumentation N) (instrumentation M) s t equal a ξ)
    (sym (Model.legal-execution M a t ξ)))

fixed-information-to-strategies : (N M : Net I O) (s : Residual.State N) (t : Residual.State M)
  → (∀ ts → Model.execute N (Information.compileWord (instrumentation N) ts) s
    ≈Mℚ Model.execute M (Information.compileWord (instrumentation M) ts) t)
  → (a : Strategy I O X) → Experiment.runWith N return⊥ a s ≈Mℚ Experiment.runWith M return⊥ a t
fixed-information-to-strategies {O = O} N M s t equal a ξ =
  trans (sym (Model.native-execution N a s ξ))
    (trans (Information.fixed-information-to-calls (DecEq._≟_ (response-dec O))
      (instrumentation N) (instrumentation M) s t equal (compileNative a) ξ)
      (Model.native-execution M a t ξ))

accept : Maybe Bool → Bool
accept nothing = false
accept (just b) = b

module Consumers {I O} (N M : Net I O)
  (equal : ∀ ts → Model.execute N (Information.compileWord (instrumentation N) ts) (Residual.initial N)
    ≈Mℚ Model.execute M (Information.compileWord (instrumentation M) ts) (Residual.initial M)) where

  native-composed-output : (a : Strategy I O Bool)
    → runᵖ (SSP.tester a P.∘ᵖ SSP.resource N) ≈Mℚ runᵖ (SSP.tester a P.∘ᵖ SSP.resource M)
  native-composed-output a ξ = trans (SSP.Correspondence.execution N (SSP.tester a) tt a (Residual.initial N) ξ)
    (trans (fixed-information-to-strategies N M (Residual.initial N) (Residual.initial M) equal a ξ)
      (sym (SSP.Correspondence.execution M (SSP.tester a) tt a (Residual.initial M) ξ)))

  acceptance : (a : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) Bool)
    → Experiment.run N (mapStrategy accept (Model.legal N a))
      ≈Mℚ Experiment.run M (mapStrategy accept (Model.legal M a))
  acceptance a ξ = trans (Model.map-execution N accept (Model.legal N a) (Residual.initial N) ξ)
    (trans (lookupᴰℚ-Dmap accept (Experiment.run N (Model.legal N a)) ξ)
      (trans (fixed-information-to-native N M (Residual.initial N) (Residual.initial M) equal a (ξ ∘ accept))
        (trans (sym (lookupᴰℚ-Dmap accept (Experiment.run M (Model.legal M a)) ξ))
          (sym (Model.map-execution M accept (Model.legal M a) (Residual.initial M) ξ)))))

  composed-output : (a : P.Calls (F.Uniform (Command I O) (Response O) (command-dec I O)) Bool)
    → runᵖ (SSP.tester (mapStrategy accept (Model.legal N a)) P.∘ᵖ SSP.resource N)
      ≈Mℚ runᵖ (SSP.tester (mapStrategy accept (Model.legal M a)) P.∘ᵖ SSP.resource M)
  composed-output a ξ = trans (SSP.Correspondence.agreement N (mapStrategy accept (Model.legal N a)) ξ)
    (trans (>>=ᴹ-congʳ return⊥ (Experiment.run N (mapStrategy accept (Model.legal N a)))
      (Experiment.run M (mapStrategy accept (Model.legal M a))) (acceptance a) ξ)
      (sym (SSP.Correspondence.agreement M (mapStrategy accept (Model.legal M a)) ξ)))

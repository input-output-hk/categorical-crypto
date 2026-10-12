{-# OPTIONS --safe --without-K --guardedness #-}

-- One accepted plaintext and one delivery decision. Only the exact original
-- ciphertext modulo E₀ is deliverable; every other decision drops the message.
-- Later activations have the fixed error boundary of the total Fine semantics.

module CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol where

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base hiding (drop)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀

open Terms Σ₀
open Run E₀

wire : ObjTerm
wire = Var (port tt tt)

ports : ObjTerm
ports = wire ⊗₀ wire

start pending finished : Fin 3
start = zero
pending = suc zero
finished = suc (suc zero)

error notice deliver drop : Rcp [] tt
error = app (cst 2) []
notice = app (cst 0) []
deliver = app (cst 0) []
drop = app (cst 1) []

error-output : TerminalOutput (Outs (Var void) ports)
error-output = terminal-output (msg tt) (there (here refl)) error

Γ : Fin 3 → List ⊤
Γ zero = []
Γ (suc zero) = tt ∷ tt ∷ tt ∷ []
Γ (suc (suc zero)) = []

private
  fail : ∀ {Δ} → React 3 Γ (Outs (Var void) ports) Δ
  fail = emit finished [] (there (here refl)) (closed-payload (msg tt) error)

  encrypted : Rcp (tt ∷ tt ∷ tt ∷ []) tt
  encrypted = app enc (var (there (there (here refl))) ∷ var (there (here refl)) ∷ var (here refl) ∷ [])

  dummy-cipher : Rcp (tt ∷ tt ∷ tt ∷ []) tt
  dummy-cipher = app enc (app (cst 0) [] ∷ var (there (here refl)) ∷ var (here refl) ∷ [])

  send : Bool → Bool → React 3 Γ (Outs (Var void) ports) (tt ∷ [])
  send dummy leaky = new tt (new tt (emit pending
    (var (there (here refl)) ∷ selected ∷ var (there (there (here refl))) ∷ [])
    (here refl) exposed))
    where
    selected : Rcp (tt ∷ tt ∷ tt ∷ []) tt
    selected = if dummy then dummy-cipher else encrypted
    exposed : Rcp (tt ∷ tt ∷ tt ∷ []) tt
    exposed = if leaky then var (there (there (here refl))) else selected

  receive : Bool → React 3 Γ (Outs (Var void) ports) (tt ∷ tt ∷ tt ∷ tt ∷ [])
  receive dummy = test (var (here refl)) (var (there (there (here refl))))
    (emit finished [] (there (here refl)) selected) fail
    where
    selected : Rcp (tt ∷ tt ∷ tt ∷ tt ∷ []) tt
    selected = if dummy then var (there (there (there (here refl))))
      else app dec (var (here refl) ∷ var (there (here refl)) ∷ [])

channel : (dummy leaky : Bool) → Role (Var void) ports
channel dummy leaky = record
  { n = 3 ; Γ = Γ ; start = start ; fresh = refl
  ; react = λ where
      zero (here refl) _ → fail
      zero (there (here refl)) _ → send dummy leaky
      zero (there (there ())) _
      (suc zero) (here refl) _ → receive dummy
      (suc zero) (there (here refl)) _ → fail
      (suc zero) (there (there ())) _
      (suc (suc zero)) (here refl) _ → fail
      (suc (suc zero)) (there (here refl)) _ → fail
      (suc (suc zero)) (there (there ())) _ }

real-role simulated-role leaky-role : Role (Var void) ports
real-role = channel false false
simulated-role = channel true false
leaky-role = channel false true

channel-terminal : ∀ dummy leaky → Terminal (channel dummy leaky) error-output
channel-terminal dummy leaky = record
  { terminal = finished
  ; boundary = λ where (here refl) _ → terminal-jump ; (there (here refl)) _ → terminal-jump ; (there (there ())) _
  ; failures = λ where
      zero (here refl) _ → emit
      zero (there (here refl)) _ → new (new emit)
      zero (there (there ())) _
      (suc zero) (here refl) _ → test emit terminal-jump
      (suc zero) (there (here refl)) _ → emit
      (suc zero) (there (there ())) _
      (suc (suc zero)) (here refl) _ → emit
      (suc (suc zero)) (there (here refl)) _ → emit
      (suc (suc zero)) (there (there ())) _ }

Γⁱ : Fin 3 → List ⊤
Γⁱ zero = []
Γⁱ (suc zero) = tt ∷ []
Γⁱ (suc (suc zero)) = []

private
  failⁱ : ∀ {Δ} → React 3 Γⁱ (Outs (Var void) ports) Δ
  failⁱ = emit finished [] (there (here refl)) (closed-payload (msg tt) error)

ideal-role : Role (Var void) ports
ideal-role = record
  { n = 3 ; Γ = Γⁱ ; start = start ; fresh = refl
  ; react = λ where
      zero (here refl) _ → failⁱ
      zero (there (here refl)) _ → emit pending (var (here refl) ∷ []) (here refl) (closed-payload (msg tt) notice)
      zero (there (there ())) _
      (suc zero) (here refl) _ → test (var (here refl)) (closed-payload (msg tt) deliver)
        (emit finished [] (there (here refl)) (var (there (here refl)))) failⁱ
      (suc zero) (there (here refl)) _ → failⁱ
      (suc zero) (there (there ())) _
      (suc (suc zero)) (here refl) _ → failⁱ
      (suc (suc zero)) (there (here refl)) _ → failⁱ
      (suc (suc zero)) (there (there ())) _ }

Γˢ : Fin 3 → List ⊤
Γˢ zero = []
Γˢ (suc zero) = tt ∷ []
Γˢ (suc (suc zero)) = []

simulator-role : Role wire wire
simulator-role = record
  { n = 3 ; Γ = Γˢ ; start = start ; fresh = refl
  ; react = λ where
      zero (here refl) _ → new tt (new tt (emit pending
        (app enc (app (cst 0) [] ∷ var (there (here refl)) ∷ var (here refl) ∷ []) ∷ [])
        (there (here refl)) (app enc (app (cst 0) [] ∷ var (there (here refl)) ∷ var (here refl) ∷ []))))
      zero (there (here refl)) _ → emit finished [] (here refl) (closed-payload (msg tt) drop)
      zero (there (there ())) _
      (suc zero) (here refl) _ → emit finished [] (there (here refl)) (closed-payload (msg tt) error)
      (suc zero) (there (here refl)) _ → test (var (here refl)) (var (there (here refl)))
        (emit finished [] (here refl) (closed-payload (msg tt) deliver))
        (emit finished [] (here refl) (closed-payload (msg tt) drop))
      (suc zero) (there (there ())) _
      (suc (suc zero)) (here refl) _ → emit finished [] (there (here refl)) (closed-payload (msg tt) error)
      (suc (suc zero)) (there (here refl)) _ → emit finished [] (here refl) (closed-payload (msg tt) drop)
      (suc (suc zero)) (there (there ())) _ }

smt simulated leaky ideal : HomTerm (Var void) ports
smt = var (tt , (tt , tt) , real-role)
simulated = var (tt , (tt , tt) , simulated-role)
leaky = var (tt , (tt , tt) , leaky-role)
ideal = var (tt , (tt , tt) , ideal-role)

simulator : HomTerm wire wire
simulator = var (tt , tt , simulator-role)

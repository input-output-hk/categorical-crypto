{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.GlobalClasses where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

payload : Bool → Set
payload false = ⊤
payload true = Bool

open import CategoricalCrypto.CSP.Interface Bool payload
open import CategoricalCrypto.CSP.Network Bool payload
open import CategoricalCrypto.CSP.Observation Bool payload
open import CategoricalCrypto.CSP.Operational Bool payload
open import CategoricalCrypto.CSP.SingleBox Bool payload
import CategoricalCrypto.CSP.Process as P

open Interface

out : Interface
out = interface singleton (λ _ → port false output)

inp : Interface
inp = interface singleton (λ _ → port false input)

module O = P (Event out) ℕ ⊤
module R = P (Event inp) ℕ ⊤

sender : O.Tree
sender = O.menu (λ _ → just (O.return tt)) (λ _ → nothing)

receiver : R.Tree
receiver = R.menu (λ _ → just (R.return tt)) (λ _ → nothing)

tri : Shape
tri = (singleton ⊕ singleton) ⊕ singleton

first second third : ⟨ tri ⟩
first = inj₁ (inj₁ tt)
second = inj₁ (inj₂ tt)
third = inj₂ tt

labels : R.Tree → ⟨ tri ⟩ → Component
labels p (inj₁ (inj₁ tt)) = Embed.component out ℕ sender
labels p (inj₁ (inj₂ tt)) = Embed.component inp ℕ receiver
labels p (inj₂ tt) = Embed.component inp ℕ p

closed : R.Tree → Network I I
closed p = record
  { components = boxes tri (labels p) ; private-shape = singleton ; private-sort = λ _ → false
  ; local-wire = λ { (inj₁ (inj₁ tt) , tt) → inj₁ tt ; (inj₁ (inj₂ tt) , tt) → inj₁ tt ; (inj₂ tt , tt) → inj₁ tt }
  ; wire-type = λ { (inj₁ (inj₁ tt) , tt) → refl ; (inj₁ (inj₂ tt) , tt) → refl ; (inj₂ tt , tt) → refl }
  ; aliases = [] ; alias-type = λ () }

exposed : R.Tree → Network I out
exposed p = record
  { components = boxes tri (labels p) ; private-shape = singleton ; private-sort = λ _ → false
  ; local-wire = λ { (inj₁ (inj₁ tt) , tt) → inj₁ tt ; (inj₁ (inj₂ tt) , tt) → inj₁ tt ; (inj₂ tt , tt) → inj₁ tt }
  ; wire-type = λ { (inj₁ (inj₁ tt) , tt) → refl ; (inj₁ (inj₂ tt) , tt) → refl ; (inj₂ tt , tt) → refl }
  ; aliases = (inj₁ tt , inj₂ (inj₂ tt)) ∷ []
  ; alias-type = λ { (here refl) → refl ; (there ()) } }

module Three = Execution (closed receiver)
module ThreeW = Wiring (closed receiver)

all-returned : ThreeW.State
all-returned (inj₁ (inj₁ tt)) = O.return tt
all-returned (inj₁ (inj₂ tt)) = R.return tt
all-returned (inj₂ tt) = R.return tt

all-gather : Three.Gather (inj₁ tt) tt ThreeW.initial-state all-returned
all-gather = record
  { selected = λ { (inj₁ (inj₁ tt)) → just tt ; (inj₁ (inj₂ tt)) → just tt ; (inj₂ tt) → just tt }
  ; incident = λ { {inj₁ (inj₁ tt)} tt conn → tt , refl ; {inj₁ (inj₂ tt)} tt conn → tt , refl ; {inj₂ tt} tt conn → tt , refl }
  ; on-wire = λ { {inj₁ (inj₁ tt)} {tt} refl → ThreeW.same ; {inj₁ (inj₂ tt)} {tt} refl → ThreeW.same ; {inj₂ tt} {tt} refl → ThreeW.same }
  ; advances = λ { {inj₁ (inj₁ tt)} {tt} refl → O.sVis refl refl ; {inj₁ (inj₂ tt)} {tt} refl → R.sVis refl refl ; {inj₂ tt} {tt} refl → R.sVis refl refl }
  ; absent = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} () ; {inj₂ tt} () }
  ; inhabited = first , tt , refl }

all-handshake : Three.Handshake all-gather
all-handshake = record
  { output-support = record
      { provider = first , tt , refl , refl
      ; unique-output = λ { {inj₁ (inj₁ tt)} _ _ → refl ; {inj₁ (inj₂ tt)} _ () ; {inj₂ tt} _ () } }
  ; listener = second , tt , refl , refl , (λ ()) }

three-advance-atomically : Three._─[_]→_ Three.initial-configuration Three.τ (Three.running all-returned)
three-advance-atomically = Three.hidden tt all-gather (λ { (inj₁ ()) ; (inj₂ ()) }) all-handshake

three-joint-completion : Three._─[_]→_ (Three.running all-returned) (Three.visible Three.√) Three.completed
three-joint-completion = Three.finish first (λ { (inj₁ (inj₁ tt)) → refl ; (inj₁ (inj₂ tt)) → refl ; (inj₂ tt) → refl })

module Blocked = Execution (closed R.stop)
module BlockedW = Wiring (closed R.stop)

blocked-class-no-gather : ∀ {x q′} → ¬ (Blocked.Gather (inj₁ tt) x BlockedW.initial-state q′)
blocked-class-no-gather gather with Blocked.Gather.incident gather {k = third} tt BlockedW.same
... | p , chosen = R.stop-no-step (Blocked.Gather.advances gather {k = third} {p = p} chosen)

module Public = Execution (exposed R.stop)
module PublicW = Wiring (exposed R.stop)

public-connection : PublicW.Connected (inj₁ tt) (Public.external-name (inj₂ tt))
public-connection = PublicW.alias (here refl)

boundary-cannot-bypass-blocked-participant : ∀ {x q′} → ¬
  (Public.Gather (Public.external-name (inj₂ tt)) x PublicW.initial-state q′)
boundary-cannot-bypass-blocked-participant gather with Public.Gather.incident gather {k = third} tt public-connection
... | p , chosen = R.stop-no-step (Public.Gather.advances gather {k = third} {p = p} chosen)

public-no-visible-event : ∀ {x q′} → ¬ (Public._─[_]→_ Public.initial-configuration
  (Public.visible (Public.event (inj₂ tt , x))) q′)
public-no-visible-event (Public.exterior x gather compatible) = boundary-cannot-bypass-blocked-participant gather

sender-no-silent : ∀ {q} → ¬ (O._─[_]→_ sender O.τ q)
sender-no-silent (O.sSil ())
sender-no-silent (O.sTau refl ())

receiver-no-silent : ∀ {q} → ¬ (R._─[_]→_ receiver R.τ q)
receiver-no-silent (R.sSil ())
receiver-no-silent (R.sTau refl ())

blocked-class-no-silent : ∀ {q} → ¬ (Blocked._─[_]→_ Blocked.initial-configuration Blocked.τ q)
blocked-class-no-silent (Blocked.internal {k = inj₁ (inj₁ tt)} step) = sender-no-silent step
blocked-class-no-silent (Blocked.internal {k = inj₁ (inj₂ tt)} step) = receiver-no-silent step
blocked-class-no-silent (Blocked.internal {k = inj₂ tt} step) = R.stop-no-step step
blocked-class-no-silent (Blocked.hidden {n = inj₁ tt} x gather confined handshake) = blocked-class-no-gather gather
blocked-class-no-silent (Blocked.hidden {n = inj₂ (inj₁ ())} x gather confined handshake)
blocked-class-no-silent (Blocked.hidden {n = inj₂ (inj₂ ())} x gather confined handshake)

blocked-class-no-completion : ∀ {q} → ¬ (Blocked._─[_]→_
  Blocked.initial-configuration (Blocked.visible Blocked.√) q)
blocked-class-no-completion (Blocked.finish _ ready) with ready first
... | ()

module BlockedObs = Observe (closed R.stop)

blocked-class-stable : BlockedObs.Stable Blocked.initial-configuration
blocked-class-stable = (λ _ → blocked-class-no-silent) , (λ _ → blocked-class-no-completion)

blocked-class-refuses-all : BlockedObs.Refuses Blocked.initial-configuration (λ _ → ⊤)
blocked-class-refuses-all = blocked-class-stable , refuses
  where
    refuses : ∀ e → ⊤ → ∀ q → ¬ (Blocked._─[_]→_ Blocked.initial-configuration (Blocked.visible e) q)
    refuses Blocked.√ _ _ step = blocked-class-no-completion step
    refuses (Blocked.event (inj₁ () , _))
    refuses (Blocked.event (inj₂ () , _))

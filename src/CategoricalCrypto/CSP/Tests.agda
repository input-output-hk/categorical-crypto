{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Tests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
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
open import CategoricalCrypto.CSP.Operational Bool payload
open import CategoricalCrypto.CSP.Plugging Bool payload
open import CategoricalCrypto.CSP.SingleBox Bool payload
open import CategoricalCrypto.CSP.Wiring Bool payload
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

producer : Network I out
producer = Embed.network out ℕ sender

consumer : Network out I
consumer = record
  { components = boxes singleton (λ _ → record { boundary = inp ; Branch = ℕ ; initial = receiver })
  ; private-shape = empty ; private-sort = λ ()
  ; local-wire = λ { (tt , tt) → inj₂ (inj₁ tt) }
  ; wire-type = λ { (tt , tt) → refl }
  ; aliases = [] ; alias-type = λ () }

experiment : Network I I
experiment = consumer ∘ producer

module Hidden = Execution experiment
module HWire = Wiring experiment

after-hidden : HWire.State
after-hidden = Hidden.update (inj₂ tt) (R.return tt)
  (Hidden.update (inj₁ tt) (O.return tt) HWire.initial-state)

hidden-gather : Hidden.Gather (inj₁ (inj₁ (inj₂ tt))) tt HWire.initial-state after-hidden
hidden-gather = record
  { selected = λ { (inj₁ tt) → just tt ; (inj₂ tt) → just tt }
  ; incident = λ { {inj₁ tt} tt conn → tt , refl ; {inj₂ tt} tt conn → tt , refl }
  ; on-wire = λ { {inj₁ tt} {tt} refl → HWire.same ; {inj₂ tt} {tt} refl → HWire.same }
  ; advances = λ { {inj₁ tt} {tt} refl → O.sVis refl refl ; {inj₂ tt} {tt} refl → R.sVis refl refl }
  ; absent = λ { {inj₁ tt} () ; {inj₂ tt} () } ; inhabited = inj₁ tt , tt , refl }

hidden-handshake : Hidden.Handshake hidden-gather
hidden-handshake = record
  { output-support = record
      { provider = inj₁ tt , tt , refl , refl
      ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ tt} _ () } }
  ; listener = inj₂ tt , tt , refl , refl , (λ ()) }

hidden-rendezvous : Hidden._─[_]→_ Hidden.initial-configuration Hidden.τ
  (Hidden.running (Hidden.update (inj₂ tt) (R.return tt)
    (Hidden.update (inj₁ tt) (O.return tt) (Wiring.initial-state experiment))))
hidden-rendezvous = Hidden.hidden tt hidden-gather (λ { (inj₁ ()) ; (inj₂ ()) }) hidden-handshake

joint-return : Hidden._─[_]→_
  (Hidden.running (Hidden.update (inj₂ tt) (R.return tt)
    (Hidden.update (inj₁ tt) (O.return tt) (Wiring.initial-state experiment))))
  (Hidden.visible Hidden.√) Hidden.completed
joint-return = Hidden.finish (inj₁ tt) (λ { (inj₁ tt) → refl ; (inj₂ tt) → refl })

module Empty = Execution (id {I})

empty-alias-no-step : ∀ {l q} → ¬ (Empty._─[_]→_ Empty.initial-configuration l q)
empty-alias-no-step (Empty.internal {k = ()} _)
empty-alias-no-step (Empty.exterior {e = inj₁ ()} x gather compatible)
empty-alias-no-step (Empty.exterior {e = inj₂ ()} x gather compatible)
empty-alias-no-step (Empty.hidden x gather confined handshake) with Empty.Gather.inhabited gather
... | () , rest
empty-alias-no-step (Empty.finish () _)

empty-alias-no-divergence : ¬ (Empty.Diverges Empty.initial-configuration)
empty-alias-no-divergence d = empty-alias-no-step (Empty.Diverges.step d)

module Alias = Execution ((id {out}) ∘ producer)
module AWire = Wiring ((id {out}) ∘ producer)
module AP = Plug producer (id {out})

alias-gather : Alias.Gather (Alias.external-name (inj₂ tt)) tt AWire.initial-state
  (Alias.update (inj₁ tt) (O.return tt) AWire.initial-state)
alias-gather = record
  { selected = λ { (inj₁ tt) → just tt ; (inj₂ ()) }
  ; incident = λ { {inj₁ tt} tt conn → tt , refl ; {inj₂ ()} }
  ; on-wire = λ { {inj₁ tt} {tt} refl → AP.right-connected (identity-alias tt) ; {inj₂ ()} }
  ; advances = λ { {inj₁ tt} {tt} refl → O.sVis refl refl ; {inj₂ ()} }
  ; absent = λ { {inj₁ tt} () ; {inj₂ ()} } ; inhabited = inj₁ tt , tt , refl }

alias-compatible : Alias.BoundaryCompatible alias-gather
alias-compatible = Alias.output-boundary refl record
  { provider = inj₁ tt , tt , refl , refl
  ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ ()} } }

transparent-visible-offer : Alias._─[_]→_ Alias.initial-configuration
  (Alias.visible (Alias.event (inj₂ tt , tt)))
  (Alias.running (Alias.update (inj₁ tt) (O.return tt)
    (Wiring.initial-state ((id {out}) ∘ producer))))
transparent-visible-offer = Alias.exterior tt alias-gather alias-compatible

alias-cannot-finish-initially : ¬ (Alias._─[_]→_ Alias.initial-configuration (Alias.visible Alias.√) Alias.completed)
alias-cannot-finish-initially (Alias.finish _ ready) with ready (inj₁ tt)
... | ()

returned : Network I out
returned = Embed.network out ℕ (O.return tt)

blocked : Network I out
blocked = Embed.network out ℕ O.stop

spinning : Network I out
spinning = Embed.network out ℕ O.div

module Blocked = Execution (returned ⊗₁ blocked)
module Spinning = Execution (returned ⊗₁ spinning)

returned-blocked-no-completion : ∀ {q} → ¬ (Blocked._─[_]→_
  Blocked.initial-configuration (Blocked.visible Blocked.√) q)
returned-blocked-no-completion (Blocked.finish _ ready) with ready (inj₂ tt)
... | ()

returned-spinning-no-completion : ∀ {q} → ¬ (Spinning._─[_]→_
  Spinning.initial-configuration (Spinning.visible Spinning.√) q)
returned-spinning-no-completion (Spinning.finish _ ready) with ready (inj₂ tt)
... | ()

spinning-continuation : (q : Wiring.State (returned ⊗₁ spinning)) → q (inj₂ tt) ≡ O.div
                      → Spinning.Diverges (Spinning.running q)
Spinning.Diverges.next (spinning-continuation q eq) = Spinning.running (Spinning.update (inj₂ tt) O.div q)
Spinning.Diverges.step (spinning-continuation q eq) = Spinning.internal {k = inj₂ tt}
  (O.sSil (cong O.Tree.force eq))
Spinning.Diverges.rest (spinning-continuation q eq) = spinning-continuation (Spinning.update (inj₂ tt) O.div q) refl

returned-spinning-divergence : Spinning.Diverges Spinning.initial-configuration
returned-spinning-divergence = spinning-continuation (Wiring.initial-state (returned ⊗₁ spinning)) refl

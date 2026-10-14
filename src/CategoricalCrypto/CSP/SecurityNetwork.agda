{-# OPTIONS --safe --without-K --guardedness #-}

-- Stateful challenge/response converter; components use the constructive native
-- Tree fragment (unit return, arbitrary payload events, no internal branches).
module CategoricalCrypto.CSP.SecurityNetwork where

open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.Empty
open import Data.List.Base
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

Payload : Bool → Set
Payload false = ⊤
Payload true = Bool

open import CategoricalCrypto.CSP.Coherence Bool Payload _≟_
open import CategoricalCrypto.CSP.Interface Bool Payload
open import CategoricalCrypto.CSP.Network Bool Payload
open import CategoricalCrypto.CSP.Observation Bool Payload
open import CategoricalCrypto.CSP.Operational Bool Payload
open import CategoricalCrypto.CSP.Plugging Bool Payload
open import CategoricalCrypto.CSP.SingleBox Bool Payload
open import CategoricalCrypto.CSP.Structure Bool Payload
open import CategoricalCrypto.CSP.Wiring Bool Payload
import CategoricalCrypto.CSP.Process as P

B Ω Y : Interface
B = interface singleton (λ _ → port true output)
Ω = B
Y = interface singleton (λ _ → port false output)

X : Interface
X = interface (singleton ⊕ singleton) [ (λ _ → port true input) , (λ _ → port true output) ]′

adapter-boundary : Interface
adapter-boundary = interface (singleton ⊕ (singleton ⊕ singleton))
  [ (λ _ → port false input) , [ (λ _ → port true input) , (λ _ → port true output) ]′ ]′

consumer-boundary : Interface
consumer-boundary = interface ((singleton ⊕ singleton) ⊕ (singleton ⊕ singleton))
  [ [ (λ _ → port true output) , (λ _ → port true input) ]′
  , [ (λ _ → port true input) , (λ _ → port true output) ]′ ]′

module G = P (Event (Y ⊗₀ B)) ⊥ ⊤
module H = P (Event adapter-boundary) ⊥ ⊤
module T = P (Event consumer-boundary) ⊥ ⊤

honest : G.Tree
honest = G.menu (λ { (inj₁ tt , _) → nothing ; (inj₂ tt , false) → just (G.return tt)
  ; (inj₂ tt , true) → nothing }) (λ ())

ideal-process : G.Tree
ideal-process = G.menu (λ { (inj₁ tt , tt) → just honest ; (inj₂ tt , _) → nothing }) (λ ())

response : Bool → H.Tree
response c = H.menu (λ { (inj₁ tt , _) → nothing ; (inj₂ (inj₁ tt) , _) → nothing
  ; (inj₂ (inj₂ tt) , r) → if r xor c then just (H.return tt) else nothing }) (λ ())

challenge : H.Tree
challenge = H.menu (λ { (inj₁ tt , _) → nothing ; (inj₂ (inj₁ tt) , c) → just (response c)
  ; (inj₂ (inj₂ tt) , _) → nothing }) (λ ())

adapter-process : H.Tree
adapter-process = H.menu (λ { (inj₁ tt , tt) → just challenge ; (inj₂ _ , _) → nothing }) (λ ())

verdict : Bool → T.Tree
verdict b = T.menu (λ { (inj₁ _ , _) → nothing ; (inj₂ (inj₁ tt) , _) → nothing
  ; (inj₂ (inj₂ tt) , v) → if v xor not b then just (T.return tt) else nothing }) (λ ())

read-honest : Bool → T.Tree
read-honest r = T.menu (λ { (inj₁ _ , _) → nothing ; (inj₂ (inj₁ tt) , b) → just (verdict (r ∧ not b))
  ; (inj₂ (inj₂ tt) , _) → nothing }) (λ ())

read-response : T.Tree
read-response = T.menu (λ { (inj₁ (inj₁ tt) , _) → nothing
  ; (inj₁ (inj₂ tt) , r) → just (read-honest r) ; (inj₂ _ , _) → nothing }) (λ ())

consumer-process : T.Tree
consumer-process = T.menu (λ { (inj₁ (inj₁ tt) , false) → just read-response
  ; (inj₁ (inj₁ tt) , true) → nothing ; (inj₁ (inj₂ tt) , _) → nothing ; (inj₂ _ , _) → nothing }) (λ ())

g : Network I (Y ⊗₀ B)
g = Embed.network (Y ⊗₀ B) ⊥ ideal-process

h : Network Y X
h = record
  { components = boxes singleton (λ _ → record { boundary = adapter-boundary ; Branch = ⊥ ; initial = adapter-process })
  ; private-shape = empty ; private-sort = λ ()
  ; local-wire = λ { (tt , inj₁ tt) → inj₂ (inj₁ tt) ; (tt , inj₂ p) → inj₂ (inj₂ p) }
  ; wire-type = λ { (tt , inj₁ tt) → refl ; (tt , inj₂ (inj₁ tt)) → refl ; (tt , inj₂ (inj₂ tt)) → refl }
  ; aliases = [] ; alias-type = λ () }

t : Network (X ⊗₀ B) Ω
t = record
  { components = boxes singleton (λ _ → record { boundary = consumer-boundary ; Branch = ⊥ ; initial = consumer-process })
  ; private-shape = empty ; private-sort = λ ()
  ; local-wire = λ { (tt , inj₁ p) → inj₂ (inj₁ (inj₁ p)) ; (tt , inj₂ (inj₁ tt)) → inj₂ (inj₁ (inj₂ tt))
      ; (tt , inj₂ (inj₂ tt)) → inj₂ (inj₂ tt) }
  ; wire-type = λ { (tt , inj₁ (inj₁ tt)) → refl ; (tt , inj₁ (inj₂ tt)) → refl ; (tt , inj₂ (inj₁ tt)) → refl
      ; (tt , inj₂ (inj₂ tt)) → refl }
  ; aliases = [] ; alias-type = λ () }

-- f is a flat two-box network, with a single private unit channel. Its honest
-- port is exposed directly, rather than retained as a composition alias.
f : Network I (X ⊗₀ B)
f = record
  { components = boxes (singleton ⊕ singleton)
      [ (λ _ → Embed.component (Y ⊗₀ B) ⊥ ideal-process) , (λ _ → Network.components h .Boxes.label tt) ]′
  ; private-shape = singleton ; private-sort = λ _ → false
  ; local-wire = λ { (inj₁ tt , inj₁ tt) → inj₁ tt ; (inj₁ tt , inj₂ tt) → inj₂ (inj₂ (inj₂ tt))
      ; (inj₂ tt , inj₁ tt) → inj₁ tt ; (inj₂ tt , inj₂ p) → inj₂ (inj₂ (inj₁ p)) }
  ; wire-type = λ { (inj₁ tt , inj₁ tt) → refl ; (inj₁ tt , inj₂ tt) → refl
      ; (inj₂ tt , inj₁ tt) → refl ; (inj₂ tt , inj₂ (inj₁ tt)) → refl ; (inj₂ tt , inj₂ (inj₂ tt)) → refl }
  ; aliases = [] ; alias-type = λ () }

composite : Network I (X ⊗₀ B)
composite = (h ⊗₁ id) ∘ g

module F = Wiring f
module C = Wiring composite

flat-name : C.Name → F.Name
flat-name (inj₁ (inj₁ (inj₁ ())))
flat-name (inj₁ (inj₁ (inj₂ (inj₁ tt)))) = inj₁ tt
flat-name (inj₁ (inj₁ (inj₂ (inj₂ tt)))) = inj₂ (inj₂ (inj₂ tt))
flat-name (inj₁ (inj₂ (inj₁ ())))
flat-name (inj₁ (inj₂ (inj₂ ())))
flat-name (inj₂ e) = inj₂ e

expanded-name : F.Name → C.Name
expanded-name (inj₁ tt) = inj₁ (inj₁ (inj₂ (inj₁ tt)))
expanded-name (inj₂ e) = inj₂ e

honest-alias : C.Connected (inj₁ (inj₁ (inj₂ (inj₂ tt)))) (inj₂ (inj₂ (inj₂ tt)))
honest-alias = C.alias (here refl)

collapse-connected : ∀ {u v} → C.Connected u v → F.Connected (flat-name u) (flat-name v)
collapse-connected = map-connected flat-name (λ { (here refl) → F.same ; (there ()) })

expand-connected : ∀ {u v} → F.Connected u v → C.Connected (expanded-name u) (expanded-name v)
expand-connected = map-connected expanded-name (λ ())

flattening : f ≅ composite
flattening = record
  { forward = record
      { box-map = λ { (inj₁ tt) → inj₁ tt ; (inj₂ tt) → inj₂ (inj₁ tt) }
      ; box-label = λ { (inj₁ tt) → refl ; (inj₂ tt) → refl }
      ; name-map = expanded-name
      ; name-type = λ { (inj₁ tt) → refl ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ (inj₁ (inj₁ tt)))) → refl
          ; (inj₂ (inj₂ (inj₁ (inj₂ tt)))) → refl ; (inj₂ (inj₂ (inj₂ tt))) → refl }
      ; connected = expand-connected ; external = λ _ → C.same
      ; local = λ { (inj₁ tt) (inj₁ tt) → C.same ; (inj₁ tt) (inj₂ tt) → C.reverse honest-alias
          ; (inj₂ tt) (inj₁ tt) → C.same ; (inj₂ tt) (inj₂ (inj₁ tt)) → C.same ; (inj₂ tt) (inj₂ (inj₂ tt)) → C.same } }
  ; backward = record
      { box-map = λ { (inj₁ tt) → inj₁ tt ; (inj₂ (inj₁ tt)) → inj₂ tt ; (inj₂ (inj₂ ())) }
      ; box-label = λ { (inj₁ tt) → refl ; (inj₂ (inj₁ tt)) → refl ; (inj₂ (inj₂ ())) }
      ; name-map = flat-name
      ; name-type = λ { (inj₁ (inj₁ (inj₁ ()))) ; (inj₁ (inj₁ (inj₂ (inj₁ tt)))) → refl
          ; (inj₁ (inj₁ (inj₂ (inj₂ tt)))) → refl ; (inj₁ (inj₂ (inj₁ ()))) ; (inj₁ (inj₂ (inj₂ ())))
          ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ (inj₁ (inj₁ tt)))) → refl
          ; (inj₂ (inj₂ (inj₁ (inj₂ tt)))) → refl ; (inj₂ (inj₂ (inj₂ tt))) → refl }
      ; connected = collapse-connected ; external = λ _ → F.same
      ; local = λ { (inj₁ tt) (inj₁ tt) → F.same ; (inj₁ tt) (inj₂ tt) → F.same
          ; (inj₂ (inj₁ tt)) (inj₁ tt) → F.same ; (inj₂ (inj₁ tt)) (inj₂ (inj₁ tt)) → F.same
          ; (inj₂ (inj₁ tt)) (inj₂ (inj₂ tt)) → F.same ; (inj₂ (inj₂ ())) } }
  ; boxes-left = λ { (inj₁ tt) → refl ; (inj₂ tt) → refl }
  ; boxes-right = λ { (inj₁ tt) → refl ; (inj₂ (inj₁ tt)) → refl ; (inj₂ (inj₂ ())) }
  ; names-left = λ { (inj₁ tt) → F.same ; (inj₂ _) → F.same }
  ; names-right = λ { (inj₁ (inj₁ (inj₁ ()))) ; (inj₁ (inj₁ (inj₂ (inj₁ tt)))) → C.same
      ; (inj₁ (inj₁ (inj₂ (inj₂ tt)))) → C.reverse honest-alias
      ; (inj₁ (inj₂ (inj₁ ()))) ; (inj₁ (inj₂ (inj₂ ()))) ; (inj₂ _) → C.same } }

real-experiment : Network I Ω
real-experiment = t ∘ f

ideal-experiment : Network I Ω
ideal-experiment = t ∘ composite

module Real = Execution real-experiment
module RealWire = Wiring real-experiment

real-connected-equality : ∀ {u v} → RealWire.Connected u v → u ≡ v
real-connected-equality RealWire.same = refl
real-connected-equality (RealWire.alias ())
real-connected-equality (RealWire.reverse p) = sym (real-connected-equality p)
real-connected-equality (RealWire.join p q) = trans (real-connected-equality p) (real-connected-equality q)

q₀ q₁ q₂ q₃ q₄ q₅ : RealWire.State
q₀ = RealWire.initial-state
q₁ = λ { (inj₁ (inj₁ tt)) → honest ; (inj₁ (inj₂ tt)) → challenge ; (inj₂ tt) → consumer-process }
q₂ = λ { (inj₁ (inj₁ tt)) → honest ; (inj₁ (inj₂ tt)) → response false ; (inj₂ tt) → read-response }
q₃ = λ { (inj₁ (inj₁ tt)) → honest ; (inj₁ (inj₂ tt)) → H.return tt ; (inj₂ tt) → read-honest true }
q₄ = λ { (inj₁ (inj₁ tt)) → G.return tt ; (inj₁ (inj₂ tt)) → H.return tt ; (inj₂ tt) → verdict true }
q₅ = λ { (inj₁ (inj₁ tt)) → G.return tt ; (inj₁ (inj₂ tt)) → H.return tt ; (inj₂ tt) → T.return tt }

token-name challenge-name response-name honest-name : RealWire.Name
token-name = inj₁ (inj₁ (inj₁ tt))
challenge-name = inj₁ (inj₁ (inj₂ (inj₁ (inj₁ tt))))
response-name = inj₁ (inj₁ (inj₂ (inj₁ (inj₂ tt))))
honest-name = inj₁ (inj₁ (inj₂ (inj₂ tt)))

no-consumer-token : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₂ tt , p)) token-name → ⊥
no-consumer-token (inj₁ p) c with real-connected-equality c
... | ()
no-consumer-token (inj₂ (inj₁ tt)) c with real-connected-equality c
... | ()
no-consumer-token (inj₂ (inj₂ tt)) c with real-connected-equality c
... | ()

token-gather : Real.Gather token-name tt q₀ q₁
token-gather = record
  { selected = λ { (inj₁ (inj₁ tt)) → just (inj₁ tt) ; (inj₁ (inj₂ tt)) → just (inj₁ tt) ; (inj₂ tt) → nothing }
  ; incident = λ { {inj₁ (inj₁ tt)} _ _ → inj₁ tt , refl ; {inj₁ (inj₂ tt)} _ _ → inj₁ tt , refl
      ; {inj₂ tt} p c → ⊥-elim (no-consumer-token p c) }
  ; on-wire = λ { {inj₁ (inj₁ tt)} {.(inj₁ tt)} refl → RealWire.same
      ; {inj₁ (inj₂ tt)} {.(inj₁ tt)} refl → RealWire.same ; {inj₂ tt} () }
  ; advances = λ { {inj₁ (inj₁ tt)} {.(inj₁ tt)} refl → G.sVis refl refl
      ; {inj₁ (inj₂ tt)} {.(inj₁ tt)} refl → H.sVis refl refl ; {inj₂ tt} () }
  ; absent = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} () ; {inj₂ tt} _ → refl }
  ; inhabited = inj₁ (inj₁ tt) , inj₁ tt , refl }

token-hidden : Real.Private token-name
token-hidden (inj₁ ()) c
token-hidden (inj₂ tt) c with real-connected-equality c
... | ()

token-step : Real._─[_]→_ (Real.running q₀) Real.τ (Real.running q₁)
token-step = Real.hidden tt token-gather token-hidden record
  { output-support = record
      { provider = inj₁ (inj₁ tt) , inj₁ tt , refl , refl
      ; unique-output = λ { {inj₁ (inj₁ tt)} _ _ → refl ; {inj₁ (inj₂ tt)} refl () ; {inj₂ tt} () } }
  ; listener = inj₁ (inj₂ tt) , inj₁ tt , refl , refl , (λ ()) }

no-ideal-challenge : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₁ (inj₁ tt) , p)) challenge-name → ⊥
no-ideal-challenge (inj₁ tt) c with real-connected-equality c
... | ()
no-ideal-challenge (inj₂ tt) c with real-connected-equality c
... | ()

challenge-gather : Real.Gather challenge-name false q₁ q₂
challenge-gather = record
  { selected = λ { (inj₁ (inj₁ tt)) → nothing ; (inj₁ (inj₂ tt)) → just (inj₂ (inj₁ tt))
      ; (inj₂ tt) → just (inj₁ (inj₁ tt)) }
  ; incident = λ { {inj₁ (inj₁ tt)} p c → ⊥-elim (no-ideal-challenge p c)
      ; {inj₁ (inj₂ tt)} _ _ → inj₂ (inj₁ tt) , refl ; {inj₂ tt} _ _ → inj₁ (inj₁ tt) , refl }
  ; on-wire = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {.(inj₂ (inj₁ tt))} refl → RealWire.same
      ; {inj₂ tt} {.(inj₁ (inj₁ tt))} refl → RealWire.same }
  ; advances = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {.(inj₂ (inj₁ tt))} refl → subst
        (λ x → H._─[_]→_ challenge (H.visible (H.event (inj₂ (inj₁ tt) , x))) (response false))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₁ (inj₂ tt) , inj₂ (inj₁ tt)} RealWire.same)) refl false))
        (H.sVis refl refl)
      ; {inj₂ tt} {.(inj₁ (inj₁ tt))} refl → subst
        (λ x → T._─[_]→_ consumer-process (T.visible (T.event (inj₁ (inj₁ tt) , x))) read-response)
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₂ tt , inj₁ (inj₁ tt)} RealWire.same)) refl false))
        (T.sVis refl refl) }
  ; absent = λ { {inj₁ (inj₁ tt)} _ → refl ; {inj₁ (inj₂ tt)} () ; {inj₂ tt} () }
  ; inhabited = inj₂ tt , inj₁ (inj₁ tt) , refl }

challenge-hidden : Real.Private challenge-name
challenge-hidden (inj₁ ()) c
challenge-hidden (inj₂ tt) c with real-connected-equality c
... | ()

challenge-step : Real._─[_]→_ (Real.running q₁) Real.τ (Real.running q₂)
challenge-step = Real.hidden false challenge-gather challenge-hidden record
  { output-support = record
      { provider = inj₂ tt , inj₁ (inj₁ tt) , refl , refl
      ; unique-output = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} refl () ; {inj₂ tt} _ _ → refl } }
  ; listener = inj₁ (inj₂ tt) , inj₂ (inj₁ tt) , refl , refl , (λ ()) }

no-ideal-response : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₁ (inj₁ tt) , p)) response-name → ⊥
no-ideal-response (inj₁ tt) c with real-connected-equality c
... | ()
no-ideal-response (inj₂ tt) c with real-connected-equality c
... | ()

response-gather : Real.Gather response-name true q₂ q₃
response-gather = record
  { selected = λ { (inj₁ (inj₁ tt)) → nothing ; (inj₁ (inj₂ tt)) → just (inj₂ (inj₂ tt))
      ; (inj₂ tt) → just (inj₁ (inj₂ tt)) }
  ; incident = λ { {inj₁ (inj₁ tt)} p c → ⊥-elim (no-ideal-response p c)
      ; {inj₁ (inj₂ tt)} _ _ → inj₂ (inj₂ tt) , refl ; {inj₂ tt} _ _ → inj₁ (inj₂ tt) , refl }
  ; on-wire = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {.(inj₂ (inj₂ tt))} refl → RealWire.same
      ; {inj₂ tt} {.(inj₁ (inj₂ tt))} refl → RealWire.same }
  ; advances = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {.(inj₂ (inj₂ tt))} refl → subst
        (λ x → H._─[_]→_ (response false) (H.visible (H.event (inj₂ (inj₂ tt) , x))) (H.return tt))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₁ (inj₂ tt) , inj₂ (inj₂ tt)} RealWire.same)) refl true))
        (H.sVis refl refl)
      ; {inj₂ tt} {.(inj₁ (inj₂ tt))} refl → subst
        (λ x → T._─[_]→_ read-response (T.visible (T.event (inj₁ (inj₂ tt) , x))) (read-honest true))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₂ tt , inj₁ (inj₂ tt)} RealWire.same)) refl true))
        (T.sVis refl refl) }
  ; absent = λ { {inj₁ (inj₁ tt)} _ → refl ; {inj₁ (inj₂ tt)} () ; {inj₂ tt} () }
  ; inhabited = inj₁ (inj₂ tt) , inj₂ (inj₂ tt) , refl }

response-hidden : Real.Private response-name
response-hidden (inj₁ ()) c
response-hidden (inj₂ tt) c with real-connected-equality c
... | ()

response-step : Real._─[_]→_ (Real.running q₂) Real.τ (Real.running q₃)
response-step = Real.hidden true response-gather response-hidden record
  { output-support = record
      { provider = inj₁ (inj₂ tt) , inj₂ (inj₂ tt) , refl , refl
      ; unique-output = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} _ _ → refl ; {inj₂ tt} refl () } }
  ; listener = inj₂ tt , inj₁ (inj₂ tt) , refl , refl , (λ ()) }

no-adapter-honest : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₁ (inj₂ tt) , p)) honest-name → ⊥
no-adapter-honest (inj₁ tt) c with real-connected-equality c
... | ()
no-adapter-honest (inj₂ (inj₁ tt)) c with real-connected-equality c
... | ()
no-adapter-honest (inj₂ (inj₂ tt)) c with real-connected-equality c
... | ()

honest-gather : Real.Gather honest-name false q₃ q₄
honest-gather = record
  { selected = λ { (inj₁ (inj₁ tt)) → just (inj₂ tt) ; (inj₁ (inj₂ tt)) → nothing ; (inj₂ tt) → just (inj₂ (inj₁ tt)) }
  ; incident = λ { {inj₁ (inj₁ tt)} _ _ → inj₂ tt , refl
      ; {inj₁ (inj₂ tt)} p c → ⊥-elim (no-adapter-honest p c) ; {inj₂ tt} _ _ → inj₂ (inj₁ tt) , refl }
  ; on-wire = λ { {inj₁ (inj₁ tt)} {.(inj₂ tt)} refl → RealWire.same ; {inj₁ (inj₂ tt)} ()
      ; {inj₂ tt} {.(inj₂ (inj₁ tt))} refl → RealWire.same }
  ; advances = λ { {inj₁ (inj₁ tt)} {.(inj₂ tt)} refl → subst
        (λ x → G._─[_]→_ honest (G.visible (G.event (inj₂ tt , x))) (G.return tt))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₁ (inj₁ tt) , inj₂ tt} RealWire.same)) refl false))
        (G.sVis refl refl)
      ; {inj₁ (inj₂ tt)} ()
      ; {inj₂ tt} {.(inj₂ (inj₁ tt))} refl → subst
        (λ x → T._─[_]→_ (read-honest true) (T.visible (T.event (inj₂ (inj₁ tt) , x))) (verdict true))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₂ tt , inj₂ (inj₁ tt)} RealWire.same)) refl false))
        (T.sVis refl refl) }
  ; absent = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} _ → refl ; {inj₂ tt} () }
  ; inhabited = inj₁ (inj₁ tt) , inj₂ tt , refl }

honest-hidden : Real.Private honest-name
honest-hidden (inj₁ ()) c
honest-hidden (inj₂ tt) c with real-connected-equality c
... | ()

honest-step : Real._─[_]→_ (Real.running q₃) Real.τ (Real.running q₄)
honest-step = Real.hidden false honest-gather honest-hidden record
  { output-support = record
      { provider = inj₁ (inj₁ tt) , inj₂ tt , refl , refl
      ; unique-output = λ { {inj₁ (inj₁ tt)} _ _ → refl ; {inj₁ (inj₂ tt)} () ; {inj₂ tt} refl () } }
  ; listener = inj₂ tt , inj₂ (inj₁ tt) , refl , refl , (λ ()) }

no-ideal-verdict : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₁ (inj₁ tt) , p))
  (Real.external-name (inj₂ tt)) → ⊥
no-ideal-verdict (inj₁ tt) c with real-connected-equality c
... | ()
no-ideal-verdict (inj₂ tt) c with real-connected-equality c
... | ()

no-adapter-verdict : ∀ p → RealWire.Connected (Network.local-wire real-experiment (inj₁ (inj₂ tt) , p))
  (Real.external-name (inj₂ tt)) → ⊥
no-adapter-verdict (inj₁ tt) c with real-connected-equality c
... | ()
no-adapter-verdict (inj₂ (inj₁ tt)) c with real-connected-equality c
... | ()
no-adapter-verdict (inj₂ (inj₂ tt)) c with real-connected-equality c
... | ()

verdict-gather : Real.Gather (Real.external-name (inj₂ tt)) true q₄ q₅
verdict-gather = record
  { selected = λ { (inj₁ _) → nothing ; (inj₂ tt) → just (inj₂ (inj₂ tt)) }
  ; incident = λ { {inj₁ (inj₁ tt)} p c → ⊥-elim (no-ideal-verdict p c)
      ; {inj₁ (inj₂ tt)} p c → ⊥-elim (no-adapter-verdict p c) ; {inj₂ tt} _ _ → inj₂ (inj₂ tt) , refl }
  ; on-wire = λ { {inj₁ _} () ; {inj₂ tt} {.(inj₂ (inj₂ tt))} refl → RealWire.same }
  ; advances = λ { {inj₁ _} () ; {inj₂ tt} {.(inj₂ (inj₂ tt))} refl → subst
        (λ x → T._─[_]→_ (verdict true) (T.visible (T.event (inj₂ (inj₂ tt) , x))) (T.return tt))
        (sym (payload-coherent (sym (Real.class-payload {kp = inj₂ tt , inj₂ (inj₂ tt)} RealWire.same)) refl true))
        (T.sVis refl refl) }
  ; absent = λ { {inj₁ (inj₁ tt)} _ → refl ; {inj₁ (inj₂ tt)} _ → refl ; {inj₂ tt} () }
  ; inhabited = inj₂ tt , inj₂ (inj₂ tt) , refl }

verdict-step : Real._─[_]→_ (Real.running q₄) (Real.visible (Real.event (inj₂ tt , true))) (Real.running q₅)
verdict-step = Real.exterior true verdict-gather (Real.output-boundary refl record
  { provider = inj₂ tt , inj₂ (inj₂ tt) , refl , refl
  ; unique-output = λ { {inj₁ _} () ; {inj₂ tt} _ _ → refl } })

joint-completion : Real._─[_]→_ (Real.running q₅) (Real.visible Real.√) Real.completed
joint-completion = Real.finish (inj₂ tt) (λ { (inj₁ (inj₁ tt)) → refl ; (inj₁ (inj₂ tt)) → refl ; (inj₂ tt) → refl })

module RealObs = Observe real-experiment

verdict-trace : List Real.Visible
verdict-trace = Real.event (inj₂ tt , true) ∷ Real.√ ∷ []

real-execution : RealObs.Executes Real.initial-configuration verdict-trace Real.completed
real-execution = RealObs.silent-step token-step (RealObs.silent-step challenge-step
  (RealObs.silent-step response-step (RealObs.silent-step honest-step
    (RealObs.visible-step verdict-step (RealObs.visible-step joint-completion RealObs.done)))))

real-verdict-trace : NativeObservation.traces (observations real-experiment) verdict-trace
real-verdict-trace = Real.completed , real-execution

real-terminal-refusal : ∀ refusal → NativeObservation.failures (observations real-experiment) verdict-trace refusal
real-terminal-refusal refusal = Real.completed , real-execution , RealObs.completed-refuses refusal

adapter-answers : ∀ c → H._─[_]→_ (response c) (H.visible (H.event (inj₂ (inj₂ tt) , not c))) (H.return tt)
adapter-answers false = H.sVis refl refl
adapter-answers true = H.sVis refl refl

consumer-payload-verdict : ∀ r b → T._─[_]→_ (verdict (r ∧ not b))
  (T.visible (T.event (inj₂ (inj₂ tt) , r ∧ not b))) (T.return tt)
consumer-payload-verdict false false = T.sVis refl refl
consumer-payload-verdict false true = T.sVis refl refl
consumer-payload-verdict true false = T.sVis refl refl
consumer-payload-verdict true true = T.sVis refl refl

grades-unequal : X ≢ Y
grades-unequal ()

real-grade-inhabited : ⟨ Interface.shape X ⟩
real-grade-inhabited = inj₁ tt

ideal-grade-inhabited : ⟨ Interface.shape Y ⟩
ideal-grade-inhabited = tt

converter-has-box : ⟨ Boxes.shape (Network.components h) ⟩
converter-has-box = tt

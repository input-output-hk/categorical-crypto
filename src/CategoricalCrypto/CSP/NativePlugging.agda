{-# OPTIONS --safe --without-K --guardedness #-}

-- The two connected private classes are produced by actual tensor/plugging.
-- Each atomic offer has both a kernel execution and a source Par/Hide step;
-- structural interchange transports the execution, while native strong
-- interchange relates its source continuations. See NativeInterchange for pin.
module CategoricalCrypto.CSP.NativePlugging (X B : Set) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes)

import CategoricalCrypto.CSP.Coherence as Coherence
open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Interchange ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Plugging ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.SemanticInvariance ⊤ (λ _ → X)
  (λ { tt tt → yes refl })
open import CategoricalCrypto.CSP.SingleBox ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Transport ⊤ (λ _ → X)
import CategoricalCrypto.CSP.NativeDisjoint as Disjoint
import CategoricalCrypto.CSP.NativeInterchange as Native

module D = Disjoint X B
module C = Coherence ⊤ (λ _ → X) D.U.unit-equality
module N = Native X B
module L = D.L
module G = D.G

inp : Interface
inp = interface singleton (λ _ → port tt input)

consumer : L.Tree → Network D.out I
consumer p = record
  { components = boxes singleton (λ _ → record { boundary = inp ; Branch = D.O.Index ; initial = p })
  ; private-shape = empty ; private-sort = λ ()
  ; local-wire = λ { (tt , tt) → inj₂ (inj₁ tt) } ; wire-type = λ { (tt , tt) → refl }
  ; aliases = [] ; alias-type = λ () }

module Four (p₁ p₂ q₁ q₂ : L.Tree) where
  a = Embed.network D.out D.O.Index p₁
  b = Embed.network D.out D.O.Index p₂
  c = consumer q₁
  d = consumer q₂
  left-network = (c ⊗₁ d) ∘ (a ⊗₁ b)
  right-network = (c ∘ a) ⊗₁ (d ∘ b)
  module K = Execution left-network
  module R = Execution right-network
  module W = Wiring left-network
  module E = Exchange a b c d

  operational-interchange : OperationalTransport left-network right-network
  operational-interchange = structural→operational E.plugging-tensor-interchange
  module T = OperationalTransport operational-interchange

  quad : N.Quad
  quad = record
    { p₁ = D.Rename false p₁ ; p₂ = D.Rename true p₂
    ; q₁ = D.Rename false q₁ ; q₂ = D.Rename true q₂
    ; cp₁ = D.confined false p₁ ; cp₂ = D.confined true p₂
    ; cq₁ = D.confined false q₁ ; cq₂ = D.confined true q₂ }

  native-interchange = N.hidden-interchange quad

  connected-equality : ∀ {u v} → W.Connected u v → u ≡ v
  connected-equality W.same = refl
  connected-equality (W.alias ())
  connected-equality (W.reverse conn) = sym (connected-equality conn)
  connected-equality (W.join u v) = trans (connected-equality u) (connected-equality v)

  first second third fourth : K.Box
  first = inj₁ (inj₁ tt)
  second = inj₁ (inj₂ tt)
  third = inj₂ (inj₁ tt)
  fourth = inj₂ (inj₂ tt)

  wire₁ wire₂ : W.Name
  wire₁ = inj₁ (inj₁ (inj₂ (inj₁ tt)))
  wire₂ = inj₁ (inj₁ (inj₂ (inj₂ tt)))

  no-cross : ∀ {n x q r} (g : K.Gather n x q r)
    → K.Gather.selected g first ≡ just tt → K.Gather.selected g fourth ≡ just tt → ⊥
  no-cross g chosen₁ chosen₂ = impossible
    (trans (connected-equality (K.Gather.on-wire g chosen₁))
      (sym (connected-equality (K.Gather.on-wire g chosen₂))))
    where
    impossible : wire₁ ≡ wire₂ → ⊥
    impossible ()

  module Pair₁ {x p′ q′} (sp : L._─[_]→_ p₁ (L.visible (L.event (tt , x))) p′)
    (sq : L._─[_]→_ q₁ (L.visible (L.event (tt , x))) q′) where

    after : W.State
    after = K.update third q′ (K.update first p′ W.initial-state)

    gather : K.Gather wire₁ x W.initial-state after
    gather = record
      { selected = λ { (inj₁ (inj₁ tt)) → just tt ; (inj₁ (inj₂ tt)) → nothing
                     ; (inj₂ (inj₁ tt)) → just tt ; (inj₂ (inj₂ tt)) → nothing }
      ; incident = λ
          { {inj₁ (inj₁ tt)} tt conn → tt , refl
          ; {inj₁ (inj₂ tt)} tt conn → ⊥-elim (impossible (connected-equality conn))
          ; {inj₂ (inj₁ tt)} tt conn → tt , refl
          ; {inj₂ (inj₂ tt)} tt conn → ⊥-elim (impossible (connected-equality conn)) }
      ; on-wire = λ { {inj₁ (inj₁ tt)} {tt} refl → W.same ; {inj₁ (inj₂ tt)} ()
                      ; {inj₂ (inj₁ tt)} {tt} refl → W.same ; {inj₂ (inj₂ tt)} () }
      ; advances = λ { {inj₁ (inj₁ tt)} {tt} refl → subst
          (λ y → L._─[_]→_ p₁ (L.visible (L.event (tt , y))) p′)
          (sym (C.payload-coherent (sym (K.class-payload {kp = first , tt} W.same)) refl x)) sp
        ; {inj₁ (inj₂ tt)} ()
        ; {inj₂ (inj₁ tt)} {tt} refl → subst
          (λ y → L._─[_]→_ q₁ (L.visible (L.event (tt , y))) q′)
          (sym (C.payload-coherent (sym (K.class-payload {kp = third , tt} W.same)) refl x)) sq
        ; {inj₂ (inj₂ tt)} () }
      ; absent = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} _ → refl
                     ; {inj₂ (inj₁ tt)} () ; {inj₂ (inj₂ tt)} _ → refl }
      ; inhabited = first , tt , refl }
      where
      impossible : wire₂ ≡ wire₁ → ⊥
      impossible ()

    handshake : K.Handshake gather
    handshake = record
      { output-support = record
          { provider = first , tt , refl , refl
          ; unique-output = λ { {inj₁ (inj₁ tt)} _ _ → refl ; {inj₁ (inj₂ tt)} ()
                                ; {inj₂ (inj₁ tt)} _ () ; {inj₂ (inj₂ tt)} () } }
      ; listener = third , tt , refl , refl , (λ ()) }

    kernel-left : K._─[_]→_ K.initial-configuration K.τ (K.running after)
    kernel-left = K.hidden x gather
      (λ { (inj₁ (inj₁ ())) ; (inj₁ (inj₂ ())) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) handshake

    kernel-right : Σ R.Configuration (λ r → R._─[_]→_ R.initial-configuration R.τ r × T.Related (K.running after) r)
    kernel-right = T.forward T.initial kernel-left

    move = N.pair₁ {f = quad} (D.rename-event false x sp) (D.rename-event false x sq)
    next = N.change-q₁ (N.change-p₁ quad (D.rename-event false x sp)) (D.rename-event false x sq)

    native-left : G._─[_]→_ (N.A.Hide (λ _ → true) (N.left-source quad)) G.τ
      (N.A.Hide (λ _ → true) (N.left-source next))
    native-left = N.AP.hide-hidden (λ _ → true) refl (N.atomic-left move)

    native-right : G._─[_]→_ (N.A.Hide (λ _ → true) (N.right-source quad)) G.τ
      (N.A.Hide (λ _ → true) (N.right-source next))
    native-right = N.AP.hide-hidden (λ _ → true) refl (N.atomic-right move)

    continuation = N.hidden-interchange next

  module Pair₂ {x p′ q′} (sp : L._─[_]→_ p₂ (L.visible (L.event (tt , x))) p′)
    (sq : L._─[_]→_ q₂ (L.visible (L.event (tt , x))) q′) where

    after : W.State
    after = K.update fourth q′ (K.update second p′ W.initial-state)

    gather : K.Gather wire₂ x W.initial-state after
    gather = record
      { selected = λ { (inj₁ (inj₁ tt)) → nothing ; (inj₁ (inj₂ tt)) → just tt
                     ; (inj₂ (inj₁ tt)) → nothing ; (inj₂ (inj₂ tt)) → just tt }
      ; incident = λ
          { {inj₁ (inj₁ tt)} tt conn → ⊥-elim (impossible (connected-equality conn))
          ; {inj₁ (inj₂ tt)} tt conn → tt , refl
          ; {inj₂ (inj₁ tt)} tt conn → ⊥-elim (impossible (connected-equality conn))
          ; {inj₂ (inj₂ tt)} tt conn → tt , refl }
      ; on-wire = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {tt} refl → W.same
                      ; {inj₂ (inj₁ tt)} () ; {inj₂ (inj₂ tt)} {tt} refl → W.same }
      ; advances = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} {tt} refl → subst
          (λ y → L._─[_]→_ p₂ (L.visible (L.event (tt , y))) p′)
          (sym (C.payload-coherent (sym (K.class-payload {kp = second , tt} W.same)) refl x)) sp
        ; {inj₂ (inj₁ tt)} () ; {inj₂ (inj₂ tt)} {tt} refl → subst
          (λ y → L._─[_]→_ q₂ (L.visible (L.event (tt , y))) q′)
          (sym (C.payload-coherent (sym (K.class-payload {kp = fourth , tt} W.same)) refl x)) sq }
      ; absent = λ { {inj₁ (inj₁ tt)} _ → refl ; {inj₁ (inj₂ tt)} ()
                     ; {inj₂ (inj₁ tt)} _ → refl ; {inj₂ (inj₂ tt)} () }
      ; inhabited = second , tt , refl }
      where
      impossible : wire₁ ≡ wire₂ → ⊥
      impossible ()

    handshake : K.Handshake gather
    handshake = record
      { output-support = record
          { provider = second , tt , refl , refl
          ; unique-output = λ { {inj₁ (inj₁ tt)} () ; {inj₁ (inj₂ tt)} _ _ → refl
                                ; {inj₂ (inj₁ tt)} () ; {inj₂ (inj₂ tt)} _ () } }
      ; listener = fourth , tt , refl , refl , (λ ()) }

    kernel-left : K._─[_]→_ K.initial-configuration K.τ (K.running after)
    kernel-left = K.hidden x gather
      (λ { (inj₁ (inj₁ ())) ; (inj₁ (inj₂ ())) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) handshake

    kernel-right : Σ R.Configuration (λ r → R._─[_]→_ R.initial-configuration R.τ r × T.Related (K.running after) r)
    kernel-right = T.forward T.initial kernel-left

    move = N.pair₂ {f = quad} (D.rename-event true x sp) (D.rename-event true x sq)
    next = N.change-q₂ (N.change-p₂ quad (D.rename-event true x sp)) (D.rename-event true x sq)

    native-left : G._─[_]→_ (N.A.Hide (λ _ → true) (N.left-source quad)) G.τ
      (N.A.Hide (λ _ → true) (N.left-source next))
    native-left = N.AP.hide-hidden (λ _ → true) refl (N.atomic-left move)

    native-right : G._─[_]→_ (N.A.Hide (λ _ → true) (N.right-source quad)) G.τ
      (N.A.Hide (λ _ → true) (N.right-source next))
    native-right = N.AP.hide-hidden (λ _ → true) refl (N.atomic-right move)

    continuation = N.hidden-interchange next

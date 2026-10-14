{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.SingleBox (Sort : Set) (Payload : Sort → Set) where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (DecidableEquality)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload
import CategoricalCrypto.CSP.Process as P

open Interface
open Port
open Boxes renaming (shape to box-shape)

module Embed (A : Interface) (Branch : Set) where
  module Native = P (Event A) Branch ⊤

  component : Native.Tree → Component
  component p = record { boundary = A ; Branch = Branch ; initial = p }

  network : Native.Tree → Network I A
  network p = record
    { components = boxes singleton (λ _ → component p)
    ; private-shape = empty ; private-sort = λ ()
    ; local-wire = λ { (tt , i) → inj₂ (inj₂ i) }
    ; wire-type = λ { (tt , i) → refl }
    ; aliases = [] ; alias-type = λ () }

  module Correspondence (initial : Native.Tree) where
    module E = Execution (network initial)
    module W = Wiring (network initial)
    open E

    configuration : Native.Tree → Configuration
    configuration p = running (λ _ → p)

    step-label : Native.Label → Label
    step-label Native.τ = τ
    step-label (Native.visible (Native.event (p , x))) = visible (event (inj₂ p , x))
    step-label (Native.visible (Native.√ tt)) = visible √

    -- The source √ target is deadlock; the network settles explicitly. Both
    -- have no further transitions, rather than introducing a silent return.
    successor : Native.Label → Native.Tree → Configuration
    successor (Native.visible (Native.√ _)) p = completed
    successor Native.τ p = configuration p
    successor (Native.visible (Native.event _)) p = configuration p

    gather-offer : ∀ {p q} i x → Native._─[_]→_ p (Native.visible (Native.event (i , x))) q
      → Gather (external-name (inj₂ i)) x (λ _ → p) (λ _ → q)
    gather-offer i x step = record
      { selected = λ _ → just i ; incident = λ { {tt} p conn → i , refl }
      ; on-wire = λ { {tt} {.i} refl → W.same }
      ; advances = λ { {tt} {.i} refl → step }
      ; absent = λ { {tt} () } ; inhabited = tt , i , refl }

    gather-compatible : ∀ {p q} i x (step : Native._─[_]→_ p (Native.visible (Native.event (i , x))) q)
      → BoundaryCompatible (gather-offer i x step)
    gather-compatible i x step with polarity (ports A i) in pol
    ... | input = input-boundary pol (λ { {tt} {.i} refl → pol })
    ... | output = output-boundary pol record
      { provider = tt , i , refl , pol ; unique-output = λ { {tt} _ _ → refl } }

    native-step : ∀ {p l q} → Native._─[_]→_ p l q
                → configuration p ─[ step-label l ]→ successor l q
    native-step (Native.sRet {r = tt} eq) = finish tt (λ { tt → eq })
    native-step (Native.sSil eq) = internal (Native.sSil eq)
    native-step (Native.sVis {e = (i , x)} eq offered) =
      exterior x (gather-offer i x (Native.sVis eq offered)) (gather-compatible i x (Native.sVis eq offered))
    native-step (Native.sTau eq offered) = internal (Native.sTau eq offered)


    data Related : Native.Tree → Configuration → Set where
      live : ∀ p → Related p (configuration p)
      settled : Related Native.stop completed

    native-label : Label → Native.Label
    native-label τ = Native.τ
    native-label (visible √) = Native.visible (Native.√ tt)
    native-label (visible (event (inj₁ () , _)))
    native-label (visible (event (inj₂ i , x))) = Native.visible (Native.event (i , x))

    connected-equality : ∀ {u v} → W.Connected u v → u ≡ v
    connected-equality W.same = refl
    connected-equality (W.alias ())
    connected-equality (W.reverse p) = sym (connected-equality p)
    connected-equality (W.join p q) = trans (connected-equality p) (connected-equality q)

    module Converse (_≟Sort_ : DecidableEquality Sort) where
      open Decidable⇒UIP _≟Sort_ using (≡-irrelevant)

      network-step : ∀ {p l q} → configuration p ─[ l ]→ q
                   → Σ Native.Tree (λ p′ → Native._─[_]→_ p (native-label l) p′ × Related p′ q)
      network-step (internal {k = tt} step) = _ , step , live _
      network-step (exterior {e = inj₁ ()} x gather compatible)
      network-step {p = p} (exterior {q′ = q′} {e = inj₂ i} x gather compatible) with Gather.inhabited gather
      ... | tt , j , chosen with connected-equality (Gather.on-wire gather chosen)
      ... | refl = q′ tt , subst (λ y → Native._─[_]→_ p (Native.visible (Native.event (i , y))) (q′ tt))
        (cong (λ eq → subst Payload eq x)
          (≡-irrelevant (sym (class-payload (Gather.on-wire gather chosen))) refl))
        (Gather.advances gather chosen) , live (q′ tt)
      network-step (hidden x gather confined handshake) with Handshake.listener handshake
      ... | tt , i , chosen , pol , distinct = ⊥-elim (distinct refl)
      network-step (finish tt ready) = Native.stop , Native.sRet (ready tt) , settled

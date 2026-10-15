{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.BinaryNetwork (X B : Set) where

open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.SingleBox ⊤ (λ _ → X)
import CategoricalCrypto.CSP.Process as Process

out inp : Interface
out = interface singleton (λ _ → port tt output)
inp = interface singleton (λ _ → port tt input)

module P = Process (⊤ × X) B ⊤

closed : P.Tree → P.Tree → Network I I
closed p q = record
  { components = boxes (singleton ⊕ singleton) (λ { (inj₁ tt) → Embed.component out B p ; (inj₂ tt) → Embed.component inp B q })
  ; private-shape = singleton ; private-sort = λ _ → tt
  ; local-wire = λ { (inj₁ tt , tt) → inj₁ tt ; (inj₂ tt , tt) → inj₁ tt }
  ; wire-type = λ { (inj₁ tt , tt) → refl ; (inj₂ tt , tt) → refl }
  ; aliases = [] ; alias-type = λ () }

module Native (p₀ q₀ : P.Tree) where
  module E = Execution (closed p₀ q₀)
  module W = Wiring (closed p₀ q₀)

  pair : P.Tree → P.Tree → W.State
  pair p q (inj₁ tt) = p
  pair p q (inj₂ tt) = q

  gather-state : ∀ {q q′ x}
    → P._─[_]→_ (q (inj₁ tt)) (P.visible (P.event (tt , x))) (q′ (inj₁ tt))
    → P._─[_]→_ (q (inj₂ tt)) (P.visible (P.event (tt , x))) (q′ (inj₂ tt))
    → E.Gather (inj₁ tt) x q q′
  gather-state sp sq = record
    { selected = λ { (inj₁ tt) → just tt ; (inj₂ tt) → just tt }
    ; incident = λ { {inj₁ tt} tt _ → tt , refl ; {inj₂ tt} tt _ → tt , refl }
    ; on-wire = λ { {inj₁ tt} {tt} refl → W.same ; {inj₂ tt} {tt} refl → W.same }
    ; advances = λ { {inj₁ tt} {tt} refl → sp ; {inj₂ tt} {tt} refl → sq }
    ; absent = λ { {inj₁ tt} () ; {inj₂ tt} () }
    ; inhabited = inj₁ tt , tt , refl }

  gather : ∀ {p p′ q q′ x} → P._─[_]→_ p (P.visible (P.event (tt , x))) p′
    → P._─[_]→_ q (P.visible (P.event (tt , x))) q′
    → E.Gather (inj₁ tt) x (pair p q) (pair p′ q′)
  gather = gather-state

  handshake : ∀ {q q′ x} (g : E.Gather (inj₁ tt) x q q′) → E.Handshake g
  handshake g with E.Gather.incident g {k = inj₁ tt} tt W.same
    | E.Gather.incident g {k = inj₂ tt} tt W.same
  ... | tt , chosen-left | tt , chosen-right = record
    { output-support = record
      { provider = inj₁ tt , tt , chosen-left , refl
      ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ tt} _ () } }
    ; listener = inj₂ tt , tt , chosen-right , refl , (λ ()) }

  rendezvous : ∀ {p p′ q q′ x} → P._─[_]→_ p (P.visible (P.event (tt , x))) p′
    → P._─[_]→_ q (P.visible (P.event (tt , x))) q′
    → E._─[_]→_ (E.running (pair p q)) E.τ (E.running (pair p′ q′))
  rendezvous {x = x} left right = E.hidden x (gather left right)
    (λ { (inj₁ ()) ; (inj₂ ()) }) record
      { output-support = record
        { provider = inj₁ tt , tt , refl , refl
        ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ tt} _ () } }
      ; listener = inj₂ tt , tt , refl , refl , (λ ()) }

  completion : ∀ {p q} → P.Tree.force p ≡ P.ret tt → P.Tree.force q ≡ P.ret tt
    → E._─[_]→_ (E.running (pair p q)) (E.visible E.√) E.completed
  completion left right = E.finish (inj₁ tt) (λ { (inj₁ tt) → left ; (inj₂ tt) → right })

  data SilentMove (q q′ : W.State) : Set where
    left : P._─[_]→_ (q (inj₁ tt)) P.τ (q′ (inj₁ tt))
      → q′ (inj₂ tt) ≡ q (inj₂ tt) → SilentMove q q′
    right : P._─[_]→_ (q (inj₂ tt)) P.τ (q′ (inj₂ tt))
      → q′ (inj₁ tt) ≡ q (inj₁ tt) → SilentMove q q′
    exchange : (x : X)
      → P._─[_]→_ (q (inj₁ tt)) (P.visible (P.event (tt , x))) (q′ (inj₁ tt))
      → P._─[_]→_ (q (inj₂ tt)) (P.visible (P.event (tt , x))) (q′ (inj₂ tt))
      → SilentMove q q′

  constant-payload : ∀ {a b : ⊤} (eq : a ≡ b) (x : X) → subst (λ _ → X) eq x ≡ x
  constant-payload refl x = refl

  gather-left : ∀ {x q q′} → E.Gather (inj₁ tt) x q q′
    → P._─[_]→_ (q (inj₁ tt)) (P.visible (P.event (tt , x))) (q′ (inj₁ tt))
  gather-left {x} g with E.Gather.incident g {k = inj₁ tt} tt W.same
  ... | tt , chosen = subst (λ z → P._─[_]→_ _ (P.visible (P.event (tt , z))) _)
    (constant-payload _ x) (E.Gather.advances g chosen)

  gather-right : ∀ {x q q′} → E.Gather (inj₁ tt) x q q′
    → P._─[_]→_ (q (inj₂ tt)) (P.visible (P.event (tt , x))) (q′ (inj₂ tt))
  gather-right {x} g with E.Gather.incident g {k = inj₂ tt} tt W.same
  ... | tt , chosen = subst (λ z → P._─[_]→_ _ (P.visible (P.event (tt , z))) _)
    (constant-payload _ x) (E.Gather.advances g chosen)

  silent-classify : ∀ {q q′} → E._─[_]→_ (E.running q) E.τ (E.running q′) → SilentMove q q′
  silent-classify (E.internal {k = inj₁ tt} step) = SilentMove.left step refl
  silent-classify (E.internal {k = inj₂ tt} step) = SilentMove.right step refl
  silent-classify (E.hidden {n = inj₁ tt} x g confined handshake) = exchange x (gather-left g) (gather-right g)
  silent-classify (E.hidden {n = inj₂ (inj₁ ())} x g confined handshake)
  silent-classify (E.hidden {n = inj₂ (inj₂ ())} x g confined handshake)

{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.NativeCorrespondence as Common
import CategoricalCrypto.CSP.NativeDisjoint as Disjoint
import CategoricalCrypto.CSP.NativeInterchange as Interchange
import CategoricalCrypto.CSP.NativePlugging as Plugging

-- Payload and internal branch types remain arbitrary in these witnesses.
module Private (X B : Set) (x : X) where
  open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
  open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
  open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X)
  open Common X B
  open L.Tree

  offer : L.Tree
  offer = L.menu (λ _ → just (L.return tt)) (λ _ → nothing)

  two = one ∙ one
  three = one ∙ (one ∙ one)

  polarity₂ : ⟨ shape+ two ⟩ → Polarity
  polarity₂ (inj₁ tt) = output
  polarity₂ (inj₂ tt) = input

  polarity₃ : ⟨ shape+ three ⟩ → Polarity
  polarity₃ (inj₁ tt) = output
  polarity₃ (inj₂ _) = input

  only₂ : ∀ k → polarity₂ k ≡ output → k ≡ inj₁ tt
  only₂ (inj₁ tt) _ = refl
  only₂ (inj₂ tt) ()

  only₃ : ∀ k → polarity₃ k ≡ output → k ≡ inj₁ tt
  only₃ (inj₁ tt) _ = refl
  only₃ (inj₂ _) ()

  module Pair = Closed two polarity₂ (inj₁ tt) (inj₂ tt) refl only₂ refl (λ ()) (λ _ → offer)
  module Triple = Closed three polarity₃ (inj₁ tt) (inj₂ (inj₁ tt)) refl only₃ refl (λ ()) (λ _ → offer)

  private-two-correspondence = Pair.initial-correspondence
  private-three-correspondence = Triple.initial-correspondence

  private-two-native : Pair.native (λ _ → offer) L.─[ L.τ ]→ Pair.native (λ _ → L.return tt)
  private-two-native = Pair.native-hidden {q = λ _ → offer} {r = λ _ → L.return tt} x (λ _ → L.sVis refl refl)

  private-two-network : Pair.K._─[_]→_ Pair.K.initial-configuration Pair.K.τ
    (Pair.K.running (λ _ → L.return tt))
  private-two-network = Pair.network-hidden x (λ _ → L.sVis refl refl)

  private-three-native : Triple.native (λ _ → offer) L.─[ L.τ ]→ Triple.native (λ _ → L.return tt)
  private-three-native = Triple.native-hidden {q = λ _ → offer} {r = λ _ → L.return tt} x (λ _ → L.sVis refl refl)

  private-three-all-advance : Triple.K._─[_]→_ Triple.K.initial-configuration Triple.K.τ
    (Triple.K.running (λ _ → L.return tt))
  private-three-all-advance = Triple.network-hidden x (λ _ → L.sVis refl refl)

  private-three-joint-return : Triple.K._─[_]→_ (Triple.K.running (λ _ → L.return tt))
    (Triple.K.visible Triple.K.√) Triple.K.completed
  private-three-joint-return = Triple.K.finish (inj₁ tt) (λ _ → refl)

  blocked-family : Family three
  blocked-family (inj₁ tt) = offer
  blocked-family (inj₂ (inj₁ tt)) = offer
  blocked-family (inj₂ (inj₂ tt)) = L.stop

  module Blocked = Closed three polarity₃ (inj₁ tt) (inj₂ (inj₁ tt)) refl only₃ refl (λ ()) blocked-family

  no-local-silent : ∀ {t} → ¬ (offer L.─[ L.τ ]→ t)
  no-local-silent (L.sSil ())
  no-local-silent (L.sTau refl ())

  blocked-class-no-step : ∀ {l c} → ¬ (Blocked.K._─[_]→_ Blocked.K.initial-configuration l c)
  blocked-class-no-step (Blocked.K.internal {k = inj₁ tt} sp) = no-local-silent sp
  blocked-class-no-step (Blocked.K.internal {k = inj₂ (inj₁ tt)} sp) = no-local-silent sp
  blocked-class-no-step (Blocked.K.internal {k = inj₂ (inj₂ tt)} sp) = L.stop-no-step sp
  blocked-class-no-step (Blocked.K.exterior {e = inj₁ ()} _ _ _)
  blocked-class-no-step (Blocked.K.exterior {e = inj₂ ()} _ _ _)
  blocked-class-no-step (Blocked.K.hidden _ g _ _) = L.stop-no-step (Blocked.gather-invert g (inj₂ (inj₂ tt)))
  blocked-class-no-step (Blocked.K.finish _ ready) with ready (inj₂ (inj₂ tt))
  ... | ()

  blocked-native-no-step : ∀ {l t} → ¬ (Blocked.native blocked-family L.─[ l ]→ t)
  blocked-native-no-step sp = reject (Blocked.native-step sp)
    where
    reject : ∀ {l t} → Σ Blocked.K.Label (λ kl → Σ Blocked.K.Configuration
      (λ c → Blocked.Matching l kl × Blocked.K._─[_]→_ Blocked.K.initial-configuration kl c × Blocked.Related t c)) → ⊥
    reject (_ , _ , _ , step , _) = blocked-class-no-step step

  blocked-native-no-divergence : ¬ (L.Diverges (Blocked.native blocked-family))
  blocked-native-no-divergence d = blocked-native-no-step (L.Diverges.step d)

  returned-blocked : Family two
  returned-blocked (inj₁ tt) = L.return tt
  returned-blocked (inj₂ tt) = L.stop
  module ReturnedBlocked = Closed two polarity₂ (inj₁ tt) (inj₂ tt) refl only₂ refl (λ ()) returned-blocked

  returned-blocked-no-completion : ∀ {c} → ¬ (ReturnedBlocked.K._─[_]→_ ReturnedBlocked.K.initial-configuration
    (ReturnedBlocked.K.visible ReturnedBlocked.K.√) c)
  returned-blocked-no-completion (ReturnedBlocked.K.finish _ ready) with ready (inj₂ tt)
  ... | ()

  returned-blocked-native-no-completion : ∀ {t} → ¬ (ReturnedBlocked.native returned-blocked
    L.─[ L.visible (L.√ tt) ]→ t)
  returned-blocked-native-no-completion sp = returned-blocked-no-completion
    (proj₁ (ReturnedBlocked.native-return-step sp))

  returned-spinning : Family two
  returned-spinning (inj₁ tt) = L.return tt
  returned-spinning (inj₂ tt) = L.div
  module Spinning = Closed two polarity₂ (inj₁ tt) (inj₂ tt) refl only₂ refl (λ ()) returned-spinning

  spinning-path : ∀ q → q (inj₂ tt) ≡ L.div → Spinning.K.Diverges (Spinning.K.running q)
  Spinning.K.Diverges.next (spinning-path q eq) = Spinning.K.running (Spinning.K.update (inj₂ tt) L.div q)
  Spinning.K.Diverges.step (spinning-path q eq) = Spinning.K.internal {k = inj₂ tt} (L.sSil (cong force eq))
  Spinning.K.Diverges.rest (spinning-path q eq) = spinning-path (Spinning.K.update (inj₂ tt) L.div q) refl

  returned-spinning-network-divergence : Spinning.K.Diverges Spinning.K.initial-configuration
  returned-spinning-network-divergence = spinning-path returned-spinning refl

  returned-spinning-native-divergence : L.Diverges (Spinning.native returned-spinning)
  returned-spinning-native-divergence = Spinning.network-divergence (Spinning.live returned-spinning)
    returned-spinning-network-divergence

  returned-spinning-no-completion : ∀ {c} → ¬ (Spinning.K._─[_]→_ Spinning.K.initial-configuration
    (Spinning.K.visible Spinning.K.√) c)
  returned-spinning-no-completion (Spinning.K.finish _ ready) with ready (inj₂ tt)
  ... | ()

  returned-spinning-native-no-completion : ∀ {t} → ¬ (Spinning.native returned-spinning
    L.─[ L.visible (L.√ tt) ]→ t)
  returned-spinning-native-no-completion sp = returned-spinning-no-completion
    (proj₁ (Spinning.native-return-step sp))

  out : Interface
  out = interface singleton (λ _ → port tt output)

  boundary-network : Family three → Network I out
  boundary-network initial = record
    { components = boxes (shape+ three)
        (λ k → record { boundary = Triple.boundary k ; Branch = O.Index ; initial = initial k })
    ; private-shape = empty ; private-sort = λ ()
    ; local-wire = λ { (k , tt) → inj₂ (inj₂ tt) } ; wire-type = λ { (k , tt) → refl }
    ; aliases = [] ; alias-type = λ () }

  module Boundary = Execution (boundary-network (λ _ → offer))
  module BoundaryWire = Wiring (boundary-network (λ _ → offer))
  module BoundaryBlocked = Execution (boundary-network blocked-family)
  module BoundaryBlockedWire = Wiring (boundary-network blocked-family)

  boundary-gather : Boundary.Gather (Boundary.external-name (inj₂ tt)) x
    BoundaryWire.initial-state (λ _ → L.return tt)
  boundary-gather = record
    { selected = λ _ → just tt ; incident = λ { {k} tt conn → tt , refl }
    ; on-wire = λ { {k} {tt} refl → BoundaryWire.same }
    ; advances = λ { {k} {tt} refl → L.sVis refl refl }
    ; absent = λ () ; inhabited = inj₁ tt , tt , refl }

  boundary-compatible : Boundary.BoundaryCompatible boundary-gather
  boundary-compatible = Boundary.output-boundary refl record
    { provider = inj₁ tt , tt , refl , refl
    ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ _} _ () } }

  boundary-three-all-advance : Boundary._─[_]→_ Boundary.initial-configuration
    (Boundary.visible (Boundary.event (inj₂ tt , x))) (Boundary.running (λ _ → L.return tt))
  boundary-three-all-advance = Boundary.exterior x boundary-gather boundary-compatible

  boundary-three-native-visible : fold three (λ _ → offer) L.─[ L.visible (L.event (tt , x)) ]→
    fold three (λ _ → L.return tt)
  boundary-three-native-visible = fold-event three {q = λ _ → offer} {r = λ _ → L.return tt}
    (tt , x) (λ _ → L.sVis refl refl)

  blocked-boundary-no-bypass : ∀ {y r} → ¬ (BoundaryBlocked._─[_]→_ BoundaryBlocked.initial-configuration
    (BoundaryBlocked.visible (BoundaryBlocked.event (inj₂ tt , y))) r)
  blocked-boundary-no-bypass (BoundaryBlocked.exterior _ g _)
    with BoundaryBlocked.Gather.incident g {k = inj₂ (inj₂ tt)} tt BoundaryBlockedWire.same
  ... | tt , chosen = L.stop-no-step (BoundaryBlocked.Gather.advances g chosen)

module Exterior (X B : Set) (x : X) where
  open Disjoint X B
  offer : L.Tree
  offer = L.menu (λ _ → just (L.return tt)) (λ _ → nothing)
  module Pair = TensorPair offer offer

  disjoint-correspondence = Pair.initial-correspondence

  exterior-left : Pair.K._─[_]→_ Pair.K.initial-configuration
    (Pair.K.visible (Pair.K.event (inj₂ (inj₁ tt) , x)))
    (Pair.K.running (Pair.K.update Pair.first (L.return tt) Pair.W.initial-state))
  exterior-left = Pair.K.exterior x (Pair.gather-left x (L.sVis refl refl)) Pair.left-compatible

  exterior-native = Pair.network-step exterior-left

  tensor-no-cross : ∀ {n y q r} (g : Pair.K.Gather n y q r)
    → Pair.K.Gather.selected g Pair.first ≡ just tt → Pair.K.Gather.selected g Pair.second ≡ just tt → ⊥
  tensor-no-cross = Pair.no-cross

  module Blocked = TensorPair (L.return tt) L.stop
  returned-blocked-no-completion : ∀ {c} → ¬ (Blocked.K._─[_]→_ Blocked.K.initial-configuration
    (Blocked.K.visible Blocked.K.√) c)
  returned-blocked-no-completion (Blocked.K.finish _ ready) with ready Blocked.second
  ... | ()

  returned-blocked-native-no-completion : ∀ {t} → ¬ (G._─[_]→_ (Blocked.native Blocked.W.initial-state)
    (G.visible (G.√ tt)) t)
  returned-blocked-native-no-completion sp = returned-blocked-no-completion (proj₁ (Blocked.native-return-step sp))

  module Spinning = TensorPair (L.return tt) L.div
  spinning-path : ∀ q → q Spinning.second ≡ L.div → Spinning.K.Diverges (Spinning.K.running q)
  Spinning.K.Diverges.next (spinning-path q eq) = Spinning.K.running (Spinning.K.update Spinning.second L.div q)
  Spinning.K.Diverges.step (spinning-path q eq) = Spinning.K.internal {k = Spinning.second}
    (L.sSil (cong L.Tree.force eq))
  Spinning.K.Diverges.rest (spinning-path q eq) = spinning-path (Spinning.K.update Spinning.second L.div q) refl

  returned-spinning-native-divergence : G.Diverges (Spinning.native Spinning.W.initial-state)
  returned-spinning-native-divergence = Spinning.network-divergence (Spinning.live Spinning.W.initial-state)
    (spinning-path Spinning.W.initial-state refl)

-- Instantiations make the public generic witnesses part of the checked closure.
module PrivateUnit = Private ⊤ ⊤ tt
module ExteriorUnit = Exterior ⊤ ⊤ tt

module Plugged (X B : Set) (x : X) where
  module P = Plugging X B
  module L = P.L
  offer : L.Tree
  offer = L.menu (λ _ → just (L.return tt)) (λ _ → nothing)
  module Four = P.Four offer offer offer offer
  module First = Four.Pair₁ {x = x} (L.sVis refl refl) (L.sVis refl refl)
  module Second = Four.Pair₂ {x = x} (L.sVis refl refl) (L.sVis refl refl)

  actual-plugging-left₁ = First.kernel-left
  actual-plugging-right₁ = First.kernel-right
  actual-native-left₁ = First.native-left
  actual-native-right₁ = First.native-right
  actual-continuation₁ = First.continuation
  actual-plugging-left₂ = Second.kernel-left
  actual-plugging-right₂ = Second.kernel-right
  actual-native-left₂ = Second.native-left
  actual-native-right₂ = Second.native-right
  actual-continuation₂ = Second.continuation

module PluggedUnit = Plugged ⊤ ⊤ tt

module Commitment where
  module N = Interchange ⊤ ⊤
  open N.L
  open Tree

  offer : Tree
  offer = menu (λ _ → just (return tt)) (λ _ → nothing)

  choice : Tree
  choice = ptree (react (λ _ → nothing) (N.I.par-choice offer offer (return tt) (return tt)))

  outside-overlap-visible : N.I.Par offer offer ─[ visible (event (false , tt)) ]→ choice
  outside-overlap-visible = sVis refl refl

  post-event-left-commitment : choice ─[ τ ]→ N.I.Par (return tt) offer
  post-event-left-commitment = sTau {i = N.I.commitment false} refl refl

  post-event-right-commitment : choice ─[ τ ]→ N.I.Par offer (return tt)
  post-event-right-commitment = sTau {i = N.I.commitment true} refl refl

{-# OPTIONS --safe --guardedness #-}

-- Existence of an infinite silent-labelled command schedule, not autonomous
-- Machine divergence and not a fairness or all-schedules assertion.
module CategoricalCrypto.CSP.BinaryDivergence (X B : Set) where

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base

import CategoricalCrypto.Channel.Core as C
import CategoricalCrypto.CSP.BinaryOperational as Operational
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Relational as R

module O = Operational X B
module S = O.S

module Divergence (p₀ q₀ : O.N.P.Tree) where
  open O.Connection p₀ q₀
  module T = R._≈ᴿ_ native-composition-correct

  response : Bool → Maybe (C.Channel.outType (S.scheduler M.⊗ᵀ S.result))
  response true = S.output (just (inj₁ S.τ))
  response false = S.output (just (inj₂ S.τ))

  record ScheduledDiverges (p : E.Configuration) : Set where
    coinductive
    field next : E.Configuration
          command : C.Channel.inType (S.scheduler M.⊗ᵀ S.result)
          side : Bool
          step : Step p command (response side) next
          rest : ScheduledDiverges next

  record CompiledDiverges (s : S.LocalState × S.LocalState) : Set where
    coinductive
    field next : S.LocalState × S.LocalState
          command : C.Channel.inType (S.scheduler M.⊗ᵀ S.result)
          side : Bool
          step : M.Machine.stepRel S.compiled s command (response side) next
          rest : CompiledDiverges next

  choose-silent-command : ∀ {p q} → E._─[_]→_ p E.τ q
    → ∃ λ i → ∃ λ side → Step p i (response side) q
  choose-silent-command (E.internal {k = inj₁ tt} move) = _ , true , left move
  choose-silent-command (E.internal {k = inj₂ tt} move) = _ , false , right move
  choose-silent-command (E.hidden {n = inj₁ tt} x g confined supported) = _ , false , exchange g
  choose-silent-command (E.hidden {n = inj₂ (inj₁ ())} x g confined supported)
  choose-silent-command (E.hidden {n = inj₂ (inj₂ ())} x g confined supported)

  schedule-divergence : ∀ {p} → E.Diverges p → ScheduledDiverges p
  ScheduledDiverges.next (schedule-divergence d) = E.Diverges.next d
  ScheduledDiverges.command (schedule-divergence d) = proj₁ (choose-silent-command (E.Diverges.step d))
  ScheduledDiverges.side (schedule-divergence d) = proj₁ (proj₂ (choose-silent-command (E.Diverges.step d)))
  ScheduledDiverges.step (schedule-divergence d) = proj₂ (proj₂ (choose-silent-command (E.Diverges.step d)))
  ScheduledDiverges.rest (schedule-divergence d) = schedule-divergence (E.Diverges.rest d)

  compile-divergence : ∀ {p s} → T.Related p s → ScheduledDiverges p → CompiledDiverges s
  CompiledDiverges.next (compile-divergence related d) = proj₁ (T.step-to related (ScheduledDiverges.step d))
  CompiledDiverges.command (compile-divergence related d) = ScheduledDiverges.command d
  CompiledDiverges.side (compile-divergence related d) = ScheduledDiverges.side d
  CompiledDiverges.step (compile-divergence related d) = proj₁ (proj₂ (T.step-to related (ScheduledDiverges.step d)))
  CompiledDiverges.rest (compile-divergence related d) = compile-divergence
    (proj₂ (proj₂ (T.step-to related (ScheduledDiverges.step d)))) (ScheduledDiverges.rest d)

  uncompile-divergence : ∀ {p s} → T.Related p s → CompiledDiverges s → ScheduledDiverges p
  ScheduledDiverges.next (uncompile-divergence related d) = proj₁ (T.step-from related (CompiledDiverges.step d))
  ScheduledDiverges.command (uncompile-divergence related d) = CompiledDiverges.command d
  ScheduledDiverges.side (uncompile-divergence related d) = CompiledDiverges.side d
  ScheduledDiverges.step (uncompile-divergence related d) = proj₁ (proj₂ (T.step-from related (CompiledDiverges.step d)))
  ScheduledDiverges.rest (uncompile-divergence related d) = uncompile-divergence
    (proj₂ (proj₂ (T.step-from related (CompiledDiverges.step d)))) (CompiledDiverges.rest d)

  opaque
    unfolding C._⊗₀_ C.construct-⊗

    reflect-silent : ∀ {p i side q} → Step p i (response side) q → E._─[_]→_ p E.τ q
    reflect-silent {side = true} (left move) = E.internal move
    reflect-silent {side = false} (right move) = E.internal move
    reflect-silent {side = false} (exchange g) = E.hidden _ g (λ { (inj₁ ()) ; (inj₂ ()) }) (handshake g)

    unschedule-divergence : ∀ {p} → ScheduledDiverges p → E.Diverges p
    E.Diverges.next (unschedule-divergence d) = ScheduledDiverges.next d
    E.Diverges.step (unschedule-divergence d) = reflect-silent {side = ScheduledDiverges.side d} (ScheduledDiverges.step d)
    E.Diverges.rest (unschedule-divergence d) = unschedule-divergence (ScheduledDiverges.rest d)

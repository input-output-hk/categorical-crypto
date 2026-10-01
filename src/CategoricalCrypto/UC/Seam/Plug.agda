{-# OPTIONS --safe --without-K --guardedness #-}

-- What a closed composite observes at the verdict interface's tick: one pass
-- of the traced loop, then the loop.
--
-- `Machines.Collapse` presents a closed composite as ONE traced machine whose
-- step `kᴳ` dispatches each letter to the factor that owns it.  Nothing here
-- looks at either factor, so the loop is stated at an arbitrary state and step.

open import Categories.Category

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.UC.Seam.Plug where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module Sm = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The tick that enters a closed loop (`Machines.Collapse.Loop`)

module Tick (X : Set) (S : MC.State)
            (k : MC.obj S × ((⊥ ⊎ ⊤) ⊎ X) → Dₚ (MC.obj S × ((⊥ ⊎ Bool) ⊎ X)))
            where

  open Col.Loop (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X S k public

  verdict : MC.obj S × (⊥ ⊎ Bool) → Dₚ Bool
  verdict (_ , inj₁ e) = ⊥-elim e
  verdict (_ , inj₂ v) = returnₚ v

  cont : MC.obj S × ((⊥ ⊎ Bool) ⊎ X) → Dₚ Bool
  cont (st , inj₁ o) = verdict (st , o)
  cont (st , inj₂ x) = iterₚ body (st , x) >>=ₚ verdict

  private
    resume-red : (p : MC.obj S × (⊥ ⊎ Bool))
               → resumeᴹ tracedᴹ (λ _ r → returnₚ r) p ≈ₚ verdict p
    resume-red (_ , inj₁ e) = ⊥-elim e
    resume-red (_ , inj₂ _) = ≈refl

  cont-red : (r : MC.obj S × ((⊥ ⊎ Bool) ⊎ X)) → (contᵢ body r >>=ₚ verdict) ≈ₚ cont r
  cont-red (st , inj₁ o) = >>=ₚ-identityˡ (st , o) verdict
  cont-red (_  , inj₂ _) = ≈refl

  tick-run : (st : MC.obj S)
           → runᴹFrom tracedᴹ st (ask tt out) ≈ₚ (k (st , inj₁ (inj₂ tt)) >>=ₚ cont)
  tick-run st =
      bindᶠ resume-red
    ⟨≈⟩ bindˣ (step-red st (inj₂ tt))
    ⟨≈⟩ >>=ₚ-assoc (k (st , inj₁ (inj₂ tt))) (contᵢ body) verdict
    ⟨≈⟩ bindᶠ cont-red

  observe : ⟦ tracedᴹ ⟧ᴼ ≈ₚ (MC.point S ttᵛ >>=ₚ λ st → k (st , inj₁ (inj₂ tt)) >>=ₚ cont)
  observe = bindᶠ tick-run

------------------------------------------------------------------------
-- …at a closed composite

-- Every interface is EXPLICIT (see `UC.Machine.𝒫ᴵ`).
module Plugged (B : Iface) (K : Proc B Ωᴵ) (u : Proc unitᴵ B) where

  Sᴷ : MC.State
  Sᴷ = Col.Sᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  kᴷ : MC.obj Sᴷ × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B))
     → Dₚ (MC.obj Sᴷ × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᴷ = Col.kᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  open Tick (Neg B ⊎ Pos B) Sᴷ kᴷ public

  -- The paired state's point is the two factors', in order; the junction is
  -- the one `λ⇐` spends.
  point-red : MC.point Sᴷ ttᵛ
            ≈ₚ (MC.point (MC.state K) ttᵛ >>=ₚ λ sk →
                MC.point (MC.state u) ttᵛ >>=ₚ λ su → returnₚ (sk , su))
  point-red = >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

  -- The composite `𝒫ᴵ` names and the collapsed trace this module is about are
  -- the same machine; the projection out of the G-construction record is paid
  -- once, here (`Machines.Collapse`'s header).
  collapse : ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ ⟦ tracedᴹ ⟧ᴼ
  collapse = runᴹ-resp-≈ᴹ {Ωᴵ}
    (Sm.⟺ᴹ (Col.compose-raw≈∘ᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u)
     Sm.○ᴹ Col.collapseᵀ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u)
    (ask tt out)

-- A composite is observed through a representative of its context factor,
-- which is what a `QB` certificate is carried on (`UC.QueryBound`'s `QB` is
-- the `≈`-closure of `Certified`).
obs-resp : (B : Iface) (u : Proc unitᴵ B) (N K : Proc B Ωᴵ) → N Sm.≈ᴹ K
         → ⟦ N 𝒫.∘ u ⟧ᴼ ≈ₚ ⟦ K 𝒫.∘ u ⟧ᴼ
obs-resp B u N K e =
  runᴹ-resp-≈ᴹ {Ωᴵ} (𝒫.∘-resp-≈ˡ {unitᴵ} {B} {Ωᴵ} {N} {K} {u} e) (ask tt out)

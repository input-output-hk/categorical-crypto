{-# OPTIONS --safe --without-K --guardedness #-}

-- What a closed composite observes at the verdict interface's tick: one pass
-- of the traced loop, then the loop.
--
-- A closed process plugged into a context is a `𝒢ₚ`-composite at `unitᴵ`/`Ωᴵ`,
-- which `Machines.Collapse` presents as ONE traced machine whose step `kᴳ`
-- dispatches each letter to the factor that owns it.  Observing it is layer
-- 1's `runᴹ` at the one-ask strategy, and `observe` below reduces that to the
-- loop: the tick enters `kᴳ` on the external summand, and whatever comes back
-- either leaves with the verdict or re-enters `iterₚ`.
--
-- Nothing here looks at either factor, so it is stated at an arbitrary state
-- and step: `UC.Seam.Adequacy` runs its strategy induction on top of the same
-- reduction, and the only part of that module which is about a strategy is
-- what happens AFTER `cont`.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine using (runᴹFrom; resumeᴹ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; ⟦_⟧ᴼ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Collapse.Congruence as ColCong
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
-- The tick, at an arbitrary traced loop

module Tick (X : Set) (S : MC.State)
            (k : MC.obj S × ((⊥ ⊎ ⊤) ⊎ X) → Dₚ (MC.obj S × ((⊥ ⊎ Bool) ⊎ X)))
            where

  tracedᴹ : Proc unitᴵ Ωᴵ
  tracedᴹ = MT.traceᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X (MC.mk S k)

  -- One pass of the loop: `k` entered on the loop summand.
  body : Body (MC.obj S) X (⊥ ⊎ Bool)
  body p = k (proj₁ p , inj₂ (proj₂ p))

  verdict : MC.obj S × (⊥ ⊎ Bool) → Dₚ Bool
  verdict (_ , inj₁ e) = ⊥-elim e
  verdict (_ , inj₂ v) = returnₚ v

  -- What a pass's output means: leave with the verdict, or keep solving.
  cont : MC.obj S × ((⊥ ⊎ Bool) ⊎ X) → Dₚ Bool
  cont (st , inj₁ o) = verdict (st , o)
  cont (st , inj₂ x) = iterₚ body (st , x) >>=ₚ verdict

  private
    solveᵗ : MC.obj S × ((⊥ ⊎ Bool) ⊎ X) → Dₚ (MC.obj S × (⊥ ⊎ Bool))
    solveᵗ = MT.solve S (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X k

    bodyᵗ : Body (MC.obj S) X (⊥ ⊎ Bool)
    bodyᵗ = MT.loopBody S (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X k

    -- The junctions the Kleisli tensor spends on a pure relabelling.
    loop-red : (p : MC.obj S × X) → bodyᵗ p ≈ₚ body p
    loop-red (st , x) = bindˣ (>>=ₚ-identityˡ st _)
                  ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₂ x) _)
                  ⟨≈⟩ >>=ₚ-identityˡ (st , inj₂ x) k

    resume-red : (p : MC.obj S × (⊥ ⊎ Bool))
               → resumeᴹ tracedᴹ (λ _ r → returnₚ r) p ≈ₚ verdict p
    resume-red (_ , inj₁ e) = ⊥-elim e
    resume-red (_ , inj₂ _) = ≈refl

    -- The distributor's case split IS the loop's continuation.
    solve-red : (r : MC.obj S × ((⊥ ⊎ Bool) ⊎ X)) → solveᵗ r ≈ₚ contᵢ bodyᵗ r
    solve-red (st , inj₁ o) = >>=ₚ-identityˡ (inj₁ (st , o)) _
    solve-red (st , inj₂ x) = >>=ₚ-identityˡ (inj₂ (st , x)) _

    solve-cont : (r : MC.obj S × ((⊥ ⊎ Bool) ⊎ X)) → (solveᵗ r >>=ₚ verdict) ≈ₚ cont r
    solve-cont (st , inj₁ o) = bindˣ (solve-red (st , inj₁ o))
                         ⟨≈⟩ >>=ₚ-identityˡ (st , o) verdict
    solve-cont (st , inj₂ x) =
      bindˣ (solve-red (st , inj₂ x) ⟨≈⟩ iterₚ-cong bodyᵗ body loop-red (st , x))

    trace-red : (st : MC.obj S) (y : ⊥ ⊎ ⊤)
              → MT.traceStep S (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X k (st , y)
                ≈ₚ (k (st , inj₁ y) >>=ₚ solveᵗ)
    trace-red st y = bindˣ (bindˣ (>>=ₚ-identityˡ st _)
                       ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₁ y) _)
                       ⟨≈⟩ >>=ₚ-identityˡ (st , inj₁ y) k)

  -- `contᵢ` of the loop's own body, read as `cont`: what the induction of a
  -- consumer that unrolls the loop resumes into.
  cont-red : (r : MC.obj S × ((⊥ ⊎ Bool) ⊎ X)) → (contᵢ body r >>=ₚ verdict) ≈ₚ cont r
  cont-red (st , inj₁ o) = >>=ₚ-identityˡ (st , o) verdict
  cont-red (_  , inj₂ _) = ≈refl

  -- The composite's single activation is the tick, and it runs one pass.
  tick-run : (st : MC.obj S)
           → runᴹFrom tracedᴹ st (ask tt out) ≈ₚ (k (st , inj₁ (inj₂ tt)) >>=ₚ cont)
  tick-run st =
      bindᶠ resume-red
    ⟨≈⟩ bindˣ (trace-red st (inj₂ tt))
    ⟨≈⟩ >>=ₚ-assoc (k (st , inj₁ (inj₂ tt))) solveᵗ verdict
    ⟨≈⟩ bindᶠ solve-cont

  observe : ⟦ tracedᴹ ⟧ᴼ ≈ₚ (MC.point S ttᵛ >>=ₚ λ st → k (st , inj₁ (inj₂ tt)) >>=ₚ cont)
  observe = bindᶠ tick-run

------------------------------------------------------------------------
-- …at a closed composite

-- `Machines.Collapse`'s `kᴳ` at this shape: the tick and the plugged
-- interface's two polarities, with the empty external summand left to
-- `⊥-elim` at the use site.
-- Every interface is EXPLICIT: left implicit, a `Proc` argument makes Agda
-- invert `Machine (Pos A + Neg B) …` for the pair (`UC.Machine`'s header).
module Plugged (B : Iface) (K : Proc B Ωᴵ) (u : Proc unitᴵ B) where

  Sᴷ : MC.State
  Sᴷ = Col.Sᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  kᴷ : MC.obj Sᴷ × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B))
     → Dₚ (MC.obj Sᴷ × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᴷ = Col.kᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  open Tick (Neg B ⊎ Pos B) Sᴷ kᴷ public

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
-- the `≈`-closure of `Certified`).  Going through the raw trace keeps the
-- G-construction's congruence out of it.
obs-resp : (B : Iface) (u : Proc unitᴵ B) (N K : Proc B Ωᴵ) → N Sm.≈ᴹ K
         → ⟦ N 𝒫.∘ u ⟧ᴼ ≈ₚ ⟦ K 𝒫.∘ u ⟧ᴼ
obs-resp B u N K e = runᴹ-resp-≈ᴹ {Ωᴵ}
  (Sm.⟺ᴹ (Col.compose-raw≈∘ᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} N u)
   Sm.○ᴹ ColCong.compose-resp-≈ᴹ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} e Sm.reflᴹ
   Sm.○ᴹ Col.compose-raw≈∘ᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u)
  (ask tt out)

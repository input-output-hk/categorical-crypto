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
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Machines.Run.Sim
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.UC.Machine.Plug where

private
  module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The tick that enters a closed loop (`Machines.Pointwise.Loop`)

module Tick (X : Set) (S : MC.State)
            (k : MC.obj S × ((⊥ ⊎ ⊤) ⊎ X) → Dₚ (MC.obj S × ((⊥ ⊎ Bool) ⊎ X)))
            where

  open Pw.Loop (⊥ ⊎ ⊤) (⊥ ⊎ Bool) X S k public

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

-- Where the context's and the process's emissions go: a query re-enters the
-- loop, a verdict leaves (`Machines.Collapse`'s `outᵍ`/`outᶠ`, case-split so
-- that the loop reduces).
module _ (B : Iface) where

  outE : Neg B ⊎ Bool → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outE (inj₁ n) = inj₂ (inj₁ n)
  outE (inj₂ v) = inj₁ (inj₂ v)

  outU : ⊥ ⊎ Pos B → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outU (inj₁ e) = ⊥-elim e
  outU (inj₂ p) = inj₂ (inj₂ p)

-- Every interface is EXPLICIT (see `UC.Machine.𝒫ᴵ`).
module Plugged (B : Iface) (K : Proc B Ωᴵ) (u : Proc unitᴵ B) where

  Sᴷ : MC.State
  Sᴷ = Col.Sᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  kᴷ : MC.obj Sᴷ × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B))
     → Dₚ (MC.obj Sᴷ × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᴷ = Col.kᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u

  open Tick (Neg B ⊎ Pos B) Sᴷ kᴷ public

  -- `kᴷ` case-split so that the loop reduces, with the two maps out of
  -- `Pos unitᴵ = ⊥` written as such.
  kᶜ : MC.obj Sᴷ × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B)) → Dₚ (MC.obj Sᴷ × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᶜ ((sk , su) , inj₁ (inj₁ ()))
  kᶜ ((sk , su) , inj₁ (inj₂ _)) =
    MC.step K (sk , inj₂ tt) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))
  kᶜ ((sk , su) , inj₂ (inj₁ n)) =
    MC.step u (su , inj₂ n) >>=ₚ λ q → returnₚ ((sk , proj₁ q) , outU B (proj₂ q))
  kᶜ ((sk , su) , inj₂ (inj₂ p)) =
    MC.step K (sk , inj₁ p) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))

  k-red : (z : _) → kᴷ z ≈ₚ kᶜ z
  k-red ((sk , su) , inj₁ (inj₁ ()))
  k-red ((sk , su) , inj₁ (inj₂ _)) = bindᶠ λ where
    (_ , inj₁ _) → ≈refl
    (_ , inj₂ _) → ≈refl
  k-red ((sk , su) , inj₂ (inj₁ n)) = bindᶠ λ where
    (_ , inj₁ ())
    (_ , inj₂ _) → ≈refl
  k-red ((sk , su) , inj₂ (inj₂ p)) = bindᶠ λ where
    (_ , inj₁ _) → ≈refl
    (_ , inj₂ _) → ≈refl

  -- Stated at the collapsed representative rather than at `K 𝒫.∘ u`: the
  -- conversion back from the G-category's `_∘_` projection dominates otherwise.
  traced≈ : tracedᴹ MS.≈ᴹ MT.traceᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) (Neg B ⊎ Pos B) (MC.mk Sᴷ kᶜ)
  traced≈ = MS.≲⇒≈ᴹ (Col.TC.trace-resp-≲ (MS.mk-cong k-red))

  -- The composite `𝒫ᴵ` names and the collapsed trace this module is about are
  -- the same machine; the projection out of the G-construction record is paid
  -- once, here (`Machines.Collapse`'s header).
  collapse : ⟦ K 𝒫.∘ u ⟧ᴼ ≈ₚ ⟦ tracedᴹ ⟧ᴼ
  collapse = runᴹ-resp-≈ᴹ {Ωᴵ}
    (MS.⟺ᴹ (Col.compose-raw≈∘ᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u)
     MS.○ᴹ Col.collapseᵀ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} K u)
    (ask tt out)

-- A composite is observed through a representative of its context factor,
-- which is what a `QB` certificate is carried on (`UC.QueryBound`'s `QB` is
-- the `≈`-closure of `Certified`).
obs-resp-ctx : (B : Iface) (u : Proc unitᴵ B) (N K : Proc B Ωᴵ) → N MS.≈ᴹ K
         → ⟦ N 𝒫.∘ u ⟧ᴼ ≈ₚ ⟦ K 𝒫.∘ u ⟧ᴼ
obs-resp-ctx B u N K e =
  runᴹ-resp-≈ᴹ {Ωᴵ} (𝒫.∘-resp-≈ˡ {unitᴵ} {B} {Ωᴵ} {N} {K} {u} e) (ask tt out)

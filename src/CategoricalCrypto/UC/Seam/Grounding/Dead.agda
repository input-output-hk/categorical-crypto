{-# OPTIONS --safe --without-K --guardedness #-}

-- Processes that never start, and what they do to a context.
--
-- A machine's initial state is a Kleisli point (`Machines.Core`'s header: "a
-- possibly-effectful initial state"), so `botₚ` is one.  `Dead` is that fact up
-- to the machine equality, which is what makes it transportable along
-- `Machines.Collapse`'s two readings of a `𝒢`-composite; deadness then
-- propagates through composition and through the grading action, because both
-- keep the acted-on process's state.
--
-- Every object argument is EXPLICIT, for the reason `UC.QueryBound`'s header
-- gives: left implicit, a hom of `𝒢ₚ` makes Agda invert
-- `Machine (A⁺ + B⁻) (A⁻ + B⁺)` for the pair at every use site.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational.Properties using (<⇒≤)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0]; ≈ₚ[]-mono)
open import ProbabilisticLogic.Dp.Zero

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒫ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ; runᴹ)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine using (Proc; T₁ᴵ; retᴵ; subᴵ′; ucBaseᴹ)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; sub-⊗₁)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounding.Dead where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝔾  = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E  = Em ucBaseᴹ

open E using (_⊛_; _≈ℰ_; T₁; Test; Closure; obs; tv₁)

------------------------------------------------------------------------
-- Divergent initialization

private
  ⊥ˢ : MC.State
  ⊥ˢ = record { obj = MC.obj MC.Iˢ ; point = λ _ → botₚ ; discard = λ _ → returnₚ ttᵛ }

-- The step is unreachable from the point, so any total one will do.
deadᴹ : (A B : 𝔾.Obj) → 𝒢ₚ 0ℓ [ A , B ]
deadᴹ A B = MC.mk ⊥ˢ λ _ → botₚ

Dead : (A B : 𝔾.Obj) → 𝒢ₚ 0ℓ [ A , B ] → Set₁
Dead A B f = Σ[ g ∈ 𝒢ₚ 0ℓ [ A , B ] ] (g S.≈ᴹ f) × Zero (MC.point (MC.state g) ttᵛ)

dead-deadᴹ : (A B : 𝔾.Obj) → Dead A B (deadᴹ A B)
dead-deadᴹ A B = deadᴹ A B , S.reflᴹ , zero-botₚ

------------------------------------------------------------------------
-- Propagation

private
  point-⊛ : (S T : MC.State) → MC.point (S MC.⊛ T) ttᵛ
          ≈ₚ (MC.point S ttᵛ >>=ₚ λ x → MC.point T ttᵛ >>=ₚ λ y → returnₚ (x , y))
  point-⊛ S T = >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

  zero-⊛ˡ : (S T : MC.State) → Zero (MC.point S ttᵛ) → Zero (MC.point (S MC.⊛ T) ttᵛ)
  zero-⊛ˡ S T z = zero-resp-≈ₚ (≈ₚ-sym _ _ (point-⊛ S T)) (zero-bindˡ _ z)

  zero-⊛ʳ : (S T : MC.State) → Zero (MC.point T ttᵛ) → Zero (MC.point (S MC.⊛ T) ttᵛ)
  zero-⊛ʳ S T z = zero-resp-≈ₚ (≈ₚ-sym _ _ (point-⊛ S T))
                               (bind-zero (MC.point S ttᵛ) λ _ → zero-bindˡ _ z)

-- A `𝒢`-composite's state is the pair of the factors' states, so a dead factor
-- kills it from either side.
dead-∘ˡ : (A B C : 𝔾.Obj) (g : 𝒢ₚ 0ℓ [ B , C ]) (f : 𝒢ₚ 0ℓ [ A , B ])
        → Dead B C g → Dead A C (𝔾._∘_ {A} {B} {C} g f)
dead-∘ˡ A B C g f (g′ , e , z) =
    Col.MT.traceᴹ (proj₁ A ⊎ proj₂ C) (proj₂ A ⊎ proj₁ C) (proj₂ B ⊎ proj₁ B)
      (Col.MC.mk (Col.Sᴳ g′ f) (Col.kᴳ g′ f))
  , (S.⟺ᴹ (Col.collapseᵀ g′ f) S.○ᴹ Col.compose-raw≈∘ᴳ g′ f) S.○ᴹ 𝔾.∘-resp-≈ˡ e
  , zero-⊛ˡ (MC.state g′) (MC.state f) z

dead-∘ʳ : (A B C : 𝔾.Obj) (g : 𝒢ₚ 0ℓ [ B , C ]) (f : 𝒢ₚ 0ℓ [ A , B ])
        → Dead A B f → Dead A C (𝔾._∘_ {A} {B} {C} g f)
dead-∘ʳ A B C g f (f′ , e , z) =
    Col.MT.traceᴹ (proj₁ A ⊎ proj₂ C) (proj₂ A ⊎ proj₁ C) (proj₂ B ⊎ proj₁ B)
      (Col.MC.mk (Col.Sᴳ g f′) (Col.kᴳ g f′))
  , (S.⟺ᴹ (Col.collapseᵀ g f′) S.○ᴹ Col.compose-raw≈∘ᴳ g f′) S.○ᴹ 𝔾.∘-resp-≈ʳ e
  , zero-⊛ʳ (MC.state g) (MC.state f′) z

-- The grading action keeps the acted-on process's state (`T₁ᴵ`, `subᴵ`), and
-- `UC.Machine.Dictionary` is the bridge to the monoidal spelling of it.
dead-T₁ : (Y A B : 𝔾.Obj) (f : 𝒢ₚ 0ℓ [ A , B ]) → Dead A B f
        → Dead (Y ⊛ A) (Y ⊛ B) (T₁ Y f)
dead-T₁ Y A B f (g , e , z) =
    T₁ᴵ (retᴵ Y) g
  , (T₁-⊗₁ {retᴵ Y} {retᴵ A} {retᴵ B} g S.○ᴹ E.T₁-resp-≈ {Y} {A} {B} {g} {f} e)
  , z

dead-sub : (X Y A : 𝔾.Obj) (s : 𝒢ₚ 0ℓ [ X , Y ]) → Dead X Y s
         → Dead (X ⊛ A) (Y ⊛ A) (E.sub {X} {Y} {A} s)
dead-sub X Y A s (g , e , z) =
    subᴵ′ {retᴵ X} {retᴵ Y} {retᴵ A} g
  , (sub-⊗₁ {retᴵ X} {retᴵ Y} {retᴵ A} g S.○ᴹ E.sub-resp-≈ {X} {Y} {A} {g} {s} e)
  , z

dead-run : (B : Iface) (f : Proc unitᴵ B) → Dead ⟦ unitᴵ ⟧ᴵ ⟦ B ⟧ᴵ f
         → (d : Strat (Neg B) (Pos B)) → Zero (runᴹ f d)
dead-run B f (g , e , z) d = zero-resp-≈ₚ (runᴹ-resp-≈ᴹ e d) (zero-bindˡ _ z)

------------------------------------------------------------------------
-- What a context sees

-- Nothing: the divergence reaches the closed composite from wherever it sits.
dead-obs : (A B : 𝔾.Obj) (f : 𝒢ₚ 0ℓ [ A , B ]) → Dead A B f
         → (Y : 𝔾.Obj) (Et : Test (Y ⊛ B)) (m : Closure (Y ⊛ A))
         → Zero (obs (tv₁ Y f Et) m)
dead-obs A B f df Y Et m =
  dead-run (retᴵ E.Ω) (𝔾._∘_ {E.𝟙} {Y ⊛ A} {E.Ω} (𝔾._∘_ {Y ⊛ A} {Y ⊛ B} {E.Ω} Et
                        (T₁ Y f)) m)
           (dead-∘ˡ E.𝟙 (Y ⊛ A) E.Ω (𝔾._∘_ {Y ⊛ A} {Y ⊛ B} {E.Ω} Et (T₁ Y f)) m
             (dead-∘ʳ (Y ⊛ A) (Y ⊛ B) E.Ω Et (T₁ Y f)
               (dead-T₁ Y A B f df)))
           (ask tt out)

dead-≈ℰ : (A B : 𝔾.Obj) (f g : 𝒢ₚ 0ℓ [ A , B ])
        → Dead A B f → Dead A B g → _≈ℰ_ {A} {B} f g
dead-≈ℰ A B f g df dg Y Et m ε ε>0 = ≈ₚ[]-mono (<⇒≤ ε>0) (≈ₚ⇒≈ₚ[0]
  (≈ₚ-trans _ _ _ (zero⇒≈bot (dead-obs A B f df Y Et m))
                  (≈ₚ-sym _ _ (zero⇒≈bot (dead-obs A B g dg Y Et m)))))

{-# OPTIONS --safe --without-K --guardedness #-}

-- What a process's initialization does to every observation it takes part in.
--
-- A machine's initial state is a Kleisli point (`Machines.Core`'s header: "a
-- possibly-effectful initial state"), so its termination MASS is the one thing
-- the machine contributes to a run no matter where it sits: a `𝒢`-composite's
-- state is the pair of the factors' states and the grading action keeps the
-- acted-on process's, so either factor's point bounds the whole
-- (`massed-obs`).  `Massed` is that bound up to the machine equality, which is
-- what makes it transportable along `Machines.Collapse`'s two readings of a
-- `𝒢`-composite.  `Dead` is its mass-0 end.
--
-- Every object argument is EXPLICIT, for the reason `UC.QueryBound`'s header
-- gives: left implicit, a hom of `𝒢ₚ` makes Agda invert
-- `Machine (A⁺ + B⁻) (A⁻ + B⁺)` for the pair at every use site.  With the
-- objects implicit this module does not come back inside 4m47 CPU.
--
-- What it is FOR, at both ends of the scale.  At mass 0 it REFUTES the
-- unguarded form of `SubBlind`: `_≤UC_` quantifies its simulator over a
-- divergent `s`, `massed-sub` makes `sub s ∘ (ι ∘ v)` observe nothing,
-- `dead-≈ℰ` makes it agree with every other such process, and `massed-run`
-- shows layer 1 still sees the difference.  At mass 1 it is the route to the
-- REPAIRED statement (`UC.Seam.Grounding.SubBlind`, whose hypothesis is
-- `SimTotal`): an observation of the simulated ideal is almost surely total
-- only if the simulator's own point is, and a point that is almost surely
-- total is invisible to an ε-closed comparison (`Dp.Mass.astotal-bind`).  The
-- second half of that route is not landed; the propagation it rests on is.
--
-- The last section re-spells the propagation AT THE SEAL, where the seam's
-- statements live.  Under the seal a hom exposes no machine, so the crossing
-- is `UC.Model.Seal`'s third discipline — `p = p` from inside the unfolding
-- block — and only the bound comes back out.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational.Properties using (<⇒≤)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ[]-mono)
open import ProbabilisticLogic.Dp.Mass

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒫ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ; runᴹ)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine
  using (Observationᴹ; Proc; T₁ᴵ; retᴵ; subᴵ′; Ωᴵ; ⊤ᵛ)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; sub-⊗₁)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Environment as Env

module CategoricalCrypto.UC.Seam.Grounding.Dead where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝔾  = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E  = Env (𝒢ₚᴹ 0ℓ) Observationᴹ

open E using (_⊗₀_; _⊗₁_; id; _≈ℰ_; Test; Closure; obs; tv₁)

------------------------------------------------------------------------
-- Lossy initialization

Massed : (A B : 𝔾.Obj) → 𝒢ₚ 0ℓ [ A , B ] → Dₚ ⊤ᵛ → Set₁
Massed A B f p =
  Σ[ g ∈ 𝒢ₚ 0ℓ [ A , B ] ] (g S.≈ᴹ f) × (MC.point (MC.state g) ttᵛ ≼ᵐ p)

-- The degenerate end: a process that never starts.
Dead : (A B : 𝔾.Obj) → 𝒢ₚ 0ℓ [ A , B ] → Set₁
Dead A B f = Massed A B f (botₚ {A = ⊤ᵛ})

private
  ⊥ˢ : MC.State
  ⊥ˢ = record { obj = MC.obj MC.Iˢ ; point = λ _ → botₚ ; discard = λ _ → returnₚ ttᵛ }

-- The step is unreachable from the point, so any total one will do.
deadᴹ : (A B : 𝔾.Obj) → 𝒢ₚ 0ℓ [ A , B ]
deadᴹ A B = MC.mk ⊥ˢ λ _ → botₚ

dead-deadᴹ : (A B : 𝔾.Obj) → Dead A B (deadᴹ A B)
dead-deadᴹ A B = deadᴹ A B , S.reflᴹ , ≼ᵐ-refl botₚ

------------------------------------------------------------------------
-- Propagation

private
  point-⊛ : (S T : MC.State) → MC.point (S MC.⊛ T) ttᵛ
          ≈ₚ (MC.point S ttᵛ >>=ₚ λ x → MC.point T ttᵛ >>=ₚ λ y → returnₚ (x , y))
  point-⊛ S T = >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

  ⊛-≼ᵐˡ : (S T : MC.State) → MC.point (S MC.⊛ T) ttᵛ ≼ᵐ MC.point S ttᵛ
  ⊛-≼ᵐˡ S T = ≼ᵐ-trans _ _ _ (≼ₚ⇒≼ᵐ _ _ (proj₁ (point-⊛ S T)))
                             (bind-≼ᵐ (MC.point S ttᵛ) _)

  ⊛-≼ᵐʳ : (S T : MC.State) → MC.point (S MC.⊛ T) ttᵛ ≼ᵐ MC.point T ttᵛ
  ⊛-≼ᵐʳ S T = ≼ᵐ-trans _ _ _ (≼ₚ⇒≼ᵐ _ _ (proj₁ (point-⊛ S T)))
                             (bindʳ-≼ᵐ (MC.point S ttᵛ) _ (MC.point T ttᵛ)
                                       λ x n → mass-bindˡ n (MC.point T ttᵛ) _)

-- A `𝒢`-composite's state is the pair of the factors' states, so either
-- factor's point bounds it.
massed-∘ˡ : (A B C : 𝔾.Obj) (g : 𝒢ₚ 0ℓ [ B , C ]) (f : 𝒢ₚ 0ℓ [ A , B ]) (p : Dₚ ⊤ᵛ)
          → Massed B C g p → Massed A C (𝔾._∘_ {A} {B} {C} g f) p
massed-∘ˡ A B C g f p (g′ , e , le) =
    Col.MT.traceᴹ (proj₁ A ⊎ proj₂ C) (proj₂ A ⊎ proj₁ C) (proj₂ B ⊎ proj₁ B)
      (Col.MC.mk (Col.Sᴳ g′ f) (Col.kᴳ g′ f))
  , (S.⟺ᴹ (Col.collapseᵀ g′ f) S.○ᴹ Col.compose-raw≈∘ᴳ g′ f) S.○ᴹ 𝔾.∘-resp-≈ˡ e
  , ≼ᵐ-trans _ _ _ (⊛-≼ᵐˡ (MC.state g′) (MC.state f)) le

massed-∘ʳ : (A B C : 𝔾.Obj) (g : 𝒢ₚ 0ℓ [ B , C ]) (f : 𝒢ₚ 0ℓ [ A , B ]) (p : Dₚ ⊤ᵛ)
          → Massed A B f p → Massed A C (𝔾._∘_ {A} {B} {C} g f) p
massed-∘ʳ A B C g f p (f′ , e , le) =
    Col.MT.traceᴹ (proj₁ A ⊎ proj₂ C) (proj₂ A ⊎ proj₁ C) (proj₂ B ⊎ proj₁ B)
      (Col.MC.mk (Col.Sᴳ g f′) (Col.kᴳ g f′))
  , (S.⟺ᴹ (Col.collapseᵀ g f′) S.○ᴹ Col.compose-raw≈∘ᴳ g f′) S.○ᴹ 𝔾.∘-resp-≈ʳ e
  , ≼ᵐ-trans _ _ _ (⊛-≼ᵐʳ (MC.state g) (MC.state f′)) le

-- The pinned relays keep the acted-on process's state (`T₁ᴵ`, `subᴵ`), and
-- `UC.Machine.Dictionary` is the bridge to the monoidal spelling of them.
massed-T₁ : (Y A B : 𝔾.Obj) (f : 𝒢ₚ 0ℓ [ A , B ]) (p : Dₚ ⊤ᵛ) → Massed A B f p
          → Massed (Y ⊗₀ A) (Y ⊗₀ B) (id {Y} ⊗₁ f) p
massed-T₁ Y A B f p (g , e , le) =
    T₁ᴵ (retᴵ Y) g
  , (T₁-⊗₁ {retᴵ Y} {retᴵ A} {retᴵ B} g S.○ᴹ 𝔾.⊗.F-resp-≈ (𝔾.Equiv.refl , e))
  , le

massed-sub : (X Y A : 𝔾.Obj) (s : 𝒢ₚ 0ℓ [ X , Y ]) (p : Dₚ ⊤ᵛ) → Massed X Y s p
           → Massed (X ⊗₀ A) (Y ⊗₀ A) (s ⊗₁ id {A}) p
massed-sub X Y A s p (g , e , le) =
    subᴵ′ {retᴵ X} {retᴵ Y} {retᴵ A} g
  , (sub-⊗₁ {retᴵ X} {retᴵ Y} {retᴵ A} g S.○ᴹ 𝔾.⊗.F-resp-≈ (e , 𝔾.Equiv.refl))
  , le

massed-run : (B : Iface) (f : Proc unitᴵ B) (p : Dₚ ⊤ᵛ) → Massed ⟦ unitᴵ ⟧ᴵ ⟦ B ⟧ᴵ f p
           → (d : Strat (Neg B) (Pos B)) → runᴹ f d ≼ᵐ p
massed-run B f p (g , e , le) d =
  ≼ᵐ-trans _ _ _ (≼ₚ⇒≼ᵐ _ _ (proj₁ (runᴹ-resp-≈ᴹ (S.⟺ᴹ e) d)))
                 (≼ᵐ-trans _ _ _ (bind-≼ᵐ (MC.point (MC.state g) ttᵛ) _) le)

------------------------------------------------------------------------
-- What a context sees

-- At most the factor's own mass: the initialization reaches the closed
-- composite from wherever it sits.
massed-obs : (A B : 𝔾.Obj) (f : 𝒢ₚ 0ℓ [ A , B ]) (p : Dₚ ⊤ᵛ) → Massed A B f p
           → (Y : 𝔾.Obj) (Et : Test (Y ⊗₀ B)) (m : Closure (Y ⊗₀ A))
           → obs (tv₁ Y f Et) m ≼ᵐ p
massed-obs A B f p mf Y Et m =
  massed-run (retᴵ E.Ω) (𝔾._∘_ {E.𝟙} {Y ⊗₀ A} {E.Ω} (𝔾._∘_ {Y ⊗₀ A} {Y ⊗₀ B} {E.Ω} Et
                           (id ⊗₁ f)) m) p
             (massed-∘ˡ E.𝟙 (Y ⊗₀ A) E.Ω (𝔾._∘_ {Y ⊗₀ A} {Y ⊗₀ B} {E.Ω} Et (id ⊗₁ f)) m p
               (massed-∘ʳ (Y ⊗₀ A) (Y ⊗₀ B) E.Ω Et (id ⊗₁ f) p
                 (massed-T₁ Y A B f p mf)))
             (ask tt out)

-- Nothing at all, at the zero end — so two such processes are
-- indistinguishable while their runs still differ.
dead-≈ℰ : (A B : 𝔾.Obj) (f g : 𝒢ₚ 0ℓ [ A , B ])
          → Dead A B f → Dead A B g → _≈ℰ_ {A} {B} f g
dead-≈ℰ A B f g df dg Y Et m ε ε>0 = ≈ₚ[]-mono (<⇒≤ ε>0)
  (massless-≈ₚ[0] _ _ (≼ᵐbot⇒0 _ (massed-obs A B f _ df Y Et m))
                      (≼ᵐbot⇒0 _ (massed-obs A B g _ dg Y Et m)))

------------------------------------------------------------------------
-- The same, at the seal

-- Under the seal a hom exposes no machine, so the bound has to be carried
-- across from inside the unfolding block; `Dₚ ⊤ᵛ` and `_≼ᵐ_` mention nothing
-- sealed, which is what lets it out.
private module Gᵒ = MonoidalCategory 𝔾ᵒ

opaque
  unfolding 𝔾ᵒ ifaceᵒ

  Massedᵒ : (A B : Gᵒ.Obj) → Gᵒ._⇒_ A B → Dₚ ⊤ᵛ → Set₁
  Massedᵒ = Massed

  massedᵒ-resp-≈ : (A B : Gᵒ.Obj) (f g : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
                 → Gᵒ._≈_ f g → Massedᵒ A B f p → Massedᵒ A B g p
  massedᵒ-resp-≈ A B f g p e (h , e′ , le) = h , e′ S.○ᴹ e , le

  -- A hom's own initialization with its state forgotten: the one thing about a
  -- machine the seal lets out, and the bound every hom carries.
  pointᵒ : (A B : Gᵒ.Obj) → Gᵒ._⇒_ A B → Dₚ ⊤ᵛ
  pointᵒ A B f = mapₚ (λ _ → ttᵛ) (MC.point (MC.state f) ttᵛ)

  massedᵒ-point : (A B : Gᵒ.Obj) (f : Gᵒ._⇒_ A B) → Massedᵒ A B f (pointᵒ A B f)
  massedᵒ-point A B f = f , S.reflᴹ , mapₚ-≼ᵐ (MC.point (MC.state f) ttᵛ) _

  massedᵒ-∘ˡ : (A B C : Gᵒ.Obj) (g : Gᵒ._⇒_ B C) (f : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
             → Massedᵒ B C g p → Massedᵒ A C (Gᵒ._∘_ g f) p
  massedᵒ-∘ˡ = massed-∘ˡ

  massedᵒ-∘ʳ : (A B C : Gᵒ.Obj) (g : Gᵒ._⇒_ B C) (f : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
             → Massedᵒ A B f p → Massedᵒ A C (Gᵒ._∘_ g f) p
  massedᵒ-∘ʳ = massed-∘ʳ

  massedᵒ-T₁ : (Y A B : Gᵒ.Obj) (f : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ) → Massedᵒ A B f p
             → Massedᵒ (Gᵒ._⊗₀_ Y A) (Gᵒ._⊗₀_ Y B) (Gᵒ._⊗₁_ (Gᵒ.id {Y}) f) p
  massedᵒ-T₁ = massed-T₁

  massedᵒ-sub : (X Y A : Gᵒ.Obj) (s : Gᵒ._⇒_ X Y) (p : Dₚ ⊤ᵛ) → Massedᵒ X Y s p
              → Massedᵒ (Gᵒ._⊗₀_ X A) (Gᵒ._⊗₀_ Y A) (Gᵒ._⊗₁_ s (Gᵒ.id {A})) p
  massedᵒ-sub = massed-sub

  -- …and what the seam reads off it: a closed observation weighs no more than
  -- the initialization of anything it is built from.
  massedᵒ-obs : (u : Gᵒ._⇒_ 𝟘ᵒ Ωᵒ) (p : Dₚ ⊤ᵛ) → Massedᵒ 𝟘ᵒ Ωᵒ u p → Obs u ≼ᵐ p
  massedᵒ-obs u p mu = massed-run Ωᴵ u p mu (ask tt out)

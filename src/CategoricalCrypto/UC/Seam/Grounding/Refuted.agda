{-# OPTIONS --safe --without-K --guardedness #-}

-- Two of `UC.Seam.Grounding`'s statements are FALSE at the intended model.
--
-- A machine's initial state is a Kleisli point (`Machines.Core`'s header: "a
-- possibly-effectful initial state"), so `botₚ` is one, and a process whose
-- point diverges observes nothing in ANY context — the divergence is copied
-- into every composite's paired state.  Two consequences.
--
--   `UnitGrade`  is false at EVERY trivial grade.  Take the simulator to be
--                such a process: `sub s ∘ (ι ∘ v)` then observes nothing, so a
--                `u` that observes nothing emulates every `v`, while `Agreeˢ`
--                still compares the two runs.  `_≤UC_`'s simulator quantifier
--                admits a divergent simulator and nothing downstream excludes
--                it.
--   `SubBlind`   says every scalar `𝟘 ⇒ 𝟘` acts as the identity, and is false
--                for the same reason.  `no-trivial-grade` shows it is not
--                merely unproved: together with `IotaBlind` — a theorem at the
--                unit grade (`UC.Seam.Grounded.iotaBlind`) — it identifies all
--                closed processes.
--
-- A repair is therefore a restriction on the simulator, not a proof: `_≤UC_`'s
-- `Σ[ s ] …` has to be cut down to the non-degenerate `s` (a termination-mass
-- side condition on `point`, or a subcategory of machines with a pure point).
-- Both change a statement, so both are the maintainer's call.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (Bool; true)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
  using (+-identityˡ; <⇒≤; ≤-reflexive; ≤-trans; _<?_; _≤?_)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (Pr≤[_]; indᵇ-nn; ≈ₚ⇒≈ₚ[0]; ≈ₚ[]-mono)
open import ProbabilisticLogic.Dp.Zero

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒫ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ; runᴹ)
open import CategoricalCrypto.Strategy using (Strat; ask; out)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ; ⟦_⟧ᴼ; T₁ᴵ; retᴵ; subᴵ′; ucBaseᴹ)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; sub-⊗₁)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Seam using (Agreeˢ; ctxRunˢ)
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ; iotaBlind; stratIsEnv)
open import CategoricalCrypto.UC.Seam.Grounding using (module TrivialGrade)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounding.Refuted where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝔾  = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module E  = Em ucBaseᴹ

open E using (_∘_; _⊛_; _≈ℰ_; ≈ℰ-sym; ≈ℰ-trans; T₁; Test; Closure; obs; tv₁)

------------------------------------------------------------------------
-- Processes that never start

private
  ⊥ˢ : MC.State
  ⊥ˢ = record { obj = MC.obj MC.Iˢ ; point = λ _ → botₚ ; discard = λ _ → returnₚ ttᵛ }

-- Its step is unreachable from the point, so any total one will do.
deadᴹ : {A B : 𝔾.Obj} → 𝒢ₚ 0ℓ [ A , B ]
deadᴹ = MC.mk ⊥ˢ λ _ → botₚ

-- Divergence at the point, up to the machine equality — which is what makes it
-- transportable along `Machines.Collapse`'s two readings of a composite.
Dead : {A B : 𝔾.Obj} → 𝒢ₚ 0ℓ [ A , B ] → Set₁
Dead {A} {B} f =
  Σ[ g ∈ 𝒢ₚ 0ℓ [ A , B ] ] (g S.≈ᴹ f) × Zero (MC.point (MC.state g) ttᵛ)

dead-deadᴹ : {A B : 𝔾.Obj} → Dead (deadᴹ {A} {B})
dead-deadᴹ = deadᴹ , S.reflᴹ , zero-botₚ

private
  point-⊛ : (S T : MC.State) → MC.point (S MC.⊛ T) ttᵛ
          ≈ₚ (MC.point S ttᵛ >>=ₚ λ x → MC.point T ttᵛ >>=ₚ λ y → returnₚ (x , y))
  point-⊛ S T = >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

  zero-⊛ˡ : {S T : MC.State} → Zero (MC.point S ttᵛ) → Zero (MC.point (S MC.⊛ T) ttᵛ)
  zero-⊛ˡ {S} {T} z = zero-resp-≈ₚ (≈ₚ-sym _ _ (point-⊛ S T)) (zero-bindˡ _ z)

  zero-⊛ʳ : {S T : MC.State} → Zero (MC.point T ttᵛ) → Zero (MC.point (S MC.⊛ T) ttᵛ)
  zero-⊛ʳ {S} {T} z = zero-resp-≈ₚ (≈ₚ-sym _ _ (point-⊛ S T))
                                   (bind-zero (MC.point S ttᵛ) λ _ → zero-bindˡ _ z)

-- A `𝒢`-composite's state is the pair of the factors' states, so a dead factor
-- kills it from either side.
dead-∘ˡ : {A B C : 𝔾.Obj} {g : 𝒢ₚ 0ℓ [ B , C ]} (f : 𝒢ₚ 0ℓ [ A , B ])
        → Dead g → Dead (g ∘ f)
dead-∘ˡ f (g′ , e , z) =
  _ , (S.⟺ᴹ (Col.collapseᵀ g′ f) S.○ᴹ Col.compose-raw≈∘ᴳ g′ f) S.○ᴹ 𝔾.∘-resp-≈ˡ e
    , zero-⊛ˡ z

dead-∘ʳ : {A B C : 𝔾.Obj} (g : 𝒢ₚ 0ℓ [ B , C ]) {f : 𝒢ₚ 0ℓ [ A , B ]}
        → Dead f → Dead (g ∘ f)
dead-∘ʳ g (f′ , e , z) =
  _ , (S.⟺ᴹ (Col.collapseᵀ g f′) S.○ᴹ Col.compose-raw≈∘ᴳ g f′) S.○ᴹ 𝔾.∘-resp-≈ʳ e
    , zero-⊛ʳ z

-- The grading action keeps the acted-on process's state (`T₁ᴵ`, `subᴵ`), and
-- `UC.Machine.Dictionary` is the bridge to the monoidal spelling of it.
dead-T₁ : (Y : 𝔾.Obj) {A B : 𝔾.Obj} {f : 𝒢ₚ 0ℓ [ A , B ]} → Dead f → Dead (T₁ Y f)
dead-T₁ Y {A} {B} (g , e , z) =
  T₁ᴵ (retᴵ Y) g , (T₁-⊗₁ {retᴵ Y} {retᴵ A} {retᴵ B} g S.○ᴹ E.T₁-resp-≈ e) , z

dead-sub : {X Y A : 𝔾.Obj} {s : 𝒢ₚ 0ℓ [ X , Y ]} → Dead s → Dead (E.sub {A = A} s)
dead-sub {X} {Y} {A} (g , e , z) =
  subᴵ′ {retᴵ X} {retᴵ Y} {retᴵ A} g , (sub-⊗₁ g S.○ᴹ E.sub-resp-≈ e) , z

dead-run : {B : Iface} {f : Proc unitᴵ B} → Dead f
         → (d : Strat (Neg B) (Pos B)) → Zero (runᴹ f d)
dead-run (g , e , z) d = zero-resp-≈ₚ (runᴹ-resp-≈ᴹ e d) (zero-bindˡ _ z)

-- Hence a dead process is observationally dead in every ancilla context, and
-- any two dead processes agree.
dead-obs : {A B : 𝔾.Obj} {f : 𝒢ₚ 0ℓ [ A , B ]} → Dead f
         → (Y : 𝔾.Obj) (Et : Test (Y ⊛ B)) (m : Closure (Y ⊛ A))
         → Zero (obs (tv₁ Y f Et) m)
dead-obs df Y Et m =
  dead-run (dead-∘ˡ m (dead-∘ʳ Et (dead-T₁ Y df))) (ask tt out)

dead-≈ℰ : {A B : 𝔾.Obj} {f g : 𝒢ₚ 0ℓ [ A , B ]} → Dead f → Dead g → f ≈ℰ g
dead-≈ℰ df dg Y Et m ε ε>0 = ≈ₚ[]-mono (<⇒≤ ε>0) (≈ₚ⇒≈ₚ[0]
  (≈ₚ-trans _ _ _ (zero⇒≈bot (dead-obs df Y Et m))
                  (≈ₚ-sym _ _ (zero⇒≈bot (dead-obs dg Y Et m)))))

------------------------------------------------------------------------
-- A closed process that does observe something

private
  v₁ : Proc unitᴵ Ωᴵ
  v₁ = MC.mk MC.Iˢ λ _ → returnₚ (ttᵛ , inj₂ true)

  v₁-run : ⟦ v₁ ⟧ᴼ ≈ₚ returnₚ true
  v₁-run = ≈ₚ-trans _ _ _ (>>=ₚ-identityˡ ttᵛ _)
                          (>>=ₚ-identityˡ (ttᵛ , inj₂ true) _)

  v₁-mass : Σ[ m ∈ ℕ ] (1ℚ ℚ.≤ Pr≤[ true ] m ⟦ v₁ ⟧ᴼ)
  v₁-mass with proj₂ v₁-run (indᵇ true) (indᵇ-nn true) 1
  ... | m , bd = m , subst (ℚ._≤ Pr≤[ true ] m ⟦ v₁ ⟧ᴼ)
                           (returnₚ-cum 0 true (indᵇ true)) bd

  0<½ : 0ℚ ℚ.< ½
  0<½ = toWitness {Q = 0ℚ <? ½} _

  1≰½ : ¬ (1ℚ ℚ.≤ ½)
  1≰½ = toWitnessFalse {Q = 1ℚ ≤? ½} _

  deadᴼ : Proc unitᴵ Ωᴵ
  deadᴼ = deadᴹ

  -- Layer 1's own comparison separates a dead process from `v₁`: `Adequacy`
  -- turns both context runs into direct runs, and the direct run of a dead
  -- process carries no mass at all.
  no-agree : ¬ Agreeˢ Ωᴵ deadᴼ v₁
  no-agree ag
    with v₁-mass
  ... | m₀ , mass
    with proj₂ (adequacy Ωᴵ v₁ (ask tt out)) (indᵇ true) (indᵇ-nn true) m₀
  ... | n₁ , reach
    with proj₂ (ag (ask tt out) ½ 0<½) true n₁
  ... | k , bound =
    1≰½ (≤-trans mass (≤-trans reach (≤-trans bound (≤-reflexive
      (trans (cong (ℚ._+ ½) (zeroᵈ (indᵇ true) (indᵇ-nn true) k)) (+-identityˡ ½))))))
    where
    zeroᵈ : Zero (ctxRunˢ Ωᴵ (ask tt out) deadᴼ)
    zeroᵈ = zero-resp-≈ₚ (≈ₚ-sym _ _ (adequacy Ωᴵ deadᴼ (ask tt out)))
                         (dead-run dead-deadᴹ (ask tt out))

------------------------------------------------------------------------
-- The refutations

module _ (𝟘 : Iface) (ι : (B : Iface) → Proc B (𝟘 ⊗ᴵ B)) where

  private
    module T = TrivialGrade 𝟘 ι

    s₀ : Proc 𝟘 𝟘
    s₀ = deadᴹ

    dead-sim : (w : Proc unitᴵ Ωᴵ) → Dead (E.sub s₀ ∘ (ι Ωᴵ ∘ w))
    dead-sim w = dead-∘ˡ (ι Ωᴵ ∘ w) (dead-sub dead-deadᴹ)

  -- A divergent simulator makes an emulation at the trivial grade hold between
  -- processes layer 1 tells apart, so the collapse to a direct agreement fails.
  no-unit-grade : ¬ T.UnitGrade
  no-unit-grade ug = no-agree
    (ug Ωᴵ deadᴼ v₁ (s₀ , dead-≈ℰ (dead-∘ʳ (ι Ωᴵ) dead-deadᴹ) (dead-sim v₁)))

  -- …and with `IotaBlind` the same simulator identifies all closed processes.
  no-trivial-grade : T.SubBlind → T.IotaBlind → ⊥
  no-trivial-grade sb ib = no-agree (stratIsEnv Ωᴵ deadᴼ v₁ (ib Ωᴵ deadᴼ v₁ ι-agree))
    where
    ι-agree : (ι Ωᴵ ∘ deadᴼ) ≈ℰ (ι Ωᴵ ∘ v₁)
    ι-agree = ≈ℰ-trans (≈ℰ-sym (sb Ωᴵ s₀ deadᴼ))
                       (≈ℰ-trans (dead-≈ℰ (dead-sim deadᴼ) (dead-sim v₁))
                                 (sb Ωᴵ s₀ v₁))

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

unitGrade-refuted : ¬ TG.UnitGrade
unitGrade-refuted = no-unit-grade 𝟘ᴳ ιᴳ

subBlind-refuted : ¬ TG.SubBlind
subBlind-refuted sb = no-trivial-grade 𝟘ᴳ ιᴳ sb iotaBlind

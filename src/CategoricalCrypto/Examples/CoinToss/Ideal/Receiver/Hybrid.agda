{-# OPTIONS --safe --without-K --guardedness #-}

-- The hybrid half of the corrupted-receiver hop: the coin-toss stage over the
-- ideal `F_com` over the concrete resource IS `Receiver.Reach.eagerᶜʰ`.
-- `hashᴴʰ` takes the lookup explicitly: see `Examples.CoinToss.Ideal.Hybrid`.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories.Category

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.UC.QueryBound.Compose.Step as CS

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Reach k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

private
  module S  = Pw.S
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The composite

resᴵᵈʰ : Proc unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ)
resᴵᵈʰ = sandwichᴹ resource (Sum.map₂ downᶠʰ) (Sum.map₂ upᶠʰ)

stageᴴʰ : Proc (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ
stageᴴʰ = T₁ᴵ Lkᴵʰ tossʰ

hybridᴹʰ : Proc unitᴵ Cᵗʰ
hybridᴹʰ = 𝒫._∘_ {unitᴵ} {Resᴵ} {Cᵗʰ}
             (𝒫._∘_ {Resᴵ} {Cⁱʰ} {Cᵗʰ} a⇐ᴵ (𝒫._∘_ {Resᴵ} {Lkᴵʰ ⊗ᴵ Honᴵʰ} {Cⁱʰ} stageᴴʰ idealʰ))
             resource

private
  module Hᶜ = CS.CP unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ
  module Hᵁ = Hᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ)
  module Hᵂ = Hᶜ.Walk (CS.unfoldᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ)

  Hᴺ : Proc unitᴵ Cⁱʰ
  Hᴺ = CS.Nᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ

  stepᴴ = CS.stepᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ

------------------------------------------------------------------------
-- The state map, and the composite's loop at each letter

θᴴʰ : EStʰ → QSt × RState
θᴴʰ (preᴱ t)       = freshᵗ      , (t , nothing)
θᴴʰ (comᴱ t b₁)    = comᵗ b₁     , (t , just b₁)
θᴴʰ (opnᴱ t b₁ b₂) = openᵗ b₁ b₂ , (t , just b₁)
θᴴʰ (endᴱ t b₁)    = doneᵗ       , (t , just b₁)

private
  padᴴʰ : EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → (QSt × RState) × (Neg unitᴵ ⊎ Pos Cⁱʰ)
  padᴴʰ w = θᴴʰ (proj₁ w) , proj₂ w

  hearᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (q : LkQʰ)
           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
         → step resource ((t , m) , inj₂ (downᶠʰ (inj₁ q))) ≈ₚ D
         → stepᴴ ((sg , (t , m)) , inj₂ (inj₁ q))
         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠʰ (proj₂ w)))
  hearᴴʰ sg t m q eq =
        Hᵂ.R-down sg (t , m) (inj₁ q) sg (inj₁ q) ≈refl (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  askᴴʰ : (sg : QSt) (r : RState) (b : Neg (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ))
        → stepᴴ ((sg , r) , inj₂ (inj₂ b))
        ≈ₚ (τStep (sg , inj₂ b) >>=ₚ λ w → Hᶜ.resumeG r (proj₁ w , outT (proj₂ w)))
  askᴴʰ sg r b =
        Hᵁ.step-R sg r (inj₂ b)
    ⟨≈⟩ >>=ₚ-assoc (τStep (sg , inj₂ b)) _ (Hᶜ.resumeG r)
    ⟨≈⟩ bindᶠ λ where
          (sg′ , inj₁ e) → >>=ₚ-identityˡ (sg′ , inj₁ (inj₂ e)) (Hᶜ.resumeG r)
          (sg′ , inj₂ y) → >>=ₚ-identityˡ (sg′ , inj₂ (inj₂ y)) (Hᶜ.resumeG r)

  cellᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (e : HonQʰ)
           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
         → step resource ((t , m) , inj₂ (downᶠʰ (inj₂ e))) ≈ₚ D
         → Hᶜ.resumeG (t , m) (sg , inj₁ (inj₂ e))
         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠʰ (proj₂ w)))
  cellᴴʰ sg t m e eq =
        Hᵁ.solve-B⁻ sg (t , m) (inj₂ e)
    ⟨≈⟩ bindˣ (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  lkᴴʰ : (sg : QSt) (r : RState) (y : LkAʰ)
       → Hᶜ.resumeF sg (r , inj₂ (inj₁ y)) ≈ₚ returnₚ ((sg , r) , inj₂ (inj₁ y))
  lkᴴʰ sg r y = Hᵂ.F-up sg r (inj₁ y) sg (inj₁ y) ≈refl

  hashᴴʰ : (φ : Tbl → EStʰ) (sg : QSt) (m : Maybe Bool)
         → ((u : Tbl) → θᴴʰ (φ u) ≡ (sg , (u , m)))
         → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
         → mapₚ padᴴʰ (hashᶜʰ t φ x) ≈ₚ stepᴴ ((sg , (t , m)) , inj₂ (inj₁ (relayᶠ x)))
  hashᴴʰ φ sg m hyp t x w eqL =
        lazy-bind _ κ (λ z → returnₚ (padᴴʰ z)) (λ u d → ret≡ (cong (_, inj₂ (inj₁ (digᶠ d))) (hyp u)))
                  t x w eqL
    ⟨≈⟩ ≈sym ( hearᴴʰ sg t m (relayᶠ x) (≈ₚ-refl _)
           ⟨≈⟩ lazy-bind (λ u d → (u , m) , inj₂ (digᴿ d)) κ _ (λ u d → lkᴴʰ sg (u , m) (digᶠ d))
                         t x w eqL )
    where κ = λ u d → (sg , (u , m)) , inj₂ (inj₁ (digᶠ d))

  hybStep : (cs : EStʰ) (z : Pos unitᴵ ⊎ Neg Cⁱʰ)
          → mapₚ padᴴʰ (eStep (cs , z)) ≈ₚ stepᴴ (θᴴʰ cs , z)
  hybStep _ (inj₁ ())
  hybStep (preᴱ t)       (inj₂ (inj₁ (relayᶠ x))) =
    hashᴴʰ preᴱ freshᵗ nothing (λ _ → refl) t x _ refl
  hybStep (comᴱ t b₁)    (inj₂ (inj₁ (relayᶠ x))) =
    hashᴴʰ (λ u → comᴱ u b₁) (comᵗ b₁) (just b₁) (λ _ → refl) t x _ refl
  hybStep (opnᴱ t b₁ b₂) (inj₂ (inj₁ (relayᶠ x))) =
    hashᴴʰ (λ u → opnᴱ u b₁ b₂) (openᵗ b₁ b₂) (just b₁) (λ _ → refl) t x _ refl
  hybStep (endᴱ t b₁)    (inj₂ (inj₁ (relayᶠ x))) =
    hashᴴʰ (λ u → endᴱ u b₁) doneᵗ (just b₁) (λ _ → refl) t x _ refl
  hybStep (preᴱ t)       (inj₂ (inj₂ (inj₁ (shareᴬʰ b₂)))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ freshᵗ (t , nothing) (inj₁ (shareᴬʰ b₂)) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (comᴱ t b₁)    (inj₂ (inj₂ (inj₁ (shareᴬʰ b₂)))) =
        >>=ₚ-identityˡ (opnᴱ t b₁ b₂ , inj₂ (inj₁ (bitᶠ b₁))) _
    ⟨≈⟩ ≈sym ( askᴴʰ (comᵗ b₁) (t , just b₁) (inj₁ (shareᴬʰ b₂))
           ⟨≈⟩ >>=ₚ-identityˡ (openᵗ b₁ b₂ , inj₁ openᴱ) _
           ⟨≈⟩ cellᴴʰ (openᵗ b₁ b₂) t (just b₁) openᴱ (cell-get t b₁)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ (outᴿ b₁)) _
           ⟨≈⟩ lkᴴʰ (openᵗ b₁ b₂) (t , just b₁) (bitᶠ b₁) )
  hybStep (opnᴱ t b₁ b₂) (inj₂ (inj₂ (inj₁ (shareᴬʰ b)))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ (openᵗ b₁ b₂) (t , just b₁) (inj₁ (shareᴬʰ b)) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (endᴱ t b₁)    (inj₂ (inj₂ (inj₁ (shareᴬʰ b)))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ doneᵗ (t , just b₁) (inj₁ (shareᴬʰ b)) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (preᴱ t)       (inj₂ (inj₂ (inj₂ goᶜ))) =
        >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ (λ b₁ → >>=ₚ-identityˡ (comᴱ t b₁ , inj₂ (inj₁ rcptᶠ)) _)
    ⟨≈⟩ ≈sym ( askᴴʰ freshᵗ (t , nothing) (inj₂ goᶜ)
           ⟨≈⟩ >>=ₚ-assoc (coinₚ uniform-Bool) _ _
           ⟨≈⟩ bindᶠ (λ b₁ → >>=ₚ-identityˡ (comᵗ b₁ , inj₁ (commitᴱ b₁)) _
                         ⟨≈⟩ cellᴴʰ (comᵗ b₁) t nothing (commitᴱ b₁) (cell-put t b₁)
                         ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ rcptᴿ) _
                         ⟨≈⟩ lkᴴʰ (comᵗ b₁) (t , just b₁) rcptᶠ) )
  hybStep (comᴱ t b₁)    (inj₂ (inj₂ (inj₂ goᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ (comᵗ b₁) (t , just b₁) (inj₂ goᶜ) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (opnᴱ t b₁ b₂) (inj₂ (inj₂ (inj₂ goᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ (openᵗ b₁ b₂) (t , just b₁) (inj₂ goᶜ) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (endᴱ t b₁)    (inj₂ (inj₂ (inj₂ goᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ doneᵗ (t , just b₁) (inj₂ goᶜ) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (preᴱ t)       (inj₂ (inj₂ (inj₂ getᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ freshᵗ (t , nothing) (inj₂ getᶜ) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (comᴱ t b₁)    (inj₂ (inj₂ (inj₂ getᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ (comᵗ b₁) (t , just b₁) (inj₂ getᶜ) ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (opnᴱ t b₁ b₂) (inj₂ (inj₂ (inj₂ getᶜ))) =
        >>=ₚ-identityˡ (endᴱ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))) _
    ⟨≈⟩ ≈sym ( askᴴʰ (openᵗ b₁ b₂) (t , just b₁) (inj₂ getᶜ)
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵗ , inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))) _
           ⟨≈⟩ Hᵁ.solve-out (doneᵗ , (t , just b₁)) (inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))) )
  hybStep (endᴱ t b₁)    (inj₂ (inj₂ (inj₂ getᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ doneᵗ (t , just b₁) (inj₂ getᶜ) ⟨≈⟩ bot-bind-≈ₚ _)

hyb-simʰ : eagerᶜʰ′ S.≲ Hᴺ
hyb-simʰ = Pw.simFn θᴴʰ
                 (λ x → >>=ₚ-identityˡ (preᴱ []) _
                    ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                           ⟨≈⟩ >>=ₚ-identityˡ freshᵗ _
                           ⟨≈⟩ >>=ₚ-identityˡ ([] , nothing) _))
                 (uncurry hybStep)

------------------------------------------------------------------------
-- …and the composite, read as `eagerᶜʰ`

private
  reassocʰ : 𝒫._≈_ {unitᴵ} {Cᵗʰ} hybridᴹʰ
               (𝒫._∘_ {unitᴵ} {Cⁱʰ} {Cᵗʰ} a⇐ᴵ
                 (𝒫._∘_ {unitᴵ} {Lkᴵʰ ⊗ᴵ Honᴵʰ} {Cⁱʰ} stageᴴʰ resᴵᵈʰ))
  reassocʰ = 𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (wire-∘ᴹ upᶠʰ downᶠʰ resource))

hybrid-eqʰ : 𝒫._≈_ {unitᴵ} {Cᵗʰ} hybridᴹʰ eagerᶜʰ
hybrid-eqʰ = reassocʰ
        S.○ᴹ 𝒫.∘-resp-≈ʳ ( S.⟺ᴹ (CS.eq-∘ᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ)
                      S.○ᴹ S.≲⇒≈ᴹ˘ hyb-simʰ )
        S.○ᴹ wire-∘ᴹ ⊎assocˡ ⊎assocʳ eagerᶜʰ′

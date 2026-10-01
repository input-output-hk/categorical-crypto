{-# OPTIONS --safe --without-K --guardedness #-}

-- The hybrid half of the second hop: the coin-toss stage over the ideal
-- `F_com` over the concrete resource IS `Examples.CoinToss.Ideal.Reach.coinᶜ`.
--
-- `hashᴴ` takes the lookup as an explicit argument: `with lookupPt t x` costs
-- 3m22s against 10s (measured), because `with` normalises a goal that names
-- the composite's step.

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

module CategoricalCrypto.Examples.CoinToss.Ideal.Hybrid (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Reach k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

private
  module S  = Pw.S
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The composite

resᴵᵈ : Proc unitᴵ (Lkᴵ ⊗ᴵ Honᴵ)
resᴵᵈ = sandwichᴹ resource (Sum.map₂ downᶠ) (Sum.map₂ upᶠ)

stageᴴ : Proc (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ
stageᴴ = T₁ᴵ Lkᴵ toss

-- The hybrid as `UC.Graded.ext-graded`/`graded₂-∘` leave it.
hybridᴹ : Proc unitᴵ Cᵗ
hybridᴹ = 𝒫._∘_ {unitᴵ} {Resᴵ} {Cᵗ}
            (𝒫._∘_ {Resᴵ} {Cⁱ} {Cᵗ} a⇐ᴵ (𝒫._∘_ {Resᴵ} {Lkᴵ ⊗ᴵ Honᴵ} {Cⁱ} stageᴴ ideal))
            resource

private
  module Hᶜ = CS.CP unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ
  module Hᵁ = Hᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ)
  module Hᵂ = Hᶜ.Walk (CS.unfoldᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ)

  Hᴺ : Proc unitᴵ Cⁱ
  Hᴺ = CS.Nᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ

  stepᴴ = CS.stepᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ

------------------------------------------------------------------------
-- The state map, and the composite's loop at each letter

θᴴ : CSt → PSt × RState
θᴴ (preᶜ t)       = freshᵖ   , (t , nothing)
θᴴ (midᶜ t b₁ b₂) = heldᵖ b₂ , (t , just b₁)
θᴴ (postᶜ t b₁)   = doneᵖ    , (t , just b₁)

private
  padᴴ : CSt × (Neg unitᴵ ⊎ Pos Cⁱ) → (PSt × RState) × (Neg unitᴵ ⊎ Pos Cⁱ)
  padᴴ w = θᴴ (proj₁ w) , proj₂ w

  posᵖ : Neg Honᴵ ⊎ Pos (Advᴵᶜ ⊗ᴵ Honᴵᶜ) → Pos Cⁱ
  posᵖ (inj₁ ())
  posᵖ (inj₂ y) = inj₂ y

  hearᴴ : (sg : PSt) (t : Tbl) (m : Maybe Bool) (q : LkQ)
          {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
        → step resource ((t , m) , inj₂ (downᶠ (inj₁ q))) ≈ₚ D
        → stepᴴ ((sg , (t , m)) , inj₂ (inj₁ q))
        ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠ (proj₂ w)))
  hearᴴ sg t m q eq =
        Hᵂ.R-down sg (t , m) (inj₁ q) sg (inj₁ q) ≈refl (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  honᴴ : (sg : PSt) (r : RState) (a : HonA)
       → Hᶜ.resumeF sg (r , inj₂ (inj₂ a))
       ≈ₚ (πStep (sg , inj₁ a) >>=ₚ λ w → returnₚ ((proj₁ w , r) , inj₂ (posᵖ (proj₂ w))))
  honᴴ sg r a =
        Hᵁ.solve-B⁺ sg r (inj₂ a)
    ⟨≈⟩ >>=ₚ-assoc (πStep (sg , inj₁ a)) _ _
    ⟨≈⟩ bindᶠ λ where
          (_   , inj₁ ())
          (sg′ , inj₂ y)  → >>=ₚ-identityˡ (sg′ , inj₂ (inj₂ y)) (Hᶜ.resumeG r)
                        ⟨≈⟩ Hᵁ.solve-out (sg′ , r) (inj₂ (inj₂ y))

  hashᴴ : (φ : Tbl → CSt) (sg : PSt) (m : Maybe Bool)
        → ((u : Tbl) → θᴴ (φ u) ≡ (sg , (u , m)))
        → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
        → mapₚ padᴴ (hashᶜ t φ x) ≈ₚ stepᴴ ((sg , (t , m)) , inj₂ (inj₁ (hashˢ x)))
  hashᴴ φ sg m hyp t x w eqL =
        lazy-bind _ κ (λ z → returnₚ (padᴴ z)) (λ u d → ret≡ (cong (_, inj₂ (inj₁ (digˢ d))) (hyp u)))
                  t x w eqL
    ⟨≈⟩ ≈sym ( hearᴴ sg t m (hashˢ x) (≈ₚ-refl _)
           ⟨≈⟩ lazy-bind (λ u d → (u , m) , inj₂ (digᴿ d)) κ _ (λ u d → Hᵂ.F-up sg (u , m) (inj₁ (digˢ d)) sg (inj₁ (digˢ d)) ≈refl)
                         t x w eqL )
    where κ = λ u d → (sg , (u , m)) , inj₂ (inj₁ (digˢ d))

  hybStep : (cs : CSt) (z : Pos unitᴵ ⊎ Neg Cⁱ)
          → mapₚ padᴴ (cStep (cs , z)) ≈ₚ stepᴴ (θᴴ cs , z)
  hybStep _ (inj₁ ())
  hybStep _ (inj₂ (inj₂ (inj₁ ())))
  hybStep _ (inj₂ (inj₂ (inj₂ ())))
  hybStep (preᶜ t)       (inj₂ (inj₁ (hashˢ x))) =
    hashᴴ preᶜ freshᵖ nothing (λ _ → refl) t x _ refl
  hybStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (hashˢ x))) =
    hashᴴ (λ u → midᶜ u b₁ b₂) (heldᵖ b₂) (just b₁) (λ _ → refl) t x _ refl
  hybStep (postᶜ t b₁)   (inj₂ (inj₁ (hashˢ x))) =
    hashᴴ (λ u → postᶜ u b₁) doneᵖ (just b₁) (λ _ → refl) t x _ refl
  hybStep (preᶜ t)       (inj₂ (inj₁ (commitˢ b₁))) =
        >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ (λ b₂ → >>=ₚ-identityˡ (midᶜ t b₁ b₂ , inj₂ (inj₂ (inj₁ (shareᴬ b₂)))) _)
    ⟨≈⟩ ≈sym ( hearᴴ freshᵖ t nothing (commitˢ b₁) (cell-put t b₁)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ rcptᴿ) _
           ⟨≈⟩ honᴴ freshᵖ (t , just b₁) rcptᴴ
           ⟨≈⟩ >>=ₚ-assoc (coinₚ uniform-Bool) _ _
           ⟨≈⟩ bindᶠ (λ b₂ → >>=ₚ-identityˡ (heldᵖ b₂ , inj₂ (inj₁ (shareᴬ b₂))) _) )
  hybStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (commitˢ b))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (hearᴴ (heldᵖ b₂) t (just b₁) (commitˢ b) ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (postᶜ t b₁)   (inj₂ (inj₁ (commitˢ b))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (hearᴴ doneᵖ t (just b₁) (commitˢ b) ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (preᶜ t)       (inj₂ (inj₁ openˢ)) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (hearᴴ freshᵖ t nothing openˢ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  hybStep (midᶜ t b₁ b₂) (inj₂ (inj₁ openˢ)) =
        >>=ₚ-identityˡ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜ (b₁ xor b₂))))) _
    ⟨≈⟩ ≈sym ( hearᴴ (heldᵖ b₂) t (just b₁) openˢ (cell-get t b₁)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ (outᴿ b₁)) _
           ⟨≈⟩ honᴴ (heldᵖ b₂) (t , just b₁) (openedᴴ b₁)
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵖ , inj₂ (inj₂ (tossedᶜ (b₁ xor b₂)))) _ )
  hybStep (postᶜ t b₁)   (inj₂ (inj₁ openˢ)) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym ( hearᴴ doneᵖ t (just b₁) openˢ (cell-get t b₁)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ (outᴿ b₁)) _
           ⟨≈⟩ honᴴ doneᵖ (t , just b₁) (openedᴴ b₁)
           ⟨≈⟩ bot-bind-≈ₚ _ )
  hybStep (preᶜ t)       (inj₂ (inj₁ failˢ)) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym ( hearᴴ freshᵖ t nothing failˢ (cell-nak t nothing)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , nothing) , inj₂ rejᴿ) _
           ⟨≈⟩ honᴴ freshᵖ (t , nothing) refusedᴴ
           ⟨≈⟩ bot-bind-≈ₚ _ )
  hybStep (midᶜ t b₁ b₂) (inj₂ (inj₁ failˢ)) =
        >>=ₚ-identityˡ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ abortedᶜ))) _
    ⟨≈⟩ ≈sym ( hearᴴ (heldᵖ b₂) t (just b₁) failˢ (cell-nak t (just b₁))
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ rejᴿ) _
           ⟨≈⟩ honᴴ (heldᵖ b₂) (t , just b₁) refusedᴴ
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵖ , inj₂ (inj₂ abortedᶜ)) _ )
  hybStep (postᶜ t b₁)   (inj₂ (inj₁ failˢ)) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym ( hearᴴ doneᵖ t (just b₁) failˢ (cell-nak t (just b₁))
           ⟨≈⟩ >>=ₚ-identityˡ ((t , just b₁) , inj₂ rejᴿ) _
           ⟨≈⟩ honᴴ doneᵖ (t , just b₁) refusedᴴ
           ⟨≈⟩ bot-bind-≈ₚ _ )

hyb-sim : coinᶜ′ S.≲ Hᴺ
hyb-sim = Pw.simFn θᴴ
                (λ x → >>=ₚ-identityˡ (preᶜ []) _
                   ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                          ⟨≈⟩ >>=ₚ-identityˡ freshᵖ _
                          ⟨≈⟩ >>=ₚ-identityˡ ([] , nothing) _))
                (uncurry hybStep)

------------------------------------------------------------------------
-- …and the composite, read as `coinᶜ`

private
  reassoc : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ
              (𝒫._∘_ {unitᴵ} {Cⁱ} {Cᵗ} a⇐ᴵ
                (𝒫._∘_ {unitᴵ} {Lkᴵ ⊗ᴵ Honᴵ} {Cⁱ} stageᴴ resᴵᵈ))
  reassoc = 𝒫.assoc
       S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (wire-∘ᴹ upᶠ downᶠ resource))

hybrid-eq : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ coinᶜ
hybrid-eq = reassoc
       S.○ᴹ 𝒫.∘-resp-≈ʳ ( S.⟺ᴹ (CS.eq-∘ᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ)
                     S.○ᴹ S.≲⇒≈ᴹ˘ hyb-sim )
       S.○ᴹ wire-∘ᴹ ⊎assocˡ ⊎assocʳ coinᶜ′

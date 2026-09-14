{-# OPTIONS --safe --without-K --guardedness #-}

-- The hybrid half of the second hop: the coin-toss stage over the ideal
-- `F_com` over the concrete resource IS `Examples.CoinToss.Ideal.Reach.coinᶜ`.
--
-- The composite is a ⊕-trace of two stateful machines, so
-- `UC.Machine.Wire.∘-wireᴹ` does not apply; what does is
-- `UC.QueryBound.Compose.Step`'s reading of a `𝒢ₚ`-composite as one machine
-- with the product state, plus the six equations `Unfolding` collects.  The
-- two wires the composite does carry — `_∙ᶠ_`'s associator on top and the
-- ideal functionality itself — are absorbed for free.
--
-- A `with lookupPt t x` in `hashᴴ` costs 3m22s against 10s, measured: `with`
-- normalises the goal to look for the scrutinee, and the goal names the
-- composite's step, which unfolds through the trace.  The scrutinee is an
-- explicit argument instead.

open import Data.Bool.Base using (Bool; _xor_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

open import Categories.Category using (Category)
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (Dₚ-DiscreteMonad; 𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; T₁ᴵ; a⇒ᴵ)
open import CategoricalCrypto.UC.Machine.Wire using (sandwichᴹ; wire-∘ᴹ)

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
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The composite

-- `ideal`'s wire absorbed into the resource: the same state, with `Resᴵ`
-- relabelled onto the ideal functionality's two ports.
resᴵᵈ : Proc unitᴵ (Lkᴵ ⊗ᴵ Honᴵ)
resᴵᵈ = sandwichᴹ resource (Sum.map (λ a → a) downᶠ) (Sum.map (λ a → a) upᶠ)

stageᴴ : Proc (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ
stageᴴ = T₁ᴵ Lkᴵ toss

-- The hybrid as `UC.Graded.ext-graded`/`graded₂-∘` leave it.
hybridᴹ : Proc unitᴵ Cᵗ
hybridᴹ = 𝒫._∘_ {unitᴵ} {Resᴵ} {Cᵗ}
            (𝒫._∘_ {Resᴵ} {Cⁱ} {Cᵗ} a⇒ᴵ (𝒫._∘_ {Resᴵ} {Lkᴵ ⊗ᴵ Honᴵ} {Cⁱ} stageᴴ ideal))
            resource

private
  module Hᶜ = CS.CP unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ
  module Hᵁ = Hᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ)

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

  -- `Neg Honᴵ` is empty, so the stage's relay of a `toss` answer always leaves
  -- upwards.
  posᵖ : Neg Honᴵ ⊎ Pos (Advᴵᶜ ⊗ᴵ Honᴵᶜ) → Pos Cⁱ
  posᵖ (inj₁ ())
  posᵖ (inj₂ y) = inj₂ y

  -- The stage forwards a downward `Lkᴵ` letter and the resource acts on it.
  hearᴴ : (sg : PSt) (t : Tbl) (m : Maybe Bool) (q : LkQ)
          {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
        → step resource ((t , m) , inj₂ (downᶠ (inj₁ q))) ≈ₚ D
        → stepᴴ ((sg , (t , m)) , inj₂ (inj₁ q))
        ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map (λ a → a) upᶠ (proj₂ w)))
  hearᴴ sg t m q eq =
        Hᵁ.step-R sg (t , m) (inj₁ q)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₁ (inj₁ q)) (Hᶜ.resumeG (t , m))
    ⟨≈⟩ Hᵁ.solve-B⁻ sg (t , m) (inj₁ q)
    ⟨≈⟩ bindˣ (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  -- The resource answers on the leak port and the stage relays it straight up.
  lkᴴ : (sg : PSt) (r : RState) (d : Dig)
      → Hᶜ.resumeF sg (r , inj₂ (inj₁ (digˢ d)))
      ≈ₚ returnₚ ((sg , r) , inj₂ (inj₁ (digˢ d)))
  lkᴴ sg r d =
        Hᵁ.solve-B⁺ sg r (inj₁ (digˢ d))
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₂ (inj₁ (digˢ d))) (Hᶜ.resumeG r)
    ⟨≈⟩ Hᵁ.solve-out (sg , r) (inj₂ (inj₁ (digˢ d)))

  -- …or on the receiver's port, where it wakes the coin-toss stage.
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

  -- A hash query moves the table and nothing else, whatever phase the toss is
  -- in; `φ` carries that phase across the table update.
  hashᴴ : (φ : Tbl → CSt) (sg : PSt) (m : Maybe Bool)
        → ((u : Tbl) → θᴴ (φ u) ≡ (sg , (u , m)))
        → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
        → mapₚ padᴴ (hashᶜ t φ x) ≈ₚ stepᴴ ((sg , (t , m)) , inj₂ (inj₁ (hashˢ x)))
  hashᴴ φ sg m hyp t x (just d) eqL =
        map-arg padᴴ (hashᶜ-hit t φ x d eqL)
    ⟨≈⟩ >>=ₚ-identityˡ (φ t , inj₂ (inj₁ (digˢ d))) _
    ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (digˢ d))) (hyp t))
    ⟨≈⟩ ≈sym ( hearᴴ sg t m (hashˢ x) (hash-hit t m x d eqL)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , m) , inj₂ (digᴿ d)) _
           ⟨≈⟩ lkᴴ sg (t , m) d )
  hashᴴ φ sg m hyp t x nothing eqL =
        map-arg padᴴ (hashᶜ-miss t φ x eqL)
    ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
    ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h))) _
                 ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (digˢ h))) (hyp ((x , h) ∷ t))))
    ⟨≈⟩ ≈sym ( hearᴴ sg t m (hashˢ x) (hash-miss t m x eqL)
           ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
           ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (((x , h) ∷ t , m) , inj₂ (digᴿ h)) _
                        ⟨≈⟩ lkᴴ sg ((x , h) ∷ t , m) h) )

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
hyb-sim = S.sim (K.pureᵏ θᴴ) (KP.structural θᴴ)
                (λ r → >>=ₚ-identityˡ (θᴴ r) _
                   ⟨≈⟩ bindˣ (>>=ₚ-identityˡ tt _ ⟨≈⟩ >>=ₚ-identityˡ tt _)
                   ⟨≈⟩ >>=ₚ-identityˡ (tt , tt) _)
                (λ x → >>=ₚ-identityˡ (preᶜ []) _
                   ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                          ⟨≈⟩ >>=ₚ-identityˡ freshᵖ _
                          ⟨≈⟩ >>=ₚ-identityˡ ([] , nothing) _))
                (λ z → bindᶠ (Pw.⊗-pureˡ θᴴ) ⟨≈⟩ hybStep (proj₁ z) (proj₂ z)
                   ⟨≈⟩ ≈sym ( bindˣ (Pw.⊗-pureˡ θᴴ z)
                          ⟨≈⟩ >>=ₚ-identityˡ (θᴴ (proj₁ z) , proj₂ z) _))

------------------------------------------------------------------------
-- …and the composite, read as `coinᶜ`

private
  -- The two wires the composite carries — `_∙ᶠ_`'s associator on top and the
  -- ideal functionality itself — cost no trace.
  reassoc : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ
              (𝒫._∘_ {unitᴵ} {Cⁱ} {Cᵗ} a⇒ᴵ
                (𝒫._∘_ {unitᴵ} {Lkᴵ ⊗ᴵ Honᴵ} {Cⁱ} stageᴴ resᴵᵈ))
  reassoc = 𝒫.assoc
       S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (wire-∘ᴹ upᶠ downᶠ resource))

hybrid-eq : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ coinᶜ
hybrid-eq = reassoc
       S.○ᴹ 𝒫.∘-resp-≈ʳ ( S.⟺ᴹ (CS.eq-∘ᶜ unitᴵ (Lkᴵ ⊗ᴵ Honᴵ) Cⁱ stageᴴ resᴵᵈ)
                     S.○ᴹ S.≲⇒≈ᴹ˘ hyb-sim )
       S.○ᴹ wire-∘ᴹ ⊎assocˡ ⊎assocʳ coinᶜ′

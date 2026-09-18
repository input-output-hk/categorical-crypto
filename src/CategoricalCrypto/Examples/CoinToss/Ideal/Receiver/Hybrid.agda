{-# OPTIONS --safe --without-K --guardedness #-}

-- The hybrid half of the corrupted-receiver hop: the coin-toss stage over the
-- ideal `F_com` over the concrete resource IS `Receiver.Reach.eagerᶜʰ`.
--
-- `Examples.CoinToss.Ideal.Hybrid` is the corrupted-committer twin and the
-- shape is its; what is new is that this stage DRIVES `F_com` — `Neg Honᴵʰ` is
-- inhabited — so the composite's loop has two more legs than the extraction
-- half's: the stage's own downward call (`cellᴴʰ`) and the answer climbing
-- back into it.  `hearᴴʰ`/`lkᴴʰ` are the extraction half's `hearᴴ`/`lkᴴ` at
-- these ports.
--
-- A `with lookupPt t x` in `hashᴴʰ` is the measured 3m22s trap that module's
-- header records; the scrutinee is an explicit argument here too.

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
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The composite

-- `idealʰ`'s wire absorbed into the resource: the same state, with `Resᴵ`
-- relabelled onto the ideal functionality's two ports.
resᴵᵈʰ : Proc unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ)
resᴵᵈʰ = sandwichᴹ resource (Sum.map (λ a → a) downᶠʰ) (Sum.map (λ a → a) upᶠʰ)

stageᴴʰ : Proc (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ
stageᴴʰ = T₁ᴵ Lkᴵʰ tossʰ

hybridᴹʰ : Proc unitᴵ Cᵗʰ
hybridᴹʰ = 𝒫._∘_ {unitᴵ} {Resᴵ} {Cᵗʰ}
             (𝒫._∘_ {Resᴵ} {Cⁱʰ} {Cᵗʰ} a⇒ᴵ (𝒫._∘_ {Resᴵ} {Lkᴵʰ ⊗ᴵ Honᴵʰ} {Cⁱʰ} stageᴴʰ idealʰ))
             resource

private
  module Hᶜ = CS.CP unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ
  module Hᵁ = Hᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ)

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

  -- `T₁ᴵ`'s relay: the stage's downward letter descends, its upward one
  -- leaves past the bypassed leak port.
  outTʰ : Neg Honᴵʰ ⊎ Pos (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) → Neg (Lkᴵʰ ⊗ᴵ Honᴵʰ) ⊎ Pos Cⁱʰ
  outTʰ (inj₁ e) = inj₁ (inj₂ e)
  outTʰ (inj₂ y) = inj₂ (inj₂ y)

  -- The environment's oracle query passes the stage untouched and the
  -- resource acts on it.
  hearᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (q : LkQʰ)
           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
         → step resource ((t , m) , inj₂ (downᶠʰ (inj₁ q))) ≈ₚ D
         → stepᴴ ((sg , (t , m)) , inj₂ (inj₁ q))
         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map (λ a → a) upᶠʰ (proj₂ w)))
  hearᴴʰ sg t m q eq =
        Hᵁ.step-R sg (t , m) (inj₁ q)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₁ (inj₁ q)) (Hᶜ.resumeG (t , m))
    ⟨≈⟩ Hᵁ.solve-B⁻ sg (t , m) (inj₁ q)
    ⟨≈⟩ bindˣ (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  -- An activation from above that the stage itself hears.
  askᴴʰ : (sg : QSt) (r : RState) (b : Neg (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ))
        → stepᴴ ((sg , r) , inj₂ (inj₂ b))
        ≈ₚ (τStep (sg , inj₂ b) >>=ₚ λ w → Hᶜ.resumeG r (proj₁ w , outTʰ (proj₂ w)))
  askᴴʰ sg r b =
        Hᵁ.step-R sg r (inj₂ b)
    ⟨≈⟩ >>=ₚ-assoc (τStep (sg , inj₂ b)) _ (Hᶜ.resumeG r)
    ⟨≈⟩ bindᶠ λ where
          (sg′ , inj₁ e) → >>=ₚ-identityˡ (sg′ , inj₁ (inj₂ e)) (Hᶜ.resumeG r)
          (sg′ , inj₂ y) → >>=ₚ-identityˡ (sg′ , inj₂ (inj₂ y)) (Hᶜ.resumeG r)

  -- …the stage's own downward call, which the cell answers.
  cellᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (e : HonQʰ)
           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}
         → step resource ((t , m) , inj₂ (downᶠʰ (inj₂ e))) ≈ₚ D
         → Hᶜ.resumeG (t , m) (sg , inj₁ (inj₂ e))
         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map (λ a → a) upᶠʰ (proj₂ w)))
  cellᴴʰ sg t m e eq =
        Hᵁ.solve-B⁻ sg (t , m) (inj₂ e)
    ⟨≈⟩ bindˣ (bindˣ eq)
    ⟨≈⟩ >>=ₚ-assoc _ _ _
    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)

  -- …the resource's answer on the leak port, relayed straight out.
  lkᴴʰ : (sg : QSt) (r : RState) (y : LkAʰ)
       → Hᶜ.resumeF sg (r , inj₂ (inj₁ y)) ≈ₚ returnₚ ((sg , r) , inj₂ (inj₁ y))
  lkᴴʰ sg r y =
        Hᵁ.solve-B⁺ sg r (inj₁ y)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₂ (inj₁ y)) (Hᶜ.resumeG r)
    ⟨≈⟩ Hᵁ.solve-out (sg , r) (inj₂ (inj₁ y))

  -- …and the stage's own upward answer, which exits at once.
  outᴴʰ : (sg : QSt) (r : RState) (y : Pos Cⁱʰ)
        → Hᶜ.resumeG r (sg , inj₂ y) ≈ₚ returnₚ ((sg , r) , inj₂ y)
  outᴴʰ sg r y = Hᵁ.solve-out (sg , r) (inj₂ y)

  -- A hash query moves the table and nothing else, whatever phase the toss is
  -- in; `φ` carries that phase across the table update.
  hashᴴʰ : (φ : Tbl → EStʰ) (sg : QSt) (m : Maybe Bool)
         → ((u : Tbl) → θᴴʰ (φ u) ≡ (sg , (u , m)))
         → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
         → mapₚ padᴴʰ (hashᶜʰ t φ x) ≈ₚ stepᴴ ((sg , (t , m)) , inj₂ (inj₁ (relayᶠ x)))
  hashᴴʰ φ sg m hyp t x (just d) eqL =
        map-arg padᴴʰ (hashᶜʰ-hit t φ x d eqL)
    ⟨≈⟩ >>=ₚ-identityˡ (φ t , inj₂ (inj₁ (digᶠ d))) _
    ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (digᶠ d))) (hyp t))
    ⟨≈⟩ ≈sym ( hearᴴʰ sg t m (relayᶠ x) (hash-hit t m x d eqL)
           ⟨≈⟩ >>=ₚ-identityˡ ((t , m) , inj₂ (digᴿ d)) _
           ⟨≈⟩ lkᴴʰ sg (t , m) (digᶠ d) )
  hashᴴʰ φ sg m hyp t x nothing eqL =
        map-arg padᴴʰ (hashᶜʰ-miss t φ x eqL)
    ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
    ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))) _
                 ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (digᶠ h))) (hyp ((x , h) ∷ t))))
    ⟨≈⟩ ≈sym ( hearᴴʰ sg t m (relayᶠ x) (hash-miss t m x eqL)
           ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
           ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (((x , h) ∷ t , m) , inj₂ (digᴿ h)) _
                        ⟨≈⟩ lkᴴʰ sg ((x , h) ∷ t , m) (digᶠ h)) )

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
           ⟨≈⟩ outᴴʰ doneᵗ (t , just b₁) (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))) )
  hybStep (endᴱ t b₁)    (inj₂ (inj₂ (inj₂ getᶜ))) =
        bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (askᴴʰ doneᵗ (t , just b₁) (inj₂ getᶜ) ⟨≈⟩ bot-bind-≈ₚ _)

hyb-simʰ : eagerᶜʰ′ S.≲ Hᴺ
hyb-simʰ = S.sim (K.pureᵏ θᴴʰ) (KP.structural θᴴʰ)
                 (λ r → >>=ₚ-identityˡ (θᴴʰ r) _
                    ⟨≈⟩ bindˣ (>>=ₚ-identityˡ tt _ ⟨≈⟩ >>=ₚ-identityˡ tt _)
                    ⟨≈⟩ >>=ₚ-identityˡ (tt , tt) _)
                 (λ x → >>=ₚ-identityˡ (preᴱ []) _
                    ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                           ⟨≈⟩ >>=ₚ-identityˡ freshᵗ _
                           ⟨≈⟩ >>=ₚ-identityˡ ([] , nothing) _))
                 (λ z → bindᶠ (Pw.⊗-pureˡ θᴴʰ) ⟨≈⟩ hybStep (proj₁ z) (proj₂ z)
                    ⟨≈⟩ ≈sym ( bindˣ (Pw.⊗-pureˡ θᴴʰ z)
                           ⟨≈⟩ >>=ₚ-identityˡ (θᴴʰ (proj₁ z) , proj₂ z) _))

------------------------------------------------------------------------
-- …and the composite, read as `eagerᶜʰ`

private
  -- The two wires the composite carries — `_∙ᶠ_`'s associator on top and the
  -- ideal functionality itself — cost no trace.
  reassocʰ : 𝒫._≈_ {unitᴵ} {Cᵗʰ} hybridᴹʰ
               (𝒫._∘_ {unitᴵ} {Cⁱʰ} {Cᵗʰ} a⇒ᴵ
                 (𝒫._∘_ {unitᴵ} {Lkᴵʰ ⊗ᴵ Honᴵʰ} {Cⁱʰ} stageᴴʰ resᴵᵈʰ))
  reassocʰ = 𝒫.assoc
        S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc S.○ᴹ 𝒫.∘-resp-≈ʳ (wire-∘ᴹ upᶠʰ downᶠʰ resource))

hybrid-eqʰ : 𝒫._≈_ {unitᴵ} {Cᵗʰ} hybridᴹʰ eagerᶜʰ
hybrid-eqʰ = reassocʰ
        S.○ᴹ 𝒫.∘-resp-≈ʳ ( S.⟺ᴹ (CS.eq-∘ᶜ unitᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ) Cⁱʰ stageᴴʰ resᴵᵈʰ)
                      S.○ᴹ S.≲⇒≈ᴹ˘ hyb-simʰ )
        S.○ᴹ wire-∘ᴹ ⊎assocˡ ⊎assocʳ eagerᶜʰ′

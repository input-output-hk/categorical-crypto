{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop's machine equality: Blum coin-tossing over the ideal `F_com`,
-- run over the concrete resource, IS the joint simulator over the ideal coin
-- (through `Examples.CoinToss.Ideal.Reach.coinᶜ`).  The one non-structural step
-- is `Dp.Coin.coin-flip` at `commitˢ b₁`: the hybrid samples the share, the
-- ideal side the coin (`docs/coin-toss.md` §5).

open import Data.Bool.Base
open import Data.Bool.Properties
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
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.UC.QueryBound.Compose.Step as CS

module CategoricalCrypto.Examples.CoinToss.Ideal.Machine (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.CoinToss.Ideal k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Hybrid k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Reach k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

private
  module S  = Pw.S
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The ideal composite

simᴵᵈ : Proc (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ
simᴵᵈ = subᴵ {Lkᴵᶜ} {Lkᴵ ⊗ᴵ Advᴵᶜ} {Honᴵᶜ} simJ

idealᴹ : Proc unitᴵ Cᵗ
idealᴹ = 𝒫._∘_ {unitᴵ} {Lkᴵᶜ ⊗ᴵ Honᴵᶜ} {Cᵗ} simᴵᵈ Fcoin

private
  module Iᶜ = CS.CP unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin
  module Iᵁ = Iᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin)
  module Iᵂ = Iᶜ.Walk (CS.unfoldᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin)

  Iᴺ : Proc unitᴵ Cᵗ
  Iᴺ = CS.Nᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin

  stepᴵ = CS.stepᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin

------------------------------------------------------------------------
-- The state map, and the composite's loop at each letter

θᴵ : CSt → JSt × FSt
θᴵ (preᶜ t)       = preʲ t , freshᵏ
θᴵ (midᶜ t b₁ b₂) = midʲ t , heldᵏ (b₁ xor b₂)
θᴵ (postᶜ t b₁)   = endʲ t , doneᵏ

private
  padᴵᵒ : CSt × (Neg unitᴵ ⊎ Pos Cⁱ) → (JSt × FSt) × (Neg unitᴵ ⊎ Pos Cᵗ)
  padᴵᵒ w = θᴵ (proj₁ w) , Sum.map₂ ⊎assocˡ (proj₂ w)

  botᴵ : (sg : JSt) (sf : FSt) (n : LkQ)
       → jStep (sg , inj₂ (inj₁ n)) ≈ₚ botₚ
       → stepᴵ ((sg , sf) , inj₂ (inj₁ (inj₁ n))) ≈ₚ botₚ
  botᴵ sg sf n eq = Iᵂ.R-bot sg sf (inj₁ (inj₁ n)) (bindˣ eq ⟨≈⟩ bot-bind-≈ₚ _)

  downᴵ : (sg : JSt) (sf : FSt) (n : LkQ) (sg′ : JSt) (c : CoinQ)
        → jStep (sg , inj₂ (inj₁ n)) ≈ₚ returnₚ (sg′ , inj₁ c)
        → {D : Dₚ (FSt × (Neg unitᴵ ⊎ Pos (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)))}
        → coinStep (sf , inj₂ (inj₁ c)) ≈ₚ D
        → stepᴵ ((sg , sf) , inj₂ (inj₁ (inj₁ n))) ≈ₚ (D >>=ₚ Iᶜ.resumeF sg′)
  downᴵ sg sf n sg′ c eq =
    Iᵂ.R-down sg sf (inj₁ (inj₁ n)) sg′ (inj₁ c) (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ c) _)

  backᴵ : (sg : JSt) (sf : FSt) (c : CoinR) (sg′ : JSt) (y : Pos (Lkᴵ ⊗ᴵ Advᴵᶜ))
        → jStep (sg , inj₁ c) ≈ₚ returnₚ (sg′ , inj₂ y)
        → Iᶜ.resumeF sg (sf , inj₂ (inj₁ c)) ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ y))
  backᴵ sg sf c sg′ y eq =
    Iᵂ.F-up sg sf (inj₁ c) sg′ (inj₁ y) (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ y) _)

  honᴵ : (sg : JSt) (sf : FSt) (a : CoinA)
       → Iᶜ.resumeF sg (sf , inj₂ (inj₂ a)) ≈ₚ returnₚ ((sg , sf) , inj₂ (inj₂ a))
  honᴵ sg sf a = Iᵂ.F-up sg sf (inj₂ a) sg (inj₂ a) ≈refl

  -- Lookup as an explicit argument: see `Examples.CoinToss.Ideal.Hybrid`.
  hashᴵ : (φ : Tbl → CSt) (ψ : Tbl → JSt) (sf : FSt)
        → ((u : Tbl) → θᴵ (φ u) ≡ (ψ u , sf))
        → ((u : Tbl) (y : Pt) → jStep (ψ u , inj₂ (inj₁ (hashˢ y))) ≈ₚ hashJ u ψ y)
        → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
        → mapₚ padᴵᵒ (hashᶜ t φ x) ≈ₚ stepᴵ ((ψ t , sf) , inj₂ (inj₁ (inj₁ (hashˢ x))))
  hashᴵ φ ψ sf hyp hj t x w eqL =
        lazy-bind _ κ (λ z → returnₚ (padᴵᵒ z))
                  (λ u d → ret≡ (cong (_, inj₂ (inj₁ (inj₁ (digˢ d)))) (hyp u))) t x w eqL
    ⟨≈⟩ ≈sym ( Iᵁ.step-R (ψ t) sf (inj₁ (inj₁ (hashˢ x)))
           ⟨≈⟩ bindˣ ( bindˣ (hj t x)
                   ⟨≈⟩ lazy-bind (λ u d → ψ u , inj₂ (inj₁ (digˢ d))) κ₁ _ (λ _ _ → ≈refl)
                                 t x w eqL)
           ⟨≈⟩ lazy-bind κ₁ κ _ (λ u d → Iᵁ.solve-out (ψ u , sf) (inj₂ (inj₁ (inj₁ (digˢ d)))))
                         t x w eqL )
    where
    κ₁ = λ u d → ψ u , inj₂ (inj₁ (inj₁ (digˢ d)))
    κ  = λ u d → (ψ u , sf) , inj₂ (inj₁ (inj₁ (digˢ d)))

  Outᴵ : Set
  Outᴵ = (JSt × FSt) × (Neg unitᴵ ⊎ Pos Cᵗ)

  shareᴵ : (t : Tbl) (b₁ : Bool)
         → (coinₚ uniform-Bool >>=ₚ λ b₂ → returnₚ {A = Outᴵ}
              ((midʲ t , heldᵏ (b₁ xor b₂)) , inj₂ (inj₁ (inj₂ (shareᴬ b₂)))))
         ≈ₚ (coinₚ uniform-Bool >>=ₚ λ c → returnₚ {A = Outᴵ}
              ((midʲ t , heldᵏ c) , inj₂ (inj₁ (inj₂ (shareᴬ (b₁ xor c))))))
  shareᴵ t false = ≈refl
  shareᴵ t true  = coin-flip uniform-Bool uniform-balanced λ x →
    ret≡ (cong (λ z → (midʲ t , heldᵏ (not x)) , inj₂ (inj₁ (inj₂ (shareᴬ z))))
               (sym (not-involutive x)))

  idlStep : (cs : CSt) (z : Pos unitᴵ ⊎ Neg Cᵗ)
          → mapₚ padᴵᵒ (cStep (cs , Sum.map₂ ⊎assocʳ z)) ≈ₚ stepᴵ (θᴵ cs , z)
  idlStep _ (inj₁ ())
  idlStep _ (inj₂ (inj₁ (inj₂ ())))
  idlStep _ (inj₂ (inj₂ ()))
  idlStep (preᶜ t)       (inj₂ (inj₁ (inj₁ (hashˢ x)))) =
    hashᴵ preᶜ preʲ freshᵏ (λ _ → refl) (λ _ _ → ≈refl) t x _ refl
  idlStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (inj₁ (hashˢ x)))) =
    hashᴵ (λ u → midᶜ u b₁ b₂) midʲ (heldᵏ (b₁ xor b₂)) (λ _ → refl) (λ _ _ → ≈refl)
          t x _ refl
  idlStep (postᶜ t b₁)   (inj₂ (inj₁ (inj₁ (hashˢ x)))) =
    hashᴵ (λ u → postᶜ u b₁) endʲ doneᵏ (λ _ → refl) (λ _ _ → ≈refl) t x _ refl
  idlStep (preᶜ t)       (inj₂ (inj₁ (inj₁ (commitˢ b₁)))) =
        >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ (λ b₂ → >>=ₚ-identityˡ (midᶜ t b₁ b₂ , inj₂ (inj₂ (inj₁ (shareᴬ b₂)))) _)
    ⟨≈⟩ shareᴵ t b₁
    ⟨≈⟩ ≈sym ( downᴵ (preʲ t) freshᵏ (commitˢ b₁) (askʲ t b₁) sampleᵏ ≈refl ≈refl
           ⟨≈⟩ >>=ₚ-assoc (coinₚ uniform-Bool) _ _
           ⟨≈⟩ bindᶠ (λ c → >>=ₚ-identityˡ (heldᵏ c , inj₂ (inj₁ (coinᵏ c))) _
                        ⟨≈⟩ backᴵ (askʲ t b₁) (heldᵏ c) (coinᵏ c) (midʲ t)
                                  (inj₂ (shareᴬ (b₁ xor c))) ≈refl) )
  idlStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (inj₁ (commitˢ b)))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (midʲ t) (heldᵏ (b₁ xor b₂)) (commitˢ b) ≈refl)
  idlStep (postᶜ t b₁)   (inj₂ (inj₁ (inj₁ (commitˢ b)))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (endʲ t) doneᵏ (commitˢ b) ≈refl)
  idlStep (preᶜ t)       (inj₂ (inj₁ (inj₁ openˢ))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (preʲ t) freshᵏ openˢ ≈refl)
  idlStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (inj₁ openˢ))) =
        >>=ₚ-identityˡ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜ (b₁ xor b₂))))) _
    ⟨≈⟩ ≈sym ( downᴵ (midʲ t) (heldᵏ (b₁ xor b₂)) openˢ (endʲ t) deliverᵏ ≈refl ≈refl
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵏ , inj₂ (inj₂ (tossedᶜ (b₁ xor b₂)))) _
           ⟨≈⟩ honᴵ (endʲ t) doneᵏ (tossedᶜ (b₁ xor b₂)) )
  idlStep (postᶜ t b₁)   (inj₂ (inj₁ (inj₁ openˢ))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (endʲ t) doneᵏ openˢ ≈refl)
  idlStep (preᶜ t)       (inj₂ (inj₁ (inj₁ failˢ))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (preʲ t) freshᵏ failˢ ≈refl)
  idlStep (midᶜ t b₁ b₂) (inj₂ (inj₁ (inj₁ failˢ))) =
        >>=ₚ-identityˡ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ abortedᶜ))) _
    ⟨≈⟩ ≈sym ( downᴵ (midʲ t) (heldᵏ (b₁ xor b₂)) failˢ (endʲ t) abortᵏ ≈refl ≈refl
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵏ , inj₂ (inj₂ abortedᶜ)) _
           ⟨≈⟩ honᴵ (endʲ t) doneᵏ abortedᶜ )
  idlStep (postᶜ t b₁)   (inj₂ (inj₁ (inj₁ failˢ))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵ (endʲ t) doneᵏ failˢ ≈refl)

------------------------------------------------------------------------
-- The machine equality

idl-sim : coinᶜ S.≲ Iᴺ
idl-sim = Pw.simFn θᴵ
                (λ x → >>=ₚ-identityˡ (preᶜ []) _
                   ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                          ⟨≈⟩ >>=ₚ-identityˡ (preʲ []) _
                          ⟨≈⟩ >>=ₚ-identityˡ freshᵏ _))
                (λ z → map-map (cStep (proj₁ z , Sum.map₂ ⊎assocʳ (proj₂ z))) _ _
                      ⟨≈⟩ idlStep (proj₁ z) (proj₂ z))

coin-machine : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ idealᴹ
coin-machine = hybrid-eq S.○ᴹ S.≲⇒≈ᴹ idl-sim
          S.○ᴹ CS.eq-∘ᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin

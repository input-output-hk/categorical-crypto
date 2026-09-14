{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop's machine equality: Blum coin-tossing over the ideal `F_com`,
-- run over the concrete resource, IS the joint simulator over the ideal coin.
--
-- `Examples.CoinToss.Ideal.Hybrid` is the other half.  Both sides are ⊕-traces
-- and their loop objects differ — `Lkᴵ ⊗ᴵ Honᴵ` against `Lkᴵᶜ ⊗ᴵ Honᴵᶜ` — so
-- neither simulates the other; `Reach.coinᶜ` is the third machine both
-- simulate out of, which is all an `EqClosure` needs.
--
-- The two simulations differ in exactly one place.  At `commitˢ b₁` the hybrid
-- samples the SHARE and the ideal side samples the COIN, publishing
-- `b₁ xor c`; the two distributions agree only after reindexing along the
-- flip, which is `Dp.Coin.coin-flip`.  Everything else is a `returnₚ`.

open import Data.Bool.Base using (Bool; false; true; not; _xor_)
open import Data.Bool.Properties using (not-involutive)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym)

open import Categories.Category using (Category)
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ; coin-flip; uniform-balanced)
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (Dₚ-DiscreteMonad; 𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; subᴵ′)

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

open Core (𝒱ₚ 0ℓ)

private
  module S  = Pw.S
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The ideal composite

simᴵᵈ : Proc (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ
simᴵᵈ = subᴵ′ {Lkᴵᶜ} {Lkᴵ ⊗ᴵ Advᴵᶜ} {Honᴵᶜ} simJ

idealᴹ : Proc unitᴵ Cᵗ
idealᴹ = 𝒫._∘_ {unitᴵ} {Lkᴵᶜ ⊗ᴵ Honᴵᶜ} {Cᵗ} simᴵᵈ Fcoin

private
  module Iᶜ = CS.CP unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin
  module Iᵁ = Iᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin)

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
  padᴵ : CSt × (Neg unitᴵ ⊎ Pos Cᵗ) → (JSt × FSt) × (Neg unitᴵ ⊎ Pos Cᵗ)
  padᴵ w = θᴵ (proj₁ w) , proj₂ w

  -- …after the bracket the sandwich puts in front of `coinᶜ′`.
  padᴵᵒ : CSt × (Neg unitᴵ ⊎ Pos Cⁱ) → (JSt × FSt) × (Neg unitᴵ ⊎ Pos Cᵗ)
  padᴵᵒ w = θᴵ (proj₁ w) , Sum.map (λ a → a) ⊎assocˡ (proj₂ w)

  -- The simulator answers from its own table, so the composite exits at once.
  upᴵ : (sg : JSt) (sf : FSt) (n : LkQ) (sg′ : JSt) (y : Pos (Lkᴵ ⊗ᴵ Advᴵᶜ))
      → jStep (sg , inj₂ (inj₁ n)) ≈ₚ returnₚ (sg′ , inj₂ y)
      → stepᴵ ((sg , sf) , inj₂ (inj₁ (inj₁ n))) ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ y))
  upᴵ sg sf n sg′ y eq =
        Iᵁ.step-R sg sf (inj₁ (inj₁ n))
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ y) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ (inj₁ y)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg′ , sf) (inj₂ (inj₁ y))

  -- …or it refuses, and the composite refuses with it.
  botᴵ : (sg : JSt) (sf : FSt) (n : LkQ)
       → jStep (sg , inj₂ (inj₁ n)) ≈ₚ botₚ
       → stepᴵ ((sg , sf) , inj₂ (inj₁ (inj₁ n))) ≈ₚ botₚ
  botᴵ sg sf n eq =
        Iᵁ.step-R sg sf (inj₁ (inj₁ n))
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ bot-bind-≈ₚ _)
    ⟨≈⟩ bot-bind-≈ₚ _

  -- …or it calls the coin, which acts.
  downᴵ : (sg : JSt) (sf : FSt) (n : LkQ) (sg′ : JSt) (c : CoinQ)
        → jStep (sg , inj₂ (inj₁ n)) ≈ₚ returnₚ (sg′ , inj₁ c)
        → {D : Dₚ (FSt × (Neg unitᴵ ⊎ Pos (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)))}
        → coinStep (sf , inj₂ (inj₁ c)) ≈ₚ D
        → stepᴵ ((sg , sf) , inj₂ (inj₁ (inj₁ n))) ≈ₚ (D >>=ₚ Iᶜ.resumeF sg′)
  downᴵ sg sf n sg′ c eq eqf =
        Iᵁ.step-R sg sf (inj₁ (inj₁ n))
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ c) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ (inj₁ c)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-B⁻ sg′ sf (inj₁ c)
    ⟨≈⟩ bindˣ eqf

  -- The coin's answer on the leak port re-enters the simulator…
  backᴵ : (sg : JSt) (sf : FSt) (c : CoinR) (sg′ : JSt) (y : Pos (Lkᴵ ⊗ᴵ Advᴵᶜ))
        → jStep (sg , inj₁ c) ≈ₚ returnₚ (sg′ , inj₂ y)
        → Iᶜ.resumeF sg (sf , inj₂ (inj₁ c)) ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ y))
  backᴵ sg sf c sg′ y eq =
        Iᵁ.solve-B⁺ sg sf (inj₁ c)
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ y) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ (inj₁ y)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg′ , sf) (inj₂ (inj₁ y))

  -- …and its answer on the honest port bypasses it.
  honᴵ : (sg : JSt) (sf : FSt) (a : CoinA)
       → Iᶜ.resumeF sg (sf , inj₂ (inj₂ a)) ≈ₚ returnₚ ((sg , sf) , inj₂ (inj₂ a))
  honᴵ sg sf a =
        Iᵁ.solve-B⁺ sg sf (inj₂ a)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₂ (inj₂ a)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg , sf) (inj₂ (inj₂ a))

  -- The scrutinee is an explicit argument: `with` would normalise the goal,
  -- which names the composite's step (`Ideal.Hybrid`'s header measures it).
  hashᴵ : (φ : Tbl → CSt) (ψ : Tbl → JSt) (sf : FSt)
        → ((u : Tbl) → θᴵ (φ u) ≡ (ψ u , sf))
        → ((u : Tbl) (y : Pt) → jStep (ψ u , inj₂ (inj₁ (hashˢ y))) ≈ₚ hashJ u ψ y)
        → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
        → mapₚ padᴵᵒ (hashᶜ t φ x) ≈ₚ stepᴵ ((ψ t , sf) , inj₂ (inj₁ (inj₁ (hashˢ x))))
  hashᴵ φ ψ sf hyp hj t x (just d) eqL =
        map-arg padᴵᵒ (hashᶜ-hit t φ x d eqL)
    ⟨≈⟩ >>=ₚ-identityˡ (φ t , inj₂ (inj₁ (digˢ d))) _
    ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (inj₁ (digˢ d)))) (hyp t))
    ⟨≈⟩ ≈sym (upᴵ (ψ t) sf (hashˢ x) (ψ t) (inj₁ (digˢ d))
                  (hj t x ⟨≈⟩ hashJ-hit t ψ x d eqL))
  hashᴵ φ ψ sf hyp hj t x nothing eqL =
        map-arg padᴵᵒ (hashᶜ-miss t φ x eqL)
    ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
    ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h))) _
                 ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (inj₁ (digˢ h)))) (hyp ((x , h) ∷ t))))
    ⟨≈⟩ ≈sym ( Iᵁ.step-R (ψ t) sf (inj₁ (inj₁ (hashˢ x)))
           ⟨≈⟩ bindˣ ( bindˣ (hj t x ⟨≈⟩ hashJ-miss t ψ x eqL)
                   ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
                   ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                                      (ψ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h))) _))
           ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
           ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                              (ψ ((x , h) ∷ t) , inj₂ (inj₁ (inj₁ (digˢ h)))) _
                        ⟨≈⟩ Iᵁ.solve-out (ψ ((x , h) ∷ t) , sf)
                                         (inj₂ (inj₁ (inj₁ (digˢ h))))) )

  -- The one place the two sides sample differently: the hybrid draws the
  -- SHARE, the ideal side draws the COIN, and `b₁ xor _` carries one to the
  -- other.  At `b₁ = false` the two are the same term.
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
          → mapₚ padᴵᵒ (cStep (cs , Sum.map (λ a → a) ⊎assocʳ z)) ≈ₚ stepᴵ (θᴵ cs , z)
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
idl-sim = S.sim (K.pureᵏ θᴵ) (KP.structural θᴵ)
                (λ r → >>=ₚ-identityˡ (θᴵ r) _
                   ⟨≈⟩ bindˣ (>>=ₚ-identityˡ tt _ ⟨≈⟩ >>=ₚ-identityˡ tt _)
                   ⟨≈⟩ >>=ₚ-identityˡ (tt , tt) _)
                (λ x → >>=ₚ-identityˡ (preᶜ []) _
                   ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                          ⟨≈⟩ >>=ₚ-identityˡ (preʲ []) _
                          ⟨≈⟩ >>=ₚ-identityˡ freshᵏ _))
                (λ z → bindᶠ (Pw.⊗-pureˡ θᴵ)
                   ⟨≈⟩ map-map (cStep (proj₁ z , Sum.map (λ a → a) ⊎assocʳ (proj₂ z))) _ _
                   ⟨≈⟩ idlStep (proj₁ z) (proj₂ z)
                   ⟨≈⟩ ≈sym ( bindˣ (Pw.⊗-pureˡ θᴵ z)
                          ⟨≈⟩ >>=ₚ-identityˡ (θᴵ (proj₁ z) , proj₂ z) _))

-- The two sides agree EXACTLY, so the emulation the UC layer reads off this
-- carries the zero schedule.
coin-machine : 𝒫._≈_ {unitᴵ} {Cᵗ} hybridᴹ idealᴹ
coin-machine = hybrid-eq S.○ᴹ S.≲⇒≈ᴹ idl-sim
          S.○ᴹ CS.eq-∘ᶜ unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ) Cᵗ simᴵᵈ Fcoin

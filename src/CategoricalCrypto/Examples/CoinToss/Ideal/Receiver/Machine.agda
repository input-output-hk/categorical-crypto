{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver hop's agreement: Blum coin-tossing over the ideal
-- `F_com`, run over the concrete resource, runs like the joint simulator over
-- the ideal coin — at every closed strategy, EXACTLY.
--
-- It is a run equality and not an `≈ᴹ`, and that is the content.  The hybrid
-- draws the honest committer's share when the environment starts it; the
-- ideal coin cannot draw then, because its bit would have to be `b₁ xor b₂`
-- at a `b₂` the environment picks afterwards.  So the two sides sample at
-- different activations, and `Machines.Sim`'s equality — whose generator is a
-- state FUNCTION — cannot relate the point mass one side's post-start state
-- is to the mixture the other's is (`docs/coin-toss.md` §5).
--
-- The gap is closed in two moves.  `deferᶜʰ` — the same reachable machine
-- with the draw at `shareᴬʰ` — IS the ideal side as a machine (`idl-simʰ`,
-- the extraction half's `idl-sim` at these ports, with the same single
-- non-structural step: `Dp.Coin.coin-flip`, because `θᴵʰ` sends a state
-- holding `b₁` and `b₂` to the coin holding `b₁ xor b₂`).  And `eagerᶜʰ` runs
-- like `deferᶜʰ` by `GamePlaying.Defer.Run`, which moves a draw across an
-- activation one layer up, where a mixture and a point mass may agree.

open import Data.Bool.Base using (Bool; false; not; true; _xor_)
open import Data.Bool.Properties using (not-involutive; xor-comm; xor-identityʳ)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; sym; trans)

open import Categories.Category using (Category)
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ; coin-flip; coinₚ-const; uniform-balanced)
open import ProbabilisticLogic.Dp.Commutative using (>>=ₚ-swap)
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.GamePlaying.Defer.Run using (DeferStep; run-defer)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (Dₚ-DiscreteMonad; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; subᴵ′)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.UC.QueryBound.Compose.Step as CS

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Machine (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Reach k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Core (𝒱ₚ 0ℓ)

private
  module S  = Pw.S
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The ideal composite

simᴵᵈʰ : Proc (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ
simᴵᵈʰ = subᴵ′ {Lkᴵᶜʰ} {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ} {Honᴵᶜʰ} simJʰ

idealᴹʰ : Proc unitᴵ Cᵗʰ
idealᴹʰ = 𝒫._∘_ {unitᴵ} {Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ} {Cᵗʰ} simᴵᵈʰ Fcoinʰ

private
  module Iᶜ = CS.CP unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ simᴵᵈʰ Fcoinʰ
  module Iᵁ = Iᶜ.Unfolding (CS.unfoldᶜ unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ simᴵᵈʰ Fcoinʰ)

  Iᴺ : Proc unitᴵ Cᵗʰ
  Iᴺ = CS.Nᶜ unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ simᴵᵈʰ Fcoinʰ

  stepᴵ = CS.stepᶜ unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ simᴵᵈʰ Fcoinʰ

------------------------------------------------------------------------
-- The state map, and the composite's loop at each letter

-- The one place the coin's own bit is named: a deferred state holding the
-- committer's `b₁` and the receiver's `b₂` is the coin holding `b₁ xor b₂`.
θᴵʰ : DStʰ → JStʰ × FStʰ
θᴵʰ (preᴰ t)       = preʲʰ t , freshᵏʰ
θᴵʰ (comᴰ t)       = midʲʰ t , waitᵏʰ
θᴵʰ (opnᴰ t b₁ b₂) = endʲʰ t , heldᵏʰ (b₁ xor b₂)
θᴵʰ (endᴰ t _)     = endʲʰ t , doneᵏʰ

private
  -- …after the bracket the sandwich puts in front of `deferᶜʰ′`.
  padᴵᵒʰ : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → (JStʰ × FStʰ) × (Neg unitᴵ ⊎ Pos Cᵗʰ)
  padᴵᵒʰ w = θᴵʰ (proj₁ w) , Sum.map (λ a → a) ⊎assocˡ (proj₂ w)

  -- The simulator answers from its own table, so the composite exits at once.
  upᴵʰ : (sg : JStʰ) (sf : FStʰ) (n : Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)) (sg′ : JStʰ)
         (y : Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))
       → jStepʰ (sg , inj₂ n) ≈ₚ returnₚ (sg′ , inj₂ y)
       → stepᴵ ((sg , sf) , inj₂ (inj₁ n)) ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ y))
  upᴵʰ sg sf n sg′ y eq =
        Iᵁ.step-R sg sf (inj₁ n)
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ y) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ (inj₁ y)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg′ , sf) (inj₂ (inj₁ y))

  -- …or it refuses, and the composite refuses with it.
  botᴵʰ : (sg : JStʰ) (sf : FStʰ) (n : Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))
        → jStepʰ (sg , inj₂ n) ≈ₚ botₚ
        → stepᴵ ((sg , sf) , inj₂ (inj₁ n)) ≈ₚ botₚ
  botᴵʰ sg sf n eq =
        Iᵁ.step-R sg sf (inj₁ n)
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ bot-bind-≈ₚ _)
    ⟨≈⟩ bot-bind-≈ₚ _

  -- …or it calls the coin, which acts.
  downᴵʰ : (sg : JStʰ) (sf : FStʰ) (n : Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)) (sg′ : JStʰ) (c : LeakQʰ)
         → jStepʰ (sg , inj₂ n) ≈ₚ returnₚ (sg′ , inj₁ c)
         → {D : Dₚ (FStʰ × (Neg unitᴵ ⊎ Pos (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)))}
         → coinStepʰ (sf , inj₂ (inj₁ c)) ≈ₚ D
         → stepᴵ ((sg , sf) , inj₂ (inj₁ n)) ≈ₚ (D >>=ₚ Iᶜ.resumeF sg′)
  downᴵʰ sg sf n sg′ c eq eqf =
        Iᵁ.step-R sg sf (inj₁ n)
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ c) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₁ (inj₁ c)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-B⁻ sg′ sf (inj₁ c)
    ⟨≈⟩ bindˣ eqf

  -- An activation of the honest port goes past the simulator to the coin…
  bypᴵʰ : (sg : JStʰ) (sf : FStʰ) (q : CoinQʰ)
          {D : Dₚ (FStʰ × (Neg unitᴵ ⊎ Pos (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)))}
        → coinStepʰ (sf , inj₂ (inj₂ q)) ≈ₚ D
        → stepᴵ ((sg , sf) , inj₂ (inj₂ q)) ≈ₚ (D >>=ₚ Iᶜ.resumeF sg)
  bypᴵʰ sg sf q eqf =
        Iᵁ.step-R sg sf (inj₂ q)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₁ (inj₂ q)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-B⁻ sg sf (inj₂ q)
    ⟨≈⟩ bindˣ eqf

  -- The coin's answer on the leak port re-enters the simulator…
  backᴵʰ : (sg : JStʰ) (sf : FStʰ) (c : LeakRʰ) (sg′ : JStʰ) (y : Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))
         → jStepʰ (sg , inj₁ c) ≈ₚ returnₚ (sg′ , inj₂ y)
         → Iᶜ.resumeF sg (sf , inj₂ (inj₁ c)) ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ y))
  backᴵʰ sg sf c sg′ y eq =
        Iᵁ.solve-B⁺ sg sf (inj₁ c)
    ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ y) _)
    ⟨≈⟩ >>=ₚ-identityˡ (sg′ , inj₂ (inj₁ y)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg′ , sf) (inj₂ (inj₁ y))

  -- …and its answer on the honest port bypasses it.
  honᴵʰ : (sg : JStʰ) (sf : FStʰ) (a : CoinAʰ)
        → Iᶜ.resumeF sg (sf , inj₂ (inj₂ a)) ≈ₚ returnₚ ((sg , sf) , inj₂ (inj₂ a))
  honᴵʰ sg sf a =
        Iᵁ.solve-B⁺ sg sf (inj₂ a)
    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₂ (inj₂ a)) (Iᶜ.resumeG sf)
    ⟨≈⟩ Iᵁ.solve-out (sg , sf) (inj₂ (inj₂ a))

  -- The scrutinee is an explicit argument: `with` would normalise the goal,
  -- which names the composite's step (`Receiver.Hybrid`'s header measures it).
  hashᴵʰ : (φ : Tbl → DStʰ) (ψ : Tbl → JStʰ) (sf : FStʰ)
         → ((u : Tbl) → θᴵʰ (φ u) ≡ (ψ u , sf))
         → ((u : Tbl) (y : Pt) → jStepʰ (ψ u , inj₂ (inj₁ (relayᶠ y))) ≈ₚ hashJʰ u ψ y)
         → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
         → mapₚ padᴵᵒʰ (hashᶜʰ t φ x) ≈ₚ stepᴵ ((ψ t , sf) , inj₂ (inj₁ (inj₁ (relayᶠ x))))
  hashᴵʰ φ ψ sf hyp hj t x (just d) eqL =
        map-arg padᴵᵒʰ (hashᶜʰ-hit t φ x d eqL)
    ⟨≈⟩ >>=ₚ-identityˡ (φ t , inj₂ (inj₁ (digᶠ d))) _
    ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (inj₁ (digᶠ d)))) (hyp t))
    ⟨≈⟩ ≈sym (upᴵʰ (ψ t) sf (inj₁ (relayᶠ x)) (ψ t) (inj₁ (digᶠ d))
                   (hj t x ⟨≈⟩ hashJʰ-hit t ψ x d eqL))
  hashᴵʰ φ ψ sf hyp hj t x nothing eqL =
        map-arg padᴵᵒʰ (hashᶜʰ-miss t φ x eqL)
    ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
    ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))) _
                 ⟨≈⟩ ret≡ (cong (_, inj₂ (inj₁ (inj₁ (digᶠ h)))) (hyp ((x , h) ∷ t))))
    ⟨≈⟩ ≈sym ( Iᵁ.step-R (ψ t) sf (inj₁ (inj₁ (relayᶠ x)))
           ⟨≈⟩ bindˣ ( bindˣ (hj t x ⟨≈⟩ hashJʰ-miss t ψ x eqL)
                   ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
                   ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                                      (ψ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))) _))
           ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ _
           ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                              (ψ ((x , h) ∷ t) , inj₂ (inj₁ (inj₁ (digᶠ h)))) _
                        ⟨≈⟩ Iᵁ.solve-out (ψ ((x , h) ∷ t) , sf)
                                         (inj₂ (inj₁ (inj₁ (digᶠ h))))) )

  -- The one non-structural step: the deferred machine draws the committer's
  -- share and the coin draws the OUTCOME, and `b₁ ↦ b₁ xor b₂` carries one to
  -- the other.  At `b₂ = false` the two are the same term.
  Outᴵʰ : Set
  Outᴵʰ = (JStʰ × FStʰ) × (Neg unitᴵ ⊎ Pos Cᵗʰ)

  shareᴵʰ : (t : Tbl) (b₂ : Bool)
          → (coinₚ uniform-Bool >>=ₚ λ b₁ → returnₚ {A = Outᴵʰ}
               ((endʲʰ t , heldᵏʰ (b₁ xor b₂)) , inj₂ (inj₁ (inj₁ (bitᶠ b₁)))))
          ≈ₚ (coinₚ uniform-Bool >>=ₚ λ c → returnₚ {A = Outᴵʰ}
               ((endʲʰ t , heldᵏʰ c) , inj₂ (inj₁ (inj₁ (bitᶠ (c xor b₂))))))
  shareᴵʰ t false = bindᶠ λ b₁ →
    ret≡ (cong₂ (λ a b → ((endʲʰ t , heldᵏʰ a) , inj₂ (inj₁ (inj₁ (bitᶠ b)))))
                (xor-identityʳ b₁) (sym (xor-identityʳ b₁)))
  shareᴵʰ t true  = coin-flip uniform-Bool uniform-balanced λ x →
    ret≡ (cong₂ (λ a b → ((endʲʰ t , heldᵏʰ a) , inj₂ (inj₁ (inj₁ (bitᶠ b)))))
                (xor-comm x true)
                (sym (trans (xor-comm (not x) true) (not-involutive x))))

  idlStepʰ : (cs : DStʰ) (z : Pos unitᴵ ⊎ Neg Cᵗʰ)
           → mapₚ padᴵᵒʰ (dStep (cs , Sum.map (λ a → a) ⊎assocʳ z)) ≈ₚ stepᴵ (θᴵʰ cs , z)
  idlStepʰ _ (inj₁ ())
  idlStepʰ (preᴰ t)       (inj₂ (inj₁ (inj₁ (relayᶠ x)))) =
    hashᴵʰ preᴰ preʲʰ freshᵏʰ (λ _ → refl) (λ _ _ → ≈refl) t x _ refl
  idlStepʰ (comᴰ t)       (inj₂ (inj₁ (inj₁ (relayᶠ x)))) =
    hashᴵʰ comᴰ midʲʰ waitᵏʰ (λ _ → refl) (λ _ _ → ≈refl) t x _ refl
  idlStepʰ (opnᴰ t b₁ b₂) (inj₂ (inj₁ (inj₁ (relayᶠ x)))) =
    hashᴵʰ (λ u → opnᴰ u b₁ b₂) endʲʰ (heldᵏʰ (b₁ xor b₂)) (λ _ → refl) (λ _ _ → ≈refl)
           t x _ refl
  idlStepʰ (endᴰ t b₁)    (inj₂ (inj₁ (inj₁ (relayᶠ x)))) =
    hashᴵʰ (λ u → endᴰ u b₁) endʲʰ doneᵏʰ (λ _ → refl) (λ _ _ → ≈refl) t x _ refl
  idlStepʰ (preᴰ t)       (inj₂ (inj₁ (inj₂ (shareᴬʰ b₂)))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵʰ (preʲʰ t) freshᵏʰ (inj₂ (shareᴬʰ b₂)) ≈refl)
  idlStepʰ (comᴰ t)       (inj₂ (inj₁ (inj₂ (shareᴬʰ b₂)))) =
        >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ (λ b₁ → >>=ₚ-identityˡ (opnᴰ t b₁ b₂ , inj₂ (inj₁ (bitᶠ b₁))) _)
    ⟨≈⟩ shareᴵʰ t b₂
    ⟨≈⟩ ≈sym ( downᴵʰ (midʲʰ t) waitᵏʰ (inj₂ (shareᴬʰ b₂)) (askʲʰ t b₂) sampleᵏʰ ≈refl ≈refl
           ⟨≈⟩ >>=ₚ-assoc (coinₚ uniform-Bool) _ _
           ⟨≈⟩ bindᶠ (λ c → >>=ₚ-identityˡ (heldᵏʰ c , inj₂ (inj₁ (coinᵏʰ c))) _
                        ⟨≈⟩ backᴵʰ (askʲʰ t b₂) (heldᵏʰ c) (coinᵏʰ c) (endʲʰ t)
                                   (inj₁ (bitᶠ (c xor b₂))) ≈refl) )
  idlStepʰ (opnᴰ t b₁ b₂) (inj₂ (inj₁ (inj₂ (shareᴬʰ b)))) =
    bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (botᴵʰ (endʲʰ t) (heldᵏʰ (b₁ xor b₂)) (inj₂ (shareᴬʰ b)) ≈refl)
  idlStepʰ (endᴰ t b₁)    (inj₂ (inj₁ (inj₂ (shareᴬʰ b)))) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (botᴵʰ (endʲʰ t) doneᵏʰ (inj₂ (shareᴬʰ b)) ≈refl)
  idlStepʰ (preᴰ t)       (inj₂ (inj₂ goᶜ)) =
        >>=ₚ-identityˡ (comᴰ t , inj₂ (inj₁ rcptᶠ)) _
    ⟨≈⟩ ≈sym ( bypᴵʰ (preʲʰ t) freshᵏʰ goᶜ ≈refl
           ⟨≈⟩ >>=ₚ-identityˡ (waitᵏʰ , inj₂ (inj₁ startᵏʰ)) _
           ⟨≈⟩ backᴵʰ (preʲʰ t) waitᵏʰ startᵏʰ (midʲʰ t) (inj₁ rcptᶠ) ≈refl )
  idlStepʰ (comᴰ t)       (inj₂ (inj₂ goᶜ)) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bypᴵʰ (midʲʰ t) waitᵏʰ goᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  idlStepʰ (opnᴰ t b₁ b₂) (inj₂ (inj₂ goᶜ)) =
    bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bypᴵʰ (endʲʰ t) (heldᵏʰ (b₁ xor b₂)) goᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  idlStepʰ (endᴰ t b₁)    (inj₂ (inj₂ goᶜ)) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bypᴵʰ (endʲʰ t) doneᵏʰ goᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  idlStepʰ (preᴰ t)       (inj₂ (inj₂ getᶜ)) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bypᴵʰ (preʲʰ t) freshᵏʰ getᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  idlStepʰ (comᴰ t)       (inj₂ (inj₂ getᶜ)) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bypᴵʰ (midʲʰ t) waitᵏʰ getᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)
  idlStepʰ (opnᴰ t b₁ b₂) (inj₂ (inj₂ getᶜ)) =
        >>=ₚ-identityˡ (endᴰ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))) _
    ⟨≈⟩ ≈sym ( bypᴵʰ (endʲʰ t) (heldᵏʰ (b₁ xor b₂)) getᶜ ≈refl
           ⟨≈⟩ >>=ₚ-identityˡ (doneᵏʰ , inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))) _
           ⟨≈⟩ honᴵʰ (endʲʰ t) doneᵏʰ (tossedᶜʰ (b₁ xor b₂)) )
  idlStepʰ (endᴰ t b₁)    (inj₂ (inj₂ getᶜ)) =
    bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bypᴵʰ (endʲʰ t) doneᵏʰ getᶜ ≈refl ⟨≈⟩ bot-bind-≈ₚ _)

idl-simʰ : deferᶜʰ S.≲ Iᴺ
idl-simʰ = S.sim (K.pureᵏ θᴵʰ) (KP.structural θᴵʰ)
                 (λ r → >>=ₚ-identityˡ (θᴵʰ r) _
                    ⟨≈⟩ bindˣ (>>=ₚ-identityˡ tt _ ⟨≈⟩ >>=ₚ-identityˡ tt _)
                    ⟨≈⟩ >>=ₚ-identityˡ (tt , tt) _)
                 (λ x → >>=ₚ-identityˡ (preᴰ []) _
                    ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                           ⟨≈⟩ >>=ₚ-identityˡ (preʲʰ []) _
                           ⟨≈⟩ >>=ₚ-identityˡ freshᵏʰ _))
                 (λ z → bindᶠ (Pw.⊗-pureˡ θᴵʰ)
                    ⟨≈⟩ map-map (dStep (proj₁ z , Sum.map (λ a → a) ⊎assocʳ (proj₂ z))) _ _
                    ⟨≈⟩ idlStepʰ (proj₁ z) (proj₂ z)
                    ⟨≈⟩ ≈sym ( bindˣ (Pw.⊗-pureˡ θᴵʰ z)
                           ⟨≈⟩ >>=ₚ-identityˡ (θᴵʰ (proj₁ z) , proj₂ z) _))

ideal-eqʰ : 𝒫._≈_ {unitᴵ} {Cᵗʰ} deferᶜʰ idealᴹʰ
ideal-eqʰ = S.≲⇒≈ᴹ idl-simʰ
       S.○ᴹ CS.eq-∘ᶜ unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ) Cᵗʰ simᴵᵈʰ Fcoinʰ

------------------------------------------------------------------------
-- Moving the draw

-- The relation the deferred sampling runs on: a family of eagerly-drawn
-- states, indexed by the secret, against one state that has not drawn.  Only
-- in the committed phase does the family actually vary.
canonʰ : DStʰ → Bool → EStʰ
canonʰ (preᴰ t)       _ = preᴱ t
canonʰ (comᴰ t)       v = comᴱ t v
canonʰ (opnᴰ t b₁ b₂) _ = opnᴱ t b₁ b₂
canonʰ (endᴰ t b₁)    _ = endᴱ t b₁

infix 4 _≋ʰ_

_≋ʰ_ : (Bool → EStʰ) → DStʰ → Set
fs ≋ʰ s = (v : Bool) → fs v ≡ canonʰ s v

private
  μʰ : Dₚ Bool
  μʰ = coinₚ uniform-Bool

  Pointᶜ : (EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
         → (DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool) → Set
  Pointᶜ L L′ = (gs : Bool → EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ))
                (t : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ))
              → (λ v → proj₁ (gs v)) ≋ʰ proj₁ t
              → ((v : Bool) → proj₂ (gs v) ≡ proj₂ t)
              → (μʰ >>=ₚ λ v → L (gs v)) ≈ₚ L′ t

  -- Both sides refuse, and the draw in front of a refusal is invisible.
  botᶜ : (L : EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
         (L′ : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
       → (μʰ >>=ₚ λ _ → botₚ >>=ₚ L) ≈ₚ (botₚ >>=ₚ L′)
  botᶜ L L′ = bindᶠ (λ _ → bot-bind-≈ₚ L)
          ⟨≈⟩ coinₚ-const uniform-Bool botₚ
          ⟨≈⟩ ≈sym (bot-bind-≈ₚ L′)

  -- An oracle query reads no secret, so the two sides agree entry by entry;
  -- on a miss the fresh digest is drawn on both and `>>=ₚ-swap` puts the two
  -- draws in the same order.
  hashCᶜ : (t : Tbl) (φᴱ : Bool → Tbl → EStʰ) (φᴰ : Tbl → DStʰ) (x : Pt)
         → ((u : Tbl) → (λ v → φᴱ v u) ≋ʰ φᴰ u)
         → (L : EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
           (L′ : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
         → Pointᶜ L L′
         → (w : Maybe Dig) → lookupPt t x ≡ w
         → (μʰ >>=ₚ λ v → hashᶜʰ t (φᴱ v) x >>=ₚ L) ≈ₚ (hashᶜʰ t φᴰ x >>=ₚ L′)
  hashCᶜ t φᴱ φᴰ x hyp L L′ pt (just d) eqL =
        bindᶠ (λ v → bindˣ (hashᶜʰ-hit t (φᴱ v) x d eqL)
                 ⟨≈⟩ >>=ₚ-identityˡ (φᴱ v t , inj₂ (inj₁ (digᶠ d))) L)
    ⟨≈⟩ pt (λ v → φᴱ v t , inj₂ (inj₁ (digᶠ d))) (φᴰ t , inj₂ (inj₁ (digᶠ d)))
           (hyp t) (λ _ → refl)
    ⟨≈⟩ ≈sym ( bindˣ (hashᶜʰ-hit t φᴰ x d eqL)
           ⟨≈⟩ >>=ₚ-identityˡ (φᴰ t , inj₂ (inj₁ (digᶠ d))) L′ )
  hashCᶜ t φᴱ φᴰ x hyp L L′ pt nothing eqL =
        bindᶠ (λ v → bindˣ (hashᶜʰ-miss t (φᴱ v) x eqL)
                 ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ L
                 ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                                    (φᴱ v ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))) L))
    ⟨≈⟩ >>=ₚ-swap μʰ (uniformₚ k)
                  (λ v h → L (φᴱ v ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))))
    ⟨≈⟩ bindᶠ (λ h → pt (λ v → φᴱ v ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h)))
                        (φᴰ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h)))
                        (hyp ((x , h) ∷ t)) (λ _ → refl))
    ⟨≈⟩ ≈sym ( bindˣ (hashᶜʰ-miss t φᴰ x eqL)
           ⟨≈⟩ >>=ₚ-assoc (uniformₚ k) _ L′
           ⟨≈⟩ bindᶠ (λ h → >>=ₚ-identityˡ
                              (φᴰ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))) L′) )

  -- One activation, at the two machines' own bracket.
  coreᶜ : (s : DStʰ) (n : Neg Cⁱʰ)
          (L : EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
          (L′ : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → Dₚ Bool)
        → Pointᶜ L L′
        → (μʰ >>=ₚ λ v → eStep (canonʰ s v , inj₂ n) >>=ₚ L) ≈ₚ (dStep (s , inj₂ n) >>=ₚ L′)
  coreᶜ (preᴰ t)       (inj₁ (relayᶠ x)) L L′ pt =
    hashCᶜ t (λ _ → preᴱ) preᴰ x (λ _ _ → refl) L L′ pt _ refl
  coreᶜ (comᴰ t)       (inj₁ (relayᶠ x)) L L′ pt =
    hashCᶜ t (λ v u → comᴱ u v) comᴰ x (λ _ _ → refl) L L′ pt _ refl
  coreᶜ (opnᴰ t b₁ b₂) (inj₁ (relayᶠ x)) L L′ pt =
    hashCᶜ t (λ _ u → opnᴱ u b₁ b₂) (λ u → opnᴰ u b₁ b₂) x (λ _ _ → refl) L L′ pt _ refl
  coreᶜ (endᴰ t b₁)    (inj₁ (relayᶠ x)) L L′ pt =
    hashCᶜ t (λ _ u → endᴱ u b₁) (λ u → endᴰ u b₁) x (λ _ _ → refl) L L′ pt _ refl
  coreᶜ (preᴰ _)       (inj₂ (inj₁ (shareᴬʰ _))) L L′ _ = botᶜ L L′
  coreᶜ (comᴰ t)       (inj₂ (inj₁ (shareᴬʰ b₂))) L L′ pt =
        bindᶠ (λ v → >>=ₚ-identityˡ (opnᴱ t v b₂ , inj₂ (inj₁ (bitᶠ v))) L)
    ⟨≈⟩ bindᶠ (λ v →
          ≈sym (coinₚ-const uniform-Bool (L (opnᴱ t v b₂ , inj₂ (inj₁ (bitᶠ v)))))
            ⟨≈⟩ pt (λ _ → opnᴱ t v b₂ , inj₂ (inj₁ (bitᶠ v)))
                   (opnᴰ t v b₂ , inj₂ (inj₁ (bitᶠ v))) (λ _ → refl) (λ _ → refl))
    ⟨≈⟩ ≈sym ( >>=ₚ-assoc (coinₚ uniform-Bool) _ L′
           ⟨≈⟩ bindᶠ (λ b₁ → >>=ₚ-identityˡ (opnᴰ t b₁ b₂ , inj₂ (inj₁ (bitᶠ b₁))) L′) )
  coreᶜ (opnᴰ _ _ _)   (inj₂ (inj₁ (shareᴬʰ _))) L L′ _ = botᶜ L L′
  coreᶜ (endᴰ _ _)     (inj₂ (inj₁ (shareᴬʰ _))) L L′ _ = botᶜ L L′
  coreᶜ (preᴰ t)       (inj₂ (inj₂ goᶜ)) L L′ pt =
        bindᶠ (λ _ → >>=ₚ-assoc (coinₚ uniform-Bool) _ L
                 ⟨≈⟩ bindᶠ (λ b₁ → >>=ₚ-identityˡ (comᴱ t b₁ , inj₂ (inj₁ rcptᶠ)) L))
    ⟨≈⟩ coinₚ-const uniform-Bool
          (coinₚ uniform-Bool >>=ₚ λ b₁ → L (comᴱ t b₁ , inj₂ (inj₁ rcptᶠ)))
    ⟨≈⟩ pt (λ v → comᴱ t v , inj₂ (inj₁ rcptᶠ)) (comᴰ t , inj₂ (inj₁ rcptᶠ))
           (λ _ → refl) (λ _ → refl)
    ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (comᴰ t , inj₂ (inj₁ rcptᶠ)) L′)
  coreᶜ (comᴰ _)       (inj₂ (inj₂ goᶜ)) L L′ _ = botᶜ L L′
  coreᶜ (opnᴰ _ _ _)   (inj₂ (inj₂ goᶜ)) L L′ _ = botᶜ L L′
  coreᶜ (endᴰ _ _)     (inj₂ (inj₂ goᶜ)) L L′ _ = botᶜ L L′
  coreᶜ (preᴰ _)       (inj₂ (inj₂ getᶜ)) L L′ _ = botᶜ L L′
  coreᶜ (comᴰ _)       (inj₂ (inj₂ getᶜ)) L L′ _ = botᶜ L L′
  coreᶜ (opnᴰ t b₁ b₂) (inj₂ (inj₂ getᶜ)) L L′ pt =
        bindᶠ (λ _ → >>=ₚ-identityˡ
                       (endᴱ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))) L)
    ⟨≈⟩ pt (λ _ → endᴱ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))))
           (endᴰ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))))
           (λ _ → refl) (λ _ → refl)
    ⟨≈⟩ ≈sym (>>=ₚ-identityˡ
                (endᴰ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))) L′)
  coreᶜ (endᴰ _ _)     (inj₂ (inj₂ getᶜ)) L L′ _ = botᶜ L L′

  padᴱʰ : EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → EStʰ × (Neg unitᴵ ⊎ Pos Cᵗʰ)
  padᴱʰ w = proj₁ w , Sum.map (λ a → a) ⊎assocˡ (proj₂ w)

  padᴰʰ : DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ) → DStʰ × (Neg unitᴵ ⊎ Pos Cᵗʰ)
  padᴰʰ w = proj₁ w , Sum.map (λ a → a) ⊎assocˡ (proj₂ w)

  -- The sandwich's relabelling commutes with everything the induction reads:
  -- it leaves the state alone and only renames the answer, so the outcome
  -- hypothesis transports by a `cong`.
  deferStepʰ : DeferStep μʰ (coinₚ-const uniform-Bool) eagerᶜʰ deferᶜʰ _≋ʰ_
  deferStepʰ fs s rel q K K′ pt =
        bindᶠ (λ v → bind-map (eStep (fs v , inj₂ (⊎assocʳ q))) padᴱʰ K)
    ⟨≈⟩ bindᶠ (λ v → ≡⇒≈ₚ (cong (λ z → eStep (z , inj₂ (⊎assocʳ q)) >>=ₚ (K ∘′ padᴱʰ))
                                (rel v)))
    ⟨≈⟩ coreᶜ s (⊎assocʳ q) (K ∘′ padᴱʰ) (K′ ∘′ padᴰʰ) pt′
    ⟨≈⟩ ≈sym (bind-map (dStep (s , inj₂ (⊎assocʳ q))) padᴰʰ K′)
    where
    pt′ : Pointᶜ (K ∘′ padᴱʰ) (K′ ∘′ padᴰʰ)
    pt′ gs t rel′ eq = pt (λ v → padᴱʰ (gs v)) (padᴰʰ t) rel′
                          (λ v → cong (Sum.map (λ a → a) ⊎assocˡ) (eq v))

defer-runʰ : (d : Strat (Neg Cᵗʰ) (Pos Cᵗʰ)) → runᴹ eagerᶜʰ d ≈ₚ runᴹ deferᶜʰ d
defer-runʰ = run-defer μʰ (coinₚ-const uniform-Bool) eagerᶜʰ deferᶜʰ _≋ʰ_ deferStepʰ
                       (preᴱ []) (preᴰ []) (λ _ → refl) ≈refl ≈refl

------------------------------------------------------------------------
-- The agreement

-- Exact, and at every closed strategy — so the emulation the UC layer reads
-- off it pays only what carrying a run-level bound into a CONTEXT costs
-- (`Receiver.UC`).
coin-runʰ : (d : Strat (Neg Cᵗʰ) (Pos Cᵗʰ)) → runᴹ hybridᴹʰ d ≈ₚ runᴹ idealᴹʰ d
coin-runʰ d = runᴹ-resp-≈ᴹ hybrid-eqʰ d ⟨≈⟩ defer-runʰ d ⟨≈⟩ runᴹ-resp-≈ᴹ ideal-eqʰ d

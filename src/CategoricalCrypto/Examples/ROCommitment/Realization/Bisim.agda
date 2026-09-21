{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed real system and the closed real GAME, letter for letter.
--
-- The machines and the games speak different alphabets: `Game.Q` is
-- `Neg (Advᴵ ⊗ᴵ Honᴵ)` renamed, and `Game.R` is `Pos (Advᴵ ⊗ᴵ Honᴵ)` plus
-- `idleR`, which is precisely the answer the game gives where the machine
-- diverges.  `deadR` names those activations, `prune` cuts them out of the
-- game, and the relabelling is then a bijection on asks and a section on
-- answers — which is what `GamePlaying.Partial.runWith⊥-bisimʳ` consumes.
--
-- The IDEAL half is not here and cannot be: see §"Where the ideal leg stops".

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (head) renaming (_∷_ to _∷ᵛ_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no; ⌊_⌋)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp

open import CategoricalCrypto.GamePlaying using (cond)
open import CategoricalCrypto.GamePlaying.Partial using (StepBisim⊥ʳ; prune; runWith⊥-bisimʳ)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction using (runWith⊥)
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Protocol.Machine.Raw using (ansᴹ)
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mapStrat; mapStrat)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Realization.Bisim (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Game k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k using (fetchT; fetchT-cong)
open import CategoricalCrypto.Examples.ROCommitment.Realization.Machine k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Transport k using (resK; resKᵀ; resKᵀ-fetchT)

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The alphabets

-- The corrupted committer's port IS the game's question alphabet.
toQ : Neg (Advᴵ ⊗ᴵ Honᴵ) → Q
toQ (inj₁ (queryᴬ x))  = askQ x
toQ (inj₁ (commitᴬ c)) = comQ c
toQ (inj₁ (openᴬ b r)) = opnQ b r

fromQ : Q → Neg (Advᴵ ⊗ᴵ Honᴵ)
fromQ (askQ x)   = inj₁ (queryᴬ x)
fromQ (comQ c)   = inj₁ (commitᴬ c)
fromQ (opnQ b r) = inj₁ (openᴬ b r)

toQ-fromQ : (q : Q) → toQ (fromQ q) ≡ q
toQ-fromQ (askQ _)   = refl
toQ-fromQ (comQ _)   = refl
toQ-fromQ (opnQ _ _) = refl

fromQ-toQ : (q : Neg (Advᴵ ⊗ᴵ Honᴵ)) → fromQ (toQ q) ≡ q
fromQ-toQ (inj₁ (queryᴬ _))  = refl
fromQ-toQ (inj₁ (commitᴬ _)) = refl
fromQ-toQ (inj₁ (openᴬ _ _)) = refl

-- …and its answers embed in the game's, `idleR` excepted: the game idles
-- exactly where the machine has no behaviour at all.
toR : Pos (Advᴵ ⊗ᴵ Honᴵ) → R
toR (inj₁ (ansᴬ d))    = ansR d
toR (inj₂ rcptᴴ)       = rcptR
toR (inj₂ (openedᴴ b)) = outR b
toR (inj₂ refusedᴴ)    = failR

-- A section of `toR`; its value at `idleR` is arbitrary, and no pruned
-- activation reaches it.
fromR : R → Pos (Advᴵ ⊗ᴵ Honᴵ)
fromR (ansR d)  = inj₁ (ansᴬ d)
fromR rcptR     = inj₂ rcptᴴ
fromR (outR b)  = inj₂ (openedᴴ b)
fromR failR     = inj₂ refusedᴴ
fromR idleR     = inj₂ refusedᴴ

fromR-toR : (c : Pos (Advᴵ ⊗ᴵ Honᴵ)) → fromR (toR c) ≡ c
fromR-toR (inj₁ (ansᴬ _))    = refl
fromR-toR (inj₂ rcptᴴ)       = refl
fromR-toR (inj₂ (openedᴴ _)) = refl
fromR-toR (inj₂ refusedᴴ)    = refl

-- The receiver's verdict and the game's opening rule are the same letter.
verdict-realOpen : (c : Dig) (b : Bool) (d : Dig)
                 → inj₂ (verdict b ⌊ d ≟ c ⌋) ≡ fromR (realOpen c b d)
verdict-realOpen c b d with d ≟ c
... | yes _ = refl
... | no  _ = refl

------------------------------------------------------------------------
-- The activations the machine refuses

-- A second commitment, and an opening before one: the two clauses where
-- `realStep` is `botₚ` and where `Game.comR`/`opnR` answer `idleR`.
deadR : StR → Q → Bool
deadR _            (askQ _)   = false
deadR (_ , nothing)  (comQ _)   = false
deadR (_ , just _)   (comQ _)   = true
deadR (_ , nothing)  (opnQ _ _) = true
deadR (_ , just _)   (opnQ _ _) = false

respR⊥ : StR → Q → Dist⊥ (StR × R)
respR⊥ = prune deadR respR

------------------------------------------------------------------------
-- Reading one activation of the closed real machine

private
  Stᴿ : Set
  Stᴿ = RSt × RState

  Aᴿ : Set
  Aᴿ = ⊥ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)

  Xᴿ : Set
  Xᴿ = Neg Resᴵ ⊎ Pos Resᴵ

  outᴳ : Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ) → Aᴿ ⊎ Xᴿ
  outᴳ = outG real resource Kʳ Kᵒ real-settles res-settles

  exitᴿ : ℕ → Stᴿ × (Aᴿ ⊎ Xᴿ) → Dist⊥ (Stᴿ × Aᴿ)
  exitᴿ = exit∘ real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ

  -- The trace's own answer alphabet keeps the empty domain summand in front.
  lift⊥ : (Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ) → Stᴿ × Aᴿ → ℚ
  lift⊥ F (s , inj₂ p) = F (s , p)

  -- What the loop does with the receiver's emission, `j` rounds from the end.
  loopᴿ : ℕ → RState → (Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ)
        → RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) → ℚ
  loopᴿ j sf F r = E⊥ (exitᴿ j ((proj₁ r , sf) , outᴳ (proj₂ r))) (lift⊥ F)

  -- The letter enters the dispatch and the receiver acts.
  enterᴿ : (sg : RSt) (sf : RState) (q : Neg (Advᴵ ⊗ᴵ Honᴵ))
           (F : Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ)
         → E⊥ (Kᴿ (sg , sf) q) F ≡ E⊥ (Kʳ sg (inj₂ q)) (loopᴿ 2 sf F)
  enterᴿ sg sf q F =
    trans (Kᶜˡ-read real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                    (sg , sf) q F (lift⊥ F) (λ _ _ → refl))
          (trans (K∘-enter real resource Kʳ Kᵒ real-settles res-settles
                           rankᴿ rankedᴿ 2 boundᴿ ((sg , sf) , inj₂ q) (lift⊥ F))
                 (dispatch-g real resource Kʳ Kᵒ real-settles res-settles
                             sg sf (inj₂ q) (λ w → E⊥ (exitᴿ 2 w) (lift⊥ F))))

  outᶠᴿ : ⊥ ⊎ Pos Resᴵ → Aᴿ ⊎ Xᴿ
  outᶠᴿ = outF real resource Kʳ Kᵒ real-settles res-settles

  -- What the receiver makes of a digest, and the loop of its reaction.
  digestᴿ : RSt → RState → (Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ) → Dig → ℚ
  digestᴿ sg sf F d = E⊥ (Kʳ sg (inj₁ (digᴿ d))) (loopᴿ 0 sf F)

  -- One oracle round trip: the receiver's query goes down, the table answers,
  -- and the receiver's reaction to the digest leaves the loop.
  oracleᴿ : (sg : RSt) (t : Tbl) (mb : Maybe Bool) (x : Pt)
            (F : Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ)
          → E⊥ (exitᴿ 2 ((sg , t , mb) , outᴳ (inj₁ (hashᴿ x)))) (lift⊥ F)
            ≡ E (fetchT (_, mb) t x) (λ u → digestᴿ sg (proj₁ u) F (proj₂ u))
  oracleᴿ sg t mb x F =
    trans (exit-loop real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                     1 (sg , t , mb) (inj₁ (hashᴿ x)) (lift⊥ F))
   (trans (dispatch-f real resource Kʳ Kᵒ real-settles res-settles
                      sg (t , mb) (inj₂ (hashᴿ x)) (λ w → E⊥ (exitᴿ 1 w) (lift⊥ F)))
   (trans (E⊥-map ansᴹ (resK (t , mb) (hashᴿ x))
                  (λ r → E⊥ (exitᴿ 1 ((sg , proj₁ r) , outᶠᴿ (proj₂ r))) (lift⊥ F)))
   (trans (Eⱼ (resKᵀ (t , mb) x) step₁)
   (trans (resKᵀ-fetchT (t , mb) x step₁)
   (trans (E-bind (fetchT (_, mb) t x) (λ u → return-ℚ (proj₁ u , digᴿ (proj₂ u))) step₁)
          (lookupᴰℚ-cong-P (entries (fetchT (_, mb) t x)) λ u →
            trans (lookupᴰℚ-return (proj₁ u , digᴿ (proj₂ u)) step₁)
           (trans (exit-loop real resource Kʳ Kᵒ real-settles res-settles
                             rankᴿ rankedᴿ 2 boundᴿ
                             0 (sg , proj₁ u) (inj₂ (digᴿ (proj₂ u))) (lift⊥ F))
                  (dispatch-g real resource Kʳ Kᵒ real-settles res-settles
                              sg (proj₁ u) (inj₁ (digᴿ (proj₂ u)))
                              (λ w → E⊥ (exitᴿ 0 w) (lift⊥ F))))))))))
    where
    step₁ : RState × Pos Resᴵ → ℚ
    step₁ p = E⊥ (exitᴿ 1 ((sg , proj₁ p) , outᶠᴿ (inj₂ (proj₂ p)))) (lift⊥ F)

  digest-relay : (m : Maybe Dig) (sf : RState) (F : Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ) (d : Dig)
               → digestᴿ (relayᴿ m) sf F d ≡ F ((waitᴿ m , sf) , inj₁ (ansᴬ d))
  digest-relay m sf F d =
    trans (E⊥-return (waitᴿ m , inj₂ (inj₁ (ansᴬ d))) (loopᴿ 0 sf F))
          (exit-out real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                    0 (waitᴿ m , sf) (inj₂ (inj₁ (ansᴬ d))) (lift⊥ F))

  digest-check : (c : Dig) (b : Bool) (sf : RState) (F : Stᴿ × Pos (Advᴵ ⊗ᴵ Honᴵ) → ℚ) (d : Dig)
               → digestᴿ (checkᴿ c b) sf F d
                 ≡ F ((waitᴿ (just c) , sf) , inj₂ (verdict b ⌊ d ≟ c ⌋))
  digest-check c b sf F d =
    trans (E⊥-return (waitᴿ (just c) , inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋))) (loopᴿ 0 sf F))
          (exit-out real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                    0 (waitᴿ (just c) , sf) (inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋))) (lift⊥ F))

  -- …and the same three activations at the pruned game.
  gameᴬ : (t : Tbl) (m : Maybe Dig) (x : Pt) (F′ : StR × R → ℚ)
        → E⊥ (respR⊥ (t , m) (askQ x)) F′
          ≡ E (fetchT (_, m) t x) (λ u → F′ (proj₁ u , ansR (proj₂ u)))
  gameᴬ t m x F′ =
    trans (Eⱼ (askX (t , m) x) F′)
   (trans (E-bind (fetchT (_, m) t x) (λ u → return-ℚ (proj₁ u , ansR (proj₂ u))) F′)
          (lookupᴰℚ-cong-P (entries (fetchT (_, m) t x)) λ u →
            lookupᴰℚ-return (proj₁ u , ansR (proj₂ u)) F′))

  gameᶜ : (t : Tbl) (c : Dig) (F′ : StR × R → ℚ)
        → E⊥ (respR⊥ (t , nothing) (comQ c)) F′ ≡ F′ ((t , just c) , rcptR)
  gameᶜ t c F′ =
    trans (Eⱼ (comR (t , nothing) c) F′) (lookupᴰℚ-return ((t , just c) , rcptR) F′)

  gameᴼ : (t : Tbl) (c : Dig) (b : Bool) (r : Dig) (F′ : StR × R → ℚ)
        → E⊥ (respR⊥ (t , just c) (opnQ b r)) F′
          ≡ E (fetchT (_, just c) t (b ∷ᵛ r)) (λ u → F′ (proj₁ u , realOpen c b (proj₂ u)))
  gameᴼ t c b r F′ =
    trans (Eⱼ (opnR (t , just c) b r) F′)
   (trans (E-bind (fetchT (_, just c) t (b ∷ᵛ r))
                  (λ u → return-ℚ (proj₁ u , realOpen c b (proj₂ u))) F′)
          (lookupᴰℚ-cong-P (entries (fetchT (_, just c) t (b ∷ᵛ r))) λ u →
            lookupᴰℚ-return (proj₁ u , realOpen c b (proj₂ u)) F′))

  -- An activation neither side serves scores nothing on either.
  refused : {A B : Set} (P : A → ℚ) (P′ : B → ℚ)
          → E⊥ (return-ℚ {A = Maybe A} nothing) P ≡ E⊥ (return-ℚ {A = Maybe B} nothing) P′
  refused P P′ = trans (lookupᴰℚ-return nothing (maybeℚ P))
                       (sym (lookupᴰℚ-return nothing (maybeℚ P′)))

------------------------------------------------------------------------
-- The real marginal: the closed machine IS the pruned real game

-- Only a resting receiver over an untouched cell is related: the composite
-- solves its loop inside one activation, and `real` never drives the cell.
_≋ᴿ_ : Stᴿ → StR → Set
(waitᴿ m , t , nothing) ≋ᴿ u = (t , m) ≡ u
(waitᴿ _ , _ , just _)  ≋ᴿ _ = ⊥
(relayᴿ _ , _)          ≋ᴿ _ = ⊥
(checkᴿ _ _ , _)        ≋ᴿ _ = ⊥

bisimᴿ : StepBisim⊥ʳ toQ fromR Kᴿ respR⊥ _≋ᴿ_
bisimᴿ (waitᴿ m , t , nothing) _ refl (inj₁ (queryᴬ x)) F F′ hF =
  trans (enterᴿ (waitᴿ m) (t , nothing) (inj₁ (queryᴬ x)) F)
 (trans (E⊥-return (relayᴿ m , inj₁ (hashᴿ x)) (loopᴿ 2 (t , nothing) F))
 (trans (oracleᴿ (relayᴿ m) t nothing x F)
 (trans (fetchT-cong (_, nothing) (_, m) t x
           (λ u → digestᴿ (relayᴿ m) (proj₁ u) F (proj₂ u))
           (λ u → F′ (proj₁ u , ansR (proj₂ u)))
           (λ v d → trans (digest-relay m (v , nothing) F d) (hF _ _ refl refl)))
        (sym (gameᴬ t m x F′)))))
bisimᴿ (waitᴿ nothing , t , nothing) _ refl (inj₁ (commitᴬ c)) F F′ hF =
  trans (enterᴿ (waitᴿ nothing) (t , nothing) (inj₁ (commitᴬ c)) F)
 (trans (E⊥-return (waitᴿ (just c) , inj₂ (inj₂ rcptᴴ)) (loopᴿ 2 (t , nothing) F))
 (trans (exit-out real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                  2 (waitᴿ (just c) , t , nothing) (inj₂ (inj₂ rcptᴴ)) (lift⊥ F))
 (trans (hF _ _ refl refl) (sym (gameᶜ t c F′)))))
bisimᴿ (waitᴿ (just c′) , t , nothing) _ refl (inj₁ (commitᴬ c)) F F′ hF =
  trans (enterᴿ (waitᴿ (just c′)) (t , nothing) (inj₁ (commitᴬ c)) F) (refused (loopᴿ 2 (t , nothing) F) F′)
bisimᴿ (waitᴿ (just c) , t , nothing) _ refl (inj₁ (openᴬ b r)) F F′ hF =
  trans (enterᴿ (waitᴿ (just c)) (t , nothing) (inj₁ (openᴬ b r)) F)
 (trans (E⊥-return (checkᴿ c b , inj₁ (hashᴿ (b ∷ᵛ r))) (loopᴿ 2 (t , nothing) F))
 (trans (oracleᴿ (checkᴿ c b) t nothing (b ∷ᵛ r) F)
 (trans (fetchT-cong (_, nothing) (_, just c) t (b ∷ᵛ r)
           (λ u → digestᴿ (checkᴿ c b) (proj₁ u) F (proj₂ u))
           (λ u → F′ (proj₁ u , realOpen c b (proj₂ u)))
           (λ v d → trans (digest-check c b (v , nothing) F d)
                          (hF _ _ refl (verdict-realOpen c b d))))
        (sym (gameᴼ t c b r F′)))))
bisimᴿ (waitᴿ nothing , t , nothing) _ refl (inj₁ (openᴬ b r)) F F′ hF =
  trans (enterᴿ (waitᴿ nothing) (t , nothing) (inj₁ (openᴬ b r)) F) (refused (loopᴿ 2 (t , nothing) F) F′)
bisimᴿ (waitᴿ _ , _ , just _)  _ () _
bisimᴿ (relayᴿ _ , _)          _ () _
bisimᴿ (checkᴿ _ _ , _)        _ () _

------------------------------------------------------------------------
-- Where the ideal leg stops

-- `Examples.ROCommitment.simulator` records EVERY answer it relays, including
-- one the oracle served from its table, so its log is not the oracle's table
-- and `Extraction`'s header claim fails on it.  `Game.respI` extracts from the
-- table (`Game.comI`), so the two are not bisimilar and no relation can make
-- them so: at a repeated query the machine's extraction is `false` where the
-- game's is the committed bit, and the game's bad event — a duplicate in the
-- ORACLE's answer log — has not fired.
sim-log-repeat : (x : Pt) (h : Dig) (L : Tbl) (m : Maybe (Dig × Bool))
               → step simulator (relayˢ x ((x , h) ∷ L) m , inj₁ (digˢ h))
                 ≈ₚ returnₚ (waitˢ ((x , h) ∷ (x , h) ∷ L) m , inj₂ (ansᴬ h))
sim-log-repeat _ _ _ _ = ≈ₚ-refl _

private
  pre-hit : (c : Dig) (x : Pt) (L : Tbl) → preimages c ((x , c) ∷ L) ≡ x ∷ preimages c L
  pre-hit c x L with c ≟ c
  ... | yes _  = refl
  ... | no  ne = ⊥-elim (ne refl)

extract-relog : (x : Pt) (h : Dig) → extract h ((x , h) ∷ (x , h) ∷ []) ≡ false
extract-relog x h =
  cong pick (trans (pre-hit h x ((x , h) ∷ [])) (cong (x ∷_) (pre-hit h x [])))

extract-table : (x : Pt) (h : Dig) → extract h ((x , h) ∷ []) ≡ head x
extract-table x h = cong pick (pre-hit h x [])

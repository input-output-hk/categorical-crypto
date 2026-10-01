{-# OPTIONS --safe --without-K --guardedness #-}

-- The strategy-to-contexts lift for state events: a bound on the flag read at
-- every `flagStrat d` with `asks≤ q d` bounds `stateRead` at every context `q`
-- admits — at the SAME cap, with no slack.
--
-- The closed flagged context is the flag reader over the closed test
-- (`flag-slide`), and it is certified by hand (`FlagCert`) at the test's own
-- count plus ONE: that unit is the flag ask, a real query of the extracted
-- strategy.  The certificate's emission tree is the test's own, so every
-- extracted strategy is `FlagShaped` at the test's count: `B`-asks, then at
-- most one flag ask, then only coins and a verdict the flag covers.  Such a
-- strategy's run of `M ▷ P` is dominated by `flagStrat` of its `B`-part
-- (`shaped-run`), which is where the premise applies.  A strategy that reads
-- the flag earlier and then continues would NOT be dominated: completed-run
-- hits are not prefix hits.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Dominated
open import CategoricalCrypto.UC.Machine.Grading
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Slide
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Laws

import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Utilities as MU
import CategoricalCrypto.UC.Seam.Extract as Ext

module CategoricalCrypto.UC.Machine.StateEvent.Lift where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open MR 𝔾.monoidal
open MU.Shorthands 𝔾.monoidal using () renaming (α⇐ to α⇐ᴳ)

------------------------------------------------------------------------
-- Closing the context

-- The closure crosses the flag reader: the context closed at `B ⊗ᴵ Ωᴵ` is
-- the reader over the test closed at `B`.
flag-slide : (Y B : Iface) (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
           → 𝒫._≈_ (Kctx (flagReader B Y E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m)
                   (flagReadᴹ 𝒫.∘ subᴵ (Kctx (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m))
flag-slide Y B E m = begin
  (flagReader B Y E 𝒫.∘ T₁ᴵ Y λᴵ⇒) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))
    ≈⟨ 𝒫.assoc ⟩
  flagReader B Y E 𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇒ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐)))
    ≈⟨ refl⟩∘⟨ bottom ⟩
  (flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ a⇐ᴵ)) 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)
    ≈⟨ 𝒫.assoc ○ (refl⟩∘⟨ 𝒫.assoc) ⟩
  flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ core) ⟩
  flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ subᴵ (subᴵ w 𝒫.∘ λᴵ⇐))
    ≈˘⟨ refl⟩∘⟨ sub-∘ E (subᴵ w 𝒫.∘ λᴵ⇐) ⟩
  flagReadᴹ 𝒫.∘ subᴵ (E 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐))
    ≈˘⟨ refl⟩∘⟨ sub-resp-≈ (𝒫.assoc ○ (refl⟩∘⟨ bottom)) ⟩
  flagReadᴹ 𝒫.∘ subᴵ ((E 𝒫.∘ T₁ᴵ Y λᴵ⇒) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))) ∎
  where
  w : Proc unitᴵ Y
  w = ρᴵ⇒ 𝒫.∘ m

  bottom : {X : Iface} → 𝒫._≈_ {X} {Y ⊗ᴵ X}
             (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇒ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))) (subᴵ w 𝒫.∘ λᴵ⇐)
  bottom = (refl⟩∘⟨ 𝒫.sym-assoc) ○ 𝒫.sym-assoc ○ (ρ-tri-sub m ⟩∘⟨refl)

  a⇐-sub : 𝒫._≈_ (a⇐ᴵ 𝒫.∘ subᴵ w) (subᴵ (subᴵ w) 𝒫.∘ a⇐ᴵ)
  a⇐-sub = begin
    a⇐ᴵ 𝒫.∘ subᴵ w
      ≈⟨ 𝒫.∘-resp-≈ a⇐-α⇐ (sub-⊗₁ w) ⟩
    α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w 𝒫.id
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ 𝔾.⊗.identity) ⟩
    α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w (𝔾._⊗₁_ 𝒫.id 𝒫.id)
      ≈⟨ 𝔾.assoc-commute-to ⟩
    𝔾._⊗₁_ (𝔾._⊗₁_ w 𝒫.id) 𝒫.id 𝒫.∘ α⇐ᴳ
      ≈˘⟨ 𝒫.∘-resp-≈ (sub-⊗₁ (subᴵ w) ○ (sub-⊗₁ w ⟩⊗⟨refl)) a⇐-α⇐ ⟩
    subᴵ (subᴵ w) 𝒫.∘ a⇐ᴵ ∎

  core : 𝒫._≈_ (a⇐ᴵ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)) (subᴵ (subᴵ w 𝒫.∘ λᴵ⇐))
  core = 𝒫.sym-assoc ○ (a⇐-sub ⟩∘⟨refl) ○ 𝒫.assoc ○ (refl⟩∘⟨ λ-tri)
       ○ ⟺ (sub-∘ (subᴵ w) λᴵ⇐)

stateRead-closed : {B : Iface} (Y : Iface) (M : Proc unitᴵ B) (P : StateTest M)
                   (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
                 → stateRead Y M P E m
                   ≈ₚ ⟦ (flagReadᴹ 𝒫.∘ subᴵ (Kctx (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m)) 𝒫.∘ (M ▷ P) ⟧ᴼ
stateRead-closed {B} Y M P E m =
    ctxRun-conj (flagReader B Y E) m (M ▷ P)
  ⟨≈⟩ ctxRun-slide (flagReader B Y E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m (M ▷ P)
  ⟨≈⟩ runᴹ-resp-≈ᴹ (𝒫.∘-resp-≈ˡ (flag-slide Y B E m)) (ask tt out)

------------------------------------------------------------------------
-- Flag-shaped strategies

-- No ask, and every verdict is covered by `b`.
Final : {Q R : Set} → Bool → Strat Q R → Set
Final b (out v)    = v ≡ true → b ≡ true
Final b (ask _ _)  = ⊥
Final b (coin _ k) = (c : Bool) → Final b (k c)

module _ {Q R : Set} where

  -- At most `n` asks on `Q`, then at most one flag ask, whose answer covers
  -- what follows; an answer off the protocol is unconstrained.
  FlagShaped : ℕ → Strat (Q ⊎ ⊤) (R ⊎ Bool) → Set
  FlagShaped n       (out v)          = v ≡ false
  FlagShaped n       (coin _ k)       = (c : Bool) → FlagShaped n (k c)
  FlagShaped n       (ask (inj₂ _) k) = (b : Bool) → Final b (k (inj₂ b))
  FlagShaped zero    (ask (inj₁ _) _) = ⊥
  FlagShaped (suc n) (ask (inj₁ _) k) = (r : R) → FlagShaped n (k (inj₁ r))

  flagShaped-mono : {n m : ℕ} → n ℕ.≤ m → (d : Strat (Q ⊎ ⊤) (R ⊎ Bool))
                  → FlagShaped n d → FlagShaped m d
  flagShaped-mono le       (out _)          h = h
  flagShaped-mono le       (coin _ k)       h = λ c → flagShaped-mono le (k c) (h c)
  flagShaped-mono (s≤s le) (ask (inj₁ _) k) h = λ r → flagShaped-mono le (k (inj₁ r)) (h r)
  flagShaped-mono le       (ask (inj₂ _) k) h = h

  -- The `Q`-part: `flagStrat`'s left inverse on flag-shaped strategies, up to
  -- the verdicts the flag replaces.
  unflagStrat : Strat (Q ⊎ ⊤) (R ⊎ Bool) → Strat Q R
  unflagStrat (out v)          = out v
  unflagStrat (ask (inj₁ q) k) = ask q (unflagStrat ∘ k ∘ inj₁)
  unflagStrat (ask (inj₂ _) _) = out false
  unflagStrat (coin μ k)       = coin μ (unflagStrat ∘ k)

  asks≤-unflag : (n : ℕ) (d : Strat (Q ⊎ ⊤) (R ⊎ Bool)) → FlagShaped n d
               → asks≤ n (unflagStrat d)
  asks≤-unflag n       (out _)          h = tt
  asks≤-unflag n       (coin _ k)       h = λ c → asks≤-unflag n (k c) (h c)
  asks≤-unflag (suc n) (ask (inj₁ _) k) h = λ r → asks≤-unflag n (k (inj₁ r)) (h r)
  asks≤-unflag n       (ask (inj₂ _) _) h = tt

module _ {B : Iface} (M : Proc unitᴵ B) (P : StateTest M) where

  private
    u = M ▷ P
    Qᵗ = indᵇ true
    nnQ = indᵇ-nn true

    final-run : (b : Bool) (s : MC.St u) (e : Strat (Neg B ⊎ ⊤) (Pos B ⊎ Bool))
              → Final b e → (j : ℕ) → cum j (runᴹFrom u s e) Qᵗ ℚ.≤ Qᵗ b
    final-run b s (out v)    h j = ≤-trans (returnₚ-cum-≤ j v Qᵗ nnQ) (indᵇ-cover h)
    final-run b s (coin μ k) h j =
      cum-bindʳ j (coinₚ μ) _ Qᵗ nnQ (Qᵗ b) (nnQ b) λ c → final-run b s (k c) (h c) j

  -- A flag-shaped strategy's run is dominated by `flagStrat` of its `B`-part.
  shaped-run : (n : ℕ) (s : MC.St u) (d : Strat (Neg B ⊎ ⊤) (Pos B ⊎ Bool)) → FlagShaped n d
             → Cofinal Qᵗ Qᵗ (runᴹFrom u s d) (runᴹFrom u s (flagStrat (unflagStrat d)))
  shaped-run n s (out v) refl j =
    0 , ≤-trans (returnₚ-cum-≤ j false Qᵗ nnQ) (≤-reflexive (indᵇ-not true))
  shaped-run n s (coin μ k) h =
    cofinal-bind Qᵗ nnQ (coinₚ μ) _ _ λ c → shaped-run n s (k c) (h c)
  shaped-run (suc n) (s , f) (ask (inj₁ q) k) h =
    cofinal-trans _ _ _ (≈ₚ⇒cofinal Qᵗ nnQ (bind-map (MC.step M (s , inj₂ q)) (sample M P f) _))
      (cofinal-trans _ _ _ (cofinal-bind Qᵗ nnQ (MC.step M (s , inj₂ q)) _ _ answered)
                           (≈ₚ⇒cofinal Qᵗ nnQ (≈sym (bind-map (MC.step M (s , inj₂ q)) (sample M P f) _))))
    where
    answered : (r : MC.St M × (⊥ ⊎ Pos B))
             → Cofinal Qᵗ Qᵗ (resumeᴹ u (λ m′ x → runᴹFrom u m′ (k x)) (sample M P f r))
                             (resumeᴹ u (λ m′ x → runᴹFrom u m′
                                           ([ flagStrat ∘ (unflagStrat ∘ k ∘ inj₁) , (λ _ → out false) ] x))
                                        (sample M P f r))
    answered (_  , inj₁ ())
    answered (s′ , inj₂ p) = shaped-run n (s′ , f ∨ P s′) (k (inj₁ p)) (h p)
  shaped-run n (s , f) (ask (inj₂ _) k) h =
    cofinal-trans _ _ _ (≈ₚ⇒cofinal Qᵗ nnQ (>>=ₚ-identityˡ ((s , f) , inj₂ (inj₂ f)) _)) λ j →
      2 , ≤-trans (final-run f (s , f) (k (inj₂ f)) (h f) j)
                  (≤-reflexive (sym (trans (>>=ₚ-identityˡ-cum 1 ((s , f) , inj₂ (inj₂ f))
                                             (resumeᴹ u λ m′ x → runᴹFrom u m′ ([ (λ _ → out false) , out ] x)) Qᵗ)
                                           (returnₚ-cum 0 f Qᵗ))))

------------------------------------------------------------------------
-- The flagged context, certified

module FlagCert (B : Iface) (N : Proc B Ωᴵ) {k : ℕ} (qN : Certified k N) where

  open Read B N
  private module qN = QBᵢ qN

  pendF : FlagSt → ℕ
  pendF waitE = 1
  pendF idle  = 0
  pendF waitF = 0

  Φᶠ : FlagSt × MC.St N → ℕ
  Φᶠ (fs , se) = qN.Φ se ℕ.+ pendF fs

  private
    Aᴺ : ℕ → Set
    Aᴺ = Ans qN.Φ (Neg B) Bool

    Aᶠ : ℕ → Set
    Aᶠ = Ans Φᶠ (Neg B ⊎ ⊤) Bool

    -- `Read.efOut` with the potentials attached: the test's query costs what
    -- it cost the test, its verdict becomes the flag ask, paid by `pendF`.
    fAns : (fs : FlagSt) {rN r : ℕ} → rN ℕ.+ pendF fs ℕ.≤ r → Aᴺ rN → Dₚ (Aᶠ r)
    fAns fs le (inj₁ ((se , lo) , q)) =
      returnₚ (inj₁ (((fs , se) , ℕP.≤-trans (ℕP.+-monoˡ-≤ (pendF fs) lo) le) , inj₁ q))
    fAns waitE le (inj₂ ((se , lo) , _)) =
      returnₚ (inj₁ (((waitF , se) , ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.+-suc _ 0)))
                                                (ℕP.≤-trans (ℕP.+-monoˡ-≤ 1 lo) le)) , inj₂ tt))
    fAns idle  le (inj₂ _) = botₚ
    fAns waitF le (inj₂ _) = botₚ

    fAns-coh : (fs : FlagSt) {rN r : ℕ} (le : rN ℕ.+ pendF fs ℕ.≤ r) (y : Aᴺ rN)
             → mapₚ forget (fAns fs le y) ≈ₚ efOut fs (forget y)
    fAns-coh fs    le (inj₁ _) = >>=ₚ-identityˡ _ _
    fAns-coh waitE le (inj₂ _) = >>=ₚ-identityˡ _ _
    fAns-coh idle  le (inj₂ _) = bot-bind-≈ₚ _
    fAns-coh waitF le (inj₂ _) = bot-bind-≈ₚ _

    leR : (x : ℕ) → (x ℕ.+ k) ℕ.+ 1 ℕ.≤ (x ℕ.+ 0) ℕ.+ (k ℕ.+ 1)
    leR x = ℕP.≤-reflexive (trans (ℕP.+-assoc x k 1) (cong (ℕ._+ (k ℕ.+ 1)) (sym (ℕP.+-identityʳ x))))

  onRᶠ : (s : FlagSt × MC.St N) (b : ⊤) → Dₚ (Aᶠ (Φᶠ s ℕ.+ (k ℕ.+ 1)))
  onRᶠ (idle  , se) _ = qN.onRᵍ se tt >>=ₚ fAns waitE (leR (qN.Φ se))
  onRᶠ (waitE , _)  _ = botₚ
  onRᶠ (waitF , _)  _ = botₚ

  onLᶠ : (s : FlagSt × MC.St N) (a : Pos B ⊎ Bool) → Dₚ (Aᶠ (Φᶠ s))
  onLᶠ (fs    , se) (inj₁ p) = qN.onLᵍ se p >>=ₚ fAns fs ℕP.≤-refl
  onLᶠ (waitF , se) (inj₂ b) = returnₚ (inj₂ (((idle , se) , ℕP.≤-refl) , b))
  onLᶠ (idle  , _)  (inj₂ _) = botₚ
  onLᶠ (waitE , _)  (inj₂ _) = botₚ

  private
    cohRᶠ : (s : FlagSt × MC.St N) (b : ⊤) → mapₚ forget (onRᶠ s b) ≈ₚ MC.step readᴹ (s , inj₂ b)
    cohRᶠ (idle , se) _ =
          map-bind (qN.onRᵍ se tt) (fAns waitE _) forget
      ⟨≈⟩ bindᶠ (fAns-coh waitE _)
      ⟨≈⟩ ≈sym (bind-map (qN.onRᵍ se tt) forget (efOut waitE))
      ⟨≈⟩ bindˣ (qN.cohR se tt)
    cohRᶠ (waitE , _) _ = bot-bind-≈ₚ _
    cohRᶠ (waitF , _) _ = bot-bind-≈ₚ _

    cohLᶠ : (s : FlagSt × MC.St N) (a : Pos B ⊎ Bool) → mapₚ forget (onLᶠ s a) ≈ₚ MC.step readᴹ (s , inj₁ a)
    cohLᶠ (fs , se) (inj₁ p) =
          map-bind (qN.onLᵍ se p) (fAns fs _) forget
      ⟨≈⟩ bindᶠ (fAns-coh fs _)
      ⟨≈⟩ ≈sym (bind-map (qN.onLᵍ se p) forget (efOut fs))
      ⟨≈⟩ bindˣ (qN.cohL se p)
    cohLᶠ (waitF , se) (inj₂ b) = >>=ₚ-identityˡ _ _
    cohLᶠ (idle  , _)  (inj₂ _) = bot-bind-≈ₚ _
    cohLᶠ (waitE , _)  (inj₂ _) = bot-bind-≈ₚ _

    pointᶠ : Dₚ (AtMost Φᶠ 0)
    pointᶠ = mapₚ (λ z → (idle , proj₁ z) , ℕP.≤-trans (ℕP.≤-reflexive (ℕP.+-identityʳ _)) (proj₂ z))
                  qN.pointᵍ

    coh₀ᶠ : mapₚ proj₁ pointᶠ ≈ₚ MC.point (MC.state readᴹ) ttᵛ
    coh₀ᶠ =
          map-map qN.pointᵍ _ proj₁
      ⟨≈⟩ ≈sym (map-map qN.pointᵍ proj₁ (idle ,_))
      ⟨≈⟩ map-arg _ qN.coh₀
      ⟨≈⟩ ≈sym (point-⊛ (MC.state flagReadᴹ) (MC.state N) ttᵛ ⟨≈⟩ >>=ₚ-identityˡ idle _)

  certᶠ : Certified (k ℕ.+ 1) readᴹ
  certᶠ = record
    { Φ = Φᶠ ; pointᵍ = pointᶠ ; coh₀ = coh₀ᶠ ; onLᵍ = onLᶠ ; onRᵍ = onRᶠ
    ; cohL = cohLᶠ ; cohR = cohRᶠ
    }

  ------------------------------------------------------------------------
  -- Every extracted strategy is flag-shaped

  open Ext (B ⊗ᴵ Ωᴵ) readᴹ (k ℕ.+ 1) certᶠ

  private
    final : (b : Bool) (f r : ℕ) (x : AtMost Φᶠ r) → Final b (extract true f r (returnₚ (inj₂ (x , b))))
    final b zero    r x = λ ()
    final b (suc f) r x = λ _ h → h

    shaped-bot : (n f r : ℕ) → FlagShaped n (extract true f r botₚ)
    shaped-bot n zero    r = refl
    shaped-bot n (suc f) r = λ _ → shaped-bot n f r

    mutual
      shapedTree : {rN r : ℕ} (le : rN ℕ.+ 1 ℕ.≤ r) (X : Dₚ (Aᴺ rN)) (f : ℕ)
                 → FlagShaped rN (extract true f r (X >>=ₚ fAns waitE le))
      shapedTree le X zero    = refl
      shapedTree le X (suc f) = λ c → shapedLeaf le (br X c) f

      shapedLeaf : {rN r : ℕ} (le : rN ℕ.+ 1 ℕ.≤ r) (y : Aᴺ rN ⊎ Dₚ (Aᴺ rN)) (f : ℕ)
                 → FlagShaped rN (extractL true f r (tagₚ y (fAns waitE le)))
      shapedLeaf le (inj₂ X′) f = shapedTree le X′ f
      shapedLeaf le (inj₁ y)  f = shapedVal le y f

      shapedVal : {rN r : ℕ} (le : rN ℕ.+ 1 ℕ.≤ r) (y : Aᴺ rN) (f : ℕ)
                → FlagShaped rN (extract true f r (fAns waitE le y))
      shapedVal le (inj₁ _)                     zero    = refl
      shapedVal le (inj₁ ((se , s≤s lo) , q))   (suc f) = λ _ p →
        flagShaped-mono lo _ (shapedTree ℕP.≤-refl (qN.onLᵍ se p) f)
      shapedVal le (inj₂ _)                     zero    = refl
      shapedVal le (inj₂ ((se , _) , _))        (suc f) = λ _ b → final b f _ _

  shaped : (f : ℕ) (z : AtMost Φᶠ 0)
         → FlagShaped k (extract true f (Φᶠ (proj₁ z) ℕ.+ (k ℕ.+ 1)) (onRᶠ (proj₁ z) tt))
  shaped f ((idle , se) , z) =
    flagShaped-mono (ℕP.+-monoˡ-≤ k (ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.+-identityʳ _))) z)) _
                    (shapedTree (leR (qN.Φ se)) (qN.onRᵍ se tt) f)
  shaped f ((waitE , se) , z) = ⊥-elim (ℕP.n≮0 (ℕP.≤-trans (ℕP.≤-reflexive (ℕP.+-comm 1 _)) z))
  shaped f ((waitF , se) , z) = shaped-bot k f _

------------------------------------------------------------------------
-- The lift

read-≈ : (B : Iface) {N D : Proc B Ωᴵ} → N S.≈ᴹ D
       → 𝒫._≈_ (Read.readᴹ B N) (flagReadᴹ 𝒫.∘ subᴵ D)
read-≈ B {N} e = S.⟺ᴹ (Read.read-collapse B N) S.○ᴹ 𝒫.∘-resp-≈ʳ (sub-resp-≈ e)

flagSkeleton : (B : Iface) (D : Proc B Ωᴵ) {k : ℕ} → QB k D
             → (M : Proc unitᴵ B) (P : StateTest M) (r : ℚ)
             → ((d : Strat (Neg B) (Pos B)) → asks≤ k d → Upper (runᴹ (M ▷ P) (flagStrat d)) r)
             → Upper ⟦ (flagReadᴹ 𝒫.∘ subᴵ D) 𝒫.∘ (M ▷ P) ⟧ᴼ r
-- The depths are bound by `case`, not as `where n₁ = proj₁ …`: conversion
-- unfolds a where-bound projection, and with the certificate concrete it then
-- evaluates the domination witness itself (> 16 GiB, against 24 s).
flagSkeleton B D {k} (N , certN , e) M P r h n =
  case to-obs u true n of λ where
    (n₁ , le₁) → case fwd u true n₁ n₁ ℕP.≤-refl of λ where
      (n₂ , le₂) → ≤-trans le₁ (≤-trans le₂ (bound n₁ n₂))
  where
  open FlagCert B N certN
  open Refine (B ⊗ᴵ Ωᴵ) (flagReadᴹ 𝒫.∘ subᴵ D) (Read.readᴹ B N) (k ℕ.+ 1) certᶠ (read-≈ B e)

  u = M ▷ P

  bound : (f i : ℕ) → cum i (plays u true f) (indᵇ true) ℚ.≤ r
  bound f i =
    cum-bindʳ i pointᵍ _ (indᵇ true) (indᵇ-nn true) r (h (out false) tt 0) λ z →
      let d′ = dstrat true f z
          m , le = cofinal-bind (indᵇ true) (indᵇ-nn true) (MC.point (MC.state u) ttᵛ) _ _
                     (λ s → shaped-run M P k s d′ (shaped f z)) i
      in ≤-trans le (h (unflagStrat d′) (asks≤-unflag k d′ (shaped f z)) m)

-- …at an admitted context: the closed test's count is `scale c (positive c′)`,
-- the flag ask is the certificate's one extra unit, and the premise is read at
-- the context's own cap.
stateLift : {B : Iface} (M : Proc unitᴵ B) (P : StateTest M) (q : ℕ) {r : ℚ}
          → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ (M ▷ P) (flagStrat d)) r)
          → StateBoundedAt q r M P
stateLift {B} M P q {r} h Y E m {c} {c′} qE qm le =
  upper-≈ (stateRead-closed Y M P E m)
    (flagSkeleton B (Kctx (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m)
       (qb-Kctx (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m
          (subst (λ j → QB j (E 𝒫.∘ T₁ᴵ Y λᴵ⇒)) (ℕP.*-identityʳ c)
             (qb-∘-category (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) (Y ⊗ᴵ B) Ωᴵ E (T₁ᴵ Y λᴵ⇒) qE
                (qb-T₁ᴵ Y (unitᴵ ⊗ᴵ B) B λᴵ⇒ qb-λᴵ⇒)))
          qm)
       M P r
       λ d a → h d (asks≤-mono le d a))

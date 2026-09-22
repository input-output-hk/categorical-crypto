{-# OPTIONS --safe --without-K --guardedness #-}

-- The accumulator invariant at the compiled context: a certificate of the
-- collapsed monitored context whose emission tree satisfies
-- `UC.Machine.Dominated.CovCtx`.
--
-- `CovCtx` reads the invariant at EVERY zero-potential state of the
-- certificate, not only at the initial one, so the certificate has to be
-- chosen so that a zero-potential state HAS an empty accumulator.  The
-- five-fold `qb-∘` tower does not: the monitor's own potential there is
-- constantly zero (`UC.Machine.Monitor.qbᵢ-monitor`), so the product state
-- carrying a raised flag and everything else spent still has potential zero,
-- and from it the compiled context reports `true` with no traffic to cover
-- it.  `pend` below is the repair — the monitor's potential is positive
-- exactly when the accumulator has fired or an answer is owed — and it costs
-- one unit of the rate, not a factor.
--
-- The certificate is built on the COLLAPSED tower
-- (`UC.Machine.Monitor.Agree.Watch.watchᴹ`), where the accumulator is a state
-- component and the emission tree is the test's own, post-processed: the
-- invariant is then an induction on that tree rather than a walk through
-- `qb-∘`.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false; true)
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties
  using (*-identityʳ; +-assoc; +-comm; +-identityʳ; +-monoʳ-≤; +-monoˡ-≤; m≤m+n;
         n≮0; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ; a⇐ᴵ; subᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Dictionary using (a⇐-α⇒)
open import CategoricalCrypto.UC.Machine.Dominated using (CovCtx)
open import CategoricalCrypto.UC.Machine.Grading using (qb-a⇐ᴳ; qb-subᴵ; qb-T₁ᴵ)
open import CategoricalCrypto.UC.Machine.Monitor
  using (FlagSt; MonSt; compileᴹ; idle; monitorᴹ; waitE; waitF)
open import CategoricalCrypto.UC.Machine.Monitor.Agree using (module Watch)
open import CategoricalCrypto.UC.Machine.Monitor.Slide
  using (closedᴹ; compiled-slide; watch-resp-≈)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx)
open import CategoricalCrypto.UC.QueryBound
  using (Ans; AtMost; Certified; QB; QBᵢ; certified⇒QB; forget; qb-closed; qb-resp-≈;
         qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Seam.EventTransfer as ET

module CategoricalCrypto.UC.Quantitative.EventLift.Cov where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ) using (_≈ᴹ_; _○ᴹ_; ⟺ᴹ)

module Cert (B : Iface) (report : Neg B → Pos B → Bool)
            (E : Proc (unitᴵ ⊗ᴵ B) Ωᴵ) {c : ℕ} (qE : Certified c E) where

  open Watch B report E
  private module qE = QBᵢ qE

  ------------------------------------------------------------------------
  -- The potential

  bit : Bool → ℕ
  bit true  = 1
  bit false = 0

  -- The monitor's own potential.  Splitting on the pending query FIRST makes
  -- `pend (acc , just q)` reduce without knowing `acc`, which is what the
  -- emission tree's query leaf needs.
  pend : MonSt B → ℕ
  pend (_   , just _)  = 1
  pend (acc , nothing) = bit acc

  pend≤1 : (m : MonSt B) → pend m ℕ.≤ 1
  pend≤1 (_     , just _)  = ≤-refl
  pend≤1 (true  , nothing) = ≤-refl
  pend≤1 (false , nothing) = z≤n

  Φᵂ : WCfg → ℕ
  Φᵂ ((_ , se) , m) = qE.Φ se ℕ.+ pend m

  private
    Aᴱ : ℕ → Set
    Aᴱ = Ans qE.Φ (Neg unitᴵ ⊎ Neg B) Bool

    Aᵂ : ℕ → Set
    Aᵂ = Ans Φᵂ (Neg B) Bool

    ------------------------------------------------------------------------
    -- The potential arithmetic

    -- A query leaf owes one unit for the answer it is waiting for, and the
    -- test's own drop pays for it.
    qBound : {x rE r : ℕ} → x ℕ.< rE → rE ℕ.< r → x ℕ.+ 1 ℕ.< r
    qBound {x} lo lt = ≤-trans (s≤s (≤-trans (≤-reflexive (+-comm x 1)) lo)) lt

    vBound : {x rE r : ℕ} (n : ℕ) → x ℕ.≤ rE → rE ℕ.+ n ℕ.≤ r → x ℕ.+ n ℕ.≤ r
    vBound n lo le = ≤-trans (+-monoˡ-≤ n lo) le

    -- The single extra unit the rate spends: the accumulator's own.
    swap₃ : (a b d : ℕ) → (a ℕ.+ b) ℕ.+ d ≡ (a ℕ.+ d) ℕ.+ b
    swap₃ a b d = trans (+-assoc a b d)
                        (trans (cong (a ℕ.+_) (+-comm b d)) (sym (+-assoc a d b)))

    ltR : (x p : ℕ) → x ℕ.+ c ℕ.< (x ℕ.+ p) ℕ.+ (c ℕ.+ 1)
    ltR x p = ≤-trans (s≤s (+-monoˡ-≤ c (m≤m+n x p)))
                      (≤-reflexive (trans (sym (+-comm ((x ℕ.+ p) ℕ.+ c) 1))
                                          (+-assoc (x ℕ.+ p) c 1)))

    leR : (x p : ℕ) → (x ℕ.+ c) ℕ.+ p ℕ.≤ (x ℕ.+ p) ℕ.+ (c ℕ.+ 1)
    leR x p = ≤-trans (≤-reflexive (swap₃ x c p)) (+-monoʳ-≤ (x ℕ.+ p) (m≤m+n c 1))

    ltL : (x : ℕ) → x ℕ.< x ℕ.+ 1
    ltL x = ≤-reflexive (sym (+-comm x 1))

    owed : {x : ℕ} → x ℕ.+ 1 ℕ.≤ 0 → ⊥
    owed {x} le = n≮0 (subst (ℕ._≤ 0) (+-comm x 1) le)

    ------------------------------------------------------------------------
    -- The test's emission, refined

    -- `Watch.wPass` with the potentials attached: a query owes an answer, a
    -- verdict is DISCARDED and the accumulator reported in its place.
    wAns : (fs : FlagSt) (m : MonSt B) {rE r : ℕ}
         → rE ℕ.< r → rE ℕ.+ pend m ℕ.≤ r → Aᴱ rE → Dₚ (Aᵂ r)
    wAns fs _         lt le (inj₁ (_         , inj₁ ()))
    wAns fs (acc , _) lt le (inj₁ ((se , lo) , inj₂ q)) =
      returnₚ (inj₁ ((((fs , se) , (acc , just q)) , qBound lo lt) , q))
    wAns waitE m      lt le (inj₂ ((se , lo) , _)) =
      returnₚ (inj₂ ((((idle , se) , m) , vBound (pend m) lo le) , proj₁ m))
    wAns idle  _      lt le (inj₂ _) = botₚ
    wAns waitF _      lt le (inj₂ _) = botₚ

    wAns-coh : (fs : FlagSt) (m : MonSt B) {rE r : ℕ}
               (lt : rE ℕ.< r) (le : rE ℕ.+ pend m ℕ.≤ r) (y : Aᴱ rE)
             → mapₚ forget (wAns fs m lt le y) ≈ₚ wPass fs m (forget y)
    wAns-coh fs _         lt le (inj₁ (_ , inj₁ ()))
    wAns-coh fs (acc , _) lt le (inj₁ (_ , inj₂ q)) = >>=ₚ-identityˡ _ _
    wAns-coh waitE m      lt le (inj₂ _)            = >>=ₚ-identityˡ _ _
    wAns-coh idle  _      lt le (inj₂ _)            = bot-bind-≈ₚ _
    wAns-coh waitF _      lt le (inj₂ _)            = bot-bind-≈ₚ _

  ------------------------------------------------------------------------
  -- The certificate

  onRᵂ : (s : WCfg) (b : ⊤) → Dₚ (Aᵂ (Φᵂ s ℕ.+ (c ℕ.+ 1)))
  onRᵂ ((idle  , se) , m) _ =
    qE.onRᵍ se tt >>=ₚ wAns waitE m (ltR (qE.Φ se) (pend m)) (leR (qE.Φ se) (pend m))
  onRᵂ ((waitE , _) , _) _ = botₚ
  onRᵂ ((waitF , _) , _) _ = botₚ

  onLᵂ : (s : WCfg) (a : Pos B) → Dₚ (Aᵂ (Φᵂ s))
  onLᵂ ((fs , se) , (acc , just q))  p =
    qE.onLᵍ se (inj₂ p)
      >>=ₚ wAns fs (acc ∨ report q p , nothing) (ltL (qE.Φ se))
                   (+-monoʳ-≤ (qE.Φ se) (pend≤1 _))
  onLᵂ ((_ , _) , (_ , nothing)) _ = botₚ

  private
    cohRᵂ : (s : WCfg) (b : ⊤) → mapₚ forget (onRᵂ s b) ≈ₚ MC.step watchᴹ (s , inj₂ b)
    cohRᵂ ((idle , se) , m) _ =
          map-bind (qE.onRᵍ se tt) (wAns waitE m _ _) forget
      ⟨≈⟩ bindᶠ (wAns-coh waitE m _ _)
      ⟨≈⟩ ≈sym (bind-map (qE.onRᵍ se tt) forget (wPass waitE m))
      ⟨≈⟩ bindˣ (qE.cohR se tt)
    cohRᵂ ((waitE , _) , _) _ = bot-bind-≈ₚ _
    cohRᵂ ((waitF , _) , _) _ = bot-bind-≈ₚ _

    cohLᵂ : (s : WCfg) (a : Pos B) → mapₚ forget (onLᵂ s a) ≈ₚ MC.step watchᴹ (s , inj₁ a)
    cohLᵂ ((fs , se) , (acc , just q)) p =
          map-bind (qE.onLᵍ se (inj₂ p)) (wAns fs (acc ∨ report q p , nothing) _ _) forget
      ⟨≈⟩ bindᶠ (wAns-coh fs (acc ∨ report q p , nothing) _ _)
      ⟨≈⟩ ≈sym (bind-map (qE.onLᵍ se (inj₂ p)) forget
                         (wPass fs (acc ∨ report q p , nothing)))
      ⟨≈⟩ bindˣ (qE.cohL se (inj₂ p))
    cohLᵂ ((_ , _) , (_ , nothing)) _ = bot-bind-≈ₚ _

    pointᵂ : Dₚ (AtMost Φᵂ 0)
    pointᵂ = mapₚ (λ z → ((idle , proj₁ z) , (false , nothing)) , zeroᵂ z) qE.pointᵍ
      where
      zeroᵂ : (z : AtMost qE.Φ 0) → Φᵂ ((idle , proj₁ z) , (false , nothing)) ℕ.≤ 0
      zeroᵂ z = ≤-trans (≤-reflexive (+-identityʳ _)) (proj₂ z)

    coh₀ᵂ : mapₚ proj₁ pointᵂ ≈ₚ MC.point (MC.state watchᴹ) ttᵛ
    coh₀ᵂ =
          map-map qE.pointᵍ _ proj₁
      ⟨≈⟩ ≈sym (map-map qE.pointᵍ proj₁ (λ se → (idle , se) , (false , nothing)))
      ⟨≈⟩ map-arg _ qE.coh₀
      ⟨≈⟩ ≈sym watch-point

  certᵂ : Certified (c ℕ.+ 1) watchᴹ
  certᵂ = record
    { Φ = Φᵂ ; pointᵍ = pointᵂ ; coh₀ = coh₀ᵂ ; onLᵍ = onLᵂ ; onRᵍ = onRᵂ
    ; cohL = cohLᵂ ; cohR = cohRᵂ
    }

  ------------------------------------------------------------------------
  -- The invariant

  open ET B watchᴹ (c ℕ.+ 1) certᵂ report

  private
    -- The accumulators advance at the same answer, so the covering survives.
    ∨-cover : {acc accᶜ b : Bool} → (acc ≡ true → accᶜ ≡ true)
            → (acc ∨ b) ≡ true → (accᶜ ∨ b) ≡ true
    ∨-cover {accᶜ = accᶜ} {true}  h _  = ∨-zeroʳ accᶜ
    ∨-cover {true}  {accᶜ} {false} h _ = trans (∨-identityʳ accᶜ) (h refl)
    ∨-cover {false} {accᶜ} {false} h ()

    -- The accumulator the machine carries is covered by the one the
    -- invariant has walked up: the verdict IS that accumulator, and both
    -- advance by `report` at the same answer.
    mutual
      covTree : (accᶜ : Bool) (fs : FlagSt) (m : MonSt B) {rE r : ℕ}
                (lt : rE ℕ.< r) (le : rE ℕ.+ pend m ℕ.≤ r) (X : Dₚ (Aᴱ rE))
              → (proj₁ m ≡ true → accᶜ ≡ true)
              → (f : ℕ) → Cov accᶜ f r (X >>=ₚ wAns fs m lt le)
      covTree accᶜ fs m lt le X h zero    = tt
      covTree accᶜ fs m lt le X h (suc f) =
        covLeaf accᶜ fs m lt le (br X true) h f , covLeaf accᶜ fs m lt le (br X false) h f

      covLeaf : (accᶜ : Bool) (fs : FlagSt) (m : MonSt B) {rE r : ℕ}
                (lt : rE ℕ.< r) (le : rE ℕ.+ pend m ℕ.≤ r) (y : Aᴱ rE ⊎ Dₚ (Aᴱ rE))
              → (proj₁ m ≡ true → accᶜ ≡ true)
              → (f : ℕ) → CovL accᶜ f r (tagₚ y (wAns fs m lt le))
      covLeaf accᶜ fs m lt le (inj₂ X′) h f = covTree accᶜ fs m lt le X′ h f
      covLeaf accᶜ fs m lt le (inj₁ y)  h f = covVal accᶜ fs m lt le y h f

      covVal : (accᶜ : Bool) (fs : FlagSt) (m : MonSt B) {rE r : ℕ}
               (lt : rE ℕ.< r) (le : rE ℕ.+ pend m ℕ.≤ r) (y : Aᴱ rE)
             → (proj₁ m ≡ true → accᶜ ≡ true)
             → (f : ℕ) → Cov accᶜ f r (wAns fs m lt le y)
      covVal accᶜ fs _         lt le (inj₁ (_ , inj₁ ())) h f
      covVal accᶜ fs (acc , _) lt le (inj₁ (_ , inj₂ q))  h zero    = tt
      covVal accᶜ fs (acc , _) lt le (inj₁ ((se , lo) , inj₂ q)) h (suc f) = answer , answer
        where
        answer : (p : Pos B) → _
        answer p = covTree (accᶜ ∨ report q p) fs (acc ∨ report q p , nothing) _ _
                           (qE.onLᵍ se (inj₂ p)) (∨-cover h) f
      covVal accᶜ waitE m lt le (inj₂ _) h zero    = tt
      covVal accᶜ waitE m lt le (inj₂ _) h (suc f) = h , h
      covVal accᶜ idle  _ lt le (inj₂ _) h f       = cov-bot accᶜ f _
      covVal accᶜ waitF _ lt le (inj₂ _) h f       = cov-bot accᶜ f _

  ------------------------------------------------------------------------
  -- …at every zero-potential state

  -- `pend` is what makes this provable: a state of potential zero has an
  -- EMPTY accumulator, so the run the invariant is read along starts where
  -- the machine does.
  covᵂ : (f : ℕ) (z : AtMost Φᵂ 0)
       → Cov false f (Φᵂ (proj₁ z) ℕ.+ (c ℕ.+ 1)) (onRᵂ (proj₁ z) tt)
  covᵂ f (((idle  , se) , (false , nothing)) , _) =
    covTree false waitE (false , nothing) _ _ (qE.onRᵍ se tt) (λ ()) f
  covᵂ f (((idle  , _)  , (false , just _))  , z) = ⊥-elim (owed z)
  covᵂ f (((idle  , _)  , (true  , just _))  , z) = ⊥-elim (owed z)
  covᵂ f (((idle  , _)  , (true  , nothing)) , z) = ⊥-elim (owed z)
  covᵂ f (((waitE , _)  , _) , _) = cov-bot false f _
  covᵂ f (((waitF , _)  , _) , _) = cov-bot false f _

------------------------------------------------------------------------
-- The compiled context, certified and covered

-- The closure is a closed process, so it is recertified at rate zero
-- (`qb-closed`) and the closed test costs exactly what the original test
-- does — the second leg of `ctxBudget` never enters.
qb-closedᴹ : (Y B : Iface) {c : ℕ} (E : Proc (Y ⊗ᴵ B) Ωᴵ)
             (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) → QB c E → QB c (closedᴹ Y B E m)
qb-closedᴹ Y B {c} E m qE =
  subst (λ k → QB k (closedᴹ Y B E m))
        (trans (*-identityʳ (c ℕ.* 1)) (*-identityʳ c))
    (qb-∘-category (unitᴵ ⊗ᴵ B) (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ
      (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) (a⇐ᴵ 𝒫.∘ subᴵ m)
      (qb-∘-category (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) (Y ⊗ᴵ B) Ωᴵ E (T₁ᴵ Y λᴵ⇒) qE
        (qb-T₁ᴵ Y (unitᴵ ⊗ᴵ B) B λᴵ⇒ (certified⇒QB (qbᵢ-wire [ ⊥-elim , id ] inj₂))))
      (qb-∘-category (unitᴵ ⊗ᴵ B) ((Y ⊗ᴵ unitᴵ) ⊗ᴵ B) (Y ⊗ᴵ (unitᴵ ⊗ᴵ B))
        a⇐ᴵ (subᴵ m)
        (qb-resp-≈ (⟺ᴹ (a⇐-α⇒ {Y} {unitᴵ} {B})) (qb-a⇐ᴳ Y unitᴵ B))
        (qb-subᴵ unitᴵ (Y ⊗ᴵ unitᴵ) B m (qb-closed m))))

-- The premise of `UC.Quantitative.EventLift.eventDominated`, at the rate the
-- invariant costs: ONE more than the test's own.  That unit is not slack —
-- `CovCtx` reads the invariant at every zero-potential state, a raised
-- accumulator must therefore carry potential, and a context that spends its
-- whole allowance before reporting leaves none at rate `c`.
covCtx : (Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
         (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) → QB c E
       → Σ[ kb ∈ QB (c ℕ.+ 1)
                    (Kctx (compileᴹ Y B (monitorᴹ report) E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m) ]
           CovCtx B (c ℕ.+ 1) report kb
covCtx Y B report {c} E m qE =
    (Watch.watchᴹ B report N , Cert.certᵂ B report N certN , eq)
  , Cert.covᵂ B report N certN
  where
  qD = qb-closedᴹ Y B E m qE

  N = proj₁ qD
  certN = proj₁ (proj₂ qD)

  eq : Watch.watchᴹ B report N ≈ᴹ Kctx (compileᴹ Y B (monitorᴹ report) E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m
  eq = watch-resp-≈ B report (proj₂ (proj₂ qD))
    ○ᴹ ⟺ᴹ (compiled-slide Y B report E m)

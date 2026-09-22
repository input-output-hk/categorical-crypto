{-# OPTIONS --safe --without-K --guardedness #-}

-- `compileᴹ`'s tight certificate: the compiled test spends the allowance of
-- the test it was compiled from.
--
-- The flag query `flagReadᴹ` makes is answered by `monitorᴹ` and never leaves
-- the composite, so the compiled test's downward traffic on `Y ⊗ᴵ B` is
-- exactly `E`'s and the potential of the composite IS `E`'s.  `qb-∘`
-- multiplies rates and cannot tell a flag-port query from one on `Y ⊗ᴵ B`,
-- which is why `UC.Machine.Monitor.qb-compileᴹ` stops at the coarse
-- `κμ c = 2 · (c ⊔ 1)`; both are kept, the coarse one being the cheaper term.
--
-- Nothing here is a port-sensitive resource theory: the accounting is local to
-- this consumer, and it is bought by reading the composite as ONE machine
-- (`UC.QueryBound.Compose.Step`'s `Nᶜ`/`unfoldᶜ`, with `Agree`'s collapse of
-- `flagReadᴹ ∘ subᴵ E`) rather than by refining `QBᵢ`
-- (`docs/event-bounds-in-setup.md` §B).

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.QueryBound.Compose.Step as CStep

module CategoricalCrypto.UC.Machine.Monitor.Tight where

open Core (𝒱ₚ 0ℓ) hiding (onRᵍ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The monitor with the compiler's reassociator absorbed

module _ (Y B : Iface) (report : Neg B → Pos B → Bool) where

  monStepᵀ : MonSt B × ((Pos Y ⊎ Pos B) ⊎ ((Neg Y ⊎ Neg B) ⊎ ⊤))
           → Dₚ (MonSt B × ((Neg Y ⊎ Neg B) ⊎ ((Pos Y ⊎ Pos B) ⊎ Bool)))
  monStepᵀ (m              , inj₂ (inj₁ (inj₁ y))) = returnₚ (m , inj₁ (inj₁ y))
  monStepᵀ ((acc , _)      , inj₂ (inj₁ (inj₂ q))) = returnₚ ((acc , just q) , inj₁ (inj₂ q))
  monStepᵀ ((acc , p)      , inj₂ (inj₂ _))        = returnₚ ((acc , p) , inj₂ (inj₂ acc))
  monStepᵀ (m              , inj₁ (inj₁ y))        = returnₚ (m , inj₂ (inj₁ (inj₁ y)))
  monStepᵀ ((acc , just q) , inj₁ (inj₂ a)) =
    returnₚ ((acc ∨ report q a , nothing) , inj₂ (inj₁ (inj₂ a)))
  monStepᵀ ((_ , nothing)  , inj₁ (inj₂ _))        = botₚ

  monᵀ : Proc (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ)
  monᵀ = mk (state (monitorᴹ report)) monStepᵀ

  mon-wireᵀ : 𝒫._≈_ {Y ⊗ᴵ B} {(Y ⊗ᴵ B) ⊗ᴵ Flagᴵ}
                (a⇒ᴵ 𝒫.∘ T₁ᴵ Y (monitorᴹ report)) monᵀ
  mon-wireᵀ = wire-∘ᴹ ⊎assocˡ ⊎assocʳ (T₁ᴵ Y (monitorᴹ report))
           ○ᴹ ≲⇒≈ᴹ (mk-cong pt)
    where
    pt : (z : _) → _
    pt (m              , inj₁ (inj₁ y))        = >>=ₚ-identityˡ _ _
    pt ((acc , just q) , inj₁ (inj₂ a)) =
      bindˣ (>>=ₚ-identityˡ ((acc ∨ report q a , nothing) , inj₂ (inj₁ a)) _)
        ⟨≈⟩ >>=ₚ-identityˡ _ _
    pt ((_ , nothing)  , inj₁ (inj₂ _))        = bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    pt (m              , inj₂ (inj₁ (inj₁ y))) = >>=ₚ-identityˡ _ _
    pt ((acc , _)      , inj₂ (inj₁ (inj₂ q))) =
      bindˣ (>>=ₚ-identityˡ ((acc , just q) , inj₁ q) _) ⟨≈⟩ >>=ₚ-identityˡ _ _
    pt ((acc , p)      , inj₂ (inj₂ _)) =
      bindˣ (>>=ₚ-identityˡ ((acc , p) , inj₂ (inj₂ acc)) _) ⟨≈⟩ >>=ₚ-identityˡ _ _

------------------------------------------------------------------------
-- The tight certificate

module _ (Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
         (N : Proc (Y ⊗ᴵ B) Ωᴵ) (qN : Certified c N) where

  open Read (Y ⊗ᴵ B) N
  open QBᵢ qN

  -- The compiled test as one product-state machine: `Compose.Step`'s reading
  -- of the composite, at the two factors the collapses above name.
  Nᶜ : Proc (Y ⊗ᴵ B) Ωᴵ
  Nᶜ = CStep.Nᶜ (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) Ωᴵ readᴹ (monᵀ Y B report)

  private
    module CP = CStep.CP (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) Ωᴵ readᴹ (monᵀ Y B report)

    open CP using (resumeF; resumeG)
    open CP.Unfolding (CStep.unfoldᶜ (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) Ωᴵ readᴹ (monᵀ Y B report))

    Φᶜ : (FlagSt × St N) × MonSt B → ℕ
    Φᶜ ((_ , se) , _) = Φ se

    recordQ : MonSt B → Neg Y ⊎ Neg B → MonSt B
    recordQ m         (inj₁ _) = m
    recordQ (acc , _) (inj₂ q) = acc , just q

    outE : (fs : FlagSt) (m : MonSt B) {r : ℕ}
         → Ans Φ (Neg Y ⊎ Neg B) Bool r → Dₚ (Ans Φᶜ (Neg Y ⊎ Neg B) Bool r)
    outE fs    m         (inj₁ ((se , lt) , q)) =
      returnₚ (inj₁ ((((fs , se) , recordQ m q) , lt) , q))
    outE waitE (acc , p) (inj₂ ((se , le) , _)) =
      returnₚ (inj₂ ((((idle , se) , (acc , p)) , le) , acc))
    outE idle  m         (inj₂ _) = botₚ
    outE waitF m         (inj₂ _) = botₚ

    cohE : (fs : FlagSt) (m : MonSt B) {r : ℕ} (y : Ans Φ (Neg Y ⊎ Neg B) Bool r)
         → mapₚ forget (outE fs m y) ≈ₚ (efOut fs (forget y) >>=ₚ resumeG m)
    cohE fs m (inj₁ ((se , lt) , inj₁ y)) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁻ (fs , se) m (inj₁ (inj₁ y))
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-out _ _)
    cohE fs (acc , p) (inj₁ ((se , lt) , inj₂ q)) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁻ (fs , se) (acc , p) (inj₁ (inj₂ q))
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-out _ _)
    cohE waitE (acc , p) (inj₂ ((se , le) , v)) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁻ (waitF , se) (acc , p) (inj₂ tt)
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁺ (waitF , se) (acc , p) (inj₂ acc)
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-out _ _)
    cohE idle  m (inj₂ _) = bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)
    cohE waitF m (inj₂ _) = bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

    pump : (fs : FlagSt) (m : MonSt B) {r : ℕ}
           (d : Dₚ (Ans Φ (Neg Y ⊎ Neg B) Bool r))
           (e : Dₚ (St N × ((Neg Y ⊎ Neg B) ⊎ Bool))) → mapₚ forget d ≈ₚ e
         → mapₚ forget (d >>=ₚ outE fs m) ≈ₚ ((e >>=ₚ efOut fs) >>=ₚ resumeG m)
    pump fs m d e coh =
          map-bind d (outE fs m) forget
      ⟨≈⟩ bindᶠ (cohE fs m)
      ⟨≈⟩ ≈sym (>>=ₚ-assoc d (λ y → efOut fs (forget y)) (resumeG m))
      ⟨≈⟩ bindˣ (≈sym (bind-map d forget (efOut fs)))
      ⟨≈⟩ bindˣ (bindˣ coh)

    onLᶜ : (s : (FlagSt × St N) × MonSt B) (a : Pos Y ⊎ Pos B)
         → Dₚ (Ans Φᶜ (Neg Y ⊎ Neg B) Bool (Φᶜ s))
    onLᶜ ((fs , se) , m)               (inj₁ y) = onLᵍ se (inj₁ y) >>=ₚ outE fs m
    onLᶜ ((fs , se) , (acc , just q))  (inj₂ p) =
      onLᵍ se (inj₂ p) >>=ₚ outE fs (acc ∨ report q p , nothing)
    onLᶜ ((fs , se) , (acc , nothing)) (inj₂ p) = botₚ

    onRᶜ : (s : (FlagSt × St N) × MonSt B) (n : ⊤)
         → Dₚ (Ans Φᶜ (Neg Y ⊎ Neg B) Bool (Φᶜ s ℕ.+ c))
    onRᶜ ((idle  , se) , m) _ = onRᵍ se tt >>=ₚ outE waitE m
    onRᶜ ((waitE , se) , m) _ = botₚ
    onRᶜ ((waitF , se) , m) _ = botₚ

    cohLᶜ : (s : (FlagSt × St N) × MonSt B) (a : Pos Y ⊎ Pos B)
          → mapₚ forget (onLᶜ s a) ≈ₚ step Nᶜ (s , inj₁ a)
    cohLᶜ ((fs , se) , m) (inj₁ y) =
          pump fs m (onLᵍ se (inj₁ y)) _ (cohL se (inj₁ y))
      ⟨≈⟩ ≈sym ( step-L (fs , se) m (inj₁ y)
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁺ (fs , se) m (inj₁ (inj₁ y)))
    cohLᶜ ((fs , se) , (acc , just q)) (inj₂ p) =
          pump fs (acc ∨ report q p , nothing) (onLᵍ se (inj₂ p)) _ (cohL se (inj₂ p))
      ⟨≈⟩ ≈sym ( step-L (fs , se) (acc , just q) (inj₂ p)
            ⟨≈⟩ >>=ₚ-identityˡ _ _
            ⟨≈⟩ solve-B⁺ (fs , se) (acc ∨ report q p , nothing) (inj₁ (inj₂ p)))
    cohLᶜ ((fs , se) , (acc , nothing)) (inj₂ p) =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (step-L (fs , se) (acc , nothing) (inj₂ p) ⟨≈⟩ bot-bind-≈ₚ _)

    cohRᶜ : (s : (FlagSt × St N) × MonSt B) (n : ⊤)
          → mapₚ forget (onRᶜ s n) ≈ₚ step Nᶜ (s , inj₂ n)
    cohRᶜ ((idle  , se) , m) _ =
      pump waitE m (onRᵍ se tt) _ (cohR se tt) ⟨≈⟩ ≈sym (step-R (idle , se) m tt)
    cohRᶜ ((waitE , se) , m) _ =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (step-R (waitE , se) m tt ⟨≈⟩ bot-bind-≈ₚ _)
    cohRᶜ ((waitF , se) , m) _ =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (step-R (waitF , se) m tt ⟨≈⟩ bot-bind-≈ₚ _)

    initᶜ : St N → (FlagSt × St N) × MonSt B
    initᶜ se = (idle , se) , (false , nothing)

    pointᵍᶜ : Dₚ (AtMost Φᶜ 0)
    pointᵍᶜ = mapₚ (λ z → initᶜ (proj₁ z) , proj₂ z) pointᵍ

    coh₀ᶜ : mapₚ proj₁ pointᵍᶜ ≈ₚ point (state Nᶜ) ttᵛ
    coh₀ᶜ =
          map-map pointᵍ (λ z → initᶜ (proj₁ z) , proj₂ z) proj₁
      ⟨≈⟩ ≈sym (map-map pointᵍ proj₁ initᶜ)
      ⟨≈⟩ map-arg initᶜ coh₀
      ⟨≈⟩ ≈sym ( point-eq
            ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ (false , nothing) _)
            ⟨≈⟩ bindˣ ( point-⊛ (state flagReadᴹ) (state N) ttᵛ
                   ⟨≈⟩ >>=ₚ-identityˡ idle _)
            ⟨≈⟩ bind-map (point (state N) ttᵛ) (idle ,_) _)

  certᵀ : Certified c Nᶜ
  certᵀ = record
    { Φ = Φᶜ ; pointᵍ = pointᵍᶜ ; coh₀ = coh₀ᶜ ; onLᵍ = onLᶜ ; onRᵍ = onRᶜ
    ; cohL = cohLᶜ ; cohR = cohRᶜ
    }

  compiledᵀ : 𝒫._≈_ {Y ⊗ᴵ B} {Ωᴵ} Nᶜ (compileᴹ Y B (monitorᴹ report) N)
  compiledᵀ =
       CStep.eq-∘ᶜ (Y ⊗ᴵ B) ((Y ⊗ᴵ B) ⊗ᴵ Flagᴵ) Ωᴵ readᴹ (monᵀ Y B report)
    ○ᴹ 𝒫.∘-resp-≈ (⟺ᴹ read-collapse) (⟺ᴹ (mon-wireᵀ Y B report))
    ○ᴹ 𝒫.assoc

qb-compileᵀ : (Y B : Iface) (report : Neg B → Pos B → Bool) {c : ℕ}
              (E : Proc (Y ⊗ᴵ B) Ωᴵ) → QB c E
            → QB c (compileᴹ Y B (monitorᴹ report) E)
qb-compileᵀ Y B report E (N , cert , e) =
  qb-resp-≈ (𝒫.∘-resp-≈ʳ (𝒫.∘-resp-≈ˡ (sub-resp-≈ e)))
            (Nᶜ Y B report N cert , certᵀ Y B report N cert , compiledᵀ Y B report N cert)

{-# OPTIONS --safe --without-K --guardedness #-}

-- Monitor agreement at embedded strategies: `docs/event-bounds-in-setup.md`
-- §2 obligation 4.
--
-- The compiled monitored experiment of `UC.Quantitative.Hits`, run at the
-- context an ordinary finite strategy embeds to, IS layer 1's run of that
-- strategy under the watch — as `_≈ₚ_`, the relation the observation layer
-- supports, with the accumulated event, termination and divergence all carried
-- across.  Nothing here assumes the two machines are structurally equal.
--
-- The compiled context is a FIVE-machine tower, so `UC.Seam.Adequacy` does not
-- apply to it directly; what is reused rather than copied is the loop
-- reduction its `Tick` was built on, factored to arbitrary interfaces as
-- `UC.Seam.Plug.Loop`, and then `adequacy` itself at the collapsed tower.
-- The tie to `strategyEnv` is a SPAN and not a simulation either way: the
-- tower is live at configurations no strategy environment matches, and `EnvSt`
-- holds trees no watch produces.
--
-- Resources are NOT this module's subject, and the three quantities stay
-- apart: the embedded strategy's honest queries (preserved exactly — the watch
-- asks what `d` asks, `Strategy.asks≤-watch`), the internal flag retrieval
-- (one activation of the private port, invisible here because it never leaves
-- the collapsed context), and the coarse compiled certificate `Hits.κμ`.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; _∨_; false; true)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐; λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Machine.Slide using (λ-nat)
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Quantitative.Hits using (eventRun)
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy using (adequacy)
open import CategoricalCrypto.UC.Seam.Plug

import Categories.Category.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Monitor.Agree where

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private
  module 𝒫 = Category 𝒫ᴵ
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})

------------------------------------------------------------------------
-- A simulation out of a state function

-- `Machines.Pointwise.⊗-pureˡ` names the shape every `_≲_`'s `θ ⊗₁ id` takes
-- at a point; this packages it, so a consumer supplies only the three
-- pointwise laws.  The two `⊛` reductions beside it are `Plug.Plugged`'s
-- `point-red` at an arbitrary pair of states.
simFn : {S T : State} {X Y : Set}
        {k : obj S × X → Dₚ (obj S × Y)} {k′ : obj T × X → Dₚ (obj T × Y)}
        (h : obj S → obj T)
      → ((s : obj S) → (returnₚ (h s) >>=ₚ discard T) ≈ₚ discard S s)
      → ((x : ⊤ᵛ) → (point S x >>=ₚ λ s → returnₚ (h s)) ≈ₚ point T x)
      → ((p : obj S × X) → (k p >>=ₚ λ r → returnₚ (h (proj₁ r) , proj₂ r))
                           ≈ₚ k′ (h (proj₁ p) , proj₂ p))
      → mk S k ≲ mk T k′
simFn {k′ = k′} h hd hp hs = sim (Col.K.pureᵏ h) (KP.structural h) hd hp law
  where
  law : (p : _) → _
  law p = bindᶠ (Col.⊗-pureˡ h) ⟨≈⟩ hs p
    ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ h p) ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p) , proj₂ p) k′)

point-⊛ : (S T : State) (x : ⊤ᵛ)
        → point (S ⊛ T) x ≈ₚ (point S ttᵛ >>=ₚ λ a → point T x >>=ₚ λ b → returnₚ (a , b))
point-⊛ S T x = >>=ₚ-identityˡ (ttᵛ , x) _

discard-⊛ : (S T : State)
          → ((s : obj S) → discard S s ≈ₚ returnₚ ttᵛ)
          → ((t : obj T) → discard T t ≈ₚ returnₚ ttᵛ)
          → (z : obj (S ⊛ T)) → discard (S ⊛ T) z ≈ₚ returnₚ ttᵛ
discard-⊛ S T hs ht (a , b) =
  bindˣ ( bindˣ (hs a) ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _
     ⟨≈⟩ bindˣ (ht b) ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

------------------------------------------------------------------------
-- A strategy embedded as a test

-- `UC.Seam.strategyEnv` read on the compiler's own domain.  The ancilla is
-- trivial, so the test is the strategy environment with the empty summand
-- eliminated; `stratTest-embeds` is that reading.
outᵁ : (B : Iface) → Neg B ⊎ Bool → (Pos unitᴵ ⊎ Neg B) ⊎ Bool
outᵁ B (inj₁ q) = inj₁ (inj₂ q)
outᵁ B (inj₂ v) = inj₂ v

stepᵁ : (B : Iface) → EnvSt B × ((Pos unitᴵ ⊎ Pos B) ⊎ ⊤)
      → Dₚ (EnvSt B × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool))
stepᵁ B (se , inj₁ (inj₁ ()))
stepᵁ B (se , inj₁ (inj₂ p)) = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₁ p))
stepᵁ B (se , inj₂ _)        = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₂ tt))

stratTest : (B : Iface) → Strat (Neg B) (Pos B) → Proc (unitᴵ ⊗ᴵ B) Ωᴵ
stratTest B d = mk (stateˢ B d) (stepᵁ B)

stratTest-embeds : (B : Iface) (d : Strat (Neg B) (Pos B))
                 → 𝒫._≈_ {unitᴵ ⊗ᴵ B} {Ωᴵ} (stratTest B d) (strategyEnv B d 𝒫.∘ λᴵ⇒)
stratTest-embeds B d =
  ⟺ᴹ (∘-wireᴹ [ ⊥-elim , id ] inj₂ (strategyEnv B d) ○ᴹ ≲⇒≈ᴹ (mk-cong pt))
  where
  pt : (z : _) → _
  pt (se , inj₁ (inj₁ ()))
  pt (se , inj₁ (inj₂ p)) =
    map-eq (stepˢ B (se , inj₁ p)) _ _ λ where (_ , inj₁ _) → refl
                                               (_ , inj₂ _) → refl
  pt (se , inj₂ _) =
    map-eq (stepˢ B (se , inj₂ tt)) _ _ λ where (_ , inj₁ _) → refl
                                                (_ , inj₂ _) → refl

------------------------------------------------------------------------
-- The test with the flag reader over it, as one machine

-- `flagReadᴹ ∘ subᴵ E` collapsed: the loop between the two runs at most two
-- passes, so the composite's step is the test's own, post-processed by where
-- the flag reader is in its cycle.
module Read (D : Iface) (E : Proc D Ωᴵ) where

  efOut : FlagSt → St E × (Neg D ⊎ Bool) → Dₚ ((FlagSt × St E) × ((Neg D ⊎ ⊤) ⊎ Bool))
  efOut fs    (se , inj₁ q) = returnₚ ((fs    , se) , inj₁ (inj₁ q))
  efOut waitE (se , inj₂ _) = returnₚ ((waitF , se) , inj₁ (inj₂ tt))
  efOut idle  (se , inj₂ _) = botₚ
  efOut waitF (se , inj₂ _) = botₚ

  readStep : (FlagSt × St E) × ((Pos D ⊎ Bool) ⊎ ⊤)
           → Dₚ ((FlagSt × St E) × ((Neg D ⊎ ⊤) ⊎ Bool))
  readStep ((fs    , se) , inj₁ (inj₁ p)) = step E (se , inj₁ p) >>=ₚ efOut fs
  readStep ((idle  , se) , inj₁ (inj₂ _)) = botₚ
  readStep ((waitE , se) , inj₁ (inj₂ _)) = botₚ
  readStep ((waitF , se) , inj₁ (inj₂ b)) = returnₚ ((idle , se) , inj₂ b)
  readStep ((idle  , se) , inj₂ _)        = step E (se , inj₂ tt) >>=ₚ efOut waitE
  readStep ((waitE , se) , inj₂ _)        = botₚ
  readStep ((waitF , se) , inj₂ _)        = botₚ

  readᴹ : Proc (D ⊗ᴵ Flagᴵ) Ωᴵ
  readᴹ = mk (Col.Sᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                     flagReadᴹ (subᴵ E))
             readStep

  private
    Sᴿ : State
    Sᴿ = Col.Sᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                flagReadᴹ (subᴵ E)

    kᴿ : obj Sᴿ × (((Pos D ⊎ Bool) ⊎ ⊤) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool)))
       → Dₚ (obj Sᴿ × (((Neg D ⊎ ⊤) ⊎ Bool) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool))))
    kᴿ = Col.kᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                flagReadᴹ (subᴵ E)

  open Loop ((Pos D ⊎ Bool) ⊎ ⊤) ((Neg D ⊎ ⊤) ⊎ Bool) ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool)) Sᴿ kᴿ

  private
    -- Where the test's own emission goes: a query leaves, a verdict re-enters
    -- the loop at the flag reader.
    relayᴰ : FlagSt → St E × (Neg D ⊎ Bool)
           → Dₚ ((FlagSt × St E) × (((Neg D ⊎ ⊤) ⊎ Bool) ⊎ ((⊤ ⊎ ⊤) ⊎ (Bool ⊎ Bool))))
    relayᴰ fs (se , inj₁ q) = returnₚ ((fs , se) , inj₁ (inj₁ (inj₁ q)))
    relayᴰ fs (se , inj₂ v) = returnₚ ((fs , se) , inj₂ (inj₂ (inj₁ v)))

    -- The flag reader answering a verdict: it asks the flag, and the ancilla
    -- relay passes that query straight down.
    verdict-pass : (fs : FlagSt) (se : St E) (v : Bool)
                 → iterₚ body ((fs , se) , inj₂ (inj₁ v)) ≈ₚ efOut fs (se , inj₂ v)
    verdict-pass idle  se v = loop-bot (idle  , se) (inj₂ (inj₁ v)) (bot-bind-≈ₚ _)
    verdict-pass waitF se v = loop-bot (waitF , se) (inj₂ (inj₁ v)) (bot-bind-≈ₚ _)
    verdict-pass waitE se v =
        loop-pass (waitE , se) (inj₂ (inj₁ v)) (waitF , se) (inj₂ (inj₁ (inj₂ tt)))
                  (>>=ₚ-identityˡ (waitF , inj₁ (inj₂ tt)) _)
      ⟨≈⟩ loop-pass (waitF , se) (inj₁ (inj₂ tt)) (waitF , se) (inj₁ (inj₁ (inj₂ tt)))
                    (>>=ₚ-identityˡ (se , inj₁ (inj₂ tt)) _)

    pump : (fs : FlagSt) (dE : Dₚ (St E × (Neg D ⊎ Bool)))
         → ((dE >>=ₚ relayᴰ fs) >>=ₚ contᵢ body) ≈ₚ (dE >>=ₚ efOut fs)
    pump fs dE = >>=ₚ-assoc dE (relayᴰ fs) (contᵢ body) ⟨≈⟩ bindᶠ out-case
      where
      out-case : (z : St E × (Neg D ⊎ Bool))
               → (relayᴰ fs z >>=ₚ contᵢ body) ≈ₚ efOut fs z
      out-case (se , inj₁ q) = >>=ₚ-identityˡ ((fs , se) , inj₁ (inj₁ (inj₁ q))) _
      out-case (se , inj₂ v) = >>=ₚ-identityˡ ((fs , se) , inj₂ (inj₂ (inj₁ v))) _
                         ⟨≈⟩ verdict-pass fs se v

    -- The ancilla relay, entered from below or from the flag reader's tick.
    relay-red : (fs : FlagSt) (se : St E) (x : Pos D ⊎ ⊤)
              → (step (subᴵ E) (se , Sum.map inj₁ inj₁ x) >>=ₚ
                 λ r → returnₚ ((fs , proj₁ r) , Col.outᶠ (proj₂ r)))
                ≈ₚ (step E (se , x) >>=ₚ relayᴰ fs)
    relay-red fs se (inj₁ p) = bind-map (step E (se , inj₁ p)) _ _
                         ⟨≈⟩ bindᶠ λ where (_ , inj₁ _) → ≈refl
                                           (_ , inj₂ _) → ≈refl
    relay-red fs se (inj₂ _) = bind-map (step E (se , inj₂ tt)) _ _
                         ⟨≈⟩ bindᶠ λ where (_ , inj₁ _) → ≈refl
                                           (_ , inj₂ _) → ≈refl

    read-step : (z : obj Sᴿ × ((Pos D ⊎ Bool) ⊎ ⊤)) → step tracedᴹ z ≈ₚ readStep z
    read-step ((fs , se) , inj₁ (inj₁ p)) =
        step-red (fs , se) (inj₁ (inj₁ p))
      ⟨≈⟩ bindˣ (relay-red fs se (inj₁ p)) ⟨≈⟩ pump fs (step E (se , inj₁ p))
    read-step ((idle  , se) , inj₁ (inj₂ b)) =
        step-red (idle , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((idle , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-bot (idle , se) (inj₂ (inj₂ b)) (bot-bind-≈ₚ _)
    read-step ((waitE , se) , inj₁ (inj₂ b)) =
        step-red (waitE , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitE , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-bot (waitE , se) (inj₂ (inj₂ b)) (bot-bind-≈ₚ _)
    read-step ((waitF , se) , inj₁ (inj₂ b)) =
        step-red (waitF , se) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (se , inj₂ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitF , se) , inj₂ (inj₂ (inj₂ b))) _
      ⟨≈⟩ loop-pass (waitF , se) (inj₂ (inj₂ b)) (idle , se) (inj₁ (inj₂ b))
                    (>>=ₚ-identityˡ (idle , inj₂ b) _)
    read-step ((idle , se) , inj₂ _) =
        step-red (idle , se) (inj₂ tt)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (waitE , inj₁ (inj₁ tt)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((waitE , se) , inj₂ (inj₁ (inj₁ tt))) _
      ⟨≈⟩ loop-fix (waitE , se) (inj₁ (inj₁ tt))
      ⟨≈⟩ bindˣ (relay-red waitE se (inj₂ tt))
      ⟨≈⟩ pump waitE (step E (se , inj₂ tt))
    read-step ((waitE , se) , inj₂ _) =
        step-red (waitE , se) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    read-step ((waitF , se) , inj₂ _) =
        step-red (waitF , se) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _

  read-collapse : 𝒫._≈_ {D ⊗ᴵ Flagᴵ} {Ωᴵ} (flagReadᴹ 𝒫.∘ subᴵ E) readᴹ
  read-collapse =
       ⟺ᴹ (Col.compose-raw≈∘ᴳ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                              flagReadᴹ (subᴵ E))
    ○ᴹ Col.collapseᵀ {Pos D ⊎ Bool} {Neg D ⊎ ⊤} {Bool ⊎ Bool} {⊤ ⊎ ⊤} {Bool} {⊤}
                     flagReadᴹ (subᴵ E)
    ○ᴹ ≲⇒≈ᴹ (mk-cong read-step)

------------------------------------------------------------------------
-- The monitor below it, as one machine

-- `monitorᴹ` with the compiler's two wires absorbed into its interface.
monStep : (B : Iface) (report : Neg B → Pos B → Bool)
        → MonSt B × (Pos B ⊎ ((Neg unitᴵ ⊎ Neg B) ⊎ ⊤))
        → Dₚ (MonSt B × (Neg B ⊎ ((Pos unitᴵ ⊎ Pos B) ⊎ Bool)))
monStep B report (_              , inj₂ (inj₁ (inj₁ ())))
monStep B report ((acc , _)      , inj₂ (inj₁ (inj₂ q))) = returnₚ ((acc , just q) , inj₁ q)
monStep B report ((acc , mq)     , inj₂ (inj₂ _))        = returnₚ ((acc , mq) , inj₂ (inj₂ acc))
monStep B report ((acc , just q) , inj₁ a) =
  returnₚ ((acc ∨ report q a , nothing) , inj₂ (inj₁ (inj₂ a)))
monStep B report ((_ , nothing)  , inj₁ _)               = botₚ

monᴹ : (B : Iface) (report : Neg B → Pos B → Bool) → Proc B ((unitᴵ ⊗ᴵ B) ⊗ᴵ Flagᴵ)
monᴹ B report = mk (state (monitorᴹ report)) (monStep B report)

mon-wire : (B : Iface) (report : Neg B → Pos B → Bool)
         → 𝒫._≈_ {B} {(unitᴵ ⊗ᴵ B) ⊗ᴵ Flagᴵ}
             (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ monitorᴹ report)) (monᴹ B report)
mon-wire B report =
     𝒫.∘-resp-≈ʳ (wire-∘ᴹ inj₂ [ ⊥-elim , id ] (monitorᴹ report))
  ○ᴹ wire-∘ᴹ ⊎assocˡ ⊎assocʳ (sandwichᴹ (monitorᴹ report) i₁ o₁)
  ○ᴹ sandwich-∘ (monitorᴹ report) i₁ o₁ i₂ o₂
  ○ᴹ ≲⇒≈ᴹ (mk-cong pt)
  where
  i₁ : Pos B ⊎ Neg (unitᴵ ⊗ᴵ (B ⊗ᴵ Flagᴵ)) → Pos B ⊎ Neg (B ⊗ᴵ Flagᴵ)
  i₁ = Sum.map id [ ⊥-elim , id ]

  o₁ : Neg B ⊎ Pos (B ⊗ᴵ Flagᴵ) → Neg B ⊎ Pos (unitᴵ ⊗ᴵ (B ⊗ᴵ Flagᴵ))
  o₁ = Sum.map id inj₂

  i₂ : Pos B ⊎ Neg ((unitᴵ ⊗ᴵ B) ⊗ᴵ Flagᴵ) → Pos B ⊎ Neg (unitᴵ ⊗ᴵ (B ⊗ᴵ Flagᴵ))
  i₂ = Sum.map id ⊎assocʳ

  o₂ : Neg B ⊎ Pos (unitᴵ ⊗ᴵ (B ⊗ᴵ Flagᴵ)) → Neg B ⊎ Pos ((unitᴵ ⊗ᴵ B) ⊗ᴵ Flagᴵ)
  o₂ = Sum.map id ⊎assocˡ

  pt : (z : _) → _
  pt (_              , inj₂ (inj₁ (inj₁ ())))
  pt ((acc , _)      , inj₂ (inj₁ (inj₂ q))) = >>=ₚ-identityˡ ((acc , just q) , inj₁ q) _
  pt ((acc , mq)     , inj₂ (inj₂ _))        = >>=ₚ-identityˡ ((acc , mq) , inj₂ (inj₂ acc)) _
  pt ((acc , just q) , inj₁ a) =
    >>=ₚ-identityˡ ((acc ∨ report q a , nothing) , inj₂ (inj₁ a)) _
  pt ((_ , nothing)  , inj₁ _)               = bot-bind-≈ₚ _

------------------------------------------------------------------------
-- The whole compiled context, as one machine

module Watch (B : Iface) (report : Neg B → Pos B → Bool)
             (E : Proc (unitᴵ ⊗ᴵ B) Ωᴵ) where

  open Read (unitᴵ ⊗ᴵ B) E

  WCfg : Set
  WCfg = (FlagSt × St E) × MonSt B

  -- What the compiled context does with one emission of the test: a query
  -- goes down through the monitor, a verdict is DISCARDED and answered by the
  -- accumulated flag instead.
  wPass : FlagSt → MonSt B → St E × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool)
        → Dₚ (WCfg × (Neg B ⊎ Bool))
  wPass fs    _          (se , inj₁ (inj₁ ()))
  wPass fs    (acc , _)  (se , inj₁ (inj₂ q)) = returnₚ (((fs , se) , (acc , just q)) , inj₁ q)
  wPass waitE (acc , mq) (se , inj₂ _) = returnₚ (((idle , se) , (acc , mq)) , inj₂ acc)
  wPass idle  _          (se , inj₂ _) = botₚ
  wPass waitF _          (se , inj₂ _) = botₚ

  -- Split before the state, so that the case tree branches on the ACTIVATION
  -- first: a tree that splits the flag-reader state first is stuck wherever a
  -- consumer holds that state abstract.
  watchTick : WCfg → Dₚ (WCfg × (Neg B ⊎ Bool))
  watchTick ((idle  , se) , m) = step E (se , inj₂ tt) >>=ₚ wPass waitE m
  watchTick ((waitE , se) , m) = botₚ
  watchTick ((waitF , se) , m) = botₚ

  watchAns : WCfg → Pos B → Dₚ (WCfg × (Neg B ⊎ Bool))
  watchAns ((fs , se) , (acc , just q)) p =
    step E (se , inj₁ (inj₂ p)) >>=ₚ wPass fs (acc ∨ report q p , nothing)
  watchAns ((fs , se) , (acc , nothing)) p = botₚ

  watchStep : WCfg × (Pos B ⊎ ⊤) → Dₚ (WCfg × (Neg B ⊎ Bool))
  watchStep (cfg , inj₁ p) = watchAns cfg p
  watchStep (cfg , inj₂ _) = watchTick cfg

  watchᴹ : Proc B Ωᴵ
  watchᴹ = mk (Col.Sᴳ {Pos B} {Neg B} {(Pos unitᴵ ⊎ Pos B) ⊎ Bool}
                      {(Neg unitᴵ ⊎ Neg B) ⊎ ⊤} {Bool} {⊤} readᴹ (monᴹ B report))
              watchStep

  private
    Sᵂ : State
    Sᵂ = Col.Sᴳ {Pos B} {Neg B} {(Pos unitᴵ ⊎ Pos B) ⊎ Bool}
                {(Neg unitᴵ ⊎ Neg B) ⊎ ⊤} {Bool} {⊤} readᴹ (monᴹ B report)

    Xᵂ : Set
    Xᵂ = ((Neg unitᴵ ⊎ Neg B) ⊎ ⊤) ⊎ ((Pos unitᴵ ⊎ Pos B) ⊎ Bool)

    kᵂ : obj Sᵂ × ((Pos B ⊎ ⊤) ⊎ Xᵂ) → Dₚ (obj Sᵂ × ((Neg B ⊎ Bool) ⊎ Xᵂ))
    kᵂ = Col.kᴳ {Pos B} {Neg B} {(Pos unitᴵ ⊎ Pos B) ⊎ Bool}
                {(Neg unitᴵ ⊎ Neg B) ⊎ ⊤} {Bool} {⊤} readᴹ (monᴹ B report)

  open Loop (Pos B ⊎ ⊤) (Neg B ⊎ Bool) Xᵂ Sᵂ kᵂ

  private
    jg : MonSt B → (FlagSt × St E) × (((Neg unitᴵ ⊎ Neg B) ⊎ ⊤) ⊎ Bool)
       → Dₚ (obj Sᵂ × ((Neg B ⊎ Bool) ⊎ Xᵂ))
    jg m r = returnₚ ((proj₁ r , m) , Col.outᵍ (proj₂ r))

    -- The emission's own fate, once the flag reader has produced it.
    wpass-red : (fs : FlagSt) (m : MonSt B) (z : St E × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool))
              → ((efOut fs z >>=ₚ jg m) >>=ₚ contᵢ body) ≈ₚ wPass fs m z
    wpass-red fs    _          (se , inj₁ (inj₁ ()))
    wpass-red fs    (acc , mq) (se , inj₁ (inj₂ q)) =
        bindˣ (>>=ₚ-identityˡ ((fs , se) , inj₁ (inj₁ (inj₂ q))) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((fs , se) , (acc , mq)) , inj₂ (inj₁ (inj₁ (inj₂ q)))) _
      ⟨≈⟩ loop-pass ((fs , se) , (acc , mq)) (inj₁ (inj₁ (inj₂ q)))
                    ((fs , se) , (acc , just q)) (inj₁ (inj₁ q))
                    (>>=ₚ-identityˡ ((acc , just q) , inj₁ q) _)
    wpass-red idle  m          (se , inj₂ v) = bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    wpass-red waitF m          (se , inj₂ v) = bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    wpass-red waitE (acc , mq) (se , inj₂ v) =
        bindˣ (>>=ₚ-identityˡ ((waitF , se) , inj₁ (inj₂ tt)) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((waitF , se) , (acc , mq)) , inj₂ (inj₁ (inj₂ tt))) _
      ⟨≈⟩ loop-pass ((waitF , se) , (acc , mq)) (inj₁ (inj₂ tt))
                    ((waitF , se) , (acc , mq)) (inj₂ (inj₂ (inj₂ acc)))
                    (>>=ₚ-identityˡ ((acc , mq) , inj₂ (inj₂ acc)) _)
      ⟨≈⟩ loop-pass ((waitF , se) , (acc , mq)) (inj₂ (inj₂ acc))
                    ((idle , se) , (acc , mq)) (inj₁ (inj₂ acc))
                    (>>=ₚ-identityˡ ((idle , se) , inj₂ acc) _)

    wpump : (fs : FlagSt) (m : MonSt B) (dE : Dₚ (St E × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool)))
          → (((dE >>=ₚ efOut fs) >>=ₚ jg m) >>=ₚ contᵢ body) ≈ₚ (dE >>=ₚ wPass fs m)
    wpump fs m dE =
        bindˣ (>>=ₚ-assoc dE (efOut fs) (jg m))
      ⟨≈⟩ >>=ₚ-assoc dE _ (contᵢ body)
      ⟨≈⟩ bindᶠ (wpass-red fs m)

    watch-step : (z : obj Sᵂ × (Pos B ⊎ ⊤)) → step tracedᴹ z ≈ₚ watchStep z
    watch-step (((idle , se) , m) , inj₂ _) =
        step-red ((idle , se) , m) (inj₂ tt) ⟨≈⟩ wpump waitE m (step E (se , inj₂ tt))
    watch-step (((waitE , se) , m) , inj₂ _) =
        step-red ((waitE , se) , m) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    watch-step (((waitF , se) , m) , inj₂ _) =
        step-red ((waitF , se) , m) (inj₂ tt) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _
    watch-step (((fs , se) , (acc , just q)) , inj₁ p) =
        step-red ((fs , se) , (acc , just q)) (inj₁ p)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ((acc ∨ report q p , nothing) , inj₂ (inj₁ (inj₂ p))) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((fs , se) , (acc ∨ report q p , nothing))
                         , inj₂ (inj₂ (inj₁ (inj₂ p)))) _
      ⟨≈⟩ loop-fix ((fs , se) , (acc ∨ report q p , nothing)) (inj₂ (inj₁ (inj₂ p)))
      ⟨≈⟩ wpump fs (acc ∨ report q p , nothing) (step E (se , inj₁ (inj₂ p)))
    watch-step (((fs , se) , (acc , nothing)) , inj₁ p) =
        step-red ((fs , se) , (acc , nothing)) (inj₁ p)
      ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _

  watch-discard : ((se : St E) → discard (state E) se ≈ₚ returnₚ ttᵛ)
                → (z : obj (state watchᴹ)) → discard (state watchᴹ) z ≈ₚ returnₚ ttᵛ
  watch-discard he =
    discard-⊛ (state readᴹ) (state (monᴹ B report))
      (discard-⊛ (state flagReadᴹ) (state E) (λ _ → ≈refl) he) (λ _ → ≈refl)

  watch-point : point (state watchᴹ) ttᵛ
              ≈ₚ (point (state E) ttᵛ >>=ₚ λ se → returnₚ ((idle , se) , (false , nothing)))
  watch-point =
      point-⊛ (state readᴹ) (state (monᴹ B report)) ttᵛ
    ⟨≈⟩ bindˣ ( point-⊛ (state flagReadᴹ) (state E) ttᵛ
           ⟨≈⟩ >>=ₚ-identityˡ idle _)
    ⟨≈⟩ >>=ₚ-assoc (point (state E) ttᵛ) _ _
    ⟨≈⟩ bindᶠ (λ se → >>=ₚ-identityˡ (idle , se) _
                 ⟨≈⟩ >>=ₚ-identityˡ (false , nothing) _)

  watch-collapse : 𝒫._≈_ {B} {Ωᴵ} (readᴹ 𝒫.∘ monᴹ B report) watchᴹ
  watch-collapse =
       ⟺ᴹ (Col.compose-raw≈∘ᴳ {Pos B} {Neg B} {(Pos unitᴵ ⊎ Pos B) ⊎ Bool}
                              {(Neg unitᴵ ⊎ Neg B) ⊎ ⊤} {Bool} {⊤} readᴹ (monᴹ B report))
    ○ᴹ Col.collapseᵀ {Pos B} {Neg B} {(Pos unitᴵ ⊎ Pos B) ⊎ Bool}
                     {(Neg unitᴵ ⊎ Neg B) ⊎ ⊤} {Bool} {⊤} readᴹ (monᴹ B report)
    ○ᴹ ≲⇒≈ᴹ (mk-cong watch-step)

------------------------------------------------------------------------
-- The reachable configurations, and the span through them

-- The configurations the compiled context actually reaches: an accumulator
-- beside the rest of the strategy tree, or beside the query an answer is
-- still owed to.  Neither the compiled context nor `strategyEnv` simulates
-- the other — the composite is live at configurations no strategy
-- environment matches (its flag reader mid-cycle), and `EnvSt` holds trees no
-- watch produces — so the two are tied by a SPAN out of this.
data WSt (B : Iface) : Set where
  wplay : Bool → Strat (Neg B) (Pos B) → WSt B
  wsusp : Bool → Neg B → (Pos B → Strat (Neg B) (Pos B)) → WSt B

module Reach (B : Iface) (report : Neg B → Pos B → Bool) where

  playᵂ : Bool → Strat (Neg B) (Pos B) → Dₚ (WSt B × (Neg B ⊎ Bool))
  playᵂ acc e@(out _)  = returnₚ (wplay acc e , inj₂ acc)
  playᵂ acc (ask q k)  = returnₚ (wsusp acc q k , inj₁ q)
  playᵂ acc (coin μ k) = coinₚ μ >>=ₚ λ b → playᵂ acc (k b)

  stepᵂ : WSt B × (Pos B ⊎ ⊤) → Dₚ (WSt B × (Neg B ⊎ Bool))
  stepᵂ (wplay acc e   , inj₂ _) = playᵂ acc e
  stepᵂ (wsusp acc q k , inj₁ p) = playᵂ (acc ∨ report q p) (k p)
  stepᵂ (wplay _ _     , inj₁ _) = botₚ
  stepᵂ (wsusp _ _ _   , inj₂ _) = botₚ

  stateᴿ : Strat (Neg B) (Pos B) → State
  stateᴿ d = record
    { obj = WSt B ; point = λ _ → returnₚ (wplay false d) ; discard = λ _ → returnₚ ttᵛ }

  reachᴹ : Strat (Neg B) (Pos B) → Proc B Ωᴵ
  reachᴹ d = mk (stateᴿ d) stepᵂ

module Span (B : Iface) (report : Neg B → Pos B → Bool) (d : Strat (Neg B) (Pos B)) where

  open Reach B report
  open Watch B report (stratTest B d)

  private
    ι : WSt B → WCfg
    ι (wplay acc e)   = (idle  , play e) , (acc , nothing)
    ι (wsusp acc q k) = (waitE , susp k) , (acc , just q)

    ι-play : (acc : Bool) (e : Strat (Neg B) (Pos B))
           → mapₚ (λ r → ι (proj₁ r) , proj₂ r) (playᵂ acc e)
             ≈ₚ (playˢ B e >>=ₚ λ z → wPass waitE (acc , nothing)
                                            (proj₁ z , outᵁ B (proj₂ z)))
    ι-play acc (out v)    = >>=ₚ-identityˡ (wplay acc (out v) , inj₂ acc) _
                      ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (play (out v) , inj₂ v) _)
    ι-play acc (ask q k)  = >>=ₚ-identityˡ (wsusp acc q k , inj₁ q) _
                      ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (susp k , inj₁ q) _)
    ι-play acc (coin μ k) = >>=ₚ-assoc (coinₚ μ) _ _
                      ⟨≈⟩ bindᶠ (λ b → ι-play acc (k b))
                      ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)

    ι-step : (z : WSt B × (Pos B ⊎ ⊤))
           → (stepᵂ z >>=ₚ λ r → returnₚ (ι (proj₁ r) , proj₂ r))
             ≈ₚ watchStep (ι (proj₁ z) , proj₂ z)
    ι-step (wplay acc e   , inj₂ _) = ι-play acc e ⟨≈⟩ ≈sym (bind-map (playˢ B e) _ _)
    ι-step (wsusp acc q k , inj₁ p) = ι-play (acc ∨ report q p) (k p)
                                ⟨≈⟩ ≈sym (bind-map (playˢ B (k p)) _ _)
    ι-step (wplay _ _     , inj₁ _) = bot-bind-≈ₚ _
    ι-step (wsusp _ _ _   , inj₂ _) = bot-bind-≈ₚ _

    reach≲watch : reachᴹ d ≲ watchᴹ
    reach≲watch = simFn ι
      (λ s → >>=ₚ-identityˡ (ι s) _ ⟨≈⟩ watch-discard (λ _ → ≈refl) (ι s))
      (λ _ → >>=ₚ-identityˡ (wplay false d) _
         ⟨≈⟩ ≈sym (watch-point ⟨≈⟩ >>=ₚ-identityˡ (play d) _))
      ι-step

  module _ (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
           (iw : IsWatch report w) where

    private
      eo = proj₁ iw
      ea = proj₁ (proj₂ iw)
      ec = proj₂ (proj₂ iw)

      κ : WSt B → EnvSt B
      κ (wplay acc e)   = play (w acc e)
      κ (wsusp acc q k) = susp λ p → w (acc ∨ report q p) (k p)

      κ-play : (acc : Bool) (e : Strat (Neg B) (Pos B))
             → mapₚ (λ r → κ (proj₁ r) , proj₂ r) (playᵂ acc e) ≈ₚ playˢ B (w acc e)
      κ-play acc (out v) =
          >>=ₚ-identityˡ (wplay acc (out v) , inj₂ acc) _
        ⟨≈⟩ ret≡ (cong (λ z → play z , inj₂ acc) (eo acc v))
        ⟨≈⟩ ≈sym (≡⇒≈ₚ (cong (playˢ B) (eo acc v)))
      κ-play acc (ask q k) =
          >>=ₚ-identityˡ (wsusp acc q k , inj₁ q) _
        ⟨≈⟩ ≈sym (≡⇒≈ₚ (cong (playˢ B) (ea acc q k)))
      κ-play acc (coin μ k) =
          >>=ₚ-assoc (coinₚ μ) _ _
        ⟨≈⟩ bindᶠ (λ b → κ-play acc (k b))
        ⟨≈⟩ ≈sym (≡⇒≈ₚ (cong (playˢ B) (ec acc μ k)))

      κ-step : (z : WSt B × (Pos B ⊎ ⊤))
             → (stepᵂ z >>=ₚ λ r → returnₚ (κ (proj₁ r) , proj₂ r))
               ≈ₚ stepˢ B (κ (proj₁ z) , proj₂ z)
      κ-step (wplay acc e   , inj₂ _) = κ-play acc e
      κ-step (wsusp acc q k , inj₁ p) = κ-play (acc ∨ report q p) (k p)
      κ-step (wplay _ _     , inj₁ _) = bot-bind-≈ₚ _
      κ-step (wsusp _ _ _   , inj₂ _) = bot-bind-≈ₚ _

      reach≲env : reachᴹ d ≲ strategyEnv B (w false d)
      reach≲env = simFn κ (λ s → >>=ₚ-identityˡ (κ s) _)
                          (λ _ → >>=ₚ-identityˡ (wplay false d) _) κ-step

    -- The compiled context and the watched strategy environment are the same
    -- machine of the layer's own equality.
    span : 𝒫._≈_ {B} {Ωᴵ} watchᴹ (strategyEnv B (w false d))
    span = ≲⇒≈ᴹ˘ reach≲watch ○ᴹ ≲⇒≈ᴹ reach≲env

------------------------------------------------------------------------
-- Agreement

-- The closure of a strategy context: no ancilla, nothing below the process.
m₀ : Proc unitᴵ (unitᴵ ⊗ᴵ unitᴵ)
m₀ = λᴵ⇐

-- The compiled monitored experiment is the watched environment over the
-- process: the two unitors and the reassociator absorb into the monitor, and
-- the compiler's three machines collapse into one.
tower : (B : Iface) (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B)
        (E : Proc (unitᴵ ⊗ᴵ B) Ωᴵ)
      → 𝒫._≈_ {unitᴵ} {Ωᴵ}
          ((compileᴹ unitᴵ B (monitorᴹ report) E 𝒫.∘ T₁ᴵ unitᴵ u) 𝒫.∘ m₀)
          (Watch.watchᴹ B report E 𝒫.∘ u)
tower B report u E =
     𝒫.assoc
  ○ᴹ 𝒫.∘-resp-≈ʳ (⟺ᴹ (λ-nat u))
  ○ᴹ 𝒫.sym-assoc
  ○ᴹ 𝒫.∘-resp-≈ˡ
       ( 𝒫.assoc
      ○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.assoc
                   ○ᴹ 𝒫.∘-resp-≈ʳ ( 𝒫.assoc
                                 ○ᴹ 𝒫.∘-resp-≈ʳ (⟺ᴹ (λ-nat (monitorᴹ report)))
                                 ○ᴹ mon-wire B report))
      ○ᴹ 𝒫.sym-assoc
      ○ᴹ 𝒫.∘-resp-≈ˡ (Read.read-collapse (unitᴵ ⊗ᴵ B) E)
      ○ᴹ Watch.watch-collapse B report E)

-- Obligation 4 of `docs/event-bounds-in-setup.md` §2.  `w` is any transformer
-- satisfying the watch equations, so this applies verbatim to
-- `Examples.ChimericLedger.Observable.auditWatchFrom`.
agree : (B : Iface) (report : Neg B → Pos B → Bool)
        (w : Bool → Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → IsWatch report w
      → (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B))
      → eventRun unitᴵ u (monitorᴹ report) (stratTest B d) m₀ ≈ₚ runᴹ u (w false d)
agree B report w iw u d =
    runᴹ-resp-≈ᴹ {Ωᴵ}
      (tower B report u (stratTest B d) ○ᴹ 𝒫.∘-resp-≈ˡ (Span.span B report d w iw))
      (ask tt out)
  ⟨≈⟩ Plugged.collapse B (strategyEnv B (w false d)) u
  ⟨≈⟩ adequacy B u (w false d)

------------------------------------------------------------------------
-- The three experiments the compiler is accepted on

-- A process that answers `true` once and then diverges: enough to separate
-- the returning, querying and diverging cases at one interface.
data OneSt : Set where fresh done : OneSt

B₀ : Iface
B₀ = Bool ⇿ ⊤

rep₀ : Neg B₀ → Pos B₀ → Bool
rep₀ _ a = a

oneStep : OneSt × (Pos unitᴵ ⊎ Neg B₀) → Dₚ (OneSt × (Neg unitᴵ ⊎ Pos B₀))
oneStep (fresh , inj₂ _) = returnₚ (done , inj₂ true)
oneStep _                = botₚ

oneᴹ : Proc unitᴵ B₀
oneᴹ = mk (record { obj = OneSt ; point = λ _ → returnₚ fresh
                  ; discard = λ _ → returnₚ ttᵛ }) oneStep

agree₀ : (d : Strat (Neg B₀) (Pos B₀))
       → eventRun unitᴵ oneᴹ (monitorᴹ rep₀) (stratTest B₀ d) m₀
         ≈ₚ runᴹ oneᴹ (watchFrom rep₀ false d)
agree₀ = agree B₀ rep₀ (watchFrom rep₀) (watchFrom-IsWatch rep₀) oneᴹ

-- Returning: the test's own verdict is discarded and the empty accumulator
-- reported in its place.
monitor-returns : eventRun unitᴵ oneᴹ (monitorᴹ rep₀) (stratTest B₀ (out true)) m₀
                ≈ₚ returnₚ false
monitor-returns = agree₀ (out true) ⟨≈⟩ >>=ₚ-identityˡ fresh _

-- Querying: the answer is relayed and the report read off the (query, answer)
-- pair, so the bit that comes back is `rep₀`'s verdict on it.
monitor-queries :
    eventRun unitᴵ oneᴹ (monitorᴹ rep₀) (stratTest B₀ (ask tt λ _ → out false)) m₀
  ≈ₚ returnₚ true
monitor-queries = agree₀ (ask tt λ _ → out false)
            ⟨≈⟩ >>=ₚ-identityˡ fresh _
            ⟨≈⟩ >>=ₚ-identityˡ (done , inj₂ true) _

-- Diverging: the first answer RAISES the flag and the second query is never
-- answered — and the raised flag is not reported.
monitor-diverges :
    eventRun unitᴵ oneᴹ (monitorᴹ rep₀)
             (stratTest B₀ (ask tt λ _ → ask tt λ _ → out false)) m₀
  ≈ₚ botₚ
monitor-diverges = agree₀ (ask tt λ _ → ask tt λ _ → out false)
             ⟨≈⟩ >>=ₚ-identityˡ fresh _
             ⟨≈⟩ >>=ₚ-identityˡ (done , inj₂ true) _
             ⟨≈⟩ bot-bind-≈ₚ _

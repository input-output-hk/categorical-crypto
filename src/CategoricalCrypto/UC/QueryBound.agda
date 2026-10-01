{-# OPTIONS --safe --without-K --guardedness #-}

-- Query bounds with content: the amortised-potential certificate, and the
-- trace its counting statement (`UC.QueryBound.Counting`) is about.
--
-- `QBᵢ c` reads "one activation from above causes at most `c` completed
-- activations below", in the AMORTISED sense — over any run,
-- #(downward outputs) ≤ c · #(activations from above).  The per-chain reading
-- is not expressible: an `Iface` carries no port structure identifying which
-- answer belongs to which query, and a measure charging every downward output
-- instead is ADDITIVE under the interface tensor, which refutes the `_⊔_` the
-- grading laws need.
--
-- `Φ` is a potential in the sense of amortised complexity: an activation from
-- above deposits `c` units, a downward output withdraws one, an upward output
-- is free, and the initial state's potential is zero.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

import Categories.Category.Construction.Kleisli.Discrete as KD
import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP

open import Data.Empty
open import Data.List.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.QueryBound where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ
  module V = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module K = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})

  -- `opaque`: the chain is shared, not normalized into each certificate.
  opaque
    map-square : {A B C D : Set} (d : Dₚ A) (h : A → B) (f : A → C)
                 (g : B → D) (k : C → D)
               → ((a : A) → g (h a) ≡ k (f a))
               → {e : Dₚ C} → mapₚ f d ≈ₚ e
               → mapₚ g (mapₚ h d) ≈ₚ mapₚ k e
    map-square d h f g k commute de = map-map d h g
      ⟨≈⟩ map-eq d _ _ commute
      ⟨≈⟩ ≈sym (map-map d f k)
      ⟨≈⟩ map-arg k de

------------------------------------------------------------------------
-- The refined answers

Below : {S : Set} → (S → ℕ) → ℕ → Set
Below {S} Φ r = Σ[ s ∈ S ] Φ s ℕ.< r

AtMost : {S : Set} → (S → ℕ) → ℕ → Set
AtMost {S} Φ r = Σ[ s ∈ S ] Φ s ℕ.≤ r

Ans : {S : Set} → (S → ℕ) → Set → Set → ℕ → Set
Ans Φ X Y r = Below Φ r × X ⊎ AtMost Φ r × Y

forget : {S X Y : Set} {P Q : S → Set} → Σ S P × X ⊎ Σ S Q × Y → S × (X ⊎ Y)
forget (inj₁ ((s , _) , x)) = s , inj₁ x
forget (inj₂ ((s , _) , y)) = s , inj₂ y

------------------------------------------------------------------------
-- The certificate

-- The state, point and step are PARAMETERS, not projections out of a `Proc`.
-- Declaring a record whose field types mention `MC.step M` for a general
-- `M : Proc A B` makes the level solver normalize
-- `Machine (Mealy-Monoidal … .⊗₀ (Pos A) (Neg B)) …` against the `_⊎_`
-- spelling, and the record-eta comparison of the two spellings of the base
-- instance exhausts a 10 GiB heap — the `GradedKleisli` eta cliff at another
-- index.  Passing the three components in keeps every spelling in the record
-- an ordinary `_×_`/`_⊎_`, and a process supplies them by projection at the
-- use site (`Certified` below), where the same conversion is a plain
-- application and costs nothing.
module Certificate {A B : Iface} (S : Set) (point : Dₚ S)
                   (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
                   where

  record QBᵢ (c : ℕ) : Set where
    field
      Φ      : S → ℕ
      pointᵍ : Dₚ (AtMost Φ 0)
      coh₀   : mapₚ proj₁ pointᵍ ≈ₚ point
      onLᵍ   : (s : S) (a : Pos A) → Dₚ (Ans Φ (Neg A) (Pos B) (Φ s))
      onRᵍ   : (s : S) (b : Neg B) → Dₚ (Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c))
      cohL   : (s : S) (a : Pos A) → mapₚ forget (onLᵍ s a) ≈ₚ step (s , inj₁ a)
      cohR   : (s : S) (b : Neg B) → mapₚ forget (onRᵍ s b) ≈ₚ step (s , inj₂ b)

  qbᵢ-mono : {c c′ : ℕ} → c ℕ.≤ c′ → QBᵢ c → QBᵢ c′
  qbᵢ-mono {c} {c′} le q = record
    { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀ ; onLᵍ = onLᵍ ; cohL = cohL
    ; onRᵍ = λ s b → mapₚ (widen s) (onRᵍ s b)
    ; cohR = λ s b → map-fuse (onRᵍ s b) (widen s) forget forget
                       (λ { (inj₁ _) → refl ; (inj₂ _) → refl }) ⟨≈⟩ cohR s b
    }
    where
    open QBᵢ q

    widen : (s : S) → Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c)
          → Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c′)
    widen s (inj₁ ((s′ , lt) , a)) = inj₁ ((s′ , ≤-trans lt (+-monoʳ-≤ (Φ s) le)) , a)
    widen s (inj₂ ((s′ , l)  , b)) = inj₂ ((s′ , ≤-trans l  (+-monoʳ-≤ (Φ s) le)) , b)

  -- The observable `UC.QueryBound.Counting` bounds; the only place the layer
  -- unrolls a machine.
  traceᵍ : S → List (Pos A ⊎ Neg B) → Dₚ (List (Neg A ⊎ Pos B))
  traceᵍ s []      = returnₚ []
  traceᵍ s (x ∷ w) = step (s , x) >>=ₚ λ p → mapₚ (proj₂ p ∷_) (traceᵍ (proj₁ p) w)

  behᵍ : List (Pos A ⊎ Neg B) → Dₚ (List (Neg A ⊎ Pos B))
  behᵍ w = point >>=ₚ λ s → traceᵍ s w

open Certificate public using (QBᵢ; qbᵢ-mono; traceᵍ; behᵍ)

------------------------------------------------------------------------
-- Inhabitation

-- At potential 0 a certificate is the half from above plus a tagging of every
-- step from below that `forget` undoes.
qbᵢ-zero : {A B : Iface} {c : ℕ} (S : Set) (point : Dₚ S)
           (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
           (onL : (s : S) (a : Pos A) → Dₚ (Ans {S} (λ _ → 0) (Neg A) (Pos B) 0))
         → ((s : S) (a : Pos A) → mapₚ forget (onL s a) ≈ₚ step (s , inj₁ a))
         → (tag : S × (Neg A ⊎ Pos B) → Ans {S} (λ _ → 0) (Neg A) (Pos B) c)
         → ((y : S × (Neg A ⊎ Pos B)) → forget (tag y) ≡ y)
         → QBᵢ S point step c
qbᵢ-zero S point step onL cohL tag untag = record
  { Φ      = λ _ → 0
  ; pointᵍ = mapₚ (_, z≤n) point
  ; coh₀   = map-map point (_, z≤n) proj₁ ⟨≈⟩ >>=ₚ-identityʳ point
  ; onLᵍ   = onL
  ; onRᵍ   = λ s b → mapₚ tag (step (s , inj₂ b))
  ; cohL   = cohL
  ; cohR   = λ s b → map-fuse (step (s , inj₂ b)) tag forget id untag
                   ⟨≈⟩ >>=ₚ-identityʳ (step (s , inj₂ b))
  }

-- `Neg unitᴵ` is empty, so a closed process has no downward output and is
-- certified at rate 0 with nothing known about it.
qbᵢ-closed : {B : Iface} (S : Set) (point : Dₚ S)
             (step : S × (Pos unitᴵ ⊎ Neg B) → Dₚ (S × (Neg unitᴵ ⊎ Pos B)))
           → QBᵢ S point step 0
qbᵢ-closed {B} S point step = qbᵢ-zero S point step (λ _ ()) (λ _ ()) up
  λ { (_ , inj₁ e) → ⊥-elim e ; (_ , inj₂ _) → refl }
  where
  up : S × (Neg unitᴵ ⊎ Pos B) → Ans {S} (λ _ → 0) (Neg unitᴵ) (Pos B) 0
  up (_ , inj₁ e) = ⊥-elim e
  up (s , inj₂ p) = inj₂ ((s , z≤n) , p)

-- At potential 0 and rate 1 the half from above needs no hypothesis: a
-- downward output fits `0 < 1` and an upward one `0 ≤ 1`.  Only the half from
-- below, which must never call down, is supplied.
qbᵢ-upward : {A B : Iface} (S : Set) (point : Dₚ S)
             (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
             (onL : (s : S) (a : Pos A) → Dₚ (Ans {S} (λ _ → 0) (Neg A) (Pos B) 0))
           → ((s : S) (a : Pos A) → mapₚ forget (onL s a) ≈ₚ step (s , inj₁ a))
           → QBᵢ S point step 1
qbᵢ-upward {A} {B} S point step onL cohL =
  qbᵢ-zero S point step onL cohL tag λ { (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl }
  where
  tag : S × (Neg A ⊎ Pos B) → Ans {S} (λ _ → 0) (Neg A) (Pos B) 1
  tag (s , inj₁ x) = inj₁ ((s , s≤s z≤n) , x)
  tag (s , inj₂ y) = inj₂ ((s , z≤n) , y)

qbᵢ-wire : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
         → QBᵢ ⊤ᵛ (returnₚ tt) (wireStep up down) 1
qbᵢ-wire up down = qbᵢ-upward ⊤ᵛ (returnₚ tt) (wireStep up down)
  (λ s a → returnₚ (inj₂ ((s , z≤n) , up a))) (λ _ _ → >>=ₚ-identityˡ _ _)

------------------------------------------------------------------------
-- The hom-level predicate

Certified : {A B : Iface} → ℕ → Proc A B → Set
Certified c M = QBᵢ (MC.St M) (MC.point (MC.state M) tt) (MC.step M) c

behᴾ : {A B : Iface} → Proc A B → List (Pos A ⊎ Neg B) → Dₚ (List (Neg A ⊎ Pos B))
behᴾ M = behᵍ (MC.St M) (MC.point (MC.state M) tt) (MC.step M)

-- `Certified` is not invariant under the machine equality: a simulation's state
-- map is a function, so a certificate for one side says nothing about the
-- other's states outside its image, and none can be pulled back for want of a
-- right inverse.  The hom-level predicate is therefore the `≈`-closure, which
-- makes `qb-resp-≈` hold by construction and identifies nothing a test can tell
-- apart (`UC.Machine.Run.runᴹ-resp-≈ᴹ`).  Store that underlying machine
-- equality directly: projecting the definitionally identical relation from
-- `𝒫ᴵ` forces the whole G-construction record at composite witnesses.
QB : {A B : Iface} → ℕ → Proc A B → Set₁
QB {A} {B} c M = Σ[ N ∈ Proc A B ] Certified c N × (N S.≈ᴹ M)

certified⇒QB : {A B : Iface} {c : ℕ} {M : Proc A B} → Certified c M → QB c M
certified⇒QB {M = M} q = M , q , S.reflᴹ

qb-wire : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
        → QB 1 (wireᴹ {A} {B} up down)
qb-wire up down = certified⇒QB (qbᵢ-wire up down)

qb-closed : {B : Iface} (M : Proc unitᴵ B) → QB 0 M
qb-closed M = certified⇒QB (qbᵢ-closed (MC.St M) (MC.point (MC.state M) tt) (MC.step M))

qb-resp-≈ : {A B : Iface} {c : ℕ} {M N : Proc A B}
          → M S.≈ᴹ N → QB c M → QB c N
qb-resp-≈ e (P , q , e′) = P , q , e′ S.○ᴹ e

qb-mono : {A B : Iface} {c c′ : ℕ} {M : Proc A B} → c ℕ.≤ c′ → QB c M → QB c′ M
qb-mono le (N , q , e) = N , qbᵢ-mono _ _ _ le q , e

-- A protocol whose every step is a `CategoricalCrypto.OracleCall.Call` asks at
-- most one query per activation and the answer to it only returns, so it is
-- 1-bounded.  The potential CANNOT be read off `Protocol.Machine.MSt`: its
-- `wait` holds the parked continuation as a FUNCTION over arbitrary call trees,
-- and a certificate must answer at every state, reachable or not — the
-- obstruction `Examples.MerkleDamgard.QueryBound`'s header records.  `QB`'s
-- `≈ᴹ`-closure is what that is for: `oneCallᴹ` is the same relay with its
-- suspension named by the continuation `fromCall` parks, whose potential is
-- constantly zero because no second call can follow.
module OneCall {A B : Iface} (P : Protocol A B)
               (call₁ : St P → Neg B → Call (Neg A) (Pos A) (St P × Pos B))
               (factors : (s : St P) (b : Neg B) → step P s b ≡ fromCall (call₁ s b))
               where

  private
    Sᴺ : Set
    Sᴺ = St P ⊎ (Pos A → St P × Pos B)

    driveᶜ : Call (Neg A) (Pos A) (St P × Pos B) → Sᴺ × (Neg A ⊎ Pos B)
    driveᶜ (inj₁ (s , b)) = inj₁ s , inj₂ b
    driveᶜ (inj₂ (q , k)) = inj₂ k , inj₁ q

    stepᴺ : Sᴺ × (Pos A ⊎ Neg B) → Dₚ (Sᴺ × (Neg A ⊎ Pos B))
    stepᴺ (inj₁ s , inj₂ b) = returnₚ (driveᶜ (call₁ s b))
    stepᴺ (inj₂ k , inj₁ a) = returnₚ (inj₁ (proj₁ (k a)) , inj₂ (proj₂ (k a)))
    stepᴺ (inj₁ _ , inj₁ _) = botₚ
    stepᴺ (inj₂ _ , inj₂ _) = botₚ

    stateᴺ : MC.State
    stateᴺ = initˢ Sᴺ (inj₁ (init P))

    oneCallᴹ : Proc A B
    oneCallᴹ = MC.mk stateᴺ stepᴺ

    Φᴺ : Sᴺ → ℕ
    Φᴺ _ = 0

    Answer = Ans Φᴺ (Neg A) (Pos B)

    onCall : (c : Call (Neg A) (Pos A) (St P × Pos B)) → Dₚ (Answer 1)
    onCall (inj₁ (s , b)) = returnₚ (inj₂ ((inj₁ s , z≤n) , b))
    onCall (inj₂ (q , k)) = returnₚ (inj₁ ((inj₂ k , s≤s z≤n) , q))

    onCall-coh : (c : Call (Neg A) (Pos A) (St P × Pos B))
               → mapₚ forget (onCall c) ≈ₚ returnₚ (driveᶜ c)
    onCall-coh (inj₁ _) = >>=ₚ-identityˡ _ _
    onCall-coh (inj₂ _) = >>=ₚ-identityˡ _ _

    certifiedᴺ : Certified 1 oneCallᴹ
    certifiedᴺ = record
      { Φ      = Φᴺ
      ; pointᵍ = returnₚ (inj₁ (init P) , z≤n)
      ; coh₀   = >>=ₚ-identityˡ _ _
      ; onLᵍ   = onL
      ; onRᵍ   = onR
      ; cohL   = λ where (inj₁ _) _ → bot-bind-≈ₚ _
                         (inj₂ _) _ → >>=ₚ-identityˡ _ _
      ; cohR   = λ where (inj₁ s) b → onCall-coh (call₁ s b)
                         (inj₂ _) _ → bot-bind-≈ₚ _
      }
      where
      onL : (s : Sᴺ) (a : Pos A) → Dₚ (Answer (Φᴺ s))
      onL (inj₁ _) _ = botₚ
      onL (inj₂ k) a = returnₚ (inj₂ ((inj₁ (proj₁ (k a)) , z≤n) , proj₂ (k a)))

      onR : (s : Sᴺ) (b : Neg B) → Dₚ (Answer (Φᴺ s ℕ.+ 1))
      onR (inj₁ s) b = onCall (call₁ s b)
      onR (inj₂ _) _ = botₚ

    θᴺ : Sᴺ → MSt P
    θᴺ (inj₁ s) = idle s
    θᴺ (inj₂ k) = wait λ r → ret (k r)

    drive-one : (c : Call (Neg A) (Pos A) (St P × Pos B))
              → (returnₚ (driveᶜ c) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P (fromCall c)
    drive-one (inj₁ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (driveᶜ (inj₁ x))
    drive-one (inj₂ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (driveᶜ (inj₂ x))

    θ-step : (z : Sᴺ × (Pos A ⊎ Neg B))
           → (stepᴺ z >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id))
             ≈ₚ ((K.pureᵏ θᴺ V.⊗₁ V.id) z >>=ₚ stepᴹ P)
    θ-step (inj₁ s , inj₂ b) =
      subst (λ t → (stepᴺ (inj₁ s , inj₂ b) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P t)
            (sym (factors s b)) (drive-one (call₁ s b))
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₁ s , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₁ a) =
      >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (inj₁ (proj₁ (k a)) , inj₂ (proj₂ (k a)))
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₂ k , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₁ s , inj₁ a) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₁ s , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₂ b) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₂ k , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)

    θ-sim : oneCallᴹ S.≲ morphism P
    θ-sim = S.sim (K.pureᵏ θᴺ) (KP.structural θᴺ)
                  (λ _ → >>=ₚ-identityˡ (inj₁ (init P)) _)
                  θ-step

  qb-oneCall : QB 1 (morphism P)
  qb-oneCall = oneCallᴹ , certifiedᴺ , S.≲⇒≈ᴹ θ-sim

open OneCall public using (qb-oneCall)

------------------------------------------------------------------------
-- The three trace-free closure properties
--
-- `T₁ᴵ`/`subᴵ` keep the plugged process's state, so its potential IS the
-- action's and `pointᵍ`/`coh₀` carry over untouched; what changes is the tagging
-- of the answers and the two bypass cases the ancilla contributes, one relay
-- apiece.  The DOWNWARD one is a completed activation, so it must withdraw a
-- unit that an activation from above deposited, and a rate of zero has none to
-- give: `c ⊔ 1` is what pays for it, and `qbᵢ-wire`'s `1` is the same fact at
-- the bare wire.

private
  0<⊔1 : (c : ℕ) → 0 ℕ.< c ℕ.⊔ 1
  0<⊔1 c = m≤n⊔m c 1

-- A certificate sees its step only up to `_≈ₚ_`.  That is what lets the two
-- action laws below be built against an explicit step — one whose relay reduces
-- — and then transported onto the action's own.
qbᵢ-resp-step : {A B : Iface} (S : Set) (point : Dₚ S)
                (step step′ : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
              → ((p : S × (Pos A ⊎ Neg B)) → step p ≈ₚ step′ p)
              → {c : ℕ} → QBᵢ S point step c → QBᵢ S point step′ c
qbᵢ-resp-step S point step step′ eq q = record
  { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀ ; onLᵍ = onLᵍ ; onRᵍ = onRᵍ
  ; cohL = λ s a → cohL s a ⟨≈⟩ eq (s , inj₁ a)
  ; cohR = λ s b → cohR s b ⟨≈⟩ eq (s , inj₂ b)
  }
  where open QBᵢ q

-- The identity is `σᴹ`, a pure machine, where the wire case-splits the sum; the
-- two are the same relay up to the junctions a `pureᴹ` spends.
qbᵢ-id : {A : Iface} → Certified 1 (𝒫.id {A})
qbᵢ-id {A} =
  qbᵢ-resp-step ⊤ᵛ (returnₚ tt) (wireStep {A} {A} id id) (MC.step (𝒫.id {A}))
    (λ where (s , inj₁ p) → ≈sym (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-identityˡ (inj₂ p) _)
             (s , inj₂ n) → ≈sym (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-identityˡ (inj₁ n) _))
    (qbᵢ-wire id id)

qb-idᴹ : {A : Iface} → QB 1 (𝒫.id {A})
qb-idᴹ = certified⇒QB qbᵢ-id

-- The two actions differ only in which summand holds the ancilla: the two
-- input splits and the four output injections.
private
  module Ancilla {A B Z : Iface} {PI NI NO PO : Set}
                 (splitP : PI → Pos A ⊎ Pos Z) (splitN : NI → Neg B ⊎ Neg Z)
                 (inA : Neg A → NO) (inZ⁻ : Neg Z → NO) (inB : Pos B → PO) (inZ⁺ : Pos Z → PO)
                 {c : ℕ} (f : Proc A B) (q : Certified c f) where

    open QBᵢ q

    relay : MC.St f × (Neg A ⊎ Pos B) → MC.St f × (NO ⊎ PO)
    relay (s , inj₁ a) = s , inj₁ (inA a)
    relay (s , inj₂ b) = s , inj₂ (inB b)

    stepP : MC.St f → Pos A ⊎ Pos Z → Dₚ (MC.St f × (NO ⊎ PO))
    stepP s (inj₁ a) = mapₚ relay (MC.step f (s , inj₁ a))
    stepP s (inj₂ z) = returnₚ (s , inj₂ (inZ⁺ z))

    stepN : MC.St f → Neg B ⊎ Neg Z → Dₚ (MC.St f × (NO ⊎ PO))
    stepN s (inj₁ b) = mapₚ relay (MC.step f (s , inj₂ b))
    stepN s (inj₂ z) = returnₚ (s , inj₁ (inZ⁻ z))

    stepᴬ : MC.St f × (PI ⊎ NI) → Dₚ (MC.St f × (NO ⊎ PO))
    stepᴬ (s , inj₁ x) = stepP s (splitP x)
    stepᴬ (s , inj₂ x) = stepN s (splitN x)

    lift : {r r′ : ℕ} → r ℕ.≤ r′ → Ans Φ (Neg A) (Pos B) r → Ans Φ NO PO r′
    lift le (inj₁ ((s , lt) , a)) = inj₁ ((s , ≤-trans lt le) , inA a)
    lift le (inj₂ ((s , l)  , b)) = inj₂ ((s , ≤-trans l  le) , inB b)

    relayed : {r r′ : ℕ} (le : r ℕ.≤ r′) (X : Dₚ (Ans Φ (Neg A) (Pos B) r))
              (t : Dₚ (MC.St f × (Neg A ⊎ Pos B))) → mapₚ forget X ≈ₚ t
            → mapₚ forget (mapₚ (lift le) X) ≈ₚ mapₚ relay t
    relayed le X t coh = map-square X (lift le) forget forget relay
                                    (λ where (inj₁ _) → refl
                                             (inj₂ _) → refl) coh

    onLP : (s : MC.St f) → Pos A ⊎ Pos Z → Dₚ (Ans Φ NO PO (Φ s))
    onLP s (inj₁ a) = mapₚ (lift ≤-refl) (onLᵍ s a)
    onLP s (inj₂ z) = returnₚ (inj₂ ((s , ≤-refl) , inZ⁺ z))

    onRN : (s : MC.St f) → Neg B ⊎ Neg Z → Dₚ (Ans Φ NO PO (Φ s ℕ.+ (c ℕ.⊔ 1)))
    onRN s (inj₁ b) = mapₚ (lift (+-monoʳ-≤ (Φ s) (m≤m⊔n c 1))) (onRᵍ s b)
    onRN s (inj₂ z) = returnₚ (inj₁ ((s , m<m+n (Φ s) (0<⊔1 c)) , inZ⁻ z))

    cohLP : (s : MC.St f) (x : Pos A ⊎ Pos Z) → mapₚ forget (onLP s x) ≈ₚ stepP s x
    cohLP s (inj₁ a) = relayed ≤-refl (onLᵍ s a) _ (cohL s a)
    cohLP s (inj₂ z) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

    cohRN : (s : MC.St f) (x : Neg B ⊎ Neg Z) → mapₚ forget (onRN s x) ≈ₚ stepN s x
    cohRN s (inj₁ b) = relayed _ (onRᵍ s b) _ (cohR s b)
    cohRN s (inj₂ z) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

    cert : QBᵢ (MC.St f) (MC.point (MC.state f) tt) stepᴬ (c ℕ.⊔ 1)
    cert = record
      { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀
      ; onLᵍ = λ s x → onLP s (splitP x) ; onRᵍ = λ s x → onRN s (splitN x)
      ; cohL = λ s x → cohLP s (splitP x) ; cohR = λ s x → cohRN s (splitN x)
      }

qbᵢ-T₁ : (Y A B : Iface) {c : ℕ} (f : Proc A B) → Certified c f
       → Certified (c ℕ.⊔ 1) (T₁ᴵ Y f)
qbᵢ-T₁ Y A B f q = qbᵢ-resp-step _ _ _ (MC.step (T₁ᴵ Y f)) eq cert
  where
  open Ancilla {Z = Y} Sum.swap Sum.swap inj₂ inj₁ inj₂ inj₁ f q

  eq : (p : MC.St f × ((Pos Y ⊎ Pos A) ⊎ (Neg Y ⊎ Neg B)))
     → stepᴬ p ≈ₚ MC.step (T₁ᴵ Y f) p
  eq (s , inj₁ (inj₁ y)) = ≈ₚ-refl _
  eq (s , inj₁ (inj₂ a)) = map-eq (MC.step f (s , inj₁ a)) _ _
    λ where (_ , inj₁ _) → refl
            (_ , inj₂ _) → refl
  eq (s , inj₂ (inj₁ y)) = ≈ₚ-refl _
  eq (s , inj₂ (inj₂ b)) = map-eq (MC.step f (s , inj₂ b)) _ _
    λ where (_ , inj₁ _) → refl
            (_ , inj₂ _) → refl

qbᵢ-sub : (X Y A : Iface) {c : ℕ} (s : Proc X Y) → Certified c s
        → Certified (c ℕ.⊔ 1) (subᴵ {A = A} s)
qbᵢ-sub X Y A s q = qbᵢ-resp-step _ _ _ (MC.step (subᴵ {A = A} s)) eq cert
  where
  open Ancilla {Z = A} id id inj₁ inj₂ inj₁ inj₂ s q

  eq : (p : MC.St s × ((Pos X ⊎ Pos A) ⊎ (Neg Y ⊎ Neg A)))
     → stepᴬ p ≈ₚ MC.step (subᴵ {A = A} s) p
  eq (t , inj₁ (inj₁ x)) = map-eq (MC.step s (t , inj₁ x)) _ _
    λ where (_ , inj₁ _) → refl
            (_ , inj₂ _) → refl
  eq (t , inj₁ (inj₂ a)) = ≈ₚ-refl _
  eq (t , inj₂ (inj₁ y)) = map-eq (MC.step s (t , inj₂ y)) _ _
    λ where (_ , inj₁ _) → refl
            (_ , inj₂ _) → refl
  eq (t , inj₂ (inj₂ a)) = ≈ₚ-refl _

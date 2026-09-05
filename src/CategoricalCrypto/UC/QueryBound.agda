{-# OPTIONS --safe --without-K --guardedness #-}

-- Query bounds with content: the amortised-potential certificate, and the
-- run-level counting statement it exists for.
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
-- is free, and the initial state's potential is zero.  All of that is carried
-- by `Ans`'s reference argument — a downward output lands in `Below` (strictly
-- less), an upward one in `AtMost` — and `cohL`/`cohR` say the refinement adds
-- no behaviour.
--
-- Two things differ from the reference arc.  The initial state is EFFECTFUL
-- here (a Kleisli point, not an element), so the zero-potential condition is
-- itself a refined value: `pointᵍ` is a distribution over zero-potential
-- states erasing to the machine's own point.  And the certificate is stated
-- over a state, a point and a step given as PARAMETERS rather than projected
-- from a process — see the note above `Certificate`.
--
-- This is a definition, not an axiom list: `UC.Budget`'s `QB` is a
-- parameter and admits the degenerate `QB c f = ⊤`, whereas `QBᵢ` cannot be
-- inhabited without exhibiting the potential, and `Counting` is what makes the
-- potential mean something about runs.

open import Categories.Category using (Category; _[_≈_])

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc; z≤n; s≤s)
open import Data.Nat.Properties using (+-monoʳ-≤; m<m+n; m≤m⊔n; m≤n⊔m; ≤-refl; ≤-trans)
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (_∘′_; id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine
  using (Proc; 𝒫ᴵ; T₁ᴵ; subᴵ; a⇒ᴵ; a⇐ᴵ; wireStep; ⊤ᵛ)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.QueryBound where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

  variable A′ B′ C′ : Set

  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ A′} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  bindᶠ : {d : Dₚ A′} {k l : A′ → Dₚ B′}
        → ((a : A′) → k a ≈ₚ l a) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l (≈ₚ-refl d) h

  return-≡ : {x y : A′} → x ≡ y → returnₚ x ≈ₚ returnₚ y
  return-≡ refl = ≈ₚ-refl _

  map-map : (d : Dₚ A′) (h : A′ → B′) (k : B′ → C′)
          → mapₚ k (mapₚ h d) ≈ₚ mapₚ (k ∘′ h) d
  map-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) (returnₚ ∘′ k)
            ⟨≈⟩ bindᶠ (λ a → >>=ₚ-identityˡ (h a) (returnₚ ∘′ k))

  map-cong : (d : Dₚ A′) {h k : A′ → B′}
           → ((a : A′) → h a ≡ k a) → mapₚ h d ≈ₚ mapₚ k d
  map-cong d eq = bindᶠ (λ a → return-≡ (eq a))

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
-- instance exhausts a 10 GiB heap — the `GradedKleisli` eta cliff at a new
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

  -- Only `onRᵍ` mentions `c`, so only its answers are widened.
  qbᵢ-mono : {c c′ : ℕ} → c ℕ.≤ c′ → QBᵢ c → QBᵢ c′
  qbᵢ-mono {c} {c′} le q = record
    { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀ ; onLᵍ = onLᵍ ; cohL = cohL
    ; onRᵍ = λ s b → mapₚ (widen s) (onRᵍ s b)
    ; cohR = λ s b → map-map (onRᵍ s b) (widen s) forget
                   ⟨≈⟩ map-cong (onRᵍ s b) (agree s)
                   ⟨≈⟩ cohR s b
    }
    where
    open QBᵢ q

    widen : (s : S) → Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c)
          → Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c′)
    widen s (inj₁ ((s′ , lt) , a)) = inj₁ ((s′ , ≤-trans lt (+-monoʳ-≤ (Φ s) le)) , a)
    widen s (inj₂ ((s′ , l)  , b)) = inj₂ ((s′ , ≤-trans l  (+-monoʳ-≤ (Φ s) le)) , b)

    agree : (s : S) (y : Ans Φ (Neg A) (Pos B) (Φ s ℕ.+ c))
          → forget (widen s y) ≡ forget y
    agree s (inj₁ _) = refl
    agree s (inj₂ _) = refl

  ------------------------------------------------------------------------
  -- What the potential means about a run

  -- The environment chooses an activation word; the machine answers with one
  -- output per activation.  This is the only place the layer unrolls a machine,
  -- and the observable a counting statement is about.
  traceᵍ : S → List (Pos A ⊎ Neg B) → Dₚ (List (Neg A ⊎ Pos B))
  traceᵍ s []      = returnₚ []
  traceᵍ s (x ∷ w) = step (s , x) >>=ₚ λ p → mapₚ (proj₂ p ∷_) (traceᵍ (proj₁ p) w)

  behᵍ : List (Pos A ⊎ Neg B) → Dₚ (List (Neg A ⊎ Pos B))
  behᵍ w = point >>=ₚ λ s → traceᵍ s w

open Certificate public using (QBᵢ; qbᵢ-mono; traceᵍ; behᵍ)

------------------------------------------------------------------------
-- Counting

private
  #inj₁ : List (A′ ⊎ B′) → ℕ
  #inj₁ []            = 0
  #inj₁ (inj₁ _ ∷ xs) = suc (#inj₁ xs)
  #inj₁ (inj₂ _ ∷ xs) = #inj₁ xs

  #inj₂ : List (A′ ⊎ B′) → ℕ
  #inj₂ []            = 0
  #inj₂ (inj₁ _ ∷ xs) = #inj₂ xs
  #inj₂ (inj₂ _ ∷ xs) = suc (#inj₂ xs)

module _ {A B : Iface} (S : Set) (point : Dₚ S)
         (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
         where

  record CountBound (c : ℕ) : Set where
    field
      runs   : (w : List (Pos A ⊎ Neg B))
             → Dₚ (Σ[ os ∈ List (Neg A ⊎ Pos B) ] #inj₁ os ℕ.≤ c ℕ.* #inj₂ w)
      erases : (w : List (Pos A ⊎ Neg B))
             → mapₚ proj₁ (runs w) ≈ₚ behᵍ S point step w

-- The counting theorem, stated and priced.  The reference arc proves it in 248
-- LOC by recursing on the activation word against the certificate's own
-- refined activations, carrying the invariant with the FINAL potential retained
-- (`#inj₁ os + Φ final ≤ Φ s + c * #inj₂ w`) — the version that composes — and
-- cashing a deposit at each activation from above.  Two things change here: the
-- recursion is effectful (`Dₚ`, so each cons step is a `>>=ₚ` rather than a
-- functorial action), and the initial slack is zeroed by `pointᵍ` rather than
-- by a `subst` on `Φ (init M) ≡ 0`.
Counting : Set₁
Counting = {A B : Iface} (S : Set) (point : Dₚ S)
           (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B))) (c : ℕ)
         → QBᵢ S point step c → CountBound S point step c

------------------------------------------------------------------------
-- Inhabitation

-- A stateless forwarder answers each activation with exactly one output, so it
-- is 1-bounded: the potential is constantly zero, an upward relay is free, and
-- a downward relay spends the single unit the activation deposited.  This is
-- also where the rate cannot be zero, which is what forces `Budget`'s
-- `qb-T₁`/`qb-sub` to `c ⊔ 1`.
qbᵢ-wire : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
         → QBᵢ ⊤ᵛ (returnₚ tt) (wireStep up down) 1
qbᵢ-wire up down = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (tt , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (tt , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = λ s a → returnₚ (inj₂ ((s , z≤n) , up a))
  ; onRᵍ   = λ s b → returnₚ (inj₁ ((s , s≤s z≤n) , down b))
  ; cohL   = λ s a → >>=ₚ-identityˡ (inj₂ ((s , z≤n) , up a)) (returnₚ ∘′ forget)
  ; cohR   = λ s b → >>=ₚ-identityˡ (inj₁ ((s , s≤s z≤n) , down b)) (returnₚ ∘′ forget)
  }

------------------------------------------------------------------------
-- The hom-level predicate

-- A process's certificate, read off its own state, point and step.
Certified : {A B : Iface} → ℕ → Proc A B → Set
Certified c M = QBᵢ (MC.St M) (MC.point (MC.state M) tt) (MC.step M) c

-- `Certified` is not invariant under the machine equality: a simulation's state
-- map is a function, so a certificate for one side says nothing about the
-- other's states outside its image, and none can be pulled back for want of a
-- right inverse.  The hom-level predicate is therefore the `≈`-closure, which
-- makes `qb-resp-≈` hold by construction and identifies nothing a test can tell
-- apart (`UC.Machine.Run.runᴹ-resp-≈ᴹ`).
QB : {A B : Iface} → ℕ → Proc A B → Set₁
QB {A} {B} c M = Σ[ N ∈ Proc A B ] Certified c N × 𝒫ᴵ [ N ≈ M ]

certified⇒QB : {A B : Iface} {c : ℕ} {M : Proc A B} → Certified c M → QB c M
certified⇒QB {M = M} q = M , q , 𝒫.Equiv.refl

qb-resp-≈ : {A B : Iface} {c : ℕ} {M N : Proc A B}
          → 𝒫ᴵ [ M ≈ N ] → QB c M → QB c N
qb-resp-≈ e (P , q , e′) = P , q , 𝒫.Equiv.trans e′ e

qb-mono : {A B : Iface} {c c′ : ℕ} {M : Proc A B} → c ℕ.≤ c′ → QB c M → QB c′ M
qb-mono le (N , q , e) = N , qbᵢ-mono _ _ _ le q , e

------------------------------------------------------------------------
-- The three trace-free closure properties
--
-- `T₁ᴵ`/`subᴵ` keep the plugged process's state, so its potential IS the
-- action's and `pointᵍ`/`coh₀` carry over untouched; what changes is the tagging
-- of the answers and the two bypass cases the ancilla contributes, one relay
-- apiece.  The DOWNWARD one is a completed activation, so it must withdraw a
-- unit that an activation from above deposited, and a rate of zero has none to
-- give: `c ⊔ 1` is what pays for it, and `qbᵢ-wire`'s `1` is the same fact at
-- the bare wire.  Nothing here unrolls a machine or touches the ⊕-trace.

private
  map-arg : {d e : Dₚ A′} (h : A′ → B′) → d ≈ₚ e → mapₚ h d ≈ₚ mapₚ h e
  map-arg {d = d} {e} h de = >>=ₚ-cong d e (returnₚ ∘′ h) (returnₚ ∘′ h) de λ _ → ≈ₚ-refl _

  -- The bypassed interface can always afford its one downward relay.
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
                id-step (qbᵢ-wire id id)
  where
  id-step : (p : ⊤ᵛ × (Pos A ⊎ Neg A))
          → wireStep {A} {A} id id p ≈ₚ MC.step (𝒫.id {A}) p
  id-step (s , inj₁ p) =
    ≈ₚ-sym _ _ (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-identityˡ (inj₂ p) _)
  id-step (s , inj₂ n) =
    ≈ₚ-sym _ _ (>>=ₚ-identityˡ s _ ⟨≈⟩ >>=ₚ-identityˡ (inj₁ n) _)

------------------------------------------------------------------------

module _ (Y A B : Iface) {c : ℕ} (f : Proc A B) (q : Certified c f) where

  private
    open QBᵢ q

    relayT : MC.St f × (Neg A ⊎ Pos B)
           → MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B))
    relayT (s , inj₁ a) = s , inj₁ (inj₂ a)
    relayT (s , inj₂ b) = s , inj₂ (inj₂ b)

    stepT : MC.St f × ((Pos Y ⊎ Pos A) ⊎ (Neg Y ⊎ Neg B))
          → Dₚ (MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)))
    stepT (s , inj₁ (inj₁ y)) = returnₚ (s , inj₂ (inj₁ y))
    stepT (s , inj₁ (inj₂ a)) = mapₚ relayT (MC.step f (s , inj₁ a))
    stepT (s , inj₂ (inj₁ y)) = returnₚ (s , inj₁ (inj₁ y))
    stepT (s , inj₂ (inj₂ b)) = mapₚ relayT (MC.step f (s , inj₂ b))

    stepT-eq : (p : MC.St f × ((Pos Y ⊎ Pos A) ⊎ (Neg Y ⊎ Neg B)))
             → stepT p ≈ₚ MC.step (T₁ᴵ Y f) p
    stepT-eq (s , inj₁ (inj₁ y)) = ≈ₚ-refl _
    stepT-eq (s , inj₁ (inj₂ a)) = map-cong (MC.step f (s , inj₁ a))
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl
    stepT-eq (s , inj₂ (inj₁ y)) = ≈ₚ-refl _
    stepT-eq (s , inj₂ (inj₂ b)) = map-cong (MC.step f (s , inj₂ b))
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl

    -- The plugged process's answer, retagged into the second summand; the
    -- reference potential only ever grows, so the witnesses survive.
    liftT : {r r′ : ℕ} → r ℕ.≤ r′
          → Ans Φ (Neg A) (Pos B) r → Ans Φ (Neg Y ⊎ Neg A) (Pos Y ⊎ Pos B) r′
    liftT le (inj₁ ((s , lt) , a)) = inj₁ ((s , ≤-trans lt le) , inj₂ a)
    liftT le (inj₂ ((s , l)  , b)) = inj₂ ((s , ≤-trans l  le) , inj₂ b)

    liftT-forget : {r r′ : ℕ} (le : r ℕ.≤ r′) (y : Ans Φ (Neg A) (Pos B) r)
                 → forget (liftT le y) ≡ relayT (forget y)
    liftT-forget le (inj₁ _) = refl
    liftT-forget le (inj₂ _) = refl

    relayed : {r r′ : ℕ} (le : r ℕ.≤ r′) (X : Dₚ (Ans Φ (Neg A) (Pos B) r))
              (t : Dₚ (MC.St f × (Neg A ⊎ Pos B))) → mapₚ forget X ≈ₚ t
            → mapₚ forget (mapₚ (liftT le) X) ≈ₚ mapₚ relayT t
    relayed le X t coh = map-map X (liftT le) forget
                   ⟨≈⟩ map-cong X (liftT-forget le)
                   ⟨≈⟩ ≈ₚ-sym _ _ (map-map X forget relayT)
                   ⟨≈⟩ map-arg relayT coh

    certT : QBᵢ (MC.St f) (MC.point (MC.state f) tt) stepT (c ℕ.⊔ 1)
    certT = record
      { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀ ; onLᵍ = onL ; onRᵍ = onR
      ; cohL = cohL′ ; cohR = cohR′
      }
      where
      onL : (s : MC.St f) (x : Pos Y ⊎ Pos A)
          → Dₚ (Ans Φ (Neg Y ⊎ Neg A) (Pos Y ⊎ Pos B) (Φ s))
      onL s (inj₁ y) = returnₚ (inj₂ ((s , ≤-refl) , inj₁ y))
      onL s (inj₂ a) = mapₚ (liftT ≤-refl) (onLᵍ s a)

      onR : (s : MC.St f) (x : Neg Y ⊎ Neg B)
          → Dₚ (Ans Φ (Neg Y ⊎ Neg A) (Pos Y ⊎ Pos B) (Φ s ℕ.+ (c ℕ.⊔ 1)))
      onR s (inj₁ y) = returnₚ (inj₁ ((s , m<m+n (Φ s) (0<⊔1 c)) , inj₁ y))
      onR s (inj₂ b) = mapₚ (liftT (+-monoʳ-≤ (Φ s) (m≤m⊔n c 1))) (onRᵍ s b)

      cohL′ : (s : MC.St f) (x : Pos Y ⊎ Pos A)
            → mapₚ forget (onL s x) ≈ₚ stepT (s , inj₁ x)
      cohL′ s (inj₁ y) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
      cohL′ s (inj₂ a) = relayed ≤-refl (onLᵍ s a) _ (cohL s a)

      cohR′ : (s : MC.St f) (x : Neg Y ⊎ Neg B)
            → mapₚ forget (onR s x) ≈ₚ stepT (s , inj₂ x)
      cohR′ s (inj₁ y) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
      cohR′ s (inj₂ b) = relayed _ (onRᵍ s b) _ (cohR s b)

  qbᵢ-T₁ : Certified (c ℕ.⊔ 1) (T₁ᴵ Y f)
  qbᵢ-T₁ = qbᵢ-resp-step _ _ stepT (MC.step (T₁ᴵ Y f)) stepT-eq certT

------------------------------------------------------------------------

module _ (X Y A : Iface) {c : ℕ} (s : Proc X Y) (q : Certified c s) where

  private
    open QBᵢ q

    relayS : MC.St s × (Neg X ⊎ Pos Y)
           → MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A))
    relayS (t , inj₁ x) = t , inj₁ (inj₁ x)
    relayS (t , inj₂ y) = t , inj₂ (inj₁ y)

    stepS : MC.St s × ((Pos X ⊎ Pos A) ⊎ (Neg Y ⊎ Neg A))
          → Dₚ (MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)))
    stepS (t , inj₁ (inj₁ x)) = mapₚ relayS (MC.step s (t , inj₁ x))
    stepS (t , inj₁ (inj₂ a)) = returnₚ (t , inj₂ (inj₂ a))
    stepS (t , inj₂ (inj₁ y)) = mapₚ relayS (MC.step s (t , inj₂ y))
    stepS (t , inj₂ (inj₂ a)) = returnₚ (t , inj₁ (inj₂ a))

    stepS-eq : (p : MC.St s × ((Pos X ⊎ Pos A) ⊎ (Neg Y ⊎ Neg A)))
             → stepS p ≈ₚ MC.step (subᴵ s {A}) p
    stepS-eq (t , inj₁ (inj₁ x)) = map-cong (MC.step s (t , inj₁ x))
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl
    stepS-eq (t , inj₁ (inj₂ a)) = ≈ₚ-refl _
    stepS-eq (t , inj₂ (inj₁ y)) = map-cong (MC.step s (t , inj₂ y))
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl
    stepS-eq (t , inj₂ (inj₂ a)) = ≈ₚ-refl _

    liftS : {r r′ : ℕ} → r ℕ.≤ r′
          → Ans Φ (Neg X) (Pos Y) r → Ans Φ (Neg X ⊎ Neg A) (Pos Y ⊎ Pos A) r′
    liftS le (inj₁ ((t , lt) , x)) = inj₁ ((t , ≤-trans lt le) , inj₁ x)
    liftS le (inj₂ ((t , l)  , y)) = inj₂ ((t , ≤-trans l  le) , inj₁ y)

    liftS-forget : {r r′ : ℕ} (le : r ℕ.≤ r′) (y : Ans Φ (Neg X) (Pos Y) r)
                 → forget (liftS le y) ≡ relayS (forget y)
    liftS-forget le (inj₁ _) = refl
    liftS-forget le (inj₂ _) = refl

    relayedS : {r r′ : ℕ} (le : r ℕ.≤ r′) (Z : Dₚ (Ans Φ (Neg X) (Pos Y) r))
               (t : Dₚ (MC.St s × (Neg X ⊎ Pos Y))) → mapₚ forget Z ≈ₚ t
             → mapₚ forget (mapₚ (liftS le) Z) ≈ₚ mapₚ relayS t
    relayedS le Z t coh = map-map Z (liftS le) forget
                    ⟨≈⟩ map-cong Z (liftS-forget le)
                    ⟨≈⟩ ≈ₚ-sym _ _ (map-map Z forget relayS)
                    ⟨≈⟩ map-arg relayS coh

    certS : QBᵢ (MC.St s) (MC.point (MC.state s) tt) stepS (c ℕ.⊔ 1)
    certS = record
      { Φ = Φ ; pointᵍ = pointᵍ ; coh₀ = coh₀ ; onLᵍ = onL ; onRᵍ = onR
      ; cohL = cohL′ ; cohR = cohR′
      }
      where
      onL : (t : MC.St s) (x : Pos X ⊎ Pos A)
          → Dₚ (Ans Φ (Neg X ⊎ Neg A) (Pos Y ⊎ Pos A) (Φ t))
      onL t (inj₁ x) = mapₚ (liftS ≤-refl) (onLᵍ t x)
      onL t (inj₂ a) = returnₚ (inj₂ ((t , ≤-refl) , inj₂ a))

      onR : (t : MC.St s) (x : Neg Y ⊎ Neg A)
          → Dₚ (Ans Φ (Neg X ⊎ Neg A) (Pos Y ⊎ Pos A) (Φ t ℕ.+ (c ℕ.⊔ 1)))
      onR t (inj₁ y) = mapₚ (liftS (+-monoʳ-≤ (Φ t) (m≤m⊔n c 1))) (onRᵍ t y)
      onR t (inj₂ a) = returnₚ (inj₁ ((t , m<m+n (Φ t) (0<⊔1 c)) , inj₂ a))

      cohL′ : (t : MC.St s) (x : Pos X ⊎ Pos A)
            → mapₚ forget (onL t x) ≈ₚ stepS (t , inj₁ x)
      cohL′ t (inj₁ x) = relayedS ≤-refl (onLᵍ t x) _ (cohL t x)
      cohL′ t (inj₂ a) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

      cohR′ : (t : MC.St s) (x : Neg Y ⊎ Neg A)
            → mapₚ forget (onR t x) ≈ₚ stepS (t , inj₂ x)
      cohR′ t (inj₁ y) = relayedS _ (onRᵍ t y) _ (cohR t y)
      cohR′ t (inj₂ a) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

  qbᵢ-sub : Certified (c ℕ.⊔ 1) (subᴵ s {A})
  qbᵢ-sub = qbᵢ-resp-step _ _ stepS (MC.step (subᴵ s {A})) stepS-eq certS

------------------------------------------------------------------------

qb-idᴹ : {A : Iface} → QB 1 (𝒫.id {A})
qb-idᴹ = certified⇒QB qbᵢ-id

-- The hom-level forms need the action to respect `_≈_`, because `QB` is the
-- `≈`-closure of `Certified` and the certificate lives on a representative;
-- those two are `GradingLawsᴹ`'s other trace-free fields.  Every interface is
-- EXPLICIT here, and that is measured rather than tidy: left implicit, a `Proc`
-- argument makes Agda invert `Machine (Pos A + Neg B) …` for the pair, and this
-- module stops coming back inside 200 s (`UC.Machine`'s header records the same
-- inversion at ~1 GiB apiece).  Which is also why `BudgetLawsᴹ` is not assembled
-- here: its four fields take their interfaces implicitly, so filling them costs
-- exactly that, and the record wants `qb-∘` anyway.
qb-T₁ᴹ : ({Y A B : Iface} {f g : Proc A B} → 𝒫ᴵ [ f ≈ g ] → 𝒫ᴵ [ T₁ᴵ Y f ≈ T₁ᴵ Y g ])
       → (Y A B : Iface) {c : ℕ} (f : Proc A B) → QB c f → QB (c ℕ.⊔ 1) (T₁ᴵ Y f)
qb-T₁ᴹ resp Y A B f (N , cert , e) = T₁ᴵ Y N , qbᵢ-T₁ Y A B N cert , resp e

qb-subᴹ : ({X Y A : Iface} {s t : Proc X Y} → 𝒫ᴵ [ s ≈ t ] → 𝒫ᴵ [ subᴵ s {A} ≈ subᴵ t ])
        → (X Y A : Iface) {c : ℕ} (s : Proc X Y) → QB c s → QB (c ℕ.⊔ 1) (subᴵ s {A})
qb-subᴹ resp X Y A s (N , cert , e) = subᴵ N , qbᵢ-sub X Y A N cert , resp e

------------------------------------------------------------------------
-- The closure property still owed

-- `qb-∘` is the reference arc's 231-LOC two-position token walk, with a ⊕-trace
-- on top of it here.  The other three fields are the theorems above, at their
-- explicit-interface spellings; they are what `UC.Budget` still wants at this
-- instance.
record BudgetLawsᴹ : Set₁ where
  field
    qb-id  : {A : Iface} → QB 1 (𝒫.id {A})
    qb-∘   : {A B C : Iface} {c c′ : ℕ} {g : Proc B C} {f : Proc A B}
           → QB c g → QB c′ f → QB (c ℕ.* c′) (g 𝒫.∘ f)
    qb-T₁  : {Y A B : Iface} {c : ℕ} {f : Proc A B}
           → QB c f → QB (c ℕ.⊔ 1) (T₁ᴵ Y f)
    qb-sub : {X Y A : Iface} {c : ℕ} {s : Proc X Y}
           → QB c s → QB (c ℕ.⊔ 1) (subᴵ s {A})


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
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.UC.Machine

module CategoricalCrypto.UC.QueryBound where

private
  module 𝒫 = Category 𝒫ᴵ

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

-- A process whose domain has no downward letters is certified at rate 0 with
-- nothing known about it.
qbᵢ-noDown : {A B : Iface} (S : Set) (point : Dₚ S)
             (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
           → (Neg A → ⊥) → QBᵢ S point step 0
qbᵢ-noDown {A} {B} S point step noDown =
  qbᵢ-zero S point step (λ s a → mapₚ up (step (s , inj₁ a)))
    (λ s a → map-fuse (step (s , inj₁ a)) up forget id untag ⟨≈⟩ >>=ₚ-identityʳ (step (s , inj₁ a)))
    up untag
  where
  up : S × (Neg A ⊎ Pos B) → Ans {S} (λ _ → 0) (Neg A) (Pos B) 0
  up (_ , inj₁ e) = ⊥-elim (noDown e)
  up (s , inj₂ p) = inj₂ ((s , z≤n) , p)

  untag : (y : S × (Neg A ⊎ Pos B)) → forget (up y) ≡ y
  untag (_ , inj₁ e) = ⊥-elim (noDown e)
  untag (_ , inj₂ _) = refl

qbᵢ-closed : {B : Iface} (S : Set) (point : Dₚ S)
             (step : S × (Pos unitᴵ ⊎ Neg B) → Dₚ (S × (Neg unitᴵ ⊎ Pos B)))
           → QBᵢ S point step 0
qbᵢ-closed S point step = qbᵢ-noDown S point step λ ()

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
-- apart (`Machines.Run.Sim.runᴹ-resp-≈ᴹ`).  Store that underlying machine
-- equality directly: projecting the definitionally identical relation from
-- `𝒫ᴵ` forces the whole G-construction record at composite witnesses.
QB : {A B : Iface} → ℕ → Proc A B → Set₁
QB {A} {B} c M = Σ[ N ∈ Proc A B ] Certified c N × (N MS.≈ᴹ M)

certified⇒QB : {A B : Iface} {c : ℕ} {M : Proc A B} → Certified c M → QB c M
certified⇒QB {M = M} q = M , q , MS.reflᴹ

qb-wire : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
        → QB 1 (wireᴹ {A} {B} up down)
qb-wire up down = certified⇒QB (qbᵢ-wire up down)

qb-λᴵ⇒ : {B : Iface} → QB 1 (λᴵ⇒ {B})
qb-λᴵ⇒ = qb-wire Sum.[ ⊥-elim , id ] inj₂

qb-closed : {B : Iface} (M : Proc unitᴵ B) → QB 0 M
qb-closed M = certified⇒QB (qbᵢ-closed (MC.St M) (MC.point (MC.state M) tt) (MC.step M))

qb-resp-≈ : {A B : Iface} {c : ℕ} {M N : Proc A B} → M MS.≈ᴹ N → QB c M → QB c N
qb-resp-≈ e (P , q , e′) = P , q , e′ MS.○ᴹ e

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
-- the bare wire.

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
    onRN s (inj₂ z) = returnₚ (inj₁ ((s , m<m+n (Φ s) (m≤n⊔m c 1)) , inZ⁻ z))

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

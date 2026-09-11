{-# OPTIONS --safe --without-K --guardedness #-}

-- A closed ancilla context with a hole is a plain context on the hole.
--
-- `UC.Machine.Bridge.ctxRun` observes a process plugged into `E ∘ T₁ Y ⌷ ∘ m`:
-- a test above, an ancilla `Y` beside, a closure `m` below.  `Kctx` is that
-- context with the hole exposed — `E` precomposed with the closure slid into
-- the ancilla slot — and `ctxRun-slide` says the two observations agree.  The
-- budget `Kctx` carries is `ctxBudget`, on the nose: the product `c * (c′ ⊔ 1)`
-- is exactly what `qb-∘` charges the four factors, with `qb-sub`'s guard
-- supplying the `⊔ 1`.
--
-- That turns a statement quantified over budgeted ANCILLA CONTEXTS into one
-- quantified over budgeted CLOSED CONTEXTS — the two-machine shape every
-- quantitative theorem of the layer is written at (`UC.Seam.Adequacy`,
-- `UC.QueryBound.Counting`).
--
-- The categorical content is `Categories.Category.Monoidal.Utilities.Ext.Hole`,
-- proved once in an arbitrary monoidal category; what this module owes it is
-- the two facts about the hole wire, `λ-nat` and `λ-slide`, and those are
-- case analyses on a sum rather than trace arguments because
-- `UC.Machine.Wire` has already absorbed the wires.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; _*_; _⊔_)
open import Data.Nat.Properties using (*-identityˡ; *-identityʳ; ≤-reflexive)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (tt)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Budget using (ctxBudget)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐; conjᴵ; ctxRun)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; sub-⊗₁; a⇐-α⇒)
open import CategoricalCrypto.UC.Machine.Grading using (qb-subᴳ; qb-a⇐ᴳ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.QueryBound
  using (QB; certified⇒QB; qbᵢ-wire; qb-mono; qb-resp-≈)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import Categories.Category.Monoidal.Utilities.Ext as MUExt
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Slide where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- The hole wire

-- Relaying a wire is relabelling one summand of it.
T₁-wire : (Y : Iface) {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
        → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y (wireᴹ up down))
            (wireᴹ (Sum.map (λ y → y) up) (Sum.map (λ y → y) down))
T₁-wire Y up down = ≲⇒≈ᴹ (mk-cong pt)
  where
  pt : (p : _) → _
  pt (s , inj₁ (inj₁ y)) = ≈refl
  pt (s , inj₁ (inj₂ a)) = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₁ y)) = ≈refl
  pt (s , inj₂ (inj₂ b)) = >>=ₚ-identityˡ _ _

-- Opening a hole beside a closed process commutes with the process.
λ-nat : {A B : Iface} (f : Proc A B)
      → 𝒫._≈_ {A} {unitᴵ ⊗ᴵ B} (λᴵ⇐ 𝒫.∘ f) (T₁ᴵ unitᴵ f 𝒫.∘ λᴵ⇐)
λ-nat {A} {B} f =
     wire-∘ᴹ inj₂ [ ⊥-elim , id ] f
  ○ᴹ ⟺ᴹ relayed
  ○ᴹ ⟺ᴹ (∘-wireᴹ inj₂ [ ⊥-elim , id ] (T₁ᴵ unitᴵ f))
  where
  relayed : sandwichᴹ (T₁ᴵ unitᴵ f) (Sum.map inj₂ (λ n → n))
                                    (Sum.map [ ⊥-elim , id ] (λ n → n))
            ≈ᴹ sandwichᴹ f (Sum.map (λ n → n) [ ⊥-elim , id ])
                           (Sum.map (λ n → n) inj₂)
  relayed = ≲⇒≈ᴹ (mk-cong pt)
    where
    pt : (p : _) → _
    pt (s , inj₁ a) = map-fuse (step f (s , inj₁ a)) _ _ _
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl
    pt (s , inj₂ (inj₂ b)) = map-fuse (step f (s , inj₂ b)) _ _ _
      λ where (_ , inj₁ _) → refl
              (_ , inj₂ _) → refl

-- …and the slide at the hole itself, which is where the ancilla and the
-- closure change places.  The only live activation is a query on `Y`: every
-- other summand of a closed interface is empty.
λ-slide : {Y : Iface} (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
        → 𝒫._≈_ {unitᴵ} {Y ⊗ᴵ (unitᴵ ⊗ᴵ unitᴵ)}
            (T₁ᴵ Y λᴵ⇐ 𝒫.∘ m) (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))
λ-slide {Y} m =
     𝒫.∘-resp-≈ˡ (T₁-wire Y inj₂ [ ⊥-elim , id ])
  ○ᴹ wire-∘ᴹ (Sum.map (λ y → y) inj₂) (Sum.map (λ y → y) [ ⊥-elim , id ]) m
  ○ᴹ ⟺ᴹ subbed
  ○ᴹ ⟺ᴹ (sandwich-∘ (subᴵ m) (Sum.map inj₂ (λ a → a)) (Sum.map [ ⊥-elim , id ] (λ a → a))
                             (Sum.map (λ a → a) ⊎assocˡ) (Sum.map (λ a → a) ⊎assocʳ))
  ○ᴹ ⟺ᴹ (wire-∘ᴹ ⊎assocʳ ⊎assocˡ
            (sandwichᴹ (subᴵ m) (Sum.map inj₂ (λ a → a))
                                (Sum.map [ ⊥-elim , id ] (λ a → a))))
  ○ᴹ ⟺ᴹ (𝒫.∘-resp-≈ʳ (∘-wireᴹ inj₂ [ ⊥-elim , id ] (subᴵ m)))
  where
  subbed : sandwichᴹ (subᴵ m)
             (λ x → Sum.map inj₂ (λ a → a) (Sum.map (λ a → a) ⊎assocˡ x))
             (λ y → Sum.map (λ a → a) ⊎assocʳ (Sum.map [ ⊥-elim , id ] (λ a → a) y))
           ≈ᴹ sandwichᴹ m (Sum.map (λ n → n) (Sum.map (λ y → y) [ ⊥-elim , id ]))
                          (Sum.map (λ n → n) (Sum.map (λ y → y) inj₂))
  subbed = ≲⇒≈ᴹ (mk-cong pt)
    where
    pt : (p : _) → _
    pt (s , inj₂ (inj₁ y)) = map-fuse (step m (s , inj₂ (inj₁ y))) _ _ _
      λ where (_ , inj₂ (inj₁ _)) → refl
    pt (s , inj₂ (inj₂ (inj₁ ())))
    pt (s , inj₂ (inj₂ (inj₂ ())))

------------------------------------------------------------------------
-- The slide

private
  natᴳ : {A B : 𝔾.Obj} (f : 𝔾._⇒_ A B)
       → 𝔾._≈_ (𝔾._∘_ (λᴵ⇐ {retᴵ B}) f)
               (𝔾._∘_ (𝔾._⊗₁_ (𝔾.id {⟦ unitᴵ ⟧ᴵ}) f) (λᴵ⇐ {retᴵ A}))
  natᴳ {A} {B} f = λ-nat {retᴵ A} {retᴵ B} f
                ○ᴹ 𝒫.∘-resp-≈ˡ (T₁-⊗₁ {unitᴵ} {retᴵ A} {retᴵ B} f)

  slideᴳ : {Y : 𝔾.Obj} (m : 𝔾._⇒_ ⟦ unitᴵ ⟧ᴵ (𝔾._⊗₀_ Y ⟦ unitᴵ ⟧ᴵ))
         → 𝔾._≈_ (𝔾._∘_ (𝔾._⊗₁_ (𝔾.id {Y}) (λᴵ⇐ {unitᴵ})) m)
                 (𝔾._∘_ 𝔾.associator.from
                     (𝔾._∘_ (𝔾._⊗₁_ m (𝔾.id {⟦ unitᴵ ⟧ᴵ})) (λᴵ⇐ {unitᴵ})))
  slideᴳ {Y} m =
       𝒫.∘-resp-≈ˡ (⟺ᴹ (T₁-⊗₁ {retᴵ Y} {unitᴵ} {unitᴵ ⊗ᴵ unitᴵ} λᴵ⇐))
    ○ᴹ λ-slide {retᴵ Y} m
    ○ᴹ 𝒫.∘-resp-≈ (a⇐-α⇒ {retᴵ Y} {unitᴵ} {unitᴵ})
         (𝒫.∘-resp-≈ˡ (sub-⊗₁ {unitᴵ} {retᴵ Y ⊗ᴵ unitᴵ} {unitᴵ} m))

  module H = MUExt.Hole 𝔾.monoidal {J = ⟦ unitᴵ ⟧ᴵ} (λ {B} → λᴵ⇐ {retᴵ B}) natᴳ slideᴳ

-- The context with its hole exposed.
Kctx : {B Y : Iface} → Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ unitᴵ)
     → Proc B Ωᴵ
Kctx E m = E 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))

slideᴹ : {B Y : Iface} (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
         (x : Proc unitᴵ B)
       → 𝒫._≈_ {unitᴵ} {Ωᴵ} ((E 𝒫.∘ T₁ᴵ Y (conjᴵ x)) 𝒫.∘ m) (Kctx E m 𝒫.∘ x)
slideᴹ {B} {Y} E m x =
     𝒫.assoc
  ○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.∘-resp-≈ˡ (T₁-⊗₁ {Y} {unitᴵ} {unitᴵ ⊗ᴵ B} (conjᴵ x))
                 ○ᴹ H.slide {⟦ Y ⟧ᴵ} {⟦ B ⟧ᴵ} m x
                 ○ᴹ 𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ (⟺ᴹ (a⇐-α⇒ {Y} {unitᴵ} {B}))
                      (𝒫.∘-resp-≈ˡ (⟺ᴹ (sub-⊗₁ {unitᴵ} {Y ⊗ᴵ unitᴵ} {B} m)))))
  ○ᴹ 𝒫.sym-assoc

-- What the bridge's observation becomes: the closed run of the plugged
-- process against `Kctx`.
ctxRun-slide : {B Y : Iface} (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ)
               (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) (x : Proc unitᴵ B)
             → ctxRun Y E m (conjᴵ x) ≈ₚ ⟦ Kctx E m 𝒫.∘ x ⟧ᴼ
ctxRun-slide E m x = runᴹ-resp-≈ᴹ {Ωᴵ} (slideᴹ E m x) (ask tt out)

------------------------------------------------------------------------
-- …and the budget it carries

private
  budget : (c c′ : ℕ) → c * (1 * ((c′ ⊔ 1) * 1)) ≡ ctxBudget c c′
  budget c c′ = cong (c *_) (*-identityˡ ((c′ ⊔ 1) * 1)
                    ⟨trans⟩ *-identityʳ (c′ ⊔ 1))
    where
    infixr 5 _⟨trans⟩_
    _⟨trans⟩_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    refl ⟨trans⟩ q = q

qb-Kctx : {B Y : Iface} (E : Proc (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
          {c c′ : ℕ} → QB c E → QB c′ m → QB (ctxBudget c c′) (Kctx E m)
qb-Kctx {B} {Y} E m {c} {c′} qE qm =
  qb-mono (≤-reflexive (budget c c′))
    (qb-∘-category B (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) Ωᴵ E _ qE
      (qb-∘-category B ((Y ⊗ᴵ unitᴵ) ⊗ᴵ B) (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) a⇐ᴵ _
        (qb-resp-≈ (⟺ᴹ (a⇐-α⇒ {Y} {unitᴵ} {B})) (qb-a⇐ᴳ Y unitᴵ B))
        (qb-∘-category B (unitᴵ ⊗ᴵ B) ((Y ⊗ᴵ unitᴵ) ⊗ᴵ B) (subᴵ m) λᴵ⇐
          (qb-resp-≈ (⟺ᴹ (sub-⊗₁ {unitᴵ} {Y ⊗ᴵ unitᴵ} {B} m))
            (qb-subᴳ unitᴵ (Y ⊗ᴵ unitᴵ) B m qm))
          (certified⇒QB (qbᵢ-wire {B} {unitᴵ ⊗ᴵ B} inj₂ [ ⊥-elim , id ])))))

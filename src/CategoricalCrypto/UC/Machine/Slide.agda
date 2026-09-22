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
--
-- The last section runs the hole the other way: a GRADED statement arrives
-- with the hole already open, and `UC.Model.Dominated.dominatedᵍ` has to close
-- it before `dominated` will accept the context.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; _*_; _⊔_)
open import Data.Nat.Properties using (*-identityˡ; *-identityʳ; ≤-reflexive)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Base using (tt)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Budget using (ctxBudget)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐; λᴵ⇒; conjᴵ; ctxRun)
open import CategoricalCrypto.UC.Machine.Dictionary
  using (T₁-⊗₁; T₁-∘; T₁-resp-≈; sub-⊗₁; sub-∘; a⇐-α⇒; a⇒-α⇐)
open import CategoricalCrypto.UC.Machine.Grading using (qb-subᴳ; qb-a⇐ᴳ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.QueryBound
  using (QB; certified⇒QB; qbᵢ-wire; qb-mono; qb-resp-≈)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)

import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Utilities as MU
import Categories.Category.Monoidal.Utilities.Ext as MUExt
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Slide where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open MR 𝔾.monoidal
open MU.Shorthands 𝔾.monoidal using () renaming (α⇐ to α⇐ᴳ)
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

-- …and the bypassed relay relabels a wire the same way.
sub-wire : {A B C : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
         → 𝒫._≈_ {A ⊗ᴵ C} {B ⊗ᴵ C} (subᴵ (wireᴹ up down))
             (wireᴹ (Sum.map up (λ c → c)) (Sum.map down (λ c → c)))
sub-wire up down = ≲⇒≈ᴹ (mk-cong pt)
  where
  pt : (p : _) → _
  pt (s , inj₁ (inj₁ a)) = >>=ₚ-identityˡ _ _
  pt (s , inj₁ (inj₂ c)) = ≈refl
  pt (s , inj₂ (inj₁ b)) = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₂ c)) = ≈refl

-- Opening a hole beside a pair is opening it beside the first component.
λ-tri : {B F : Iface}
      → 𝒫._≈_ {B ⊗ᴵ F} {(unitᴵ ⊗ᴵ B) ⊗ᴵ F} (a⇒ᴵ 𝒫.∘ λᴵ⇐) (subᴵ λᴵ⇐)
λ-tri {B} {F} =
     ∘-wireᴹ inj₂ [ ⊥-elim , id ] (a⇒ᴵ {unitᴵ} {B} {F})
  ○ᴹ ≲⇒≈ᴹ (mk-cong pt)
  ○ᴹ ⟺ᴹ (sub-wire inj₂ [ ⊥-elim , id ])
  where
  pt : (p : _) → _
  pt (s , inj₁ (inj₁ _))        = >>=ₚ-identityˡ _ _
  pt (s , inj₁ (inj₂ _))        = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₁ (inj₁ ())))
  pt (s , inj₂ (inj₁ (inj₂ _))) = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₂ _))        = >>=ₚ-identityˡ _ _

-- Closing the trivial ancilla at the hole is closing it beside the process.
ρᴵ⇒ : {Y : Iface} → Proc (Y ⊗ᴵ unitᴵ) Y
ρᴵ⇒ = wireᴹ [ id , ⊥-elim ] inj₁

ρ-tri : {Y B : Iface}
      → 𝒫._≈_ {(Y ⊗ᴵ unitᴵ) ⊗ᴵ B} {Y ⊗ᴵ B} (T₁ᴵ Y λᴵ⇒ 𝒫.∘ a⇐ᴵ) (subᴵ ρᴵ⇒)
ρ-tri {Y} {B} =
     𝒫.∘-resp-≈ˡ (T₁-wire Y [ ⊥-elim , id ] inj₂)
  ○ᴹ wire-∘ᴹ (Sum.map (λ y → y) [ ⊥-elim , id ]) (Sum.map (λ y → y) inj₂)
             (a⇐ᴵ {Y} {unitᴵ} {B})
  ○ᴹ ≲⇒≈ᴹ (mk-cong pt)
  ○ᴹ ⟺ᴹ (sub-wire [ id , ⊥-elim ] inj₁)
  where
  pt : (p : _) → _
  pt (s , inj₁ (inj₁ (inj₁ _)))  = >>=ₚ-identityˡ _ _
  pt (s , inj₁ (inj₁ (inj₂ ())))
  pt (s , inj₁ (inj₂ _))         = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₁ _))         = >>=ₚ-identityˡ _ _
  pt (s , inj₂ (inj₂ _))         = >>=ₚ-identityˡ _ _

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

-- A closed ancilla wired in beside the hole crosses a relay ON the hole: the
-- interchange of the closure acting on the ancilla leg with the relay acting
-- on the hole, every other factor being a wire.  The only facts it spends are
-- the hole wire's naturality and its triangle.
relay-slide : {Y B F : Iface} (w : Proc unitᴵ Y) (μ : Proc B (B ⊗ᴵ F))
            → 𝒫._≈_ {B} {(Y ⊗ᴵ B) ⊗ᴵ F}
                (a⇒ᴵ 𝒫.∘ (T₁ᴵ Y μ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)))
                (subᴵ (subᴵ w 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
relay-slide {Y} {B} {F} w μ = begin
  a⇒ᴵ 𝒫.∘ (T₁ᴵ Y μ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐))
    ≈⟨ 𝒫.∘-resp-≈ (a⇒-α⇐ {Y} {B} {F})
         (𝒫.∘-resp-≈ (T₁-⊗₁ {Y} μ) (𝒫.∘-resp-≈ˡ (sub-⊗₁ {unitᴵ} {Y} {B} w))) ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {Y}) μ 𝒫.∘ (𝔾._⊗₁_ w (𝒫.id {B}) 𝒫.∘ λᴵ⇐))
    ≈⟨ refl⟩∘⟨ 𝒫.sym-assoc ⟩
  α⇐ᴳ 𝒫.∘ ((𝔾._⊗₁_ (𝒫.id {Y}) μ 𝒫.∘ 𝔾._⊗₁_ w (𝒫.id {B})) 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ (⟺ serialize₂₁ ⟩∘⟨refl) ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ w μ 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ (serialize₁₂ ⟩∘⟨refl) ⟩
  α⇐ᴳ 𝒫.∘ ((𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F}) 𝒫.∘ 𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ) 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ 𝒫.assoc ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F}) 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐))
    ≈⟨ 𝒫.sym-assoc ⟩
  (α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F})) 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ⟺ 𝔾.⊗.identity)) ⟩∘⟨refl ⟩
  (α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w (𝔾._⊗₁_ (𝒫.id {B}) (𝒫.id {F})))
    𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ 𝔾.assoc-commute-to ⟩∘⟨refl ⟩
  (𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ α⇐ᴳ)
    𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ 𝒫.assoc ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F})
    𝒫.∘ (α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐))
    ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ (λ-nat μ ○ᴹ 𝒫.∘-resp-≈ˡ (T₁-⊗₁ {unitᴵ} μ))) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (α⇐ᴳ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ))
    ≈⟨ refl⟩∘⟨ 𝒫.sym-assoc ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ ((α⇐ᴳ 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
    ≈˘⟨ refl⟩∘⟨ ((a⇒-α⇐ {unitᴵ} {B} {F} ⟩∘⟨refl) ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ ((a⇒ᴵ 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
    ≈⟨ refl⟩∘⟨ (λ-tri ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (subᴵ λᴵ⇐ 𝒫.∘ μ)
    ≈⟨ refl⟩∘⟨ (sub-⊗₁ {B} {unitᴵ ⊗ᴵ B} {F} λᴵ⇐ ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (𝔾._⊗₁_ λᴵ⇐ (𝒫.id {F}) 𝒫.∘ μ)
    ≈⟨ 𝒫.sym-assoc ⟩
  (𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ 𝔾._⊗₁_ λᴵ⇐ (𝒫.id {F})) 𝒫.∘ μ
    ≈˘⟨ 𝔾.⊗.homomorphism ⟩∘⟨refl ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B}) 𝒫.∘ λᴵ⇐) (𝒫.id {F} 𝒫.∘ 𝒫.id {F}) 𝒫.∘ μ
    ≈⟨ ((⟺ (sub-⊗₁ {unitᴵ} {Y} {B} w) ⟩∘⟨refl) ⟩⊗⟨ 𝒫.identity²) ⟩∘⟨refl ⟩
  𝔾._⊗₁_ (subᴵ w 𝒫.∘ λᴵ⇐) (𝒫.id {F}) 𝒫.∘ μ
    ≈˘⟨ sub-⊗₁ {B} {Y ⊗ᴵ B} {F} (subᴵ w 𝒫.∘ λᴵ⇐) ⟩∘⟨refl ⟩
  subᴵ (subᴵ w 𝒫.∘ λᴵ⇐) 𝒫.∘ μ ∎

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
-- Closing the hole again

-- A renaming by two identities is no renaming.
sandwich-id : {X Y : Set} (f : Machine X Y) (i : X → X) (o : Y → Y)
            → ((z : X) → i z ≡ z) → ((w : Y) → o w ≡ w)
            → sandwichᴹ f i o ≈ᴹ f
sandwich-id f i o ei eo = ≲⇒≈ᴹ (mk-cong pt)
  where
  pt : (p : _) → _
  pt (s , z) = ≡⇒≈ₚ (cong (λ w → mapₚ (λ q → proj₁ q , o (proj₂ q)) (step f (s , w))) (ei z))
           ⟨≈⟩ map-eq (step f (s , z)) _ (λ q → q)
                      (λ q → cong (proj₁ q ,_) (eo (proj₂ q)))
           ⟨≈⟩ >>=ₚ-identityʳ (step f (s , z))

-- The two hole wires absorb into one renaming, and that renaming is the
-- identity.
unit-cancel : {B : Iface} (x : Proc unitᴵ B) → 𝒫._≈_ {unitᴵ} {B} (λᴵ⇒ 𝒫.∘ conjᴵ x) x
unit-cancel {B} x =
     𝒫.∘-resp-≈ʳ (wire-∘ᴹ inj₂ [ ⊥-elim , id ] x)
  ○ᴹ wire-∘ᴹ [ ⊥-elim , id ] inj₂ (sandwichᴹ x i₁ o₁)
  ○ᴹ sandwich-∘ x i₁ o₁ i₂ o₂
  ○ᴹ sandwich-id x (λ z → i₁ (i₂ z)) (λ y → o₂ (o₁ y))
       (λ where (inj₁ ())
                (inj₂ _) → refl)
       (λ where (inj₁ ())
                (inj₂ _) → refl)
  where
  i₁ : Pos unitᴵ ⊎ Neg (unitᴵ ⊗ᴵ B) → Pos unitᴵ ⊎ Neg B
  i₁ = Sum.map (λ a → a) [ ⊥-elim , id ]

  o₁ : Neg unitᴵ ⊎ Pos B → Neg unitᴵ ⊎ Pos (unitᴵ ⊗ᴵ B)
  o₁ = Sum.map (λ a → a) inj₂

  i₂ : Pos unitᴵ ⊎ Neg B → Pos unitᴵ ⊎ Neg (unitᴵ ⊗ᴵ B)
  i₂ = Sum.map (λ a → a) inj₂

  o₂ : Neg unitᴵ ⊎ Pos (unitᴵ ⊗ᴵ B) → Neg unitᴵ ⊎ Pos B
  o₂ = Sum.map (λ a → a) [ ⊥-elim , id ]

-- …so relaying it past an ancilla is no relay either.
T₁-conj : {Y B : Iface} (x : Proc unitᴵ B)
        → 𝒫._≈_ {Y ⊗ᴵ unitᴵ} {Y ⊗ᴵ B} (T₁ᴵ Y x) (T₁ᴵ Y (λᴵ⇒ {B}) 𝒫.∘ T₁ᴵ Y (conjᴵ x))
T₁-conj {Y} {B} x =
  T₁-resp-≈ (𝒫.Equiv.sym (unit-cancel x)) ○ᴹ T₁-∘ (λᴵ⇒ {B}) (conjᴵ x)

-- …hence the bridge's observation is unchanged by opening the hole.
ctxRun-conj : {B Y : Iface} (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
              (x : Proc unitᴵ B)
            → ctxRun Y E m x ≈ₚ ctxRun Y (E 𝒫.∘ T₁ᴵ Y (λᴵ⇒ {B})) m (conjᴵ x)
ctxRun-conj {B} {Y} E m x =
  runᴹ-resp-≈ᴹ {Ωᴵ}
    (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (T₁-conj x) ○ᴹ 𝒫.sym-assoc)) (ask tt out)

------------------------------------------------------------------------
-- …and the budget it carries

private
  budget : (c c′ : ℕ) → c * (1 * ((c′ ⊔ 1) * 1)) ≡ ctxBudget c c′
  budget c c′ = cong (c *_) (trans (*-identityˡ ((c′ ⊔ 1) * 1))
                                   (*-identityʳ (c′ ⊔ 1)))

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

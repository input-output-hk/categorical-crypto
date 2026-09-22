{-# OPTIONS --safe --without-K --guardedness #-}

-- Compiling a monitor and closing an ancilla context commute: the compiled
-- context of `UC.Quantitative.Hits` with its closure slid in is the monitor
-- over the CLOSED test, and hence — through `Monitor.Agree`'s two collapses —
-- one machine whose state carries the accumulator.
--
-- The content is one interchange: the closure `m` acts on the ancilla leg and
-- the monitor on the hole, so the two cross, and every other factor is a wire.
-- `relay-slide` is that interchange in the monoidal spelling, at the hole wire
-- `λᴵ⇐` rather than at a unitor — the machine layer's closed interface is not
-- the 𝒢-tensor's unit (`UC.Machine.Dictionary.𝟭ᴵ`).

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_])
open import Function.Base using (id)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning using (≈refl)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐; λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; a⇒-α⇐; sub-⊗₁)
open import CategoricalCrypto.UC.Machine.Monitor using (Flagᴵ; compileᴹ; flagReadᴹ; monitorᴹ)
open import CategoricalCrypto.UC.Machine.Monitor.Agree
  using (mon-wire; monᴹ; module Read; module Watch)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; T₁-wire; λ-nat)
open import CategoricalCrypto.UC.Machine.Wire

import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Utilities as MU
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Monitor.Slide where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open MR 𝔾.monoidal
open MU.Shorthands 𝔾.monoidal using () renaming (α⇐ to α⇐ᴳ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- The bypassed relay is a functor
--
-- `UC.Machine.Dictionary`'s `T₁-resp-≈`/`T₁-∘` on the other leg; these belong
-- there beside them.

sub-resp-≈ : {X Y A : Iface} {f g : Proc X Y} → 𝒫._≈_ {X} {Y} f g
           → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ f) (subᴵ g)
sub-resp-≈ {X} {Y} {A} {f} {g} e =
     sub-⊗₁ {X} {Y} {A} f
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ)} {(⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ)}
       {(f , 𝒫.id {A})} {(g , 𝒫.id {A})} (e , 𝔾.Equiv.refl {x = 𝒫.id {A}})
  ○ᴹ ⟺ᴹ (sub-⊗₁ {X} {Y} {A} g)

sub-∘ : {X Y Z A : Iface} (g : Proc Y Z) (f : Proc X Y)
      → 𝒫._≈_ {X ⊗ᴵ A} {Z ⊗ᴵ A} (subᴵ (g 𝒫.∘ f)) (subᴵ g 𝒫.∘ subᴵ f)
sub-∘ {X} {Y} {Z} {A} g f =
     sub-⊗₁ {X} {Z} {A} (g 𝒫.∘ f)
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ)} {(⟦ Z ⟧ᴵ , ⟦ A ⟧ᴵ)}
       {(g 𝒫.∘ f , 𝒫.id {A})} {(g 𝒫.∘ f , 𝒫.id {A} 𝒫.∘ 𝒫.id {A})}
       (𝔾.Equiv.refl {x = g 𝒫.∘ f} , 𝒫.Equiv.sym 𝒫.identity²)
  ○ᴹ 𝔾.⊗.homomorphism
  ○ᴹ ⟺ᴹ (𝒫.∘-resp-≈ (sub-⊗₁ {Y} {Z} {A} g) (sub-⊗₁ {X} {Y} {A} f))

-- …and it relabels a wire, as `UC.Machine.Slide.T₁-wire` does on the other.
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

------------------------------------------------------------------------
-- The two wire identities the slide spends

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

------------------------------------------------------------------------
-- The interchange

-- A closed ancilla wired in beside the hole crosses a relay ON the hole.
-- This is `Categories.Category.Monoidal.Utilities.Ext.Hole` material: the
-- only facts it spends are the hole wire's naturality and its triangle.
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
-- The compiled context, closed

-- `Monitor.Agree`'s two collapses, as one: the monitored test over a closed
-- one is a single machine, whose state carries the accumulator.
watch-collapsed : (B : Iface) (report : Neg B → Pos B → Bool)
                  (D : Proc (unitᴵ ⊗ᴵ B) Ωᴵ)
                → 𝒫._≈_ {B} {Ωᴵ}
                    ((flagReadᴹ 𝒫.∘ subᴵ D) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ monitorᴹ report)))
                    (Watch.watchᴹ B report D)
watch-collapsed B report D =
     𝒫.∘-resp-≈ (Read.read-collapse (unitᴵ ⊗ᴵ B) D) (mon-wire B report)
  ○ᴹ Watch.watch-collapse B report D

-- …so the collapsed machine respects the machine equality in its test, which
-- `Watch.watchᴹ` itself does not visibly do.
watch-resp-≈ : (B : Iface) (report : Neg B → Pos B → Bool)
               {D₀ D₁ : Proc (unitᴵ ⊗ᴵ B) Ωᴵ} → 𝒫._≈_ {unitᴵ ⊗ᴵ B} {Ωᴵ} D₀ D₁
             → 𝒫._≈_ {B} {Ωᴵ} (Watch.watchᴹ B report D₀) (Watch.watchᴹ B report D₁)
watch-resp-≈ B report e =
     ⟺ᴹ (watch-collapsed B report _)
  ○ᴹ 𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (sub-resp-≈ e))
  ○ᴹ watch-collapsed B report _

-- The original test with the ancilla closed by `m`, the hole still open.
closedᴹ : (Y B : Iface) → Proc (Y ⊗ᴵ B) Ωᴵ → Proc unitᴵ (Y ⊗ᴵ unitᴵ)
        → Proc (unitᴵ ⊗ᴵ B) Ωᴵ
closedᴹ Y B E m = (E 𝒫.∘ T₁ᴵ Y λᴵ⇒) 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)

-- The monitored context of `UC.Quantitative.EventLift.openedᴹ`, with its
-- closure slid in, IS the collapsed watch over the closed test.
compiled-slide : (Y B : Iface) (report : Neg B → Pos B → Bool)
                 (E : Proc (Y ⊗ᴵ B) Ωᴵ) (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ))
               → 𝒫._≈_ {B} {Ωᴵ}
                   (Kctx (compileᴹ Y B (monitorᴹ report) E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m)
                   (Watch.watchᴹ B report (closedᴹ Y B E m))
compiled-slide Y B report E m = begin
  Kctx (compileᴹ Y B μ E 𝒫.∘ T₁ᴵ Y λᴵ⇒) m
    ≈⟨ 𝒫.assoc ⟩
  (flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ)))
    𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐)))
    ≈⟨ 𝒫.assoc ⟩
  flagReadᴹ 𝒫.∘ ((subᴵ E 𝒫.∘ (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ))
                 𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))))
    ≈⟨ refl⟩∘⟨ 𝒫.assoc ⟩
  flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ ((a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ)
                              𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐)))))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ core) ⟩
  flagReadᴹ 𝒫.∘ (subᴵ E 𝒫.∘ (subᴵ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m))
                              𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ))))
    ≈⟨ refl⟩∘⟨ 𝒫.sym-assoc ⟩
  flagReadᴹ 𝒫.∘ ((subᴵ E 𝒫.∘ subᴵ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)))
                 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ)))
    ≈˘⟨ refl⟩∘⟨ (sub-∘ E (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)) ⟩∘⟨refl) ⟩
  flagReadᴹ 𝒫.∘ (subᴵ (E 𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)))
                 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ)))
    ≈˘⟨ refl⟩∘⟨ (sub-resp-≈ 𝒫.assoc ⟩∘⟨refl) ⟩
  flagReadᴹ 𝒫.∘ (subᴵ (closedᴹ Y B E m) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ)))
    ≈⟨ 𝒫.sym-assoc ⟩
  (flagReadᴹ 𝒫.∘ subᴵ (closedᴹ Y B E m)) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ))
    ≈⟨ 𝒫.∘-resp-≈ (Read.read-collapse (unitᴵ ⊗ᴵ B) (closedᴹ Y B E m))
                  (mon-wire B report) ⟩
  Read.readᴹ (unitᴵ ⊗ᴵ B) (closedᴹ Y B E m) 𝒫.∘ monᴹ B report
    ≈⟨ Watch.watch-collapse B report (closedᴹ Y B E m) ⟩
  Watch.watchᴹ B report (closedᴹ Y B E m) ∎
  where
  μ = monitorᴹ report

  w : Proc unitᴵ Y
  w = ρᴵ⇒ 𝒫.∘ m

  -- The four wires below the monitor are the ancilla `w` wired in beside the
  -- hole; `relay-slide` then crosses it.
  bottom : 𝒫._≈_ {B} {Y ⊗ᴵ B}
             (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))) (subᴵ w 𝒫.∘ λᴵ⇐)
  bottom = 𝒫.sym-assoc ○ᴹ (ρ-tri ⟩∘⟨refl) ○ᴹ 𝒫.sym-assoc
      ○ᴹ (⟺ (sub-∘ ρᴵ⇒ m) ⟩∘⟨refl)

  core : 𝒫._≈_ {B} {(Y ⊗ᴵ B) ⊗ᴵ Flagᴵ}
           ((a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ) 𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐))))
           (subᴵ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ)))
  core = begin
    (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ) 𝒫.∘ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ (subᴵ m 𝒫.∘ λᴵ⇐)))
      ≈⟨ refl⟩∘⟨ bottom ⟩
    (a⇒ᴵ 𝒫.∘ T₁ᴵ Y μ) 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)
      ≈⟨ 𝒫.assoc ⟩
    a⇒ᴵ 𝒫.∘ (T₁ᴵ Y μ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐))
      ≈⟨ relay-slide w μ ⟩
    subᴵ (subᴵ w 𝒫.∘ λᴵ⇐) 𝒫.∘ μ
      ≈⟨ sub-∘ (subᴵ w) λᴵ⇐ ⟩∘⟨refl ⟩
    (subᴵ (subᴵ w) 𝒫.∘ subᴵ λᴵ⇐) 𝒫.∘ μ
      ≈˘⟨ (refl⟩∘⟨ λ-tri) ⟩∘⟨refl ⟩
    (subᴵ (subᴵ w) 𝒫.∘ (a⇒ᴵ 𝒫.∘ λᴵ⇐)) 𝒫.∘ μ
      ≈⟨ 𝒫.assoc ⟩
    subᴵ (subᴵ w) 𝒫.∘ ((a⇒ᴵ 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
      ≈⟨ refl⟩∘⟨ 𝒫.assoc ⟩
    subᴵ (subᴵ w) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ))
      ≈˘⟨ sub-resp-≈ (𝒫.sym-assoc ○ᴹ (ρ-tri ⟩∘⟨refl) ○ᴹ ⟺ (sub-∘ ρᴵ⇒ m)) ⟩∘⟨refl ⟩
    subᴵ (T₁ᴵ Y λᴵ⇒ 𝒫.∘ (a⇐ᴵ 𝒫.∘ subᴵ m)) 𝒫.∘ (a⇒ᴵ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ)) ∎

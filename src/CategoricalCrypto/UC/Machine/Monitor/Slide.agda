{-# OPTIONS --safe --without-K --guardedness #-}

-- Compiling a monitor and closing an ancilla context commute: the compiled
-- context of `UC.Quantitative.Hits` with its closure slid in is the monitor
-- over the CLOSED test, and hence — through `Monitor.Agree`'s two collapses —
-- one machine whose state carries the accumulator.
--
-- The content is one interchange: the closure `m` acts on the ancilla leg and
-- the monitor on the hole, so the two cross, and every other factor is a wire.
-- That interchange is `UC.Machine.Slide.Relay.relay-slide`, at the hole wire
-- `λᴵ⇐` rather than at a unitor — the machine layer's closed interface is not
-- the 𝒢-tensor's unit (`UC.Machine.Dictionary.𝟭ᴵ`).

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (Bool)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐; λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-resp-≈; sub-∘)
open import CategoricalCrypto.UC.Machine.Monitor using (Flagᴵ; compileᴹ; flagReadᴹ; monitorᴹ)
open import CategoricalCrypto.UC.Machine.Monitor.Agree
  using (mon-wire; monᴹ; module Read; module Watch)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; λ-tri; ρ-tri; ρᴵ⇒)
open import CategoricalCrypto.UC.Machine.Slide.Relay using (relay-slide)

import Categories.Category.Monoidal.Reasoning as MR
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Monitor.Slide where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open MR 𝔾.monoidal
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

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

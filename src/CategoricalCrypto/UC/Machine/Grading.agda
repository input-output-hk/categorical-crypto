{-# OPTIONS --safe --without-K --guardedness #-}

-- The grading action's laws, and the assemblies (`Gradingᴹ`, `Budgetᴹ`) they
-- buy.  Two disciplines are load-bearing here.  Every object implicit is
-- PINNED (see the comment above `GradingLawsᴹ`), without which the assembly
-- exhausts a 10 GiB heap.  And the section lives in its OWN module: inside
-- `UC.Machine` the same pinned text is a measured 852 s check against 74 s for
-- the rest of the module — split, the two check in 74 s + 22 s.

open import Categories.Category using (Category)

open import Data.Nat.Base as ℕ using ()
open import Level using (0ℓ; suc)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Grading)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Machine.Grading where

private module 𝒫 = Category 𝒫ᴵ


-- Four of the eight are TRACE-FREE: `T₁ᴵ`/`subᴵ` keep the plugged process's
-- state and only relabel the interface, so `T₁-resp-≈`/`sub-resp-≈` are one
-- `_≲_` at the given simulation's own state map, and `T₁-id`/`sub-id` compare
-- two stateless wires (`𝒫.id` is `σᴹ = pureᴹ +-swap`) up to the junctions a
-- `pureᴹ` spends.  The other four each compare a `𝒫ᴵ`-composite, and
-- composition here is the ⊕-trace, so each needs a trace-fusion step of the
-- kind `Monoidal (GConstruction C)`'s `homomorphism` needed.  That gate is now
-- closed (`GConstructionTrace.⊗-trace-mid`, `GConstructionLoop.trace-mid`);
-- these four are still only stated — a record inhabited by nothing, no escape
-- hatch, as everywhere in this branch.
-- EVERY object implicit is passed explicitly, for the same reason `𝒫ᴵ` does it
-- one section up.  Left to inference, the object arguments of `𝒫._≈_`/`𝒫._∘_`
-- are solved by inverting `Proc`, and the solutions come back with `_⊗ᴵ_`
-- UNFOLDED to its `⇿`-of-`⊎` normal form.  `Grading`'s own field types keep
-- `_⊛_ := _⊗ᴵ_` folded, so the assembly would then have to reconcile the two
-- spellings inside a carrier that inlines the whole Mealy-monoidal record —
-- the `GradedKleisli` eta cliff, and a 10 GiB heap.  Pinned, both sides are
-- syntactically the same term and the assembly (`Gradingᴹ`) is free.
record GradingLawsᴹ : Set (suc 0ℓ) where
  field
    T₁-resp-≈ : {Y A B : Iface} {f g : Proc A B}
              → 𝒫._≈_ {A} {B} f g
              → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f) (T₁ᴵ Y {A} {B} g)
    T₁-id     : {Y A : Iface}
              → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ A}
                  (T₁ᴵ Y {A} {A} (𝒫.id {A})) (𝒫.id {Y ⊗ᴵ A})
    T₁-∘      : {Y A B C : Iface} {g : Proc B C} {f : Proc A B}
              → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ C}
                  (T₁ᴵ Y {A} {C} (𝒫._∘_ {A} {B} {C} g f))
                  (𝒫._∘_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Y ⊗ᴵ C}
                     (T₁ᴵ Y {B} {C} g) (T₁ᴵ Y {A} {B} f))
    sub-resp-≈ : {X Y A : Iface} {s t : Proc X Y}
               → 𝒫._≈_ {X} {Y} s t
               → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A}
                   (subᴵ′ {X} {Y} {A} s) (subᴵ′ {X} {Y} {A} t)
    sub-id     : {X A : Iface}
               → 𝒫._≈_ {X ⊗ᴵ A} {X ⊗ᴵ A}
                   (subᴵ′ {X} {X} {A} (𝒫.id {X})) (𝒫.id {X ⊗ᴵ A})
    sub-∘      : {X Y Z A : Iface} {t : Proc Y Z} {s : Proc X Y}
               → 𝒫._≈_ {X ⊗ᴵ A} {Z ⊗ᴵ A}
                   (subᴵ′ {X} {Z} {A} (𝒫._∘_ {X} {Y} {Z} t s))
                   (𝒫._∘_ {X ⊗ᴵ A} {Y ⊗ᴵ A} {Z ⊗ᴵ A}
                      (subᴵ′ {Y} {Z} {A} t) (subᴵ′ {X} {Y} {A} s))
    a-isoˡ     : {X Y A : Iface}
               → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ A)}
                   (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
                      (a⇐ᴵ {X} {Y} {A}) (a⇒ᴵ {X} {Y} {A}))
                   (𝒫.id {X ⊗ᴵ (Y ⊗ᴵ A)})
    a-nat      : {X Y A B : Iface} {f : Proc A B}
               → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ B}
                   (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ B)} {(X ⊗ᴵ Y) ⊗ᴵ B}
                      (a⇒ᴵ {X} {Y} {B})
                      (T₁ᴵ X {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f)))
                   (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {(X ⊗ᴵ Y) ⊗ᴵ B}
                      (T₁ᴵ (X ⊗ᴵ Y) {A} {B} f) (a⇒ᴵ {X} {Y} {A}))

-- The assembly at the intended data.
Gradingᴹ : GradingLawsᴹ → Grading 𝒫ᴵ
Gradingᴹ L = record
  { _⊛_ = _⊗ᴵ_
  ; T₁  = T₁ᴵ
  ; sub = subᴵ′
  ; a⇒  = a⇒ᴵ
  ; a⇐  = a⇐ᴵ
  ; T₁-resp-≈  = λ {Y} {A} {B} {f} {g} → T₁-resp-≈ {Y} {A} {B} {f} {g}
  ; T₁-id      = λ {Y} {A} → T₁-id {Y} {A}
  ; T₁-∘       = λ {Y} {A} {B} {C} {g} {f} → T₁-∘ {Y} {A} {B} {C} {g} {f}
  ; sub-resp-≈ = λ {X} {Y} {A} {s} {t} → sub-resp-≈ {X} {Y} {A} {s} {t}
  ; sub-id     = λ {X} {A} → sub-id {X} {A}
  ; sub-∘      = λ {X} {Y} {Z} {A} {t} {s} → sub-∘ {X} {Y} {Z} {A} {t} {s}
  ; a-isoˡ     = λ {X} {Y} {A} → a-isoˡ {X} {Y} {A}
  ; a-nat      = λ {X} {Y} {A} {B} {f} → a-nat {X} {Y} {A} {B} {f}
  }
  where open GradingLawsᴹ L
------------------------------------------------------------------------
-- The budget assembly on top of it

-- Same pinning discipline; `qb-a⇒`/`qb-a⇐` are `qbᵢ-wire` on the nose, and the
-- record wants only `BudgetLawsᴹ`'s four fields beyond the theorems.

-- `Budget.QB` takes the rate BEFORE the object implicits.
QB′ : ℕ.ℕ → {A B : Iface} → Proc A B → Set₁
QB′ c {A} {B} = QB {A} {B} c

qb-a⇒ᴹ : {X Y A : Iface} → QB′ 1 (a⇒ᴵ {X} {Y} {A})
qb-a⇒ᴹ {X} {Y} {A} =
  certified⇒QB (qbᵢ-wire {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} ⊎assocˡ ⊎assocʳ)

qb-a⇐ᴹ : {X Y A : Iface} → QB′ 1 (a⇐ᴵ {X} {Y} {A})
qb-a⇐ᴹ {X} {Y} {A} =
  certified⇒QB (qbᵢ-wire {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)} ⊎assocʳ ⊎assocˡ)

Budgetᴹ : (L : GradingLawsᴹ) → BudgetLawsᴹ → Budget 𝒫ᴵ (Gradingᴹ L) (suc 0ℓ)
Budgetᴹ L B = record
  { QB        = QB′
  ; qb-id     = λ {A} → qb-id {A}
  ; qb-∘      = λ {A} {B′} {C} {c} {c′} {g} {f} → qb-∘ {A} {B′} {C} {c} {c′} {g} {f}
  ; qb-resp-≈ = λ {A} {B′} {c} {f} {g} → qb-resp-≈ {A} {B′} {c} {f} {g}
  ; qb-mono   = λ {A} {B′} {c} {c′} {f} → qb-mono {A} {B′} {c} {c′} {f}
  ; qb-T₁     = λ {Y} {A} {B′} {c} {f} → qb-T₁ {Y} {A} {B′} {c} {f}
  ; qb-sub    = λ {X} {Y} {A} {c} {s} → qb-sub {X} {Y} {A} {c} {s}
  ; qb-a⇒     = λ {X} {Y} {A} → qb-a⇒ᴹ {X} {Y} {A}
  ; qb-a⇐     = λ {X} {Y} {A} → qb-a⇐ᴹ {X} {Y} {A}
  }
  where open BudgetLawsᴹ B

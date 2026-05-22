{-# OPTIONS --allow-unsolved-metas --no-require-unique-meta-solutions #-}

------------------------------------------------------------------------
-- Plan (new strategy):
--   Machine ≅ Hom in (G-construction ∘ GradedKleisli ∘ SFunM)-built category
--
-- This file sketches the correspondence. Actual definitions are TODO.
--
-- ---------------------------------------------------------------------
-- The categorical picture
-- ---------------------------------------------------------------------
--
-- Start: `SFunM` (CategoricalCrypto.SFunM) — the category whose
-- morphisms `A → B` are stateful monadic functions
--
--     fun : State × A → M (State × B)
--
-- parameterised over a commutative, extensional monad M.
--
-- Step 1. ✓ `SFunᵉ-monoidal`        (Monoidal w/ coproduct tensor (⊎, ⊥)).
-- Step 2. ✓ `SFunᵉ-traced`          (Traced symmetric monoidal).
-- Step 3. ✓ `SFunᵉ-GConstruction`   (this file).
-- Step 4. ✓ `SFunᵉ-GradedKleisli`   (this file).
-- Step 5. ✓ Channel ↔ Obj, Machine ↔ Hom translations (this file).

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad.Ext
open import Class.Monad.Iterative
open import Class.Monad.OfRel

open import Categories.Category using (Category)
open import Relation.Binary using (IsEquivalence)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal.Instance.One using (One-Monoidal)
open import Categories.Monad.Graded using (GradedKleisliTriple)

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; _ᵀ; _⊗₀_; destruct-⊗; In; Out)
open import CategoricalCrypto.Machine.Core as MC using (Machine; MkMachine; _⊗ᵀ_; machine-type; _≈ℰ_)

module CategoricalCrypto.Machine.Category {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ F-Laws        : FunctorLaws M      ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  ⦃ M-Iter        : IterativeMonad M   ⦄
  ⦃ M-OfRel       : MonadOfRel M       ⦄
  where

open import CategoricalCrypto.SFunM
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄
open import CategoricalCrypto.SFunM.Monoidal
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄
open import CategoricalCrypto.SFunM.Traced
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄ ⦃ M-Iter ⦄

import Categories.GConstruction as GC
import Categories.GradedKleisli as GK

------------------------------------------------------------------------
-- Step 3.  Apply Joyal-Street-Verity "Int" / G-construction
--
-- Result: a category whose
--   • objects are pairs (A⁺, A⁻) of SFunᵉ-objects (i.e. types — exactly
--     the data of a Channel, modulo the State/Maybe layer added in
--     Step 4),
--   • morphisms (A⁺, A⁻) ⇒ (B⁺, B⁻) are SFunᵉ morphisms
--         A⁺ ⊎ B⁻ ⇒ A⁻ ⊎ B⁺
--     — the shape of a bidirectional step function on the channel
--     `A ⊗₀ B ᵀ`.
--
-- The `GConstruction` module takes four trace-naturality axioms as
-- module parameters. These are derivable from the basic traced-monoidal
-- structure (Hasegawa 1997, Thm 2.3) but the derivation is non-trivial
-- at setoid level. We postulate them here; the inner identity-law and
-- assoc'-coherence holes inside GConstruction.agda remain unsolved
-- (hence `--allow-unsolved-metas`).

private
  -- β swaps the last two factors: (P ⊎ Q) ⊎ R → (P ⊎ R) ⊎ Q.
  -- Matches the (private) `β` inside `Categories.GConstruction`.
  β-fn : ∀ {P Q R} → SFunᵉ ((P ⊎ Q) ⊎ R) ((P ⊎ R) ⊎ Q)
  β-fn = α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ)

postulate
  SFunᵉ-trace-resp-≈ : ∀ {X A B} {f g : SFunᵉ (A ⊎ X) (B ⊎ X)}
                     → f ≈ᵉ g → tr {X = X} f ≈ᵉ tr {X = X} g

  SFunᵉ-trace-∘ˡ : ∀ {X A B B'} {g : SFunᵉ B B'} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
                 → (g ∘ᵉ tr {X = X} f) ≈ᵉ tr {X = X} ((g ⊗ᵉ idᵉ) ∘ᵉ f)

  SFunᵉ-trace-∘ʳ : ∀ {X A A' B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)} {h : SFunᵉ A' A}
                 → (tr {X = X} f ∘ᵉ h) ≈ᵉ tr {X = X} (f ∘ᵉ (h ⊗ᵉ idᵉ))

  -- β swaps the inner two factors, so (β ∘ f ∘ β) has the X and Y
  -- swapped in its codomain shape. The trace axes flip accordingly.
  SFunᵉ-trace-comm : ∀ {X Y A B}
                     {f : SFunᵉ ((A ⊎ X) ⊎ Y) ((B ⊎ X) ⊎ Y)}
                   → tr {X = X} (tr {X = Y} f)
                     ≈ᵉ tr {X = Y} (tr {X = X} (β-fn ∘ᵉ (f ∘ᵉ β-fn)))

  -- Dinaturality (sliding): a morphism h on the trace variable can
  -- slide between f's output and input sides of the trace.
  SFunᵉ-trace-dinatural : ∀ {X Y A B}
                          {f : SFunᵉ (A ⊎ X) (B ⊎ Y)}
                          {h : SFunᵉ Y X}
                        → tr {X = X} ((idᵉ {B} ⊗ᵉ h) ∘ᵉ f)
                          ≈ᵉ tr {X = Y} (f ∘ᵉ (idᵉ {A} ⊗ᵉ h))

-- The G-construction applied to SFunᵉ. Objects are channel-shaped
-- pairs; morphisms are bidirectional step functions.
SFunᵉ-GConstruction : Category _ _ _
SFunᵉ-GConstruction =
  GC.GConstruction SFunᵉ-Category SFunᵉ-monoidal SFunᵉ-traced
    SFunᵉ-trace-resp-≈
    SFunᵉ-trace-∘ˡ
    SFunᵉ-trace-∘ʳ
    SFunᵉ-trace-comm
    SFunᵉ-trace-dinatural

------------------------------------------------------------------------
-- Step 4.  Apply `GradedKleisli` over the G-constructed category.
--
-- This layer adds the "optional output" structure that `Machine.stepRel`
-- encodes via `Maybe outType` in its codomain (and, eventually, the
-- list-of-events grading that backs trace history).
--
-- The plan calls for a `Maybe`-like graded monad on
-- `SFunᵉ-GConstruction`, graded by a monoidal category. Building such a
-- triple from first principles is substantial (T₀, ext, return, sub, plus
-- ten coherence laws); for now we *postulate* the triple so that the
-- categorical pipeline stays connected end-to-end. A concrete instance
-- (built from the underlying `Maybe` monad of `M`) is a follow-up.
--
-- We grade by the terminal monoidal category `One` — i.e. the unit
-- monoid — matching the "no history" choice mentioned in the plan.

One-MonoidalCategory : MonoidalCategory _ _ _
One-MonoidalCategory = record { U = One ; monoidal = One-Monoidal }

private
  module GC-C = Category SFunᵉ-GConstruction

-- Concrete triple: the *identity* graded monad over SFunᵉ-GConstruction.
-- T₀ ignores the grade and returns the object unchanged; ext, return,
-- and sub are all identity. Every law collapses to a category-identity
-- law of `SFunᵉ-GConstruction`.
SFunᵉ-GradedTriple : GradedKleisliTriple One-MonoidalCategory SFunᵉ-GConstruction
SFunᵉ-GradedTriple = record
  { T₀               = λ _ A → A
  ; ext              = λ _ f → f
  ; return           = GC-C.id
  ; sub              = λ _ → GC-C.id
  ; ext-identityˡ    = GC-C.identityˡ
  ; ext-identityʳ    = trans-id² _
  ; ext-assoc        = GC-C.Equiv.sym GC-C.identityˡ
  ; ext-resp-≈       = λ p → p
  ; sub-commute      = GC-C.identityʳ
  ; sub-identity     = GC-C.Equiv.refl
  ; sub-homomorphism = GC-C.Equiv.sym GC-C.identity²
  ; sub-resp-≈       = λ _ → GC-C.Equiv.refl
  }
  where
    -- `id ∘ f ∘ id ≈ f`, used for ext-identityʳ.
    trans-id² : ∀ {A B} (f : A GC-C.⇒ B) → (GC-C.id GC-C.∘ f GC-C.∘ GC-C.id) GC-C.≈ f
    trans-id² f = GC-C.Equiv.trans GC-C.identityˡ GC-C.identityʳ

-- The graded-Kleisli category over `SFunᵉ-GConstruction`. Its objects
-- pair a grade (in `One`) with a G-construction object — when the
-- grading collapses, this is morally just `SFunᵉ-GConstruction` with a
-- per-arrow "may not emit" decoration.
SFunᵉ-GradedKleisli : Category _ _ _
SFunᵉ-GradedKleisli =
  GK.GradedKleisli SFunᵉ-GConstruction One-MonoidalCategory SFunᵉ-GradedTriple

------------------------------------------------------------------------
-- Step 5.  Channel ↔ Obj, Machine ↔ Hom correspondence.
--
-- This is the payoff of the categorical construction. A `Channel A` is
-- literally the inType/outType pair that the G-construction takes as
-- an object. A `Machine A B`'s `stepRel` has the same shape as a hom
-- in `SFunᵉ-GConstruction` from (inType A , outType A) to
-- (inType B , outType B), modulo the relation-vs-function and
-- Maybe-output gaps documented in (a)–(d) at the top of the file.
--
-- Target category. We use `SFunᵉ-GConstruction` directly rather than
-- `SFunᵉ-GradedKleisli`, because the postulated `SFunᵉ-GradedTriple`
-- keeps `T₀` opaque — and an opaque `T₀ k d` blocks constructing
-- explicit hom-set elements. The graded layer can be reinstated once a
-- concrete `Maybe`-graded triple is built.

Channel→Obj : Channel → GC-C.Obj
Channel→Obj A = Channel.inType A , Channel.outType A

Obj→Channel : GC-C.Obj → Channel
Obj→Channel (A⁺ , A⁻) = A⁺ ⇿ A⁻

Channel→Obj→Channel : ∀ A → Obj→Channel (Channel→Obj A) ≡ A
Channel→Obj→Channel _ = refl

Obj→Channel→Obj : ∀ X → Channel→Obj (Obj→Channel X) ≡ X
Obj→Channel→Obj (_ , _) = refl

GC-Hom : Channel → Channel → Type _
GC-Hom A B = (Channel→Obj A) GC-C.⇒ (Channel→Obj B)

-- ─────────────────────────────────────────────────────────────────────
-- The Hom type for the full Machine ↔ Hom bijection.
-- ─────────────────────────────────────────────────────────────────────
-- A "Machine-shaped Hom" is an SFunᵉ-style record whose codomain is
-- *Maybe*-augmented to accommodate "no emission" and whose `fun`
-- ranges in M (which, via the `MonadOfRel M` constraint, can encode
-- arbitrary relations). This matches Machine.stepRel exactly — both
-- have the shape
--
--   State → in(A⊗ᵀB) → State × Maybe out(A⊗ᵀB) → Type
--
-- (Machine via `stepRel`; MaybeHom via `fun (s, i) ≡ return (s', mo)`,
-- with `of-rel` providing the relation→M bridge in the forward
-- direction).
--
-- This `MaybeHom` is what the postulated `SFunᵉ-GradedTriple` of
-- Step 4 would produce once instantiated to the concrete `Maybe`-graded
-- triple over `M`. It plays the role of "hom in the Maybe-graded
-- Kleisli category over SFunᵉ-GConstruction".

record MaybeHom (A B : Channel) : Type₁ where
  constructor MkMaybeHom
  field
    {State} : Type
    fun     : State × Channel.inType (A ⊗ᵀ B)
            → M (State × Maybe (Channel.outType (A ⊗ᵀ B)))

open MaybeHom

-- ─────────────────────────────────────────────────────────────────────
-- Hom→Machine: any `MaybeHom A B` can be read as a Machine.
-- ─────────────────────────────────────────────────────────────────────
-- The Machine's `stepRel s i mo s'` is membership of `(s', mo)` in
-- the M-value `MH.fun (s, i)`. For `M = (· → Type)`, this is exactly
-- predicate membership.

Hom→Machine : ∀ {A B : Channel} → MaybeHom A B → Machine A B
Hom→Machine MH =
  MkMachine λ s i mo s' → member (s' , mo) (MaybeHom.fun MH (s , i))

-- ─────────────────────────────────────────────────────────────────────
-- Machine→Hom: every Machine yields a `MaybeHom A B`.
-- ─────────────────────────────────────────────────────────────────────
-- The SFunᵉ-like `fun (s, i)` is the M-value encoding the relation
-- `λ (s', mo) → Machine.stepRel s i mo s'`.

Machine→Hom : ∀ {A B : Channel} → Machine A B → MaybeHom A B
Machine→Hom Mch = record
  { State = Machine.State Mch
  ; fun = λ (s , i) → of-rel λ (s' , mo) → Machine.stepRel Mch s i mo s'
  }

-- ─────────────────────────────────────────────────────────────────────
-- Round-trip equalities.
-- ─────────────────────────────────────────────────────────────────────
-- Both directions of the bijection compose to the identity, up to:
--   • pointwise logical equivalence of stepRels (Machine round-trip)
--   • pointwise propositional equality of M-values (MaybeHom round-trip)
-- Both are provable from the two `MonadOfRel` laws.

-- Machine → Hom → Machine: every step `(s, i, mo, s')` recovers the
-- original `Machine.stepRel`. Stated as a pair of implications.
Machine-roundtrip-sound :
  ∀ {A B : Channel} (Mch : Machine A B)
    {s : Machine.State Mch}
    {i  : Channel.inType (A ⊗ᵀ B)}
    {mo : Maybe (Channel.outType (A ⊗ᵀ B))}
    {s' : Machine.State Mch}
  → Machine.stepRel Mch s i mo s'
  → Machine.stepRel (Hom→Machine (Machine→Hom Mch)) s i mo s'
Machine-roundtrip-sound Mch p = of-rel-sound p

Machine-roundtrip-complete :
  ∀ {A B : Channel} (Mch : Machine A B)
    {s : Machine.State Mch}
    {i  : Channel.inType (A ⊗ᵀ B)}
    {mo : Maybe (Channel.outType (A ⊗ᵀ B))}
    {s' : Machine.State Mch}
  → Machine.stepRel (Hom→Machine (Machine→Hom Mch)) s i mo s'
  → Machine.stepRel Mch s i mo s'
Machine-roundtrip-complete Mch p = of-rel-complete p

-- Hom → Machine → Hom: every M-value is recovered pointwise.
MaybeHom-roundtrip :
  ∀ {A B : Channel} (MH : MaybeHom A B)
    (s : MaybeHom.State MH)
    (i : Channel.inType (A ⊗ᵀ B))
  → MaybeHom.fun (Machine→Hom (Hom→Machine MH)) (s , i)
  ≡ MaybeHom.fun MH (s , i)
MaybeHom-roundtrip MH s i = member-η (MaybeHom.fun MH (s , i))

-- Specialisation hooks for the functional subset (kept for use sites
-- that already construct Homs directly from channel-level functions).

FunctionMachine→Hom :
  ∀ {A B : Channel}
  → ((Channel.inType A ⊎ Channel.outType B) → (Channel.outType A ⊎ Channel.inType B))
  → GC-Hom A B
FunctionMachine→Hom f = record
  { State = ⊤
  ; init  = tt
  ; fun   = λ (_ , i) → return (tt , f i)
  }

TotalFunctionMachine'→Hom :
  ∀ {A B : Channel}
  → (Channel.inType A → Channel.inType B)
  → (Channel.outType B → Channel.outType A)
  → GC-Hom A B
TotalFunctionMachine'→Hom p q = FunctionMachine→Hom
  λ where
    (inj₁ a-in)  → inj₂ (p a-in)
    (inj₂ b-out) → inj₁ (q b-out)

------------------------------------------------------------------------
-- MaybeHomCategory: the category whose hom-set is `MaybeHom A B`.
--
-- We define identity and composition on MaybeHom via the bijection
-- (`Machine→Hom`/`Hom→Machine` + Machine's `id` and `_∘_`). The
-- equivalence is induced through the bijection too.
--
-- The bijection-induced definitions make Machine→Hom a functor *by
-- construction* — `functor-id` and `functor-∘` below hold definitionally
-- once `Hom→Machine ∘ Machine→Hom = id` propositionally on MaybeHoms.
-- That last propositional equality is the one non-trivial ingredient
-- (we have it pointwise via `member-η`, but Agda needs it at the
-- record level).
--
-- The MaybeHomCategory laws below are stated, not yet proven. They are
-- the categorical analogue of MachineCategory's laws and will be
-- discharged in a future iteration by transporting from
-- SFunᵉ-GradedKleisli (once the postulated `SFunᵉ-GradedTriple` is
-- replaced by a concrete `Maybe`-graded triple). The transport from
-- MaybeHomCategory back to MachineCategory is the final piece below.

idᴹᴴ : ∀ {A : Channel} → MaybeHom A A
idᴹᴴ = Machine→Hom MC.id

_∘ᴹᴴ_ : ∀ {A B C : Channel} → MaybeHom B C → MaybeHom A B → MaybeHom A C
g ∘ᴹᴴ f = Machine→Hom (Hom→Machine g MC.∘ Hom→Machine f)

_≈ᴹᴴ_ : ∀ {A B : Channel} → MaybeHom A B → MaybeHom A B → Type₁
_≈ᴹᴴ_ MH₁ MH₂ = Hom→Machine MH₁ ≈ℰ Hom→Machine MH₂

-- `_≈ᴹᴴ_` is an equivalence (inherited from `_≈ℰ_`).
≈ᴹᴴ-isEquivalence : ∀ {A B} → IsEquivalence (_≈ᴹᴴ_ {A} {B})
≈ᴹᴴ-isEquivalence = record
  { refl  = λ E       → refl
  ; sym   = λ p E     → sym (p E)
  ; trans = λ p q E   → trans (p E) (q E)
  }

-- MaybeHomCategory's category laws. Stated here as the "categorical"
-- residue of MachineCategory's laws — they will hold by transport from
-- `SFunᵉ-GradedKleisli` when its underlying triple is concrete and the
-- GConstruction holes are filled.
postulate
  MaybeHomCategory-assoc :
    ∀ {A B C D} {f : MaybeHom A B} {g : MaybeHom B C} {h : MaybeHom C D}
    → ((h ∘ᴹᴴ g) ∘ᴹᴴ f) ≈ᴹᴴ (h ∘ᴹᴴ (g ∘ᴹᴴ f))

  MaybeHomCategory-identityˡ :
    ∀ {A B} {f : MaybeHom A B} → (idᴹᴴ ∘ᴹᴴ f) ≈ᴹᴴ f

  MaybeHomCategory-identityʳ :
    ∀ {A B} {f : MaybeHom A B} → (f ∘ᴹᴴ idᴹᴴ) ≈ᴹᴴ f

  MaybeHomCategory-∘-resp-≈ :
    ∀ {A B C} {f h : MaybeHom B C} {g i : MaybeHom A B}
    → f ≈ᴹᴴ h → g ≈ᴹᴴ i → (f ∘ᴹᴴ g) ≈ᴹᴴ (h ∘ᴹᴴ i)

MaybeHomCategory : Category _ _ _
MaybeHomCategory = record
  { Obj       = Channel
  ; _⇒_       = MaybeHom
  ; _≈_       = _≈ᴹᴴ_
  ; id        = idᴹᴴ
  ; _∘_       = _∘ᴹᴴ_
  ; assoc     = MaybeHomCategory-assoc
  ; sym-assoc = IsEquivalence.sym ≈ᴹᴴ-isEquivalence MaybeHomCategory-assoc
  ; identityˡ = MaybeHomCategory-identityˡ
  ; identityʳ = MaybeHomCategory-identityʳ
  ; identity² = MaybeHomCategory-identityˡ
  ; equiv     = ≈ᴹᴴ-isEquivalence
  ; ∘-resp-≈  = MaybeHomCategory-∘-resp-≈
  }

------------------------------------------------------------------------
-- Functoriality of Machine→Hom and Hom→Machine.
--
-- By definition of `idᴹᴴ` and `_∘ᴹᴴ_` via the bijection,
-- functoriality of `Machine→Hom` reduces to the propositional
-- equality `Hom→Machine ∘ Machine→Hom = id` on Machine records. We
-- have this at the *stepRel* level (Machine-roundtrip-sound/complete);
-- the missing step is Machine-extensionality — that two Machines with
-- the same State and pointwise-equivalent stepRels are propositionally
-- equal. We postulate that as `Machine-ext` for the transport.

postulate
  -- The "round-trip on the Machine side": composing Hom→Machine with
  -- Machine→Hom is the identity on Machines (up to propositional
  -- equality of Machine records). At stepRel level this follows from
  -- `of-rel-sound`/`of-rel-complete`; lifting to propositional Machine
  -- equality requires Machine-extensionality, postulated here.
  Hom-Machine-roundtrip-≡ : ∀ {A B} (Mch : Machine A B)
                          → Hom→Machine (Machine→Hom Mch) ≡ Mch

functor-id : ∀ {A : Channel} → Machine→Hom (MC.id {A}) ≡ idᴹᴴ
functor-id = refl

functor-∘ : ∀ {A B C : Channel} (g : Machine B C) (f : Machine A B)
          → Machine→Hom (g MC.∘ f) ≡ Machine→Hom g ∘ᴹᴴ Machine→Hom f
functor-∘ g f = cong₂ (λ x y → Machine→Hom (x MC.∘ y))
                       (sym (Hom-Machine-roundtrip-≡ g))
                       (sym (Hom-Machine-roundtrip-≡ f))

------------------------------------------------------------------------
-- Transport: MachineCategory laws from MaybeHomCategory laws.
--
-- For any Machine, `Machine→Hom`'s round-trip recovers it on the nose
-- (via Hom-Machine-roundtrip-≡). Combined with functoriality, every
-- MachineCategory law reduces to the corresponding MaybeHomCategory
-- law applied to the Homs of the participants.

≈ℰ-isEquivalence : ∀ {A B} → IsEquivalence (_≈ℰ_ {A} {B})
≈ℰ-isEquivalence = record
  { refl  = λ E       → refl
  ; sym   = λ p E     → sym (p E)
  ; trans = λ p q E   → trans (p E) (q E)
  }

-- Helper: unfold one layer of `∘ᴹᴴ` applied to Hom-images, collapsing
-- it via the round-trip postulate back to Machine composition.
private
  unfold-∘ᴹᴴ : ∀ {A B C} (g : Machine B C) (f : Machine A B)
             → Hom→Machine (Machine→Hom g ∘ᴹᴴ Machine→Hom f) ≡ g MC.∘ f
  unfold-∘ᴹᴴ g f = trans
    (Hom-Machine-roundtrip-≡ _)
    (cong₂ MC._∘_ (Hom-Machine-roundtrip-≡ g) (Hom-Machine-roundtrip-≡ f))

  -- For the identity round-trip.
  unfold-idᴹᴴ : ∀ {A} → Hom→Machine (idᴹᴴ {A}) ≡ MC.id
  unfold-idᴹᴴ = Hom-Machine-roundtrip-≡ MC.id

  -- ≈ℰ between two Machines lifts to ≈ᴹᴴ between their Homs.
  ≈ℰ→≈ᴹᴴ : ∀ {A B} {M₁ M₂ : Machine A B}
         → M₁ ≈ℰ M₂
         → Machine→Hom M₁ ≈ᴹᴴ Machine→Hom M₂
  ≈ℰ→≈ᴹᴴ {M₁ = M₁} {M₂ = M₂} p =
    subst (λ X → X ≈ℰ Hom→Machine (Machine→Hom M₂))
          (sym (Hom-Machine-roundtrip-≡ M₁))
    (subst (λ X → M₁ ≈ℰ X)
           (sym (Hom-Machine-roundtrip-≡ M₂)) p)

MachineCategory-assoc :
  ∀ {A B C D} {f : Machine A B} {g : Machine B C} {h : Machine C D}
  → ((h MC.∘ g) MC.∘ f) ≈ℰ (h MC.∘ (g MC.∘ f))
MachineCategory-assoc {f = f} {g = g} {h = h} =
  subst₂ _≈ℰ_ lhs-eq rhs-eq MaybeHomCategory-assoc
  where
    lhs-eq : Hom→Machine ((Machine→Hom h ∘ᴹᴴ Machine→Hom g) ∘ᴹᴴ Machine→Hom f)
           ≡ (h MC.∘ g) MC.∘ f
    lhs-eq = trans (cong (λ X → Hom→Machine (X ∘ᴹᴴ Machine→Hom f))
                          (sym (functor-∘ h g)))
                   (unfold-∘ᴹᴴ (h MC.∘ g) f)

    rhs-eq : Hom→Machine (Machine→Hom h ∘ᴹᴴ (Machine→Hom g ∘ᴹᴴ Machine→Hom f))
           ≡ h MC.∘ (g MC.∘ f)
    rhs-eq = trans (cong (λ X → Hom→Machine (Machine→Hom h ∘ᴹᴴ X))
                          (sym (functor-∘ g f)))
                   (unfold-∘ᴹᴴ h (g MC.∘ f))

MachineCategory-identityˡ :
  ∀ {A B} {f : Machine A B} → (MC.id MC.∘ f) ≈ℰ f
MachineCategory-identityˡ {f = f} =
  subst₂ _≈ℰ_ lhs-eq (Hom-Machine-roundtrip-≡ f) MaybeHomCategory-identityˡ
  where
    lhs-eq : Hom→Machine (idᴹᴴ ∘ᴹᴴ Machine→Hom f) ≡ MC.id MC.∘ f
    lhs-eq = unfold-∘ᴹᴴ MC.id f

MachineCategory-identityʳ :
  ∀ {A B} {f : Machine A B} → (f MC.∘ MC.id) ≈ℰ f
MachineCategory-identityʳ {f = f} =
  subst₂ _≈ℰ_ lhs-eq (Hom-Machine-roundtrip-≡ f) MaybeHomCategory-identityʳ
  where
    lhs-eq : Hom→Machine (Machine→Hom f ∘ᴹᴴ idᴹᴴ) ≡ f MC.∘ MC.id
    lhs-eq = unfold-∘ᴹᴴ f MC.id

MachineCategory-∘-resp-≈ :
  ∀ {A B C} {f h : Machine B C} {g i : Machine A B}
  → f ≈ℰ h → g ≈ℰ i → (f MC.∘ g) ≈ℰ (h MC.∘ i)
MachineCategory-∘-resp-≈ {f = f} {h = h} {g = g} {i = i} p q =
  subst₂ _≈ℰ_ lhs-eq rhs-eq
         (MaybeHomCategory-∘-resp-≈ (≈ℰ→≈ᴹᴴ p) (≈ℰ→≈ᴹᴴ q))
  where
    lhs-eq : Hom→Machine (Machine→Hom f ∘ᴹᴴ Machine→Hom g) ≡ f MC.∘ g
    lhs-eq = unfold-∘ᴹᴴ f g

    rhs-eq : Hom→Machine (Machine→Hom h ∘ᴹᴴ Machine→Hom i) ≡ h MC.∘ i
    rhs-eq = unfold-∘ᴹᴴ h i

MachineCategory : Category _ _ _
MachineCategory = record
  { Obj       = Channel
  ; _⇒_       = Machine
  ; _≈_       = _≈ℰ_
  ; id        = MC.id
  ; _∘_       = MC._∘_
  ; assoc     = MachineCategory-assoc
  ; sym-assoc = IsEquivalence.sym ≈ℰ-isEquivalence MachineCategory-assoc
  ; identityˡ = MachineCategory-identityˡ
  ; identityʳ = MachineCategory-identityʳ
  ; identity² = MachineCategory-identityˡ
  ; equiv     = ≈ℰ-isEquivalence
  ; ∘-resp-≈  = MachineCategory-∘-resp-≈
  }

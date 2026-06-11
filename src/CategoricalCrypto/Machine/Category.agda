------------------------------------------------------------------------
-- Plan (new strategy):
--   Machine ≅ Hom in (G-construction ∘ GradedKleisli ∘ SFunM)-built category
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

open import CategoricalCrypto.Channel.Core
  using (Channel; _⇿_; _ᵀ; _⊗₀_; destruct-⊗; construct-⊗; In; Out)
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
-- at setoid level. We postulate them here.

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

-- The G-construction applied to SFunᵉ. Objects are channel-shaped
-- pairs; morphisms are bidirectional step functions.
SFunᵉ-GConstruction : Category _ _ _
SFunᵉ-GConstruction =
  GC.GConstruction SFunᵉ-Category SFunᵉ-monoidal SFunᵉ-traced
    SFunᵉ-trace-resp-≈
    -- The implicits are passed explicitly: leaving them to unification
    -- makes the conversion checker unfold `tr`/`≈ᵉ` against an
    -- eta-expanded meta, which gets stuck on higher-order constraints.
    (λ {X} {A} {B} {B'} {g} {f} → SFunᵉ-trace-∘ˡ {X} {A} {B} {B'} {g} {f})
    SFunᵉ-trace-∘ʳ
    SFunᵉ-trace-comm

------------------------------------------------------------------------
-- Step 4.  Apply `GradedKleisli` over the G-constructed category.
--
-- This layer adds the "optional output" structure that `Machine.stepRel`
-- encodes via `Maybe outType` in its codomain (and, eventually, the
-- list-of-events grading that backs trace history).
--
-- The triple is `Maybe`-graded: `T₀ ⋆ (A⁺, A⁻) = (A⁺ ⊎ ⊤, A⁻)`. A
-- morphism `A ⇒ T₀ ⋆ B` in G(SFunᵉ) unfolds to
-- `SFunᵉ(A⁺ ⊎ B⁻, A⁻ ⊎ (B⁺ ⊎ ⊤))`, which under the canonical iso
-- `Maybe X ≅ X ⊎ ⊤` is the `MaybeHom` hom-set shape. `return` and `ext`
-- are concrete (Tier 1); the five triple laws involving `ext` (and
-- `sub-commute`) are postulated for now — discharging them is
-- substantial setoid-level work (Tier 2/3) — while the three `sub`-only
-- laws are proven directly.
--
-- We grade by the terminal monoidal category `One` — i.e. the unit
-- monoid — so all subsumption maps `sub` are identities.

One-MonoidalCategory : MonoidalCategory zeroˡ zeroˡ zeroˡ
One-MonoidalCategory = record { U = One ; monoidal = One-Monoidal }

private
  module GC-C = Category SFunᵉ-GConstruction

-- ─────────────────────────────────────────────────────────────────────
-- Maybe-graded triple: T₀'s action on objects.
-- ─────────────────────────────────────────────────────────────────────
-- T₀(⋆, (A⁺, A⁻)) = (A⁺ ⊎ ⊤, A⁻) — augments the "input" component of a
-- G-object with a ⊤ alternative. A morphism A ⇒ T₀(⋆, B) in
-- G(SFunᵉ) unfolds to SFunᵉ(A⁺ ⊎ B⁻, A⁻ ⊎ (B⁺ ⊎ ⊤)), which is the
-- shape of `MaybeHom A B` (up to the canonical iso
-- `Maybe X ≅ X ⊎ ⊤` applied at A⁻ ⊎ B⁺).
-- The (singleton) object type of the grading category `One`.
OneObj : Type
OneObj = Category.Obj (One {zeroˡ} {zeroˡ} {zeroˡ})

MaybeT₀ : OneObj → GC-C.Obj → GC-C.Obj
MaybeT₀ _ (A⁺ , A⁻) = (A⁺ ⊎ ⊤) , A⁻

-- The unit (`return`) at A : G-Hom A (MaybeT₀ ⋆ A).
-- Unfolded type: SFunᵉ(A⁺ ⊎ A⁻, A⁻ ⊎ (A⁺ ⊎ ⊤)).
-- Built as the G-identity (the braiding σᵉ) post-composed with the
-- inj₁ injection on the A⁺-summand of the output side.
MaybeT-return : ∀ {A : GC-C.Obj} → A GC-C.⇒ MaybeT₀ _ A
MaybeT-return {A⁺ , A⁻} = (idᵉ {A⁻} ⊗ᵉ pure-reshape inj₁) ∘ᵉ σᵉ {A⁺} {A⁻}

-- Kleisli extension. Given f : A ⇒ MaybeT₀ ⋆ B, build
-- ext(f) : MaybeT₀ ⋆ A ⇒ MaybeT₀ ⋆ B.
-- Unfolded type: SFunᵉ((A⁺ ⊎ ⊤) ⊎ B⁻, A⁻ ⊎ (B⁺ ⊎ ⊤)).
-- Semantics: when the input is the ⊤ added by MaybeT₀(A), emit ⊤ on
-- the output's B-side (propagate the "nothing"); otherwise dispatch to f.
MaybeT-ext : ∀ {A B : GC-C.Obj}
           → A GC-C.⇒ MaybeT₀ _ B
           → MaybeT₀ _ A GC-C.⇒ MaybeT₀ _ B
MaybeT-ext f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ where
      (s , inj₁ (inj₁ a)) → SFunᵉ.fun f (s , inj₁ a)
      (s , inj₁ (inj₂ _)) → return (s , inj₂ (inj₂ tt))
      (s , inj₂ b)        → SFunᵉ.fun f (s , inj₂ b)
  }

-- The Maybe-graded triple over SFunᵉ-GConstruction. T₀ adds a ⊤
-- alternative to the "input" component of each G-object (so morphisms
-- into T₀ B carry an optional "no emission" on their output coproduct);
-- return and ext are the concrete unit and Kleisli-extension realising
-- this. sub is identity (the grading category V = One has only one
-- morphism). The five graded-Kleisli laws involving `ext` are
-- substantial (equations in SFunᵉ-GConstruction's hom-equivalence over
-- list-trace evaluation) and are postulated here; the three sub-only
-- laws are proved from `SFunᵉ-GConstruction`'s identity laws directly.
--
-- Proof sketches for each ext-related postulate (Tier 3 roadmap):
--
-- • MaybeT-ext-identityˡ : ext(return) ≈ G-id at T₀ A.
--   After GC-C.identityʳ on the outer ∘, the goal is
--     MaybeT-ext MaybeT-return ≈ GC-C.id {MaybeT₀ u A}.
--   GC-C.id at T₀ A unfolds to σᵉ : SFunᵉ((A⁺⊎⊤)⊎A⁻, A⁻⊎(A⁺⊎⊤)).
--   MaybeT-ext (MaybeT-return) is a pure SFunᵉ — its `fun` is monadic
--   `return ∘ <case-routing>` at every input. The case-routing
--   computes the same σ-fn that σᵉ uses. The proof reduces to:
--     (i)  define `pure-reshape-of-record` lemma — if an SFunᵉ's `fun`
--          is `return ∘ g` pointwise for some `g : A → B`, then the
--          SFunᵉ is ≈ᵉ-equal to `pure-reshape g`;
--     (ii) apply this to both MaybeT-ext(MaybeT-return) (giving a pure
--          reshape with the case-by-case σ function) and GC-C.id;
--     (iii) conclude via `pure-reshape-cong` since both g's agree
--           pointwise.
--   Estimated: 30-50 lines, including (i) which is reusable.
--
-- • MaybeT-ext-identityʳ : ext(f) ∘ᴋ return ≈ f.
--   GC-C.∘ uses trace internally (G-construction composition), so this
--   isn't a direct SFunᵉ ∘ identity. After unfolding GC-C.∘ as
--   `trace (assoc ∘ (return ⊗ ext f) ∘ assoc⁻¹)`, the trace loop
--   degenerates because `return` is pure on the trace variable. The
--   proof uses `SFunᵉ-trace-∘ʳ` (the existing trace naturality
--   postulate) plus careful unfolding of `MaybeT-return`'s structure.
--   Estimated: 80-120 lines.
--
-- • MaybeT-ext-assoc : ext(ext(f) ∘ g) ≈ ext(f) ∘ ext(g).
--   The hardest law. Both sides are SFunᵉ-GConstruction morphisms
--   whose `fun` does case-routing on input. Each case dispatches to
--   either f, g, or both via G-construction composition (trace).
--   The proof requires:
--     (i)   an input-case lemma reducing ext's behavior to f/g calls;
--     (ii)  trace fusion across the nested composition (similar in
--           spirit to vanishing₂ in Traced.agda);
--     (iii) ext-resp-≈ to push GC-C.identityˡ inside ext on the RHS.
--   Estimated: 200-400 lines. Likely needs additional helper lemmas
--   about MaybeT-ext's interaction with G-composition.
--
-- • MaybeT-ext-resp-≈ : f ≈ g → ext(f) ≈ ext(g).
--   Congruence of ext under ≈ᵉ. Inductive on input lists. Key step:
--   a "trace factoring" lemma:
--     eval (MaybeT-ext f) xs ≡ <interleave eval f (filter₁ xs)
--                                  with constant ⊤-emissions on
--                                  filter₂ xs positions>.
--   This factor-lemma is the substantive content; once stated, the
--   conclusion follows by applying f ≈ g to filter₁ xs.
--   Estimated: 60-100 lines (factor-lemma + induction).
--
-- • MaybeT-sub-commute : ext(GC-id ∘ f) ∘ GC-id ≈ GC-id ∘ ext(f).
--   Trivially provable once ext-resp-≈ is in place:
--     LHS = ext(GC-id ∘ f) ∘ GC-id
--         ≈⟨ GC-C.identityʳ ⟩  ext(GC-id ∘ f)
--         ≈⟨ MaybeT-ext-resp-≈ GC-C.identityˡ ⟩  ext(f)
--         ≈˘⟨ GC-C.identityˡ ⟩  GC-id ∘ ext(f) = RHS.
--   Estimated: 5 lines after ext-resp-≈.
private
  postulate
    MaybeT-ext-identityˡ : ∀ {u A}
      → GC-C.id GC-C.∘ MaybeT-ext (MaybeT-return {A}) GC-C.≈ GC-C.id {MaybeT₀ u A}
    MaybeT-ext-identityʳ : ∀ {u A B} {f : A GC-C.⇒ MaybeT₀ u B}
      → GC-C.id GC-C.∘ MaybeT-ext f GC-C.∘ MaybeT-return GC-C.≈ f
    MaybeT-ext-assoc : ∀ {u : OneObj} {v w A B C}
      {f : B GC-C.⇒ MaybeT₀ w C} {g : A GC-C.⇒ MaybeT₀ v B}
      → MaybeT-ext (MaybeT-ext f GC-C.∘ g)
        GC-C.≈ GC-C.id GC-C.∘ (MaybeT-ext f GC-C.∘ MaybeT-ext g)
    MaybeT-ext-resp-≈ : ∀ {u : OneObj} {v A B} {f g : A GC-C.⇒ MaybeT₀ v B}
      → f GC-C.≈ g → MaybeT-ext {A} {B} f GC-C.≈ MaybeT-ext g
    MaybeT-sub-commute : ∀ {u₁ u₂ v₁ v₂ : OneObj} {A B}
      {α : Lift zeroˡ ⊤} {β : Lift zeroˡ ⊤} {f : A GC-C.⇒ MaybeT₀ u₂ B}
      → MaybeT-ext (GC-C.id GC-C.∘ f) GC-C.∘ GC-C.id
        GC-C.≈ GC-C.id GC-C.∘ MaybeT-ext {A} {B} f

SFunᵉ-GradedTriple : GradedKleisliTriple One-MonoidalCategory SFunᵉ-GConstruction
SFunᵉ-GradedTriple = record
  { T₀               = MaybeT₀
  ; ext              = λ _ → MaybeT-ext
  ; return           = MaybeT-return
  ; sub              = λ _ → GC-C.id
  ; ext-identityˡ    = MaybeT-ext-identityˡ
  ; ext-identityʳ    = MaybeT-ext-identityʳ
  ; ext-assoc        = MaybeT-ext-assoc
  ; ext-resp-≈       = MaybeT-ext-resp-≈
  ; sub-commute      = MaybeT-sub-commute
  ; sub-identity     = GC-C.Equiv.refl
  ; sub-homomorphism = GC-C.Equiv.sym GC-C.identity²
  ; sub-resp-≈       = λ _ → GC-C.Equiv.refl
  }

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
-- Maybe-output gaps bridged by `MaybeHom` below.
--
-- Target category. We use `SFunᵉ-GConstruction` directly rather than
-- `SFunᵉ-GradedKleisli`: with the grading collapsed to `One`, the
-- graded layer only wraps the same underlying data in an existential
-- grade plus subsumption bookkeeping, which gets in the way of
-- constructing explicit hom-set elements.

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
-- This `MaybeHom` is the hom-shape produced by the `Maybe`-graded
-- triple `SFunᵉ-GradedTriple` of Step 4 — a hom `A ⇒ T₀ ⋆ B` in
-- G(SFunᵉ), read through the canonical iso `Maybe X ≅ X ⊎ ⊤`. It plays
-- the role of "hom in the Maybe-graded Kleisli category over
-- SFunᵉ-GConstruction".

record MaybeHom (A B : Channel) : Type₁ where
  constructor MkMaybeHom
  field
    {State} : Type
    fun     : State × Channel.inType (A ⊗ᵀ B)
            → M (State × Maybe (Channel.outType (A ⊗ᵀ B)))

open MaybeHom

-- ─────────────────────────────────────────────────────────────────────
-- Principled Maybe-Kleisli hom: literally the hom-set of the
-- Maybe-graded Kleisli category. Unfolds to an `SFunᵉ` with state, init,
-- and a `fun : State × (inType A ⊎ outType B) → M(State × (outType A ⊎
-- (inType B ⊎ ⊤)))`. The unique difference from `MaybeHom` above is the
-- extra `init` field and the use of `_⊎ ⊤` (the G-Kleisli T₀ shape)
-- instead of `Maybe`. The two are isomorphic — see `MaybeHom→Kl` /
-- `Kl→MaybeHom` below.
MaybeHom-Kl : Channel → Channel → Type₁
MaybeHom-Kl A B = (Channel→Obj A) GC-C.⇒ MaybeT₀ _ (Channel→Obj B)

-- ─────────────────────────────────────────────────────────────────────
-- Iso between MaybeHom and MaybeHom-Kl.
-- ─────────────────────────────────────────────────────────────────────
-- The forward direction needs an explicit initial state since
-- `MaybeHom` is init-less; the backward direction discards init.
-- The Maybe-vs-(⊎⊤) shape mismatch is handled by `maybe→sum` /
-- `sum→maybe` below; the opaque `inType (A ⊗ᵀ B)` ↔ `inType A ⊎
-- outType B` bridge uses `destruct-⊗` / `construct-⊗`.

private
  -- Maybe X ↔ X ⊎ ⊤ at the value level.
  maybe→sum-⊤ : ∀ {X : Type} → Maybe X → X ⊎ ⊤
  maybe→sum-⊤ (just x) = inj₁ x
  maybe→sum-⊤ nothing  = inj₂ tt

  sum-⊤→maybe : ∀ {X : Type} → X ⊎ ⊤ → Maybe X
  sum-⊤→maybe (inj₁ x) = just x
  sum-⊤→maybe (inj₂ _) = nothing

  -- Outgoing-side reshape: `Maybe (outType A ⊎ inType B) →
  -- outType A ⊎ (inType B ⊎ ⊤)`. Bundles maybe→sum-⊤ with the
  -- ⊎-reassociation that takes (outType A ⊎ inType B) ⊎ ⊤ to the
  -- right-nested form used by MaybeT₀'s output.
  out-mh→kl : ∀ {A B : Channel}
    → Maybe (Channel.outType (A ⊗ᵀ B))
    → Channel.outType A ⊎ (Channel.inType B ⊎ ⊤)
  out-mh→kl nothing  = inj₂ (inj₂ tt)
  out-mh→kl (just z) with destruct-⊗ {m = Out} z
  ... | inj₁ a = inj₁ a
  ... | inj₂ b = inj₂ (inj₁ b)

  out-kl→mh : ∀ {A B : Channel}
    → Channel.outType A ⊎ (Channel.inType B ⊎ ⊤)
    → Maybe (Channel.outType (A ⊗ᵀ B))
  out-kl→mh (inj₁ a)         = just (construct-⊗ {m = Out} (inj₁ a))
  out-kl→mh (inj₂ (inj₁ b))  = just (construct-⊗ {m = Out} (inj₂ b))
  out-kl→mh (inj₂ (inj₂ _))  = nothing

-- Build a `MaybeHom-Kl` from a `MaybeHom` together with an initial state.
MaybeHom→Kl : ∀ {A B : Channel} (MH : MaybeHom A B)
            → MaybeHom.State MH → MaybeHom-Kl A B
MaybeHom→Kl {A} {B} MH init₀ = record
  { State = MaybeHom.State MH
  ; init  = init₀
  ; fun   = λ (s , i) →
      MaybeHom.fun MH (s , construct-⊗ {m = In} i) >>= λ (s' , mo) →
        return (s' , out-mh→kl {A} {B} mo)
  }

-- Forget the init field and reshape the output back to `Maybe`.
Kl→MaybeHom : ∀ {A B : Channel} → MaybeHom-Kl A B → MaybeHom A B
Kl→MaybeHom {A} {B} Kl = record
  { State = SFunᵉ.State Kl
  ; fun   = λ (s , i) →
      SFunᵉ.fun Kl (s , destruct-⊗ {m = In} i) >>= λ (s' , z) →
        return (s' , out-kl→mh {A} {B} z)
  }

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

-- ─────────────────────────────────────────────────────────────────────
-- Machine ↔ MaybeHom-Kl: the principled route via the Maybe-graded
-- Kleisli hom (composes Machine ↔ MaybeHom with the MaybeHom ↔ Kl iso).
-- ─────────────────────────────────────────────────────────────────────

Machine→Kl : ∀ {A B : Channel} (Mch : Machine A B)
           → Machine.State Mch → MaybeHom-Kl A B
Machine→Kl Mch init₀ = MaybeHom→Kl (Machine→Hom Mch) init₀

Kl→Machine : ∀ {A B : Channel} → MaybeHom-Kl A B → Machine A B
Kl→Machine Kl = Hom→Machine (Kl→MaybeHom Kl)

-- ─────────────────────────────────────────────────────────────────────
-- Principled category operations on `MaybeHom-Kl`, built directly
-- from the Maybe-graded triple's `MaybeT-return` (the unit) and
-- `MaybeT-ext` (the Kleisli extension) plus G-construction composition.
-- These are the canonical category structure on `MaybeHom-Kl` — the
-- forgetful image of the graded Kleisli category's id and ∘ under the
-- collapse V=One. Modulo the 5 postulated `ext-*` laws on the triple,
-- the four MaybeHomCategory laws (assoc, identityˡ/ʳ, ∘-resp-≈) are
-- derivable from these by transport through `MaybeHom↔Kl`.
idᴹᴴ-Kl : ∀ {A : Channel} → MaybeHom-Kl A A
idᴹᴴ-Kl {A} = MaybeT-return {Channel→Obj A}

_∘ᴹᴴ-Kl_ : ∀ {A B C : Channel}
         → MaybeHom-Kl B C → MaybeHom-Kl A B → MaybeHom-Kl A C
g ∘ᴹᴴ-Kl f = MaybeT-ext g GC-C.∘ f

_≈ᴹᴴ-Kl_ : ∀ {A B : Channel} → MaybeHom-Kl A B → MaybeHom-Kl A B → Type _
f ≈ᴹᴴ-Kl g = f GC-C.≈ g

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
-- SFunᵉ-GradedKleisli (once the five postulated `MaybeT-ext-*` laws of
-- the triple are discharged). The transport from MaybeHomCategory back
-- to MachineCategory is the final piece below.

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
-- `SFunᵉ-GradedKleisli` once the triple's postulated `ext` laws are
-- discharged (the category laws of `Categories.GradedKleisli` itself
-- are fully proven).
--
-- Two routes to discharge each of these (Tier 3 roadmap):
--
-- Route A — via Machine: each MaybeHomCategory law is the bijection
-- image of the corresponding MachineCategory law. Specifically:
--   • idᴹᴴ ∘ᴹᴴ f = Machine→Hom (Hom→Machine idᴹᴴ MC.∘ Hom→Machine f)
--                = Machine→Hom (MC.id MC.∘ Hom→Machine f)   [via Hom-Machine-roundtrip-≡]
--                = Machine→Hom (Hom→Machine f)               [via MachineCategory.identityˡ]
--                ≈ᴹᴴ f                                        [via roundtrip + ≈ℰ-refl]
-- Same pattern for the other three.
-- Required (currently unproved): MachineCategory's identityˡ/ʳ,
-- assoc, ∘-resp-≈. These are Machine-level statements not yet in
-- Machine.Core.
--
-- Route B — via the Maybe-graded triple: each MaybeHomCategory law
-- is the iso image (MaybeHom↔Kl) of the corresponding MaybeHom-Kl
-- law. Specifically:
--   MaybeHom-Kl forms a category via the GradedKleisli construction;
--   the iso Kl→MaybeHom takes that category's laws to MaybeHomCategory's
--   laws — modulo (a) the 5 postulated `MaybeT-ext-*` laws above, and
--   (b) showing the iso is functorial (preserves id and ∘ up to ≈ᴹᴴ).
-- Both routes are substantial but the framework is in place for
-- either to be pursued.
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

{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Overview:
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
open import Data.List.Properties using (map-cong)
open import Relation.Binary using (IsEquivalence)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal.Instance.One using (One-Monoidal)
open import Categories.Monad.Graded using (GradedKleisliTriple)

open import CategoricalCrypto.Channel.Core
  using (Channel; _⇿_; _ᵀ; _⊗₀_; destruct-⊗; construct-⊗; In; Out)
open import CategoricalCrypto.Machine.Core as MC using (Machine; MkMachine; _⊗ᵀ_; machine-type; _≈ℰ_)
open import CategoricalCrypto.Machine.Iso

module CategoricalCrypto.Machine.Category {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  ⦃ M-Iter        : IterativeMonad M   ⦄
  ⦃ M-OfRel       : MonadOfRel M       ⦄
  where

open import CategoricalCrypto.SFunM
  ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄
open import CategoricalCrypto.SFunM.Monoidal
  ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄
open import CategoricalCrypto.SFunM.Traced
  ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄ ⦃ M-Iter ⦄

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
-- module parameters. Naturality (∘ˡ/∘ʳ) and the Fubini exchange (comm)
-- are proven in `CategoricalCrypto.SFunM.Traced` from the
-- `IterativeMonad` axioms. Congruence (resp-≈) is of a different
-- nature: it asserts that the trace respects *observational* (`eval`-
-- level) equality, which does not follow from the iteration axioms —
-- those only give congruence for pointwise-equal step functions. It is
-- a genuine semantic assumption about `M` (provable for, e.g., the
-- relational instance, but not abstractly), so it is an axiom of the
-- `IterativeMonad` class (`iter-trace-cong`), from which
-- `CategoricalCrypto.SFunM.Traced` derives the `SFunᵉ`-level statement
-- `trace-resp-≈-ᵉ` used here.

private
  -- β swaps the last two factors: (P ⊎ Q) ⊎ R → (P ⊎ R) ⊎ Q.
  -- Matches the (private) `β` inside `Categories.GConstruction`.
  β-fn : ∀ {P Q R} → SFunᵉ ((P ⊎ Q) ⊎ R) ((P ⊎ R) ⊎ Q)
  β-fn = α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ)

SFunᵉ-trace-resp-≈ : ∀ {X A B} {f g : SFunᵉ (A ⊎ X) (B ⊎ X)}
                   → f ≈ᵉ g → tr {X = X} f ≈ᵉ tr {X = X} g
SFunᵉ-trace-resp-≈ {X} {A} {B} {f} {g} = trace-resp-≈-ᵉ {X} {A} {B} {f} {g}

SFunᵉ-trace-∘ˡ : ∀ {X A B B'} {g : SFunᵉ B B'} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
               → (g ∘ᵉ tr {X = X} f) ≈ᵉ tr {X = X} ((g ⊗ᵉ idᵉ) ∘ᵉ f)
SFunᵉ-trace-∘ˡ {X} {A} {B} {B'} {g} {f} = trace-∘ˡ-ᵉ {X} {A} {B} {B'} {g} {f}

SFunᵉ-trace-∘ʳ : ∀ {X A A' B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)} {h : SFunᵉ A' A}
               → (tr {X = X} f ∘ᵉ h) ≈ᵉ tr {X = X} (f ∘ᵉ (h ⊗ᵉ idᵉ))
SFunᵉ-trace-∘ʳ {X} {A} {A'} {B} {f} {h} = trace-∘ʳ-ᵉ {X} {A} {A'} {B} {f} {h}

-- β swaps the inner two factors, so (β ∘ f ∘ β) has the X and Y
-- swapped in its codomain shape. The trace axes flip accordingly.
SFunᵉ-trace-comm : ∀ {X Y A B}
                   {f : SFunᵉ ((A ⊎ X) ⊎ Y) ((B ⊎ X) ⊎ Y)}
                 → tr {X = X} (tr {X = Y} f)
                   ≈ᵉ tr {X = Y} (tr {X = X} (β-fn ∘ᵉ (f ∘ᵉ β-fn)))
SFunᵉ-trace-comm {X} {Y} {A} {B} {f} = trace-comm-ᵉ {X} {Y} {A} {B} {f}

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
-- are concrete, and all eight triple laws are proven — the three
-- `sub`-only ones from `SFunᵉ-GConstruction`'s identity laws, the five
-- `ext` ones at the trace-evaluation level (see the infrastructure
-- preceding the triple).
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

------------------------------------------------------------------------
-- Infrastructure for discharging the graded-Kleisli `ext` laws.
--
-- All five laws are `≈ᵉ`-equations between trace composites. The key
-- observations:
--
--   • `GC-C.∘ F G` unfolds *definitionally* to
--     `tr (gc-α ∘ᵉ ((F ⊗ᵉ G) ∘ᵉ gc-γ))` where `gc-α`/`gc-γ` (spelled
--     out below) are the G-construction's coherence reshapes, and
--     `GC-C.id` unfolds to `σᵉ`.
--   • Those reshapes — and `MaybeT-return` — are *pure* (stateless,
--     effect-free); `IsPure` characterizes such morphisms pointwise,
--     so a G-composition's trace loop steps through exactly one
--     effectful call per bounce (`gc-body-fun₁/₂`).
--   • `trace-cong`/`trace-sim` lift pointwise `fun`-equality (resp. a
--     state-projection simulation) to `≈ᵉ`.
--   • `ext-factor` factors `eval (MaybeT-ext f)` through `eval f`,
--     giving the congruence law from observational equality alone.

private
  -- The coherence reshapes of `GConstruction`'s composition, spelled
  -- out as SFunᵉ composites (definitionally equal to the originals).
  gc-γ : ∀ {A⁺ C⁻ B⁻ B⁺ : Type}
       → SFunᵉ ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)) ((B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻))
  gc-γ = α⇒ᵉ ∘ᵉ ((σᵉ ⊗ᵉ idᵉ) ∘ᵉ (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ (σᵉ ⊗ᵉ idᵉ)) ∘ᵉ ((idᵉ ⊗ᵉ α⇐ᵉ) ∘ᵉ (α⇒ᵉ ∘ᵉ (idᵉ ⊗ᵉ σᵉ))))))

  gc-α : ∀ {B⁻ C⁺ A⁻ B⁺ : Type}
       → SFunᵉ ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺)) ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺))
  gc-α = α⇒ᵉ ∘ᵉ ((σᵉ ⊗ᵉ idᵉ) ∘ᵉ (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ (σᵉ ⊗ᵉ idᵉ)) ∘ᵉ ((idᵉ ⊗ᵉ α⇐ᵉ) ∘ᵉ α⇒ᵉ))))

  gc-∘-≡ : ∀ {A B C : GC-C.Obj} (F : B GC-C.⇒ C) (G : A GC-C.⇒ B)
         → (F GC-C.∘ G) ≡ tr (gc-α ∘ᵉ ((F ⊗ᵉ G) ∘ᵉ gc-γ))
  gc-∘-≡ F G = refl

  gc-id-≡ : ∀ {A : GC-C.Obj} → GC-C.id {A} ≡ σᵉ
  gc-id-≡ = refl

  -- ────────────────────────────────────────────────────────────────
  -- Pure (stateless, effect-free) morphisms, pointwise.
  IsPure : {A B : Type} → (A → B) → SFunᵉ A B → Type
  IsPure g F = ∀ s x → SFunᵉ.fun F (s , x) ≡ return (s , g x)

  ⊎map : {A B C D : Type} → (A → B) → (C → D) → A ⊎ C → B ⊎ D
  ⊎map p q (inj₁ a) = inj₁ (p a)
  ⊎map p q (inj₂ c) = inj₂ (q c)

  pure-prsh : {A B : Type} (g : A → B) → IsPure g (pure-reshape g)
  pure-prsh g s x = refl

  pure-idᵉ : {A : Type} → IsPure {A} id idᵉ
  pure-idᵉ s x = refl

  pure-∘ᵉ : {A B C : Type} {q : A → B} {p : B → C}
            {Q : SFunᵉ A B} {P : SFunᵉ B C}
          → IsPure p P → IsPure q Q → IsPure (p ∘ q) (P ∘ᵉ Q)
  pure-∘ᵉ {q = q} {p} {Q} {P} pP pQ (sP , sQ) x = begin
    (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) →
      SFunᵉ.fun P (sP , b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ pQ sQ x ⟩>>=⟨refl ⟩
    (return (sQ , q x) >>= λ (sQ' , b) →
      SFunᵉ.fun P (sP , b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ >>=-identityˡ ⟩
    (SFunᵉ.fun P (sP , q x) >>= λ (sP' , c) → return ((sP' , sQ) , c))
      ≡⟨ pP sP (q x) ⟩>>=⟨refl ⟩
    (return (sP , p (q x)) >>= λ (sP' , c) → return ((sP' , sQ) , c))
      ≡⟨ >>=-identityˡ ⟩
    return ((sP , sQ) , p (q x)) ∎
    where open ≡-Reasoning

  pure-⊗ᵉ : {A B C D : Type} {p : A → B} {q : C → D}
            {P : SFunᵉ A B} {Q : SFunᵉ C D}
          → IsPure p P → IsPure q Q → IsPure (⊎map p q) (P ⊗ᵉ Q)
  pure-⊗ᵉ {p = p} {q} {P} {Q} pP pQ (sP , sQ) (inj₁ a) = begin
    (SFunᵉ.fun P (sP , a) >>= λ (sP' , b) → return ((sP' , sQ) , inj₁ b))
      ≡⟨ pP sP a ⟩>>=⟨refl ⟩
    (return (sP , p a) >>= λ (sP' , b) → return ((sP' , sQ) , inj₁ b))
      ≡⟨ >>=-identityˡ ⟩
    return ((sP , sQ) , inj₁ (p a)) ∎
    where open ≡-Reasoning
  pure-⊗ᵉ {p = p} {q} {P} {Q} pP pQ (sP , sQ) (inj₂ c) = begin
    (SFunᵉ.fun Q (sQ , c) >>= λ (sQ' , d) → return ((sP , sQ') , inj₂ d))
      ≡⟨ pQ sQ c ⟩>>=⟨refl ⟩
    (return (sQ , q c) >>= λ (sQ' , d) → return ((sP , sQ') , inj₂ d))
      ≡⟨ >>=-identityˡ ⟩
    return ((sP , sQ) , inj₂ (q c)) ∎
    where open ≡-Reasoning

  pure-≗ : {A B : Type} {p q : A → B} {F : SFunᵉ A B}
         → IsPure p F → p ≗ q → IsPure q F
  pure-≗ pF eq s x = trans (pF s x) (cong (λ y → return (s , y)) (eq x))

  -- The value-level routing of `gc-α`/`gc-γ`: loop channels (B⁻/B⁺)
  -- bounce, exit channels (A⁻/C⁺) leave; externals (A⁺/C⁻) dispatch
  -- to the components.
  gc-α-fn : {B⁻ C⁺ A⁻ B⁺ : Type}
          → (B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺) → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  gc-α-fn (inj₁ (inj₁ b⁻)) = inj₂ (inj₁ b⁻)
  gc-α-fn (inj₁ (inj₂ c⁺)) = inj₁ (inj₂ c⁺)
  gc-α-fn (inj₂ (inj₁ a⁻)) = inj₁ (inj₁ a⁻)
  gc-α-fn (inj₂ (inj₂ b⁺)) = inj₂ (inj₂ b⁺)

  gc-γ-fn : {A⁺ C⁻ B⁻ B⁺ : Type}
          → (A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺) → (B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)
  gc-γ-fn (inj₁ (inj₁ a⁺)) = inj₂ (inj₁ a⁺)
  gc-γ-fn (inj₁ (inj₂ c⁻)) = inj₁ (inj₂ c⁻)
  gc-γ-fn (inj₂ (inj₁ b⁻)) = inj₂ (inj₂ b⁻)
  gc-γ-fn (inj₂ (inj₂ b⁺)) = inj₁ (inj₁ b⁺)

  gc-α-pure : ∀ {B⁻ C⁺ A⁻ B⁺ : Type} → IsPure (gc-α-fn {B⁻} {C⁺} {A⁻} {B⁺}) gc-α
  gc-α-pure =
    pure-≗ (pure-∘ᵉ (pure-prsh α-fn)
             (pure-∘ᵉ (pure-⊗ᵉ (pure-prsh σ-fn) pure-idᵉ)
               (pure-∘ᵉ (pure-prsh α-fn-inv)
                 (pure-∘ᵉ (pure-⊗ᵉ pure-idᵉ (pure-⊗ᵉ (pure-prsh σ-fn) pure-idᵉ))
                   (pure-∘ᵉ (pure-⊗ᵉ pure-idᵉ (pure-prsh α-fn-inv))
                     (pure-prsh α-fn))))))
      λ where
        (inj₁ (inj₁ b⁻)) → refl
        (inj₁ (inj₂ c⁺)) → refl
        (inj₂ (inj₁ a⁻)) → refl
        (inj₂ (inj₂ b⁺)) → refl

  gc-γ-pure : ∀ {A⁺ C⁻ B⁻ B⁺ : Type} → IsPure (gc-γ-fn {A⁺} {C⁻} {B⁻} {B⁺}) gc-γ
  gc-γ-pure =
    pure-≗ (pure-∘ᵉ (pure-prsh α-fn)
             (pure-∘ᵉ (pure-⊗ᵉ (pure-prsh σ-fn) pure-idᵉ)
               (pure-∘ᵉ (pure-prsh α-fn-inv)
                 (pure-∘ᵉ (pure-⊗ᵉ pure-idᵉ (pure-⊗ᵉ (pure-prsh σ-fn) pure-idᵉ))
                   (pure-∘ᵉ (pure-⊗ᵉ pure-idᵉ (pure-prsh α-fn-inv))
                     (pure-∘ᵉ (pure-prsh α-fn) (pure-⊗ᵉ pure-idᵉ (pure-prsh σ-fn))))))))
      λ where
        (inj₁ (inj₁ a⁺)) → refl
        (inj₁ (inj₂ c⁻)) → refl
        (inj₂ (inj₁ b⁻)) → refl
        (inj₂ (inj₂ b⁺)) → refl

  -- `MaybeT-return`'s value-level routing.
  ret-fn : {A⁺ A⁻ : Type} → A⁺ ⊎ A⁻ → A⁻ ⊎ (A⁺ ⊎ ⊤)
  ret-fn (inj₁ a) = inj₂ (inj₁ a)
  ret-fn (inj₂ a) = inj₁ a

  ret-pure : ∀ {A : GC-C.Obj} → IsPure ret-fn (MaybeT-return {A})
  ret-pure {A⁺ , A⁻} =
    pure-≗ (pure-∘ᵉ (pure-⊗ᵉ pure-idᵉ (pure-prsh inj₁)) (pure-prsh σ-fn))
      λ where
        (inj₁ a) → refl
        (inj₂ a) → refl

  -- `MaybeT-ext` preserves pure behaviour, with the ⊤-input shortcut.
  ext-fn : {A⁺ B⁻ A⁻ B⁺ : Type}
         → (A⁺ ⊎ B⁻ → A⁻ ⊎ (B⁺ ⊎ ⊤))
         → (A⁺ ⊎ ⊤) ⊎ B⁻ → A⁻ ⊎ (B⁺ ⊎ ⊤)
  ext-fn g (inj₁ (inj₁ a)) = g (inj₁ a)
  ext-fn g (inj₁ (inj₂ _)) = inj₂ (inj₂ tt)
  ext-fn g (inj₂ b)        = g (inj₂ b)

  ext-pure : ∀ {A B : GC-C.Obj} {g} {F : A GC-C.⇒ MaybeT₀ _ B}
           → IsPure g F → IsPure (ext-fn g) (MaybeT-ext F)
  ext-pure p s (inj₁ (inj₁ a)) = p s (inj₁ a)
  ext-pure p s (inj₁ (inj₂ _)) = refl
  ext-pure p s (inj₂ b)        = p s (inj₂ b)

  -- Pure morphisms evaluate to `return ∘ map`.
  pure-trace : {A B : Type} {g : A → B} {F : SFunᵉ A B} → IsPure g F
             → ∀ s xs → trace (SFunᵉ.fun F) s xs ≡ return (map g xs)
  pure-trace p s [] = refl
  pure-trace {g = g} {F} p s (x ∷ xs) = begin
    (SFunᵉ.fun F (s , x) >>= λ (s' , b) →
      trace (SFunᵉ.fun F) s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ p s x ⟩>>=⟨refl ⟩
    (return (s , g x) >>= λ (s' , b) →
      trace (SFunᵉ.fun F) s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    (trace (SFunᵉ.fun F) s xs >>= λ bs → return (g x ∷ bs))
      ≡⟨ pure-trace {F = F} p s xs ⟩>>=⟨refl ⟩
    (return (map g xs) >>= λ bs → return (g x ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    return (g x ∷ map g xs) ∎
    where open ≡-Reasoning

  pure-≈ᵉ : {A B : Type} {p q : A → B} {F G : SFunᵉ A B}
          → IsPure p F → IsPure q G → p ≗ q → F ≈ᵉ G
  pure-≈ᵉ {F = F} {G} pF pG eq xs =
    trans (pure-trace {F = F} pF (SFunᵉ.init F) xs)
      (trans (cong return (map-cong eq xs))
             (sym (pure-trace {F = G} pG (SFunᵉ.init G) xs)))

  -- Composing with a pure morphism on either side collapses to a
  -- single call plus a `return`-rewrap.
  ∘ᵉ-pureˡ : {A B C : Type} {q : A → B} {Q : SFunᵉ A B} (P : SFunᵉ B C)
           → IsPure q Q
           → ∀ sP sQ x
           → SFunᵉ.fun (P ∘ᵉ Q) ((sP , sQ) , x)
             ≡ (SFunᵉ.fun P (sP , q x) >>= λ (sP' , c) → return ((sP' , sQ) , c))
  ∘ᵉ-pureˡ {q = q} {Q} P pQ sP sQ x = begin
    (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) →
      SFunᵉ.fun P (sP , b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ pQ sQ x ⟩>>=⟨refl ⟩
    (return (sQ , q x) >>= λ (sQ' , b) →
      SFunᵉ.fun P (sP , b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ >>=-identityˡ ⟩
    (SFunᵉ.fun P (sP , q x) >>= λ (sP' , c) → return ((sP' , sQ) , c)) ∎
    where open ≡-Reasoning

  ∘ᵉ-pureʳ : {A B C : Type} {p : B → C} {P : SFunᵉ B C} (Q : SFunᵉ A B)
           → IsPure p P
           → ∀ sP sQ x
           → SFunᵉ.fun (P ∘ᵉ Q) ((sP , sQ) , x)
             ≡ (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) → return ((sP , sQ') , p b))
  ∘ᵉ-pureʳ {p = p} {P} Q pP sP sQ x = begin
    (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) →
      SFunᵉ.fun P (sP , b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ refl⟩>>=⟨ (λ (sQ' , b) → pP sP b ⟩>>=⟨refl) ⟩
    (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) →
      return (sP , p b) >>= λ (sP' , c) → return ((sP' , sQ') , c))
      ≡⟨ refl⟩>>=⟨ (λ (sQ' , b) → >>=-identityˡ) ⟩
    (SFunᵉ.fun Q (sQ , x) >>= λ (sQ' , b) → return ((sP , sQ') , p b)) ∎
    where open ≡-Reasoning

  -- One-step characterization of the G-composition body
  -- `gc-α ∘ᵉ ((F ⊗ᵉ G) ∘ᵉ gc-γ)`: an input that `gc-γ` routes to the
  -- F-side (resp. G-side) makes exactly one call into F (resp. G),
  -- rewrapped through `gc-α`.
  module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Type}
           (F : SFunᵉ (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (G : SFunᵉ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) where

    private
      body : SFunᵉ ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)) ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺))
      body = gc-α ∘ᵉ ((F ⊗ᵉ G) ∘ᵉ gc-γ)

    gc-body-fun₁ : ∀ sα sF sG sγ {v} {a} → gc-γ-fn v ≡ inj₁ a
      → SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , v)
        ≡ (SFunᵉ.fun F (sF , a) >>= λ (sF' , w) →
            return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)))
    gc-body-fun₁ sα sF sG sγ {v} {a} eq = begin
      SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , v)
        ≡⟨ ∘ᵉ-pureʳ ((F ⊗ᵉ G) ∘ᵉ gc-γ) gc-α-pure sα ((sF , sG) , sγ) v ⟩
      (SFunᵉ.fun ((F ⊗ᵉ G) ∘ᵉ gc-γ) (((sF , sG) , sγ) , v) >>= λ (sR' , b) →
        return ((sα , sR') , gc-α-fn b))
        ≡⟨ ∘ᵉ-pureˡ (F ⊗ᵉ G) gc-γ-pure (sF , sG) sγ v ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , gc-γ-fn v) >>= λ (sFG' , c) →
         return ((sFG' , sγ) , c)) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ cong (λ z → (SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , z) >>= λ (sFG' , c) →
             return ((sFG' , sγ) , c)) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b)) eq ⟩
      ((SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , inj₁ a) >>= λ (sFG' , c) →
         return ((sFG' , sγ) , c)) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun F (sF , a) >>= λ (sF' , b₀) →
         return ((sF' , sG) , inj₁ b₀) >>= λ (sFG' , c) → return ((sFG' , sγ) , c))
        >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ (refl⟩>>=⟨ (λ (sF' , b₀) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun F (sF , a) >>= λ (sF' , b₀) → return (((sF' , sG) , sγ) , inj₁ b₀))
        >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun F (sF , a) >>= λ (sF' , b₀) →
        return (((sF' , sG) , sγ) , inj₁ b₀) >>= λ (sR' , b) →
          return ((sα , sR') , gc-α-fn b))
        ≡⟨ refl⟩>>=⟨ (λ (sF' , b₀) → >>=-identityˡ) ⟩
      (SFunᵉ.fun F (sF , a) >>= λ (sF' , b₀) →
        return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ b₀))) ∎
      where open ≡-Reasoning

    gc-body-fun₂ : ∀ sα sF sG sγ {v} {c} → gc-γ-fn v ≡ inj₂ c
      → SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , v)
        ≡ (SFunᵉ.fun G (sG , c) >>= λ (sG' , w) →
            return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
    gc-body-fun₂ sα sF sG sγ {v} {c} eq = begin
      SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , v)
        ≡⟨ ∘ᵉ-pureʳ ((F ⊗ᵉ G) ∘ᵉ gc-γ) gc-α-pure sα ((sF , sG) , sγ) v ⟩
      (SFunᵉ.fun ((F ⊗ᵉ G) ∘ᵉ gc-γ) (((sF , sG) , sγ) , v) >>= λ (sR' , b) →
        return ((sα , sR') , gc-α-fn b))
        ≡⟨ ∘ᵉ-pureˡ (F ⊗ᵉ G) gc-γ-pure (sF , sG) sγ v ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , gc-γ-fn v) >>= λ (sFG' , c') →
         return ((sFG' , sγ) , c')) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ cong (λ z → (SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , z) >>= λ (sFG' , c') →
             return ((sFG' , sγ) , c')) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b)) eq ⟩
      ((SFunᵉ.fun (F ⊗ᵉ G) ((sF , sG) , inj₂ c) >>= λ (sFG' , c') →
         return ((sFG' , sγ) , c')) >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun G (sG , c) >>= λ (sG' , d) →
         return ((sF , sG') , inj₂ d) >>= λ (sFG' , c') → return ((sFG' , sγ) , c'))
        >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ (refl⟩>>=⟨ (λ (sG' , d) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun G (sG , c) >>= λ (sG' , d) → return (((sF , sG') , sγ) , inj₂ d))
        >>= λ (sR' , b) → return ((sα , sR') , gc-α-fn b))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun G (sG , c) >>= λ (sG' , d) →
        return (((sF , sG') , sγ) , inj₂ d) >>= λ (sR' , b) →
          return ((sα , sR') , gc-α-fn b))
        ≡⟨ refl⟩>>=⟨ (λ (sG' , d) → >>=-identityˡ) ⟩
      (SFunᵉ.fun G (sG , c) >>= λ (sG' , d) →
        return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ d))) ∎
      where open ≡-Reasoning

  -- ────────────────────────────────────────────────────────────────
  -- Lifting pointwise `fun` equality to trace/eval equality (the
  -- state-projection variant `trace-sim` lives in SFunM).
  trace-cong : {A B S : Type} {f g : SFunType A B S}
             → (∀ s x → f (s , x) ≡ g (s , x))
             → ∀ s xs → trace f s xs ≡ trace g s xs
  trace-cong h s [] = refl
  trace-cong {f = f} {g} h s (x ∷ xs) = begin
    (f (s , x) >>= λ (s' , b) → trace f s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ h s x ⟩>>=⟨refl ⟩
    (g (s , x) >>= λ (s' , b) → trace f s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , b) → trace-cong h s' xs ⟩>>=⟨refl) ⟩
    (g (s , x) >>= λ (s' , b) → trace g s' xs >>= λ bs → return (b ∷ bs)) ∎
    where open ≡-Reasoning

  -- ────────────────────────────────────────────────────────────────
  -- Interleaving factorization of `MaybeT-ext`: its evaluation is the
  -- underlying morphism's evaluation on the non-⊤ inputs, with the
  -- canned ⊤-emission re-inserted at the ⊤-input positions.
  ext-proj : {A⁺ B⁻ : Type} → List ((A⁺ ⊎ ⊤) ⊎ B⁻) → List (A⁺ ⊎ B⁻)
  ext-proj []                   = []
  ext-proj (inj₁ (inj₁ a) ∷ xs) = inj₁ a ∷ ext-proj xs
  ext-proj (inj₁ (inj₂ _) ∷ xs) = ext-proj xs
  ext-proj (inj₂ b ∷ xs)        = inj₂ b ∷ ext-proj xs

  ext-reasm : {A⁺ B⁻ O : Type} → O
            → List ((A⁺ ⊎ ⊤) ⊎ B⁻) → List O → List O
  ext-reasm o⊤ []                   _        = []
  ext-reasm o⊤ (inj₁ (inj₂ _) ∷ xs) ys       = o⊤ ∷ ext-reasm o⊤ xs ys
  ext-reasm o⊤ (inj₁ (inj₁ _) ∷ xs) []       = []
  ext-reasm o⊤ (inj₁ (inj₁ _) ∷ xs) (y ∷ ys) = y ∷ ext-reasm o⊤ xs ys
  ext-reasm o⊤ (inj₂ _ ∷ xs)        []       = []
  ext-reasm o⊤ (inj₂ _ ∷ xs)        (y ∷ ys) = y ∷ ext-reasm o⊤ xs ys

  ext-factor : ∀ {A B : GC-C.Obj} (F : A GC-C.⇒ MaybeT₀ _ B)
               (s : SFunᵉ.State F) xs
             → trace (SFunᵉ.fun (MaybeT-ext F)) s xs
               ≡ (trace (SFunᵉ.fun F) s (ext-proj xs) >>= λ ys →
                   return (ext-reasm (inj₂ (inj₂ tt)) xs ys))
  ext-factor F s [] = sym >>=-identityˡ
  ext-factor {A} {B} F s (inj₁ (inj₁ a) ∷ xs) = begin
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      trace (SFunᵉ.fun (MaybeT-ext F)) s' xs >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → ext-factor F s' xs ⟩>>=⟨refl) ⟩
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      (trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (ext-reasm o⊤ xs ys))
        >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → >>=-assoc _) ⟩
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys →
        return (ext-reasm o⊤ xs ys) >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → refl⟩>>=⟨ λ ys → >>=-identityˡ) ⟩
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys →
        return (y ∷ ext-reasm o⊤ xs ys))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → refl⟩>>=⟨ λ ys → sym >>=-identityˡ) ⟩
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys →
        return (y ∷ ys) >>= λ ys' → return (ext-reasm o⊤ (inj₁ (inj₁ a) ∷ xs) ys'))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → sym (>>=-assoc _)) ⟩
    (SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
      (trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (y ∷ ys))
        >>= λ ys' → return (ext-reasm o⊤ (inj₁ (inj₁ a) ∷ xs) ys'))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((SFunᵉ.fun F (s , inj₁ a) >>= λ (s' , y) →
       trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (y ∷ ys))
      >>= λ ys' → return (ext-reasm o⊤ (inj₁ (inj₁ a) ∷ xs) ys')) ∎
    where
      open ≡-Reasoning
      o⊤ = inj₂ (inj₂ tt)
  ext-factor F s (inj₁ (inj₂ u) ∷ xs) = begin
    (return (s , inj₂ (inj₂ tt)) >>= λ (s' , y) →
      trace (SFunᵉ.fun (MaybeT-ext F)) s' xs >>= λ bs → return (y ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    (trace (SFunᵉ.fun (MaybeT-ext F)) s xs >>= λ bs → return (o⊤ ∷ bs))
      ≡⟨ ext-factor F s xs ⟩>>=⟨refl ⟩
    ((trace (SFunᵉ.fun F) s (ext-proj xs) >>= λ ys → return (ext-reasm o⊤ xs ys))
      >>= λ bs → return (o⊤ ∷ bs))
      ≡⟨ >>=-assoc _ ⟩
    (trace (SFunᵉ.fun F) s (ext-proj xs) >>= λ ys →
      return (ext-reasm o⊤ xs ys) >>= λ bs → return (o⊤ ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ ys → >>=-identityˡ) ⟩
    (trace (SFunᵉ.fun F) s (ext-proj xs) >>= λ ys →
      return (o⊤ ∷ ext-reasm o⊤ xs ys)) ∎
    where
      open ≡-Reasoning
      o⊤ = inj₂ (inj₂ tt)
  ext-factor F s (inj₂ b ∷ xs) = begin
    (SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
      trace (SFunᵉ.fun (MaybeT-ext F)) s' xs >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → ext-factor F s' xs ⟩>>=⟨refl) ⟩
    (SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
      (trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (ext-reasm o⊤ xs ys))
        >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → >>=-assoc _) ⟩
    (SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
      trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys →
        return (ext-reasm o⊤ xs ys) >>= λ bs → return (y ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → refl⟩>>=⟨ λ ys → trans >>=-identityˡ (sym >>=-identityˡ)) ⟩
    (SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
      trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys →
        return (y ∷ ys) >>= λ ys' → return (ext-reasm o⊤ (inj₂ b ∷ xs) ys'))
      ≡⟨ refl⟩>>=⟨ (λ (s' , y) → sym (>>=-assoc _)) ⟩
    (SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
      (trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (y ∷ ys))
        >>= λ ys' → return (ext-reasm o⊤ (inj₂ b ∷ xs) ys'))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((SFunᵉ.fun F (s , inj₂ b) >>= λ (s' , y) →
       trace (SFunᵉ.fun F) s' (ext-proj xs) >>= λ ys → return (y ∷ ys))
      >>= λ ys' → return (ext-reasm o⊤ (inj₂ b ∷ xs) ys')) ∎
    where
      open ≡-Reasoning
      o⊤ = inj₂ (inj₂ tt)

-- The Maybe-graded triple over SFunᵉ-GConstruction. T₀ adds a ⊤
-- alternative to the "input" component of each G-object (so morphisms
-- into T₀ B carry an optional "no emission" on their output coproduct);
-- return and ext are the concrete unit and Kleisli-extension realising
-- this. sub is identity (the grading category V = One has only one
-- morphism). All eight graded-Kleisli laws are proven: the three
-- sub-only laws from `SFunᵉ-GConstruction`'s identity laws directly,
-- the five `ext` laws below from the trace-level infrastructure above.
private
  -- Congruence: `MaybeT-ext` respects observational equality, via the
  -- interleaving factorization `ext-factor`.
  MaybeT-ext-resp-≈ : ∀ {u : OneObj} {v A B} {f g : A GC-C.⇒ MaybeT₀ v B}
    → f GC-C.≈ g → MaybeT-ext {A} {B} f GC-C.≈ MaybeT-ext g
  MaybeT-ext-resp-≈ {f = f} {g} p xs = begin
    eval (MaybeT-ext f) xs
      ≡⟨ ext-factor f (SFunᵉ.init f) xs ⟩
    (eval f (ext-proj xs) >>= λ ys → return (ext-reasm (inj₂ (inj₂ tt)) xs ys))
      ≡⟨ p (ext-proj xs) ⟩>>=⟨refl ⟩
    (eval g (ext-proj xs) >>= λ ys → return (ext-reasm (inj₂ (inj₂ tt)) xs ys))
      ≡⟨ sym (ext-factor g (SFunᵉ.init g) xs) ⟩
    eval (MaybeT-ext g) xs ∎
    where open ≡-Reasoning

  -- Subsumption commutes with ext: pure category reasoning, since all
  -- `sub` maps are `GC-C.id`.
  MaybeT-sub-commute : ∀ {u₁ u₂ v₁ v₂ : OneObj} {A B}
    {α : Lift zeroˡ ⊤} {β : Lift zeroˡ ⊤} {f : A GC-C.⇒ MaybeT₀ u₂ B}
    → MaybeT-ext (GC-C.id GC-C.∘ f) GC-C.∘ GC-C.id
      GC-C.≈ GC-C.id GC-C.∘ MaybeT-ext {A} {B} f
  MaybeT-sub-commute {f = f} = begin
    MaybeT-ext (GC-C.id GC-C.∘ f) GC-C.∘ GC-C.id
      ≈⟨ GC-C.identityʳ ⟩
    MaybeT-ext (GC-C.id GC-C.∘ f)
      ≈⟨ MaybeT-ext-resp-≈ GC-C.identityˡ ⟩
    MaybeT-ext f
      ≈⟨ GC-C.identityˡ ⟨
    GC-C.id GC-C.∘ MaybeT-ext f ∎
    where open GC-C.HomReasoning

  -- Left identity: `ext return` is pure and computes exactly the
  -- braiding σ-fn that `GC-C.id` is made of.
  MaybeT-ext-identityˡ : ∀ {u A}
    → GC-C.id GC-C.∘ MaybeT-ext (MaybeT-return {A}) GC-C.≈ GC-C.id {MaybeT₀ u A}
  MaybeT-ext-identityˡ {u} {A⁺ , A⁻} = begin
    GC-C.id GC-C.∘ MaybeT-ext MaybeT-return
      ≈⟨ GC-C.identityˡ ⟩
    MaybeT-ext (MaybeT-return {A⁺ , A⁻})
      ≈⟨ pure-≈ᵉ (ext-pure {F = MaybeT-return} (ret-pure {A⁺ , A⁻})) (pure-prsh σ-fn)
           (λ where
             (inj₁ (inj₁ a)) → refl
             (inj₁ (inj₂ _)) → refl
             (inj₂ a)        → refl) ⟩
    GC-C.id {MaybeT₀ u (A⁺ , A⁻)} ∎
    where open GC-C.HomReasoning

  -- Right identity: composing with `MaybeT-return` routes every input
  -- through exactly one call to `f`; the loop administration around it
  -- is pure and collapses. Proven by a state-projection simulation.
  MaybeT-ext-identityʳ : ∀ {u A B} {f : A GC-C.⇒ MaybeT₀ u B}
    → GC-C.id GC-C.∘ MaybeT-ext f GC-C.∘ MaybeT-return GC-C.≈ f
  MaybeT-ext-identityʳ {u} {A⁺ , A⁻} {B⁺ , B⁻} {f} =
    GC-C.Equiv.trans GC-C.identityˡ core
    where
      body : SFunᵉ ((A⁺ ⊎ B⁻) ⊎ (A⁻ ⊎ (A⁺ ⊎ ⊤)))
                   ((A⁻ ⊎ (B⁺ ⊎ ⊤)) ⊎ (A⁻ ⊎ (A⁺ ⊎ ⊤)))
      body = gc-α ∘ᵉ ((MaybeT-ext f ⊗ᵉ MaybeT-return) ∘ᵉ gc-γ)

      h : SFunᵉ.State body → SFunᵉ.State f
      h (sα , ((sF , sG) , sγ)) = sF

      -- A loop value on the A⁻ side bounces purely off `MaybeT-return`
      -- and exits.
      step-val : ∀ sα sF sG sγ (a⁻ : A⁻)
        → tr-step body ((sα , ((sF , sG) , sγ)) , inj₁ a⁻)
          ≡ return (inj₂ ((sα , ((sF , sG) , sγ)) , inj₁ a⁻))
      step-val sα sF sG sγ a⁻ = begin
        (SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , inj₂ (inj₁ a⁻)) >>= tr-cont)
          ≡⟨ gc-body-fun₂ (MaybeT-ext f) MaybeT-return sα sF sG sγ
               {v = inj₂ (inj₁ a⁻)} {c = inj₂ a⁻} refl ⟩>>=⟨refl ⟩
        ((SFunᵉ.fun (MaybeT-return {A⁺ , A⁻}) (sG , inj₂ a⁻) >>= λ (sG' , w) →
           return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w))) >>= tr-cont)
          ≡⟨ (ret-pure {A⁺ , A⁻} sG (inj₂ a⁻) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return (sG , inj₁ a⁻) >>= λ (sG' , w) →
           return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w))) >>= tr-cont)
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return ((sα , ((sF , sG) , sγ)) , inj₁ (inj₁ a⁻)) >>= tr-cont)
          ≡⟨ >>=-identityˡ ⟩
        return (inj₂ ((sα , ((sF , sG) , sγ)) , inj₁ a⁻)) ∎
        where open ≡-Reasoning

      loop-finish : ∀ sα sF sG sγ (a⁻ : A⁻)
        → (iter (tr-step body) ((sα , ((sF , sG) , sγ)) , inj₁ a⁻)
            >>= λ (s' , b) → return (h s' , b))
          ≡ return (sF , inj₁ a⁻)
      loop-finish sα sF sG sγ a⁻ = begin
        (iter (tr-step body) ((sα , ((sF , sG) , sγ)) , inj₁ a⁻)
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ iter-fix {f = tr-step body} ((sα , ((sF , sG) , sγ)) , inj₁ a⁻) ⟩>>=⟨refl ⟩
        ((tr-step body ((sα , ((sF , sG) , sγ)) , inj₁ a⁻)
           >>= iter-cont iter (tr-step body)) >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (step-val sα sF sG sγ a⁻ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return (inj₂ ((sα , ((sF , sG) , sγ)) , inj₁ a⁻))
           >>= iter-cont iter (tr-step body)) >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return ((sα , ((sF , sG) , sγ)) , inj₁ a⁻) >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩
        return (sF , inj₁ a⁻) ∎
        where open ≡-Reasoning

      -- The continuation after `f`'s only call collapses to `return`,
      -- whether entered from the top level (via tr-fun-cont) ...
      post-top : ∀ sα sG sγ sF' (w : A⁻ ⊎ (B⁺ ⊎ ⊤))
        → ((return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w))
             >>= tr-fun-cont (iter (tr-step body)))
            >>= λ (s' , b) → return (h s' , b))
          ≡ return (sF' , w)
      post-top sα sG sγ sF' (inj₁ a⁻) = begin
        ((return ((sα , ((sF' , sG) , sγ)) , inj₂ (inj₁ a⁻))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (iter (tr-step body) ((sα , ((sF' , sG) , sγ)) , inj₁ a⁻)
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ loop-finish sα sF' sG sγ a⁻ ⟩
        return (sF' , inj₁ a⁻) ∎
        where open ≡-Reasoning
      post-top sα sG sγ sF' (inj₂ y) = begin
        ((return ((sα , ((sF' , sG) , sγ)) , inj₁ (inj₂ y))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return ((sα , ((sF' , sG) , sγ)) , inj₂ y) >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩
        return (sF' , inj₂ y) ∎
        where open ≡-Reasoning

      -- ... or from inside the loop (via tr-cont / iter-cont).
      post-loop : ∀ sα sG sγ sF' (w : A⁻ ⊎ (B⁺ ⊎ ⊤))
        → (((return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)) >>= tr-cont)
             >>= iter-cont iter (tr-step body))
            >>= λ (s' , b) → return (h s' , b))
          ≡ return (sF' , w)
      post-loop sα sG sγ sF' (inj₁ a⁻) = begin
        (((return ((sα , ((sF' , sG) , sγ)) , inj₂ (inj₁ a⁻)) >>= tr-cont)
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return (inj₁ ((sα , ((sF' , sG) , sγ)) , inj₁ a⁻))
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (iter (tr-step body) ((sα , ((sF' , sG) , sγ)) , inj₁ a⁻)
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ loop-finish sα sF' sG sγ a⁻ ⟩
        return (sF' , inj₁ a⁻) ∎
        where open ≡-Reasoning
      post-loop sα sG sγ sF' (inj₂ y) = begin
        (((return ((sα , ((sF' , sG) , sγ)) , inj₁ (inj₂ y)) >>= tr-cont)
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return (inj₂ ((sα , ((sF' , sG) , sγ)) , inj₂ y))
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return ((sα , ((sF' , sG) , sγ)) , inj₂ y) >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩
        return (sF' , inj₂ y) ∎
        where open ≡-Reasoning

      hyp : ∀ s x
        → (SFunᵉ.fun (tr body) (s , x) >>= λ (s' , b) → return (h s' , b))
          ≡ SFunᵉ.fun f (h s , x)
      hyp (sα , ((sF , sG) , sγ)) (inj₁ a⁺) = begin
        ((SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , inj₁ (inj₁ a⁺))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (gc-body-fun₂ (MaybeT-ext f) MaybeT-return sα sF sG sγ
               {v = inj₁ (inj₁ a⁺)} {c = inj₁ a⁺} refl ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        (((SFunᵉ.fun (MaybeT-return {A⁺ , A⁻}) (sG , inj₁ a⁺) >>= λ (sG' , w) →
            return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ ((ret-pure {A⁺ , A⁻} sG (inj₁ a⁺) ⟩>>=⟨refl) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        (((return (sG , inj₂ (inj₁ a⁺)) >>= λ (sG' , w) →
            return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ (inj₁ a⁺)))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (iter (tr-step body) ((sα , ((sF , sG) , sγ)) , inj₂ (inj₁ a⁺))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ iter-fix {f = tr-step body} ((sα , ((sF , sG) , sγ)) , inj₂ (inj₁ a⁺)) ⟩>>=⟨refl ⟩
        ((tr-step body ((sα , ((sF , sG) , sγ)) , inj₂ (inj₁ a⁺))
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ ((gc-body-fun₁ (MaybeT-ext f) MaybeT-return sα sF sG sγ
               {v = inj₂ (inj₂ (inj₁ a⁺))} {a = inj₁ (inj₁ a⁺)} refl ⟩>>=⟨refl) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((((SFunᵉ.fun f (sF , inj₁ a⁺) >>= λ (sF' , w) →
             return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w))) >>= tr-cont)
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ ((>>=-assoc _ ⟩>>=⟨refl) ⟩>>=⟨refl) ⟩
        (((SFunᵉ.fun f (sF , inj₁ a⁺) >>= λ (sF' , w) →
            return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)) >>= tr-cont)
           >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (>>=-assoc _ ⟩>>=⟨refl) ⟩
        ((SFunᵉ.fun f (sF , inj₁ a⁺) >>= λ (sF' , w) →
           (return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)) >>= tr-cont)
             >>= iter-cont iter (tr-step body))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-assoc _ ⟩
        (SFunᵉ.fun f (sF , inj₁ a⁺) >>= λ (sF' , w) →
          (((return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)) >>= tr-cont)
             >>= iter-cont iter (tr-step body))
            >>= λ (s' , b) → return (h s' , b)))
          ≡⟨ refl⟩>>=⟨ (λ (sF' , w) → post-loop sα sG sγ sF' w) ⟩
        (SFunᵉ.fun f (sF , inj₁ a⁺) >>= λ (sF' , w) → return (sF' , w))
          ≡⟨ >>=-identityʳ _ ⟩
        SFunᵉ.fun f (sF , inj₁ a⁺) ∎
        where open ≡-Reasoning
      hyp (sα , ((sF , sG) , sγ)) (inj₂ b⁻) = begin
        ((SFunᵉ.fun body ((sα , ((sF , sG) , sγ)) , inj₁ (inj₂ b⁻))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (gc-body-fun₁ (MaybeT-ext f) MaybeT-return sα sF sG sγ
               {v = inj₁ (inj₂ b⁻)} {a = inj₂ b⁻} refl ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        (((SFunᵉ.fun f (sF , inj₂ b⁻) >>= λ (sF' , w) →
            return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)))
           >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ (>>=-assoc _ ⟩>>=⟨refl) ⟩
        ((SFunᵉ.fun f (sF , inj₂ b⁻) >>= λ (sF' , w) →
           return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w))
             >>= tr-fun-cont (iter (tr-step body)))
          >>= λ (s' , b) → return (h s' , b))
          ≡⟨ >>=-assoc _ ⟩
        (SFunᵉ.fun f (sF , inj₂ b⁻) >>= λ (sF' , w) →
          ((return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w))
             >>= tr-fun-cont (iter (tr-step body)))
            >>= λ (s' , b) → return (h s' , b)))
          ≡⟨ refl⟩>>=⟨ (λ (sF' , w) → post-top sα sG sγ sF' w) ⟩
        (SFunᵉ.fun f (sF , inj₂ b⁻) >>= λ (sF' , w) → return (sF' , w))
          ≡⟨ >>=-identityʳ _ ⟩
        SFunᵉ.fun f (sF , inj₂ b⁻) ∎
        where open ≡-Reasoning

      core : (MaybeT-ext f GC-C.∘ MaybeT-return) GC-C.≈ f
      core xs =
        trace-sim h hyp (SFunᵉ.init (MaybeT-ext f GC-C.∘ MaybeT-return)) xs

  -- Associativity: both sides trace the same loop with the same state;
  -- the step functions agree pointwise (the inner `g` vs `MaybeT-ext g`
  -- difference only shows on the external ⊤-shortcut, which unrolls
  -- purely through the loop). `iter-cong` lifts the pointwise equality
  -- through the iteration.
  MaybeT-ext-assoc : ∀ {u : OneObj} {v w A B C}
    {f : B GC-C.⇒ MaybeT₀ w C} {g : A GC-C.⇒ MaybeT₀ v B}
    → MaybeT-ext (MaybeT-ext f GC-C.∘ g)
      GC-C.≈ GC-C.id GC-C.∘ (MaybeT-ext f GC-C.∘ MaybeT-ext g)
  MaybeT-ext-assoc {u} {v} {w} {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {f} {g} =
    GC-C.Equiv.trans core (GC-C.Equiv.sym GC-C.identityˡ)
    where
      bodyL : SFunᵉ ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ (B⁺ ⊎ ⊤)))
                    ((A⁻ ⊎ (C⁺ ⊎ ⊤)) ⊎ (B⁻ ⊎ (B⁺ ⊎ ⊤)))
      bodyL = gc-α ∘ᵉ ((MaybeT-ext f ⊗ᵉ g) ∘ᵉ gc-γ)

      bodyR : SFunᵉ (((A⁺ ⊎ ⊤) ⊎ C⁻) ⊎ (B⁻ ⊎ (B⁺ ⊎ ⊤)))
                    ((A⁻ ⊎ (C⁺ ⊎ ⊤)) ⊎ (B⁻ ⊎ (B⁺ ⊎ ⊤)))
      bodyR = gc-α ∘ᵉ ((MaybeT-ext f ⊗ᵉ MaybeT-ext g) ∘ᵉ gc-γ)

      step-≗ : ∀ p → tr-step bodyL p ≡ tr-step bodyR p
      step-≗ ((sα , ((sF , sG) , sγ)) , inj₁ b⁻) =
        trans (gc-body-fun₂ (MaybeT-ext f) g sα sF sG sγ
                 {v = inj₂ (inj₁ b⁻)} {c = inj₂ b⁻} refl ⟩>>=⟨refl)
          (sym (gc-body-fun₂ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
                 {v = inj₂ (inj₁ b⁻)} {c = inj₂ b⁻} refl ⟩>>=⟨refl))
      step-≗ ((sα , ((sF , sG) , sγ)) , inj₂ y) =
        trans (gc-body-fun₁ (MaybeT-ext f) g sα sF sG sγ
                 {v = inj₂ (inj₂ y)} {a = inj₁ y} refl ⟩>>=⟨refl)
          (sym (gc-body-fun₁ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
                 {v = inj₂ (inj₂ y)} {a = inj₁ y} refl ⟩>>=⟨refl))

      tfc-eq : ∀ r → tr-fun-cont (iter (tr-step bodyL)) r
                   ≡ tr-fun-cont (iter (tr-step bodyR)) r
      tfc-eq (s , inj₁ b)  = refl
      tfc-eq (s , inj₂ x') = iter-cong step-≗ (s , x')

      funeq : ∀ s x
        → SFunᵉ.fun (MaybeT-ext (MaybeT-ext f GC-C.∘ g)) (s , x)
          ≡ SFunᵉ.fun (MaybeT-ext f GC-C.∘ MaybeT-ext g) (s , x)
      funeq (sα , ((sF , sG) , sγ)) (inj₁ (inj₁ a)) = begin
        (SFunᵉ.fun bodyL ((sα , ((sF , sG) , sγ)) , inj₁ (inj₁ a))
          >>= tr-fun-cont (iter (tr-step bodyL)))
          ≡⟨ gc-body-fun₂ (MaybeT-ext f) g sα sF sG sγ
               {v = inj₁ (inj₁ a)} {c = inj₁ a} refl ⟩>>=⟨refl ⟩
        ((SFunᵉ.fun g (sG , inj₁ a) >>= λ (sG' , w) →
           return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
          >>= tr-fun-cont (iter (tr-step bodyL)))
          ≡⟨ refl⟩>>=⟨ tfc-eq ⟩
        ((SFunᵉ.fun g (sG , inj₁ a) >>= λ (sG' , w) →
           return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
          >>= tr-fun-cont (iter (tr-step bodyR)))
          ≡⟨ gc-body-fun₂ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
               {v = inj₁ (inj₁ (inj₁ a))} {c = inj₁ (inj₁ a)} refl ⟩>>=⟨refl ⟨
        (SFunᵉ.fun bodyR ((sα , ((sF , sG) , sγ)) , inj₁ (inj₁ (inj₁ a)))
          >>= tr-fun-cont (iter (tr-step bodyR))) ∎
        where open ≡-Reasoning
      funeq (sα , ((sF , sG) , sγ)) (inj₁ (inj₂ u′)) = sym (begin
        (SFunᵉ.fun bodyR ((sα , ((sF , sG) , sγ)) , inj₁ (inj₁ (inj₂ u′)))
          >>= tr-fun-cont (iter (tr-step bodyR)))
          ≡⟨ gc-body-fun₂ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
               {v = inj₁ (inj₁ (inj₂ u′))} {c = inj₁ (inj₂ u′)} refl ⟩>>=⟨refl ⟩
        ((return (sG , inj₂ (inj₂ tt)) >>= λ (sG' , w) →
           return ((sα , ((sF , sG') , sγ)) , gc-α-fn (inj₂ w)))
          >>= tr-fun-cont (iter (tr-step bodyR)))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ (inj₂ tt)))
          >>= tr-fun-cont (iter (tr-step bodyR)))
          ≡⟨ >>=-identityˡ ⟩
        iter (tr-step bodyR) ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ tt))
          ≡⟨ iter-fix {f = tr-step bodyR} ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ tt)) ⟩
        (tr-step bodyR ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ tt))
          >>= iter-cont iter (tr-step bodyR))
          ≡⟨ (gc-body-fun₁ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
               {v = inj₂ (inj₂ (inj₂ tt))} {a = inj₁ (inj₂ tt)} refl ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        (((return (sF , inj₂ (inj₂ tt)) >>= λ (sF' , w) →
            return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w))) >>= tr-cont)
          >>= iter-cont iter (tr-step bodyR))
          ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
        ((return ((sα , ((sF , sG) , sγ)) , inj₁ (inj₂ (inj₂ tt))) >>= tr-cont)
          >>= iter-cont iter (tr-step bodyR))
          ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        (return (inj₂ ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ tt)))
          >>= iter-cont iter (tr-step bodyR))
          ≡⟨ >>=-identityˡ ⟩
        return ((sα , ((sF , sG) , sγ)) , inj₂ (inj₂ tt)) ∎)
        where open ≡-Reasoning
      funeq (sα , ((sF , sG) , sγ)) (inj₂ c⁻) = begin
        (SFunᵉ.fun bodyL ((sα , ((sF , sG) , sγ)) , inj₁ (inj₂ c⁻))
          >>= tr-fun-cont (iter (tr-step bodyL)))
          ≡⟨ gc-body-fun₁ (MaybeT-ext f) g sα sF sG sγ
               {v = inj₁ (inj₂ c⁻)} {a = inj₂ c⁻} refl ⟩>>=⟨refl ⟩
        ((SFunᵉ.fun f (sF , inj₂ c⁻) >>= λ (sF' , w) →
           return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)))
          >>= tr-fun-cont (iter (tr-step bodyL)))
          ≡⟨ refl⟩>>=⟨ tfc-eq ⟩
        ((SFunᵉ.fun f (sF , inj₂ c⁻) >>= λ (sF' , w) →
           return ((sα , ((sF' , sG) , sγ)) , gc-α-fn (inj₁ w)))
          >>= tr-fun-cont (iter (tr-step bodyR)))
          ≡⟨ gc-body-fun₁ (MaybeT-ext f) (MaybeT-ext g) sα sF sG sγ
               {v = inj₁ (inj₂ c⁻)} {a = inj₂ c⁻} refl ⟩>>=⟨refl ⟨
        (SFunᵉ.fun bodyR ((sα , ((sF , sG) , sγ)) , inj₁ (inj₂ c⁻))
          >>= tr-fun-cont (iter (tr-step bodyR))) ∎
        where open ≡-Reasoning

      core : MaybeT-ext (MaybeT-ext f GC-C.∘ g)
             GC-C.≈ (MaybeT-ext f GC-C.∘ MaybeT-ext g)
      core xs = trace-cong funeq
        (SFunᵉ.init (MaybeT-ext (MaybeT-ext f GC-C.∘ g))) xs

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
-- collapse V=One. Since the triple's laws are all proven, the four
-- MaybeHomCategory laws (assoc, identityˡ/ʳ, ∘-resp-≈) are derivable
-- from these by transport through `MaybeHom↔Kl`.
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
-- The bijection-induced definitions make Machine→Hom a functor:
-- `functor-id` below holds definitionally, and `functor-∘` holds up to
-- the categorical hom equality `_≈ᴹᴴ_`, because the Machine round-trip
-- `Hom→Machine ∘ Machine→Hom` is an honest machine isomorphism
-- (`Hom-Machine-roundtrip-≅ᴹ`), provable from the `MonadOfRel` laws.
--
-- The MaybeHomCategory laws are proven below by transporting the
-- machine-level bisimulations (`∘-identityˡ-≅ᴹ`/`∘-identityʳ-≅ᴹ`/
-- `∘-assoc-≅ᴹ`, proven in `Machine.Iso`) through the round-trip.

idᴹᴴ : ∀ {A : Channel} → MaybeHom A A
idᴹᴴ = Machine→Hom MC.id

_∘ᴹᴴ_ : ∀ {A B C : Channel} → MaybeHom B C → MaybeHom A B → MaybeHom A C
g ∘ᴹᴴ f = Machine→Hom (Hom→Machine g MC.∘ Hom→Machine f)

_≈ᴹᴴ_ : ∀ {A B : Channel} → MaybeHom A B → MaybeHom A B → Type₁
_≈ᴹᴴ_ MH₁ MH₂ = Hom→Machine MH₁ ≅ℰ Hom→Machine MH₂

-- `_≈ᴹᴴ_` is an equivalence (inherited from `_≅ℰ_`).
≈ᴹᴴ-isEquivalence : ∀ {A B} → IsEquivalence (_≈ᴹᴴ_ {A} {B})
≈ᴹᴴ-isEquivalence = record
  { refl = ≅ℰ-refl ; sym = ≅ℰ-sym ; trans = ≅ℰ-trans }

-- Why `_≅ℰ_`, and not `_≈ℰ_`: an earlier iteration used
--
--   MH₁ ≈ᴹᴴ MH₂ = Hom→Machine MH₁ ≈ℰ Hom→Machine MH₂
--
-- i.e., for every environment E, *propositional equality* of the
-- Machine records `map-ℰ (Hom→Machine MHᵢ) E`. That made the category
-- laws *independent* statements: a Machine record can only be
-- propositionally equal to another if their State fields are equal as
-- types (apply `cong Machine.State`), but the category operations
-- change the state representation. As the two lemmas below verify
-- definitionally, for `identityˡ` the two sides have, per environment
-- E, states
--
--   (MaybeHom.State f × ⊤) × Machine.State E      (idᴹᴴ ∘ᴹᴴ f)
--    MaybeHom.State f      × Machine.State E      (f)
--
-- — isomorphic but not provably equal in Agda (such equalities follow
-- from univalence but are not derivable; nor are they refutable).
-- Environment equivalence up to machine isomorphism (`_≅ℰ_`, see
-- `Machine.Iso`) keeps the quantification over environments but is
-- invariant under such state-repackaging, so the category laws become
-- honest bisimulation statements. `_≈ℰ_` itself is left untouched for
-- the UC definitions.
private
  -- The state-type computations backing the comment above (both hold
  -- by refl; `cong Machine.State` of any ≈ℰ-based identityˡ proof
  -- would thus prove ((S × ⊤) × T) ≡ (S × T) for arbitrary S, T).
  identityˡ-state-lhs : ∀ {A B} (f : MaybeHom A B) (E : MC.ℰ B)
            → Machine.State (MC.map-ℰ (Hom→Machine (idᴹᴴ ∘ᴹᴴ f)) E)
              ≡ ((MaybeHom.State f × ⊤) × Machine.State E)
  identityˡ-state-lhs f E = refl

  identityˡ-state-rhs : ∀ {A B} (f : MaybeHom A B) (E : MC.ℰ B)
            → Machine.State (MC.map-ℰ (Hom→Machine f) E)
              ≡ (MaybeHom.State f × Machine.State E)
  identityˡ-state-rhs f E = refl

------------------------------------------------------------------------
-- The Machine round-trip, as an honest machine isomorphism.
--
-- `Hom→Machine (Machine→Hom Mch)` keeps `Machine.State Mch`
-- definitionally and only repackages the stepRel through `of-rel`, so
-- the identity on states is a bisimulation: the step transports are
-- exactly the `MonadOfRel` laws (`of-rel-sound`/`of-rel-complete`,
-- packaged above as `Machine-roundtrip-sound`/`-complete`). No
-- Machine-extensionality (propositional equality of Machine records)
-- is needed anywhere below: functoriality of `Machine→Hom` and the
-- MaybeHomCategory laws only use the round-trip up to `_≅ᴹ_`.

Hom-Machine-roundtrip-≅ᴹ : ∀ {A B} (Mch : Machine A B)
                         → Hom→Machine (Machine→Hom Mch) ≅ᴹ Mch
Hom-Machine-roundtrip-≅ᴹ Mch = MkIso
  (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl)
  (Machine-roundtrip-complete Mch) (Machine-roundtrip-sound Mch)

------------------------------------------------------------------------
-- The structural laws of machine composition, up to `_≅ᴹ_`.
--
-- These are honest bisimulation statements on the relational trace
-- semantics (the composite differs from its reassociation only in
-- state representation and deterministic relay hops). All three —
-- `∘-identityˡ-≅ᴹ`, `∘-identityʳ-≅ᴹ`, and `∘-assoc-≅ᴹ` — are proven
-- in `Machine.Iso` (associativity via the flattened three-machine
-- TriTrace normal form).

-- Composition is a congruence for `_≅ℰ_` as well; unlike the `_≅ᴹ_`
-- case this genuinely needs associativity, to re-bracket the
-- environment onto the left component and the left composite onto the
-- right component.
∘-resp-≅ℰ : ∀ {A B C} {f h : Machine B C} {g i : Machine A B}
          → f ≅ℰ h → g ≅ℰ i → (f MC.∘ g) ≅ℰ (h MC.∘ i)
∘-resp-≅ℰ {f = f} {h} {g} {i} p q E =
  ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (p E) ≅ᴹ-refl)
      (≅ᴹ-trans (q (E MC.∘ h)) ∘-assoc-≅ᴹ))

private
  -- Unfold one layer of `∘ᴹᴴ`/`idᴹᴴ`, collapsing the round-trip up to
  -- machine isomorphism (both are `Machine→Hom` of something, so this
  -- is `Hom-Machine-roundtrip-≅ᴹ` at the corresponding Machine).
  unfold-∘ᴹᴴ-≅ᴹ : ∀ {A B C} (g : MaybeHom B C) (f : MaybeHom A B)
                → Hom→Machine (g ∘ᴹᴴ f) ≅ᴹ (Hom→Machine g MC.∘ Hom→Machine f)
  unfold-∘ᴹᴴ-≅ᴹ g f = Hom-Machine-roundtrip-≅ᴹ _

  unfold-idᴹᴴ-≅ᴹ : ∀ {A} → Hom→Machine (idᴹᴴ {A}) ≅ᴹ MC.id
  unfold-idᴹᴴ-≅ᴹ = Hom-Machine-roundtrip-≅ᴹ MC.id

-- The four MaybeHomCategory laws, by transport of the machine-level
-- laws through the round-trip. ∘-resp-≈ needs no machine-level law
-- beyond associativity: it is the congruence `∘-resp-≅ℰ`.

MaybeHomCategory-identityˡ :
  ∀ {A B} {f : MaybeHom A B} → (idᴹᴴ ∘ᴹᴴ f) ≈ᴹᴴ f
MaybeHomCategory-identityˡ {f = f} =
  ≅ᴹ⇒≅ℰ (≅ᴹ-trans
    (≅ᴹ-trans (unfold-∘ᴹᴴ-≅ᴹ idᴹᴴ f)
              (∘-resp-≅ᴹ unfold-idᴹᴴ-≅ᴹ ≅ᴹ-refl))
    ∘-identityˡ-≅ᴹ)

MaybeHomCategory-identityʳ :
  ∀ {A B} {f : MaybeHom A B} → (f ∘ᴹᴴ idᴹᴴ) ≈ᴹᴴ f
MaybeHomCategory-identityʳ {f = f} =
  ≅ᴹ⇒≅ℰ (≅ᴹ-trans
    (≅ᴹ-trans (unfold-∘ᴹᴴ-≅ᴹ f idᴹᴴ)
              (∘-resp-≅ᴹ ≅ᴹ-refl unfold-idᴹᴴ-≅ᴹ))
    ∘-identityʳ-≅ᴹ)

MaybeHomCategory-assoc :
  ∀ {A B C D} {f : MaybeHom A B} {g : MaybeHom B C} {h : MaybeHom C D}
  → ((h ∘ᴹᴴ g) ∘ᴹᴴ f) ≈ᴹᴴ (h ∘ᴹᴴ (g ∘ᴹᴴ f))
MaybeHomCategory-assoc {f = f} {g = g} {h = h} =
  ≅ᴹ⇒≅ℰ (≅ᴹ-trans
    (≅ᴹ-trans (unfold-∘ᴹᴴ-≅ᴹ (h ∘ᴹᴴ g) f)
              (∘-resp-≅ᴹ (unfold-∘ᴹᴴ-≅ᴹ h g) ≅ᴹ-refl))
    (≅ᴹ-trans ∘-assoc-≅ᴹ
      (≅ᴹ-sym (≅ᴹ-trans (unfold-∘ᴹᴴ-≅ᴹ h (g ∘ᴹᴴ f))
                        (∘-resp-≅ᴹ ≅ᴹ-refl (unfold-∘ᴹᴴ-≅ᴹ g f))))))

MaybeHomCategory-∘-resp-≈ :
  ∀ {A B C} {f h : MaybeHom B C} {g i : MaybeHom A B}
  → f ≈ᴹᴴ h → g ≈ᴹᴴ i → (f ∘ᴹᴴ g) ≈ᴹᴴ (h ∘ᴹᴴ i)
MaybeHomCategory-∘-resp-≈ {f = f} {h = h} {g = g} {i = i} p q =
  ≅ℰ-trans (≅ᴹ⇒≅ℰ (unfold-∘ᴹᴴ-≅ᴹ f g))
    (≅ℰ-trans (∘-resp-≅ℰ p q)
      (≅ℰ-sym (≅ᴹ⇒≅ℰ (unfold-∘ᴹᴴ-≅ᴹ h i))))

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
-- Functoriality of `Machine→Hom`.
--
-- `functor-id` is definitional (`idᴹᴴ` *is* `Machine→Hom MC.id`).
-- `functor-∘` holds up to the categorical hom equality `_≈ᴹᴴ_`: both
-- sides round-trip through `Hom→Machine`, and each round-trip is the
-- honest machine isomorphism `Hom-Machine-roundtrip-≅ᴹ`. A
-- *propositional* version (`Machine→Hom (g ∘ f) ≡ …`) would need
-- Machine-extensionality, which we neither have nor need.

functor-id : ∀ {A : Channel} → Machine→Hom (MC.id {A}) ≡ idᴹᴴ
functor-id = refl

functor-∘ : ∀ {A B C : Channel} (g : Machine B C) (f : Machine A B)
          → Machine→Hom (g MC.∘ f) ≈ᴹᴴ (Machine→Hom g ∘ᴹᴴ Machine→Hom f)
functor-∘ g f = ≅ᴹ⇒≅ℰ
  (≅ᴹ-trans (Hom-Machine-roundtrip-≅ᴹ (g MC.∘ f))
    (≅ᴹ-sym (≅ᴹ-trans (unfold-∘ᴹᴴ-≅ᴹ (Machine→Hom g) (Machine→Hom f))
              (∘-resp-≅ᴹ (Hom-Machine-roundtrip-≅ᴹ g)
                         (Hom-Machine-roundtrip-≅ᴹ f)))))

------------------------------------------------------------------------
-- The category of Machines, with the same hom equality `_≅ℰ_`. The
-- laws are the machine-level bisimulations, lifted pointwise to all
-- environments via `≅ᴹ⇒≅ℰ`.

≈ℰ-isEquivalence : ∀ {A B} → IsEquivalence (_≈ℰ_ {A} {B})
≈ℰ-isEquivalence = record
  { refl  = λ E       → refl
  ; sym   = λ p E     → sym (p E)
  ; trans = λ p q E   → trans (p E) (q E)
  }

MachineCategory : Category _ _ _
MachineCategory = record
  { Obj       = Channel
  ; _⇒_       = Machine
  ; _≈_       = _≅ℰ_
  ; id        = MC.id
  ; _∘_       = MC._∘_
  ; assoc     = ≅ᴹ⇒≅ℰ ∘-assoc-≅ᴹ
  ; sym-assoc = ≅ℰ-sym (≅ᴹ⇒≅ℰ ∘-assoc-≅ᴹ)
  ; identityˡ = ≅ᴹ⇒≅ℰ ∘-identityˡ-≅ᴹ
  ; identityʳ = ≅ᴹ⇒≅ℰ ∘-identityʳ-≅ᴹ
  ; identity² = ≅ᴹ⇒≅ℰ ∘-identityˡ-≅ᴹ
  ; equiv     = ≅ℰ-isEquivalence
  ; ∘-resp-≈  = ∘-resp-≅ℰ
  }

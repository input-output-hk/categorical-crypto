{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

-- Machine isomorphism: equality of machines up to a stepRel-preserving
-- bijection of states. This is the hom equality used by the category
-- of machines (`MaybeHomCategory` in `Machine.Category`): unlike the
-- propositional equality underlying `_≈ℰ_`, it is invariant under the
-- state-representation changes that machine composition performs, so
-- the category laws are provable for it (as explicit bisimulations on
-- the trace semantics).

module CategoricalCrypto.Machine.Iso where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Relation.Binary using (IsEquivalence)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

private variable A B C D E : Channel

infix 4 _≅ᴹ_

record _≅ᴹ_ (M M' : Machine A B) : Type where
  constructor MkIso
  open Machine M  renaming (State to S;  stepRel to R)
  open Machine M' renaming (State to S'; stepRel to R')
  field
    to        : S → S'
    from      : S' → S
    from∘to   : ∀ s → from (to s) ≡ s
    to∘from   : ∀ s' → to (from s') ≡ s'
    step-to   : ∀ {s i mo s''} → R s i mo s'' → R' (to s) i mo (to s'')
    step-from : ∀ {s' i mo s''} → R' s' i mo s'' → R (from s') i mo (from s'')

open _≅ᴹ_

≅ᴹ-refl : {M : Machine A B} → M ≅ᴹ M
≅ᴹ-refl = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) (λ p → p) (λ p → p)

≅ᴹ-sym : {M M' : Machine A B} → M ≅ᴹ M' → M' ≅ᴹ M
≅ᴹ-sym φ = MkIso (from φ) (to φ) (to∘from φ) (from∘to φ) (step-from φ) (step-to φ)

≅ᴹ-trans : {M₁ M₂ M₃ : Machine A B} → M₁ ≅ᴹ M₂ → M₂ ≅ᴹ M₃ → M₁ ≅ᴹ M₃
≅ᴹ-trans φ ψ = MkIso
  (λ s → to ψ (to φ s))
  (λ s → from φ (from ψ s))
  (λ s → trans (cong (from φ) (from∘to ψ (to φ s))) (from∘to φ s))
  (λ s → trans (cong (to ψ) (to∘from φ (from ψ s))) (to∘from ψ s))
  (λ p → step-to ψ (step-to φ p))
  (λ p → step-from φ (step-from ψ p))

≅ᴹ-isEquivalence : IsEquivalence (_≅ᴹ_ {A} {B})
≅ᴹ-isEquivalence = record { refl = ≅ᴹ-refl ; sym = ≅ᴹ-sym ; trans = ≅ᴹ-trans }

------------------------------------------------------------------------
-- Congruence: machine composition respects isomorphism.
--
-- An iso of components lifts through the tensor (`CompRel`), the
-- channel reshapes (`modifyStepRel` — definitionally transparent), and
-- the trace (`TraceRel`, by structural recursion). The messages are
-- untouched; only the states map.

private
  ×-map : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
        → (A → C) → (B → D) → A × B → C × D
  ×-map f g (a , b) = f a , g b

  -- Lift a step correspondence through `TraceRel`.
  TraceRel-map :
    ∀ {A B C} (M N : Machine (A ⊗₀ C) (B ⊗₀ C))
      (φ : Machine.State M → Machine.State N)
    → (∀ {s i mo s'} → Machine.stepRel M s i mo s'
                     → Machine.stepRel N (φ s) i mo (φ s'))
    → ∀ {s i mo s'} → TraceRel M s i mo s'
                    → TraceRel N (φ s) i mo (φ s')
  TraceRel-map M N φ h Trace[ p ]      = Trace[ h p ]
  TraceRel-map M N φ h (p Trace∷ₒ tr₀) = h p Trace∷ₒ TraceRel-map M N φ h tr₀
  TraceRel-map M N φ h (p Trace∷ᵢ tr₀) = h p Trace∷ᵢ TraceRel-map M N φ h tr₀

  -- Lift component isos through the tensor's `CompRel`.
  CompRel-map :
    ∀ {A B C D} {M₁ M₁' : Machine A B} {M₂ M₂' : Machine C D}
      (φ₁ : M₁ ≅ᴹ M₁') (φ₂ : M₂ ≅ᴹ M₂')
    → ∀ {s i mo s'} → Tensor.CompRel M₁ M₂ s i mo s'
    → Tensor.CompRel M₁' M₂'
        (×-map (to φ₁) (to φ₂) s) i mo
        (×-map (to φ₁) (to φ₂) s')
  CompRel-map φ₁ φ₂ (Tensor.Step₁ p) = Tensor.Step₁ (step-to φ₁ p)
  CompRel-map φ₁ φ₂ (Tensor.Step₂ p) = Tensor.Step₂ (step-to φ₂ p)

∘-resp-≅ᴹ : {M₁ M₁' : Machine B C} {M₂ M₂' : Machine A B}
          → M₁ ≅ᴹ M₁' → M₂ ≅ᴹ M₂'
          → (M₁ ∘ M₂) ≅ᴹ (M₁' ∘ M₂')
∘-resp-≅ᴹ {M₁ = M₁} {M₁'} {M₂} {M₂'} φ₁ φ₂ = MkIso
  (×-map (to φ₂) (to φ₁))
  (×-map (from φ₂) (from φ₁))
  (λ (s₂ , s₁) → cong₂ _,_ (from∘to φ₂ s₂) (from∘to φ₁ s₁))
  (λ (s₂ , s₁) → cong₂ _,_ (to∘from φ₂ s₂) (to∘from φ₁ s₁))
  (TraceRel-map _ _ _ (CompRel-map φ₂ φ₁))
  (TraceRel-map _ _ _ (CompRel-map (≅ᴹ-sym φ₂) (≅ᴹ-sym φ₁)))



private
  -- Tiny injectivity / conflict helpers (stated over transparent types;
  -- applied to opaque-typed equations via conversion inside the
  -- unfolding blocks).
  inj₁-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
           → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl

  inj₂-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
           → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-inj refl = refl

  inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ ()

  just-inj : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  just≢nothing : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
               → just x ≡ nothing → W
  just≢nothing ()

  nothing≢just : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
               → nothing ≡ just x → W
  nothing≢just ()

private
  -- General-index inversion views: splitting on `TraceRel`/`CompRel`
  -- with fully general indices always succeeds; the resulting
  -- propositional equations are then discharged by conversion inside
  -- `opaque unfolding` blocks (the case-split unifier itself does not
  -- see the unfolding).
  trace-view :
    ∀ {A B C} {M : Machine (A ⊗₀ C) (B ⊗₀ C)} {s i w s'}
    → TraceRel M s i w s'
    → (Machine.stepRel M s i w s')
    ⊎ (∃ λ s₁ → ∃ λ outC →
         Machine.stepRel M s i (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s₁
         × TraceRel M s₁ ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ᵢ outC) w s')
    ⊎ (∃ λ s₁ → ∃ λ inC →
         Machine.stepRel M s i (just ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ₒ inC)) s₁
         × TraceRel M s₁ (((L⊗ ϵ) ⊗R) ↑ᵢ inC) w s')
  trace-view Trace[ p ]      = inj₁ p
  trace-view (p Trace∷ₒ tr₀) = inj₂ (inj₁ (_ , _ , p , tr₀))
  trace-view (p Trace∷ᵢ tr₀) = inj₂ (inj₂ (_ , _ , p , tr₀))

  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp'
    → (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

------------------------------------------------------------------------
-- Composition with the identity machine: the constructive half of the
-- `(id ∘ m) ≅ᴹ m` bisimulation. Every m-step embeds into the composite
-- as a trace chain of one m-step plus deterministic id-relays (the six
-- shapes below, one per external input/output configuration). The
-- inverse half — every composite chain contains exactly one m-step —
-- and the corresponding statements for `m ∘ id` and associativity are
-- future work; see `Machine.Category`, which takes them as module
-- parameters (`∘-identityˡ-≅ᴹ`/`∘-identityʳ-≅ᴹ`/`∘-assoc-≅ᴹ`).

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine

  -- case: external A-in input, external A-out output.
  idˡ-embed-AA : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {a : Channel.inType A} {b : Channel.outType A}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₁ a))
                  (just (construct-⊗ {m = Out} (inj₁ b))) sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₁ a))
                  (just (construct-⊗ {m = Out} (inj₁ b))) (sm' , tt)
  idˡ-embed-AA m p = Trace[ Tensor.Step₁ p ]

  -- case: A-in input, no output.
  idˡ-embed-A∅ : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {a : Channel.inType A}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₁ a)) nothing sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₁ a)) nothing (sm' , tt)
  idˡ-embed-A∅ m p = Trace[ Tensor.Step₁ p ]

  -- case: A-in input, middle-B output (m emits towards B; id
  -- relays it to the external B side).
  idˡ-embed-AB : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {a : Channel.inType A} {ib : Channel.inType B}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₁ a))
                  (just (construct-⊗ {m = Out} (inj₂ ib))) sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₁ a))
                  (just (construct-⊗ {m = Out} (inj₂ ib))) (sm' , tt)
  idˡ-embed-AB m p = Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ refl ]

  -- case: external B-side input (id relays inward), A-out output.
  idˡ-embed-BA : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {ob : Channel.outType B} {b : Channel.outType A}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₂ ob))
                  (just (construct-⊗ {m = Out} (inj₁ b))) sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₂ ob))
                  (just (construct-⊗ {m = Out} (inj₁ b))) (sm' , tt)
  idˡ-embed-BA m p = Tensor.Step₂ refl Trace∷ₒ Trace[ Tensor.Step₁ p ]

  -- case: external B-side input, middle-B output (three hops).
  idˡ-embed-BB : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {ob : Channel.outType B} {ib : Channel.inType B}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₂ ob))
                  (just (construct-⊗ {m = Out} (inj₂ ib))) sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₂ ob))
                  (just (construct-⊗ {m = Out} (inj₂ ib))) (sm' , tt)
  idˡ-embed-BB m p =
    Tensor.Step₂ refl Trace∷ₒ (Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ refl ])

  -- case: external B-side input, no output.
  idˡ-embed-B∅ : ∀ {A B} (m : Machine A B) {sm sm' : Machine.State m}
                {ob : Channel.outType B}
              → Machine.stepRel m sm (construct-⊗ {m = In} (inj₂ ob)) nothing sm'
              → Machine.stepRel (_∘_ {B = B} id m) (sm , tt)
                  (construct-⊗ {m = In} (inj₂ ob)) nothing (sm' , tt)
  idˡ-embed-B∅ m p = Tensor.Step₂ refl Trace∷ₒ Trace[ Tensor.Step₁ p ]

------------------------------------------------------------------------
-- Environment equivalence up to machine isomorphism: the analogue of
-- `_≈ℰ_` with propositional equality of the environment-composites
-- replaced by machine isomorphism. This is the hom equality of the
-- categories in `Machine.Category`: coarse enough to be UC-flavoured
-- (machines are equated when no environment distinguishes them, up to
-- state repackaging), fine enough that the category laws are honest
-- bisimulation statements. `_≈ℰ_` itself is untouched and remains in
-- use for the UC definitions.

infix 4 _≅ℰ_

_≅ℰ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
_≅ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≅ᴹ map-ℰ M' E

≅ℰ-refl : {M : Machine A B} → M ≅ℰ M
≅ℰ-refl E = ≅ᴹ-refl

≅ℰ-sym : {M M' : Machine A B} → M ≅ℰ M' → M' ≅ℰ M
≅ℰ-sym p E = ≅ᴹ-sym (p E)

≅ℰ-trans : {M₁ M₂ M₃ : Machine A B} → M₁ ≅ℰ M₂ → M₂ ≅ℰ M₃ → M₁ ≅ℰ M₃
≅ℰ-trans p q E = ≅ᴹ-trans (p E) (q E)

≅ℰ-isEquivalence : IsEquivalence (_≅ℰ_ {A} {B})
≅ℰ-isEquivalence = record { refl = ≅ℰ-refl ; sym = ≅ℰ-sym ; trans = ≅ℰ-trans }

-- Machine isomorphism implies environment equivalence (composing with
-- an environment is a congruence for `_≅ᴹ_`).
≅ᴹ⇒≅ℰ : {M M' : Machine A B} → M ≅ᴹ M' → M ≅ℰ M'
≅ᴹ⇒≅ℰ φ E = ∘-resp-≅ᴹ ≅ᴹ-refl φ

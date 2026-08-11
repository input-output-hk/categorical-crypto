{-# OPTIONS --safe --without-K #-}

module Categories.FreeMonoidal where

--------------------------------------------------------------------------------
-- Various free monoidal categories. The intended interface to this
-- file is further below, the `FreeMonoidalData` type and
-- `FreeMonoidal` module.
--------------------------------------------------------------------------------

open import Level

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product
open import Function.Base using (case_of_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

data Variant : Set where
  Mon Symm : Variant

-- NOTE: these are deliberately NOT global `instance`s.  Downstream the APROP
-- cone provides its own local instances (e.g. `Symm ≤ Symm`, and per-signature
-- `Symm ≤ v (asFreeMonoidalData …)`), and a global `v≤v : ∀ {v} → v ≤ v` makes
-- those instance searches ambiguous/stuck.  Consumers pass `⦃ v≤v ⦄`
-- explicitly where needed.
data _≤_ : Variant → Variant → Set where
  v≤v : ∀ {v} → v ≤ v

-- The `Mon`-variant "symmetry": `Symm ≤ Mon` is uninhabited, so this is the
-- canonical absurd witness.  Sharing ONE definition (rather than an inline
-- `λ where ⦃ () ⦄` at each use site) keeps the `Symmetric-C` field of a Mon
-- `⟦_⟧ᵥ` definitionally equal across constructions — distinct extended lambdas
-- are not, even when both are absurd.
noSymmetric : ∀ {o ℓ e} {C : Category o ℓ e} {M : Monoidal C}
            → ⦃ Symm ≤ Mon ⦄ → Symmetric M
noSymmetric ⦃ () ⦄

record ⟦_⟧ᵥ (v : Variant) {o ℓ e : Level} : Set (suc (o ⊔ ℓ ⊔ e)) where
  field C : Category o ℓ e
        Monoidal-C : Monoidal C
        Symmetric-C : ⦃ Symm ≤ v ⦄ → Symmetric Monoidal-C

  module Cat where
    open Category C public
    open Monoidal Monoidal-C public
    open import Categories.Category.Monoidal.Utilities Monoidal-C
    open Shorthands public

    module _ ⦃ _ : Symm ≤ v ⦄ where
      open Symmetric Symmetric-C using (commutative; hexagon₁; module braiding) public
      σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      σ {X} {Y} = braiding.⇒.η (X , Y)

-- A `⟦ v ⟧ᵥ` from a bundled `MonoidalCategory` plus its `v`-gated symmetry.
-- One shared builder so the variant interpretation reads the same wherever a
-- target category is reflected into (the free functor, the object map, FSolve.Into).
fromMC : ∀ {o ℓ e} {v} (C : MonoidalCategory o ℓ e)
       → (⦃ Symm ≤ v ⦄ → Symmetric (C .MonoidalCategory.monoidal))
       → ⟦ v ⟧ᵥ {o} {ℓ} {e}
fromMC C sym = record
  { C           = C .MonoidalCategory.U
  ; Monoidal-C  = C .MonoidalCategory.monoidal
  ; Symmetric-C = sym
  }

module FreeMonoidalHelper (v : Variant) (X : Set) where
  infixr 10 _⊗₀_

  data ObjTerm : Set where
    unit : ObjTerm
    _⊗₀_ : ObjTerm → ObjTerm → ObjTerm
    Var : X → ObjTerm

  -- the parallel wires named by a list of labels, right-nested
  wires : List X → ObjTerm
  wires []       = unit
  wires (x ∷ xs) = Var x ⊗₀ wires xs

  -- the flat wire-list of an object term
  flatten : ObjTerm → List X
  flatten unit      = []
  flatten (Y ⊗₀ Z) = flatten Y ++ flatten Z
  flatten (Var x)   = x ∷ []

  private
    ⊗₀-inj₁ : ∀ {a b a' b'} → (a ⊗₀ b) ≡ (a' ⊗₀ b') → a ≡ a'
    ⊗₀-inj₁ refl = refl
    ⊗₀-inj₂ : ∀ {a b a' b'} → (a ⊗₀ b) ≡ (a' ⊗₀ b') → b ≡ b'
    ⊗₀-inj₂ refl = refl
    Var-inj : ∀ {x y} → Var x ≡ Var y → x ≡ y
    Var-inj refl = refl

  ≟ObjTerm : DecidableEquality X → DecidableEquality ObjTerm
  ≟ObjTerm _≟X_ = go
    where
      go : DecidableEquality ObjTerm
      go unit      unit       = yes refl
      go unit      (_ ⊗₀ _)   = no λ ()
      go unit      (Var _)    = no λ ()
      go (_ ⊗₀ _)  unit       = no λ ()
      go (a ⊗₀ b)  (a' ⊗₀ b') = case go a a' of λ where
        (no ¬p)    → no λ eq → ¬p (⊗₀-inj₁ eq)
        (yes refl) → case go b b' of λ where
          (yes refl) → yes refl
          (no ¬q)    → no λ eq → ¬q (⊗₀-inj₂ eq)
      go (_ ⊗₀ _)  (Var _)    = no λ ()
      go (Var _)   unit       = no λ ()
      go (Var _)   (_ ⊗₀ _)   = no λ ()
      go (Var x)   (Var y)    = case _≟X_ x y of λ where
        (yes refl) → yes refl
        (no ¬p)    → no λ eq → ¬p (Var-inj eq)

  module Mor (mor : ObjTerm → ObjTerm → Set) where
    infix  4 _≈Term_
    infixr 9 _∘_
    infixr 10 _⊗₁_

    private variable A B C D : ObjTerm

    data HomTerm : ObjTerm → ObjTerm → Set where
      var : mor A B → HomTerm A B
      id : HomTerm A A
      -- `{A B C}` spelled out, NOT generalised (which would order them
      -- `{B}{C}{A}`): only then does a `Category`'s `_∘_ = _∘_` eta-contract to
      -- the constructor, which is what `Tactic.Category.solve` matches on.
      _∘_ : ∀ {A B C} → HomTerm B C → HomTerm A B → HomTerm A C
      _⊗₁_ : HomTerm A B → HomTerm C D → HomTerm (A ⊗₀ C) (B ⊗₀ D)
      λ⇒ : HomTerm (unit ⊗₀ A) A
      λ⇐ : HomTerm A (unit ⊗₀ A)
      ρ⇒ : HomTerm (A ⊗₀ unit) A
      ρ⇐ : HomTerm A (A ⊗₀ unit)
      α⇒ : HomTerm ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
      α⇐ : HomTerm (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
      σ : ⦃ Symm ≤ v ⦄ → HomTerm (A ⊗₀ B) (B ⊗₀ A)

    private variable f f' g g' h i : HomTerm A B

    data _≈Term_ : HomTerm A B → HomTerm A B → Set where
      idˡ : id ∘ f ≈Term f
      idʳ : f ∘ id ≈Term f
      assoc : (h ∘ g) ∘ f ≈Term h ∘ (g ∘ f)
      ∘-resp-≈ : f ≈Term h → g ≈Term i → f ∘ g ≈Term h ∘ i
      ≈-Term-refl : f ≈Term f
      ≈-Term-sym : f ≈Term g → g ≈Term f
      ≈-Term-trans : f ≈Term g → g ≈Term h → f ≈Term h
      id⊗id≈id : id ⊗₁ id ≈Term id {A ⊗₀ B}
      ⊗-resp-≈ : f ≈Term f' → g ≈Term g' → f ⊗₁ g ≈Term f' ⊗₁ g'
      ⊗-∘-dist : (g ∘ f) ⊗₁ (g' ∘ f') ≈Term g ⊗₁ g' ∘ f ⊗₁ f'
      λ⇐∘λ⇒≈id : λ⇐ ∘ (λ⇒ {A}) ≈Term id
      λ⇒∘λ⇐≈id : λ⇒ ∘ (λ⇐ {A}) ≈Term id
      ρ⇐∘ρ⇒≈id : ρ⇐ ∘ (ρ⇒ {A}) ≈Term id
      ρ⇒∘ρ⇐≈id : ρ⇒ ∘ (ρ⇐ {A}) ≈Term id
      α⇐∘α⇒≈id : α⇐ ∘ (α⇒ {A} {B} {C}) ≈Term id
      α⇒∘α⇐≈id : α⇒ ∘ (α⇐ {A} {B} {C}) ≈Term id
      λ⇒∘id⊗f≈f∘λ⇒ : λ⇒ ∘ id ⊗₁ f ≈Term f ∘ λ⇒
      ρ⇒∘f⊗id≈f∘ρ⇒ : ρ⇒ ∘ f ⊗₁ id ≈Term f ∘ ρ⇒
      α-comm : α⇒ ∘ (f ⊗₁ g) ⊗₁ h ≈Term f ⊗₁ g ⊗₁ h ∘ α⇒
      triangle : id ⊗₁ λ⇒ ∘ (α⇒ {A} {unit} {B}) ≈Term ρ⇒ ⊗₁ id
      pentagon : id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ≈Term α⇒ ∘ (α⇒ {A ⊗₀ B} {C} {D})
      σ∘σ≈id : ⦃ _ : Symm ≤ v ⦄ → σ ∘ σ ≈Term id {A ⊗₀ B}
      σ∘[f⊗g]≈[g⊗f]∘σ : ⦃ _ : Symm ≤ v ⦄ {f : HomTerm A B} {g : HomTerm C D} → σ ∘ (f ⊗₁ g) ≈Term (g ⊗₁ f) ∘ σ
      hexagon : ⦃ _ : Symm ≤ v ⦄ → id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈Term α⇒ ∘ σ ∘ α⇒ {A} {B} {C}

    ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
    ≡⇒≈Term refl = ≈-Term-refl

    FreeMonoidal : Category 0ℓ 0ℓ 0ℓ
    FreeMonoidal = categoryHelper record
      { Obj       = ObjTerm
      ; _⇒_       = HomTerm
      ; _≈_       = _≈Term_
      ; id        = id
      ; _∘_       = _∘_
      ; assoc     = assoc
      ; identityˡ = idˡ
      ; identityʳ = idʳ
      ; equiv     = record { refl = ≈-Term-refl ; sym = ≈-Term-sym ; trans = ≈-Term-trans }
      ; ∘-resp-≈  = ∘-resp-≈
      }

    Monoidal-FreeMonoidal : Monoidal FreeMonoidal
    Monoidal-FreeMonoidal = monoidalHelper FreeMonoidal record
      { ⊗               = record
          { F₀           = uncurry _⊗₀_
          ; F₁           = uncurry _⊗₁_
          ; identity     = id⊗id≈id
          ; homomorphism = ⊗-∘-dist
          ; F-resp-≈     = uncurry ⊗-resp-≈
          }
      ; unit            = unit
      ; unitorˡ         = record { from = λ⇒ ; to = λ⇐ ; iso = record { isoˡ = λ⇐∘λ⇒≈id ; isoʳ = λ⇒∘λ⇐≈id } }
      ; unitorʳ         = record { from = ρ⇒ ; to = ρ⇐ ; iso = record { isoˡ = ρ⇐∘ρ⇒≈id ; isoʳ = ρ⇒∘ρ⇐≈id } }
      ; associator      = record { from = α⇒ ; to = α⇐ ; iso = record { isoˡ = α⇐∘α⇒≈id ; isoʳ = α⇒∘α⇐≈id } }
      ; unitorˡ-commute = λ⇒∘id⊗f≈f∘λ⇒
      ; unitorʳ-commute = ρ⇒∘f⊗id≈f∘ρ⇒
      ; assoc-commute   = α-comm
      ; triangle        = triangle
      ; pentagon        = pentagon
      }

    -- the free monoidal category itself, as the coherence solver's target
    -- bundle (`FinSetup FMC`).
    FMC : MonoidalCategory _ _ _
    FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

    --------------------------------------------------------------------------
    -- Structural merge / split isos between `wires a ⊗₀ wires suf` and the
    -- flat `wires (a ++ suf)`.  Only λ/α coherence morphisms appear, so they
    -- are box-independent; the wire-level engine and the solver front-ends
    -- instantiate them at their generator families instead of re-defining.
    --------------------------------------------------------------------------
    merge : (a : List X) {suf : List X} → HomTerm (wires a ⊗₀ wires suf) (wires (a ++ suf))
    merge []      = λ⇒
    merge (x ∷ a) = id ⊗₁ merge a ∘ α⇒

    split : (a : List X) {suf : List X} → HomTerm (wires (a ++ suf)) (wires a ⊗₀ wires suf)
    split []      = λ⇐
    split (x ∷ a) = α⇐ ∘ id ⊗₁ split a

    open MR FreeMonoidal
    open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; split₁ʳ; merge₂ʳ)
    open Category.HomReasoning FreeMonoidal

    id⊗-∘ : ∀ {Z} {A B C} (P : HomTerm B C) (Q : HomTerm A B)
          → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id {Z} ⊗₁ (P ∘ Q)
    id⊗-∘ P Q = merge₂ʳ

    id⊗-∘3 : ∀ {Z} {A B C D} (P : HomTerm C D) (Q : HomTerm B C) (R : HomTerm A B)
           → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ∘ id {Z} ⊗₁ R ≈Term id {Z} ⊗₁ (P ∘ Q ∘ R)
    id⊗-∘3 {Z} P Q R = (refl⟩∘⟨ id⊗-∘ Q R) ○ id⊗-∘ P (Q ∘ R)

    id⊗-cancel : ∀ {Z} {A B} {P : HomTerm B A} {Q : HomTerm A B}
               → P ∘ Q ≈Term id → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id
    id⊗-cancel {P = P} {Q} PQ = id⊗-∘ P Q ○ (refl⟩⊗⟨ PQ) ○ id⊗id≈id

    -- a ⊗-pair of cancelling composites cancels.  This is the drawer's ⊗-face;
    -- `id⊗-cancel` above is exactly its left-framed instance `⊗-cancel idˡ`,
    -- named because four sites want that framing.
    ⊗-cancel : ∀ {A A' B B'} {P : HomTerm A' A} {Q : HomTerm A A'}
                 {R : HomTerm B' B} {S : HomTerm B B'}
             → P ∘ Q ≈Term id → R ∘ S ≈Term id
             → (P ⊗₁ R) ∘ (Q ⊗₁ S) ≈Term id
    ⊗-cancel PQ RS = ⟺ ⊗-∘-dist ○ (PQ ⟩⊗⟨ RS) ○ id⊗id≈id

    -- Two 3-fold composites sharing a middle iso `Fm ∘ Tm ≈ id` cancel it,
    -- leaving `To ∘ M₁ ∘ M₂ ∘ Ff`.  No assumption on `M₁` / `M₂`.
    cancel-mid-iso
      : ∀ {A₀ A₁ A₂ A₃ A₄ A₅ : ObjTerm}
          (To : HomTerm A₄ A₅) (M₁ : HomTerm A₂ A₄) (Fm : HomTerm A₃ A₂)
          (Tm : HomTerm A₂ A₃) (M₂ : HomTerm A₁ A₂) (Ff : HomTerm A₀ A₁)
      → Fm ∘ Tm ≈Term id
      → (To ∘ M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
        ≈Term To ∘ M₁ ∘ M₂ ∘ Ff
    -- `cancelʳ m-iso : (M₁ ∘ Fm) ∘ Tm ≈ M₁`, in the `center` of the composite.
    cancel-mid-iso _ _ _ _ _ _ m-iso = center (cancelʳ m-iso)

    -- A 3-fold composite and its reverse cancel, innermost pair first: the
    -- `cancel-mid-iso` face above, then the two outer pairs.
    cancel₃
      : ∀ {A₀ A₁ A₂ A₃ : ObjTerm}
          {a : HomTerm A₂ A₃} {b : HomTerm A₁ A₂} {c : HomTerm A₀ A₁}
          {c⁻ : HomTerm A₁ A₀} {b⁻ : HomTerm A₂ A₁} {a⁻ : HomTerm A₃ A₂}
      → c ∘ c⁻ ≈Term id → b ∘ b⁻ ≈Term id → a ∘ a⁻ ≈Term id
      → (a ∘ b ∘ c) ∘ (c⁻ ∘ b⁻ ∘ a⁻) ≈Term id
    cancel₃ hc hb ha = cancel-mid-iso _ _ _ _ _ _ hc ○ (refl⟩∘⟨ cancelˡ hb) ○ ha

    α-conj : ∀ {A B C D E G} (f : HomTerm A B) (g : HomTerm C D) (h : HomTerm E G)
           → α⇒ ∘ (f ⊗₁ g) ⊗₁ h ∘ α⇐ ≈Term f ⊗₁ (g ⊗₁ h)
    α-conj f g h = pullˡ α-comm ○ cancelʳ α⇒∘α⇐≈id

    merge∘split : ∀ (a : List X) {suf} → merge a {suf} ∘ split a ≈Term id
    merge∘split []      = λ⇒∘λ⇐≈id
    merge∘split (x ∷ a) = cancelInner α⇒∘α⇐≈id ○ id⊗-cancel (merge∘split a)

    split∘merge : ∀ (a : List X) {suf} → split a {suf} ∘ merge a ≈Term id
    split∘merge []      = λ⇐∘λ⇒≈id
    split∘merge (x ∷ a) = cancelInner (id⊗-cancel (split∘merge a)) ○ α⇐∘α⇒≈id

    --------------------------------------------------------------------------
    -- The canonical structural iso `Y ≅ wires (flatten Y)`
    --------------------------------------------------------------------------
    flat⇒ : (Y : ObjTerm) → HomTerm Y (wires (flatten Y))
    flat⇒ unit      = id
    flat⇒ (Y ⊗₀ Z) = merge (flatten Y) ∘ (flat⇒ Y ⊗₁ flat⇒ Z)
    flat⇒ (Var x)   = ρ⇐

    flat⇐ : (Y : ObjTerm) → HomTerm (wires (flatten Y)) Y
    flat⇐ unit      = id
    flat⇐ (Y ⊗₀ Z) = (flat⇐ Y ⊗₁ flat⇐ Z) ∘ split (flatten Y)
    flat⇐ (Var x)   = ρ⇒

    flat⇐∘flat⇒ : ∀ (Y : ObjTerm) → flat⇐ Y ∘ flat⇒ Y ≈Term id
    flat⇐∘flat⇒ unit = idˡ
    flat⇐∘flat⇒ (Y ⊗₀ Z) =
      cancelInner (split∘merge (flatten Y))
      ○ ⊗-cancel (flat⇐∘flat⇒ Y) (flat⇐∘flat⇒ Z)
    flat⇐∘flat⇒ (Var x) = ρ⇒∘ρ⇐≈id

    --------------------------------------------------------------------------
    -- The flat-shift wire-frame algebra: `rpad` (suffix idle wires), `liftW`
    -- (prefix idle wires), `pad` (both), and their functoriality lemmas.  Only
    -- `merge`/`split` and the monoidal structure appear, so they live here
    -- alongside merge/split; the wire-level engine and the front-ends
    -- re-export them.
    --------------------------------------------------------------------------

    -- right-pad a morphism g : wires a ⇒ wires b by `suf` idle wires.
    rpad : ∀ {a b} (suf : List X) → HomTerm (wires a) (wires b)
         → HomTerm (wires (a ++ suf)) (wires (b ++ suf))
    rpad {a} {b} suf g = merge b ∘ (g ⊗₁ id {wires suf}) ∘ split a

    -- `liftW p W` : prepend `p` idle wires to a flat morphism on `wires u`.
    liftW : (p : List X) {u v : List X} → HomTerm (wires u) (wires v)
          → HomTerm (wires (p ++ u)) (wires (p ++ v))
    liftW []      W = W
    liftW (x ∷ p) W = id ⊗₁ liftW p W

    -- full padding: `pre` idle wires, the box, then `suf` idle wires.
    -- `pad pre suf g = liftW pre (rpad suf g)` definitionally.
    pad : ∀ {a b} (pre : List X) (suf : List X) → HomTerm (wires a) (wires b)
        → HomTerm (wires (pre ++ (a ++ suf))) (wires (pre ++ (b ++ suf)))
    pad pre suf g = liftW pre (rpad suf g)

    -- liftW p respects ≈ and ∘ (functoriality of the flat shift).
    liftW-resp : ∀ (p : List X) {u v} {P Q : HomTerm (wires u) (wires v)}
               → P ≈Term Q → liftW p P ≈Term liftW p Q
    liftW-resp []      eq = eq
    liftW-resp (x ∷ p) eq = refl⟩⊗⟨ liftW-resp p eq

    liftW-∘ : ∀ (p : List X) {u v w} (P : HomTerm (wires v) (wires w)) (Q : HomTerm (wires u) (wires v))
            → liftW p (P ∘ Q) ≈Term liftW p P ∘ liftW p Q
    liftW-∘ []      P Q = ≈-Term-refl
    liftW-∘ (x ∷ p) P Q = (refl⟩⊗⟨ liftW-∘ p P Q) ○ (⟺ (id⊗-∘ _ _))

    -- liftW of an identity is an identity.
    liftW-id : ∀ (p : List X) {u} → liftW p (id {wires u}) ≈Term id
    liftW-id []      = ≈-Term-refl
    liftW-id (x ∷ p) = (refl⟩⊗⟨ liftW-id p) ○ id⊗id≈id

    -- rpad respects ≈.
    rpad-resp : ∀ {a b} (suf : List X) {g g' : HomTerm (wires a) (wires b)}
              → g ≈Term g' → rpad suf g ≈Term rpad suf g'
    rpad-resp suf eq = refl⟩∘⟨ ((eq ⟩⊗⟨refl) ⟩∘⟨refl)

    -- rpad of an identity is an identity.
    rpad-id : ∀ (rt : List X) {u} → rpad rt (id {wires u}) ≈Term id
    rpad-id rt {u} =
      refl⟩∘⟨ (id⊗id≈id ⟩∘⟨refl)
      ○ refl⟩∘⟨ idˡ
      ○ merge∘split u

    -- rpad distributes over ∘.
    rpad-∘ : ∀ (rt : List X) {u v w} (P : HomTerm (wires v) (wires w)) (Q : HomTerm (wires u) (wires v))
           → rpad rt (P ∘ Q) ≈Term rpad rt P ∘ rpad rt Q
    rpad-∘ rt {u} {v} {w} P Q =
      refl⟩∘⟨ (split₁ʳ ⟩∘⟨refl)
      ○ refl⟩∘⟨ (insertInner (split∘merge v) ⟩∘⟨refl)
      ○ center⁻¹ ≈-Term-refl assoc

    -- pad respects ≈.  `pad pre suf = liftW pre ∘ rpad suf` definitionally, so
    -- the pad functoriality lemmas factor through the liftW-*/rpad-* ones.
    pad-resp : ∀ {a b} (pre suf : List X) {g g' : HomTerm (wires a) (wires b)}
             → g ≈Term g' → pad pre suf g ≈Term pad pre suf g'
    pad-resp pre suf eq    = liftW-resp pre (rpad-resp suf eq)

    -- pad of an identity is an identity.
    pad-id : ∀ {a} (pre suf : List X) → pad pre suf (id {wires a}) ≈Term id
    pad-id pre suf         = liftW-resp pre (rpad-id suf) ○ liftW-id pre

    -- pad distributes over ∘.
    pad-∘ : ∀ {a b c} (pre suf : List X)
              (g : HomTerm (wires b) (wires c)) (f : HomTerm (wires a) (wires b))
          → pad pre suf (g ∘ f) ≈Term pad pre suf g ∘ pad pre suf f
    pad-∘ pre suf g f      = liftW-resp pre (rpad-∘ suf g f) ○ liftW-∘ pre _ _

    module _ ⦃ _ : Symm ≤ v ⦄ where
      open import Categories.Morphism FreeMonoidal

      σ-iso : A ⊗₀ B ≅ B ⊗₀ A
      σ-iso = record { from = σ ; to = σ ; iso = record { isoˡ = σ∘σ≈id ; isoʳ = σ∘σ≈id } }

      Symmetric-Monoidal : Symmetric Monoidal-FreeMonoidal
      Symmetric-Monoidal = symmetricHelper Monoidal-FreeMonoidal record
        { braiding    = pointwise-iso (λ _ → σ-iso) λ where (f , g) → σ∘[f⊗g]≈[g⊗f]∘σ
        ; commutative = σ∘σ≈id
        ; hexagon     = hexagon
        }

  --------------------------------------------------------------------------
  -- Generator bind: the free monoidal category construction is functorial in
  -- its generator family.  A map `h` from one generator family into the free
  -- category over another (both over the SAME atoms) extends homomorphically,
  -- identity on objects.  This is the case `FreeFunctor` cannot express — its
  -- object map is a recursion, not the identity — so it is the library-level
  -- functoriality fact any such injection is an instance of, rather than a
  -- clone of the equational-respect table.
  --------------------------------------------------------------------------
  module Bind {mor₁ mor₂ : ObjTerm → ObjTerm → Set}
              (h : ∀ {A B} → mor₁ A B → Mor.HomTerm mor₂ A B)
    where
    private
      module M₁ = Mor mor₁
      module M₂ = Mor mor₂

    bind : ∀ {A B} → M₁.HomTerm A B → M₂.HomTerm A B
    bind (M₁.var g)   = h g
    bind M₁.id        = M₂.id
    bind (g M₁.∘ f)   = bind g M₂.∘ bind f
    bind (f M₁.⊗₁ g)  = bind f M₂.⊗₁ bind g
    bind M₁.λ⇒        = M₂.λ⇒
    bind M₁.λ⇐        = M₂.λ⇐
    bind M₁.ρ⇒        = M₂.ρ⇒
    bind M₁.ρ⇐        = M₂.ρ⇐
    bind M₁.α⇒        = M₂.α⇒
    bind M₁.α⇐        = M₂.α⇐
    bind (M₁.σ ⦃ s ⦄) = M₂.σ ⦃ s ⦄

    -- bind preserves the equational theory (each axiom maps to the same axiom).
    bind-resp-≈ : ∀ {A B} {f g : M₁.HomTerm A B} → f M₁.≈Term g → bind f M₂.≈Term bind g
    bind-resp-≈ M₁.idˡ                     = M₂.idˡ
    bind-resp-≈ M₁.idʳ                     = M₂.idʳ
    bind-resp-≈ M₁.assoc                   = M₂.assoc
    bind-resp-≈ (M₁.∘-resp-≈ p q)          = M₂.∘-resp-≈ (bind-resp-≈ p) (bind-resp-≈ q)
    bind-resp-≈ M₁.≈-Term-refl             = M₂.≈-Term-refl
    bind-resp-≈ (M₁.≈-Term-sym p)          = M₂.≈-Term-sym (bind-resp-≈ p)
    bind-resp-≈ (M₁.≈-Term-trans p q)      = M₂.≈-Term-trans (bind-resp-≈ p) (bind-resp-≈ q)
    bind-resp-≈ M₁.id⊗id≈id                = M₂.id⊗id≈id
    bind-resp-≈ (M₁.⊗-resp-≈ p q)          = M₂.⊗-resp-≈ (bind-resp-≈ p) (bind-resp-≈ q)
    bind-resp-≈ M₁.⊗-∘-dist                = M₂.⊗-∘-dist
    bind-resp-≈ M₁.λ⇐∘λ⇒≈id                = M₂.λ⇐∘λ⇒≈id
    bind-resp-≈ M₁.λ⇒∘λ⇐≈id                = M₂.λ⇒∘λ⇐≈id
    bind-resp-≈ M₁.ρ⇐∘ρ⇒≈id                = M₂.ρ⇐∘ρ⇒≈id
    bind-resp-≈ M₁.ρ⇒∘ρ⇐≈id                = M₂.ρ⇒∘ρ⇐≈id
    bind-resp-≈ M₁.α⇐∘α⇒≈id                = M₂.α⇐∘α⇒≈id
    bind-resp-≈ M₁.α⇒∘α⇐≈id                = M₂.α⇒∘α⇐≈id
    bind-resp-≈ M₁.λ⇒∘id⊗f≈f∘λ⇒            = M₂.λ⇒∘id⊗f≈f∘λ⇒
    bind-resp-≈ M₁.ρ⇒∘f⊗id≈f∘ρ⇒            = M₂.ρ⇒∘f⊗id≈f∘ρ⇒
    bind-resp-≈ M₁.α-comm                  = M₂.α-comm
    bind-resp-≈ M₁.triangle                = M₂.triangle
    bind-resp-≈ M₁.pentagon                = M₂.pentagon
    bind-resp-≈ (M₁.σ∘σ≈id ⦃ s ⦄)          = M₂.σ∘σ≈id ⦃ s ⦄
    bind-resp-≈ (M₁.σ∘[f⊗g]≈[g⊗f]∘σ ⦃ s ⦄) = M₂.σ∘[f⊗g]≈[g⊗f]∘σ ⦃ s ⦄
    bind-resp-≈ (M₁.hexagon ⦃ s ⦄)         = M₂.hexagon ⦃ s ⦄

record FreeMonoidalData : Set₁ where
  field v : Variant
        X : Set

  open FreeMonoidalHelper v X

  field mor : ObjTerm → ObjTerm → Set

module FreeMonoidal (d : FreeMonoidalData) where
  open FreeMonoidalData d
  open FreeMonoidalHelper v X hiding (module Mor; wires; flatten; ≟ObjTerm) public
  -- The wire-combinator helpers (`split`/`merge`/`liftW`/`pad`/`rpad`/…)
  -- live in `Mor` for the solver's benefit, but are NOT re-exported here:
  -- downstream consumers that `open FreeMonoidal d` (the APROP cone,
  -- PermuteCoherence, …) define their own combinators of the same names,
  -- so re-exporting these would pollute every such namespace. The solver
  -- opens `FreeMonoidalHelper.Mor` directly and is unaffected.
  open FreeMonoidalHelper.Mor v X mor public
    hiding ( liftW; liftW-id; liftW-resp; liftW-∘
           ; merge; merge∘split; split; split∘merge
           ; pad; pad-id; pad-resp; pad-∘
           ; rpad; rpad-id; rpad-resp; rpad-∘ )

-- The object action of the free functor depends only on the atoms'
-- interpretation `⟦_⟧ᵖ₀`, never on the generating morphisms `mor`.  Hoisting
-- it out of the `FreeMonoidalData`-parametrised `FreeFunctorHelper` means two
-- free functors over the SAME atoms but DIFFERENT generators share ONE object
-- map, *definitionally* — which is what lets a caller state a generator's
-- interpretation type (`⟦ Y ⟧₀ ⇒ ⟦ Z ⟧₀`) before fixing the generator
-- signature.
module FreeObjInterp (v : Variant) (X : Set) {o ℓ e : Level}
                     (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e})
                     (let module C = ⟦_⟧ᵥ.Cat ⟦v⟧)
                     (⟦_⟧ᵖ₀ : X → C.Obj) where
  open FreeMonoidalHelper v X
  ⟦_⟧₀ : ObjTerm → C.Obj
  ⟦ unit ⟧₀ = C.unit
  ⟦ A ⊗₀ B ⟧₀ = ⟦ A ⟧₀ C.⊗₀ ⟦ B ⟧₀
  ⟦ Var x ⟧₀ = ⟦ x ⟧ᵖ₀

module FreeFunctorHelper (d : FreeMonoidalData) (let open FreeMonoidalData d)
                         {o ℓ e : Level} (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) where
  open FreeMonoidal d public

  module C = ⟦_⟧ᵥ.Cat ⟦v⟧
  module FM = Category FreeMonoidal

  module Go (⟦_⟧ᵖ₀ : X → C.Obj) where
    open FreeObjInterp v X ⟦v⟧ ⟦_⟧ᵖ₀ public

record FreeFunctorData (d : FreeMonoidalData) {o ℓ e : Level}
                       : Set (suc (o ⊔ ℓ ⊔ e)) where
  open FreeMonoidalData d

  field ⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}

  open FreeFunctorHelper d ⟦v⟧ public

  field ⟦_⟧ᵖ₀ : X → C.Obj

  open Go ⟦_⟧ᵖ₀ public -- this gives us ⟦_⟧₀

  field ⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀

module FreeFunctor {d : FreeMonoidalData} {o ℓ e : Level}
                   (ffd : FreeFunctorData d {o} {ℓ} {e}) where
  open FreeFunctorData ffd

  open ⟦_⟧ᵥ ⟦v⟧

  ⟦_⟧₁ : ∀ {A B} → A FM.⇒ B → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
  ⟦ var x ⟧₁ = ⟦ x ⟧ᵖ₁
  ⟦ id ⟧₁ = C.id
  ⟦ f ∘ f₁ ⟧₁ = ⟦ f ⟧₁ C.∘ ⟦ f₁ ⟧₁
  ⟦ f ⊗₁ f₁ ⟧₁ = ⟦ f ⟧₁ C.⊗₁ ⟦ f₁ ⟧₁
  ⟦ λ⇒ ⟧₁ = C.λ⇒
  ⟦ λ⇐ ⟧₁ = C.λ⇐
  ⟦ ρ⇒ ⟧₁ = C.ρ⇒
  ⟦ ρ⇐ ⟧₁ = C.ρ⇐
  ⟦ α⇒ ⟧₁ = C.α⇒
  ⟦ α⇐ ⟧₁ = C.α⇐
  ⟦ σ ⟧₁ = C.σ

  ⟦⟧-resp-≈ : ∀ {A B} {f g : A FM.⇒ B} → f FM.≈ g → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  ⟦⟧-resp-≈ idˡ                 = C.identityˡ
  ⟦⟧-resp-≈ idʳ                 = C.identityʳ
  ⟦⟧-resp-≈ assoc               = C.assoc
  ⟦⟧-resp-≈ (∘-resp-≈ h h')     = C.∘-resp-≈ (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ≈-Term-refl         = C.Equiv.refl
  ⟦⟧-resp-≈ (≈-Term-sym h)      = C.Equiv.sym (⟦⟧-resp-≈ h)
  ⟦⟧-resp-≈ (≈-Term-trans h h') = C.Equiv.trans (⟦⟧-resp-≈ h) (⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ id⊗id≈id            = C.⊗.identity
  ⟦⟧-resp-≈ (⊗-resp-≈ h h')     = C.⊗.F-resp-≈ (⟦⟧-resp-≈ h , ⟦⟧-resp-≈ h')
  ⟦⟧-resp-≈ ⊗-∘-dist            = C.⊗.homomorphism
  ⟦⟧-resp-≈ λ⇐∘λ⇒≈id            = C.unitorˡ.isoˡ
  ⟦⟧-resp-≈ λ⇒∘λ⇐≈id            = C.unitorˡ.isoʳ
  ⟦⟧-resp-≈ ρ⇐∘ρ⇒≈id            = C.unitorʳ.isoˡ
  ⟦⟧-resp-≈ ρ⇒∘ρ⇐≈id            = C.unitorʳ.isoʳ
  ⟦⟧-resp-≈ α⇐∘α⇒≈id            = C.associator.isoˡ
  ⟦⟧-resp-≈ α⇒∘α⇐≈id            = C.associator.isoʳ
  ⟦⟧-resp-≈ λ⇒∘id⊗f≈f∘λ⇒        = C.unitorˡ-commute-from
  ⟦⟧-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒        = C.unitorʳ-commute-from
  ⟦⟧-resp-≈ α-comm              = C.assoc-commute-from
  ⟦⟧-resp-≈ triangle            = C.triangle
  ⟦⟧-resp-≈ pentagon            = C.pentagon
  ⟦⟧-resp-≈ σ∘σ≈id              = C.commutative
  ⟦⟧-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ     = C.braiding.⇒.commute _
  ⟦⟧-resp-≈ hexagon             = C.hexagon₁

  freeFunctor : Functor FreeMonoidal C
  freeFunctor = record
    { F₀ = ⟦_⟧₀
    ; F₁ = ⟦_⟧₁
    ; identity = C.Equiv.refl
    ; homomorphism = C.Equiv.refl
    ; F-resp-≈ = ⟦⟧-resp-≈
    }

{-# OPTIONS --safe --without-K #-}

module Categories.FreeMonoidal where

--------------------------------------------------------------------------------
-- Various free monoidal categories. The intended interface to this
-- file is further below, the `FreeMonoidalData` type and
-- `FreeMonoidal` module.
--------------------------------------------------------------------------------

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory; monoidalHelper)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties using (pointwise-iso)

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (uncurry; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

data Variant : Set where
  Mon Symm : Variant

-- NOTE: these are deliberately NOT global `instance`s.  Downstream the APROP
-- cone provides its own local instances (e.g. `Symm ≤ Symm`, and per-signature
-- `Symm ≤ v (asFreeMonoidalData …)`), and a global `v≤v : ∀ {v} → v ≤ v` makes
-- those instance searches ambiguous/stuck.  The solver passes `⦃ v≤v ⦄`
-- explicitly where needed.
data _≤_ : Variant → Variant → Set where
  v≤v : ∀ {v} → v ≤ v
  M≤S : Mon ≤ Symm

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

module FreeMonoidalHelper (v : Variant) (X : Set) where
  infixr 10 _⊗₀_

  data ObjTerm : Set where
    unit : ObjTerm
    _⊗₀_ : ObjTerm → ObjTerm → ObjTerm
    Var : X → ObjTerm

  -- the parallel wires named by a list of labels, right-nested.  Object-level
  -- (generator-independent), so it lives here; the structural merge/split isos
  -- between `wires a ⊗₀ wires suf` and `wires (a ++ suf)` are generic in the
  -- generator family and live in `Mor` below.
  wires : List X → ObjTerm
  wires []       = unit
  wires (x ∷ xs) = Var x ⊗₀ wires xs

  module Mor (mor : ObjTerm → ObjTerm → Set) where
    infix  4 _≈Term_
    infixr 9 _∘_
    infixr 10 _⊗₁_

    private variable A B C D : ObjTerm

    data HomTerm : ObjTerm → ObjTerm → Set where
      var : mor A B → HomTerm A B
      id : HomTerm A A
      _∘_ : HomTerm B C → HomTerm A B → HomTerm A C
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

    open MR FreeMonoidal using (center⁻¹; cancelInner; insertInner; pullˡ; cancelʳ)
    open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; split₁ʳ; merge₂ʳ)
    open Category.HomReasoning FreeMonoidal using (_○_; ⟺; refl⟩∘⟨_; _⟩∘⟨refl)

    -- fuse two id-tensored factors:  id⊗₁P ∘ id⊗₁Q ≈ id⊗₁(P∘Q)
    id⊗-∘ : ∀ {Z} {A B C} (P : HomTerm B C) (Q : HomTerm A B)
          → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id {Z} ⊗₁ (P ∘ Q)
    id⊗-∘ P Q = merge₂ʳ

    -- collapse three id-tensored factors:  id⊗₁P ∘ id⊗₁Q ∘ id⊗₁R ≈ id⊗₁(P∘Q∘R)
    id⊗-∘3 : ∀ {Z} {A B C D} (P : HomTerm C D) (Q : HomTerm B C) (R : HomTerm A B)
           → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ∘ id {Z} ⊗₁ R ≈Term id {Z} ⊗₁ (P ∘ Q ∘ R)
    id⊗-∘3 {Z} P Q R = (refl⟩∘⟨ id⊗-∘ Q R) ○ id⊗-∘ P (Q ∘ R)

    -- cancel two id-tensored mutually-inverse factors outright.
    id⊗-cancel : ∀ {Z} {A B} {P : HomTerm B A} {Q : HomTerm A B}
               → P ∘ Q ≈Term id → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id
    id⊗-cancel {P = P} {Q} PQ = id⊗-∘ P Q ○ (refl⟩⊗⟨ PQ) ○ id⊗id≈id

    -- conjugate a triple tensor by the associator:
    --   α⇒ ∘ (f ⊗₁ g) ⊗₁ h ∘ α⇐ ≈ f ⊗₁ (g ⊗₁ h).
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

record FreeMonoidalData : Set₁ where
  field v : Variant
        X : Set

  open FreeMonoidalHelper v X

  field mor : ObjTerm → ObjTerm → Set

module FreeMonoidal (d : FreeMonoidalData) where
  open FreeMonoidalData d
  open FreeMonoidalHelper v X hiding (module Mor; wires) public
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
           ; rpad; rpad-id; rpad-resp; rpad-∘
           ; id⊗-cancel; id⊗-∘; id⊗-∘3; α-conj )

-- This module is a hack, it allows us to 'define' `⟦_⟧₀` in the
-- middle of `FreeFunctorData`. We cannot inline this module, since
-- Agda only allows definitions that can be defined in a let-binding
-- in the middle of a record.
module FreeFunctorHelper (d : FreeMonoidalData) (let open FreeMonoidalData d)
                         {o ℓ e : Level} (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) where
  open FreeMonoidal d public

  module C = ⟦_⟧ᵥ.Cat ⟦v⟧
  module FM = Category FreeMonoidal

  module Go (⟦_⟧ᵖ₀ : X → C.Obj) where
    ⟦_⟧₀ : FM.Obj → C.Obj
    ⟦ unit ⟧₀ = C.unit
    ⟦ A ⊗₀ B ⟧₀ = ⟦ A ⟧₀ C.⊗₀ ⟦ B ⟧₀
    ⟦ Var x ⟧₀ = ⟦ x ⟧ᵖ₀

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

  CM : MonoidalCategory o ℓ e
  CM = record { U = C ; monoidal = Monoidal-C }
  FreeMonoidalM : MonoidalCategory 0ℓ 0ℓ 0ℓ
  FreeMonoidalM = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

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

  isMonoidal-freeFunctor : IsMonoidalFunctor FreeMonoidalM CM freeFunctor
  isMonoidal-freeFunctor = record
    { ε = C.id
    ; ⊗-homo = ntHelper record
      { η       = λ _ → C.id
      ; commute = λ _ → C.identityˡ ○ ⟺ C.identityʳ
      }
    ; associativity = elimʳ (C.identityˡ ○ C.⊗.identity) ○ ⟺ (C.identityˡ ○ elimˡ C.⊗.identity)
    ; unitaryˡ = elimʳ (C.identityˡ ○ C.⊗.identity)
    ; unitaryʳ = elimʳ (C.identityˡ ○ C.⊗.identity)
    }
    where open Category.HomReasoning C
          open import Categories.Morphism.Reasoning C using (elimˡ; elimʳ)

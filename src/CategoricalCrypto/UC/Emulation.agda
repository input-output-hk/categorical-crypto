{-# OPTIONS --safe --without-K #-}

-- UC emulation, stated directly on the grading action.
--
-- A process carrying an adversary interface is a hom `A ⇒ X ⊛ B`; `f ≤UC g`
-- says a simulator `s : Y ⇒ X` turns the ideal `g` into something no
-- environment tells apart from the real `f`.  The reference arc reached the
-- same statement through a graded Kleisli category and its coherence-iso
-- regrading (`Abstract`/`Abstract2`, ~540 LOC); none of that tower is needed
-- for the three metatheorems, which are `sub`'s functoriality plus `_≈ℰ_`'s
-- congruence.
--
-- The dummy-adversary form is *equivalent* here, not merely implied: taking
-- `a := id` inverts `dummy-complete`, which is how `UC.Model.Bridge` reads an
-- inherited `_≤UC_` — whose statement carries the quantifier — back into this
-- one.
--
-- Universal composition is NOT here.  Superseded: it needs a `sub`/`T₁`
-- interchange and an `a⇒`-naturality that `Grading` does not ask for, so this
-- layer could only STATE it, and at the intended instance it is the inherited
-- `Abstract2.UC-compose`, a theorem, transported by `UC.Model.Bridge`'s
-- identification of the two orders.

open import Data.Product.Base using (Σ-syntax; _,_)
import Categories.Morphism.Reasoning as MR

open import Level using (_⊔_)

open import CategoricalCrypto.UC.Core using (UCBase)

module CategoricalCrypto.UC.Emulation
  {o ℓ e os ℓs} (base : UCBase o ℓ e os ℓs) where

open import CategoricalCrypto.UC.Environment base public

open HomReasoning
open MR 𝒞 using (elimˡ)

private variable A B′ X Y Z : Obj

infix 4 _≤UC_ _≤UC⁺_

_≤UC_ : {A B′ X Y : Obj} → A ⇒ X ⊛ B′ → A ⇒ Y ⊛ B′ → Set (o ⊔ ℓ ⊔ ℓs)
_≤UC_ {X = X} {Y} f g = Σ[ s ∈ Y ⇒ X ] f ≈ℰ (sub s ∘ g)

_≤UC⁺_ : {A B′ X Y : Obj} → A ⇒ X ⊛ B′ → A ⇒ Y ⊛ B′ → Set (o ⊔ ℓ ⊔ ℓs)
_≤UC⁺_ {X = X} {Y} f g =
  {Z : Obj} (a : X ⇒ Z) → Σ[ s ∈ Y ⇒ Z ] (sub a ∘ f) ≈ℰ (sub s ∘ g)

private
  merge : {X Y Z A : Obj} {t : Y ⇒ Z} {s : X ⇒ Y} {g : A ⇒ X ⊛ B′}
        → sub t ∘ (sub s ∘ g) ≈ sub (t ∘ s) ∘ g
  merge = sym-assoc ○ ∘-resp-≈ˡ (⟺ sub-∘)

≤UC-refl : {f : A ⇒ X ⊛ B′} → f ≤UC f
≤UC-refl = id , ≈ℰ-sym (≈⇒≈ℰ (elimˡ sub-id))

≤UC-trans : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} {h : A ⇒ Z ⊛ B′}
          → f ≤UC g → g ≤UC h → f ≤UC h
≤UC-trans (s , e) (t , d) =
  s ∘ t , ≈ℰ-trans e (≈ℰ-trans (≈ℰ-congˡ (sub s) d) (≈⇒≈ℰ merge))

dummy-complete : {f : A ⇒ X ⊛ B′} {g : A ⇒ Y ⊛ B′} → f ≤UC g → f ≤UC⁺ g
dummy-complete (s , e) a =
  a ∘ s , ≈ℰ-trans (≈ℰ-congˡ (sub a) e) (≈⇒≈ℰ merge)

------------------------------------------------------------------------
-- Degenerate grades

-- An emulation at a grade every simulator is blind to IS a plain agreement:
-- `f ≤UC g` quantifies the simulator at the graded codomain, and at such a grade
-- it collapses.
blind-grade : {A B′ Z : Obj} {f g : A ⇒ Z ⊛ B′}
            → ((s : Z ⇒ Z) → (sub s ∘ g) ≈ℰ g) → f ≤UC g → f ≈ℰ g
blind-grade blind (s , em) = ≈ℰ-trans em (blind s)

-- …and if the wire inflating a closed process to that grade is absorbed by the
-- ancilla quantifier as well, the emulation is an agreement of the UNGRADED
-- processes: the premise a concrete carry consumes, `UC.Seam.pov-carry` through
-- `UC.Seam.Grounding.StratIsEnv`.
--
-- The two hypotheses are where the content sits, and both are degeneracy facts
-- about the chosen grade rather than about the emulation.  Proved HERE, over an
-- arbitrary base, because at the intended instance a term whose type is an
-- `≈ℰ` between machine COMPOSITES η-expands the observation record and with it
-- the machine equality — measured at a 3 GiB heap, `UC.Seam.Grounding`'s header.
unit-grade : {A B′ Z : Obj} {ι : B′ ⇒ Z ⊛ B′} {u v : A ⇒ B′}
           → ((s : Z ⇒ Z) → (sub s ∘ (ι ∘ v)) ≈ℰ (ι ∘ v))
           → ((ι ∘ u) ≈ℰ (ι ∘ v) → u ≈ℰ v)
           → _≤UC_ {A} {B′} {Z} {Z} (ι ∘ u) (ι ∘ v) → u ≈ℰ v
unit-grade blind reflect e = reflect (blind-grade blind e)

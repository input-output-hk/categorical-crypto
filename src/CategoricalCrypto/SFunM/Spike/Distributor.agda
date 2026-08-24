{-# OPTIONS --safe --without-K #-}

-- SPIKE: the distributor of `Spike.MonoidalDistributive`, one letter and then a
-- whole word at a time.
--
-- One letter (§1) is what `Spike.Tensor` runs on: a map out of `X ⊗₀ (A + C)`
-- is its two branches (`δ-unique`).  A word is what the interface tensor's
-- *congruence* runs on, and binary distributivity does not hand it over:
-- `eval (f ⊗ᵉ idᴹ) n` has to be recognized as `eval f` run on the `A`-subword
-- with the `C`-letters carried along, which the elementwise layer reads off
-- `List`'s `lefts`/`fillˡ` for free.  §2 is that statement:
--
--   X ⊗₀ pow n (A + C)  ≅  ⨁ { X ⊗₀ (pow k A ⊗₀ pow m C) | w : Split n k m }
--
-- a 2ⁿ-fold sum indexed by the words of length `n` over the two letters, whose
-- `w`-th injection `ι w` is the elementwise `fillˡ`.  Both halves of the
-- universal property are proved — `pow-unique` (maps out agree branchwise,
-- which is what the congruence consumes) and `pow-copair`/`pow-copair-inject`
-- (branches assemble) — and `pow-≅` reads the object-level iso off them.
--
-- Only binary distributivity and the symmetry of `⊗` are used: `hdˡ`/`hdʳ`
-- braid the head letter past the tail so that the single `δ⇐` splits it at the
-- state `X ⊗₀ pow n (A + C)`, so no `distributeʳ` field has to be added.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD
import CategoricalCrypto.SFunM.Spike.SlotFrame as SlotFrame

module CategoricalCrypto.SFunM.Spike.Distributor {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv
open MD.MonoidalDistributive dist
open Mealy 𝒱
open SlotFrame 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism U using (JointEpi; _≅_)
open import Categories.Morphism.Reasoning U

private variable A B C X Y Z : Obj
private variable n k m : ℕ

------------------------------------------------------------------------
-- One letter
------------------------------------------------------------------------

-- Two maps out of a distributed sum agree as soon as their branches do: this is
-- the lever that replaces the ⊕-side coherence chains.
δ-unique : {u v : X ⊗₀ (A + B) ⇒ Y}
         → u ∘ id ⊗₁ i₁ ≈ v ∘ id ⊗₁ i₁ → u ∘ id ⊗₁ i₂ ≈ v ∘ id ⊗₁ i₂ → u ≈ v
δ-unique e₁ e₂ = insertʳ distributeˡ.isoʳ
               ○ (∘-distribˡ-[] ○ []-cong₂ e₁ e₂ ○ ⟺ ∘-distribˡ-[]) ⟩∘⟨refl
               ○ cancelʳ distributeˡ.isoʳ

δ⇐-i₁ : δ⇐ ∘ id {X} ⊗₁ i₁ ≈ i₁ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₁ = (refl⟩∘⟨ ⟺ inject₁) ○ cancelˡ distributeˡ.isoˡ

δ⇐-i₂ : δ⇐ ∘ id {X} ⊗₁ i₂ ≈ i₂ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₂ = (refl⟩∘⟨ ⟺ inject₂) ○ cancelˡ distributeˡ.isoˡ

+-unique₂ : {u v : A + B ⇒ Y} → u ∘ i₁ ≈ v ∘ i₁ → u ∘ i₂ ≈ v ∘ i₂ → u ≈ v
+-unique₂ e₁ e₂ = ⟺ +-g-η ○ []-cong₂ e₁ e₂ ○ +-g-η

------------------------------------------------------------------------
-- Cancelling an invertible map on the right
------------------------------------------------------------------------

epiʳ : {h : X ⇒ Y} {h⁻ : Y ⇒ X} → h ∘ h⁻ ≈ id → {u v : Y ⇒ Z} → u ∘ h ≈ v ∘ h → u ≈ v
epiʳ i e = insertʳ i ○ (e ⟩∘⟨refl) ○ ⟺ (insertʳ i)

swapˡ-swapˡ : swapˡ {Y} {X} {Z} ∘ swapˡ ≈ id
swapˡ-swapˡ = center (cancelʳ associator.isoˡ)
            ○ (refl⟩∘⟨ pullˡ (merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity))
            ○ (refl⟩∘⟨ identityˡ) ○ associator.isoʳ

------------------------------------------------------------------------
-- Words
------------------------------------------------------------------------

infixr 5 a∷_ c∷_

-- A word of length `n` over the two letters, `k` of the first and `m` of the
-- second.  Carrying the two counts in the type is what lets a word's sorted
-- decomposition be spelled `pow k A ⊗₀ pow m C` with no arithmetic.
data Split : ℕ → ℕ → ℕ → Set where
  []  : Split 0 0 0
  a∷_ : Split n k m → Split (suc n) (suc k) m
  c∷_ : Split n k m → Split (suc n) k (suc m)

-- The word's letterwise injection: the elementwise layer's `fillˡ`.
ι : ∀ {A C : Obj} {n k m} → Split n k m → pow k A ⊗₀ pow m C ⇒ pow n (A + C)
ι []     = λ⇒
ι (a∷ w) = i₁ ⊗₁ ι w ∘ α⇒
ι (c∷ w) = i₂ ⊗₁ ι w ∘ swapˡ

-- Peeling the head off the sorted decomposition.
γˡ : ∀ {A C X : Obj} {k m} → (X ⊗₀ A) ⊗₀ (pow k A ⊗₀ pow m C) ⇒ X ⊗₀ (pow (suc k) A ⊗₀ pow m C)
γˡ = id ⊗₁ α⇐ ∘ α⇒

γʳ : ∀ {A C X : Obj} {k m} → (X ⊗₀ C) ⊗₀ (pow k A ⊗₀ pow m C) ⇒ X ⊗₀ (pow k A ⊗₀ pow (suc m) C)
γʳ = id ⊗₁ swapˡ ∘ α⇒

------------------------------------------------------------------------
-- Splitting the head letter
------------------------------------------------------------------------

-- Each letter's contribution to a word one longer, with the head braided past
-- the tail so that `δ⇐` splits it at the state `X ⊗₀ pow n (A + C)`.
hdˡ : ∀ {A C X : Obj} {n} → (X ⊗₀ A) ⊗₀ pow n (A + C) ⇒ X ⊗₀ pow (suc n) (A + C)
hdˡ = id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ i₁ ∘ swp))

hdʳ : ∀ {A C X : Obj} {n} → (X ⊗₀ C) ⊗₀ pow n (A + C) ⇒ X ⊗₀ pow (suc n) (A + C)
hdʳ = id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ i₂ ∘ swp))

private
  -- The letter alone: braiding it out and back is the identity.
  hd-letter : (g : A ⇒ B)
            → id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ swp {Z} {A} {X})) ≈ id ⊗₁ (g ⊗₁ id {X}) ∘ α⇒
  hd-letter {Z = Z} {X = X} g = begin
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))))
      ≈⟨ refl⟩∘⟨ pullˡ step-α ⟩
    id ⊗₁ σ⇒ ∘ ((id ⊗₁ (id ⊗₁ g) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)))
      ≈⟨ refl⟩∘⟨ cancelInner associator.isoʳ ⟩
    id ⊗₁ σ⇒ ∘ (id ⊗₁ (id ⊗₁ g) ∘ (id ⊗₁ σ⇒ ∘ α⇒))
      ≈⟨ pullˡ step-σ ⟩
    (id ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒ ∘ α⇒)
      ≈⟨ center σ-pad-inv ⟩
    id ⊗₁ (g ⊗₁ id) ∘ (id ∘ α⇒)
      ≈⟨ refl⟩∘⟨ identityˡ ⟩
    id ⊗₁ (g ⊗₁ id) ∘ α⇒  ∎
    where
      step-α : α⇒ ∘ id {Z ⊗₀ X} ⊗₁ g ≈ id ⊗₁ (id ⊗₁ g) ∘ α⇒
      step-α = (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from

      step-σ : id {Z} ⊗₁ σ⇒ ∘ id ⊗₁ (id {X} ⊗₁ g) ≈ id ⊗₁ (g ⊗₁ id {X}) ∘ id ⊗₁ σ⇒
      step-σ = merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (id , g)) ○ split₂ʳ

  -- …and the head inclusion is natural in the letter and in the tail.
  hd-nat : (g : A ⇒ B) (h : X ⇒ Y)
         → (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ swp {Z} {A} {Y}))) ∘ id ⊗₁ h
         ≈ id ⊗₁ (g ⊗₁ h) ∘ α⇒
  hd-nat {Z = Z} g h = begin
    (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ swp))) ∘ id ⊗₁ h
      ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ assoc) ⟩
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ (swp ∘ id ⊗₁ h)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ swp-natural h ⟩
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ ((id ⊗₁ h) ⊗₁ id ∘ swp)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pad-transport (id ⊗₁ h) g) ⟩
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ (((id ⊗₁ h) ⊗₁ id ∘ id ⊗₁ g) ∘ swp))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ ((id ⊗₁ h) ⊗₁ id ∘ (id ⊗₁ g ∘ swp)))
      ≈⟨ refl⟩∘⟨ (pullˡ assoc-commute-from ○ assoc) ⟩
    id ⊗₁ σ⇒ ∘ (id ⊗₁ (h ⊗₁ id) ∘ (α⇒ ∘ (id ⊗₁ g ∘ swp)))
      ≈⟨ pullˡ step-σ ○ assoc ⟩
    id ⊗₁ (id ⊗₁ h) ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ g ∘ swp)))
      ≈⟨ refl⟩∘⟨ hd-letter g ⟩
    id ⊗₁ (id ⊗₁ h) ∘ (id ⊗₁ (g ⊗₁ id) ∘ α⇒)
      ≈⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ (⟺ serialize₂₁)) ⟩
    id ⊗₁ (g ⊗₁ h) ∘ α⇒  ∎
    where
      step-σ : id {Z} ⊗₁ σ⇒ ∘ id ⊗₁ (h ⊗₁ id {A}) ≈ id ⊗₁ (id ⊗₁ h) ∘ id ⊗₁ σ⇒
      step-σ = merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (h , id)) ○ split₂ʳ

-- `pow` is opaque to the unifier, so from here on the length and the two
-- letters are spelled out wherever a statement is *applied* at a shorter word.
hdˡ-ι : ∀ {A C X : Obj} {n k m} (w : Split n k m)
      → hdˡ {A} {C} {X} {n} ∘ id ⊗₁ ι w ≈ id ⊗₁ ι (a∷ w) ∘ γˡ {A} {C} {X} {k} {m}
hdˡ-ι w = hd-nat i₁ (ι w)
        ○ ⟺ ((split₂ʳ ⟩∘⟨refl) ○ center (pad-inv associator.isoʳ) ○ (refl⟩∘⟨ identityˡ))

hdʳ-ι : ∀ {A C X : Obj} {n k m} (w : Split n k m)
      → hdʳ {A} {C} {X} {n} ∘ id ⊗₁ ι w ≈ id ⊗₁ ι (c∷ w) ∘ γʳ {A} {C} {X} {k} {m}
hdʳ-ι w = hd-nat i₂ (ι w)
        ○ ⟺ ((split₂ʳ ⟩∘⟨refl) ○ center (pad-inv swapˡ-swapˡ) ○ (refl⟩∘⟨ identityˡ))

-- The head letter of a word splits: `δ-unique` at the state `X ⊗₀ pow n (A + C)`.
head-unique : ∀ {A C X Y : Obj} (n : ℕ) {u v : X ⊗₀ pow (suc n) (A + C) ⇒ Y}
            → u ∘ hdˡ {A} {C} {X} {n} ≈ v ∘ hdˡ {A} {C} {X} {n}
            → u ∘ hdʳ {A} {C} {X} {n} ≈ v ∘ hdʳ {A} {C} {X} {n} → u ≈ v
head-unique n e₁ e₂ = epiʳ (cancelInner associator.isoʳ ○ σ-pad-inv)
                         (δ-unique (branch e₁) (branch e₂))
  where
    branch : {j : A ⇒ B} {u v : X ⊗₀ (B ⊗₀ Z) ⇒ Y}
           → u ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ j ∘ swp)))
           ≈ v ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (id ⊗₁ j ∘ swp)))
           → (u ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ id ⊗₁ j ≈ (v ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ id ⊗₁ j
    branch e = epiʳ swp-swp (assoc ○ assoc ○ (refl⟩∘⟨ assoc) ○ e
                             ○ ⟺ (assoc ○ assoc ○ (refl⟩∘⟨ assoc)))

------------------------------------------------------------------------
-- The iterated distributor: uniqueness
------------------------------------------------------------------------

-- Maps out of `X ⊗₀ pow n (A + C)` are determined by their `2ⁿ` letterwise
-- branches.  `δ-unique` splits one letter; this splits a word.
pow-unique : ∀ {A C X Y : Obj} (n : ℕ) {u v : X ⊗₀ pow n (A + C) ⇒ Y}
           → (∀ {k m} (w : Split n k m) → u ∘ id ⊗₁ ι w ≈ v ∘ id ⊗₁ ι w) → u ≈ v
pow-unique zero e = epiʳ (pad-inv unitorˡ.isoʳ) (e [])
pow-unique {A} {C} {X} (suc n) e =
  head-unique n
    (pow-unique {A} {C} {X ⊗₀ A} n (λ w → transfer (hdˡ-ι {A = A} {C} {X} w) (e (a∷ w))))
    (pow-unique {A} {C} {X ⊗₀ C} n (λ w → transfer (hdʳ-ι {A = A} {C} {X} w) (e (c∷ w))))
  where
    -- Both branches transport the hypothesis at the longer word along the head
    -- inclusion, up to the shuffle `γˡ`/`γʳ` that peels the head off.
    transfer : ∀ {S T V W R} {hd : S ⇒ T} {g : V ⇒ S} {j : W ⇒ T} {γ : V ⇒ W}
                 {u v : T ⇒ R}
             → hd ∘ g ≈ j ∘ γ → u ∘ j ≈ v ∘ j → (u ∘ hd) ∘ g ≈ (v ∘ hd) ∘ g
    transfer c d = assoc ○ (refl⟩∘⟨ c) ○ sym-assoc ○ (d ⟩∘⟨refl)
                 ○ assoc ○ (refl⟩∘⟨ ⟺ c) ○ sym-assoc

-- The same at no state, which is the form `eval` needs.
pow-unique′ : ∀ {A C Y : Obj} (n : ℕ) {u v : pow n (A + C) ⇒ Y}
            → (∀ {k m} (w : Split n k m) → u ∘ ι w ≈ v ∘ ι w) → u ≈ v
pow-unique′ n e = epiʳ unitorˡ.isoʳ
  (pow-unique n λ w → pullʳ unitorˡ-commute-from ○ sym-assoc ○ (e w ⟩∘⟨refl)
                    ○ assoc ○ ⟺ (pullʳ unitorˡ-commute-from))

-- The same statement in upstream's vocabulary.
ι-jointEpi : ∀ {A C X : Obj} (n : ℕ)
           → JointEpi (Σ ℕ λ k → Σ ℕ λ m → Split n k m)
                      (λ (k , m , _) → X ⊗₀ (pow k A ⊗₀ pow m C))
                      (λ (_ , _ , w) → id ⊗₁ ι w)
ι-jointEpi n _ _ e = pow-unique n λ {k} {m} w → e (k , m , w)

------------------------------------------------------------------------
-- The iterated distributor: copairing
------------------------------------------------------------------------

γˡ-iso : ∀ {A C X : Obj} {k m}
       → γˡ {A} {C} {X} {k} {m} ∘ (α⇐ ∘ id ⊗₁ α⇒) ≈ id
γˡ-iso = cancelInner associator.isoʳ ○ pad-inv associator.isoˡ

γʳ-iso : ∀ {A C X : Obj} {k m}
       → γʳ {A} {C} {X} {k} {m} ∘ (α⇐ ∘ id ⊗₁ swapˡ) ≈ id
γʳ-iso = cancelInner associator.isoʳ ○ pad-inv swapˡ-swapˡ

-- Exposing the head letter's sum, which is where the one-step `δ⇐` acts.
splitHead : ∀ {A C X : Obj} {n}
          → X ⊗₀ pow (suc n) (A + C) ⇒ ((X ⊗₀ pow n (A + C)) ⊗₀ A) + ((X ⊗₀ pow n (A + C)) ⊗₀ C)
splitHead = δ⇐ ∘ (α⇐ ∘ id ⊗₁ σ⇒)

private
  splitHead-hdˡ : ∀ {A C X : Obj} {n}
                → splitHead {A} {C} {X} {n} ∘ hdˡ {A} {C} {X} {n} ≈ i₁ ∘ swp
  splitHead-hdˡ = assoc ○ (refl⟩∘⟨ cancelInner σ-pad-inv)
                ○ (refl⟩∘⟨ cancelˡ associator.isoˡ) ○ pullˡ δ⇐-i₁

  splitHead-hdʳ : ∀ {A C X : Obj} {n}
                → splitHead {A} {C} {X} {n} ∘ hdʳ {A} {C} {X} {n} ≈ i₂ ∘ swp
  splitHead-hdʳ = assoc ○ (refl⟩∘⟨ cancelInner σ-pad-inv)
                ○ (refl⟩∘⟨ cancelˡ associator.isoˡ) ○ pullˡ δ⇐-i₂

-- Branches indexed by words assemble into a map out of `X ⊗₀ pow n (A + C)`.
-- The two recursive branch families are named so that `pow-copair-inject` can
-- talk about the very same terms `pow-copair` recurses on.
brˡ : ∀ {A C Y : Obj} (X : Obj) (n : ℕ)
      (h : ∀ {k m} → Split (suc n) k m → X ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y)
      {k m} → Split n k m → (X ⊗₀ A) ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y
brˡ {A} {C} X n h {k} {m} w = h (a∷ w) ∘ γˡ {A} {C} {X} {k} {m}

brʳ : ∀ {A C Y : Obj} (X : Obj) (n : ℕ)
      (h : ∀ {k m} → Split (suc n) k m → X ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y)
      {k m} → Split n k m → (X ⊗₀ C) ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y
brʳ {A} {C} X n h {k} {m} w = h (c∷ w) ∘ γʳ {A} {C} {X} {k} {m}

pow-copair : ∀ {A C Y : Obj} (X : Obj) (n : ℕ)
           → (∀ {k m} → Split n k m → X ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y)
           → X ⊗₀ pow n (A + C) ⇒ Y
pow-copair X zero h = h [] ∘ id ⊗₁ λ⇐
pow-copair {A} {C} X (suc n) h =
  [ pow-copair (X ⊗₀ A) n (brˡ X n h) ∘ swp
  , pow-copair (X ⊗₀ C) n (brʳ X n h) ∘ swp ] ∘ splitHead {A} {C} {X} {n}

pow-copair-inject : ∀ {A C Y : Obj} (X : Obj) (n : ℕ)
                    (h : ∀ {k m} → Split n k m → X ⊗₀ (pow k A ⊗₀ pow m C) ⇒ Y)
                    {k m} (w : Split n k m)
                  → pow-copair X n h ∘ id ⊗₁ ι w ≈ h w
pow-copair-inject X zero h [] = cancelʳ (pad-inv unitorˡ.isoˡ)
pow-copair-inject {A} {C} X (suc n) h {suc k} {m} (a∷ w) =
  epiʳ (γˡ-iso {A} {C} {X} {k} {m})
       (assoc ○ (refl⟩∘⟨ ⟺ (hdˡ-ι {A = A} {C} {X} w)) ○ pullˡ copair-hdˡ
        ○ pow-copair-inject (X ⊗₀ A) n (brˡ X n h) w)
  where
    copair-hdˡ : pow-copair X (suc n) h ∘ hdˡ {A} {C} {X} {n}
               ≈ pow-copair (X ⊗₀ A) n (brˡ X n h)
    copair-hdˡ = assoc ○ (refl⟩∘⟨ splitHead-hdˡ {A} {C} {X} {n}) ○ pullˡ inject₁
               ○ cancelʳ swp-swp
pow-copair-inject {A} {C} X (suc n) h {k} {suc m} (c∷ w) =
  epiʳ (γʳ-iso {A} {C} {X} {k} {m})
       (assoc ○ (refl⟩∘⟨ ⟺ (hdʳ-ι {A = A} {C} {X} w)) ○ pullˡ copair-hdʳ
        ○ pow-copair-inject (X ⊗₀ C) n (brʳ X n h) w)
  where
    copair-hdʳ : pow-copair X (suc n) h ∘ hdʳ {A} {C} {X} {n}
               ≈ pow-copair (X ⊗₀ C) n (brʳ X n h)
    copair-hdʳ = assoc ○ (refl⟩∘⟨ splitHead-hdʳ {A} {C} {X} {n}) ○ pullˡ inject₂
               ○ cancelʳ swp-swp

------------------------------------------------------------------------
-- The 2ⁿ-fold sum, and the object-level iso
------------------------------------------------------------------------

-- A family indexed by the words of length `n`, summed as an iterated binary `+`
-- over the two-letter branching.
bigSum : (n : ℕ) → (∀ {k m} → Split n k m → Obj) → Obj
bigSum zero    F = F []
bigSum (suc n) F = bigSum n (λ w → F (a∷ w)) + bigSum n (λ w → F (c∷ w))

inj : ∀ {n} (F : ∀ {k m} → Split n k m → Obj) {k m} (w : Split n k m) → F w ⇒ bigSum n F
inj F []     = id
inj F (a∷ w) = i₁ ∘ inj (λ w′ → F (a∷ w′)) w
inj F (c∷ w) = i₂ ∘ inj (λ w′ → F (c∷ w′)) w

bigSum-copair : ∀ {Y} (n : ℕ) (F : ∀ {k m} → Split n k m → Obj)
              → (∀ {k m} (w : Split n k m) → F w ⇒ Y) → bigSum n F ⇒ Y
bigSum-copair zero    F h = h []
bigSum-copair (suc n) F h = [ bigSum-copair n (λ w → F (a∷ w)) (λ w → h (a∷ w))
                            , bigSum-copair n (λ w → F (c∷ w)) (λ w → h (c∷ w)) ]

bigSum-inject : ∀ {Y} (n : ℕ) (F : ∀ {k m} → Split n k m → Obj)
                (h : ∀ {k m} (w : Split n k m) → F w ⇒ Y) {k m} (w : Split n k m)
              → bigSum-copair n F h ∘ inj F w ≈ h w
bigSum-inject zero    F h []     = identityʳ
bigSum-inject (suc n) F h (a∷ w) =
  pullˡ inject₁ ○ bigSum-inject n (λ w′ → F (a∷ w′)) (λ w′ → h (a∷ w′)) w
bigSum-inject (suc n) F h (c∷ w) =
  pullˡ inject₂ ○ bigSum-inject n (λ w′ → F (c∷ w′)) (λ w′ → h (c∷ w′)) w

bigSum-unique : ∀ {Y} (n : ℕ) (F : ∀ {k m} → Split n k m → Obj) {u v : bigSum n F ⇒ Y}
              → (∀ {k m} (w : Split n k m) → u ∘ inj F w ≈ v ∘ inj F w) → u ≈ v
bigSum-unique zero    F e = ⟺ identityʳ ○ e [] ○ identityʳ
bigSum-unique (suc n) F e =
  +-unique₂ (bigSum-unique n (λ w → F (a∷ w)) (λ w → assoc ○ e (a∷ w) ○ sym-assoc))
            (bigSum-unique n (λ w → F (c∷ w)) (λ w → assoc ○ e (c∷ w) ○ sym-assoc))

-- The iterated distributor.  Both halves of the universal property are in hand,
-- so the object-level iso is the usual two-line argument.
pow-≅ : ∀ {A C : Obj} (X : Obj) (n : ℕ)
      → X ⊗₀ pow n (A + C) ≅ bigSum n (λ {k} {m} _ → X ⊗₀ (pow k A ⊗₀ pow m C))
pow-≅ {A} {C} X n = record
  { from = pow-copair X n (inj F)
  ; to   = bigSum-copair n F ιs
  ; iso  = record
      { isoˡ = pow-unique {A} {C} {X} {_} n λ w →
                 assoc ○ (refl⟩∘⟨ pow-copair-inject X n (inj F) w)
                       ○ bigSum-inject n F ιs w ○ ⟺ identityˡ
      ; isoʳ = bigSum-unique n F λ w →
                 assoc ○ (refl⟩∘⟨ bigSum-inject n F ιs w)
                       ○ pow-copair-inject X n (inj F) w ○ ⟺ identityˡ
      }
  }
  where
    F : ∀ {k m} → Split n k m → Obj
    F {k} {m} _ = X ⊗₀ (pow k A ⊗₀ pow m C)

    ιs : ∀ {k m} (w : Split n k m) → F w ⇒ X ⊗₀ pow n (A + C)
    ιs w = id ⊗₁ ι w

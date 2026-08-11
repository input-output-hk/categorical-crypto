{-# OPTIONS --safe --without-K #-}

-- General theory of Markov categories: deterministic morphisms,
-- marginals, joints from kernels, and basic structural results

open import Level
open import Data.Product using (_,_; ∃-syntax)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Markov using (MarkovCategory; shuffle)

import Categories.Morphism.Reasoning as MR
import Categories.Category.Monoidal.Reasoning as MonR

module Categories.Markov.Properties {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞}
  {symmetric : Symmetric monoidal} (𝓜 : MarkovCategory symmetric) where

open Category 𝒞
open Symmetric symmetric
open MarkovCategory 𝓜
open HomReasoning
open Equiv
open MR 𝒞
open MonR monoidal using (⊗-resp-≈; ⊗-resp-≈ˡ; ⊗-resp-≈ʳ; _⟩⊗⟨_; refl⟩⊗⟨_; _⟩⊗⟨refl; ⊗-distrib-over-∘)

private variable A A' B B' C C' X X' Y Y' Z : Obj

------------------------------------------------------------------------
-- 1. The unit is terminal: `del` is the unique morphism into `unit`.

del-unique : (f : X ⇒ unit) → f ≈ del
del-unique f = begin
  f               ≈˘⟨ identityˡ ⟩
  id ∘ f          ≈˘⟨ del-𝟙 ⟩∘⟨refl ⟩
  del {unit} ∘ f  ≈⟨ discard-natural f ⟩
  del             ∎

del-unique₂ : (f g : X ⇒ unit) → f ≈ g
del-unique₂ f g = trans (del-unique f) (sym (del-unique g))

------------------------------------------------------------------------
-- 2. Deterministic morphisms.
--
-- A morphism `f : X ⇒ Y` is *deterministic* if copying its output
-- agrees with applying it to two copies of the input. Equivalently
-- (under the Markov axiom), `f` is a comonoid homomorphism w.r.t.
-- the canonical (copy, del) comonoid on every object.
--
-- Intuitively, in the Kleisli category of a probability monad,
-- deterministic kernels are the "function-like" ones — they send each
-- input to a Dirac on a single output. The deterministic subcategory
-- `Det(𝒞)` is itself a Markov category.

IsDeterministic : X ⇒ Y → Set e
IsDeterministic f = copy ∘ f ≈ (f ⊗₁ f) ∘ copy

------------------------------------------------------------------------
-- 3. Closure properties of `IsDeterministic`.

id-det : IsDeterministic (id {X})
id-det = begin
  copy ∘ id          ≈⟨ identityʳ ⟩
  copy               ≈˘⟨ identityˡ ⟩
  id ∘ copy          ≈˘⟨ ⊗.identity ⟩∘⟨refl ⟩
  (id ⊗₁ id) ∘ copy  ∎

∘-det : {f : Y ⇒ Z} {g : X ⇒ Y} → IsDeterministic f → IsDeterministic g → IsDeterministic (f ∘ g)
∘-det {f = f} {g} fd gd = begin
  copy ∘ (f ∘ g)                ≈⟨ sym-assoc ⟩
  (copy ∘ f) ∘ g                ≈⟨ fd ⟩∘⟨refl ⟩
  ((f ⊗₁ f) ∘ copy) ∘ g         ≈⟨ assoc ⟩
  (f ⊗₁ f) ∘ (copy ∘ g)         ≈⟨ refl⟩∘⟨ gd ⟩
  (f ⊗₁ f) ∘ ((g ⊗₁ g) ∘ copy)  ≈⟨ sym-assoc ⟩
  ((f ⊗₁ f) ∘ (g ⊗₁ g)) ∘ copy  ≈˘⟨ ⊗.homomorphism ⟩∘⟨refl ⟩
  ((f ∘ g) ⊗₁ (f ∘ g)) ∘ copy   ∎

del-det : IsDeterministic (del {X})
del-det = begin
  copy ∘ del                            ≈⟨ copy-on-unit ⟩∘⟨refl ⟩
  unitorˡ.to ∘ del                      ≈˘⟨ refl⟩∘⟨ discard-natural copy ⟩
  unitorˡ.to ∘ (del ∘ copy)             ≈⟨ sym-assoc ⟩
  (unitorˡ.to ∘ del) ∘ copy             ≈⟨ ⊗-as-del ⟩∘⟨refl ⟩
  (del ⊗₁ del) ∘ copy                   ∎
  where
    copy-on-unit : copy ≈ unitorˡ.to
    copy-on-unit = begin
      copy                                   ≈˘⟨ identityˡ ⟩
      id ∘ copy                              ≈˘⟨ unitorˡ.isoˡ ⟩∘⟨refl ⟩
      (unitorˡ.to ∘ unitorˡ.from) ∘ copy     ≈⟨ assoc ⟩
      unitorˡ.to ∘ (unitorˡ.from ∘ copy)     ≈⟨ refl⟩∘⟨ copy-𝟙 ⟩
      unitorˡ.to ∘ id                        ≈⟨ identityʳ ⟩
      unitorˡ.to                             ∎

    ⊗-as-del : unitorˡ.to ∘ del ≈ del ⊗₁ del
    ⊗-as-del = begin
      unitorˡ.to ∘ del                        ≈˘⟨ refl⟩∘⟨ del-⊗ ⟩
      unitorˡ.to ∘ (unitorˡ.from ∘ (del ⊗₁ del))
                                              ≈⟨ sym-assoc ⟩
      (unitorˡ.to ∘ unitorˡ.from) ∘ (del ⊗₁ del)
                                              ≈⟨ unitorˡ.isoˡ ⟩∘⟨refl ⟩
      id ∘ (del ⊗₁ del)                       ≈⟨ identityˡ ⟩
      del ⊗₁ del                              ∎

------------------------------------------------------------------------
-- 3b. Shuffle infrastructure.
--
-- `shuffle : (X⊗X) ⊗ (Y⊗Y) → (X⊗Y) ⊗ (X⊗Y)` (defined in `Categories.Markov`)
-- is the structural morphism that swaps the middle two factors of a
-- four-fold product.  Closure of determinism under `⊗₁` and the
-- determinism of `copy` itself both go through facts about shuffle.

-- `shuffle` is natural at the "duplicated" type — applying `(f ⊗ f)`
-- and `(g ⊗ g)` then shuffling agrees with shuffling then applying
-- `(f ⊗ g) ⊗ (f ⊗ g)`.  (This is the restricted form of the standard
-- categorical four-shuffle naturality; restricted because our
-- `shuffle` has type `(X⊗X) ⊗ (Y⊗Y) → (X⊗Y) ⊗ (X⊗Y)` with both
-- factors duplicated, matching the shape needed by `copy-⊗`.)
--
-- The structural steps are explicit `assoc` / `sym-assoc` rewrites;
-- the substantive steps in between are α-naturality, B-naturality,
-- and the inner Markov lemmas.  Earlier versions used
-- `Categories.Tactic.Category.solve` for the assoc-chains but the
-- reflection-based normalisation made this file ~2× slower to check;
-- since each `solve` invocation here was just one or two `assoc`s,
-- inlining them is both faster and more obvious to read.
-- `Categories.MonoidalCoherence.Solver` doesn't apply because the
-- equations mix structural morphisms with named ones (`f, g, inner`,
-- `copy`) — the universal coherence theorem requires the solver to
-- run with `mor = ⊥`, no variable morphisms.

shuffle-natural : {f : X ⇒ X'} {g : Y ⇒ Y'}
                → shuffle symmetric ∘ ((f ⊗₁ f) ⊗₁ (g ⊗₁ g))
                ≈ ((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ shuffle symmetric
shuffle-natural {f = f} {g} = begin
  (associator.to ∘ (id ⊗₁ inner) ∘ associator.from)
    ∘ ((f ⊗₁ f) ⊗₁ (g ⊗₁ g))
    ≈⟨ assoc ⟩
  associator.to ∘ ((id ⊗₁ inner) ∘ associator.from)
    ∘ ((f ⊗₁ f) ⊗₁ (g ⊗₁ g))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  associator.to ∘ (id ⊗₁ inner)
    ∘ (associator.from ∘ ((f ⊗₁ f) ⊗₁ (g ⊗₁ g)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  associator.to ∘ (id ⊗₁ inner)
    ∘ ((f ⊗₁ (f ⊗₁ (g ⊗₁ g))) ∘ associator.from)
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  associator.to ∘ ((id ⊗₁ inner) ∘ (f ⊗₁ (f ⊗₁ (g ⊗₁ g))))
    ∘ associator.from
    ≈⟨ refl⟩∘⟨ inner-on-right ⟩∘⟨refl ⟩
  associator.to ∘ ((f ⊗₁ (g ⊗₁ (f ⊗₁ g))) ∘ (id ⊗₁ inner))
    ∘ associator.from
    ≈⟨ sym-assoc ⟩
  (associator.to ∘ ((f ⊗₁ (g ⊗₁ (f ⊗₁ g))) ∘ (id ⊗₁ inner)))
    ∘ associator.from
    ≈⟨ sym-assoc ⟩∘⟨refl ⟩
  ((associator.to ∘ (f ⊗₁ (g ⊗₁ (f ⊗₁ g)))) ∘ (id ⊗₁ inner))
    ∘ associator.from
    ≈⟨ assoc ⟩
  (associator.to ∘ (f ⊗₁ (g ⊗₁ (f ⊗₁ g))))
    ∘ ((id ⊗₁ inner) ∘ associator.from)
    ≈⟨ assoc-commute-to ⟩∘⟨refl ⟩
  (((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ associator.to)
    ∘ ((id ⊗₁ inner) ∘ associator.from)
    ≈⟨ assoc ⟩
  ((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ (associator.to ∘ (id ⊗₁ inner) ∘ associator.from) ∎
  where
    -- The "middle" of shuffle:  `α⇐ ∘ (B ⊗ id) ∘ α⇒`.
    inner : A ⊗₀ (B ⊗₀ C) ⇒ B ⊗₀ (A ⊗₀ C)
    inner = associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to

    -- inner is natural: by α-naturality + B-naturality + α-naturality.
    inner-natural : {p : A ⇒ A'} {q : B ⇒ B'} {r : C ⇒ C'}
                  → inner ∘ (p ⊗₁ (q ⊗₁ r)) ≈ (q ⊗₁ (p ⊗₁ r)) ∘ inner
    inner-natural {p = p} {q} {r} = begin
      (associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to)
        ∘ (p ⊗₁ (q ⊗₁ r))
        ≈⟨ assoc ⟩
      associator.from ∘ ((braiding.⇒.η _ ⊗₁ id) ∘ associator.to)
        ∘ (p ⊗₁ (q ⊗₁ r))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      associator.from ∘ (braiding.⇒.η _ ⊗₁ id)
        ∘ (associator.to ∘ (p ⊗₁ (q ⊗₁ r)))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to ⟩
      associator.from ∘ (braiding.⇒.η _ ⊗₁ id)
        ∘ (((p ⊗₁ q) ⊗₁ r) ∘ associator.to)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      associator.from ∘ ((braiding.⇒.η _ ⊗₁ id) ∘ ((p ⊗₁ q) ⊗₁ r))
        ∘ associator.to
        ≈⟨ refl⟩∘⟨ B⊗id-natural ⟩∘⟨refl ⟩
      associator.from ∘ (((q ⊗₁ p) ⊗₁ r) ∘ (braiding.⇒.η _ ⊗₁ id))
        ∘ associator.to
        ≈⟨ sym-assoc ⟩
      (associator.from ∘ (((q ⊗₁ p) ⊗₁ r) ∘ (braiding.⇒.η _ ⊗₁ id)))
        ∘ associator.to
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((associator.from ∘ ((q ⊗₁ p) ⊗₁ r)) ∘ (braiding.⇒.η _ ⊗₁ id))
        ∘ associator.to
        ≈⟨ assoc ⟩
      (associator.from ∘ ((q ⊗₁ p) ⊗₁ r))
        ∘ ((braiding.⇒.η _ ⊗₁ id) ∘ associator.to)
        ≈⟨ assoc-commute-from ⟩∘⟨refl ⟩
      ((q ⊗₁ (p ⊗₁ r)) ∘ associator.from)
        ∘ ((braiding.⇒.η _ ⊗₁ id) ∘ associator.to)
        ≈⟨ assoc ⟩
      (q ⊗₁ (p ⊗₁ r)) ∘ (associator.from
        ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to) ∎
      where
        -- `(B ⊗ id) ∘ ((p ⊗ q) ⊗ r) ≈ ((q ⊗ p) ⊗ r) ∘ (B ⊗ id)`:
        -- naturality of B in the first factor.
        B⊗id-natural :
          (braiding.⇒.η _ ⊗₁ id) ∘ ((p ⊗₁ q) ⊗₁ r)
          ≈ ((q ⊗₁ p) ⊗₁ r) ∘ (braiding.⇒.η _ ⊗₁ id)
        B⊗id-natural = begin
          (braiding.⇒.η _ ⊗₁ id) ∘ ((p ⊗₁ q) ⊗₁ r)
            ≈˘⟨ ⊗-distrib-over-∘ ⟩
          ((braiding.⇒.η _ ∘ (p ⊗₁ q)) ⊗₁ (id ∘ r))
            ≈⟨ braiding.⇒.commute (p , q) ⟩⊗⟨ (trans identityˡ (sym identityʳ)) ⟩
          (((q ⊗₁ p) ∘ braiding.⇒.η _) ⊗₁ (r ∘ id))
            ≈⟨ ⊗-distrib-over-∘ ⟩
          ((q ⊗₁ p) ⊗₁ r) ∘ (braiding.⇒.η _ ⊗₁ id) ∎

    -- (id ⊗ inner) ∘ (f ⊗ (f ⊗ (g ⊗ g))) ≈ (f ⊗ (g ⊗ (f ⊗ g))) ∘ (id ⊗ inner).
    -- Reduces to inner-natural under the `id ⊗ _` wrapping.
    inner-on-right :
      (id ⊗₁ inner) ∘ (f ⊗₁ (f ⊗₁ (g ⊗₁ g)))
      ≈ (f ⊗₁ (g ⊗₁ (f ⊗₁ g))) ∘ (id ⊗₁ inner)
    inner-on-right = begin
      (id ⊗₁ inner) ∘ (f ⊗₁ (f ⊗₁ (g ⊗₁ g)))
        ≈˘⟨ ⊗-distrib-over-∘ ⟩
      (id ∘ f) ⊗₁ (inner ∘ (f ⊗₁ (g ⊗₁ g)))
        ≈⟨ (trans identityˡ (sym identityʳ)) ⟩⊗⟨ inner-natural ⟩
      (f ∘ id) ⊗₁ ((g ⊗₁ (f ⊗₁ g)) ∘ inner)
        ≈⟨ ⊗-distrib-over-∘ ⟩
      (f ⊗₁ (g ⊗₁ (f ⊗₁ g))) ∘ (id ⊗₁ inner) ∎

private
  4-copy-R : X ⇒ X ⊗₀ (X ⊗₀ (X ⊗₀ X))
  4-copy-R = (id ⊗₁ ((id ⊗₁ copy) ∘ copy)) ∘ copy

  α-from-4-copy : associator.from ∘ ((copy ⊗₁ copy) ∘ copy) ≈ 4-copy-R {X}
  α-from-4-copy = begin
    associator.from ∘ ((copy ⊗₁ copy) ∘ copy)
      ≈⟨ refl⟩∘⟨ (sym-decomp ⟩∘⟨refl) ⟩
    associator.from ∘ (((id ⊗₁ copy) ∘ (copy ⊗₁ id)) ∘ copy)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    associator.from ∘ ((id ⊗₁ copy) ∘ ((copy ⊗₁ id) ∘ copy))
      ≈⟨ sym-assoc ⟩
    (associator.from ∘ (id ⊗₁ copy)) ∘ ((copy ⊗₁ id) ∘ copy)
      ≈⟨ α-past-id-copy ⟩∘⟨refl ⟩
    ((id ⊗₁ (id ⊗₁ copy)) ∘ associator.from) ∘ ((copy ⊗₁ id) ∘ copy)
      ≈⟨ assoc ⟩
    (id ⊗₁ (id ⊗₁ copy)) ∘ (associator.from ∘ ((copy ⊗₁ id) ∘ copy))
      ≈⟨ refl⟩∘⟨ coassoc ⟩
    (id ⊗₁ (id ⊗₁ copy)) ∘ ((id ⊗₁ copy) ∘ copy)
      ≈⟨ sym-assoc ⟩
    ((id ⊗₁ (id ⊗₁ copy)) ∘ (id ⊗₁ copy)) ∘ copy
      ≈˘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((id ∘ id) ⊗₁ ((id ⊗₁ copy) ∘ copy)) ∘ copy
      ≈⟨ (identityˡ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    (id ⊗₁ ((id ⊗₁ copy) ∘ copy)) ∘ copy ∎
    where
      sym-decomp : copy ⊗₁ copy ≈ (id ⊗₁ copy) ∘ (copy ⊗₁ id)
      sym-decomp = begin
        copy ⊗₁ copy                  ≈˘⟨ identityˡ ⟩⊗⟨ identityʳ ⟩
        (id ∘ copy) ⊗₁ (copy ∘ id)    ≈⟨ ⊗-distrib-over-∘ ⟩
        (id ⊗₁ copy) ∘ (copy ⊗₁ id)   ∎

      α-past-id-copy : associator.from ∘ (id ⊗₁ copy) ≈ (id ⊗₁ (id ⊗₁ copy)) ∘ associator.from
      α-past-id-copy = begin
        associator.from ∘ (id ⊗₁ copy)
          ≈˘⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩
        associator.from ∘ ((id ⊗₁ id) ⊗₁ copy)
          ≈⟨ assoc-commute-from ⟩
        (id ⊗₁ (id ⊗₁ copy)) ∘ associator.from ∎

  inner-fixes-3-copy :
      (associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to) ∘ ((id ⊗₁ copy) ∘ copy)
    ≈ (id ⊗₁ copy {X}) ∘ copy {X}
  inner-fixes-3-copy {X} = begin
    (associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to) ∘ ((id ⊗₁ copy) ∘ copy)
      ≈⟨ assoc ⟩
    associator.from ∘ ((braiding.⇒.η _ ⊗₁ id) ∘ associator.to) ∘ ((id ⊗₁ copy) ∘ copy)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ (associator.to ∘ ((id ⊗₁ copy) ∘ copy))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-to-on-3-copy ⟩
    associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ ((copy ⊗₁ id) ∘ copy)
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    associator.from ∘ (((braiding.⇒.η _ ⊗₁ id) ∘ (copy ⊗₁ id)) ∘ copy)
      ≈˘⟨ refl⟩∘⟨ (⊗-distrib-over-∘ ⟩∘⟨refl) ⟩
    associator.from ∘ (((braiding.⇒.η _ ∘ copy) ⊗₁ (id ∘ id)) ∘ copy)
      ≈⟨ refl⟩∘⟨ ((cocomm ⟩⊗⟨ identityˡ) ⟩∘⟨refl) ⟩
    associator.from ∘ ((copy ⊗₁ id) ∘ copy)
      ≈⟨ coassoc ⟩
    (id ⊗₁ copy) ∘ copy ∎
    where
      α-to-on-3-copy : associator.to ∘ ((id ⊗₁ copy) ∘ copy) ≈ (copy ⊗₁ id) ∘ copy
      α-to-on-3-copy = begin
        associator.to ∘ ((id ⊗₁ copy) ∘ copy)
          ≈˘⟨ refl⟩∘⟨ coassoc ⟩
        associator.to ∘ (associator.from ∘ ((copy ⊗₁ id) ∘ copy))
          ≈⟨ MR.Cancellers.cancelˡ 𝒞 associator.isoˡ ⟩
        (copy ⊗₁ id) ∘ copy ∎

  shuffle-on-4-copy : shuffle symmetric ∘ ((copy ⊗₁ copy) ∘ copy) ≈ (copy ⊗₁ copy) ∘ copy {X}
  shuffle-on-4-copy = begin
    (associator.to ∘ (id ⊗₁ inner-fn) ∘ associator.from) ∘ ((copy ⊗₁ copy) ∘ copy)
      ≈⟨ assoc ⟩
    associator.to ∘ ((id ⊗₁ inner-fn) ∘ associator.from) ∘ ((copy ⊗₁ copy) ∘ copy)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    associator.to ∘ (id ⊗₁ inner-fn) ∘ (associator.from ∘ ((copy ⊗₁ copy) ∘ copy))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-from-4-copy ⟩
    associator.to ∘ (id ⊗₁ inner-fn) ∘ ((id ⊗₁ ((id ⊗₁ copy) ∘ copy)) ∘ copy)
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    associator.to ∘ ((id ⊗₁ inner-fn) ∘ (id ⊗₁ ((id ⊗₁ copy) ∘ copy))) ∘ copy
      ≈˘⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    associator.to ∘ ((id ∘ id) ⊗₁ (inner-fn ∘ ((id ⊗₁ copy) ∘ copy))) ∘ copy
      ≈⟨ refl⟩∘⟨ (identityˡ ⟩⊗⟨ inner-fixes-3-copy) ⟩∘⟨refl ⟩
    associator.to ∘ (id ⊗₁ ((id ⊗₁ copy) ∘ copy)) ∘ copy
      ≈˘⟨ refl⟩∘⟨ α-from-4-copy ⟩
    associator.to ∘ (associator.from ∘ ((copy ⊗₁ copy) ∘ copy))
      ≈⟨ MR.Cancellers.cancelˡ 𝒞 associator.isoˡ ⟩
    (copy ⊗₁ copy) ∘ copy ∎
    where
      inner-fn : A ⊗₀ (B ⊗₀ C) ⇒ B ⊗₀ (A ⊗₀ C)
      inner-fn = associator.from ∘ (braiding.⇒.η _ ⊗₁ id) ∘ associator.to

copy-det : IsDeterministic (copy {X})
copy-det = begin
  copy ∘ copy                                 ≈⟨ copy-⊗ ⟩∘⟨refl ⟩
  (shuffle symmetric ∘ (copy ⊗₁ copy)) ∘ copy ≈⟨ assoc ⟩
  shuffle symmetric ∘ ((copy ⊗₁ copy) ∘ copy) ≈⟨ shuffle-on-4-copy ⟩
  (copy ⊗₁ copy) ∘ copy                       ∎

⊗₁-det : {f : X ⇒ Y} {g : X' ⇒ Y'} → IsDeterministic f → IsDeterministic g → IsDeterministic (f ⊗₁ g)
⊗₁-det {f = f} {g} fd gd = begin
  copy ∘ (f ⊗₁ g)
    ≈⟨ copy-⊗ ⟩∘⟨refl ⟩
  (shuffle symmetric ∘ (copy ⊗₁ copy)) ∘ (f ⊗₁ g)
    ≈⟨ assoc ⟩
  shuffle symmetric ∘ ((copy ⊗₁ copy) ∘ (f ⊗₁ g))
    ≈˘⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩
  shuffle symmetric ∘ ((copy ∘ f) ⊗₁ (copy ∘ g))
    ≈⟨ refl⟩∘⟨ (fd ⟩⊗⟨ gd) ⟩
  shuffle symmetric ∘ (((f ⊗₁ f) ∘ copy) ⊗₁ ((g ⊗₁ g) ∘ copy))
    ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩
  shuffle symmetric ∘ (((f ⊗₁ f) ⊗₁ (g ⊗₁ g)) ∘ (copy ⊗₁ copy))
    ≈⟨ sym-assoc ⟩
  (shuffle symmetric ∘ ((f ⊗₁ f) ⊗₁ (g ⊗₁ g))) ∘ (copy ⊗₁ copy)
    ≈⟨ shuffle-natural ⟩∘⟨refl ⟩
  (((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ shuffle symmetric) ∘ (copy ⊗₁ copy)
    ≈⟨ assoc ⟩
  ((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ (shuffle symmetric ∘ (copy ⊗₁ copy))
    ≈˘⟨ refl⟩∘⟨ copy-⊗ ⟩
  ((f ⊗₁ g) ⊗₁ (f ⊗₁ g)) ∘ copy ∎

------------------------------------------------------------------------
-- 4. Marginals (projections).

fstᴹ : X ⊗₀ Y ⇒ X
fstᴹ = unitorʳ.from ∘ (id ⊗₁ del)

sndᴹ : X ⊗₀ Y ⇒ Y
sndᴹ = unitorˡ.from ∘ (del ⊗₁ id)

------------------------------------------------------------------------
-- 5. Joints from pairs of kernels.

⟨_,_⟩ᴹ : X ⇒ Y → X ⇒ Z → X ⇒ Y ⊗₀ Z
⟨ f , g ⟩ᴹ = (f ⊗₁ g) ∘ copy

private
  discard-r : (f : X ⇒ Y) (g : X ⇒ Z)
    → (id ⊗₁ del) ∘ ((f ⊗₁ g) ∘ copy) ≈ (f ⊗₁ id) ∘ ((id ⊗₁ del) ∘ copy)
  discard-r f g = begin
    (id ⊗₁ del) ∘ ((f ⊗₁ g) ∘ copy)        ≈⟨ sym-assoc ⟩
    ((id ⊗₁ del) ∘ (f ⊗₁ g)) ∘ copy        ≈˘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((id ∘ f) ⊗₁ (del ∘ g)) ∘ copy         ≈⟨ (identityˡ ⟩⊗⟨ discard-natural g) ⟩∘⟨refl ⟩
    (f ⊗₁ del) ∘ copy                      ≈˘⟨ (identityʳ ⟩⊗⟨ identityˡ) ⟩∘⟨refl ⟩
    ((f ∘ id) ⊗₁ (id ∘ del)) ∘ copy        ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((f ⊗₁ id) ∘ (id ⊗₁ del)) ∘ copy       ≈⟨ assoc ⟩
    (f ⊗₁ id) ∘ ((id ⊗₁ del) ∘ copy)       ∎

  discard-l : (f : X ⇒ Y) (g : X ⇒ Z)
    → (del ⊗₁ id) ∘ ((f ⊗₁ g) ∘ copy) ≈ (id ⊗₁ g) ∘ ((del ⊗₁ id) ∘ copy)
  discard-l f g = begin
    (del ⊗₁ id) ∘ ((f ⊗₁ g) ∘ copy)        ≈⟨ sym-assoc ⟩
    ((del ⊗₁ id) ∘ (f ⊗₁ g)) ∘ copy        ≈˘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((del ∘ f) ⊗₁ (id ∘ g)) ∘ copy         ≈⟨ (discard-natural f ⟩⊗⟨ identityˡ) ⟩∘⟨refl ⟩
    (del ⊗₁ g) ∘ copy                      ≈˘⟨ (identityˡ ⟩⊗⟨ identityʳ) ⟩∘⟨refl ⟩
    ((id ∘ del) ⊗₁ (g ∘ id)) ∘ copy        ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
    ((id ⊗₁ g) ∘ (del ⊗₁ id)) ∘ copy       ≈⟨ assoc ⟩
    (id ⊗₁ g) ∘ ((del ⊗₁ id) ∘ copy)       ∎

fst-⟨,⟩ : (f : X ⇒ Y) (g : X ⇒ Z) → fstᴹ ∘ ⟨ f , g ⟩ᴹ ≈ f
fst-⟨,⟩ f g = begin
  (unitorʳ.from ∘ (id ⊗₁ del)) ∘ ((f ⊗₁ g) ∘ copy)  ≈⟨ assoc ⟩
  unitorʳ.from ∘ ((id ⊗₁ del) ∘ ((f ⊗₁ g) ∘ copy))  ≈⟨ refl⟩∘⟨ discard-r f g ⟩
  unitorʳ.from ∘ ((f ⊗₁ id) ∘ ((id ⊗₁ del) ∘ copy)) ≈⟨ sym-assoc ⟩
  (unitorʳ.from ∘ (f ⊗₁ id)) ∘ ((id ⊗₁ del) ∘ copy) ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
  (f ∘ unitorʳ.from) ∘ ((id ⊗₁ del) ∘ copy)         ≈⟨ assoc ⟩
  f ∘ (unitorʳ.from ∘ ((id ⊗₁ del) ∘ copy))         ≈⟨ refl⟩∘⟨ counit-r ⟩
  f ∘ id                                             ≈⟨ identityʳ ⟩
  f                                                  ∎

snd-⟨,⟩ : (f : X ⇒ Y) (g : X ⇒ Z) → sndᴹ ∘ ⟨ f , g ⟩ᴹ ≈ g
snd-⟨,⟩ f g = begin
  (unitorˡ.from ∘ (del ⊗₁ id)) ∘ ((f ⊗₁ g) ∘ copy)  ≈⟨ assoc ⟩
  unitorˡ.from ∘ ((del ⊗₁ id) ∘ ((f ⊗₁ g) ∘ copy))  ≈⟨ refl⟩∘⟨ discard-l f g ⟩
  unitorˡ.from ∘ ((id ⊗₁ g) ∘ ((del ⊗₁ id) ∘ copy)) ≈⟨ sym-assoc ⟩
  (unitorˡ.from ∘ (id ⊗₁ g)) ∘ ((del ⊗₁ id) ∘ copy) ≈⟨ unitorˡ-commute-from ⟩∘⟨refl ⟩
  (g ∘ unitorˡ.from) ∘ ((del ⊗₁ id) ∘ copy)         ≈⟨ assoc ⟩
  g ∘ (unitorˡ.from ∘ ((del ⊗₁ id) ∘ copy))          ≈⟨ refl⟩∘⟨ counit-l ⟩
  g ∘ id                                             ≈⟨ identityʳ ⟩
  g                                                  ∎

braiding-on-joint : (f : X ⇒ Y) (g : X ⇒ Z) → braiding.⇒.η _ ∘ ⟨ f , g ⟩ᴹ ≈ ⟨ g , f ⟩ᴹ
braiding-on-joint f g = begin
  braiding.⇒.η _ ∘ ((f ⊗₁ g) ∘ copy) ≈⟨ sym-assoc ⟩
  (braiding.⇒.η _ ∘ (f ⊗₁ g)) ∘ copy ≈⟨ braiding.⇒.commute (f , g) ⟩∘⟨refl ⟩
  ((g ⊗₁ f) ∘ braiding.⇒.η _) ∘ copy ≈⟨ assoc ⟩
  (g ⊗₁ f) ∘ (braiding.⇒.η _ ∘ copy) ≈⟨ refl⟩∘⟨ cocomm ⟩
  (g ⊗₁ f) ∘ copy                    ∎

⟨,⟩-cong : {f f' : X ⇒ Y} {g g' : X ⇒ Z} → f ≈ f' → g ≈ g' → ⟨ f , g ⟩ᴹ ≈ ⟨ f' , g' ⟩ᴹ
⟨,⟩-cong {f = f} {f'} {g} {g'} f≈f' g≈g' = begin
  (f ⊗₁ g) ∘ copy   ≈⟨ (f≈f' ⟩⊗⟨ g≈g') ⟩∘⟨refl ⟩
  (f' ⊗₁ g') ∘ copy ∎

------------------------------------------------------------------------
-- 6. Almost-sure equality.

_≈ᵃˢ[_]_ : (f : X ⇒ Y) (p : unit ⇒ X) (g : X ⇒ Y) → Set e
f ≈ᵃˢ[ p ] g = (id ⊗₁ f) ∘ copy ∘ p ≈ (id ⊗₁ g) ∘ copy ∘ p

≈ᵃˢ-refl : {p : unit ⇒ X} {f : X ⇒ Y} → f ≈ᵃˢ[ p ] f
≈ᵃˢ-refl = refl

≈ᵃˢ-sym : {p : unit ⇒ X} {f g : X ⇒ Y} → f ≈ᵃˢ[ p ] g → g ≈ᵃˢ[ p ] f
≈ᵃˢ-sym eq = sym eq

≈ᵃˢ-trans : {p : unit ⇒ X} {f g h : X ⇒ Y} → f ≈ᵃˢ[ p ] g → g ≈ᵃˢ[ p ] h → f ≈ᵃˢ[ p ] h
≈ᵃˢ-trans eq₁ eq₂ = trans eq₁ eq₂

≈⇒≈ᵃˢ : {p : unit ⇒ X} {f g : X ⇒ Y} → f ≈ g → f ≈ᵃˢ[ p ] g
≈⇒≈ᵃˢ f≈g = refl⟩⊗⟨ f≈g ⟩∘⟨refl

------------------------------------------------------------------------
-- 7. Conditionals

IsConditional : (ψ : unit ⇒ X ⊗₀ Y) (f : X ⇒ Y) → Set e
IsConditional ψ f = ⟨ id , f ⟩ᴹ ∘ (fstᴹ ∘ ψ) ≈ ψ

HasConditionals : Set (o ⊔ ℓ ⊔ e)
HasConditionals = ∀ {X Y} → (ψ : unit ⇒ X ⊗₀ Y) → ∃[ f ] IsConditional ψ f

------------------------------------------------------------------------
-- 8. Bayesian inversion

IsBayesianInverse : (p : unit ⇒ X) (f : X ⇒ Y) (f† : Y ⇒ X) → Set e
IsBayesianInverse p f f† = ⟨ f† , id ⟩ᴹ ∘ (f ∘ p) ≈ ⟨ id , f ⟩ᴹ ∘ p

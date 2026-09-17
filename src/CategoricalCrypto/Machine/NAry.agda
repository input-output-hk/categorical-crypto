{-# OPTIONS --safe #-}

-- ============================================================================
-- Rewiring a ⨂ of per-node Kleisli machines past a shared environment.
--
-- `insert-id`, `⨂-reshape-env` and `⨂-absorb-env` are the rewirings a
-- UC-style transfer argument would need when the per-node protocol machines
-- are tensored with `⨂ᴷ` and composed with an environment, and all three are
-- derived from the binary laws of `Machine.Monoidal`.  No such argument exists
-- in this tree yet, so all three are currently unused outside this module.
--
-- Elaboration note.  Channel families must be PINNED wherever `⨂` appears in
-- an inferred position (hence `strip`, and the explicit `{n} {E₁} {E₂}` on
-- `⨂-zip` below).  Left implicit they generate `⨂ ?B ≟ ⨂ E` constraints that
-- block on an abstract `n` — `⨂` is a stuck recursion, not a constructor, so
-- Agda cannot invert it — and the elaborator then diverges into heap
-- exhaustion.  For the same reason the reasoning steps are stated over
-- abstract machines (`slide-∘ᴷ`, `slide-⊗ᴷ`, `post-α`) and only afterwards
-- instantiated at the ⨂ composites.
-- ============================================================================

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal
open import Tactic.Defaults

module CategoricalCrypto.Machine.NAry where

private variable A B C D E E₁ E₂ : Channel

insert-id-helper : ∀ {n} (C : Fin n → Channel)
  → Machine (A ⊗₀ B ⊗₀ (⨂ (λ k → C k ⊗₀ I))) (A ⊗₀ B ⊗₀ (⨂ C))
insert-id-helper {n = n} _ = CC.id ⊗₁ CC.id ⊗₁ ⨂₁ {n = n} (λ _ → ρ⇒)

-- The same with an arbitrary per-node forwarder `u` in place of `ρ⇒`; the
-- channel families are pinned, see the elaboration note above.
⨂-reshape-env-helper : ∀ {n} {E₂' E₂ : Fin n → Channel}
  (u : (k : Fin n) → Machine (E₂' k) (E₂ k))
  → Machine (A ⊗₀ B ⊗₀ ⨂ E₂') (A ⊗₀ B ⊗₀ ⨂ E₂)
⨂-reshape-env-helper {n = n} {E₂' = E₂'} {E₂ = E₂} u = CC.id ⊗₁ CC.id ⊗₁ ⨂₁ {n} {E₂'} {E₂} u

-- The n-ary interchange ("zip"): two parallel ⨂s of channels become one ⨂ of
-- pairs.  This is the only part of `⨂-absorb-env-helper` below that needs
-- induction — everything else is a fixed permutation of four channel atoms,
-- which `⇒-solver` builds.  At each step the head channels are pulled together
-- and the tails are zipped recursively.
⨂-zip : ∀ {n} {F₁ F₂ : Fin n → Channel}
      → Machine (⨂ F₁ ⊗₀ ⨂ F₂) (⨂ (λ k → F₁ k ⊗₀ F₂ k))
⨂-zip {zero}            = λ⇒
⨂-zip {suc n} {F₁} {F₂} =
  (CC.id ⊗₁ ⨂-zip {n} {λ k → F₁ (fsuc k)} {λ k → F₂ (fsuc k)}) ∘ mid4

-- Rewiring the per-node environment channels past the shared environment `E`:
-- the `⨂ E₂` that composition strands on the left is carried across and zipped
-- onto the `⨂ E₁` on the right.
⨂-absorb-env-helper : ∀ {n} {E : Channel} (D : Fin n → Channel) {E₁ E₂ : Fin n → Channel}
  → Machine ((⨂ D ⊗₀ ⨂ E₂) ⊗₀ E ⊗₀ (⨂ E₁)) ((⨂ D) ⊗₀ E ⊗₀ (⨂ (λ k → E₁ k ⊗₀ E₂ k)))
⨂-absorb-env-helper {n} {E} D {E₁} {E₂} =
  (CC.id ⊗₁ CC.id ⊗₁ ⨂-zip {n} {E₁} {E₂}) ∘ absorb-regroup

∘ᴷ-unfold : ∀ {A B C E₁ E₂} (M₂ : Machine B (C ⊗₀ E₂)) (M₁ : Machine A (B ⊗₀ E₁))
          → (M₂ ∘ᴷ M₁) ≡ (∘ᴷ-fwd CC.∘ ((M₂ ⊗ʳ E₁) CC.∘ M₁))
∘ᴷ-unfold _ _ = refl

⊗ᴷ-unfold : ∀ {A₁ B₁ E₁ A₂ B₂ E₂} (M₁ : Machine A₁ (B₁ ⊗₀ E₁)) (M₂ : Machine A₂ (B₂ ⊗₀ E₂))
          → (M₁ ⊗ᴷ M₂) ≡ (⊗ᴷ-fwd CC.∘ (M₁ ⊗₁ M₂))
⊗ᴷ-unfold _ _ = refl

-- `insert-id-helper`'s inner `⨂₁ (λ _ → ρ⇒)`, with its channel families
-- PINNED; see the elaboration note in the header.
strip : ∀ {n} (E : Fin n → Channel) → Machine (⨂ (λ k → E k ⊗₀ I)) (⨂ E)
strip {n} E = ⨂₁ {n = n} {A = λ k → E k ⊗₀ I} {B = E} (λ _ → ρ⇒)

module Derived where

  -- Inserting a unit with `idᴷ ∘ᴷ _` and stripping it again is a no-op.
  unit-∘ᴷ : ∀ {A C E₁} (h : Machine A (C ⊗₀ E₁))
          → ((CC.id ⊗₁ ρ⇒) CC.∘ (idᴷ ∘ᴷ h)) ≅ᴹ h
  unit-∘ᴷ h =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ ρ-∘ᴷ-fwd ≅ᴹ-refl)
    (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-sym (⊗₁-interchange idᴷ ρ⇒ CC.id CC.id)) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ ρ-idᴷ ∘-identityˡ-≅ᴹ) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl)
              ∘-identityˡ-≅ᴹ)))))

  -- If each `f' k` is `f k` up to a forwarder `u k` on its environment channel,
  -- then `⨂₁ u` turns `⨂ᴷ f'` into `⨂ᴷ f`.  The proof is by induction on
  -- `n`, the step being `⊗ᴷ-fwd`'s naturality together with the interchange
  -- law.  The channel families are pinned, see the elaboration note in the
  -- header.
  ⨂-post : ∀ {n} {B C E₂ E₂' : Fin n → Channel}
           (f  : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k))
           (f' : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂' k))
           (u  : (k : Fin n) → Machine (E₂' k) (E₂ k))
         → (∀ k → ((CC.id ⊗₁ u k) CC.∘ f' k) ≅ᴹ f k)
         → ((CC.id ⊗₁ ⨂₁ {n} {E₂'} {E₂} u) CC.∘ ⨂ᴷ f') ≅ᴹ ⨂ᴷ f
  ⨂-post {zero}  f f' u eq = ≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl) ∘-identityˡ-≅ᴹ
  ⨂-post {suc n} {E₂ = E₂} {E₂' = E₂'} f f' u eq =
    ≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ (≅ᴹ-sym ⊗₁-id) ≅ᴹ-refl) ≅ᴹ-refl)
    (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗ᴷ-fwd-natural CC.id (u fzero) CC.id
                            (⨂₁ {n} {λ k → E₂' (fsuc k)} {λ k → E₂ (fsuc k)} (λ k → u (fsuc k))))
                         ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange _ _ _ _))
                          (⊗₁-resp-≅ᴹ (eq fzero)
                                      (⨂-post (λ k → f (fsuc k)) (λ k → f' (fsuc k))
                                              (λ k → u (fsuc k)) (λ k → eq (fsuc k)))))))))

  -- `insert-id-helper` undoes the per-node unit insertion: the instance
  -- `u = λ _ → ρ⇒`.
  ⨂-unit : ∀ {n} {B C E₂ : Fin n → Channel}
           (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k))
         → ((CC.id ⊗₁ strip E₂) CC.∘ ⨂ᴷ (λ k → idᴷ ∘ᴷ f k)) ≅ᴹ ⨂ᴷ f
  ⨂-unit f = ⨂-post f (λ k → idᴷ ∘ᴷ f k) (λ _ → ρ⇒) (λ k → unit-∘ᴷ (f k))

  -- Sliding a post-composed `CC.id ⊗₁ u` through `_∘ᴷ g`.  Stated over abstract
  -- machines: instantiating it at the ⨂ composites is then cheap, whereas
  -- inlining the same chain at those types is not.
  slide-∘ᴷ : ∀ {A B C E₁ E₂ E₂'}
             (F : Machine B (C ⊗₀ E₂)) (F' : Machine B (C ⊗₀ E₂'))
             (u : Machine E₂' E₂) (g : Machine A (B ⊗₀ E₁))
           → ((CC.id ⊗₁ u) CC.∘ F') ≅ᴹ F
           → ((CC.id ⊗₁ (CC.id ⊗₁ u)) CC.∘ (F' ∘ᴷ g)) ≅ᴹ (F ∘ᴷ g)
  slide-∘ᴷ F F' u g eq =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (∘ᴷ-fwd-natural CC.id CC.id u) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
                  (∘-resp-≅ᴹ
                    (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange F' (CC.id ⊗₁ u) CC.id CC.id))
                              (⊗₁-resp-≅ᴹ eq ∘-identityˡ-≅ᴹ))
                    ≅ᴹ-refl)))))

  -- Re-bracketing the outer `α`, again over abstract machines.
  post-α : ∀ {A X Y D} (α : Machine Y D) (H : Machine X Y)
             (P : Machine A X) (Q : Machine A Y)
         → (H CC.∘ P) ≅ᴹ Q → (α CC.∘ Q) ≅ᴹ ((α CC.∘ H) CC.∘ P)
  post-α α H P Q eq = ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym eq)) (≅ᴹ-sym ∘-assoc-≅ᴹ)

  insert-id : ∀ {A D} {n} {E₁} {B C E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k)) (g : Machine A (⨂ B ⊗₀ E₁))
    (α : Machine (⨂ C ⊗₀ E₁ ⊗₀ ⨂ E₂) D)
    → (α CC.∘ (⨂ᴷ f ∘ᴷ g))
      ≅ᴹ ((α CC.∘ insert-id-helper E₂) CC.∘ (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g))
  insert-id {E₂ = E₂} f g α =
    post-α α (insert-id-helper E₂)
             (⨂ᴷ (λ k → idᴷ ∘ᴷ f k) ∘ᴷ g)
             (⨂ᴷ f ∘ᴷ g)
             (slide-∘ᴷ (⨂ᴷ f) (⨂ᴷ (λ k → idᴷ ∘ᴷ f k)) (strip E₂) g (⨂-unit f))

  -- `insert-id` for an arbitrary per-node reshaping of the environment
  -- channels: a `⨂ᴷ` of machines that agree up to forwarders `u k` on their
  -- environment channels can be swapped under `α ∘ (_ ∘ᴷ g)` at the price of
  -- `⨂₁ u` next to `α`.
  ⨂-reshape-env : ∀ {A D} {n} {E₁} {B C E₂ E₂' : Fin n → Channel}
    (f  : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂ k))
    (f' : (k : Fin n) → Machine (B k) (C k ⊗₀ E₂' k))
    (u  : (k : Fin n) → Machine (E₂' k) (E₂ k))
    → (∀ k → ((CC.id ⊗₁ u k) CC.∘ f' k) ≅ᴹ f k)
    → (g : Machine A (⨂ B ⊗₀ E₁)) (α : Machine (⨂ C ⊗₀ E₁ ⊗₀ ⨂ E₂) D)
    → (α CC.∘ (⨂ᴷ f ∘ᴷ g))
      ≅ᴹ ((α CC.∘ ⨂-reshape-env-helper {n = n} {E₂' = E₂'} {E₂ = E₂} u) CC.∘ (⨂ᴷ f' ∘ᴷ g))
  ⨂-reshape-env {n = n} {E₂ = E₂} {E₂' = E₂'} f f' u eq g α =
    post-α α (⨂-reshape-env-helper {n = n} {E₂' = E₂'} {E₂ = E₂} u)
             (⨂ᴷ f' ∘ᴷ g)
             (⨂ᴷ f ∘ᴷ g)
             (slide-∘ᴷ (⨂ᴷ f) (⨂ᴷ f') (⨂₁ {n} {E₂'} {E₂} u) g (⨂-post f f' u eq))

  slide-⊗ᴷ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂ E₂'}
             (X : Machine A₁ (B₁ ⊗₀ E₁)) (Y : Machine A₂ (B₂ ⊗₀ E₂)) (u : Machine E₂ E₂')
           → ((CC.id ⊗₁ (CC.id ⊗₁ u)) CC.∘ (X ⊗ᴷ Y)) ≅ᴹ (X ⊗ᴷ ((CC.id ⊗₁ u) CC.∘ Y))
  slide-⊗ᴷ X Y u =
    ≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ (≅ᴹ-sym ⊗₁-id) ≅ᴹ-refl) ≅ᴹ-refl) ≅ᴹ-refl)
    (≅ᴹ-trans (∘-resp-≅ᴹ (⊗ᴷ-fwd-natural CC.id CC.id CC.id u) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
              (∘-resp-≅ᴹ ≅ᴹ-refl
                (≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange X (CC.id ⊗₁ CC.id) Y (CC.id ⊗₁ u)))
                          (⊗₁-resp-≅ᴹ (≅ᴹ-trans (∘-resp-≅ᴹ ⊗₁-id ≅ᴹ-refl) ∘-identityˡ-≅ᴹ)
                                      ≅ᴹ-refl))))))

  -- `⨂ᴷ` is functorial for `_∘ᴷ_`, once the per-node environment channels are
  -- zipped together.  The proof is by induction on `n`, the step being the
  -- binary `⊗ᴷ-∘ᴷ`.
  ⨂-functorial : ∀ {n} {B C D E₁ E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k))
    (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k))
    → ((CC.id ⊗₁ ⨂-zip {n} {E₁} {E₂}) CC.∘ (⨂ᴷ f ∘ᴷ ⨂ᴷ g)) ≅ᴹ ⨂ᴷ (λ k → f k ∘ᴷ g k)
  ⨂-functorial {zero}  f g = λ-zip-idᴷ
  ⨂-functorial {suc n} {E₁ = E₁} {E₂ = E₂} f g =
    ≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-trans (⊗₁-resp-≅ᴹ (≅ᴹ-sym ∘-identityˡ-≅ᴹ) ≅ᴹ-refl)
                                  (⊗₁-interchange CC.id CC.id mid4 (CC.id ⊗₁ ⨂-zip)))
                        ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl
                (⊗ᴷ-∘ᴷ (f fzero) (g fzero)
                       (⨂ᴷ (λ k → f (fsuc k))) (⨂ᴷ (λ k → g (fsuc k)))))
    (≅ᴹ-trans (slide-⊗ᴷ (f fzero ∘ᴷ g fzero)
                        (⨂ᴷ (λ k → f (fsuc k)) ∘ᴷ ⨂ᴷ (λ k → g (fsuc k)))
                        (⨂-zip {n} {λ k → E₁ (fsuc k)} {λ k → E₂ (fsuc k)}))
              (⊗ᴷ-resp-≅ᴹ ≅ᴹ-refl
                (⨂-functorial (λ k → f (fsuc k)) (λ k → g (fsuc k)))))))

  ⨂-absorb-env : ∀ {A E F} {n} {B C D E₁ E₂ : Fin n → Channel}
    (f : (k : Fin n) → Machine (C k) (D k ⊗₀ E₂ k))
    (g : (k : Fin n) → Machine (B k) (C k ⊗₀ E₁ k))
    (h : Machine A (⨂ B ⊗₀ E))
    (α : Machine (⨂ D ⊗₀ E ⊗₀ ⨂ (λ k → E₁ k ⊗₀ E₂ k)) F)
    → (α CC.∘ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h))
      ≅ᴹ ((α CC.∘ (⨂-absorb-env-helper D) CC.∘ (⨂ᴷ f ⊗₁ CC.id)) CC.∘ (⨂ᴷ g ∘ᴷ h))
  ⨂-absorb-env {n = n} {D = D} {E₁ = E₁} {E₂ = E₂} f g h α =
    post-α α (⨂-absorb-env-helper D CC.∘ (⨂ᴷ f ⊗₁ CC.id))
             (⨂ᴷ g ∘ᴷ h)
             (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h)
             eq
    where
      eq : ((⨂-absorb-env-helper D CC.∘ (⨂ᴷ f ⊗₁ CC.id)) CC.∘ (⨂ᴷ g ∘ᴷ h))
         ≅ᴹ (⨂ᴷ (λ k → f k ∘ᴷ g k) ∘ᴷ h)
      eq =
        ≅ᴹ-trans (∘-resp-≅ᴹ ∘-assoc-≅ᴹ ≅ᴹ-refl)
        (≅ᴹ-trans ∘-assoc-≅ᴹ
        (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (∘ᴷ-assoc (⨂ᴷ f) (⨂ᴷ g) h))
                  (slide-∘ᴷ (⨂ᴷ (λ k → f k ∘ᴷ g k)) (⨂ᴷ f ∘ᴷ ⨂ᴷ g)
                            (⨂-zip {n} {E₁} {E₂}) h (⨂-functorial f g))))

-- The module's intended public surface, for transfer arguments that this tree
-- does not yet contain.
open Derived public using (unit-∘ᴷ; insert-id; ⨂-reshape-env; ⨂-absorb-env)

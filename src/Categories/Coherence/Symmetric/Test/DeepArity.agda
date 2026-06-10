{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `rewriteDeep!` on multi-arity generators, and the convexity/retry story.
-- Companion to `Test.Deep` (split into its own module to keep per-module
-- type-checking memory bounded — each deep test retains a sizeable normal
-- form).
--
-- Configuration: a merge `m : a ⊗ a → a`, a split `e : a → a ⊗ a`, a unary
-- `k : a → a`, and a scalar-ish `u : unit → a`.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.DeepArity
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (is-just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Coherence.Symmetric C

module DeepArity (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (eᴹ : A C.⇒ (A C.⊗₀ A))
  (kᴹ : A C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ)

  a : ObjTerm
  a = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

  arity : Fin 4 → ObjTerm × ObjTerm
  arity zero                = (a ⊗₀ a) , a
  arity (suc zero)          = a , (a ⊗₀ a)
  arity (suc (suc zero))    = a , a
  arity (suc (suc (suc _))) = unitᵗ , a

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero                → mᴹ
    (suc zero)          → eᴹ
    (suc (suc zero))    → kᴹ
    (suc (suc (suc _))) → uᴹ)

  private
    m sp k u : S.HomTerm _ _
    m  = S.Agen (gen zero)
    sp = S.Agen (gen (suc zero))
    k  = S.Agen (gen (suc (suc zero)))
    u  = S.Agen (gen (suc (suc (suc zero))))

  -- Multi-wire redex: the split-then-process composite `(k ⊗ k) ∘ e`,
  -- carved out from under the closing merge `m`.
  module _ (fuse : (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ eᴹ) where

    test-deep-multiwire : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ _
    test-deep-multiwire =
      rewriteDeep! (m S.∘ (k S.⊗₁ k) S.∘ sp)
                   ((k S.⊗₁ k) S.∘ sp) sp fuse

  -- Scalar redex: `u : unit → a` has an EMPTY input interface, so the carved
  -- hole has no inputs and the frame's `pre` context ends in a unit wire.
  module _ (grow : uᴹ ≈ kᴹ ∘ uᴹ) where

    test-deep-scalar : mᴹ ∘ (uᴹ ⊗₁ kᴹ) ≈ _
    test-deep-scalar =
      rewriteDeep! (m S.∘ (u S.⊗₁ k)) u (k S.∘ u) grow

  -- Swapped merge arguments: in `m ∘ σ ∘ (k ⊗ k)` the merge consumes the two
  -- `k` outputs in swapped order; matching the rule's `m ∘ (k ⊗ k)` forces
  -- the (identically labelled) `k`-edges to be paired crosswise.
  module _ (slide : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ≈ kᴹ ∘ mᴹ) where

    test-deep-swapped-merge : mᴹ ∘ σ ∘ (kᴹ ⊗₁ kᴹ) ≈ _
    test-deep-swapped-merge =
      rewriteDeep! (m S.∘ S.σ S.∘ (k S.⊗₁ k))
                   (m S.∘ (k S.⊗₁ k)) (k S.∘ m) slide

  ------------------------------------------------------------------------------
  -- Convexity at the carve, and the match retry that makes it precise.

  -- TRUE non-convexity, rejected at the *carve*: in `k ∘ k ∘ k`, matching
  -- `k ⊗ k` on the two outer `k`s is injective — the search accepts it — but
  -- the middle `k` is a complement path from the redex's output back into its
  -- input, so the carved graph is cyclic through the hole and the topological
  -- ordering gets stuck.  No convex occurrence exists at all here, so the
  -- match retry exhausts and `deepFoc` correctly fails.  (Contrast with
  -- `deep-overlap-rejected` in `Test.Deep.DeepRewrite`, which dies earlier,
  -- at the search's injectivity check.)
  deep-non-convex-rejected
    : is-just (deepFoc (k S.∘ k S.∘ k) (k S.⊗₁ k)) ≡ false
  deep-non-convex-rejected = refl

  -- Match retry: in `(k ∘ k ∘ k) ⊗ k` the DFS's FIRST match for `k ⊗ k` is a
  -- non-convex outer pair as above, but convex pairings with the parallel
  -- fourth `k` exist; `deepFoc` walks past the non-convex matches to a
  -- carvable one.  (Before match enumeration + carve retry, this failed
  -- spuriously — the non-convex first match masked the others.)
  module _ (mix : kᴹ ⊗₁ kᴹ ≈ eᴹ ∘ mᴹ) where

    test-deep-retry : (kᴹ ∘ kᴹ ∘ kᴹ) ⊗₁ kᴹ ≈ _
    test-deep-retry =
      rewriteDeep! ((k S.∘ k S.∘ k) S.⊗₁ k) (k S.⊗₁ k) (sp S.∘ m) mix

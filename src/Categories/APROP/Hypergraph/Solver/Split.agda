{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Equation splitting as an automatic solver heuristic
-- (docs/smc-solver-performance.md, "Splitting as an automatic solver
-- heuristic").
--
-- `solveSplit? f g` decomposes a free-SMC goal `f ≈Term g` along shared
-- syntactic structure before ever calling the hypergraph solver:
--
--   1. refl peeling      — syntactically equal terms (conservative `eq?`)
--                          discharge by `≈-Term-refl`, zero solver cost;
--   2. aligned-cut `∘`   — same (decidable) middle object: recurse on the
--                          two pairs, compose by `∘-resp-≈`;
--   3. aligned `⊗₁`      — factor objects match by index unification:
--                          recurse pairwise, compose by `⊗-resp-≈`;
--   4. fallback          — the whole-term solve `findIsoᵀ` + the opaque
--                          `soundness-full-wired`, so completeness is
--                          unchanged (failures only ever fall back, at the
--                          level where the decomposition got stuck).
--
-- `solveSplitR?` is the entry point: it first reassociates both sides to
-- right-nested `∘`-chains (`reassoc`, assoc-only — no coherence), exposing
-- cuts so that case 2 peels common chain prefixes head-by-head.
--
-- Everything is sound by construction: each piece is solver-proven or
-- `refl`, composed by the `_≈Term_` congruence rules.  Conservativity of
-- `eq?` (returning `nothing` when unsure) only costs completeness of the
-- fast path, never soundness.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Split (sig-dec : APROPSignatureDec) where

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal using (v≤v)

open APROPSignatureDec sig-dec using (sig; _≟-mor_; _≟-ObjTerm_)
open APROP sig

open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIsoTab sig-dec using (findIsoᵀ)
open import Categories.APROP.Hypergraph.SoundnessFullWired sig-dec
  using (soundness-full-wired)

open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst₂)
open import Relation.Nullary using (yes; no)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

private
  -- UIP on `ObjTerm` (decidable equality ⇒ UIP, no `K`): collapses the
  -- reflexive endpoint equations that `--without-K` unification refuses to
  -- delete when matching index-constrained constructors twice.
  uip : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q
  uip = Decidable⇒UIP.≡-irrelevant _≟-ObjTerm_

--------------------------------------------------------------------------------
-- Conservative syntactic equality.  Only the yes-direction is needed: a
-- `just` certifies syntactic equality; `nothing` means "unsure" (it is NOT
-- a disequality proof).
--
-- Matching both terms as the same index-constrained constructor (`id`,
-- unitors, associators, `σ`) at a *shared* endpoint type gets stuck under
-- `--without-K` (reflexive equations like `A ≟ A` cannot be deleted), so —
-- as in `Verify.flat-match` — the worker `eqH?` compares terms at fully
-- general endpoints, taking the endpoint equalities as explicit proof
-- arguments; whatever reflexive proofs remain are collapsed by `uip`.
-- For `_∘_` the middle object is existential and is compared via
-- `_≟-ObjTerm_` (taking only the `yes` branch); generator labels via
-- `_≟-mor_`; the σ instance argument is matched as `v≤v`, the unique
-- constructor of `Symm ≤ Symm`.

eqH? : ∀ {A B A' B'} (f : HomTerm A B) (g : HomTerm A' B')
       (p : A ≡ A') (q : B ≡ B')
     → Maybe (subst₂ HomTerm p q f ≡ g)
eqH? (Agen m) (Agen m') refl refl with m ≟-mor m'
... | yes r = just (cong Agen r)
... | no _  = nothing
eqH? id id refl q with uip q refl
... | refl = just refl
eqH? (_∘_ {B = M} f₂ f₁) (_∘_ {B = N} g₂ g₁) refl refl with M ≟-ObjTerm N
... | no _ = nothing
... | yes refl with eqH? f₂ g₂ refl refl | eqH? f₁ g₁ refl refl
...   | just e₂ | just e₁ = just (cong₂ _∘_ e₂ e₁)
...   | _       | _       = nothing
eqH? (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂) refl refl
  with eqH? f₁ g₁ refl refl | eqH? f₂ g₂ refl refl
... | just e₁ | just e₂ = just (cong₂ _⊗₁_ e₁ e₂)
... | _       | _       = nothing
eqH? λ⇒ λ⇒ p refl with uip p refl
... | refl = just refl
eqH? λ⇐ λ⇐ refl q with uip q refl
... | refl = just refl
eqH? ρ⇒ ρ⇒ p refl with uip p refl
... | refl = just refl
eqH? ρ⇐ ρ⇐ refl q with uip q refl
... | refl = just refl
eqH? α⇒ α⇒ refl q with uip q refl
... | refl = just refl
eqH? α⇐ α⇐ refl q with uip q refl
... | refl = just refl
eqH? (σ ⦃ v≤v ⦄) (σ ⦃ v≤v ⦄) refl q with uip q refl
... | refl = just refl
eqH? _ _ _ _ = nothing

eq? : ∀ {A B} (f g : HomTerm A B) → Maybe (f ≡ g)
eq? f g = eqH? f g refl refl

--------------------------------------------------------------------------------
-- The whole-term fallback: hypergraph-iso search on the (tabulated)
-- translations, made into a `f ≈Term g` by the opaque soundness theorem.
-- The proof body sits inside the `just` and is never forced by consumers
-- that only inspect `is-just`.

fallback : ∀ {A B} (f g : HomTerm A B) → Maybe (f ≈Term g)
fallback f g =
  Maybe.map (λ iso → soundness-full-wired {f = f} {g = g} iso)
            (findIsoᵀ ⟪ f ⟫ ⟪ g ⟫)

--------------------------------------------------------------------------------
-- The splitting solver.  Structural recursion (only on subterms); failure
-- at a level falls back AT THAT LEVEL rather than propagating, so a stuck
-- decomposition still solves the smallest window it reached.

solveSplit? : ∀ {A B} (f g : HomTerm A B) → Maybe (f ≈Term g)
solveSplit? f g with eq? f g
solveSplit? f g | just refl = just ≈-Term-refl
solveSplit? (_∘_ {B = M} f₂ f₁) (_∘_ {B = N} g₂ g₁) | nothing with M ≟-ObjTerm N
... | no _ = fallback (f₂ ∘ f₁) (g₂ ∘ g₁)
... | yes refl with solveSplit? f₂ g₂ | solveSplit? f₁ g₁
...   | just p₂ | just p₁ = just (∘-resp-≈ p₂ p₁)
...   | _       | _       = fallback (f₂ ∘ f₁) (g₂ ∘ g₁)
solveSplit? (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂) | nothing with solveSplit? f₁ g₁ | solveSplit? f₂ g₂
... | just p₁ | just p₂ = just (⊗-resp-≈ p₁ p₂)
... | _       | _       = fallback (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂)
solveSplit? f g | nothing = fallback f g

--------------------------------------------------------------------------------
-- Reassociation (cut exposure): normalize `∘` to right-nested form,
-- recursing under `⊗₁`.  `comp` grafts a term onto the right end of a
-- right-nested spine.  Soundness uses only `assoc` and the congruence
-- rules — no coherence.

comp : ∀ {A B C} → HomTerm B C → HomTerm A B → HomTerm A C
comp (h ∘ g) f = h ∘ comp g f
comp h       f = h ∘ f

comp-sound : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B) → comp g f ≈Term g ∘ f
comp-sound (h ∘ g)   f = ≈-Term-trans (∘-resp-≈ ≈-Term-refl (comp-sound g f))
                                      (≈-Term-sym assoc)
comp-sound (Agen m)  f = ≈-Term-refl
comp-sound id        f = ≈-Term-refl
comp-sound (g ⊗₁ g') f = ≈-Term-refl
comp-sound λ⇒        f = ≈-Term-refl
comp-sound λ⇐        f = ≈-Term-refl
comp-sound ρ⇒        f = ≈-Term-refl
comp-sound ρ⇐        f = ≈-Term-refl
comp-sound α⇒        f = ≈-Term-refl
comp-sound α⇐        f = ≈-Term-refl
comp-sound σ         f = ≈-Term-refl

reassoc : ∀ {A B} → HomTerm A B → HomTerm A B
reassoc (g ∘ f)  = comp (reassoc g) (reassoc f)
reassoc (f ⊗₁ g) = reassoc f ⊗₁ reassoc g
reassoc f        = f

reassoc-sound : ∀ {A B} (f : HomTerm A B) → reassoc f ≈Term f
reassoc-sound (g ∘ f)  = ≈-Term-trans (comp-sound (reassoc g) (reassoc f))
                                      (∘-resp-≈ (reassoc-sound g) (reassoc-sound f))
reassoc-sound (f ⊗₁ g) = ⊗-resp-≈ (reassoc-sound f) (reassoc-sound g)
reassoc-sound (Agen m) = ≈-Term-refl
reassoc-sound id       = ≈-Term-refl
reassoc-sound λ⇒       = ≈-Term-refl
reassoc-sound λ⇐       = ≈-Term-refl
reassoc-sound ρ⇒       = ≈-Term-refl
reassoc-sound ρ⇐       = ≈-Term-refl
reassoc-sound α⇒       = ≈-Term-refl
reassoc-sound α⇐       = ≈-Term-refl
reassoc-sound σ        = ≈-Term-refl

--------------------------------------------------------------------------------
-- Entry point: reassociate both sides, split, then transport the result
-- back along `reassoc-sound`.

solveSplitR? : ∀ {A B} (f g : HomTerm A B) → Maybe (f ≈Term g)
solveSplitR? f g =
  Maybe.map
    (λ p → ≈-Term-trans (≈-Term-sym (reassoc-sound f))
                        (≈-Term-trans p (reassoc-sound g)))
    (solveSplit? (reassoc f) (reassoc g))

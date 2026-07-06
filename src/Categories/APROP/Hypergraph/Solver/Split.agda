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
--                          `soundness`, so completeness is
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

open import Categories.APROP.Hypergraph.Solver.Signature

module Categories.APROP.Hypergraph.Solver.Split (sig-dec : APROPSignatureDec) where

open import Categories.APROP
open import Categories.FreeMonoidal

open APROPSignatureDec sig-dec using (sig; _≟-mor_; _≟-ObjTerm_)
open APROP sig

open import Categories.APROP.Hypergraph.Model.Translation sig
open import Categories.APROP.Hypergraph.Solver.Match.FindIsoTab sig-dec
open import Categories.APROP.Hypergraph.Soundness sig-dec


open import Data.Maybe.Base
import Data.Maybe.Base as Maybe
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Axiom.UniquenessOfIdentityProofs

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
-- as in `Verify.flat-match-subst` — the worker `eqH?` compares terms at fully
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
eqH? (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂) refl refl with eqH? f₁ g₁ refl refl | eqH? f₂ g₂ refl refl
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
fallback f g = Maybe.map (λ iso → soundness {f = f} {g = g} iso) (findIsoᵀ ⟪ f ⟫ ⟪ g ⟫)

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

--------------------------------------------------------------------------------
-- BALANCED reassociation: flatten the ∘-spine into a `Chain`, then rebuild it
-- as a BALANCED `∘`-tree (depth ~log n instead of n) via adjacent pairing.
-- A balanced tree makes ⟪_⟫'s `hComposeP` tower shallow, so `tabH`/`findIsoᵀ`
-- traverse O(log n) per field instead of O(n) — the dominant cost of deep-gate
-- frame construction on long context spines (e.g. Frobenius).  Assoc-only, used
-- only INSIDE frames where the gate re-finds the iso (`findIsoᵀ`/`Verify`), so —
-- like `reassoc` in `deepFrame` — it needs no soundness proof.

private
  data Chain : ObjTerm → ObjTerm → Set where
    [_] : ∀ {A B} → HomTerm A B → Chain A B
    _◂_ : ∀ {A B C} → HomTerm B C → Chain A B → Chain A C

  appC : ∀ {A B C} → Chain B C → Chain A B → Chain A C
  appC [ f ]    c = f ◂ c
  appC (g ◂ gs) c = g ◂ appC gs c

  lenC : ∀ {A B} → Chain A B → ℕ
  lenC [ _ ]    = 1
  lenC (_ ◂ gs) = suc (lenC gs)

  -- One pairing pass: combine adjacent factors, halving the chain length.
  pairC : ∀ {A B} → Chain A B → Chain A B
  pairC [ f ]          = [ f ]
  pairC (h ◂ [ g ])    = [ h ∘ g ]
  pairC (h ◂ (g ◂ gs)) = (h ∘ g) ◂ pairC gs

  -- Right-collapse (only the fuel-exhausted fallback; unreachable with fuel = length).
  oneC : ∀ {A B} → Chain A B → HomTerm A B
  oneC [ f ]    = f
  oneC (g ◂ gs) = g ∘ oneC gs

  balC : ∀ {A B} → ℕ → Chain A B → HomTerm A B
  balC _       [ f ]     = f
  balC zero    (g ◂ gs)  = oneC (g ◂ gs)
  balC (suc n) (g ◂ gs)  = balC n (pairC (g ◂ gs))

  -- Identity elimination on a chain.  Every `id` factor in a `∘`-spine
  -- translates (`⟪_⟫`) to an `hComposeP` seam against an edge-free `hId`
  -- subgraph — a full tower node (its `vlab-P`/`ein-c`/`eout-c`/`count-non`/
  -- `nonMem` all get forced by `tabH`), yet `⟪ id ∘ x ⟫ ≅ᴴ ⟪ x ⟫` and
  -- `⟪ x ∘ id ⟫ ≅ᴴ ⟪ x ⟫` (the idˡ/idʳ laws hold in the model — the very
  -- point of pruning).  So dropping `id` factors leaves the carve gate
  -- (`findIsoᵀ`/`Verify`) success UNCHANGED while shortening the tower the
  -- finder must force.  A matched `id : HomTerm B C` forces `C ≡ B`, so the
  -- tail `gs : Chain A B` is already at the demanded type `Chain A C`.
  -- The last factor is kept verbatim (a sole `id` chain has no spine to
  -- collapse into, and the frame's endpoint objects must be preserved).
  dropIdC : ∀ {A B} → Chain A B → Chain A B
  dropIdC [ f ]        = [ f ]
  dropIdC (id   ◂ gs)  = dropIdC gs
  dropIdC (g    ◂ gs)  = g ◂ dropIdC gs

  -- Recognise a *fully identity* term: syntactically `id`, or a tensor whose
  -- both sides are themselves fully identity.  Returns `A ≡ B` (the endpoints
  -- coincide).  `⟪ id{A} ⊗₁ id{B} ⟫` and `⟪ id{A⊗B} ⟫` both reduce to
  -- `hTensor (hId A) (hId B)`, so collapsing an all-identity tensor leaf to a
  -- single `id` leaves the translated graph IDENTICAL — used below to spare
  -- the gate the per-leaf `hTensor` tower that `permute`'s `id ⊗₁ …` padding
  -- otherwise emits.
  isIdᵗ : ∀ {A B} → HomTerm A B → Maybe (A ≡ B)
  isIdᵗ id        = just refl
  isIdᵗ (f ⊗₁ g) with isIdᵗ f | isIdᵗ g
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing
  isIdᵗ _         = nothing

  -- Adjacent inverse-coherence cancellation on a chain.  The decode/retract
  -- seams produce runs like `… ◂ α⇐ ◂ α⇒ ◂ …` (the `unflatten-++-≅` bridge of
  -- one edge's `mid'` meeting the inverse bridge of the next), and `permute`'s
  -- `α⇒ ∘ … ∘ α⇐` swap brackets meet head-to-tail.  Each such pair composes to
  -- `id` in the model (`α⇐∘α⇒≈id`, `α⇒∘α⇐≈id`, the λ/ρ analogues, and `σ∘σ≈id`
  -- at matching types), so the pair translates to a graph identity and can be
  -- dropped without changing the carve gate's verdict.  When the two
  -- constructors are matched as a definite inverse pair, the shared boundary
  -- forces the outer endpoints to coincide, so the remaining tail is already
  -- at the demanded type.  A single right-to-left pass with look-again after a
  -- cancellation handles cascading seams; non-cancelling heads are kept.
  cancelC : ∀ {A B} → Chain A B → Chain A B
  cancelC [ f ]      = [ f ]
  cancelC (g ◂ gs)   = step g (cancelC gs)
    where
      step : ∀ {A B C} → HomTerm B C → Chain A B → Chain A C
      step α⇒ (α⇐ ◂ gs) = gs
      step α⇐ (α⇒ ◂ gs) = gs
      step λ⇒ (λ⇐ ◂ gs) = gs
      step λ⇐ (λ⇒ ◂ gs) = gs
      step ρ⇒ (ρ⇐ ◂ gs) = gs
      step ρ⇐ (ρ⇒ ◂ gs) = gs
      step (σ ⦃ _ ⦄) ((σ ⦃ _ ⦄) ◂ gs) = id ◂ gs
      -- End-of-chain pairs: the inverse partner is the final factor.
      step α⇒ [ α⇐ ] = [ id ]
      step α⇐ [ α⇒ ] = [ id ]
      step λ⇒ [ λ⇐ ] = [ id ]
      step λ⇐ [ λ⇒ ] = [ id ]
      step ρ⇒ [ ρ⇐ ] = [ id ]
      step ρ⇐ [ ρ⇒ ] = [ id ]
      step (σ ⦃ _ ⦄) [ σ ⦃ _ ⦄ ] = [ id ]
      step g  gs        = g ◂ gs

mutual
  flat∘ : ∀ {A B} → HomTerm A B → Chain A B
  flat∘ (g ∘ f)  = appC (flat∘ g) (flat∘ f)
  flat∘ (f ⊗₁ g) = tensorLeaf (reassocBal f) (reassocBal g)
  flat∘ f        = [ f ]

  -- Build the `⊗₁` leaf, collapsing it to a single `id` when both reassociated
  -- factors are fully identity (so the downstream `dropIdC` can then erase it
  -- entirely from any enclosing spine).
  tensorLeaf : ∀ {A B C D} → HomTerm A C → HomTerm B D → Chain (A ⊗₀ B) (C ⊗₀ D)
  tensorLeaf f g with isIdᵗ f | isIdᵗ g
  ... | just refl | just refl = [ id ]
  ... | _         | _         = [ f ⊗₁ g ]

  reassocBal : ∀ {A B} → HomTerm A B → HomTerm A B
  reassocBal f = let c = dropIdC (cancelC (dropIdC (flat∘ f))) in balC (lenC c) c

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

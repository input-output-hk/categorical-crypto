{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- SolverMor: the end-to-end assembly of the untyped free-monoidal diagram
-- solver from its three independently-built milestones:
--
--   * `Categories.SolverReflect`   — `reflect : WTerm n m → DiagU n` with the
--     UNCONDITIONAL soundness `reflect-sound boxSound` (TASK A: the box-leaf
--     right-unitor coherence `BoxSound` is now DISCHARGED here, via the Mac
--     Lane / Kelly unit coherence laws — see `Reflect.boxSound`).
--   * `Categories.SolverCompare`   — decidable normal-form equality `_≟DiagU_`
--     on diagrams and `≈NF⇒≡`.
--   * `Categories.SolverNormalize` — the σ-free interchange `swap-step-sound`
--     and the `Star`-path lifting `⇒W*-sound′` (the reorder engine).
--   * `Categories.SolveMorSpike`   — the transport `solveMorReflected` of any
--     `≈Term` equation into an arbitrary target monoidal category `C`.
--
-- We deliver:
--
--   (1) `solveMorW? : (s t : WTerm n m) → Maybe (embed s ≈Term embed t)`
--       the runnable solver on the wire-fragment WTerm language (id / ∘ / box,
--       objects already `wires`-flat — exactly the fragment `reflect` targets).
--       It reflects both sides, decides NF-equality, and on success chains
--       `reflect-sound boxSound` on each end with `≈NF⇒≡` in the middle.  No
--       hole, no postulate.  (We work on `WTerm` rather than the full `HomTerm`
--       because `reflect` only covers the wire fragment; see the report.)
--
--   (2) `solveMorWC? : (s t : WTerm n m)
--                     → Maybe (C [ ⟦ embed s ⟧₁ ≈ ⟦ embed t ⟧₁ ])`
--       the same decision, transported into an ARBITRARY target monoidal
--       category `C` with a generator interpretation `⟦Mor⟧`, by composing (1)
--       with `SolveMorSpike.solveMorReflected`.
--
--   (3) a LITMUS TEST that the pipeline actually RUNS (returns `just`): the
--       associativity equation `(h ∘ʷ g) ∘ʷ f ≈ h ∘ʷ (g ∘ʷ f)`, whose two
--       sides reflect to NF-equal diagrams, decided positively by the solver.
--       This exercises reflect + ∘ᵈ-append + decidable NF compare end-to-end.
--
-- The genuine two-box interchange (which needs the reorder engine, not just
-- NF-equality of `reflect` output) is the proven, σ-free
-- `SolverNormalize.swap-step-sound` (an instance of `TwoBoxSwap.two-box-swap`);
-- `SolveMorSpike.SolveMor.WithMor.interchange-target` transports exactly that
-- equation into an arbitrary target monoidal category `C`.  It is NOT routed
-- through `solveMorW?` here because that decides NF-equality of `reflect`
-- output, which the reorder engine deliberately sits on top of.
--------------------------------------------------------------------------------

module Categories.SolverMor where

open import Level using (Level)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to any-just)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped
open import Categories.SolverReflect using (module Reflect)
open import Categories.SolverCompare using (module SolverCompare)

--------------------------------------------------------------------------------
-- The solver is relative to a label set `X` with decidable equality, a
-- morphism-generator family `Mor`, and a decidable "same generator" test.
--------------------------------------------------------------------------------
module SolverMor
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor  : List X → List X → Set)
  where

  -- the diagram / term machinery (shared definitionally across all modules).
  open Untyped Mon {X} Mor
  open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R

  -- the reflect milestone (with TASK A's `boxSound` already discharged).
  open Reflect Mon {X} _≟X_ Mor
    using ( WTerm; boxʷ; idʷ; _∘ʷ_; embed; reflect; out-reflect
          ; reflect-sound; boxSound; BoxSound; coeCod' )

  -- the compare milestone.
  open SolverCompare Mon {X} _≟X_ Mor
    using (Gen; gen; module Decide)

  module Solve (_≟Mor_ : DecidableEquality Gen) where

    open Decide _≟Mor_
      using (_≈NF_; _≟DiagU_; ≈NF⇒≡; ≈NF⇒width; coeW)

    --------------------------------------------------------------------------------
    -- Bridge: SolverReflect's `coeCod'` and SolverCompare's `coeW` are the SAME
    -- flat-codomain coercion (both are `subst` / refl-match identities).  This
    -- lets us state the soundness in the `coeW` form `Assembly` uses while
    -- proving it with `reflect-sound`.
    --------------------------------------------------------------------------------
    coeCod'≈coeW : ∀ {n p q} (e : p ≡ q) (h : HomTerm (wires n) (wires p))
                 → coeCod' e h ≈Term coeW e h
    coeCod'≈coeW refl h = ≈-Term-refl

    --------------------------------------------------------------------------------
    -- The reflect-then-compare soundness on WTerms, in `coeW` form.
    --   coeW (out-reflect t) ⟦ reflect t ⟧  ≈Term  embed t          (unconditional)
    --------------------------------------------------------------------------------
    reflectW-sound : ∀ {n m} (t : WTerm n m)
                   → coeW (out-reflect t) ⟦ reflect t ⟧ ≈Term embed t
    reflectW-sound t = ≈-Term-trans
      (≈-Term-sym (coeCod'≈coeW (out-reflect t) ⟦ reflect t ⟧))
      (reflect-sound boxSound t)

    --------------------------------------------------------------------------------
    -- Transport an `≈NF` of the two reflected diagrams into a `≈Term` of their
    -- coerced interpretations (the diagrams share input width `n`; the two
    -- output-width witnesses are equal by UIP, here absorbed by `≡⇒≈Term` after
    -- `≈NF⇒≡`).  Mirrors `Assembly.nfEq-coerced`.
    --------------------------------------------------------------------------------
    nfEq-coerced : ∀ {n m} (s t : WTerm n m)
                 → reflect s ≈NF reflect t
                 → coeW (out-reflect s) ⟦ reflect s ⟧
                   ≈Term coeW (out-reflect t) ⟦ reflect t ⟧
    nfEq-coerced s t eq = aux (≈NF⇒≡ eq) (out-reflect s) (out-reflect t)
      where
        aux : ∀ {n p} {d d' : DiagU n} (e : d ≡ d')
                (q₁ : out d ≡ p) (q₂ : out d' ≡ p)
            → coeW q₁ ⟦ d ⟧ ≈Term coeW q₂ ⟦ d' ⟧
        aux {d = d} refl q₁ q₂ =
          ≡⇒≈Term (cong (λ z → coeW z ⟦ d ⟧) (uip q₁ q₂))
          where
            -- UIP on List X equalities (output widths), derived from _≟X_.
            uip : ∀ {p q : List X} (a b : p ≡ q) → a ≡ b
            uip refl refl = refl

    --------------------------------------------------------------------------------
    -- (1) THE SOLVER on the wire fragment.
    --------------------------------------------------------------------------------
    solveMorW? : ∀ {n m} (s t : WTerm n m) → Maybe (embed s ≈Term embed t)
    solveMorW? s t with reflect s ≟DiagU reflect t
    ... | no  _  = nothing
    ... | yes eq = just (begin
            embed s
              ≈⟨ reflectW-sound s ⟨
            coeW (out-reflect s) ⟦ reflect s ⟧
              ≈⟨ nfEq-coerced s t eq ⟩
            coeW (out-reflect t) ⟦ reflect t ⟧
              ≈⟨ reflectW-sound t ⟩
            embed t ∎)

--------------------------------------------------------------------------------
-- (2) Transport to an arbitrary target monoidal category.
--
-- Compose `solveMorW?` with `SolveMorSpike.solveMorReflected`.  Kept in a
-- separate module so the (object/morphism) interpretation parameters are only
-- demanded when the C-level solver is actually used.
--------------------------------------------------------------------------------
module SolverMorTarget
  {o ℓ e : Level}
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (Mor  : List X → List X → Set)
  (_≟Mor_ : DecidableEquality (SolverCompare.Gen Mon {X} _≟X_ Mor))
  (C : MonoidalCategory o ℓ e)
  (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
  where

  open import Categories.SolveMorSpike using (module SolveMor)

  open Untyped Mon {X} Mor using (wires; mor)
  open Reflect Mon {X} _≟X_ Mor using (WTerm; embed)

  open SolverMor {X} _≟X_ Mor using (module Solve)
  open Solve _≟Mor_ using (solveMorW?)

  -- the spike, instantiated at the same (X, Mor, C, ⟦_⟧ᵖ₀).  Its generator
  -- interpretation `⟦Mor⟧` lives in the inner parameter module `WithMor`, so
  -- we expose `⟦_⟧obj` here and demand `⟦Mor⟧` per use.
  module S = SolveMor {o} {ℓ} {e} {X} Mor C ⟦_⟧ᵖ₀
  open S using (⟦_⟧obj)

  Cᵤ : Category o ℓ e
  Cᵤ = MonoidalCategory.U C

  module WithGen
    (⟦Mor⟧ : ∀ {a b} → Mor a b → Cᵤ [ ⟦ wires a ⟧obj , ⟦ wires b ⟧obj ])
    where
    open S.WithMor ⟦Mor⟧ using (⟦_⟧₁; solveMorReflected)

    -- (2) the C-level solver: decide on the free side, transport to C.
    solveMorWC? : ∀ {n m} (s t : WTerm n m)
                → Maybe (Cᵤ [ ⟦ embed s ⟧₁ ≈ ⟦ embed t ⟧₁ ])
    solveMorWC? s t with solveMorW? s t
    ... | nothing = nothing
    ... | just p  = just (solveMorReflected p)

--------------------------------------------------------------------------------
-- (3) LITMUS TEST: the pipeline actually RUNS (returns `just <proof>`).
--
-- We instantiate at X = ⊤ (so wire labels are unary, `wires` lists are lengths)
-- with the maximal generator family `Mor _ _ = ⊤` (a box for every dom/cod),
-- and a decidable generator equality.  We then check that `solveMorW?` returns
-- `just` on a genuinely non-reflexive equation: the ASSOCIATIVITY of `∘ʷ`,
--   (h ∘ʷ g) ∘ʷ f   vs   h ∘ʷ (g ∘ʷ f) ,
-- whose two sides reflect (via `∘ᵈ`-append) to NF-equal diagrams.  This drives
-- reflect + ∘ᵈ + decidable NF compare + `reflect-sound boxSound` end to end.
--------------------------------------------------------------------------------
module Litmus where

  open import Data.Unit using (⊤; tt)
  open import Data.Unit.Properties using () renaming (_≟_ to _≟⊤_)

  M : List ⊤ → List ⊤ → Set
  M _ _ = ⊤

  open SolverMor {⊤} _≟⊤_ M
  open Untyped Mon {⊤} M using (mor)
  open Reflect Mon {⊤} _≟⊤_ M using (WTerm; boxʷ; idʷ; _∘ʷ_; embed)
  open SolverCompare Mon {⊤} _≟⊤_ M using (Gen; _≟L_)
  open FreeMonoidalHelper.Mor Mon ⊤ mor using (_≈Term_)

  -- decidable equality on the generator triples  (a , b , tt).
  _≟G_ : DecidableEquality Gen
  (a , b , tt) ≟G (a' , b' , tt) with a ≟L a' | b ≟L b'
  ... | yes refl | yes refl = yes refl
  ... | no  a≢   | _        = no λ { refl → a≢ refl }
  ... | yes _    | no  b≢   = no λ { refl → b≢ refl }

  open Solve _≟G_ using (solveMorW?)

  -- three composable boxes  f : 1→2 , g : 2→3 , h : 3→4  (lengths via List ⊤).
  one two three four : List ⊤
  one   = tt ∷ []
  two   = tt ∷ tt ∷ []
  three = tt ∷ tt ∷ tt ∷ []
  four  = tt ∷ tt ∷ tt ∷ tt ∷ []

  f : WTerm one two
  f = boxʷ tt
  g : WTerm two three
  g = boxʷ tt
  h : WTerm three four
  h = boxʷ tt

  lhs rhs : WTerm one four
  lhs = (h ∘ʷ g) ∘ʷ f
  rhs = h ∘ʷ (g ∘ʷ f)

  -- THE RUN: the solver returns `just` (with a genuine ≈Term proof inside).
  litmus-assoc : Maybe (embed lhs ≈Term embed rhs)
  litmus-assoc = solveMorW? lhs rhs

  -- THE PROOF that the run actually fires.  `Is-just litmus-assoc` is inhabited
  -- exactly when `litmus-assoc` reduces to `just _`; the fact that `just tt`
  -- typechecks here IS the evidence the solver said `just` (not `nothing`).
  litmus-runs : Is-just litmus-assoc
  litmus-runs = any-just tt

  -- and we can extract the genuine `≈Term` witness the solver produced.
  litmus-proof : embed lhs ≈Term embed rhs
  litmus-proof = to-witness litmus-runs

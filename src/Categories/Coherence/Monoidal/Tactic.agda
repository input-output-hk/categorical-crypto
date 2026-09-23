------------------------------------------------------------------------
-- A reflection frontend for the monoidal coherence solver.
--
--   solve-mor 𝒞 : proves `f ≈ g` in `MonoidalCategory 𝒞` whenever the
--   backend's decision procedure equates their wire diagrams
--   (coherence + naturality + interchange over opaque generators).

{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Tactic where

open import Data.Bool
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
import Data.Vec as Vec
open import Data.Fin
open import Data.Fin.Reflection

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.TCM.Syntax
open import Agda.Builtin.Reflection using (primQNameEquality)

open import Reflection.Utils.Args
open import Reflection.Utils.Core
open import Reflection.Utils.Reduction
open import Reflection.QuotedDefinitions

open import Tactic.Solver.Core

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor
import Categories.Morphism as Morphismᴹ

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core
import Categories.Coherence.Monoidal as Coh

------------------------------------------------------------------------
-- Names

private
  `∘    = quote Category._∘_
  `id   = quote Category.id
  `hom  = quote Category._⇒_
  `≈    = quote Category._≈_
  `⊗₁   = quote Monoidal._⊗₁_
  `⊗₀   = quote Monoidal._⊗₀_
  `unit = quote Monoidal.unit
  `λiso = quote Monoidal.unitorˡ
  `ρiso = quote Monoidal.unitorʳ
  `αiso = quote Monoidal.associator
  `from = quote Morphismᴹ._≅_.from
  `to   = quote Morphismᴹ._≅_.to
  `F₀   = quote Functor.F₀
  `₀    = quote Functor.₀
  `F₁   = quote Functor.F₁
  `₁    = quote Functor.₁
  `⊗f   = quote Monoidal.⊗
  `pair = quote _,_

  blocked : List Name
  blocked = `∘ ∷ `id ∷ `hom ∷ `≈ ∷ `⊗₁ ∷ `⊗₀ ∷ `unit
          ∷ `λiso ∷ `ρiso ∷ `αiso ∷ `from ∷ `to ∷ `F₀ ∷ `⊗f ∷ []

  _==_ : Name → Name → Bool
  _==_ = primQNameEquality

  -- emission targets
  `Var   = quote FreeMonoidalHelper.Var
  `unitᵒ = quote FreeMonoidalHelper.unit
  `⊗ᵒ    = quote FreeMonoidalHelper._⊗₀_
  `var   = quote FreeMonoidalHelper.Mor.var
  `idᴹ   = quote FreeMonoidalHelper.Mor.id
  `∘ᴹ    = quote FreeMonoidalHelper.Mor._∘_
  `⊗₁ᴹ   = quote FreeMonoidalHelper.Mor._⊗₁_
  `λ⇒ = quote FreeMonoidalHelper.Mor.λ⇒ ; `λ⇐ = quote FreeMonoidalHelper.Mor.λ⇐
  `ρ⇒ = quote FreeMonoidalHelper.Mor.ρ⇒ ; `ρ⇐ = quote FreeMonoidalHelper.Mor.ρ⇐
  `α⇒ = quote FreeMonoidalHelper.Mor.α⇒ ; `α⇐ = quote FreeMonoidalHelper.Mor.α⇐
  `genS  = quote FinSig.genS
  `solve = quote Coh.MorSolve.solveMor!

------------------------------------------------------------------------
-- The object level: a `DetectedTheory` driven by `parseGoalTerm`,
-- with atoms emitted in `indexed` mode as `Var i` references into the
-- store that later becomes the `vars` vector.

private
  enc⊗ᵒ : EncodeEnv → Occurrence → List Term → Term
  enc⊗ᵒ _ _ (x ∷ y ∷ []) = con `⊗ᵒ (x ⟨∷⟩ y ⟨∷⟩ [])
  enc⊗ᵒ _ _ _            = unknown

  ⊗₀op unitOp F₀op : Operator
  ⊗₀op = record
    { opTerm   = def `⊗₀ []
    ; parseOcc = defaultParseOcc 2
    ; encode   = enc⊗ᵒ
    }
  unitOp = record
    { opTerm   = def `unit []
    ; parseOcc = defaultParseOcc 0
    ; encode   = λ _ _ _ → con `unitᵒ []
    }
  F₀op = record
    { opTerm   = def `F₀ []
    ; parseOcc = f₀parse
    ; encode   = enc⊗ᵒ
    }
    where
    -- accept only the bundle's own bifunctor applied to a pair
    f₀parse : Args Term → Maybe Occurrence
    f₀parse as = case takeLast 2 (vArgs as) of λ where
      (just (F Vec.∷ p Vec.∷ Vec.[])) → case (headName F , p) of λ where
        (just g , con c cargs) →
          if (g == `⊗f) ∧ (c == `pair)
            then (case takeLast 2 (vArgs cargs) of λ where
              (just (x Vec.∷ y Vec.∷ Vec.[])) →
                just (record { operands = x ∷ y ∷ [] ; indices = [] })
              _ → nothing)
            else nothing
        _ → nothing
      _ → nothing

  -- the same parser under the record-module shorthand head
  ₀op : Operator
  ₀op = record F₀op { opTerm = def `₀ [] }

  objTheory : DetectedTheory
  objTheory = record
    { operators    = ⊗₀op ∷ F₀op ∷ ₀op ∷ unitOp ∷ []
    ; constants    = []
    ; literalSpec  = nothing
    ; blockedNames = blocked
    ; sortOf       = nothing
    -- the reference is a `Fin` literal: `toTerm` erases the bound
    -- into hidden `unknown`s, so `fromℕ`'s over-tight bound is fine
    ; atomEmission = indexed (λ _ _ s → con `Var (toTerm (fromℕ s) ⟨∷⟩ []))
    ; encodeEq     = λ _ _ _ → unknown   -- single terms only, never equations
    ; finishSolve  = λ _ body _ → body
    }

  objFuel : ℕ
  objFuel = 1024

  -- The `prepIndex` pre-pass: bring an object term onto the shape the
  -- PURE object operators can recognise. `f₀parse` needs
  -- `F₀ (⊗ M) (con _,_ x y)`; an endpoint that came from a derived
  -- tensor functor — `-⊗ j`, `j ⊗-`, the braiding's `flip ⊗`, any
  -- `_∘F_` composite — weak-head reduces only as far as
  -- `F₀ (⊗ M) ⟨neutral pair⟩`, and a pure `parseOcc` cannot reduce
  -- the pair. Running in TC, this pass can: it rebuilds the node as
  -- an ordinary `_⊗₀_` application and recurses into the components.
  -- A node in which nothing is recognised is returned unchanged (not
  -- weak-head normalised), so atom spellings emitted into the `vars`
  -- vector stay exactly as the user wrote them. A rebuilt node's four
  -- hidden level/category arguments are left `unknown` — safe, since
  -- such a node is always consumed by `⊗₀op` and never atomised.
  expandObj : ℕ → Term → TC Term
  expandObj zero t = pure t
  expandObj (suc n) t = do
    t' ← whnfIfReducible t
    case t' of λ where
      (def f as) →
        if f == `⊗₀ then (case takeLast 3 (vArgs as) of λ where
          (just (M Vec.∷ x Vec.∷ y Vec.∷ Vec.[])) → rebuild M x y
          _ → pure t)
        else if (f == `F₀) ∨ (f == `₀) then (case takeLast 2 (vArgs as) of λ where
          (just (F Vec.∷ p Vec.∷ Vec.[])) → viaF₀ F p
          _ → pure t)
        else pure t
      _ → pure t
    where
    rebuild : Term → Term → Term → TC Term
    rebuild M x y = do
      x' ← expandObj n x
      y' ← expandObj n y
      pure (def `⊗₀ (4 ⋯⟅∷⟆ M ⟨∷⟩ x' ⟨∷⟩ y' ⟨∷⟩ []))

    viaF₀ : Term → Term → TC Term
    viaF₀ (def g gas) p =
      if g == `⊗f
        then (case takeLast 1 (vArgs gas) of λ where
          (just (M Vec.∷ Vec.[])) → do
            p' ← whnfIfReducible p
            case p' of λ where
              (con c cargs) →
                if c == `pair
                  then (case takeLast 2 (vArgs cargs) of λ where
                    (just (x Vec.∷ y Vec.∷ Vec.[])) → rebuild M x y
                    _ → pure t)
                  else pure t
              _ → pure t
          _ → pure t)
        else pure t
    viaF₀ _ _ = pure t

------------------------------------------------------------------------
-- The morphism level: the two-level theory over the object level.

private
  -- composite nodes leave their ObjTerm indices to the elaborator
  node2 : Name → EncodeEnv → List Term → Term
  node2 c _ (g ∷ h ∷ []) = con c (g ⟨∷⟩ h ⟨∷⟩ [])
  node2 c _ _            = unknown

  -- pinning a leaf's ObjTerm index means supplying the FULL hidden
  -- prefix: quoted constructors carry their data parameters
  -- ({ℓ′} v X mor = 4 for HomTerm) before their own implicits, and
  -- the internal checker only inserts hidden arguments where none
  -- were given
  leaf1 : Name → EncodeEnv → List Term → Term
  leaf1 c _ (x ∷ []) = con c (4 ⋯⟅∷⟆ x ⟅∷⟆ [])
  leaf1 c _ _        = unknown

  leaf3 : Name → EncodeEnv → List Term → Term
  leaf3 c _ (x ∷ y ∷ z ∷ []) = con c (4 ⋯⟅∷⟆ x ⟅∷⟆ y ⟅∷⟆ z ⟅∷⟆ [])
  leaf3 c _ _                = unknown

  -- λ/ρ take one object implicit, α takes three; anything else
  -- projected out of an iso is an opaque box
  isoOcc : Name → Name → Name → Args Term → TC (Maybe TwoLevelOccurrence)
  isoOcc cλ cρ cα as = do
    inner ← innerDef as
    case inner of λ where
      (just (g , ias)) →
        if g == `λiso then hiddenIndexLeaf 1 (leaf1 cλ) ias
        else if g == `ρiso then hiddenIndexLeaf 1 (leaf1 cρ) ias
        else if g == `αiso then hiddenIndexLeaf 3 (leaf3 cα) ias
        else pure nothing
      nothing → pure nothing

  -- `_⊗₁_` is `curry′ F₁` on morphisms just as `_⊗₀_` is on objects, so
  -- a derived tensor functor's action — `₁ (-⊗ j) α`, say — reaches the
  -- parser as `F₁ (⊗ M) ⟨pair-valued morphism⟩`, stuck on the blocked
  -- `⊗`.  The pair morphism itself is headed by an unblocked name
  -- (`constʳ`'s `F₁`, …), so one more whnf exposes the literal `_,_`,
  -- and the occurrence is the `_⊗₁_` node on its components.  Anything
  -- else under an `F₁` head stays an opaque box.
  f₁parse : Args Term → TC (Maybe TwoLevelOccurrence)
  f₁parse as = case takeLast 2 (vArgs as) of λ where
    (just (F Vec.∷ p Vec.∷ Vec.[])) → case headName F of λ where
      (just g) →
        if g == `⊗f
          then (do
            p' ← whnfIfReducible p
            case p' of λ where
              (con c cargs) →
                if c == `pair
                  then (case takeLast 2 (vArgs cargs) of λ where
                    (just (x Vec.∷ y Vec.∷ Vec.[])) → do
                      -- the components are elaborator-produced (the pair
                      -- functor's own `F₁`s wrapped around the user's
                      -- morphisms), never user spellings; whnf strips
                      -- that wrapper so an atom among them keeps the
                      -- spelling the user wrote elsewhere in the goal
                      x' ← whnfIfReducible x
                      y' ← whnfIfReducible y
                      pure (just (record
                        { indices  = []
                        ; operands = x' ∷ y' ∷ []
                        ; encode   = λ env _ → node2 `⊗₁ᴹ env }))
                    _ → pure nothing)
                  else pure nothing
              _ → pure nothing)
          else pure nothing
      nothing → pure nothing
    _ → pure nothing

  mkOp : Name → (Args Term → TC (Maybe TwoLevelOccurrence)) → TwoLevelOperator
  mkOp nm p = record { opTerm = def nm [] ; parseOcc = p }

  morTheory : TwoLevelTheory
  morTheory = record
    { macroName    = "solve-mor"
    ; indexTheory  = objTheory
    ; prepIndex    = expandObj objFuel
    ; operators    = mkOp `∘    (fixedArity 2 (node2 `∘ᴹ))
                   ∷ mkOp `⊗₁   (fixedArity 2 (node2 `⊗₁ᴹ))
                   ∷ mkOp `F₁   f₁parse
                   ∷ mkOp `₁    f₁parse
                   ∷ mkOp `id   (hiddenIndexLeaf 1 (leaf1 `idᴹ))
                   ∷ mkOp `from (isoOcc `λ⇒ `ρ⇒ `α⇒)
                   ∷ mkOp `to   (isoOcc `λ⇐ `ρ⇐ `α⇐)
                   ∷ []
    ; blockedNames = blocked
    ; atomRef      = λ _ i → con `var (con `genS (toTerm (fromℕ i) ⟨∷⟩ []) ⟨∷⟩ [])
    ; matchType    = endpoints
    ; encodeSig    = encSig
    ; finishSolve  = finish
    }
    where
    endpoints : Term → Maybe (List Term)
    endpoints (def f as) =
      if f == `hom
        then (case takeLast 2 (vArgs as) of λ where
          (just (x Vec.∷ y Vec.∷ Vec.[])) → just (x ∷ y ∷ [])
          _ → nothing)
        else nothing
    endpoints _ = nothing

    encSig : EncodeEnv → Term → List Term → Term
    encSig _ b (x ∷ y ∷ []) = (x `, y) `, b
    encSig _ _ _            = unknown

    finish : EncodeEnv → Term → Term → List Term → List Term → Term
    finish env lhs rhs vars sig = def `solve
      ( 3 ⋯⟅∷⟆ EncodeEnv.R↓ env
      ⟨∷⟩ unknown ⟅∷⟆ `vec vars
      ⟨∷⟩ unknown ⟅∷⟆ `vec sig
      ⟨∷⟩ 2 ⋯⟅∷⟆ lhs ⟨∷⟩ rhs ⟨∷⟩ unknown ⟅∷⟆ [])

------------------------------------------------------------------------
-- The macro.

solve-mor-macro : Term → Term → TC ⊤
solve-mor-macro 𝒞 hole = do
  𝒞' ← checkType 𝒞 (def (quote MonoidalCategory) (3 ⋯⟨∷⟩ []))
  solveByTwoLevelTheory morTheory 𝒞' hole

macro
  solve-mor : Term → Term → TC ⊤
  solve-mor = solve-mor-macro

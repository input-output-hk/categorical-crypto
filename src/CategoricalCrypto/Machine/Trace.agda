{-# OPTIONS --safe #-}

-- ============================================================================
-- Generic trace verification for machines.
--
-- A trace is a chronological list of entries, each naming a *hint*, the
-- input the step consumes, and an *expectation* about the output it emits.
-- Hints exist because step relations are nondeterministic: a rule may have
-- premises with witnesses that the input does not determine, so the trace
-- has to name them. Checking a step is then a decision problem rather than
-- a search.
--
-- A machine is made checkable by a `Checkable` record: the hint type, a way
-- to read the hint off a step, and a per-step checker that returns either a
-- machine-specific error or a step carrying that hint. An `Observation`
-- fixes what is checked about outputs: nothing (`ignoreOutputs`) or equality
-- with an expected output (`exactOutputs`).
--
-- From these, once for every machine:
--   * `verifyTrace`, which returns a `ValidTrace` carrying the derivations,
--     or a `TraceErr` locating the first failing entry;
--   * `toRun`, which forgets hints and expectations and yields the run of
--     the machine that the trace describes (soundness);
--   * given `Complete` (errors refute, and a hint determines output and
--     target), `complete`, which shows that an error means no run with these
--     hints exists, and `validTrace?`, which decides `ValidTrace`.
-- ============================================================================

module CategoricalCrypto.Machine.Trace where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Maybe.Properties using () renaming (≡-dec to ≡-decMaybe)
import Data.Sum as S
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Class.Monad.Ext using (Functor-⊎; Applicative-⊎; Monad-⊎)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core using (Machine; _⊗ᵀ_)

module _ {A B : Channel} (M : Machine A B) where

  open Channel (A ⊗ᵀ B) renaming (inType to Input; outType to Output) public
  open Machine M using (State; stepRel)

  ------------------------------------------------------------------------------
  -- Steps and runs

  -- A step from `s` on input `i`, packaged with what it emits and where it
  -- goes.
  record Step (s : State) (i : Input) : Type where
    constructor step
    field
      out        : Maybe Output
      next       : State
      derivation : stepRel s i out next

  open Step public

  -- Runs of the machine, labelled by the inputs consumed and outputs emitted.
  data Run : State → List (Input × Maybe Output) → State → Type where
    done : ∀ {s} → Run s [] s
    _∷_  : ∀ {s i o s′ l s″}
         → stepRel s i o s′ → Run s′ l s″ → Run s ((i , o) ∷ l) s″

  ------------------------------------------------------------------------------
  -- What a machine provides to be checkable

  record Checkable : Type₁ where
    field
      Hint   : Type
      hintOf : ∀ {s i} → Step s i → Hint

    StepWith : Hint → State → Input → Type
    StepWith h s i = Σ[ x ∈ Step s i ] hintOf x ≡ h

    -- Traces name inputs as `Msg`s. Because `_⊗₀_` is opaque, a flat sum of
    -- the leaf message types is often easier to produce and to match on than
    -- `Input` itself; `embed` maps it into `Input`, typically via selectors.
    -- Use `Msg = Input` and `embed = id` when no flattening is wanted.
    field
      Msg       : Type
      embed     : Msg → Input
      Err       : Hint → Msg → State → Type
      checkStep : ∀ h m s → Err h m s ⊎ StepWith h s (embed m)

  -- Optional: errors are genuine refutations, and a hint pins down the
  -- result of a step. Needed for completeness, not for soundness.
  record Complete (C : Checkable) : Type where
    open Checkable C
    field
      refute : ∀ {h m s} → Err h m s → ¬ StepWith h s (embed m)
      unique : ∀ {h i s} (x y : StepWith h s i)
             → (x .proj₁ .out , x .proj₁ .next) ≡ (y .proj₁ .out , y .proj₁ .next)

    -- With `Complete`, `checkStep` is a decision procedure: whether a step
    -- with a given hint exists is decidable.
    step? : ∀ h m s → Dec (StepWith h s (embed m))
    step? h m s with checkStep h m s
    ... | inj₁ err = no (refute err)
    ... | inj₂ x   = yes x

  ------------------------------------------------------------------------------
  -- What is checked about outputs

  record Observation : Type₁ where
    field
      Expect  : Type
      Matches : Expect → Maybe Output → Type
      match?  : ∀ e o → Dec (Matches e o)

  ignoreOutputs : Observation
  ignoreOutputs = record
    { Expect  = ⊤
    ; Matches = λ _ _ → ⊤
    ; match?  = λ _ _ → yes tt
    }

  -- `Output` is a sum built with the opaque `_⊗₀_`, so its decidable
  -- equality has to be supplied by the machine, typically proved in a block
  -- that unfolds `_⊗₀_`.
  exactOutputs : DecidableEquality Output → Observation
  exactOutputs _≟_ = record
    { Expect  = Maybe Output
    ; Matches = λ e o → o ≡ e
    ; match?  = λ e o → ≡-decMaybe _≟_ o e
    }

  ------------------------------------------------------------------------------
  -- The verifier

  module Verifier (C : Checkable) (Ob : Observation) where

    open Checkable C
    open Observation Ob

    record Entry : Type where
      constructor ⟨_,_,_⟩
      field
        hint   : Hint
        input  : Msg
        expect : Expect

    Trace : Type
    Trace = List Entry

    private variable
      s s′ : State
      h    : Hint
      m    : Msg
      e    : Expect
      es   : Trace

    -- A trace together with a run of the machine that realises it.
    data ValidTrace : State → Trace → State → Type where
      []  : ValidTrace s [] s
      ok∷ : ((x , _) : StepWith h s (embed m))
          → Matches e (x .out)
          → ValidTrace (x .next) es s′
          → ValidTrace s (⟨ h , m , e ⟩ ∷ es) s′

    data StepErr (h : Hint) (m : Msg) (e : Expect) (s : State) : Type where
      rejected        : Err h m s → StepErr h m e s
      output-mismatch : ((x , _) : StepWith h s (embed m))
                      → ¬ Matches e (x .out)
                      → StepErr h m e s

    -- The first failing entry, with the valid prefix leading up to it.
    data TraceErr : State → Trace → Type where
      here  : StepErr h m e s → TraceErr s (⟨ h , m , e ⟩ ∷ es)
      there : ((x , _) : StepWith h s (embed m))
            → Matches e (x .out)
            → TraceErr (x .next) es
            → TraceErr s (⟨ h , m , e ⟩ ∷ es)

    verifyStep : ∀ h m e s
               → StepErr h m e s ⊎ Σ[ (x , _) ∈ StepWith h s (embed m) ] Matches e (x .out)
    verifyStep h m e s = do
      x@(x′ , _) ← S.map₁ rejected (checkStep h m s)
      case match? e (x′ .out) of λ where
        (yes ok) → return (x , ok)
        (no ¬ok) → inj₁ (output-mismatch x ¬ok)

    verifyTrace : ∀ s es → TraceErr s es ⊎ Σ[ s′ ∈ State ] ValidTrace s es s′
    verifyTrace s []                   = return (s , [])
    verifyTrace s (⟨ h , m , e ⟩ ∷ es) = do
      (x@(x′ , _) , ok) ← S.map₁ here (verifyStep h m e s)
      (s′ , vt) ← S.map₁ (there x ok) (verifyTrace (x′ .next) es)
      return (s′ , ok∷ x ok vt)

    --------------------------------------------------------------------------
    -- Soundness: a valid trace is a run of the machine

    labels : ValidTrace s es s′ → List (Input × Maybe Output)
    labels []                         = []
    labels (ok∷ {m = m} (x , _) _ vt) = (embed m , x .out) ∷ labels vt

    toRun : (vt : ValidTrace s es s′) → Run s (labels vt) s′
    toRun []           = done
    toRun (ok∷ (x , _) _ vt) = x .derivation ∷ toRun vt

    EntryMatches : Entry → Input × Maybe Output → Type
    EntryMatches ⟨ _ , m , e ⟩ (i , o) = embed m ≡ i × Matches e o

    labels-match : (vt : ValidTrace s es s′) → Pointwise EntryMatches es (labels vt)
    labels-match []            = []
    labels-match (ok∷ _ ok vt) = (refl , ok) ∷ labels-match vt

    --------------------------------------------------------------------------
    -- Completeness: with `Complete`, an error rules out every valid trace

    module _ (comp : Complete C) where

      open Complete comp

      private
        out-eq : (x y : StepWith h s (embed m)) → x .proj₁ .out ≡ y .proj₁ .out
        out-eq x y = cong proj₁ (unique x y)

        next-eq : (x y : StepWith h s (embed m)) → x .proj₁ .next ≡ y .proj₁ .next
        next-eq x y = cong proj₂ (unique x y)

      complete : TraceErr s es → ¬ (Σ[ s′ ∈ State ] ValidTrace s es s′)
      complete (here (rejected err)) (_ , ok∷ y _ _) = refute err y
      complete (here {e = e} (output-mismatch x ¬ok)) (_ , ok∷ y ok _) =
        ¬ok (subst (Matches e) (out-eq y x) ok)
      complete (there {es = es} x _ err) (s″ , ok∷ y _ vt) =
        complete err (s″ , subst (λ t → ValidTrace t es s″) (next-eq y x) vt)

      validTrace? : ∀ s es → Dec (Σ[ s′ ∈ State ] ValidTrace s es s′)
      validTrace? s es with verifyTrace s es
      ... | inj₁ err = no (complete err)
      ... | inj₂ vt  = yes vt

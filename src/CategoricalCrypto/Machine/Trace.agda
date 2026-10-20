{-# OPTIONS --safe #-}

-- ============================================================================
-- Generic trace verification for machines.
--
-- A trace is a chronological list of entries, each naming a *hint* and the
-- input the step consumes.  Hints exist because step relations are
-- nondeterministic: a rule may have premises with witnesses that the input
-- does not determine, so the trace has to name them.  Checking a step is
-- then a decision problem rather than a search.
--
-- A machine is made checkable by a `Checkable` record: the hint type, a way
-- to read the hint off a step, and a per-step checker that returns either a
-- machine-specific error or a step carrying that hint.
--
-- From these, once for every machine:
--   * `verifyTrace`, which returns a `ValidTrace` carrying the derivations,
--     or a `TraceErr` locating the first failing entry;
--   * `toRun`, which forgets hints and yields the run of the machine that
--     the trace describes (soundness);
--   * given `Complete` (errors refute, and a hint determines output and
--     target), `complete`, which shows that an error means no run with these
--     hints exists, and `validTrace?`, which decides `ValidTrace`.
--
-- Outputs are checked separately, since they do not influence which run is
-- found.  An `Observation` fixes what is expected of each output, for
-- example equality (`exactOutputs`); `passes?` decides whether the outputs
-- of a valid trace meet a list of expectations, and given `Complete`,
-- `passing?` decides whether any run with these hints does.
-- ============================================================================

module CategoricalCrypto.Machine.Trace where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.Maybe.Properties using () renaming (≡-dec to ≡-decMaybe)
import Data.List as L
import Data.Sum as S
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; []; _∷_)
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

  module Verifier (C : Checkable) where

    open Checkable C

    record Entry : Type where
      constructor ⟨_,_⟩
      field
        hint  : Hint
        input : Msg

    Trace : Type
    Trace = List Entry

    private variable
      s s′ s″ t t′ : State
      h            : Hint
      m            : Msg
      es           : Trace

    -- A trace together with a run of the machine that realises it.
    data ValidTrace : State → Trace → State → Type where
      []  : ValidTrace s [] s
      ok∷ : ((x , _) : StepWith h s (embed m))
          → ValidTrace (x .next) es s′
          → ValidTrace s (⟨ h , m ⟩ ∷ es) s′

    -- The first failing entry, with the valid prefix leading up to it.
    data TraceErr : State → Trace → Type where
      here  : Err h m s → TraceErr s (⟨ h , m ⟩ ∷ es)
      there : ((x , _) : StepWith h s (embed m))
            → TraceErr (x .next) es
            → TraceErr s (⟨ h , m ⟩ ∷ es)

    verifyTrace : ∀ s es → TraceErr s es ⊎ Σ[ s′ ∈ State ] ValidTrace s es s′
    verifyTrace s []               = return (s , [])
    verifyTrace s (⟨ h , m ⟩ ∷ es) = do
      x@(x′ , _) ← S.map₁ here (checkStep h m s)
      (s′ , vt)  ← S.map₁ (there x) (verifyTrace (x′ .next) es)
      return (s′ , ok∷ x vt)

    --------------------------------------------------------------------------
    -- Soundness: a valid trace is a run of the machine

    labels : ValidTrace s es s′ → List (Input × Maybe Output)
    labels []                       = []
    labels (ok∷ {m = m} (x , _) vt) = (embed m , x .out) ∷ labels vt

    toRun : (vt : ValidTrace s es s′) → Run s (labels vt) s′
    toRun []               = done
    toRun (ok∷ (x , _) vt) = x .derivation ∷ toRun vt

    -- The run consumes exactly the trace's inputs, in order.
    EntryInput : Entry → Input × Maybe Output → Type
    EntryInput ⟨ _ , m ⟩ (i , _) = embed m ≡ i

    labels-inputs : (vt : ValidTrace s es s′) → Pointwise EntryInput es (labels vt)
    labels-inputs []         = []
    labels-inputs (ok∷ _ vt) = refl ∷ labels-inputs vt

    outputs : ValidTrace s es s′ → List (Maybe Output)
    outputs vt = L.map proj₂ (labels vt)

    --------------------------------------------------------------------------
    -- Checking outputs: an `Observation` expects something of each output of
    -- the run, in order.  It does not influence which run is found.

    module _ (Ob : Observation) where

      open Observation Ob

      Passes : List Expect → ValidTrace s es s′ → Type
      Passes exps vt = Pointwise Matches exps (outputs vt)

      passes? : ∀ exps (vt : ValidTrace s es s′) → Dec (Passes exps vt)
      passes? exps vt = Pointwise.decidable match? exps (outputs vt)

    --------------------------------------------------------------------------
    -- Completeness: with `Complete`, an error rules out every valid trace,
    -- and the outputs of a valid trace are determined by its entries

    module _ (comp : Complete C) where

      open Complete comp

      private
        out-eq : (x y : StepWith h s (embed m)) → x .proj₁ .out ≡ y .proj₁ .out
        out-eq x y = cong proj₁ (unique x y)

        next-eq : (x y : StepWith h s (embed m)) → x .proj₁ .next ≡ y .proj₁ .next
        next-eq x y = cong proj₂ (unique x y)

      complete : TraceErr s es → ¬ (Σ[ s′ ∈ State ] ValidTrace s es s′)
      complete (here err) (_ , ok∷ y _) = refute err y
      complete (there {es = es} x err) (s″ , ok∷ y vt) =
        complete err (s″ , subst (λ t → ValidTrace t es s″) (next-eq y x) vt)

      validTrace? : ∀ s es → Dec (Σ[ s′ ∈ State ] ValidTrace s es s′)
      validTrace? s es with verifyTrace s es
      ... | inj₁ err = no (complete err)
      ... | inj₂ vt  = yes vt

      private
        outputs-unique′ : (vt : ValidTrace s es s′) (vt′ : ValidTrace t es t′)
                        → s ≡ t → outputs vt ≡ outputs vt′
        outputs-unique′ []         []          _    = refl
        outputs-unique′ (ok∷ x vt) (ok∷ y vt′) refl =
          cong₂ _∷_ (out-eq x y) (outputs-unique′ vt vt′ (next-eq x y))

      -- A hint pins down each step, so all valid traces emit the same outputs.
      outputs-unique : (vt : ValidTrace s es s′) (vt′ : ValidTrace s es s″)
                     → outputs vt ≡ outputs vt′
      outputs-unique vt vt′ = outputs-unique′ vt vt′ refl

      -- Whether some run realises the trace and meets the expectations.
      module _ (Ob : Observation) where

        open Observation Ob

        Passing : State → Trace → List Expect → Type
        Passing s es exps = Σ[ s′ ∈ State ] Σ[ vt ∈ ValidTrace s es s′ ] Passes Ob exps vt

        passing? : ∀ s es exps → Dec (Passing s es exps)
        passing? s es exps with validTrace? s es
        ... | no ¬vt = no λ (s′ , vt , _) → ¬vt (s′ , vt)
        ... | yes (s′ , vt) with passes? Ob exps vt
        ...   | yes ok = yes (s′ , vt , ok)
        ...   | no ¬ok = no λ (_ , vt′ , ok) →
                  ¬ok (subst (Pointwise Matches exps) (outputs-unique vt′ vt) ok)

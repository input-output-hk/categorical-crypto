{-# OPTIONS --safe #-}

-- ============================================================================
-- Composing trace checkers along the machine builders.
--
-- The combinators work on `Checker`s, which check steps on inputs rather
-- than on a flattened `Msg`, because `trᶜ` has to check steps on inputs that
-- were fed back from outputs.  `Verifier` applies to every result.
--
--   * `_⊗ᶜ_`: a step of `M₁ ⊗₁ M₂` is a step of exactly one component, so
--     the hint is `Hint₁ ⊎ Hint₂`.
--   * `trᶜ`: a step of `tr M` is a chain of steps of `M`, each output on the
--     looped channel fed back as the next input, so the hint is a non-empty
--     list of hints of `M`.
--   * `reindexᶜ`: `modifyStepRel p M` steps as `M` does, so the hint is
--     unchanged; the outputs are moved back along a section of `p`.
--   * `_∘ᶜ_`: `M₁ ∘ M₂` is built from the three above, and so is its checker.
--     A hint is the list of internal steps, each naming the machine it is a
--     step of.
--   * `functionᶜ`: function machines, such as `id`, step deterministically.
--
-- Each combinator preserves `Complete` (`⊗ᶜ-complete`, `trᶜ-complete`,
-- `reindexᶜ-complete`, `∘ᶜ-complete`, `functionᶜ-complete`).  Reindexing
-- needs `back` to be a two-sided inverse; the injectivity and disjointness
-- of the ports involved come from left inverses (`which`, `unσ`, `classify`).
-- ============================================================================

module CategoricalCrypto.Machine.Trace.Compose where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_) renaming ([_] to [_]⁺)
import Data.List.NonEmpty as L⁺
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
  using ( Machine; _⊗ᵀ_; _⊗₁_; _∘_; id; FunctionMachine; modifyStepRel
        ; module Tensor; comp-view; CompView; ⊗σ; ∘σ; ∣ˡσ; ∣^ˡσ
        ; tr; TraceRel; Trace[_]; _Trace∷ₒ_; _Trace∷ᵢ_ )
open import CategoricalCrypto.Machine.Trace


-- A map with a left inverse is injective, also under `Maybe`.
<$>-injective : ∀ {X Y : Type} {f : X → Y} (g : Y → X) → (∀ x → g (f x) ≡ x)
              → ∀ {o o′ : Maybe X} → (f <$> o) ≡ (f <$> o′) → o ≡ o′
<$>-injective {X} {Y} {f = f} g gf {o} {o′} eq = trans (sym (gf? o)) (trans (cong (λ (z : Maybe Y) → g <$> z) eq) (gf? o′))
  where
    gf? : (o : Maybe X) → (g <$> (f <$> o)) ≡ o
    gf? nothing  = refl
    gf? (just x) = cong just (gf x)

∷⁺-injʳ : ∀ {X : Type} {a b : X} {xs ys : List⁺ X} → a ∷⁺ xs ≡ b ∷⁺ ys → xs ≡ ys
∷⁺-injʳ refl = refl

------------------------------------------------------------------------------
-- Tensor

module _ {A B C D : Channel} {M₁ : Machine A B} {M₂ : Machine C D} where

  open Tensor M₁ M₂ using (CompRel; Step₁; Step₂)

  private
    M = M₁ ⊗₁ M₂

    σᵢ : Input M → Channel.inType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ))
    σᵢ = app (⊗σ {A} {B} {C} {D} {In})

    σₒ : Output M → Channel.outType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ))
    σₒ = app (⊗σ {A} {B} {C} {D} {Out})

    -- Inputs and outputs of the two components side by side.
    Inner = Channel.inType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ))

    lₒ : Output M₁ → Channel.outType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ))
    lₒ o = ϵ ⊗R ↑ₒ o

    rₒ : Output M₂ → Channel.outType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ))
    rₒ o = L⊗ ϵ ↑ₒ o

  -- Which component an input of the tensor goes to.
  Side : Input M → Type
  Side i = (Σ[ m ∈ Input M₁ ] σᵢ i ≡ ϵ ⊗R ↑ᵢ m) ⊎ (Σ[ m ∈ Input M₂ ] σᵢ i ≡ L⊗ ϵ ↑ᵢ m)

  opaque
    unfolding _⊗₀_

    side : ∀ i → Side i
    side (inj₁ (inj₁ a)) = inj₁ (inj₁ a , refl)
    side (inj₂ (inj₁ b)) = inj₁ (inj₂ b , refl)
    side (inj₁ (inj₂ c)) = inj₂ (inj₁ c , refl)
    side (inj₂ (inj₂ d)) = inj₂ (inj₂ d , refl)

    lift₁ : Output M₁ → Output M
    lift₁ (inj₁ a) = inj₁ (inj₁ a)
    lift₁ (inj₂ b) = inj₂ (inj₁ b)

    lift₂ : Output M₂ → Output M
    lift₂ (inj₁ c) = inj₁ (inj₂ c)
    lift₂ (inj₂ d) = inj₂ (inj₂ d)

    lift₁-σ : ∀ o → σₒ (lift₁ o) ≡ ϵ ⊗R ↑ₒ o
    lift₁-σ (inj₁ _) = refl
    lift₁-σ (inj₂ _) = refl

    lift₂-σ : ∀ o → σₒ (lift₂ o) ≡ L⊗ ϵ ↑ₒ o
    lift₂-σ (inj₁ _) = refl
    lift₂-σ (inj₂ _) = refl

    -- Left inverses, for injectivity and disjointness.
    which : Inner → Input M₁ ⊎ Input M₂
    which x = x

    which-l : ∀ m → which (ϵ ⊗R ↑ᵢ m) ≡ inj₁ m
    which-l _ = refl

    which-r : ∀ m → which (L⊗ ϵ ↑ᵢ m) ≡ inj₂ m
    which-r _ = refl

    unσ : Channel.outType ((A ⊗₀ B ᵀ) ⊗₀ (C ⊗₀ D ᵀ)) → Output M
    unσ (inj₁ o) = lift₁ o
    unσ (inj₂ o) = lift₂ o

    unσ-σ : ∀ o → unσ (σₒ o) ≡ o
    unσ-σ (inj₁ (inj₁ _)) = refl
    unσ-σ (inj₁ (inj₂ _)) = refl
    unσ-σ (inj₂ (inj₁ _)) = refl
    unσ-σ (inj₂ (inj₂ _)) = refl

  private
    lift₁-σ? : (o : Maybe (Output M₁)) → (ϵ ⊗R ↑ₒ_ <$> o) ≡ (σₒ <$> (lift₁ <$> o))
    lift₁-σ? nothing  = refl
    lift₁-σ? (just o) = cong just (sym (lift₁-σ o))

    lift₂-σ? : (o : Maybe (Output M₂)) → (L⊗ ϵ ↑ₒ_ <$> o) ≡ (σₒ <$> (lift₂ <$> o))
    lift₂-σ? nothing  = refl
    lift₂-σ? (just o) = cong just (sym (lift₂-σ o))

    l-inj : ∀ {m m′} → _≡_ {A = Inner} (ϵ ⊗R ↑ᵢ m) (ϵ ⊗R ↑ᵢ m′) → m ≡ m′
    l-inj eq = inj₁-injective (trans (sym (which-l _)) (trans (cong which eq) (which-l _)))

    r-inj : ∀ {m m′} → _≡_ {A = Inner} (L⊗ ϵ ↑ᵢ m) (L⊗ ϵ ↑ᵢ m′) → m ≡ m′
    r-inj eq = inj₂-injective (trans (sym (which-r _)) (trans (cong which eq) (which-r _)))

    l≢r : ∀ {m m′} → _≡_ {A = Inner} (ϵ ⊗R ↑ᵢ m) (L⊗ ϵ ↑ᵢ m′) → ⊥
    l≢r eq with () ← trans (sym (which-l _)) (trans (cong which eq) (which-r _))

  module _ (C₁ : Checker M₁) (C₂ : Checker M₂) where

    private
      module C₁ = Checkable C₁
      module C₂ = Checkable C₂

    Hint⊗ = C₁.Hint ⊎ C₂.Hint

    private
      viewHint : ∀ {s x y s′} → CompView M₁ M₂ s x y s′ → Hint⊗
      viewHint (inj₁ (_ , _ , _ , _ , _ , d)) = inj₁ (C₁.hintOf (step _ _ d))
      viewHint (inj₂ (_ , _ , _ , _ , _ , d)) = inj₂ (C₂.hintOf (step _ _ d))

      -- Moving a derivation along its indices does not change its hint.
      viewHint-subst : ∀ {s x x′ y y′ s′} (ex : x ≡ x′) (ey : y ≡ y′) (r : CompRel s x y s′)
                     → viewHint (comp-view (subst₂ (λ x y → CompRel s x y s′) ex ey r))
                     ≡ viewHint (comp-view r)
      viewHint-subst refl refl _ = refl

    -- An input on one component with a hint for the other.
    data WrongSide : Type where
      wrong-side : WrongSide

    private
      ErrAt : ∀ {i} → Hint⊗ → Side i → Machine.State M → Type
      ErrAt (inj₁ h) (inj₁ (m , _)) (s₁ , _) = C₁.Err h m s₁
      ErrAt (inj₂ h) (inj₂ (m , _)) (_ , s₂) = C₂.Err h m s₂
      ErrAt (inj₁ _) (inj₂ _)       _        = WrongSide
      ErrAt (inj₂ _) (inj₁ _)       _        = WrongSide

    _⊗ᶜ_ : Checker M
    _⊗ᶜ_ = record { Hint = Hint⊗ ; hintOf = hintOf ; Err = Err ; checkStep = check }
      where
        hintOf : ∀ {s i} → Step M s i → Hint⊗
        hintOf x = viewHint (comp-view (x .derivation))

        Err : Hint⊗ → Input M → Machine.State M → Type
        Err h i s = ErrAt h (side i) s

        check : ∀ h i s → Err h i s ⊎ Σ[ x ∈ Step M s i ] hintOf x ≡ h
        check h i s@(s₁ , s₂) with side i | h
        ... | inj₁ _ | inj₂ _ = inj₁ wrong-side
        ... | inj₂ _ | inj₁ _ = inj₁ wrong-side
        ... | inj₁ (m , eq) | inj₁ h₁ with C₁.checkStep h₁ m s₁
        ...   | inj₁ err = inj₁ err
        ...   | inj₂ (step o s₁′ d , refl) =
                inj₂ ( step (lift₁ <$> o) (s₁′ , s₂)
                         (subst₂ (λ x y → CompRel s x y (s₁′ , s₂)) (sym eq) (lift₁-σ? o) (Step₁ d))
                     , viewHint-subst (sym eq) (lift₁-σ? o) (Step₁ d) )
        check h i s@(s₁ , s₂) | inj₂ (m , eq) | inj₂ h₂ with C₂.checkStep h₂ m s₂
        ...   | inj₁ err = inj₁ err
        ...   | inj₂ (step o s₂′ d , refl) =
                inj₂ ( step (lift₂ <$> o) (s₁ , s₂′)
                         (subst₂ (λ x y → CompRel s x y (s₁ , s₂′)) (sym eq) (lift₂-σ? o) (Step₂ d))
                     , viewHint-subst (sym eq) (lift₂-σ? o) (Step₂ d) )

    ⊗ᶜ-complete : Complete _ C₁ → Complete _ C₂ → Complete _ _⊗ᶜ_
    ⊗ᶜ-complete k₁ k₂ = record { refute = refute ; unique = unique }
      where
        module K₁ = Complete k₁
        module K₂ = Complete k₂

        StepWith⊗ : Hint⊗ → Machine.State M → Input M → Type
        StepWith⊗ h s i = Σ[ x ∈ Step M s i ] viewHint (comp-view (x .derivation)) ≡ h

        refute : ∀ {h i s} → ErrAt h (side i) s → ¬ StepWith⊗ h s i
        refute {h} {i} err (step _ _ d , hx) with side i | h | comp-view d
        refute err (step _ _ _ , hx) | inj₁ (_ , eq) | inj₁ _ | inj₁ (_ , _ , ex , _ , _ , d₁)
          with refl ← l-inj (trans (sym eq) ex) = K₁.refute err (step _ _ d₁ , inj₁-injective hx)
        refute err (step _ _ _ , hx) | inj₂ (_ , eq) | inj₂ _ | inj₂ (_ , _ , ex , _ , _ , d₂)
          with refl ← r-inj (trans (sym eq) ex) = K₂.refute err (step _ _ d₂ , inj₂-injective hx)
        refute _ (step _ _ _ , _)  | inj₂ (_ , eq) | inj₁ _ | inj₁ (_ , _ , ex , _) = l≢r (trans (sym ex) eq)
        refute _ (step _ _ _ , _)  | inj₁ (_ , eq) | inj₂ _ | inj₂ (_ , _ , ex , _) = l≢r (trans (sym eq) ex)
        refute _ (step _ _ _ , ()) | _ | inj₁ _ | inj₂ _
        refute _ (step _ _ _ , ()) | _ | inj₂ _ | inj₁ _

        unique : ∀ {h i s} (x y : StepWith⊗ h s i)
               → (x .proj₁ .out , x .proj₁ .next) ≡ (y .proj₁ .out , y .proj₁ .next)
        unique (step _ _ d , hx) (step _ _ d′ , hy) with comp-view d | comp-view d′
        unique (step _ _ _ , hx) (step _ _ _ , hy)
          | inj₁ (_ , mo , ex , ey , es , d₁) | inj₁ (_ , mo′ , ex′ , ey′ , es′ , d₁′)
          with refl ← l-inj (trans (sym ex) ex′) =
            let u = K₁.unique (step mo _ d₁ , inj₁-injective (trans hx (sym hy))) (step mo′ _ d₁′ , refl)
            in cong₂ _,_ (<$>-injective unσ unσ-σ (trans ey (trans (cong (λ (z : Maybe (Output M₁)) → lₒ <$> z) (cong proj₁ u)) (sym ey′))))
                         (cong₂ _,_ (cong proj₂ u) (trans es (sym es′)))
        unique (step _ _ _ , hx) (step _ _ _ , hy)
          | inj₂ (_ , mo , ex , ey , es , d₂) | inj₂ (_ , mo′ , ex′ , ey′ , es′ , d₂′)
          with refl ← r-inj (trans (sym ex) ex′) =
            let u = K₂.unique (step mo _ d₂ , inj₂-injective (trans hx (sym hy))) (step mo′ _ d₂′ , refl)
            in cong₂ _,_ (<$>-injective unσ unσ-σ (trans ey (trans (cong (λ (z : Maybe (Output M₂)) → rₒ <$> z) (cong proj₁ u)) (sym ey′))))
                         (cong₂ _,_ (trans es (sym es′)) (cong proj₂ u))
        unique (step _ _ _ , hx) (step _ _ _ , hy) | inj₁ _ | inj₂ _ with () ← trans hx (sym hy)
        unique (step _ _ _ , hx) (step _ _ _ , hy) | inj₂ _ | inj₁ _ with () ← trans hx (sym hy)

------------------------------------------------------------------------------
-- Trace

module _ {A B C : Channel} {M : Machine (A ⊗₀ C) (B ⊗₀ C)} where

  open Machine M using (State)

  private
    Tr = tr M

    -- How inputs and outputs of `tr M` sit inside those of `M`, as in the
    -- step relation of `tr M`.
    lowerᵢ : Input Tr → Input M
    lowerᵢ i = app (∣ˡσ {A} {C} {B ⊗₀ C} {In}) (app (∣^ˡσ {A} {B} {C} {In}) i)

    lowerₒ : Maybe (Output Tr) → Maybe (Output M)
    lowerₒ o = app (∣ˡσ {A} {C} {B ⊗₀ C} {Out}) <$> (app (∣^ˡσ {A} {B} {C} {Out}) <$> o)

    -- The two feedback wires, as in `_Trace∷ₒ_` and `_Trace∷ᵢ_`.
    outₒ : Channel.outType C → Output M
    outₒ c = (L⊗ ϵ) ⊗R ↑ₒ c

    inₒ : Channel.outType C → Input M
    inₒ c = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ c

    outᵢ : Channel.inType C → Output M
    outᵢ c = L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ c

    inᵢ : Channel.inType C → Input M
    inᵢ c = (L⊗ ϵ) ⊗R ↑ᵢ c

  -- Where an output of `M` goes: out of `tr M`, or back into `M`.
  data Route : Maybe (Output M) → Type where
    halt  : ∀ o → Route (lowerₒ o)
    loopₒ : ∀ c → Route (just (outₒ c))
    loopᵢ : ∀ c → Route (just (outᵢ c))

  opaque
    unfolding _⊗₀_

    route : ∀ o → Route o
    route nothing                   = halt nothing
    route (just (inj₁ (inj₁ a)))    = halt (just (inj₁ a))
    route (just (inj₂ (inj₁ b)))    = halt (just (inj₂ b))
    route (just (inj₁ (inj₂ c)))    = loopₒ c
    route (just (inj₂ (inj₂ c)))    = loopᵢ c

  feedback : ∀ {o} → Route o → Maybe (Input M)
  feedback (halt _)  = nothing
  feedback (loopₒ c) = just (inₒ c)
  feedback (loopᵢ c) = just (inᵢ c)

  opaque
    unfolding route

    route-lowerₒ : ∀ o → route (lowerₒ o) ≡ halt o
    route-lowerₒ nothing         = refl
    route-lowerₒ (just (inj₁ _)) = refl
    route-lowerₒ (just (inj₂ _)) = refl

    route-outₒ : ∀ c → route (just (outₒ c)) ≡ loopₒ c
    route-outₒ _ = refl

    route-outᵢ : ∀ c → route (just (outᵢ c)) ≡ loopᵢ c
    route-outᵢ _ = refl

  private
    -- `route` without the index, so that its results can be compared.
    classify : Maybe (Output M) → Maybe (Output Tr) ⊎ (Channel.outType C ⊎ Channel.inType C)
    classify o = kind (route o)
      where
        kind : ∀ {o} → Route o → Maybe (Output Tr) ⊎ (Channel.outType C ⊎ Channel.inType C)
        kind (halt o)  = inj₁ o
        kind (loopₒ c) = inj₂ (inj₁ c)
        kind (loopᵢ c) = inj₂ (inj₂ c)

    classify-lowerₒ : ∀ {o} → classify (lowerₒ o) ≡ inj₁ o
    classify-lowerₒ {o} rewrite route-lowerₒ o = refl

    classify-outₒ : ∀ {c} → classify (just (outₒ c)) ≡ inj₂ (inj₁ c)
    classify-outₒ {c} rewrite route-outₒ c = refl

    classify-outᵢ : ∀ {c} → classify (just (outᵢ c)) ≡ inj₂ (inj₂ c)
    classify-outᵢ {c} rewrite route-outᵢ c = refl

    -- Where the output of a step is fed back, read off an equal output.
    feedback-≡ : ∀ {x y} → x ≡ y → feedback (route x) ≡ feedback (route y)
    feedback-≡ refl = refl

  module _ (CM : Checker M) where

    open Checkable CM

    hintsOf : ∀ {s i o s′} → TraceRel M s i o s′ → List⁺ Hint
    hintsOf Trace[ d ]    = [ hintOf (step _ _ d) ]⁺
    hintsOf (d Trace∷ₒ r) = hintOf (step _ _ d) ∷⁺ hintsOf r
    hintsOf (d Trace∷ᵢ r) = hintOf (step _ _ d) ∷⁺ hintsOf r

    private variable
      h h′ : Hint
      hs   : List Hint
      i j  : Input M
      s    : State

    -- The first internal step that fails, after the valid ones before it.
    data TrErr : List⁺ Hint → Input M → State → Type where
      here  : Err h i s → TrErr (h ∷ hs) i s
      there : ((x , _) : StepWith h s i) → feedback (route (x .out)) ≡ just j
            → TrErr (h′ ∷ hs) j (x .next) → TrErr (h ∷ h′ ∷ hs) i s
      -- The output is fed back, but no hint is left for the next step.
      short : ((x , _) : StepWith h s i) → feedback (route (x .out)) ≡ just j
            → TrErr (h ∷ []) i s
      -- The output leaves `tr M`, but hints are left over.
      long  : ((x , _) : StepWith h s i) → feedback (route (x .out)) ≡ nothing
            → TrErr (h ∷ h′ ∷ hs) i s

    private
      -- Either a failing internal step, or the chain of internal steps that
      -- makes up one step of `tr M`.
      Loop : List⁺ Hint → Input M → State → Type
      Loop hs i s = TrErr hs i s
                  ⊎ Σ[ o ∈ Maybe (Output Tr) ] Σ[ s′ ∈ State ]
                    Σ[ r ∈ TraceRel M s i (lowerₒ o) s′ ] hintsOf r ≡ hs

      loop : ∀ h hs i s → Loop (h ∷ hs) i s

      -- After one internal step, stop or feed its output back.
      continue : ∀ hs (x : StepWith h s i) (w : Route (x .proj₁ .out))
               → route (x .proj₁ .out) ≡ w → Loop (h ∷ hs) i s

      loop h hs i s with checkStep h i s
      ... | inj₁ err = inj₁ (here err)
      ... | inj₂ x   = continue hs x (route _) refl

      continue []         (step _ s′ d , refl) (halt o′) _  = inj₂ (o′ , s′ , Trace[ d ] , refl)
      continue (_ ∷ _)    x@(step _ _ _ , _)   (halt _)  eq = inj₁ (long x (cong feedback eq))
      continue []         x@(step _ _ _ , _)   (loopₒ _) eq = inj₁ (short x (cong feedback eq))
      continue []         x@(step _ _ _ , _)   (loopᵢ _) eq = inj₁ (short x (cong feedback eq))
      continue (h′ ∷ hs′) x@(step _ s′ d , refl) (loopₒ c) eq with loop h′ hs′ (inₒ c) s′
      ... | inj₁ err                 = inj₁ (there x (cong feedback eq) err)
      ... | inj₂ (o′ , s″ , r , eq′) = inj₂ (o′ , s″ , d Trace∷ₒ r , cong (_ ∷⁺_) eq′)
      continue (h′ ∷ hs′) x@(step _ s′ d , refl) (loopᵢ c) eq with loop h′ hs′ (inᵢ c) s′
      ... | inj₁ err                 = inj₁ (there x (cong feedback eq) err)
      ... | inj₂ (o′ , s″ , r , eq′) = inj₂ (o′ , s″ , d Trace∷ᵢ r , cong (_ ∷⁺_) eq′)

    trᶜ : Checker Tr
    trᶜ = record
      { Hint      = List⁺ Hint
      ; hintOf    = λ x → hintsOf (x .derivation)
      ; Err       = λ hs i → TrErr hs (lowerᵢ i)
      ; checkStep = λ where
          (h ∷ hs) i s → case loop h hs (lowerᵢ i) s of λ where
            (inj₁ err)               → inj₁ err
            (inj₂ (o , s′ , r , eq)) → inj₂ (step o s′ r , eq)
      }

    module _ (k : Complete _ CM) where

      open Complete k

      private
        -- An error rules out every chain of internal steps with these hints.
        refuteTr : ∀ {hs j s o s″} → TrErr hs j s
                 → (r : TraceRel M s j (lowerₒ o) s″) → hintsOf r ≡ hs → ⊥
        refuteTr (here err) Trace[ d ]    eq = refute err (step _ _ d , cong L⁺.head eq)
        refuteTr (here err) (d Trace∷ₒ _) eq = refute err (step _ _ d , cong L⁺.head eq)
        refuteTr (here err) (d Trace∷ᵢ _) eq = refute err (step _ _ d , cong L⁺.head eq)
        refuteTr {o = o} (there x fb err) (_Trace∷ₒ_ {outC = c} d r) eq =
          let u  = unique (step _ _ d , cong L⁺.head eq) x
              fb′ = trans (sym (cong feedback (route-outₒ c))) (trans (feedback-≡ (cong proj₁ u)) fb)
          in refuteTr {o = o} (subst₂ (TrErr _) (just-injective (sym fb′)) (sym (cong proj₂ u)) err) r (∷⁺-injʳ eq)
        refuteTr {o = o} (there x fb err) (_Trace∷ᵢ_ {inC = c} d r) eq =
          let u  = unique (step _ _ d , cong L⁺.head eq) x
              fb′ = trans (sym (cong feedback (route-outᵢ c))) (trans (feedback-≡ (cong proj₁ u)) fb)
          in refuteTr {o = o} (subst₂ (TrErr _) (just-injective (sym fb′)) (sym (cong proj₂ u)) err) r (∷⁺-injʳ eq)
        refuteTr (there _ _ _) Trace[ _ ] eq with () ← cong L⁺.tail eq
        refuteTr {o = o} (short x fb) Trace[ d ] eq
          with () ← trans (sym (cong feedback (route-lowerₒ o)))
                          (trans (feedback-≡ (cong proj₁ (unique (step _ _ d , cong L⁺.head eq) x))) fb)
        refuteTr (short _ _) (_ Trace∷ₒ _) eq with () ← cong L⁺.tail eq
        refuteTr (short _ _) (_ Trace∷ᵢ _) eq with () ← cong L⁺.tail eq
        refuteTr (long _ _) Trace[ _ ] eq with () ← cong L⁺.tail eq
        refuteTr (long x fb) (_Trace∷ₒ_ {outC = c} d _) eq
          with () ← trans (sym (cong feedback (route-outₒ c)))
                          (trans (feedback-≡ (cong proj₁ (unique (step _ _ d , cong L⁺.head eq) x))) fb)
        refuteTr (long x fb) (_Trace∷ᵢ_ {inC = c} d _) eq
          with () ← trans (sym (cong feedback (route-outᵢ c)))
                          (trans (feedback-≡ (cong proj₁ (unique (step _ _ d , cong L⁺.head eq) x))) fb)

        -- Two chains with the same hints are the same chain.
        uniqueTr : ∀ {s j o o′ s₁ s₂}
                   (r : TraceRel M s j (lowerₒ o) s₁) (r′ : TraceRel M s j (lowerₒ o′) s₂)
                 → hintsOf r ≡ hintsOf r′ → (o , s₁) ≡ (o′ , s₂)
        uniqueTr Trace[ d ] Trace[ d′ ] eq =
          let u = unique (step _ _ d , cong L⁺.head eq) (step _ _ d′ , refl)
          in cong₂ _,_ (inj₁-injective (trans (sym classify-lowerₒ)
                                              (trans (cong classify (cong proj₁ u)) classify-lowerₒ)))
                       (cong proj₂ u)
        uniqueTr {o = o} {o′} (d Trace∷ₒ r) (d′ Trace∷ₒ r′) eq
          with u ← unique (step _ _ d , cong L⁺.head eq) (step _ _ d′ , refl)
          with refl ← inj₁-injective (inj₂-injective (trans (sym classify-outₒ)
                                                       (trans (cong classify (cong proj₁ u)) classify-outₒ)))
             | refl ← cong proj₂ u
          = uniqueTr {o = o} {o′} r r′ (∷⁺-injʳ eq)
        uniqueTr {o = o} {o′} (d Trace∷ᵢ r) (d′ Trace∷ᵢ r′) eq
          with u ← unique (step _ _ d , cong L⁺.head eq) (step _ _ d′ , refl)
          with refl ← inj₂-injective (inj₂-injective (trans (sym classify-outᵢ)
                                                       (trans (cong classify (cong proj₁ u)) classify-outᵢ)))
             | refl ← cong proj₂ u
          = uniqueTr {o = o} {o′} r r′ (∷⁺-injʳ eq)
        uniqueTr (d Trace∷ₒ _) (d′ Trace∷ᵢ _) eq
          with () ← trans (sym classify-outₒ)
                          (trans (cong classify (cong proj₁ (unique (step _ _ d , cong L⁺.head eq) (step _ _ d′ , refl))))
                                 classify-outᵢ)
        uniqueTr (d Trace∷ᵢ _) (d′ Trace∷ₒ _) eq
          with () ← trans (sym classify-outᵢ)
                          (trans (cong classify (cong proj₁ (unique (step _ _ d , cong L⁺.head eq) (step _ _ d′ , refl))))
                                 classify-outₒ)
        uniqueTr Trace[ _ ] (_ Trace∷ₒ _) eq with () ← cong L⁺.tail eq
        uniqueTr Trace[ _ ] (_ Trace∷ᵢ _) eq with () ← cong L⁺.tail eq
        uniqueTr (_ Trace∷ₒ _) Trace[ _ ] eq with () ← cong L⁺.tail eq
        uniqueTr (_ Trace∷ᵢ _) Trace[ _ ] eq with () ← cong L⁺.tail eq

      trᶜ-complete : Complete _ trᶜ
      trᶜ-complete = record
        { refute = λ where err (step o _ r , eq) → refuteTr {o = o} err r eq
        ; unique = λ where (step o _ r , ex) (step o′ _ r′ , ey) → uniqueTr {o = o} {o′} r r′ (trans ex (sym ey))
        }

------------------------------------------------------------------------------
-- Reindexing

module _ {A B C D : Channel} {M : Machine A B}
         (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
         (back : ∀ o → Σ[ o′ ∈ Channel.outType (C ⊗₀ D ᵀ) ] app (p {Out}) o′ ≡ o) where

  open Machine M using (stepRel)

  private
    M′ = modifyStepRel p M

    back? : (o : Maybe (Output M)) → Σ[ o′ ∈ Maybe (Output M′) ] (app (p {Out}) <$> o′) ≡ o
    back? nothing  = nothing , refl
    back? (just o) = let (o′ , eq) = back o in just o′ , cong just eq

  module _ (CM : Checker M) where

    open Checkable CM

    private
      hintOf′ : ∀ {s i} → Step M′ s i → Hint
      hintOf′ (step _ s′ d) = hintOf (step _ s′ d)

      -- Moving a derivation along its output does not change its hint.
      hint-subst : ∀ {s i o o′ s′} (eq : o ≡ o′) (d : stepRel s i o s′)
                 → hintOf (step o′ s′ (subst (λ y → stepRel s i y s′) eq d)) ≡ hintOf (step o s′ d)
      hint-subst refl _ = refl

      check′ : ∀ h i s → Err h (app (p {In}) i) s ⊎ Σ[ x ∈ Step M′ s i ] hintOf′ x ≡ h
      check′ h i s with checkStep h (app (p {In}) i) s
      ... | inj₁ err = inj₁ err
      ... | inj₂ (step o s′ d , eq) with back? o
      ...   | o′ , eq′ = inj₂ ( step o′ s′ (subst (λ y → stepRel s (app (p {In}) i) y s′) (sym eq′) d)
                              , trans (hint-subst (sym eq′) d) eq )

    reindexᶜ : Checker M′
    reindexᶜ = record
      { Hint      = Hint
      ; hintOf    = hintOf′
      ; Err       = λ h i → Err h (app (p {In}) i)
      ; checkStep = check′
      }

    -- Completeness needs `back` to be a two-sided inverse, so that `p` is
    -- injective on outputs.
    reindexᶜ-complete : (∀ o → back (app (p {Out}) o) .proj₁ ≡ o) → Complete _ CM → Complete _ reindexᶜ
    reindexᶜ-complete back-app k = record
      { refute = λ err x → refute err (down x)
      ; unique = λ x y → let u = unique (down x) (down y) in
          cong₂ _,_ (<$>-injective {f = app (p {Out})} (λ o → back o .proj₁) back-app (cong proj₁ u))
                    (cong proj₂ u)
      }
      where
        open Complete k

        -- A step of `M′` is a step of `M`, with the same hint.
        down : ∀ {h s i} → Σ[ x ∈ Step M′ s i ] hintOf′ x ≡ h
             → Σ[ x ∈ Step M s (app (p {In}) i) ] hintOf x ≡ h
        down (step _ s′ d , eq) = step _ s′ d , eq

------------------------------------------------------------------------------
-- Sequential composition

opaque
  unfolding _⊗₀_

  ∘σ-back : ∀ {A B C} (o : Channel.outType ((A ⊗₀ B) ⊗₀ (B ⊗₀ C) ᵀ))
          → Σ[ o′ ∈ Channel.outType ((A ⊗₀ B) ⊗₀ (C ⊗₀ B) ᵀ) ] app (∘σ {A} {B} {C} {Out}) o′ ≡ o
  ∘σ-back (inj₁ (inj₁ a)) = inj₁ (inj₁ a) , refl
  ∘σ-back (inj₁ (inj₂ b)) = inj₁ (inj₂ b) , refl
  ∘σ-back (inj₂ (inj₁ b)) = inj₂ (inj₂ b) , refl
  ∘σ-back (inj₂ (inj₂ c)) = inj₂ (inj₁ c) , refl

  ∘σ-back-app : ∀ {A B C} o → ∘σ-back {A} {B} {C} (app (∘σ {A} {B} {C} {Out}) o) .proj₁ ≡ o
  ∘σ-back-app (inj₁ (inj₁ _)) = refl
  ∘σ-back-app (inj₁ (inj₂ _)) = refl
  ∘σ-back-app (inj₂ (inj₁ _)) = refl
  ∘σ-back-app (inj₂ (inj₂ _)) = refl

infixr 9 _∘ᶜ_
_∘ᶜ_ : ∀ {A B C} {M₁ : Machine B C} {M₂ : Machine A B}
     → Checker M₁ → Checker M₂ → Checker (M₁ ∘ M₂)
_∘ᶜ_ {A} {B} {C} C₁ C₂ = trᶜ (reindexᶜ (∘σ {A} {B} {C}) ∘σ-back (C₂ ⊗ᶜ C₁))

∘ᶜ-complete : ∀ {A B C} {M₁ : Machine B C} {M₂ : Machine A B} {C₁ : Checker M₁} {C₂ : Checker M₂}
            → Complete _ C₁ → Complete _ C₂ → Complete _ (C₁ ∘ᶜ C₂)
∘ᶜ-complete {A} {B} {C} {C₁ = C₁} {C₂} k₁ k₂ =
  trᶜ-complete _ (reindexᶜ-complete (∘σ {A} {B} {C}) ∘σ-back _ ∘σ-back-app (⊗ᶜ-complete C₂ C₁ k₂ k₁))

------------------------------------------------------------------------------
-- Function machines

module _ {A B : Channel} where

  functionᶜ : (f : Channel.inType (A ⊗ᵀ B) → Maybe (Channel.outType (A ⊗ᵀ B)))
            → Checker (FunctionMachine {A} {B} f)
  functionᶜ f = record
    { Hint      = ⊤
    ; hintOf    = λ _ → tt
    ; Err       = λ _ _ _ → ⊥
    ; checkStep = λ _ i _ → inj₂ (step (f i) tt refl , refl)
    }

  functionᶜ-complete : ∀ f → Complete _ (functionᶜ f)
  functionᶜ-complete f = record
    { refute = λ ()
    ; unique = λ where (step _ _ refl , _) (step _ _ refl , _) → refl
    }

idᶜ : ∀ {A} → Checker (id {A})
idᶜ = functionᶜ _

idᶜ-complete : ∀ {A} → Complete _ (idᶜ {A})
idᶜ-complete = functionᶜ-complete _

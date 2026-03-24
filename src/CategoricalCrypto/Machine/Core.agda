{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
{-# OPTIONS -v allTactics:100 #-}

module CategoricalCrypto.Machine.Core where

open import categorical-crypto.Prelude hiding (id; _∘_)
import categorical-crypto.Prelude as P
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import Relation.Binary.PropositionalEquality.Properties
open import Tactic.Defaults

-- --------------------------------------------------------------------------------
-- -- Machines, which form the morphisms

machine-type : Type → Channel → Type₁
machine-type S A = let open Channel A in S → inType → Maybe outType → S → Type

_⊗ᵀ_ : Fun₂ Channel
A ⊗ᵀ B = A ⊗₀ B ᵀ

MachineType : Channel → Channel → Type → Type₁
MachineType A B S = machine-type S (A ⊗ᵀ B)

record Machine (A B : Channel) : Type₁ where
  constructor MkMachine

  machine-channel = A ⊗ᵀ B

  field
    {State} : Type
    stepRel : machine-type State machine-channel

-- This module exposes various ways of building machines
-- TODO: all of these are functors from the appropriate categories
module _ {A B : Channel} (let open Channel (A ⊗ᵀ B)) where

  StatelessMachine      : (inType → Maybe outType → Type)          → Machine A B
  FunctionMachine       : (inType → Maybe outType)                 → Machine A B
  TotalFunctionMachine  : A ⊗₀ B ᵀ [ In ]⇒[ Out ] A ⊗₀ B ᵀ          → Machine A B
  TotalFunctionMachine' : A [ In ]⇒[ In ] B → B [ Out ]⇒[ Out ] A  → Machine A B
  
  StatelessMachine      R   = MkMachine {State = ⊤} $ λ _ i o _ → R i o
  FunctionMachine       f   = StatelessMachine      $ λ i → f i ≡_
  TotalFunctionMachine  p   = FunctionMachine       $ just P.∘ app p
  TotalFunctionMachine' p q = TotalFunctionMachine  $ ⊗-combine {In} {Out} (p ⇒ₜ ⇒-negate-transpose-right) (⇒-transpose-left-negate-right ⇒ₜ q) ⇒ₜ ⊗-sym
  -- TotalFunctionMachine' forces all messages to go 'through' the machine, i.e.
  -- messages on the domain become messages on the codomain and vice versa if
  -- e.g. A ≡ B then it's easy to accidentally send a message the wrong way
  -- which is prevented here

id : ∀ {A} → Machine A A
id = TotalFunctionMachine' ⇒-solver ⇒-solver

-- given transformation on the channels, transform the machine
modifyStepRel : ∀ {A B C D} → (∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ) → Machine A B → Machine C D
modifyStepRel p (MkMachine stepRel) = MkMachine $ \s m m' s' → stepRel s (app {mᵢ = In} p m) (app {mₒ = Out} p <$> m') s'

module Tensor {A B C D} (M₁ : Machine A B) (M₂ : Machine C D) where
  open Machine M₁ renaming (State to State₁; stepRel to stepRel₁; machine-channel to machine-channel₁)
  open Machine M₂ renaming (State to State₂; stepRel to stepRel₂; machine-channel to machine-channel₂)

  State = State₁ × State₂
  AllCs = machine-channel₁ ⊗₀ machine-channel₂

  data CompRel : machine-type State AllCs where
    Step₁ : ∀ {m m' s s' s₂} → stepRel₁ s m m' s' → CompRel (s , s₂) (ϵ ⊗R ↑ᵢ m) (ϵ ⊗R ↑ₒ_ <$> m') (s' , s₂)
    Step₂ : ∀ {m m' s s' s₁} → stepRel₂ s m m' s' → CompRel (s₁ , s) (L⊗ ϵ ↑ᵢ m) (L⊗ ϵ ↑ₒ_ <$> m') (s₁ , s')

  infixr 9 _⊗₁_
  _⊗₁_ : Machine (A ⊗₀ C) (B ⊗₀ D)
  _⊗₁_ = modifyStepRel ⇒-solver machine-inter
    where
      machine-inter : Machine (A ⊗₀ B ᵀ) ((C ⊗₀ D ᵀ) ᵀ)
      machine-inter = MkMachine CompRel
   
open Tensor using (_⊗₁_) public

_⊗ˡ_ : ∀ {A B} (C : Channel) → Machine A B → Machine (C ⊗₀ A) (C ⊗₀ B)
C ⊗ˡ M = id ⊗₁ M

_⊗ʳ_ : ∀ {A B} → Machine A B → (C : Channel) → Machine (A ⊗₀ C) (B ⊗₀ C)
M ⊗ʳ C = M ⊗₁ id

_∣ˡ : ∀ {A B C} → Machine (A ⊗₀ B) C → Machine A C
_∣ˡ = modifyStepRel ⇒-solver

_∣ʳ : ∀ {A B C} → Machine (A ⊗₀ B) C → Machine B C
_∣ʳ = modifyStepRel ⇒-solver

_∣^ˡ : ∀ {A B C} → Machine A (B ⊗₀ C) → Machine A B
_∣^ˡ = modifyStepRel ⇒-solver
  
_∣^ʳ : ∀ {A B C} → Machine A (B ⊗₀ C) → Machine A C
_∣^ʳ = modifyStepRel ⇒-solver

liftᴷ : ∀ {A B E} → Machine A B → Machine A (B ⊗₀ E)
liftᴷ {E = E} M = (M ⊗ʳ E) ∣ˡ

-- trace monoidal category?
-- What happens when you compose with a trace ?
-- Product of the traces ?
-- The regular composition "eats" messages
-- Trace: input-output behavior of the machines, list of messages
module _ {A B C} (M : Machine (A ⊗₀ C) (B ⊗₀ C)) (let open Machine M) where

  data TraceRel : machine-type State ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C)) where

    Trace[_] : ∀ {s inM outM s'} → stepRel s inM outM s' → TraceRel s inM outM s'

    _Trace∷ₒ_ : ∀ {s s' s'' inM outC outMₘ} → stepRel s inM (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s' →
                                             TraceRel s' (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ᵢ outC) outMₘ s'' →
                                             TraceRel s inM outMₘ s''
                                        
    _Trace∷ᵢ_ : ∀ {s s' s'' inM inC outMₘ} → stepRel s inM (just (L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹ ↑ₒ inC)) s' →
                                            TraceRel s' ((L⊗ ϵ) ⊗R ↑ᵢ inC) outMₘ s'' →
                                            TraceRel s inM outMₘ s''

  tr : Machine A B
  tr = MkMachine TraceRel ∣ˡ ∣^ˡ

infixr 9 _∘_

_∘_ : ∀ {B C A} → Machine B C → Machine A B → Machine A C
_∘_ {B} M₁ M₂ = tr {C = B} $ modifyStepRel ⇒-solver (M₂ ⊗₁ M₁)

⊗-assoc : ∀ {A B C} → Machine ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
⊗-assoc = TotalFunctionMachine' ⇒-solver ⇒-solver
  
⊗-assoc⃖ : ∀ {A B C} → Machine (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
⊗-assoc⃖ = TotalFunctionMachine' ⇒-solver ⇒-solver

⊗-symₘ : ∀ {A B} → Machine (A ⊗₀ B) (B ⊗₀ A)
⊗-symₘ = TotalFunctionMachine' ⇒-solver ⇒-solver

idᴷ : ∀ {A} → Machine A (A ⊗₀ I)
idᴷ = liftᴷ id

transpose : ∀ {A B} → Machine A B → Machine (B ᵀ) (A ᵀ)
transpose = modifyStepRel ⇒-solver
 
-- cup : Machine I (A ⊗ A ᵀ)
-- cup = StatelessMachine λ x x₁ → {!!}

-- cap : Machine (A ᵀ ⊗ A) I
-- cap {A} = modifyStepRel ⇒-solver (transpose (cup {A})) {!!} {!!}

⨂₁ : ∀ {n} → {A B : Fin n → Channel} → ((k : Fin n) → Machine (A k) (B k)) → Machine (⨂ A) (⨂ B)
⨂₁ {zero} M = id
⨂₁ {suc n} M = M fzero ⊗₁ ⨂₁ (M P.∘ fsuc)


infixr 9 _∘ᴷ_
_∘ᴷ_ : ∀ {A B C E₁ E₂} → Machine B (C ⊗₀ E₂) → Machine A (B ⊗₀ E₁) → Machine A (C ⊗₀ (E₁ ⊗₀ E₂))
_∘ᴷ_ {E₁ = E₁} M₂ M₁ = TotalFunctionMachine' ⇒-solver ⇒-solver ∘ (M₂ ⊗ʳ E₁ ∘ M₁)

_⊗ᴷ_ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂} → Machine A₁ (B₁ ⊗₀ E₁) → Machine A₂ (B₂ ⊗₀ E₂) → Machine (A₁ ⊗₀ A₂) ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
M₁ ⊗ᴷ M₂ = TotalFunctionMachine' ⇒-solver ⇒-solver ∘ M₁ ⊗₁ M₂

⨂ᴷ : ∀ {n} → {A B E : Fin n → Channel} → ((k : Fin n) → Machine (A k) (B k ⊗₀ E k)) → Machine (⨂ A) (⨂ B ⊗₀ ⨂ E)
⨂ᴷ {zero} M = idᴷ
⨂ᴷ {suc n} M = M fzero ⊗ᴷ ⨂ᴷ (M P.∘ fsuc)

⨂ᴷ-sub-state : ∀ {n} {A B E : Fin n → Channel} {f : (k : Fin n) → Machine (A k) (B k ⊗₀ E k)} → (k : Fin n) → Machine.State (⨂ᴷ f) → Machine.State (f k)
⨂ᴷ-sub-state fzero ((s , _) , _) = s
⨂ᴷ-sub-state (fsuc k) ((_ , s) , _) = ⨂ᴷ-sub-state k s

import Relation.Binary.HeterogeneousEquality as H

record _≡ᴹ_ {A B C D : Channel} (M₁ : Machine A B) (M₂ : Machine C D) : Type₁ where
  field A≡C   : A  ≡   C
        B≡D   : B  ≡   D
        M₁≡M₂ : M₁ H.≅ M₂

≡ᴹ-subst : ∀ {a} {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
  → (P : ∀ {X Y} → Machine X Y → Type a) → M₁ ≡ᴹ M₂
  → P M₁ → P M₂
≡ᴹ-subst _ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } PM₂ = PM₂

≡ᴹ-refl : ∀ {A B} → {M : Machine A B} → M ≡ᴹ M
≡ᴹ-refl = record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }

≡ᴹ-sym : ∀ {A B C D} → {M₁ : Machine A B} {M₂ : Machine C D} → M₁ ≡ᴹ M₂ → M₂ ≡ᴹ M₁
≡ᴹ-sym record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } =
  record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl }

module _
  {A B : Channel}
  (m   : Machine A B) where
  
  open Machine m using (State) renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  open Channel (A ⊗₀ B ᵀ)

  data Trace : State → State → Type where
    []         : ∀ {s} → Trace s s
    _∷ʳ⟨_,_,_⟩ : ∀ {s s' s''} → Trace s s' → (i : inType) → (o : Maybe outType) → s' -⟦ i / o ⟧ᵐ⇀ s'' → Trace s s''

  Invariant : (P : State → Type) → Type
  Invariant P = (s₁ s₂ : State) → Trace s₁ s₂ → P s₁ → P s₂

module _ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D} where
  state-subst : M₁ ≡ᴹ M₂ → Machine.State M₁ → Machine.State M₂
  state-subst = ≡ᴹ-subst Machine.State

  Trace-subst : ∀ {s₁ s₂} → (eq : M₁ ≡ᴹ M₂)
    → Trace M₁ s₁ s₂ → Trace M₂ (state-subst eq s₁) (state-subst eq s₂)
  Trace-subst record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } trace = trace

Invariant-trans : {A B C D : Channel} → {M₁ : Machine A B} → {M₂ : Machine C D} → (eq : M₁ ≡ᴹ M₂)
  → (P : Machine.State M₁ → Type) → Invariant M₁ P → Invariant M₂ (P P.∘ state-subst (≡ᴹ-sym eq))
Invariant-trans record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H.refl } P inv = inv

--------------------------------------------------------------------------------
-- Open adversarial protocols

record OAP (A E₁ B E₂ : Channel) : Type₁ where
  field Adv        : Channel
        Protocol   : Machine A (B ⊗₀ Adv)
        Adversary  : Machine (Adv ⊗₀ E₁) E₂

--------------------------------------------------------------------------------
-- Environment model

ℰ-Out : Channel
ℰ-Out = record {inType = Bool ; outType = ⊥}

-- Presheaf on the category of channels & machines
-- we just take machines that output a boolean
-- for now, not on the Kleisli construction
ℰ : Channel → Type₁
ℰ C = Machine C ℰ-Out

map-ℰ : ∀ {A B} → Machine A B → ℰ B → ℰ A
map-ℰ M E = E ∘ M

--------------------------------------------------------------------------------
-- UC relations

-- perfect equivalence
_≈ℰ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
_≈ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≡ map-ℰ M' E

_≤UC_ : ∀ {A B E E''} → Machine A (B ⊗₀ E) → Machine A (B ⊗₀ E'') → Type₁
_≤UC_ {B = B} {E} R I = ∀ E' (A : Machine E E') → ∃[ S ] ((B ⊗ˡ A) ∘ R) ≈ℰ ((B ⊗ˡ S) ∘ I)

-- equivalent to _≤UC_ by "completeness of the dummy adversary"
_≤'UC_ : ∀ {A B E} → Machine A (B ⊗₀ E) → Machine A (B ⊗₀ E) → Type₁
_≤'UC_ {B = B} R I = ∃[ S ] R ≈ℰ (B ⊗ˡ S ∘ I)

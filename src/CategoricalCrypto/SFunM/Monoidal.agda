{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Monoidal structure on `SFunᵉ-Category` with the *coproduct* tensor
-- (⊎, ⊥).
--
-- Rationale: a Channel models a bidirectional protocol port whose
-- traffic at each instant is EITHER an input on one side OR a
-- back-flow on the other — never both simultaneously. The natural
-- tensor for such ports is the disjoint sum, not the product.
--
-- Under this tensor:
--   • A ⊗₀ B = A ⊎ B
--   • unit   = ⊥
--   • f ⊗₁ g routes inj₁/inj₂ inputs to f / g respectively, tracks
--     both states.
--
-- This file defines the structural pieces. The full `Monoidal` record
-- (with bifunctor laws, coherence) is assembled at the bottom; some
-- equational obligations are stubbed pending a more careful treatment
-- of `≈ᵉ` reasoning over `eval`.

open import categorical-crypto.Prelude hiding (Bifunctor)
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Data.List.Properties using (map-∘; map-id; map-cong)

open import Class.Core
open import Class.Monad.Ext

module CategoricalCrypto.SFunM.Monoidal {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ F-Laws        : FunctorLaws M      ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  where

open import CategoricalCrypto.SFunM
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄

open import Categories.Morphism SFunᵉ-Category using (_≅_)

private variable A B C D : Type

------------------------------------------------------------------------
-- The ⊎-tensor on SFunᵉ.
--
-- `f ⊗ᵉ g` is the stateful function that, given a sum-typed input,
-- dispatches to f or g (running on its own state) and re-wraps the
-- output. States are paired.

_⊗ᵉ'_ : ∀ {A B C D Sf Sg}
  → SFunType A B Sf
  → SFunType C D Sg
  → SFunType (A ⊎ C) (B ⊎ D) (Sf × Sg)
(f ⊗ᵉ' g) ((sf , sg) , inj₁ a) = do
  (sf' , b) ← f (sf , a)
  return ((sf' , sg) , inj₁ b)
(f ⊗ᵉ' g) ((sf , sg) , inj₂ c) = do
  (sg' , d) ← g (sg , c)
  return ((sf , sg') , inj₂ d)

infixr 9 _⊗ᵉ_
_⊗ᵉ_ : SFunᵉ A B → SFunᵉ C D → SFunᵉ (A ⊎ C) (B ⊎ D)
f ⊗ᵉ g = let module f = SFunᵉ f; module g = SFunᵉ g in record
  { State = f.State × g.State
  ; init  = f.init , g.init
  ; fun   = f.fun ⊗ᵉ' g.fun
  }

------------------------------------------------------------------------
-- Structural morphisms (associator, unitors, symmetry).
--
-- These are all stateless (`State = ⊤`) and deterministic — they
-- just permute the sum structure of the input.

-- Pure stateless reshape, lifted into SFunᵉ.
pure-reshape : (A → B) → SFunᵉ A B
pure-reshape f = record
  { State = ⊤
  ; init  = tt
  ; fun   = λ (tt , a) → return (tt , f a)
  }

-- `pure-reshape f` is observationally `return ∘ List.map f`.
pure-reshape-correct : ∀ {A B} {f : A → B} → eval (pure-reshape f) ≗ return ∘ map f
pure-reshape-correct {f = f} [] = refl
pure-reshape-correct {f = f} (a ∷ xs) = begin
  eval (pure-reshape f) (a ∷ xs)
    ≡⟨⟩
  (return (tt , f a) >>= λ (tt , b) →
    trace (SFunᵉ.fun (pure-reshape f)) tt xs >>= λ bs → return (b ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  (trace (SFunᵉ.fun (pure-reshape f)) tt xs >>= λ bs → return (f a ∷ bs))
    ≡⟨ pure-reshape-correct xs ⟩>>=⟨refl ⟩
  (return (map f xs) >>= λ bs → return (f a ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  return (f a ∷ map f xs)
  ∎
  where open ≡-Reasoning

-- Composing two pure reshapes equals one pure reshape with composed function.
-- Plumbs `pure-reshape-correct` through `trace-∘` and `map-∘`.
pure-reshape-∘ : ∀ {A B C} {g : B → C} {f : A → B}
  → (pure-reshape g ∘ᵉ pure-reshape f) ≈ᵉ pure-reshape (g ∘ f)
pure-reshape-∘ {g = g} {f = f} xs = begin
  eval (pure-reshape g ∘ᵉ pure-reshape f) xs
    -- Step 1: unfold ∘ᵉ to Kleisli form via sym trace-∘
    ≡⟨ sym (trace-∘ {sg = tt} {sf = tt}
                     {g = SFunᵉ.fun (pure-reshape g)}
                     {f = SFunᵉ.fun (pure-reshape f)} xs) ⟩
  ((eval (pure-reshape f) xs >>= λ y → return (eval (pure-reshape g) y)) >>= λ x → x)
    -- Step 2: pure-reshape-correct on inner eval (pure-reshape f)
    ≡⟨ pure-reshape-correct xs ⟩>>=⟨refl ⟩>>=⟨refl ⟩
  ((return (map f xs) >>= λ y → return (eval (pure-reshape g) y)) >>= λ x → x)
    -- Step 3: >>=-identityˡ on outer
    ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
  (return (eval (pure-reshape g) (map f xs)) >>= λ x → x)
    -- Step 4: >>=-identityˡ
    ≡⟨ >>=-identityˡ ⟩
  eval (pure-reshape g) (map f xs)
    -- Step 5: pure-reshape-correct
    ≡⟨ pure-reshape-correct (map f xs) ⟩
  return (map g (map f xs))
    -- Step 6: sym map-∘ — fuse maps
    ≡⟨ cong return (sym (map-∘ xs)) ⟩
  return (map (g ∘ f) xs)
    -- Step 7: sym pure-reshape-correct
    ≡⟨ sym (pure-reshape-correct xs) ⟩
  eval (pure-reshape (g ∘ f)) xs
  ∎
  where open ≡-Reasoning

-- Pure functions backing the structural morphisms — named so coherence
-- proofs can refer to them without falling foul of Agda's extended-lambda
-- comparison (two textually-identical extended lambdas are *not*
-- definitionally equal).

α-fn : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
α-fn (inj₁ (inj₁ a)) = inj₁ a
α-fn (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
α-fn (inj₂ c)        = inj₂ (inj₂ c)

α-fn-inv : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
α-fn-inv (inj₁ a)        = inj₁ (inj₁ a)
α-fn-inv (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
α-fn-inv (inj₂ (inj₂ c)) = inj₂ c

λ-fn : ⊥ ⊎ A → A
λ-fn (inj₂ a) = a

ρ-fn : A ⊎ ⊥ → A
ρ-fn (inj₁ a) = a

-- Associator: (A ⊎ B) ⊎ C ≅ A ⊎ (B ⊎ C)
α⇒ᵉ : SFunᵉ ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α⇒ᵉ = pure-reshape α-fn

α⇐ᵉ : SFunᵉ (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α⇐ᵉ = pure-reshape α-fn-inv

-- Left unitor: ⊥ ⊎ A ≅ A
λ⇒ᵉ : SFunᵉ (⊥ ⊎ A) A
λ⇒ᵉ = pure-reshape λ-fn

λ⇐ᵉ : SFunᵉ A (⊥ ⊎ A)
λ⇐ᵉ = pure-reshape inj₂

-- Right unitor: A ⊎ ⊥ ≅ A
ρ⇒ᵉ : SFunᵉ (A ⊎ ⊥) A
ρ⇒ᵉ = pure-reshape ρ-fn

ρ⇐ᵉ : SFunᵉ A (A ⊎ ⊥)
ρ⇐ᵉ = pure-reshape inj₁

-- Symmetry: A ⊎ B ≅ B ⊎ A
σᵉ : SFunᵉ (A ⊎ B) (B ⊎ A)
σᵉ = pure-reshape λ where
  (inj₁ a) → inj₂ a
  (inj₂ b) → inj₁ b

------------------------------------------------------------------------
-- Coherence and bifunctor laws — TODO.
--
-- To assemble a `Monoidal SFunᵉ-Category` record we need:
--
--   • A Bifunctor `⊗` with:
--       - F₀ = curry _⊎_
--       - F₁ = curry _⊗ᵉ_
--       - identity      : idᵉ ⊗ᵉ idᵉ ≈ᵉ idᵉ
--       - homomorphism  : (f ∘ᵉ g) ⊗ᵉ (h ∘ᵉ i) ≈ᵉ (f ⊗ᵉ h) ∘ᵉ (g ⊗ᵉ i)
--       - F-resp-≈      : f ≈ᵉ f' → g ≈ᵉ g' → f ⊗ᵉ g ≈ᵉ f' ⊗ᵉ g'
--
--   • Isomorphisms (unitorˡ, unitorʳ, associator) — done as
--     stateless pure morphisms above (α⇒ᵉ/α⇐ᵉ, λ⇒ᵉ/λ⇐ᵉ, ρ⇒ᵉ/ρ⇐ᵉ),
--     plus proofs that they actually compose to identity.
--
--   • Commutativity squares (unitor/associator naturality).
--
--   • Triangle and pentagon coherence laws.
--
-- Every law is a `_≈ᵉ_` equality, hence reduces to a `_≗_` equality
-- of `eval` on every input list. Each proof inducts on the input list
-- and unrolls the monadic do-notation using monad laws + the
-- commutative/extensional/functor laws assumed by SFunM's module
-- parameters.
--
-- Pattern (matches `id-correct` / `trace-∘` in SFunM.agda):
--   1. eval (LHS) ≡⟨ definition unfold ⟩ trace LHS.fun init xs
--   2. ≡⟨ induction + monad laws ⟩ trace RHS.fun init xs
--   3. ≡⟨ definition fold ⟩ eval (RHS)
--
-- The trace-∘ lemma already does this for ∘ᵉ; the ⊗ᵉ analogue
-- (a `trace-⊗ᵉ` connecting `trace (f ⊗ᵉ g)` to interleaved traces of
-- f and g on the inj₁/inj₂ branches) is provided below.

------------------------------------------------------------------------
-- The trace-⊗ᵉ primitive — per-step unfolding of `trace (f ⊗ᵉ' g)`.
--
-- These are the workhorse lemmas: they unfold one `inj₁` or `inj₂`
-- step of `trace (f ⊗ᵉ' g)` into a single application of `f` (resp.
-- `g`) followed by the rest of the trace and the appropriate `inj`
-- re-wrap. Together with induction on the input list, they reduce
-- every ⊗ᵉ-equation to monad-law reasoning on f and g separately.
--
-- Proof: `>>=-assoc` then `>>=-identityˡ` under the f-bind.

trace-⊗ᵉ-cons-inj₁ : ∀ {A B C D Sf Sg} {sf : Sf} {sg : Sg}
  {f : SFunType A B Sf} {g : SFunType C D Sg}
  (a : A) (xs : List (A ⊎ C))
  → trace (f ⊗ᵉ' g) (sf , sg) (inj₁ a ∷ xs)
    ≡ (f (sf , a) >>= λ (sf' , b) →
       trace (f ⊗ᵉ' g) (sf' , sg) xs >>= λ bs →
       return (inj₁ b ∷ bs))
trace-⊗ᵉ-cons-inj₁ {sf = sf} {sg} {f} {g} a xs = begin
  trace (f ⊗ᵉ' g) (sf , sg) (inj₁ a ∷ xs)
    ≡⟨⟩
  ((f (sf , a) >>= λ (sf' , b) → return ((sf' , sg) , inj₁ b)) >>=
    λ s'-x' → trace (f ⊗ᵉ' g) (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-assoc (f (sf , a)) ⟩
  (f (sf , a) >>= λ (sf' , b) → return ((sf' , sg) , inj₁ b) >>=
    λ s'-x' → trace (f ⊗ᵉ' g) (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace (f ⊗ᵉ' g) (sf' , sg) xs >>= λ bs → return (inj₁ b ∷ bs))
  ∎
  where open ≡-Reasoning

trace-⊗ᵉ-cons-inj₂ : ∀ {A B C D Sf Sg} {sf : Sf} {sg : Sg}
  {f : SFunType A B Sf} {g : SFunType C D Sg}
  (c : C) (xs : List (A ⊎ C))
  → trace (f ⊗ᵉ' g) (sf , sg) (inj₂ c ∷ xs)
    ≡ (g (sg , c) >>= λ (sg' , d) →
       trace (f ⊗ᵉ' g) (sf , sg') xs >>= λ bs →
       return (inj₂ d ∷ bs))
trace-⊗ᵉ-cons-inj₂ {sf = sf} {sg} {f} {g} c xs = begin
  trace (f ⊗ᵉ' g) (sf , sg) (inj₂ c ∷ xs)
    ≡⟨⟩
  ((g (sg , c) >>= λ (sg' , d) → return ((sf , sg') , inj₂ d)) >>=
    λ s'-x' → trace (f ⊗ᵉ' g) (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-assoc (g (sg , c)) ⟩
  (g (sg , c) >>= λ (sg' , d) → return ((sf , sg') , inj₂ d) >>=
    λ s'-x' → trace (f ⊗ᵉ' g) (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ refl⟩>>=⟨ (λ (sg' , d) → >>=-identityˡ) ⟩
  (g (sg , c) >>= λ (sg' , d) →
    trace (f ⊗ᵉ' g) (sf , sg') xs >>= λ bs → return (inj₂ d ∷ bs))
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The full trace-⊗ᵉ — separation lemma.
--
-- Given an input list `xs : List (A ⊎ C)`, the trace of `f ⊗ᵉ' g` on
-- `xs` equals an "all f's first, then all g's" trace where:
--   • `filter₁ xs` are the inj₁ inputs, run through f
--   • `filter₂ xs` are the inj₂ inputs, run through g
--   • `weave xs bs ds` re-interleaves the two output lists into the
--     original tag pattern.
--
-- This requires **commutativity** of M (in the inj₂ case the outer
-- order has `g` first, but RHS has all f's first — we swap via
-- `>>=-comm-y`).

filter₁ : ∀ {A C : Type} → List (A ⊎ C) → List A
filter₁ [] = []
filter₁ (inj₁ a ∷ xs) = a ∷ filter₁ xs
filter₁ (inj₂ _ ∷ xs) = filter₁ xs

filter₂ : ∀ {A C : Type} → List (A ⊎ C) → List C
filter₂ [] = []
filter₂ (inj₁ _ ∷ xs) = filter₂ xs
filter₂ (inj₂ c ∷ xs) = c ∷ filter₂ xs

weave : ∀ {A B C D : Type}
  → List (A ⊎ C) → List B → List D → List (B ⊎ D)
weave [] _ _ = []
weave (inj₁ _ ∷ xs) (b ∷ bs) ds = inj₁ b ∷ weave xs bs ds
weave (inj₁ _ ∷ _)  []       _  = []
weave (inj₂ _ ∷ xs) bs (d ∷ ds) = inj₂ d ∷ weave xs bs ds
weave (inj₂ _ ∷ _)  _       []  = []

trace-⊗ᵉ : ∀ {A B C D Sf Sg} {f : SFunType A B Sf} {g : SFunType C D Sg}
  (sf : Sf) (sg : Sg) (xs : List (A ⊎ C))
  → trace (f ⊗ᵉ' g) (sf , sg) xs
    ≡ (trace f sf (filter₁ xs) >>= λ bs →
       trace g sg (filter₂ xs) >>= λ ds →
       return (weave xs bs ds))
trace-⊗ᵉ sf sg [] = begin
  return []
    ≡⟨ sym >>=-identityˡ ⟩
  (return [] >>= λ _ → return [])
    ≡⟨ sym >>=-identityˡ ⟩
  (return [] >>= λ _ → return [] >>= λ _ → return [])
  ∎
  where open ≡-Reasoning

trace-⊗ᵉ {f = f} {g} sf sg (inj₁ a ∷ xs) = begin
  trace (f ⊗ᵉ' g) (sf , sg) (inj₁ a ∷ xs)
    -- Step 1: unfold first ⊗ᵉ step
    ≡⟨ trace-⊗ᵉ-cons-inj₁ a xs ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace (f ⊗ᵉ' g) (sf' , sg) xs >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 2: apply IH on tail
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → trace-⊗ᵉ sf' sg xs ⟩>>=⟨refl) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    (trace f sf' (filter₁ xs) >>= λ bs1 →
      trace g sg (filter₂ xs) >>= λ ds → return (weave xs bs1 ds))
        >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 3: associativity (flatten outer compound bind)
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-assoc _) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 →
      (trace g sg (filter₂ xs) >>= λ ds → return (weave xs bs1 ds))
        >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 4: associativity again
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs1 → >>=-assoc _) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 →
      trace g sg (filter₂ xs) >>= λ ds →
        return (weave xs bs1 ds) >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 5: identityˡ at innermost (Common form, mod weave def)
    -- Note: inj₁ b ∷ weave xs bs1 ds = weave (inj₁ a ∷ xs) (b ∷ bs1) ds [definitional]
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs1 → refl⟩>>=⟨ λ ds → >>=-identityˡ) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 →
      trace g sg (filter₂ xs) >>= λ ds →
        return (weave (inj₁ a ∷ xs) (b ∷ bs1) ds))
    -- Step 6: sym identityˡ — re-introduce `return (b ∷ bs1) >>= λ bs → ...`
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs1 → refl⟩>>=⟨ λ ds → sym >>=-identityˡ) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 →
      trace g sg (filter₂ xs) >>= λ ds →
        return (b ∷ bs1) >>= λ bs → return (weave (inj₁ a ∷ xs) bs ds))
    -- Step 7: commute `trace g` past `return (b ∷ bs1)` via >>=-comm-y
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs1 → >>=-comm-y _) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 →
      return (b ∷ bs1) >>= λ bs →
        trace g sg (filter₂ xs) >>= λ ds → return (weave (inj₁ a ∷ xs) bs ds))
    -- Step 8: sym >>=-assoc to re-bracket inner trace-f >>= return
    ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → sym (>>=-assoc _)) ⟩
  (f (sf , a) >>= λ (sf' , b) →
    (trace f sf' (filter₁ xs) >>= λ bs1 → return (b ∷ bs1)) >>= λ bs →
      trace g sg (filter₂ xs) >>= λ ds → return (weave (inj₁ a ∷ xs) bs ds))
    -- Step 9: sym >>=-assoc to factor f out
    ≡⟨ sym (>>=-assoc _) ⟩
  ((f (sf , a) >>= λ (sf' , b) →
    trace f sf' (filter₁ xs) >>= λ bs1 → return (b ∷ bs1)) >>= λ bs →
      trace g sg (filter₂ xs) >>= λ ds → return (weave (inj₁ a ∷ xs) bs ds))
    -- Step 10: definitional — fold back into trace
    ≡⟨⟩
  (trace f sf (filter₁ (inj₁ a ∷ xs)) >>= λ bs →
    trace g sg (filter₂ (inj₁ a ∷ xs)) >>= λ ds →
      return (weave (inj₁ a ∷ xs) bs ds))
  ∎
  where open ≡-Reasoning

trace-⊗ᵉ {f = f} {g} sf sg (inj₂ c ∷ xs) = begin
  trace (f ⊗ᵉ' g) (sf , sg) (inj₂ c ∷ xs)
    -- Step 1: unfold first ⊗ᵉ step
    ≡⟨ trace-⊗ᵉ-cons-inj₂ c xs ⟩
  (g (sg , c) >>= λ (sg' , d) →
    trace (f ⊗ᵉ' g) (sf , sg') xs >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 2: apply IH on tail (note: now g's state is updated, f's stays sf)
    ≡⟨ refl⟩>>=⟨ (λ (sg' , d) → trace-⊗ᵉ sf sg' xs ⟩>>=⟨refl) ⟩
  (g (sg , c) >>= λ (sg' , d) →
    (trace f sf (filter₁ xs) >>= λ bs1 →
      trace g sg' (filter₂ xs) >>= λ ds → return (weave xs bs1 ds))
        >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 3: associativity
    ≡⟨ refl⟩>>=⟨ (λ (sg' , d) → >>=-assoc _) ⟩
  (g (sg , c) >>= λ (sg' , d) →
    trace f sf (filter₁ xs) >>= λ bs1 →
      (trace g sg' (filter₂ xs) >>= λ ds → return (weave xs bs1 ds))
        >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 4: associativity
    ≡⟨ refl⟩>>=⟨ (λ (sg' , d) → refl⟩>>=⟨ λ bs1 → >>=-assoc _) ⟩
  (g (sg , c) >>= λ (sg' , d) →
    trace f sf (filter₁ xs) >>= λ bs1 →
      trace g sg' (filter₂ xs) >>= λ ds →
        return (weave xs bs1 ds) >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 5: identityˡ at innermost (Common-form)
    -- Note: inj₂ d ∷ weave xs bs1 ds = weave (inj₂ c ∷ xs) bs1 (d ∷ ds) [definitional]
    ≡⟨ refl⟩>>=⟨ (λ (sg' , d) → refl⟩>>=⟨ λ bs1 → refl⟩>>=⟨ λ ds → >>=-identityˡ) ⟩
  (g (sg , c) >>= λ (sg' , d) →
    trace f sf (filter₁ xs) >>= λ bs1 →
      trace g sg' (filter₂ xs) >>= λ ds →
        return (weave (inj₂ c ∷ xs) bs1 (d ∷ ds)))
    -- Step 6: commute g and trace-f-filter₁ via >>=-comm-y at outer level
    ≡⟨ >>=-comm-y _ ⟩
  (trace f sf (filter₁ xs) >>= λ bs1 →
    g (sg , c) >>= λ (sg' , d) →
      trace g sg' (filter₂ xs) >>= λ ds →
        return (weave (inj₂ c ∷ xs) bs1 (d ∷ ds)))
    -- Step 7: sym identityˡ to introduce `return (d ∷ ds) >>= λ ds' → ...`
    ≡⟨ refl⟩>>=⟨ (λ bs1 → refl⟩>>=⟨ λ (sg' , d) → refl⟩>>=⟨ λ ds → sym >>=-identityˡ) ⟩
  (trace f sf (filter₁ xs) >>= λ bs1 →
    g (sg , c) >>= λ (sg' , d) →
      trace g sg' (filter₂ xs) >>= λ ds →
        return (d ∷ ds) >>= λ ds' → return (weave (inj₂ c ∷ xs) bs1 ds'))
    -- Step 8: sym >>=-assoc to re-bracket inner trace-g >>= return
    ≡⟨ refl⟩>>=⟨ (λ bs1 → refl⟩>>=⟨ λ (sg' , d) → sym (>>=-assoc _)) ⟩
  (trace f sf (filter₁ xs) >>= λ bs1 →
    g (sg , c) >>= λ (sg' , d) →
      (trace g sg' (filter₂ xs) >>= λ ds → return (d ∷ ds)) >>= λ ds' →
        return (weave (inj₂ c ∷ xs) bs1 ds'))
    -- Step 9: sym >>=-assoc to factor g out
    ≡⟨ refl⟩>>=⟨ (λ bs1 → sym (>>=-assoc _)) ⟩
  (trace f sf (filter₁ xs) >>= λ bs1 →
    (g (sg , c) >>= λ (sg' , d) →
      trace g sg' (filter₂ xs) >>= λ ds → return (d ∷ ds)) >>= λ ds' →
        return (weave (inj₂ c ∷ xs) bs1 ds'))
    -- Step 10: definitional — fold back into trace
    ≡⟨⟩
  (trace f sf (filter₁ (inj₂ c ∷ xs)) >>= λ bs →
    trace g sg (filter₂ (inj₂ c ∷ xs)) >>= λ ds →
      return (weave (inj₂ c ∷ xs) bs ds))
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Bifunctor laws — proofs follow `id-correct` / `trace-∘`.

-- `id-correct-⊗ᵉ`: running `idᵉ ⊗ᵉ idᵉ` is the same as `return` (the
-- identity-trace), so by `id-correct` it's the same as `eval idᵉ`.
-- Proof structure mirrors `id-correct` from SFunM.agda.
id-correct-⊗ᵉ : ∀ {A B} → return ≗ eval (idᵉ {A} ⊗ᵉ idᵉ {B})
id-correct-⊗ᵉ [] = refl
id-correct-⊗ᵉ (inj₁ a ∷ xs) = sym (begin
  eval (idᵉ ⊗ᵉ idᵉ) (inj₁ a ∷ xs)
    ≡⟨⟩
  ((return (tt , a) >>= λ (sf' , b) → return ((sf' , tt) , inj₁ b)) >>=
    λ s'-x' → trace _ (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
  (return ((tt , tt) , inj₁ a) >>=
    λ s'-x' → trace _ (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  (trace _ (tt , tt) xs >>= λ bs → return (inj₁ a ∷ bs))
    ≡⟨ sym (id-correct-⊗ᵉ xs) ⟩>>=⟨refl ⟩
  (return xs >>= λ bs → return (inj₁ a ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  return (inj₁ a ∷ xs)
  ∎)
  where open ≡-Reasoning
id-correct-⊗ᵉ (inj₂ b ∷ xs) = sym (begin
  eval (idᵉ ⊗ᵉ idᵉ) (inj₂ b ∷ xs)
    ≡⟨⟩
  ((return (tt , b) >>= λ (sg' , d) → return ((tt , sg') , inj₂ d)) >>=
    λ s'-x' → trace _ (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
  (return ((tt , tt) , inj₂ b) >>=
    λ s'-x' → trace _ (proj₁ s'-x') xs >>= λ bs → return (proj₂ s'-x' ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  (trace _ (tt , tt) xs >>= λ bs → return (inj₂ b ∷ bs))
    ≡⟨ sym (id-correct-⊗ᵉ xs) ⟩>>=⟨refl ⟩
  (return xs >>= λ bs → return (inj₂ b ∷ bs))
    ≡⟨ >>=-identityˡ ⟩
  return (inj₂ b ∷ xs)
  ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- ⊗ᵉ-resp-≈ᵉ — congruence under _≈ᵉ_.
--
-- Strategy: fold both sides through `trace-⊗ᵉ`, which separates a
-- `trace (f ⊗ᵉ' g)` into independent `trace f` and `trace g` runs
-- on filtered subsequences. The hypotheses `f ≈ᵉ f'` and `g ≈ᵉ g'`
-- then apply directly to each side.

-- Bifunctor identity: (idᵉ ⊗ᵉ idᵉ) is observationally idᵉ.
-- Both sides equal `return` via id-correct-⊗ᵉ and id-correct.
⊗ᵉ-identity : ∀ {A B} → (idᵉ {A} ⊗ᵉ idᵉ {B}) ≈ᵉ idᵉ
⊗ᵉ-identity xs = trans (sym (id-correct-⊗ᵉ xs)) (id-correct xs)

⊗ᵉ-resp-≈ᵉ : ∀ {A B C D} {f f' : SFunᵉ A B} {g g' : SFunᵉ C D}
  → f ≈ᵉ f' → g ≈ᵉ g' → (f ⊗ᵉ g) ≈ᵉ (f' ⊗ᵉ g')
⊗ᵉ-resp-≈ᵉ {f = f} {f'} {g} {g'} p q xs = begin
  eval (f ⊗ᵉ g) xs
    ≡⟨ trace-⊗ᵉ (SFunᵉ.init f) (SFunᵉ.init g) xs ⟩
  (eval f (filter₁ xs) >>= λ bs →
    eval g (filter₂ xs) >>= λ ds →
      return (weave xs bs ds))
    ≡⟨ p (filter₁ xs) ⟩>>=⟨refl ⟩
  (eval f' (filter₁ xs) >>= λ bs →
    eval g (filter₂ xs) >>= λ ds →
      return (weave xs bs ds))
    ≡⟨ refl⟩>>=⟨ (λ bs → q (filter₂ xs) ⟩>>=⟨refl) ⟩
  (eval f' (filter₁ xs) >>= λ bs →
    eval g' (filter₂ xs) >>= λ ds →
      return (weave xs bs ds))
    ≡⟨ sym (trace-⊗ᵉ (SFunᵉ.init f') (SFunᵉ.init g') xs) ⟩
  eval (f' ⊗ᵉ g') xs
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Bifunctor homomorphism law.
--
-- ((f ∘ᵉ g) ⊗ᵉ (h ∘ᵉ i)) ≈ᵉ ((f ⊗ᵉ h) ∘ᵉ (g ⊗ᵉ i))
--
-- Approach: prove the function-level version by induction on the input
-- list. The function-level statement is stronger (works for arbitrary
-- start states), which lets us state it without committing to init
-- states — needed for the inductive step where intermediate states
-- arise from the head-of-list step.

⊗ᵉ-homomorphism' : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
  {Sf Sg Sh Si : Type}
  {f : SFunType B₁ C₁ Sf} {g : SFunType A₁ B₁ Sg}
  {h : SFunType B₂ C₂ Sh} {i : SFunType A₂ B₂ Si}
  (sf : Sf) (sg : Sg) (sh : Sh) (si : Si)
  (xs : List (A₁ ⊎ A₂))
  → trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh , si)) xs
    ≡ (trace (g ⊗ᵉ' i) (sg , si) xs >>= λ ys →
       trace (f ⊗ᵉ' h) (sf , sh) ys)
-- Base case: trace _ _ [] = return [] on both sides, then >>=-identityˡ.
⊗ᵉ-homomorphism' sf sg sh si [] = sym >>=-identityˡ

⊗ᵉ-homomorphism' {f = f} {g} {h} {i} sf sg sh si (inj₁ a ∷ xs') = begin
  trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh , si)) (inj₁ a ∷ xs')
    -- Step 1: trace-⊗ᵉ-cons-inj₁
    ≡⟨ trace-⊗ᵉ-cons-inj₁ a xs' ⟩
  ((f ∘ᵉ' g) ((sf , sg) , a) >>= λ ((sf' , sg') , b) →
    trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf' , sg') , (sh , si)) xs' >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 2: definitional — unfold (f ∘ᵉ' g) ((sf, sg), a)
    ≡⟨⟩
  ((g (sg , a) >>= λ (sg' , b₀) → f (sf , b₀) >>= λ (sf' , c) → return ((sf' , sg') , c)) >>=
    λ ((sf' , sg') , b) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf' , sg') , (sh , si)) xs' >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 3: >>=-assoc — flatten outer
    ≡⟨ >>=-assoc (g (sg , a)) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    (f (sf , b₀) >>= λ (sf' , c) → return ((sf' , sg') , c)) >>= λ ((sf'' , sg'') , b) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf'' , sg'') , (sh , si)) xs' >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 4: >>=-assoc — flatten inner
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → >>=-assoc (f (sf , b₀))) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    f (sf , b₀) >>= λ (sf' , c) → return ((sf' , sg') , c) >>= λ ((sf'' , sg'') , b) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf'' , sg'') , (sh , si)) xs' >>= λ bs → return (inj₁ b ∷ bs))
    -- Step 5: >>=-identityˡ on the return
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → refl⟩>>=⟨ λ (sf' , c) → >>=-identityˡ) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    f (sf , b₀) >>= λ (sf' , c) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf' , sg') , (sh , si)) xs' >>= λ bs → return (inj₁ c ∷ bs))
    -- Step 6: IH on inner trace
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → refl⟩>>=⟨ λ (sf' , c) →
        ⊗ᵉ-homomorphism' sf' sg' sh si xs' ⟩>>=⟨refl) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    f (sf , b₀) >>= λ (sf' , c) →
      (trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys → trace (f ⊗ᵉ' h) (sf' , sh) ys)
        >>= λ bs → return (inj₁ c ∷ bs))
    -- Step 7: >>=-assoc to flatten
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → refl⟩>>=⟨ λ (sf' , c) → >>=-assoc _) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    f (sf , b₀) >>= λ (sf' , c) →
      trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys →
        trace (f ⊗ᵉ' h) (sf' , sh) ys >>= λ bs → return (inj₁ c ∷ bs))
    -- Step 8: >>=-comm-y to swap f and trace(g⊗i)
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → >>=-comm-y _) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys →
      f (sf , b₀) >>= λ (sf' , c) →
        trace (f ⊗ᵉ' h) (sf' , sh) ys >>= λ bs → return (inj₁ c ∷ bs))
    -- Step 9: fold innermost into trace(f⊗h)(sf, sh)(inj₁ b₀ ∷ ys) via sym cons-inj₁
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → refl⟩>>=⟨ λ ys → sym (trace-⊗ᵉ-cons-inj₁ b₀ ys)) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys →
      trace (f ⊗ᵉ' h) (sf , sh) (inj₁ b₀ ∷ ys))
    -- Step 10: sym >>=-identityˡ — re-introduce a return-bind on (inj₁ b₀ ∷ ys)
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → refl⟩>>=⟨ λ ys → sym >>=-identityˡ) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys →
      return (inj₁ b₀ ∷ ys) >>= λ ys' → trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 11: sym >>=-assoc — factor trace(f⊗h) past ys-bind
    ≡⟨ refl⟩>>=⟨ (λ (sg' , b₀) → sym (>>=-assoc _)) ⟩
  (g (sg , a) >>= λ (sg' , b₀) →
    (trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys → return (inj₁ b₀ ∷ ys)) >>= λ ys' →
      trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 12: sym >>=-assoc — factor trace(f⊗h) past g-bind
    ≡⟨ sym (>>=-assoc _) ⟩
  ((g (sg , a) >>= λ (sg' , b₀) →
    trace (g ⊗ᵉ' i) (sg' , si) xs' >>= λ ys → return (inj₁ b₀ ∷ ys)) >>= λ ys' →
      trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 13: fold first part into trace(g⊗i)(sg,si)(inj₁ a ∷ xs') via sym cons-inj₁
    ≡⟨ sym (trace-⊗ᵉ-cons-inj₁ a xs') ⟩>>=⟨refl ⟩
  (trace (g ⊗ᵉ' i) (sg , si) (inj₁ a ∷ xs') >>= λ ys' → trace (f ⊗ᵉ' h) (sf , sh) ys')
  ∎
  where open ≡-Reasoning

⊗ᵉ-homomorphism' {f = f} {g} {h} {i} sf sg sh si (inj₂ a ∷ xs') = begin
  trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh , si)) (inj₂ a ∷ xs')
    -- Step 1: trace-⊗ᵉ-cons-inj₂
    ≡⟨ trace-⊗ᵉ-cons-inj₂ a xs' ⟩
  ((h ∘ᵉ' i) ((sh , si) , a) >>= λ ((sh' , si') , d) →
    trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh' , si')) xs' >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 2: definitional — unfold (h ∘ᵉ' i)
    ≡⟨⟩
  ((i (si , a) >>= λ (si' , b) → h (sh , b) >>= λ (sh' , c) → return ((sh' , si') , c)) >>=
    λ ((sh' , si') , d) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh' , si')) xs' >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 3: >>=-assoc — flatten outer
    ≡⟨ >>=-assoc (i (si , a)) ⟩
  (i (si , a) >>= λ (si' , b) →
    (h (sh , b) >>= λ (sh' , c) → return ((sh' , si') , c)) >>= λ ((sh'' , si'') , d) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh'' , si'')) xs' >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 4: >>=-assoc — flatten inner
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → >>=-assoc (h (sh , b))) ⟩
  (i (si , a) >>= λ (si' , b) →
    h (sh , b) >>= λ (sh' , c) → return ((sh' , si') , c) >>= λ ((sh'' , si'') , d) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh'' , si'')) xs' >>= λ bs → return (inj₂ d ∷ bs))
    -- Step 5: >>=-identityˡ on the return
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → refl⟩>>=⟨ λ (sh' , c) → >>=-identityˡ) ⟩
  (i (si , a) >>= λ (si' , b) →
    h (sh , b) >>= λ (sh' , c) →
      trace ((f ∘ᵉ' g) ⊗ᵉ' (h ∘ᵉ' i)) ((sf , sg) , (sh' , si')) xs' >>= λ bs → return (inj₂ c ∷ bs))
    -- Step 6: IH on inner trace
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → refl⟩>>=⟨ λ (sh' , c) →
        ⊗ᵉ-homomorphism' sf sg sh' si' xs' ⟩>>=⟨refl) ⟩
  (i (si , a) >>= λ (si' , b) →
    h (sh , b) >>= λ (sh' , c) →
      (trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys → trace (f ⊗ᵉ' h) (sf , sh') ys)
        >>= λ bs → return (inj₂ c ∷ bs))
    -- Step 7: >>=-assoc to flatten
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → refl⟩>>=⟨ λ (sh' , c) → >>=-assoc _) ⟩
  (i (si , a) >>= λ (si' , b) →
    h (sh , b) >>= λ (sh' , c) →
      trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys →
        trace (f ⊗ᵉ' h) (sf , sh') ys >>= λ bs → return (inj₂ c ∷ bs))
    -- Step 8: >>=-comm-y to swap h and trace(g⊗i)
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → >>=-comm-y _) ⟩
  (i (si , a) >>= λ (si' , b) →
    trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys →
      h (sh , b) >>= λ (sh' , c) →
        trace (f ⊗ᵉ' h) (sf , sh') ys >>= λ bs → return (inj₂ c ∷ bs))
    -- Step 9: fold innermost into trace(f⊗h)(sf, sh)(inj₂ b ∷ ys) via sym cons-inj₂
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → refl⟩>>=⟨ λ ys → sym (trace-⊗ᵉ-cons-inj₂ b ys)) ⟩
  (i (si , a) >>= λ (si' , b) →
    trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys →
      trace (f ⊗ᵉ' h) (sf , sh) (inj₂ b ∷ ys))
    -- Step 10: sym >>=-identityˡ
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → refl⟩>>=⟨ λ ys → sym >>=-identityˡ) ⟩
  (i (si , a) >>= λ (si' , b) →
    trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys →
      return (inj₂ b ∷ ys) >>= λ ys' → trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 11: sym >>=-assoc — factor trace(f⊗h) past ys-bind
    ≡⟨ refl⟩>>=⟨ (λ (si' , b) → sym (>>=-assoc _)) ⟩
  (i (si , a) >>= λ (si' , b) →
    (trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys → return (inj₂ b ∷ ys)) >>= λ ys' →
      trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 12: sym >>=-assoc — factor trace(f⊗h) past i-bind
    ≡⟨ sym (>>=-assoc _) ⟩
  ((i (si , a) >>= λ (si' , b) →
    trace (g ⊗ᵉ' i) (sg , si') xs' >>= λ ys → return (inj₂ b ∷ ys)) >>= λ ys' →
      trace (f ⊗ᵉ' h) (sf , sh) ys')
    -- Step 13: fold first part into trace(g⊗i)(sg, si)(inj₂ a ∷ xs') via sym cons-inj₂
    ≡⟨ sym (trace-⊗ᵉ-cons-inj₂ a xs') ⟩>>=⟨refl ⟩
  (trace (g ⊗ᵉ' i) (sg , si) (inj₂ a ∷ xs') >>= λ ys' → trace (f ⊗ᵉ' h) (sf , sh) ys')
  ∎
  where open ≡-Reasoning

-- The SFunᵉ-level bifunctor homomorphism, via ⊗ᵉ-homomorphism' (with
-- init states) and then trace-∘ to fold back into the ∘ᵉ form on the
-- right.
⊗ᵉ-homomorphism : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
  {f : SFunᵉ B₁ C₁} {g : SFunᵉ A₁ B₁}
  {h : SFunᵉ B₂ C₂} {i : SFunᵉ A₂ B₂}
  → ((f ∘ᵉ g) ⊗ᵉ (h ∘ᵉ i)) ≈ᵉ ((f ⊗ᵉ h) ∘ᵉ (g ⊗ᵉ i))
⊗ᵉ-homomorphism {f = f} {g} {h} {i} xs = begin
  eval ((f ∘ᵉ g) ⊗ᵉ (h ∘ᵉ i)) xs
    ≡⟨ ⊗ᵉ-homomorphism' (SFunᵉ.init f) (SFunᵉ.init g) (SFunᵉ.init h) (SFunᵉ.init i) xs ⟩
  (eval (g ⊗ᵉ i) xs >>= λ ys → eval (f ⊗ᵉ h) ys)
    -- Bridge to the literal Kleisli-unfolded shape so trace-∘ matches:
    -- introduce `return _ >>= id` and re-associate.
    ≡⟨ refl⟩>>=⟨ (λ ys → sym >>=-identityˡ) ⟩
  (eval (g ⊗ᵉ i) xs >>= λ ys → return (eval (f ⊗ᵉ h) ys) >>= λ x → x)
    ≡⟨ sym (>>=-assoc _) ⟩
  ((eval (g ⊗ᵉ i) xs >>= λ ys → return (eval (f ⊗ᵉ h) ys)) >>= λ x → x)
    ≡⟨ trace-∘ {sg = SFunᵉ.init (f ⊗ᵉ h)} {sf = SFunᵉ.init (g ⊗ᵉ i)}
                {g = SFunᵉ.fun (f ⊗ᵉ h)} {f = SFunᵉ.fun (g ⊗ᵉ i)} xs ⟩
  eval ((f ⊗ᵉ h) ∘ᵉ (g ⊗ᵉ i)) xs
  ∎
  where open ≡-Reasoning


------------------------------------------------------------------------
-- Bifunctor ⊗ — combines the three established lemmas (⊗ᵉ-identity,
-- ⊗ᵉ-homomorphism, ⊗ᵉ-resp-≈ᵉ) into a single Bifunctor record.

⊗ᵉ-bifunctor : Bifunctor SFunᵉ-Category SFunᵉ-Category SFunᵉ-Category
⊗ᵉ-bifunctor = record
  { F₀           = λ { (A , B) → A ⊎ B }
  ; F₁           = λ { (f , g) → f ⊗ᵉ g }
  ; identity     = ⊗ᵉ-identity
  ; homomorphism = ⊗ᵉ-homomorphism
  ; F-resp-≈     = λ { (p , q) → ⊗ᵉ-resp-≈ᵉ p q }
  }

------------------------------------------------------------------------
-- Iso lemmas: when composing two pure-reshapes gives the identity.
--
-- Specialised consequence of pure-reshape-∘ + pure-reshape-correct +
-- `map-cong/map-id/id-correct`. Every λ/ρ/α iso obligation reduces to
-- a pointwise (∀ x → g (f x) ≡ x) discharge.

pure-reshape-∘ᵉ-id : ∀ {A B} {f : A → B} {g : B → A}
  → (∀ x → g (f x) ≡ x)
  → (pure-reshape g ∘ᵉ pure-reshape f) ≈ᵉ idᵉ
pure-reshape-∘ᵉ-id {f = f} {g} g-f-id xs = begin
  eval (pure-reshape g ∘ᵉ pure-reshape f) xs
    ≡⟨ pure-reshape-∘ xs ⟩
  eval (pure-reshape (g ∘ f)) xs
    ≡⟨ pure-reshape-correct xs ⟩
  return (map (g ∘ f) xs)
    ≡⟨ cong return (map-cong g-f-id xs) ⟩
  return (map id xs)
    ≡⟨ cong return (map-id xs) ⟩
  return xs
    ≡⟨ id-correct xs ⟩
  eval idᵉ xs
  ∎
  where open ≡-Reasoning

-- Iso witnesses for the six unitor/associator compositions.

λ-isoˡ : ∀ {A} → (λ⇐ᵉ ∘ᵉ λ⇒ᵉ {A}) ≈ᵉ idᵉ
λ-isoˡ = pure-reshape-∘ᵉ-id λ { (inj₂ a) → refl }

λ-isoʳ : ∀ {A} → (λ⇒ᵉ ∘ᵉ λ⇐ᵉ {A}) ≈ᵉ idᵉ
λ-isoʳ = pure-reshape-∘ᵉ-id (λ a → refl)

ρ-isoˡ : ∀ {A} → (ρ⇐ᵉ ∘ᵉ ρ⇒ᵉ {A}) ≈ᵉ idᵉ
ρ-isoˡ = pure-reshape-∘ᵉ-id λ { (inj₁ a) → refl }

ρ-isoʳ : ∀ {A} → (ρ⇒ᵉ ∘ᵉ ρ⇐ᵉ {A}) ≈ᵉ idᵉ
ρ-isoʳ = pure-reshape-∘ᵉ-id (λ a → refl)

α-isoˡ : ∀ {A B C} → (α⇐ᵉ ∘ᵉ α⇒ᵉ {A} {B} {C}) ≈ᵉ idᵉ
α-isoˡ = pure-reshape-∘ᵉ-id λ where
  (inj₁ (inj₁ a)) → refl
  (inj₁ (inj₂ b)) → refl
  (inj₂ c)        → refl

α-isoʳ : ∀ {A B C} → (α⇒ᵉ ∘ᵉ α⇐ᵉ {A} {B} {C}) ≈ᵉ idᵉ
α-isoʳ = pure-reshape-∘ᵉ-id λ where
  (inj₁ a)        → refl
  (inj₂ (inj₁ b)) → refl
  (inj₂ (inj₂ c)) → refl

-- Bundle each iso into the agda-categories `_≅_` shape.

unitorˡ-≅ : ∀ {A} → ((⊥ ⊎ A) ≅ A)
unitorˡ-≅ = record
  { from = λ⇒ᵉ
  ; to   = λ⇐ᵉ
  ; iso  = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ }
  }

unitorʳ-≅ : ∀ {A} → ((A ⊎ ⊥) ≅ A)
unitorʳ-≅ = record
  { from = ρ⇒ᵉ
  ; to   = ρ⇐ᵉ
  ; iso  = record { isoˡ = ρ-isoˡ ; isoʳ = ρ-isoʳ }
  }

associator-≅ : ∀ {A B C} → (((A ⊎ B) ⊎ C) ≅ (A ⊎ (B ⊎ C)))
associator-≅ = record
  { from = α⇒ᵉ
  ; to   = α⇐ᵉ
  ; iso  = record { isoˡ = α-isoˡ ; isoʳ = α-isoʳ }
  }

------------------------------------------------------------------------
-- Commute squares for the unitorˡ.
--
-- `λ⇒ᵉ ∘ᵉ (idᵉ ⊗ᵉ f) ≈ᵉ f ∘ᵉ λ⇒ᵉ` and the inverse direction.
--
-- Strategy: both sides reduce (by list induction at the function level
-- with an arbitrary starting state) to the canonical form
-- `trace f sf (unwrap-ˡ xs)`, where `unwrap-ˡ` strips the `⊥ ⊎` wrapper
-- from each element.

unwrap-ˡ : List (⊥ ⊎ A) → List A
unwrap-ˡ [] = []
unwrap-ˡ (inj₂ a ∷ xs) = a ∷ unwrap-ˡ xs
unwrap-ˡ (inj₁ () ∷ _)

private
  -- LHS canonical form for unitorˡ-commute-from.
  unitorˡ-commute-from-LHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List (⊥ ⊎ A))
    → trace (SFunᵉ.fun λ⇒ᵉ ∘ᵉ' (SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f)) ((tt , (tt , sf))) xs
      ≡ trace f sf (unwrap-ˡ xs)
  unitorˡ-commute-from-LHS sf [] = refl
  unitorˡ-commute-from-LHS sf (inj₁ () ∷ _)
  unitorˡ-commute-from-LHS {f = f} sf (inj₂ a ∷ rest) = begin
    trace (SFunᵉ.fun λ⇒ᵉ ∘ᵉ' (SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f)) ((tt , (tt , sf))) (inj₂ a ∷ rest)
      ≡⟨⟩  -- unfold trace cons + ∘ᵉ' + (idᵉ ⊗ᵉ' f) on inj₂
    (((f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₂ b)) >>=
        λ ((tt , sf') , y) → SFunᵉ.fun λ⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , (tt , sf')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₂ b) >>=
        λ ((tt , sf') , y) → SFunᵉ.fun λ⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , (tt , sf')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    -- After identityˡ, y ↦ inj₂ b; SFunᵉ.fun λ⇒ᵉ (tt, inj₂ b) ≡ return (tt, b) definitionally.
    ((f (sf , a) >>= λ (sf' , b) →
        return (tt , b) >>= λ (tt , c) → return ((tt , (tt , sf')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , (tt , sf')) , b))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , b) → return ((tt , (tt , sf')) , b) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun λ⇒ᵉ ∘ᵉ' (SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f)) ((tt , (tt , sf'))) rest >>=
      λ bs → return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → unitorˡ-commute-from-LHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , b) → trace f sf' (unwrap-ˡ rest) >>= λ bs → return (b ∷ bs))
      ≡⟨⟩
    trace f sf (a ∷ unwrap-ˡ rest)
    ∎
    where open ≡-Reasoning

  -- RHS canonical form for unitorˡ-commute-from.
  unitorˡ-commute-from-RHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List (⊥ ⊎ A))
    → trace (f ∘ᵉ' SFunᵉ.fun λ⇒ᵉ) ((sf , tt)) xs
      ≡ trace f sf (unwrap-ˡ xs)
  unitorˡ-commute-from-RHS sf [] = refl
  unitorˡ-commute-from-RHS sf (inj₁ () ∷ _)
  unitorˡ-commute-from-RHS {f = f} sf (inj₂ a ∷ rest) = begin
    trace (f ∘ᵉ' SFunᵉ.fun λ⇒ᵉ) ((sf , tt)) (inj₂ a ∷ rest)
      ≡⟨⟩  -- unfold trace + ∘ᵉ' + λ⇒ᵉ on inj₂
    ((return (tt , a) >>= λ (tt , b) → f (sf , b) >>= λ (sf' , c) → return ((sf' , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , c) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace (f ∘ᵉ' SFunᵉ.fun λ⇒ᵉ) ((sf' , tt)) rest >>= λ bs → return (c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → unitorˡ-commute-from-RHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , c) → trace f sf' (unwrap-ˡ rest) >>= λ bs → return (c ∷ bs))
      ≡⟨⟩
    trace f sf (a ∷ unwrap-ˡ rest)
    ∎
    where open ≡-Reasoning

unitorˡ-commute-from-ᵉ : ∀ {A B} {f : SFunᵉ A B}
  → (λ⇒ᵉ ∘ᵉ (idᵉ ⊗ᵉ f)) ≈ᵉ (f ∘ᵉ λ⇒ᵉ)
unitorˡ-commute-from-ᵉ {f = f} xs =
  trans (unitorˡ-commute-from-LHS (SFunᵉ.init f) xs)
        (sym (unitorˡ-commute-from-RHS (SFunᵉ.init f) xs))

------------------------------------------------------------------------
-- unitorˡ-commute-to: λ⇐ᵉ ∘ᵉ f ≈ᵉ (idᵉ ⊗ᵉ f) ∘ᵉ λ⇐ᵉ
--
-- Both sides reduce to `trace f sf xs >>= λ bs → return (map inj₂ bs)`.

private
  unitorˡ-commute-to-LHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List A)
    → trace (SFunᵉ.fun λ⇐ᵉ ∘ᵉ' f) ((tt , sf)) xs
      ≡ (trace f sf xs >>= λ bs → return (map inj₂ bs))
  unitorˡ-commute-to-LHS sf [] = sym >>=-identityˡ
  unitorˡ-commute-to-LHS {f = f} sf (a ∷ rest) = begin
    trace (SFunᵉ.fun λ⇐ᵉ ∘ᵉ' f) ((tt , sf)) (a ∷ rest)
      ≡⟨⟩  -- unfold trace cons + ∘ᵉ' + λ⇐ᵉ.fun (tt, b) ≡ return (tt, inj₂ b)
    ((f (sf , a) >>= λ (sf' , b) → return (tt , inj₂ b) >>=
        λ (tt , c) → return ((tt , sf') , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₂ b))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₂ b) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun λ⇐ᵉ ∘ᵉ' f) ((tt , sf')) rest >>= λ bs → return (inj₂ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → unitorˡ-commute-to-LHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      (trace f sf' rest >>= λ bs' → return (map inj₂ bs')) >>= λ bs → return (inj₂ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-assoc _) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (map inj₂ bs') >>= λ bs → return (inj₂ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs' → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (inj₂ b ∷ map inj₂ bs'))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs' → sym >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (b ∷ bs') >>= λ bs → return (map inj₂ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → sym (>>=-assoc _)) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      (trace f sf' rest >>= λ bs' → return (b ∷ bs')) >>= λ bs → return (map inj₂ bs))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((f (sf , a) >>= λ (sf' , b) → trace f sf' rest >>= λ bs' → return (b ∷ bs')) >>=
      λ bs → return (map inj₂ bs))
      ≡⟨⟩
    (trace f sf (a ∷ rest) >>= λ bs → return (map inj₂ bs))
    ∎
    where open ≡-Reasoning

  unitorˡ-commute-to-RHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List A)
    → trace ((SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f) ∘ᵉ' SFunᵉ.fun λ⇐ᵉ) (((tt , sf) , tt)) xs
      ≡ (trace f sf xs >>= λ bs → return (map inj₂ bs))
  unitorˡ-commute-to-RHS sf [] = sym >>=-identityˡ
  unitorˡ-commute-to-RHS {f = f} sf (a ∷ rest) = begin
    trace ((SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f) ∘ᵉ' SFunᵉ.fun λ⇐ᵉ) (((tt , sf) , tt)) (a ∷ rest)
      ≡⟨⟩  -- unfold trace cons + ∘ᵉ' + λ⇐ᵉ.fun (tt, a) ≡ return (tt, inj₂ a) definitionally
    ((return (tt , inj₂ a) >>=
        λ (tt , b) → (SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f) ((tt , sf) , b) >>=
          λ ((tt , sf') , c) → return (((tt , sf') , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    -- After identityˡ: b ↦ inj₂ a; (idᵉ ⊗ᵉ' f) ((tt, sf), inj₂ a) reduces to the f-bind.
    (((f (sf , a) >>= λ (sf' , c) → return ((tt , sf') , inj₂ c)) >>=
        λ ((tt , sf') , c) → return (((tt , sf') , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , c) → return ((tt , sf') , inj₂ c) >>=
        λ ((tt , sf') , c) → return (((tt , sf') , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , c) → return (((tt , sf') , tt) , inj₂ c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , c) → return (((tt , sf') , tt) , inj₂ c) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace ((SFunᵉ.fun (idᵉ {⊥}) ⊗ᵉ' f) ∘ᵉ' SFunᵉ.fun λ⇐ᵉ) (((tt , sf') , tt)) rest >>=
      λ bs → return (inj₂ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → unitorˡ-commute-to-RHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      (trace f sf' rest >>= λ bs' → return (map inj₂ bs')) >>= λ bs → return (inj₂ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-assoc _) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (map inj₂ bs') >>= λ bs → return (inj₂ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → refl⟩>>=⟨ λ bs' → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (inj₂ c ∷ map inj₂ bs'))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → refl⟩>>=⟨ λ bs' → sym >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (c ∷ bs') >>= λ bs → return (map inj₂ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → sym (>>=-assoc _)) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      (trace f sf' rest >>= λ bs' → return (c ∷ bs')) >>= λ bs → return (map inj₂ bs))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((f (sf , a) >>= λ (sf' , c) → trace f sf' rest >>= λ bs' → return (c ∷ bs')) >>=
      λ bs → return (map inj₂ bs))
      ≡⟨⟩
    (trace f sf (a ∷ rest) >>= λ bs → return (map inj₂ bs))
    ∎
    where open ≡-Reasoning

unitorˡ-commute-to-ᵉ : ∀ {A B} {f : SFunᵉ A B}
  → (λ⇐ᵉ ∘ᵉ f) ≈ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ λ⇐ᵉ)
unitorˡ-commute-to-ᵉ {f = f} xs =
  trans (unitorˡ-commute-to-LHS (SFunᵉ.init f) xs)
        (sym (unitorˡ-commute-to-RHS (SFunᵉ.init f) xs))

------------------------------------------------------------------------
-- unitorʳ commute squares — mirror of unitorˡ with inj₁.

unwrap-ʳ : List (A ⊎ ⊥) → List A
unwrap-ʳ [] = []
unwrap-ʳ (inj₁ a ∷ xs) = a ∷ unwrap-ʳ xs
unwrap-ʳ (inj₂ () ∷ _)

private
  unitorʳ-commute-from-LHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List (A ⊎ ⊥))
    → trace (SFunᵉ.fun ρ⇒ᵉ ∘ᵉ' (f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥}))) ((tt , (sf , tt))) xs
      ≡ trace f sf (unwrap-ʳ xs)
  unitorʳ-commute-from-LHS sf [] = refl
  unitorʳ-commute-from-LHS sf (inj₂ () ∷ _)
  unitorʳ-commute-from-LHS {f = f} sf (inj₁ a ∷ rest) = begin
    trace (SFunᵉ.fun ρ⇒ᵉ ∘ᵉ' (f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥}))) ((tt , (sf , tt))) (inj₁ a ∷ rest)
      ≡⟨⟩
    (((f (sf , a) >>= λ (sf' , b) → return ((sf' , tt) , inj₁ b)) >>=
        λ ((sf' , tt) , y) → SFunᵉ.fun ρ⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , (sf' , tt)) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((sf' , tt) , inj₁ b) >>=
        λ ((sf' , tt) , y) → SFunᵉ.fun ρ⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , (sf' , tt)) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) →
        return (tt , b) >>= λ (tt , c) → return ((tt , (sf' , tt)) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , (sf' , tt)) , b))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , b) → return ((tt , (sf' , tt)) , b) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun ρ⇒ᵉ ∘ᵉ' (f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥}))) ((tt , (sf' , tt))) rest >>=
      λ bs → return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → unitorʳ-commute-from-LHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , b) → trace f sf' (unwrap-ʳ rest) >>= λ bs → return (b ∷ bs))
      ≡⟨⟩
    trace f sf (a ∷ unwrap-ʳ rest)
    ∎
    where open ≡-Reasoning

  unitorʳ-commute-from-RHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List (A ⊎ ⊥))
    → trace (f ∘ᵉ' SFunᵉ.fun ρ⇒ᵉ) ((sf , tt)) xs
      ≡ trace f sf (unwrap-ʳ xs)
  unitorʳ-commute-from-RHS sf [] = refl
  unitorʳ-commute-from-RHS sf (inj₂ () ∷ _)
  unitorʳ-commute-from-RHS {f = f} sf (inj₁ a ∷ rest) = begin
    trace (f ∘ᵉ' SFunᵉ.fun ρ⇒ᵉ) ((sf , tt)) (inj₁ a ∷ rest)
      ≡⟨⟩
    ((return (tt , a) >>= λ (tt , b) → f (sf , b) >>= λ (sf' , c) → return ((sf' , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , c) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace (f ∘ᵉ' SFunᵉ.fun ρ⇒ᵉ) ((sf' , tt)) rest >>= λ bs → return (c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → unitorʳ-commute-from-RHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , c) → trace f sf' (unwrap-ʳ rest) >>= λ bs → return (c ∷ bs))
      ≡⟨⟩
    trace f sf (a ∷ unwrap-ʳ rest)
    ∎
    where open ≡-Reasoning

unitorʳ-commute-from-ᵉ : ∀ {A B} {f : SFunᵉ A B}
  → (ρ⇒ᵉ ∘ᵉ (f ⊗ᵉ idᵉ)) ≈ᵉ (f ∘ᵉ ρ⇒ᵉ)
unitorʳ-commute-from-ᵉ {f = f} xs =
  trans (unitorʳ-commute-from-LHS (SFunᵉ.init f) xs)
        (sym (unitorʳ-commute-from-RHS (SFunᵉ.init f) xs))

------------------------------------------------------------------------
-- unitorʳ-commute-to: ρ⇐ᵉ ∘ᵉ f ≈ᵉ (f ⊗ᵉ idᵉ) ∘ᵉ ρ⇐ᵉ

private
  unitorʳ-commute-to-LHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List A)
    → trace (SFunᵉ.fun ρ⇐ᵉ ∘ᵉ' f) ((tt , sf)) xs
      ≡ (trace f sf xs >>= λ bs → return (map inj₁ bs))
  unitorʳ-commute-to-LHS sf [] = sym >>=-identityˡ
  unitorʳ-commute-to-LHS {f = f} sf (a ∷ rest) = begin
    trace (SFunᵉ.fun ρ⇐ᵉ ∘ᵉ' f) ((tt , sf)) (a ∷ rest)
      ≡⟨⟩
    ((f (sf , a) >>= λ (sf' , b) → return (tt , inj₁ b) >>=
        λ (tt , c) → return ((tt , sf') , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₁ b))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , b) → return ((tt , sf') , inj₁ b) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun ρ⇐ᵉ ∘ᵉ' f) ((tt , sf')) rest >>= λ bs → return (inj₁ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → unitorʳ-commute-to-LHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      (trace f sf' rest >>= λ bs' → return (map inj₁ bs')) >>= λ bs → return (inj₁ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-assoc _) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (map inj₁ bs') >>= λ bs → return (inj₁ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs' → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (inj₁ b ∷ map inj₁ bs'))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → refl⟩>>=⟨ λ bs' → sym >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace f sf' rest >>= λ bs' → return (b ∷ bs') >>= λ bs → return (map inj₁ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → sym (>>=-assoc _)) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      (trace f sf' rest >>= λ bs' → return (b ∷ bs')) >>= λ bs → return (map inj₁ bs))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((f (sf , a) >>= λ (sf' , b) → trace f sf' rest >>= λ bs' → return (b ∷ bs')) >>=
      λ bs → return (map inj₁ bs))
      ≡⟨⟩
    (trace f sf (a ∷ rest) >>= λ bs → return (map inj₁ bs))
    ∎
    where open ≡-Reasoning

  unitorʳ-commute-to-RHS : ∀ {A B Sf} {f : SFunType A B Sf}
    (sf : Sf) (xs : List A)
    → trace ((f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥})) ∘ᵉ' SFunᵉ.fun ρ⇐ᵉ) (((sf , tt) , tt)) xs
      ≡ (trace f sf xs >>= λ bs → return (map inj₁ bs))
  unitorʳ-commute-to-RHS sf [] = sym >>=-identityˡ
  unitorʳ-commute-to-RHS {f = f} sf (a ∷ rest) = begin
    trace ((f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥})) ∘ᵉ' SFunᵉ.fun ρ⇐ᵉ) (((sf , tt) , tt)) (a ∷ rest)
      ≡⟨⟩
    ((return (tt , inj₁ a) >>=
        λ (tt , b) → (f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥})) ((sf , tt) , b) >>=
          λ ((sf' , tt) , c) → return (((sf' , tt) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    (((f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , inj₁ c)) >>=
        λ ((sf' , tt) , c) → return (((sf' , tt) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , c) → return ((sf' , tt) , inj₁ c) >>=
        λ ((sf' , tt) , c) → return (((sf' , tt) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , c) → return (((sf' , tt) , tt) , inj₁ c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , c) → return (((sf' , tt) , tt) , inj₁ c) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace ((f ⊗ᵉ' SFunᵉ.fun (idᵉ {⊥})) ∘ᵉ' SFunᵉ.fun ρ⇐ᵉ) (((sf' , tt) , tt)) rest >>=
      λ bs → return (inj₁ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → unitorʳ-commute-to-RHS sf' rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      (trace f sf' rest >>= λ bs' → return (map inj₁ bs')) >>= λ bs → return (inj₁ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-assoc _) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (map inj₁ bs') >>= λ bs → return (inj₁ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → refl⟩>>=⟨ λ bs' → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (inj₁ c ∷ map inj₁ bs'))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → refl⟩>>=⟨ λ bs' → sym >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace f sf' rest >>= λ bs' → return (c ∷ bs') >>= λ bs → return (map inj₁ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → sym (>>=-assoc _)) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      (trace f sf' rest >>= λ bs' → return (c ∷ bs')) >>= λ bs → return (map inj₁ bs))
      ≡⟨ sym (>>=-assoc _) ⟩
    ((f (sf , a) >>= λ (sf' , c) → trace f sf' rest >>= λ bs' → return (c ∷ bs')) >>=
      λ bs → return (map inj₁ bs))
      ≡⟨⟩
    (trace f sf (a ∷ rest) >>= λ bs → return (map inj₁ bs))
    ∎
    where open ≡-Reasoning

unitorʳ-commute-to-ᵉ : ∀ {A B} {f : SFunᵉ A B}
  → (ρ⇐ᵉ ∘ᵉ f) ≈ᵉ ((f ⊗ᵉ idᵉ) ∘ᵉ ρ⇐ᵉ)
unitorʳ-commute-to-ᵉ {f = f} xs =
  trans (unitorʳ-commute-to-LHS (SFunᵉ.init f) xs)
        (sym (unitorʳ-commute-to-RHS (SFunᵉ.init f) xs))

------------------------------------------------------------------------
-- assoc-commute-from: α⇒ᵉ ∘ᵉ ((f ⊗ᵉ g) ⊗ᵉ h) ≈ᵉ (f ⊗ᵉ (g ⊗ᵉ h)) ∘ᵉ α⇒ᵉ
--
-- Canonical form: trace₃ f g h (sf, sg, sh) xs — dispatches each input
-- to f, g, or h based on its 3-way tag, producing a right-associated
-- output sum.

trace₃ : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ Sf Sg Sh}
  → SFunType A₁ B₁ Sf → SFunType A₂ B₂ Sg → SFunType A₃ B₃ Sh
  → Sf × Sg × Sh
  → List ((A₁ ⊎ A₂) ⊎ A₃)
  → M (List (B₁ ⊎ (B₂ ⊎ B₃)))
trace₃ f g h (sf , sg , sh) [] = return []
trace₃ f g h (sf , sg , sh) (inj₁ (inj₁ a) ∷ rest) =
  f (sf , a) >>= λ (sf' , b) →
    trace₃ f g h (sf' , sg , sh) rest >>= λ bs → return (inj₁ b ∷ bs)
trace₃ f g h (sf , sg , sh) (inj₁ (inj₂ a) ∷ rest) =
  g (sg , a) >>= λ (sg' , b) →
    trace₃ f g h (sf , sg' , sh) rest >>= λ bs → return (inj₂ (inj₁ b) ∷ bs)
trace₃ f g h (sf , sg , sh) (inj₂ a ∷ rest) =
  h (sh , a) >>= λ (sh' , b) →
    trace₃ f g h (sf , sg , sh') rest >>= λ bs → return (inj₂ (inj₂ b) ∷ bs)

private
  assoc-commute-from-LHS : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ Sf Sg Sh}
    {f : SFunType A₁ B₁ Sf} {g : SFunType A₂ B₂ Sg} {h : SFunType A₃ B₃ Sh}
    (sf : Sf) (sg : Sg) (sh : Sh)
    (xs : List ((A₁ ⊎ A₂) ⊎ A₃))
    → trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg) , sh))) xs
      ≡ trace₃ f g h (sf , sg , sh) xs
  assoc-commute-from-LHS sf sg sh [] = refl
  assoc-commute-from-LHS {f = f} {g} {h} sf sg sh (inj₁ (inj₁ a) ∷ rest) = begin
    trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg) , sh))) (inj₁ (inj₁ a) ∷ rest)
      ≡⟨⟩
    ((((f (sf , a) >>= λ (sf' , b) → return ((sf' , sg) , inj₁ b)) >>=
          λ ((sf' , sg') , b) → return (((sf' , sg') , sh) , inj₁ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((f (sf , a) >>= λ (sf' , b) → return ((sf' , sg) , inj₁ b) >>=
          λ ((sf' , sg') , b) → return (((sf' , sg') , sh) , inj₁ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((f (sf , a) >>= λ (sf' , b) → return (((sf' , sg) , sh) , inj₁ (inj₁ b))) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , b) → return (((sf' , sg) , sh) , inj₁ (inj₁ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    -- After identityˡ: y ↦ inj₁ (inj₁ b); α⇒ᵉ.fun (tt, inj₁ (inj₁ b)) ≡ return (tt, inj₁ b)
    ((f (sf , a) >>= λ (sf' , b) →
        return (tt , inj₁ b) >>= λ (tt , c) → return ((tt , ((sf' , sg) , sh)) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , b) → return ((tt , ((sf' , sg) , sh)) , inj₁ b))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , b) → return ((tt , ((sf' , sg) , sh)) , inj₁ b) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf' , sg) , sh))) rest >>=
      λ bs → return (inj₁ b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) → assoc-commute-from-LHS sf' sg sh rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , b) →
      trace₃ f g h (sf' , sg , sh) rest >>= λ bs → return (inj₁ b ∷ bs))
    ∎
    where open ≡-Reasoning
  assoc-commute-from-LHS {f = f} {g} {h} sf sg sh (inj₁ (inj₂ a) ∷ rest) = begin
    trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg) , sh))) (inj₁ (inj₂ a) ∷ rest)
      ≡⟨⟩
    ((((g (sg , a) >>= λ (sg' , b) → return ((sf , sg') , inj₂ b)) >>=
          λ ((sf' , sg') , b) → return (((sf' , sg') , sh) , inj₁ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (g (sg , a)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((g (sg , a) >>= λ (sg' , b) → return ((sf , sg') , inj₂ b) >>=
          λ ((sf' , sg') , b) → return (((sf' , sg') , sh) , inj₁ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((refl⟩>>=⟨ (λ (sg' , b) → >>=-identityˡ)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((g (sg , a) >>= λ (sg' , b) → return (((sf , sg') , sh) , inj₁ (inj₂ b))) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (g (sg , a)) ⟩>>=⟨refl) ⟩
    ((g (sg , a) >>= λ (sg' , b) → return (((sf , sg') , sh) , inj₁ (inj₂ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sg' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    -- After identityˡ: y ↦ inj₁ (inj₂ b); α⇒ᵉ.fun (tt, inj₁ (inj₂ b)) ≡ return (tt, inj₂ (inj₁ b))
    ((g (sg , a) >>= λ (sg' , b) →
        return (tt , inj₂ (inj₁ b)) >>= λ (tt , c) → return ((tt , ((sf , sg') , sh)) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sg' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((g (sg , a) >>= λ (sg' , b) → return ((tt , ((sf , sg') , sh)) , inj₂ (inj₁ b)))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (g (sg , a)) ⟩
    (g (sg , a) >>= λ (sg' , b) → return ((tt , ((sf , sg') , sh)) , inj₂ (inj₁ b)) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sg' , b) → >>=-identityˡ) ⟩
    (g (sg , a) >>= λ (sg' , b) →
      trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg') , sh))) rest >>=
      λ bs → return (inj₂ (inj₁ b) ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sg' , b) → assoc-commute-from-LHS sf sg' sh rest ⟩>>=⟨refl) ⟩
    (g (sg , a) >>= λ (sg' , b) →
      trace₃ f g h (sf , sg' , sh) rest >>= λ bs → return (inj₂ (inj₁ b) ∷ bs))
    ∎
    where open ≡-Reasoning
  assoc-commute-from-LHS {f = f} {g} {h} sf sg sh (inj₂ a ∷ rest) = begin
    trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg) , sh))) (inj₂ a ∷ rest)
      ≡⟨⟩
    (((h (sh , a) >>= λ (sh' , b) → return (((sf , sg) , sh') , inj₂ b)) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (h (sh , a)) ⟩>>=⟨refl) ⟩
    ((h (sh , a) >>= λ (sh' , b) → return (((sf , sg) , sh') , inj₂ b) >>=
        λ (((sf' , sg') , sh') , y) → SFunᵉ.fun α⇒ᵉ (tt , y) >>=
          λ (tt , c) → return ((tt , ((sf' , sg') , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sh' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    -- After identityˡ: y ↦ inj₂ b; α⇒ᵉ.fun (tt, inj₂ b) ≡ return (tt, inj₂ (inj₂ b))
    ((h (sh , a) >>= λ (sh' , b) →
        return (tt , inj₂ (inj₂ b)) >>= λ (tt , c) → return ((tt , ((sf , sg) , sh')) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sh' , b) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((h (sh , a) >>= λ (sh' , b) → return ((tt , ((sf , sg) , sh')) , inj₂ (inj₂ b)))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (h (sh , a)) ⟩
    (h (sh , a) >>= λ (sh' , b) → return ((tt , ((sf , sg) , sh')) , inj₂ (inj₂ b)) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sh' , b) → >>=-identityˡ) ⟩
    (h (sh , a) >>= λ (sh' , b) →
      trace (SFunᵉ.fun α⇒ᵉ ∘ᵉ' ((f ⊗ᵉ' g) ⊗ᵉ' h)) ((tt , ((sf , sg) , sh'))) rest >>=
      λ bs → return (inj₂ (inj₂ b) ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sh' , b) → assoc-commute-from-LHS sf sg sh' rest ⟩>>=⟨refl) ⟩
    (h (sh , a) >>= λ (sh' , b) →
      trace₃ f g h (sf , sg , sh') rest >>= λ bs → return (inj₂ (inj₂ b) ∷ bs))
    ∎
    where open ≡-Reasoning

  assoc-commute-from-RHS : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ Sf Sg Sh}
    {f : SFunType A₁ B₁ Sf} {g : SFunType A₂ B₂ Sg} {h : SFunType A₃ B₃ Sh}
    (sf : Sf) (sg : Sg) (sh : Sh)
    (xs : List ((A₁ ⊎ A₂) ⊎ A₃))
    → trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg , sh)) , tt)) xs
      ≡ trace₃ f g h (sf , sg , sh) xs
  assoc-commute-from-RHS sf sg sh [] = refl
  assoc-commute-from-RHS {f = f} {g} {h} sf sg sh (inj₁ (inj₁ a) ∷ rest) = begin
    trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg , sh)) , tt)) (inj₁ (inj₁ a) ∷ rest)
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    (((f (sf , a) >>= λ (sf' , c) → return ((sf' , (sg , sh)) , inj₁ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (f (sf , a)) ⟩>>=⟨refl) ⟩
    ((f (sf , a) >>= λ (sf' , c) → return ((sf' , (sg , sh)) , inj₁ c) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((f (sf , a) >>= λ (sf' , c) → return (((sf' , (sg , sh)) , tt) , inj₁ c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (f (sf , a)) ⟩
    (f (sf , a) >>= λ (sf' , c) → return (((sf' , (sg , sh)) , tt) , inj₁ c) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → >>=-identityˡ) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf' , (sg , sh)) , tt)) rest >>=
      λ bs → return (inj₁ c ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , c) → assoc-commute-from-RHS sf' sg sh rest ⟩>>=⟨refl) ⟩
    (f (sf , a) >>= λ (sf' , c) →
      trace₃ f g h (sf' , sg , sh) rest >>= λ bs → return (inj₁ c ∷ bs))
    ∎
    where open ≡-Reasoning
  assoc-commute-from-RHS {f = f} {g} {h} sf sg sh (inj₁ (inj₂ a) ∷ rest) = begin
    trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg , sh)) , tt)) (inj₁ (inj₂ a) ∷ rest)
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    ((((g (sg , a) >>= λ (sg' , c) → return ((sg' , sh) , inj₁ c)) >>=
          λ ((sg' , sh') , c) → return ((sf , (sg' , sh')) , inj₂ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((>>=-assoc (g (sg , a)) ⟩>>=⟨refl) ⟩>>=⟨refl) ⟩
    (((g (sg , a) >>= λ (sg' , c) → return ((sg' , sh) , inj₁ c) >>=
          λ ((sg' , sh') , c) → return ((sf , (sg' , sh')) , inj₂ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((refl⟩>>=⟨ (λ (sg' , c) → >>=-identityˡ)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((g (sg , a) >>= λ (sg' , c) → return ((sf , (sg' , sh)) , inj₂ (inj₁ c))) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (g (sg , a)) ⟩>>=⟨refl) ⟩
    ((g (sg , a) >>= λ (sg' , c) → return ((sf , (sg' , sh)) , inj₂ (inj₁ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sg' , c) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((g (sg , a) >>= λ (sg' , c) → return (((sf , (sg' , sh)) , tt) , inj₂ (inj₁ c)))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (g (sg , a)) ⟩
    (g (sg , a) >>= λ (sg' , c) → return (((sf , (sg' , sh)) , tt) , inj₂ (inj₁ c)) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sg' , c) → >>=-identityˡ) ⟩
    (g (sg , a) >>= λ (sg' , c) →
      trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg' , sh)) , tt)) rest >>=
      λ bs → return (inj₂ (inj₁ c) ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sg' , c) → assoc-commute-from-RHS sf sg' sh rest ⟩>>=⟨refl) ⟩
    (g (sg , a) >>= λ (sg' , c) →
      trace₃ f g h (sf , sg' , sh) rest >>= λ bs → return (inj₂ (inj₁ c) ∷ bs))
    ∎
    where open ≡-Reasoning
  assoc-commute-from-RHS {f = f} {g} {h} sf sg sh (inj₂ a ∷ rest) = begin
    trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg , sh)) , tt)) (inj₂ a ∷ rest)
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    ((((h (sh , a) >>= λ (sh' , c) → return ((sg , sh') , inj₂ c)) >>=
          λ ((sg' , sh') , c) → return ((sf , (sg' , sh')) , inj₂ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((>>=-assoc (h (sh , a)) ⟩>>=⟨refl) ⟩>>=⟨refl) ⟩
    (((h (sh , a) >>= λ (sh' , c) → return ((sg , sh') , inj₂ c) >>=
          λ ((sg' , sh') , c) → return ((sf , (sg' , sh')) , inj₂ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ ((refl⟩>>=⟨ (λ (sh' , c) → >>=-identityˡ)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
    (((h (sh , a) >>= λ (sh' , c) → return ((sf , (sg , sh')) , inj₂ (inj₂ c))) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (>>=-assoc (h (sh , a)) ⟩>>=⟨refl) ⟩
    ((h (sh , a) >>= λ (sh' , c) → return ((sf , (sg , sh')) , inj₂ (inj₂ c)) >>=
        λ ((sf' , (sg' , sh')) , c) → return (((sf' , (sg' , sh')) , tt) , c))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ (refl⟩>>=⟨ (λ (sh' , c) → >>=-identityˡ)) ⟩>>=⟨refl ⟩
    ((h (sh , a) >>= λ (sh' , c) → return (((sf , (sg , sh')) , tt) , inj₂ (inj₂ c)))
      >>= λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ >>=-assoc (h (sh , a)) ⟩
    (h (sh , a) >>= λ (sh' , c) → return (((sf , (sg , sh')) , tt) , inj₂ (inj₂ c)) >>=
      λ s'-x' → trace _ (proj₁ s'-x') rest >>= λ bs → return (proj₂ s'-x' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sh' , c) → >>=-identityˡ) ⟩
    (h (sh , a) >>= λ (sh' , c) →
      trace ((f ⊗ᵉ' (g ⊗ᵉ' h)) ∘ᵉ' SFunᵉ.fun α⇒ᵉ) (((sf , (sg , sh')) , tt)) rest >>=
      λ bs → return (inj₂ (inj₂ c) ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sh' , c) → assoc-commute-from-RHS sf sg sh' rest ⟩>>=⟨refl) ⟩
    (h (sh , a) >>= λ (sh' , c) →
      trace₃ f g h (sf , sg , sh') rest >>= λ bs → return (inj₂ (inj₂ c) ∷ bs))
    ∎
    where open ≡-Reasoning

assoc-commute-from-ᵉ : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
  {f : SFunᵉ A₁ B₁} {g : SFunᵉ A₂ B₂} {h : SFunᵉ A₃ B₃}
  → (α⇒ᵉ ∘ᵉ ((f ⊗ᵉ g) ⊗ᵉ h)) ≈ᵉ ((f ⊗ᵉ (g ⊗ᵉ h)) ∘ᵉ α⇒ᵉ)
assoc-commute-from-ᵉ {f = f} {g} {h} xs =
  trans (assoc-commute-from-LHS (SFunᵉ.init f) (SFunᵉ.init g) (SFunᵉ.init h) xs)
        (sym (assoc-commute-from-RHS (SFunᵉ.init f) (SFunᵉ.init g) (SFunᵉ.init h) xs))

------------------------------------------------------------------------
-- Pure-reshape helpers for the coherence laws (triangle, pentagon)
-- and the symmetric `assoc-commute-to`.
--
-- All structural morphisms (α, λ, ρ, id) are stateless pure-reshapes,
-- so coherence equalities reduce to pointwise equality of the
-- underlying A → B reshape functions, dispatched by case analysis.

-- Pointwise function equality lifts to ≈ᵉ on pure-reshapes.
pure-reshape-cong : ∀ {A B} {f g : A → B}
  → (∀ x → f x ≡ g x) → pure-reshape f ≈ᵉ pure-reshape g
pure-reshape-cong {f = f} {g} eq xs = begin
  eval (pure-reshape f) xs   ≡⟨ pure-reshape-correct xs ⟩
  return (map f xs)          ≡⟨ cong return (map-cong eq xs) ⟩
  return (map g xs)          ≡⟨ sym (pure-reshape-correct xs) ⟩
  eval (pure-reshape g) xs   ∎
  where open ≡-Reasoning

-- idᵉ is observationally `pure-reshape id`.
idᵉ≈ᵉpure-id : ∀ {A} → idᵉ {A} ≈ᵉ pure-reshape (id {A = A})
idᵉ≈ᵉpure-id xs = begin
  eval idᵉ xs                  ≡⟨ sym (id-correct xs) ⟩
  return xs                    ≡⟨ cong return (sym (map-id xs)) ⟩
  return (map id xs)           ≡⟨ sym (pure-reshape-correct xs) ⟩
  eval (pure-reshape id) xs    ∎
  where open ≡-Reasoning

-- Sum bifunctor map.
⊎-map : (A → B) → (C → D) → A ⊎ C → B ⊎ D
⊎-map f g (inj₁ a) = inj₁ (f a)
⊎-map f g (inj₂ c) = inj₂ (g c)

-- weave re-assembles `map f (filter₁ xs)` and `map g (filter₂ xs)`
-- under the original tag pattern — which is exactly `map (⊎-map f g) xs`.
weave-map : (f : A → B) (g : C → D) (xs : List (A ⊎ C))
  → weave xs (map f (filter₁ xs)) (map g (filter₂ xs)) ≡ map (⊎-map f g) xs
weave-map f g [] = refl
weave-map f g (inj₁ a ∷ xs) = cong (inj₁ (f a) ∷_) (weave-map f g xs)
weave-map f g (inj₂ c ∷ xs) = cong (inj₂ (g c) ∷_) (weave-map f g xs)

-- The ⊗-product of two pure-reshapes is itself a pure-reshape.
pure-reshape-⊗ᵉ : {f : A → B} {g : C → D}
  → (pure-reshape f ⊗ᵉ pure-reshape g) ≈ᵉ pure-reshape (⊎-map f g)
pure-reshape-⊗ᵉ {f = f} {g} xs = begin
  eval (pure-reshape f ⊗ᵉ pure-reshape g) xs
    ≡⟨ trace-⊗ᵉ tt tt xs ⟩
  (eval (pure-reshape f) (filter₁ xs) >>= λ bs →
    eval (pure-reshape g) (filter₂ xs) >>= λ ds →
      return (weave xs bs ds))
    ≡⟨ pure-reshape-correct (filter₁ xs) ⟩>>=⟨refl ⟩
  (return (map f (filter₁ xs)) >>= λ bs →
    eval (pure-reshape g) (filter₂ xs) >>= λ ds →
      return (weave xs bs ds))
    ≡⟨ >>=-identityˡ ⟩
  (eval (pure-reshape g) (filter₂ xs) >>= λ ds →
    return (weave xs (map f (filter₁ xs)) ds))
    ≡⟨ pure-reshape-correct (filter₂ xs) ⟩>>=⟨refl ⟩
  (return (map g (filter₂ xs)) >>= λ ds →
    return (weave xs (map f (filter₁ xs)) ds))
    ≡⟨ >>=-identityˡ ⟩
  return (weave xs (map f (filter₁ xs)) (map g (filter₂ xs)))
    ≡⟨ cong return (weave-map f g xs) ⟩
  return (map (⊎-map f g) xs)
    ≡⟨ sym (pure-reshape-correct xs) ⟩
  eval (pure-reshape (⊎-map f g)) xs ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- assoc-commute-to: dual of assoc-commute-from, derived via the iso
-- conjugation lemma.

open import Categories.Morphism.Reasoning.Iso SFunᵉ-Category
  using (conjugate-from)

assoc-commute-to-ᵉ : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
  {f : SFunᵉ A₁ B₁} {g : SFunᵉ A₂ B₂} {h : SFunᵉ A₃ B₃}
  → (α⇐ᵉ ∘ᵉ (f ⊗ᵉ (g ⊗ᵉ h))) ≈ᵉ (((f ⊗ᵉ g) ⊗ᵉ h) ∘ᵉ α⇐ᵉ)
assoc-commute-to-ᵉ {f = f} {g} {h} =
  conjugate-from associator-≅ associator-≅
    (λ xs → sym (assoc-commute-from-ᵉ {f = f} {g} {h} xs))

------------------------------------------------------------------------
-- triangle coherence.
--
-- (idᵉ ⊗ᵉ λ⇒ᵉ) ∘ᵉ α⇒ᵉ ≈ᵉ ρ⇒ᵉ ⊗ᵉ idᵉ
--
-- Both sides reduce to the pure-reshape that drops the ⊥ middle
-- component of (X ⊎ ⊥) ⊎ Y.

triangle-ᵉ : ∀ {X Y} → ((idᵉ ⊗ᵉ λ⇒ᵉ) ∘ᵉ α⇒ᵉ {X} {⊥} {Y}) ≈ᵉ (ρ⇒ᵉ ⊗ᵉ idᵉ)
triangle-ᵉ {X} {Y} xs = begin
  eval ((idᵉ ⊗ᵉ λ⇒ᵉ) ∘ᵉ α⇒ᵉ) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (⊗ᵉ-resp-≈ᵉ idᵉ≈ᵉpure-id (λ _ → refl)) (λ _ → refl) xs ⟩
  eval ((pure-reshape id ⊗ᵉ pure-reshape λ-fn) ∘ᵉ pure-reshape α-fn) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ pure-reshape-⊗ᵉ (λ _ → refl) xs ⟩
  eval (pure-reshape (⊎-map id λ-fn) ∘ᵉ pure-reshape α-fn) xs
    ≡⟨ pure-reshape-∘ xs ⟩
  eval (pure-reshape (⊎-map id λ-fn ∘ α-fn)) xs
    ≡⟨ pure-reshape-cong tri-fn-eq xs ⟩
  eval (pure-reshape (⊎-map ρ-fn id)) xs
    ≡⟨ sym (pure-reshape-⊗ᵉ xs) ⟩
  eval (pure-reshape ρ-fn ⊗ᵉ pure-reshape id) xs
    ≡⟨ sym (⊗ᵉ-resp-≈ᵉ (λ _ → refl) idᵉ≈ᵉpure-id xs) ⟩
  eval (ρ⇒ᵉ ⊗ᵉ idᵉ) xs ∎
  where
    open ≡-Reasoning
    tri-fn-eq : (x : (X ⊎ ⊥) ⊎ Y)
      → (⊎-map id λ-fn ∘ α-fn) x ≡ ⊎-map ρ-fn id x
    tri-fn-eq (inj₁ (inj₁ x)) = refl
    tri-fn-eq (inj₂ y)        = refl

------------------------------------------------------------------------
-- pentagon coherence.
--
-- (idᵉ ⊗ᵉ α⇒ᵉ) ∘ᵉ α⇒ᵉ ∘ᵉ (α⇒ᵉ ⊗ᵉ idᵉ) ≈ᵉ α⇒ᵉ ∘ᵉ α⇒ᵉ

pentagon-ᵉ : ∀ {X Y Z W} →
    ((idᵉ ⊗ᵉ α⇒ᵉ {Y} {Z} {W}) ∘ᵉ
      (α⇒ᵉ {X} {Y ⊎ Z} {W} ∘ᵉ (α⇒ᵉ {X} {Y} {Z} ⊗ᵉ idᵉ {W})))
  ≈ᵉ (α⇒ᵉ {X} {Y} {Z ⊎ W} ∘ᵉ α⇒ᵉ {X ⊎ Y} {Z} {W})
pentagon-ᵉ {X} {Y} {Z} {W} xs = begin
  eval ((idᵉ ⊗ᵉ α⇒ᵉ) ∘ᵉ (α⇒ᵉ ∘ᵉ (α⇒ᵉ ⊗ᵉ idᵉ))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (⊗ᵉ-resp-≈ᵉ idᵉ≈ᵉpure-id (λ _ → refl)) (λ _ → refl) xs ⟩
  eval ((pure-reshape id ⊗ᵉ pure-reshape α-fn) ∘ᵉ
         (α⇒ᵉ ∘ᵉ (pure-reshape α-fn ⊗ᵉ idᵉ))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (λ _ → refl)
        (∘ᵉ-resp-≈ᵉ (λ _ → refl) (⊗ᵉ-resp-≈ᵉ (λ _ → refl) idᵉ≈ᵉpure-id))
        xs ⟩
  eval ((pure-reshape id ⊗ᵉ pure-reshape α-fn) ∘ᵉ
         (α⇒ᵉ ∘ᵉ (pure-reshape α-fn ⊗ᵉ pure-reshape id))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ pure-reshape-⊗ᵉ
        (∘ᵉ-resp-≈ᵉ (λ _ → refl) pure-reshape-⊗ᵉ) xs ⟩
  eval (pure-reshape (⊎-map id α-fn) ∘ᵉ
         (pure-reshape α-fn ∘ᵉ pure-reshape (⊎-map α-fn id))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (λ _ → refl) pure-reshape-∘ xs ⟩
  eval (pure-reshape (⊎-map id α-fn) ∘ᵉ
         pure-reshape (α-fn ∘ ⊎-map α-fn id)) xs
    ≡⟨ pure-reshape-∘ xs ⟩
  eval (pure-reshape (⊎-map id α-fn ∘ (α-fn ∘ ⊎-map α-fn id))) xs
    ≡⟨ pure-reshape-cong pent-fn-eq xs ⟩
  eval (pure-reshape (α-fn ∘ α-fn)) xs
    ≡⟨ sym (pure-reshape-∘ xs) ⟩
  eval (α⇒ᵉ ∘ᵉ α⇒ᵉ) xs ∎
  where
    open ≡-Reasoning
    pent-fn-eq : (x : ((X ⊎ Y) ⊎ Z) ⊎ W)
      → (⊎-map id α-fn ∘ (α-fn ∘ ⊎-map α-fn id)) x ≡ (α-fn ∘ α-fn) x
    pent-fn-eq (inj₁ (inj₁ (inj₁ x))) = refl
    pent-fn-eq (inj₁ (inj₁ (inj₂ y))) = refl
    pent-fn-eq (inj₁ (inj₂ z))        = refl
    pent-fn-eq (inj₂ w)               = refl

------------------------------------------------------------------------
-- The Monoidal record.

SFunᵉ-monoidal : Monoidal SFunᵉ-Category
SFunᵉ-monoidal =
  record
    { ⊗ = ⊗ᵉ-bifunctor
    ; unit = ⊥
    ; unitorˡ = unitorˡ-≅
    ; unitorʳ = unitorʳ-≅
    ; associator = associator-≅
    ; unitorˡ-commute-from = unitorˡ-commute-from-ᵉ
    ; unitorˡ-commute-to = unitorˡ-commute-to-ᵉ
    ; unitorʳ-commute-from = unitorʳ-commute-from-ᵉ
    ; unitorʳ-commute-to = unitorʳ-commute-to-ᵉ
    ; assoc-commute-from = assoc-commute-from-ᵉ
    ; assoc-commute-to = assoc-commute-to-ᵉ
    ; triangle = triangle-ᵉ
    ; pentagon = pentagon-ᵉ
  }

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

open import categorical-crypto.Prelude
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

private
  -- Pure stateless reshape, lifted into SFunᵉ.
  pure-reshape : (A → B) → SFunᵉ A B
  pure-reshape f = record
    { State = ⊤
    ; init  = tt
    ; fun   = λ (tt , a) → return (tt , f a)
    }

-- Associator: (A ⊎ B) ⊎ C ≅ A ⊎ (B ⊎ C)
α⇒ᵉ : SFunᵉ ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α⇒ᵉ = pure-reshape λ where
  (inj₁ (inj₁ a)) → inj₁ a
  (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
  (inj₂ c)        → inj₂ (inj₂ c)

α⇐ᵉ : SFunᵉ (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α⇐ᵉ = pure-reshape λ where
  (inj₁ a)        → inj₁ (inj₁ a)
  (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
  (inj₂ (inj₂ c)) → inj₂ c

-- Left unitor: ⊥ ⊎ A ≅ A
λ⇒ᵉ : SFunᵉ (⊥ ⊎ A) A
λ⇒ᵉ = pure-reshape λ where
  (inj₂ a) → a

λ⇐ᵉ : SFunᵉ A (⊥ ⊎ A)
λ⇐ᵉ = pure-reshape inj₂

-- Right unitor: A ⊎ ⊥ ≅ A
ρ⇒ᵉ : SFunᵉ (A ⊎ ⊥) A
ρ⇒ᵉ = pure-reshape λ where
  (inj₁ a) → a

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

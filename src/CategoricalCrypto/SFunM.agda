{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (_>>=_; return)

open import Categories.Category.Core
open import Categories.Category.Helper
open import Categories.Category.Instance.Setoids
open import Categories.Monad.Construction.Kleisli
import Categories.Monad.Setoids.Discrete as Discrete

open import Relation.Binary

module CategoricalCrypto.SFunM (K : KleisliTriple (Setoids 0ℓ 0ℓ)) where

open Discrete K
open ≈ᴹ-Reasoning

SFunType : Type → Type → Type → Type
SFunType A B S = S × A → M (S × B)

record SFunᵉ (A B : Type) : Type₁ where
  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State State′ : Type

mkᵉ : State → SFunType A B State → SFunᵉ A B
mkᵉ {State = S} s k = record { State = S ; init = s ; fun = k }

idᵏ : SFunType A A ⊤
idᵏ (_ , a) = return (tt , a)

idᵉ : SFunᵉ A A
idᵉ = mkᵉ tt idᵏ

_∘ᵉ'_ : SFunType B C State′ → SFunType A B State → SFunType A C (State′ × State)
_∘ᵉ'_ g f ((sg , sf) , a) = do
  (sf , b) ← f (sf , a)
  (sg , c) ← g (sg , b)
  return ((sg , sf) , c)

_∘ᵉ_ : SFunᵉ B C → SFunᵉ A B → SFunᵉ A C
_∘ᵉ_ g f = let module g = SFunᵉ g; module f = SFunᵉ f in
  mkᵉ (g.init , f.init) (g.fun ∘ᵉ' f.fun)

-- Like `_⊗_`, but with shared state
[_∣_]ᵏ : SFunType A B State → SFunType C D State → SFunType (A ⊎ C) (B ⊎ D) State
[ f ∣ g ]ᵏ (s , inj₁ a) = (λ (s′ , b) → s′ , inj₁ b) <$>ᴹ f (s , a)
[ f ∣ g ]ᵏ (s , inj₂ c) = (λ (s′ , d) → s′ , inj₂ d) <$>ᴹ g (s , c)

trace : SFunType A B State → State → List A → M (List B)
trace f s [] = return []
trace f s (a ∷ as) = do
  (s , b) ← f (s , a)
  bs ← trace f s as
  return (b ∷ bs)

eval : SFunᵉ A B → List A → M (List B)
eval f as = let open SFunᵉ f in trace fun init as

infix 4 _≈ᵉ_

_≈ᵉ_ : SFunᵉ A B → SFunᵉ A B → Type
f ≈ᵉ g = ∀ xs → eval f xs ≈ᴹ eval g xs

≈ᵉ-isEquivalence : IsEquivalence (_≈ᵉ_ {A} {B})
≈ᵉ-isEquivalence = record
  { refl  = λ _ → ≈ᴹ.refl
  ; sym   = λ f≈g xs → ≈ᴹ.sym (f≈g xs)
  ; trans = λ f≈g g≈h xs → ≈ᴹ.trans (f≈g xs) (g≈h xs)
  }

module ≈ᵉ {A B : Type} = IsEquivalence (≈ᵉ-isEquivalence {A} {B})

-- Composition is associative and unital only up to the monad's commutativity.
module Laws (>>=-comm : Commutative) where

  id-correct : (xs : List A) → return xs ≈ᴹ eval idᵉ xs
  id-correct []       = ≈ᴹ.refl
  id-correct (a ∷ as) = begin
    return (a ∷ as)
      ≈˘⟨ >>=-identityˡ-≈ ⟩
    (return as >>= λ as → return (a ∷ as))
      ≈⟨ >>=-cong-x (id-correct as) ⟩
    (eval idᵉ as >>= λ as → return (a ∷ as))
      ≈˘⟨ >>=-identityˡ-≈ ⟩
    eval idᵉ (a ∷ as) ∎

  -- Uses commutativity to swap the next-step `trace f` recursion with the
  -- current-step `g` action.
  trace-∘ : {sg : State′} {sf : State}
            {g : SFunType B C State′} {f : SFunType A B State}
            (xs : List A)
    → (trace f sf xs >>= trace g sg) ≈ᴹ trace (g ∘ᵉ' f) (sg , sf) xs
  trace-∘ {sg = sg} {sf} {g} {f} [] = >>=-identityˡ-≈
  trace-∘ {sg = sg} {sf} {g} {f} (a ∷ as) = begin
    ((f (sf , a) >>= (λ (sf' , b) → trace f sf' as >>= (λ bs → return (b ∷ bs)))) >>= trace g sg)
      ≈⟨ >>=-assoc-≈ (f (sf , a)) ⟩
    (f (sf , a) >>= (λ (sf' , b) → (trace f sf' as >>= (λ bs → return (b ∷ bs))) >>= trace g sg))
      ≈⟨ >>=-cong-f (λ _ → >>=-assoc-≈ (trace f _ as)) ⟩
    (f (sf , a) >>= (λ (sf' , b) → trace f sf' as >>= (λ bs → return (b ∷ bs) >>= trace g sg)))
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f (λ _ → >>=-identityˡ-≈)) ⟩
    (f (sf , a) >>= (λ (sf' , b) → trace f sf' as >>= (λ bs → trace g sg (b ∷ bs))))
      ≈⟨ >>=-cong-f (λ _ → >>=-comm _) ⟩
    (f (sf , a) >>= (λ (sf' , b) → g (sg , b) >>= (λ (sg' , c) →
      trace f sf' as >>= (λ bs → trace g sg' bs >>= (λ cs → return (c ∷ cs))))))
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f (λ _ → ≈ᴹ.sym (>>=-assoc-≈ (trace f _ as)))) ⟩
    (f (sf , a) >>= (λ (sf' , b) → g (sg , b) >>= (λ (sg' , c) →
      (trace f sf' as >>= (λ bs → trace g sg' bs)) >>= (λ cs → return (c ∷ cs)))))
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f (λ _ → >>=-cong-x (trace-∘ as))) ⟩
    (f (sf , a) >>= (λ (sf' , b) → g (sg , b) >>= (λ (sg' , c) →
      trace (g ∘ᵉ' f) (sg' , sf') as >>= (λ cs → return (c ∷ cs)))))
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f (λ _ → ≈ᴹ.sym >>=-identityˡ-≈)) ⟩
    (f (sf , a) >>= (λ (sf' , b) → g (sg , b) >>= (λ (sg' , c) →
      return ((sg' , sf') , c) >>= (λ (s , c) → trace (g ∘ᵉ' f) s as >>= (λ cs → return (c ∷ cs))))))
      ≈⟨ >>=-cong-f (λ _ → ≈ᴹ.sym (>>=-assoc-≈ (g (sg , _)))) ⟩
    (f (sf , a) >>= (λ (sf' , b) →
      (g (sg , b) >>= (λ (sg' , c) → return ((sg' , sf') , c)))
      >>= (λ (s , c) → trace (g ∘ᵉ' f) s as >>= (λ cs → return (c ∷ cs)))))
      ≈˘⟨ >>=-assoc-≈ (f (sf , a)) ⟩
    ((f (sf , a) >>= (λ (sf' , b) →
      g (sg , b) >>= (λ (sg' , c) → return ((sg' , sf') , c))))
      >>= (λ (s , c) → trace (g ∘ᵉ' f) s as >>= (λ cs → return (c ∷ cs)))) ∎

  assoc-∘ᵉ : {f : SFunᵉ A B} {g : SFunᵉ B C} {h : SFunᵉ C D} → ((h ∘ᵉ g) ∘ᵉ f) ≈ᵉ (h ∘ᵉ (g ∘ᵉ f))
  assoc-∘ᵉ {f = f} {g} {h} xs = begin
    eval ((h ∘ᵉ g) ∘ᵉ f) xs
      ≈˘⟨ trace-∘ xs ⟩
    (eval f xs >>= eval (h ∘ᵉ g))
      ≈⟨ >>=-cong-f (λ ys → ≈ᴹ.sym (trace-∘ ys)) ⟩
    (eval f xs >>= λ ys → eval g ys >>= eval h)
      ≈˘⟨ >>=-assoc-≈ (eval f xs) ⟩
    ((eval f xs >>= eval g) >>= eval h)
      ≈⟨ >>=-cong-x (trace-∘ xs) ⟩
    (eval (g ∘ᵉ f) xs >>= eval h)
      ≈⟨ trace-∘ xs ⟩
    eval (h ∘ᵉ (g ∘ᵉ f)) xs ∎

  identityˡ-∘ᵉ : {f : SFunᵉ A B} → (idᵉ ∘ᵉ f) ≈ᵉ f
  identityˡ-∘ᵉ {f = f} xs = begin
    eval (idᵉ ∘ᵉ f) xs
      ≈˘⟨ trace-∘ xs ⟩
    (eval f xs >>= eval idᵉ)
      ≈⟨ >>=-cong-f (λ ys → ≈ᴹ.sym (id-correct ys)) ⟩
    (eval f xs >>= return)
      ≈⟨ >>=-identityʳ-≈ (eval f xs) ⟩
    eval f xs ∎

  identityʳ-∘ᵉ : {f : SFunᵉ A B} → (f ∘ᵉ idᵉ) ≈ᵉ f
  identityʳ-∘ᵉ {f = f} xs = begin
    eval (f ∘ᵉ idᵉ) xs
      ≈˘⟨ trace-∘ xs ⟩
    (eval idᵉ xs >>= eval f)
      ≈⟨ >>=-cong-x (≈ᴹ.sym (id-correct xs)) ⟩
    (return xs >>= eval f)
      ≈⟨ >>=-identityˡ-≈ ⟩
    eval f xs ∎

  ∘ᵉ-resp-≈ᵉ : {f h : SFunᵉ B C} {g i : SFunᵉ A B} → f ≈ᵉ h → g ≈ᵉ i → (f ∘ᵉ g) ≈ᵉ (h ∘ᵉ i)
  ∘ᵉ-resp-≈ᵉ {f = f} {h} {g} {i} f≈h g≈i xs = begin
    eval (f ∘ᵉ g) xs
      ≈˘⟨ trace-∘ xs ⟩
    (eval g xs >>= eval f)
      ≈⟨ >>=-cong (g≈i xs) (λ ys → f≈h ys) ⟩
    (eval i xs >>= eval h)
      ≈⟨ trace-∘ xs ⟩
    eval (h ∘ᵉ i) xs ∎

  SFunᵉ-Category : Category _ _ _
  SFunᵉ-Category = categoryHelper record
    { Obj       = Type
    ; _⇒_       = SFunᵉ
    ; _≈_       = _≈ᵉ_
    ; id        = idᵉ
    ; _∘_       = _∘ᵉ_
    ; assoc     = assoc-∘ᵉ
    ; identityˡ = identityˡ-∘ᵉ
    ; identityʳ = identityʳ-∘ᵉ
    ; equiv     = ≈ᵉ-isEquivalence
    ; ∘-resp-≈  = ∘ᵉ-resp-≈ᵉ
    }

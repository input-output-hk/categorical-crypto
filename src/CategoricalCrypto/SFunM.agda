{-# OPTIONS --safe #-}

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad.Ext.Setoid

open import Categories.Category.Core
open import Categories.Category.Helper

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as R-Setoid

module CategoricalCrypto.SFunM {M : Type↑}
  ⦃ Monad-M : Monad M     ⦄
  ⦃ MS      : MonadSetoid M ⦄ where

SFunType : Type → Type → Type → Type
SFunType A B S = S × A → M (S × B)

record SFunᵉ (A B : Type) : Type₁ where
  field
    State : Type
    init  : State
    fun   : SFunType A B State

private variable A B C D State : Type

idᵉ : SFunᵉ A A
idᵉ = record
  { State = ⊤
  ; fun = λ (_ , a) → return (_ , a)
  }

_∘ᵉ'_ : ∀ {A B C State₁ State₂}
  → SFunType B C State₂
  → SFunType A B State₁
  → SFunType A C (State₂ × State₁)
_∘ᵉ'_ g f ((sg , sf) , a) = do
  (sf , b) ← f (sf , a)
  (sg , c) ← g (sg , b)
  return ((sg , sf) , c)

_∘ᵉ_ : ∀ {A B C}
  → SFunᵉ B C
  → SFunᵉ A B
  → SFunᵉ A C
_∘ᵉ_ g f = let module g = SFunᵉ g; module f = SFunᵉ f in record
  { State = g.State × f.State
  ; init  = g.init , f.init
  ; fun   = g.fun ∘ᵉ' f.fun
  }

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

≈ᵉ-isEquivalence : ∀ {A B} → IsEquivalence (_≈ᵉ_ {A} {B})
≈ᵉ-isEquivalence = record
  { refl  = λ _ → ≈ᴹ.refl
  ; sym   = λ f≈g xs → ≈ᴹ.sym (f≈g xs)
  ; trans = λ f≈g g≈h xs → ≈ᴹ.trans (f≈g xs) (g≈h xs)
  }

module _ ⦃ M-Laws : MonadLawsSetoid M       ⦄
         ⦃ M-Comm : CommutativeMonadSetoid M ⦄ where

  id-correct : ∀ {A} (xs : List A) → return xs ≈ᴹ eval (idᵉ {A}) xs
  id-correct []       = ≈ᴹ.refl
  id-correct (a ∷ as) = begin
    return (a ∷ as)
      ≈⟨ ≈ᴹ.sym >>=-identityˡ-≈ ⟩
    (return as >>= λ as → return (a ∷ as))
      ≈⟨ >>=-cong-x (id-correct as) ⟩
    (eval idᵉ as >>= λ as → return (a ∷ as))
      ≈⟨ ≈ᴹ.sym >>=-identityˡ-≈ ⟩
    eval idᵉ (a ∷ as) ∎
    where open R-Setoid ≈ᴹ-setoid

  -- Composition of traces unfolds the per-step interleaving into a
  -- run-then-run sequencing. Uses commutativity to swap the next-step
  -- `trace f` recursion with the current-step `g` action.
  trace-∘ : ∀ {StateG StateF sg sf}
            {g : SFunType B C StateG} {f : SFunType A B StateF}
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
      ≈⟨ >>=-cong-f (λ _ → >>=-comm-y-≈ _) ⟩
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
      ≈⟨ ≈ᴹ.sym (>>=-assoc-≈ (f (sf , a))) ⟩
    ((f (sf , a) >>= (λ (sf' , b) →
      g (sg , b) >>= (λ (sg' , c) → return ((sg' , sf') , c))))
      >>= (λ (s , c) → trace (g ∘ᵉ' f) s as >>= (λ cs → return (c ∷ cs)))) ∎
    where open R-Setoid ≈ᴹ-setoid

  assoc-∘ᵉ : {A B C D : Type} {f : SFunᵉ A B} {g : SFunᵉ B C} {h : SFunᵉ C D}
           → ((h ∘ᵉ g) ∘ᵉ f) ≈ᵉ (h ∘ᵉ (g ∘ᵉ f))
  assoc-∘ᵉ {f = f} {g} {h} xs = begin
    eval ((h ∘ᵉ g) ∘ᵉ f) xs
      ≈⟨ ≈ᴹ.sym (trace-∘ xs) ⟩
    (eval f xs >>= eval (h ∘ᵉ g))
      ≈⟨ >>=-cong-f (λ ys → ≈ᴹ.sym (trace-∘ ys)) ⟩
    (eval f xs >>= λ ys → eval g ys >>= eval h)
      ≈⟨ ≈ᴹ.sym (>>=-assoc-≈ (eval f xs)) ⟩
    ((eval f xs >>= eval g) >>= eval h)
      ≈⟨ >>=-cong-x (trace-∘ xs) ⟩
    (eval (g ∘ᵉ f) xs >>= eval h)
      ≈⟨ trace-∘ xs ⟩
    eval (h ∘ᵉ (g ∘ᵉ f)) xs ∎
    where open R-Setoid ≈ᴹ-setoid

  identityˡ-∘ᵉ : {f : SFunᵉ A B} → (idᵉ ∘ᵉ f) ≈ᵉ f
  identityˡ-∘ᵉ {f = f} xs = begin
    eval (idᵉ ∘ᵉ f) xs
      ≈⟨ ≈ᴹ.sym (trace-∘ xs) ⟩
    (eval f xs >>= eval idᵉ)
      ≈⟨ >>=-cong-f (λ ys → ≈ᴹ.sym (id-correct ys)) ⟩
    (eval f xs >>= return)
      ≈⟨ >>=-identityʳ-≈ (eval f xs) ⟩
    eval f xs ∎
    where open R-Setoid ≈ᴹ-setoid

  identityʳ-∘ᵉ : {f : SFunᵉ A B} → (f ∘ᵉ idᵉ) ≈ᵉ f
  identityʳ-∘ᵉ {f = f} xs = begin
    eval (f ∘ᵉ idᵉ) xs
      ≈⟨ ≈ᴹ.sym (trace-∘ xs) ⟩
    (eval idᵉ xs >>= eval f)
      ≈⟨ >>=-cong-x (≈ᴹ.sym (id-correct xs)) ⟩
    (return xs >>= eval f)
      ≈⟨ >>=-identityˡ-≈ ⟩
    eval f xs ∎
    where open R-Setoid ≈ᴹ-setoid

  ∘ᵉ-resp-≈ᵉ : {A B C : Type} {f h : SFunᵉ B C} {g i : SFunᵉ A B}
             → f ≈ᵉ h → g ≈ᵉ i → (f ∘ᵉ g) ≈ᵉ (h ∘ᵉ i)
  ∘ᵉ-resp-≈ᵉ {f = f} {h} {g} {i} f≈h g≈i xs = begin
    eval (f ∘ᵉ g) xs
      ≈⟨ ≈ᴹ.sym (trace-∘ xs) ⟩
    (eval g xs >>= eval f)
      ≈⟨ >>=-cong (g≈i xs) (λ ys → f≈h ys) ⟩
    (eval i xs >>= eval h)
      ≈⟨ trace-∘ xs ⟩
    eval (h ∘ᵉ i) xs ∎
    where open R-Setoid ≈ᴹ-setoid

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

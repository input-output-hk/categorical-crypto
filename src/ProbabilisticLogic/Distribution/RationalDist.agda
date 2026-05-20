{-# OPTIONS --safe --without-K #-}

-- A `ℚ`-weighted distribution monad
--
-- `Dist-ℚ A` is the type of probability distributions on `A` with
-- ℚ-valued weights summing to 1

open import categorical-crypto.Prelude
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties
  using ( +-*-commutativeRing
        ; +-identityˡ; +-identityʳ; +-assoc
        ; *-identityˡ; *-identityʳ; *-zeroʳ; *-assoc
        ; *-distribˡ-+ )
open import Data.List hiding (map)
import Data.List.NonEmpty as NE
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Construct.On as On
open import Algebra using (CommutativeRing)

import ProbabilisticLogic.Distribution.Linearity as Linearity

module ProbabilisticLogic.Distribution.RationalDist where

private
  module Lin = Linearity (CommutativeRing.commutativeSemiring +-*-commutativeRing)

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C D X Y : Type ℓ

------------------------------------------------------------------------
-- Underlying carrier and total mass.

DistData : Type ℓ → Type ℓ
DistData A = NE.List⁺ (ℚ × A)

mass-L : List (ℚ × A) → ℚ
mass-L []             = 0ℚ
mass-L ((q , _) ∷ xs) = q ℚ.+ mass-L xs

mass : DistData A → ℚ
mass (h NE.∷ t) = proj₁ h ℚ.+ mass-L t

scale-ℚ : ℚ → DistData A → DistData A
scale-ℚ q = NE.map (λ (q′ , a) → (q ℚ.* q′ , a))

bindᴰ-cons : (ℚ × A) → List (ℚ × A) → (A → DistData B) → DistData B
bindᴰ-cons (q , a) []         k = scale-ℚ q (k a)
bindᴰ-cons (q , a) (e ∷ rest) k = scale-ℚ q (k a) NE.⁺++⁺ bindᴰ-cons e rest k

infixl 1 _>>=ᴰ_
_>>=ᴰ_ : DistData A → (A → DistData B) → DistData B
(h NE.∷ t) >>=ᴰ k = bindᴰ-cons h t k

------------------------------------------------------------------------
-- Probability distribution: a `DistData` whose weights sum to 1.

record Dist-ℚ (A : Type ℓ) : Type ℓ where
  constructor mk-Dist
  field
    entries : DistData A
    mass-1  : mass entries ≡ 1ℚ

open Dist-ℚ public

------------------------------------------------------------------------
-- Mass lemmas.  These are linearity / distribution properties used to
-- prove that `_>>=ᴰ_` preserves total mass when the kernel does.

mass-L-++ : (xs ys : List (ℚ × A)) → mass-L (xs ++ ys) ≡ mass-L xs ℚ.+ mass-L ys
mass-L-++ []             ys = sym (+-identityˡ (mass-L ys))
mass-L-++ ((q , _) ∷ xs) ys = trans
  (cong (q ℚ.+_) (mass-L-++ xs ys))
  (sym (+-assoc q (mass-L xs) (mass-L ys)))

mass-⁺++⁺ : (μ ν : DistData A) → mass (μ NE.⁺++⁺ ν) ≡ mass μ ℚ.+ mass ν
mass-⁺++⁺ (h NE.∷ t) (h′ NE.∷ t′) = trans
  (cong (proj₁ h ℚ.+_) (mass-L-++ t (h′ ∷ t′)))
  (sym (+-assoc (proj₁ h) (mass-L t) (proj₁ h′ ℚ.+ mass-L t′)))

mass-scale-L : {A : Type ℓ} (q : ℚ) (xs : List (ℚ × A))
             → mass-L (map (λ (q′ , a) → (q ℚ.* q′ , a)) xs) ≡ q ℚ.* mass-L xs
mass-scale-L q []              = sym (*-zeroʳ q)
mass-scale-L q ((q′ , _) ∷ xs) = trans
  (cong ((q ℚ.* q′) ℚ.+_) (mass-scale-L q xs))
  (sym (*-distribˡ-+ q q′ (mass-L xs)))

mass-scale-ℚ : (q : ℚ) (μ : DistData A) → mass (scale-ℚ q μ) ≡ q ℚ.* mass μ
mass-scale-ℚ q (h NE.∷ t) = trans
  (cong ((q ℚ.* proj₁ h) ℚ.+_) (mass-scale-L q t))
  (sym (*-distribˡ-+ q (proj₁ h) (mass-L t)))

private
  Lin-mass-L≡mass-L : (xs : List (ℚ × A)) → Lin.mass-L xs ≡ mass-L xs
  Lin-mass-L≡mass-L []             = refl
  Lin-mass-L≡mass-L ((q , _) ∷ xs) =
    trans (cong (ℚ._+ Lin.mass-L xs) (*-identityʳ q))
          (cong (q ℚ.+_) (Lin-mass-L≡mass-L xs))

-- Recursion principle for `bindᴰ-cons`: any "linear" measure `H` on
-- `DistData` (one that distributes over `⁺++⁺` and pulls scalars out
-- of `scale-ℚ`) evaluates on a `bindᴰ-cons` to the obvious weighted
-- sum over kernel outputs.
-- TODO: wouldn't this be more compact
bindᴰ-cons-eval : (H : DistData B → ℚ)
  → (∀ μ ν → H (μ NE.⁺++⁺ ν) ≡ H μ ℚ.+ H ν) → (∀ q μ → H (scale-ℚ q μ) ≡ q ℚ.* H μ)
  → (q : ℚ) (a : A) (rest : List (ℚ × A)) (k : A → DistData B)
  → H (bindᴰ-cons (q , a) rest k) ≡ Lin.lookup-L ((q , a) ∷ rest) (H ∘ k)
bindᴰ-cons-eval H H-++ H-scale q a [] k = trans (H-scale q (k a)) (sym (+-identityʳ _))
bindᴰ-cons-eval H H-++ H-scale q a ((q′ , a′) ∷ rest) k = begin
  H (scale-ℚ q (k a) NE.⁺++⁺ bindᴰ-cons (q′ , a′) rest k)
    ≡⟨ H-++ (scale-ℚ q (k a)) (bindᴰ-cons (q′ , a′) rest k) ⟩
  H (scale-ℚ q (k a)) ℚ.+ H (bindᴰ-cons (q′ , a′) rest k)
    ≡⟨ cong₂ ℚ._+_ (H-scale q (k a)) (bindᴰ-cons-eval H H-++ H-scale q′ a′ rest k) ⟩
  q ℚ.* H (k a) ℚ.+ (q′ ℚ.* H (k a′) ℚ.+ Lin.lookup-L rest (λ a″ → H (k a″))) ∎
  where open ≡-Reasoning

mass-bindᴰ : (μ : DistData A) (k : A → DistData B)
           → (∀ a → mass (k a) ≡ 1ℚ) → mass (μ >>=ᴰ k) ≡ mass μ
mass-bindᴰ ((q , a) NE.∷ t) k mass-k = begin
  mass (bindᴰ-cons (q , a) t k)
    ≡⟨ bindᴰ-cons-eval mass mass-⁺++⁺ mass-scale-ℚ q a t k ⟩
  q ℚ.* mass (k a) ℚ.+ Lin.lookup-L t (λ a′ → mass (k a′))
    ≡⟨ cong₂ ℚ._+_ (trans (cong (q ℚ.*_) (mass-k a)) (*-identityʳ q)) (Lin.lookup-L-cong-P t mass-k) ⟩
  q ℚ.+ Lin.mass-L t
    ≡⟨ cong (q ℚ.+_) (Lin-mass-L≡mass-L t) ⟩
  q ℚ.+ mass-L t ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The `Dist-ℚ` monad: `return-ℚ`, `_>>=ᴹ_`, plus the comonoid
-- "primitives" `del-ℚ` and `copy-ℚ`.

return-ℚ : A → Dist-ℚ A
return-ℚ a = mk-Dist ((1ℚ , a) NE.∷ []) (+-identityʳ 1ℚ)

infixl 1 _>>=ᴹ_
_>>=ᴹ_ : Dist-ℚ A → (A → Dist-ℚ B) → Dist-ℚ B
μ >>=ᴹ k = mk-Dist (entries μ >>=ᴰ entries ∘ k)
                   (trans (mass-bindᴰ (entries μ) (entries ∘ k) (mass-1 ∘ k)) (mass-1 μ))

del-ℚ : A → Dist-ℚ ⊤
del-ℚ _ = return-ℚ tt

copy-ℚ : A → Dist-ℚ (A × A)
copy-ℚ a = return-ℚ (a , a)

------------------------------------------------------------------------
-- Extensional equality for `Dist-ℚ`

lookupᴰℚ : DistData A → (A → ℚ) → ℚ
lookupᴰℚ μ = Lin.lookup-L (NE.toList μ)

infix 4 _≈ᴰℚ_ _≈Mℚ_

_≈ᴰℚ_ : ∀ {A : Type ℓ} → DistData A → DistData A → Type ℓ
μ ≈ᴰℚ ν = ∀ P → lookupᴰℚ μ P ≡ lookupᴰℚ ν P

_≈Mℚ_ : ∀ {A : Type ℓ} → Dist-ℚ A → Dist-ℚ A → Type ℓ
μ ≈Mℚ ν = entries μ ≈ᴰℚ entries ν

------------------------------------------------------------------------
-- Linearity / Fubini lemmas for `lookupᴰℚ`.

lookupᴰℚ-cong-P : (μ : DistData A) {P P′ : A → ℚ} → (∀ a → P a ≡ P′ a)
                → lookupᴰℚ μ P ≡ lookupᴰℚ μ P′
lookupᴰℚ-cong-P μ P≡P′ = Lin.lookup-L-cong-P (NE.toList μ) P≡P′

lookupᴰℚ-⁺++⁺ : (μ ν : DistData A) (P : A → ℚ)
              → lookupᴰℚ (μ NE.⁺++⁺ ν) P ≡ lookupᴰℚ μ P ℚ.+ lookupᴰℚ ν P
lookupᴰℚ-⁺++⁺ (h NE.∷ t) (h′ NE.∷ t′) P = trans
  (cong (proj₁ h ℚ.* P (proj₂ h) ℚ.+_) (Lin.lookup-L-++ t (h′ ∷ t′) P))
  (sym (+-assoc (proj₁ h ℚ.* P (proj₂ h))
                    (Lin.lookup-L t P)
                    (proj₁ h′ ℚ.* P (proj₂ h′) ℚ.+ Lin.lookup-L t′ P)))

lookupᴰℚ-scale : (q : ℚ) (μ : DistData A) (P : A → ℚ)
               → lookupᴰℚ (scale-ℚ q μ) P ≡ q ℚ.* lookupᴰℚ μ P
lookupᴰℚ-scale q (h NE.∷ t) P = begin
  (q ℚ.* proj₁ h) ℚ.* P (proj₂ h) ℚ.+ Lin.lookup-L (map _ t) P
    ≡⟨ cong ((q ℚ.* proj₁ h) ℚ.* P (proj₂ h) ℚ.+_) (Lin.lookup-L-scaleL q t P) ⟩
  (q ℚ.* proj₁ h) ℚ.* P (proj₂ h) ℚ.+ q ℚ.* Lin.lookup-L t P
    ≡⟨ cong (ℚ._+ q ℚ.* Lin.lookup-L t P) (*-assoc q (proj₁ h) (P (proj₂ h))) ⟩
  q ℚ.* (proj₁ h ℚ.* P (proj₂ h)) ℚ.+ q ℚ.* Lin.lookup-L t P
    ≡⟨ sym (*-distribˡ-+ q (proj₁ h ℚ.* P (proj₂ h)) (Lin.lookup-L t P)) ⟩
  q ℚ.* (proj₁ h ℚ.* P (proj₂ h) ℚ.+ Lin.lookup-L t P) ∎
  where open ≡-Reasoning

lookupᴰℚ-bind : (μ : DistData A) (k : A → DistData B) (P : B → ℚ)
              → lookupᴰℚ (μ >>=ᴰ k) P ≡ lookupᴰℚ μ (λ a → lookupᴰℚ (k a) P)
lookupᴰℚ-bind ((q , a) NE.∷ t) k P =
  bindᴰ-cons-eval (λ μ → lookupᴰℚ μ P)
                  (λ μ ν → lookupᴰℚ-⁺++⁺ μ ν P)
                  (λ q′ μ → lookupᴰℚ-scale q′ μ P)
                  q a t k

------------------------------------------------------------------------
-- Linearity in the test function. `lookupᴰℚ μ` is a linear functional:
-- additive, scalar-multiplicative, and zero on the zero test.

ret-eval : (x : ℚ) → 1ℚ ℚ.* x ℚ.+ 0ℚ ≡ x
ret-eval x = trans (+-identityʳ (1ℚ ℚ.* x)) (*-identityˡ x)

lookupᴰℚ-return : (a : A) (P : A → ℚ) → lookupᴰℚ (entries (return-ℚ a)) P ≡ P a
lookupᴰℚ-return a P = ret-eval (P a)

lookupᴰℚ-zero : (μ : DistData A) → lookupᴰℚ μ (λ _ → 0ℚ) ≡ 0ℚ
lookupᴰℚ-zero (h NE.∷ t) = Lin.lookup-L-zero (h ∷ t)

lookupᴰℚ-+ : (μ : DistData A) (P Q : A → ℚ)
           → lookupᴰℚ μ (λ a → P a ℚ.+ Q a) ≡ lookupᴰℚ μ P ℚ.+ lookupᴰℚ μ Q
lookupᴰℚ-+ (h NE.∷ t) P Q = Lin.lookup-L-+ (h ∷ t) P Q

lookupᴰℚ-*ₗ : (q : ℚ) (μ : DistData A) (P : A → ℚ)
            → lookupᴰℚ μ (λ a → q ℚ.* P a) ≡ q ℚ.* lookupᴰℚ μ P
lookupᴰℚ-*ₗ q (h NE.∷ t) P = Lin.lookup-L-*ₗ q (h ∷ t) P

-- For a constant test function, `lookupᴰℚ μ` is `mass μ * c`.

mass-as-const : (μ : DistData A) (c : ℚ) → lookupᴰℚ μ (λ _ → c) ≡ mass μ ℚ.* c
mass-as-const (h NE.∷ t) c =
  trans (Lin.lookup-L-const (h ∷ t) c) (cong (ℚ._* c) (Lin-mass-L≡mass-L (h ∷ t)))

lookupᴰℚ-swap : (μ : DistData A) (ν : DistData B) (P : A → B → ℚ)
              → lookupᴰℚ μ (λ a → lookupᴰℚ ν (P a))
              ≡ lookupᴰℚ ν (λ b → lookupᴰℚ μ (λ a → P a b))
lookupᴰℚ-swap μ ν = Lin.lookup-L-swap (NE.toList μ) (NE.toList ν)

------------------------------------------------------------------------
-- Equivalence and congruence.

≈ᴰℚ-isEquivalence : IsEquivalence (_≈ᴰℚ_ {A = A})
≈ᴰℚ-isEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ μ≈ν P → sym (μ≈ν P)
  ; trans = λ μ≈ν ν≈ρ P → trans (μ≈ν P) (ν≈ρ P)
  }

≈Mℚ-isEquivalence : IsEquivalence (_≈Mℚ_ {A = A})
≈Mℚ-isEquivalence = On.isEquivalence entries ≈ᴰℚ-isEquivalence

>>=ᴰ-cong : {μ ν : DistData A} {f g : A → DistData B}
          → μ ≈ᴰℚ ν → (∀ a → f a ≈ᴰℚ g a) → (μ >>=ᴰ f) ≈ᴰℚ (ν >>=ᴰ g)
>>=ᴰ-cong {μ = μ} {ν} {f} {g} μ≈ν f≈g P = begin
  lookupᴰℚ (μ >>=ᴰ f) P
    ≡⟨ lookupᴰℚ-bind μ f P ⟩
  lookupᴰℚ μ (λ a → lookupᴰℚ (f a) P)
    ≡⟨ lookupᴰℚ-cong-P μ (λ a → f≈g a P) ⟩
  lookupᴰℚ μ (λ a → lookupᴰℚ (g a) P)
    ≡⟨ μ≈ν _ ⟩
  lookupᴰℚ ν (λ a → lookupᴰℚ (g a) P)
    ≡⟨ sym (lookupᴰℚ-bind ν g P) ⟩
  lookupᴰℚ (ν >>=ᴰ g) P ∎
  where open ≡-Reasoning

>>=ᴹ-cong : {μ ν : Dist-ℚ A} {f g : A → Dist-ℚ B}
          → μ ≈Mℚ ν → (∀ a → f a ≈Mℚ g a)
          → (μ >>=ᴹ f) ≈Mℚ (ν >>=ᴹ g)
>>=ᴹ-cong {μ = μ} {ν} μ≈ν f≈g = >>=ᴰ-cong {μ = entries μ} {entries ν} μ≈ν f≈g

------------------------------------------------------------------------
-- Monad laws (in the `_≈Mℚ_` setoid)

>>=ᴹ-identityˡ : (a : A) (k : A → Dist-ℚ B) → (return-ℚ a >>=ᴹ k) ≈Mℚ k a
>>=ᴹ-identityˡ a k P = trans
  (lookupᴰℚ-scale 1ℚ (entries (k a)) P)
  (*-identityˡ (lookupᴰℚ (entries (k a)) P))

>>=ᴹ-identityʳ : (μ : Dist-ℚ A) → (μ >>=ᴹ return-ℚ) ≈Mℚ μ
>>=ᴹ-identityʳ μ P = trans
  (lookupᴰℚ-bind (entries μ) (λ a → entries (return-ℚ a)) P)
  (lookupᴰℚ-cong-P (entries μ) λ a → ret-eval (P a))

>>=ᴹ-assoc : (μ : Dist-ℚ A) (f : A → Dist-ℚ B) (g : B → Dist-ℚ C)
           → ((μ >>=ᴹ f) >>=ᴹ g) ≈Mℚ (μ >>=ᴹ λ a → f a >>=ᴹ g)
>>=ᴹ-assoc μ f g P = begin
  lookupᴰℚ (entries (μ >>=ᴹ f) >>=ᴰ (entries ∘ g)) P
    ≡⟨ lookupᴰℚ-bind (entries μ >>=ᴰ (entries ∘ f)) (entries ∘ g) P ⟩
  lookupᴰℚ (entries μ >>=ᴰ (entries ∘ f)) (λ b → lookupᴰℚ (entries (g b)) P)
    ≡⟨ lookupᴰℚ-bind (entries μ) (entries ∘ f) (λ b → lookupᴰℚ (entries (g b)) P) ⟩
  lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries (f a)) (λ b → lookupᴰℚ (entries (g b)) P))
    ≡⟨ lookupᴰℚ-cong-P (entries μ) (λ a → sym (lookupᴰℚ-bind (entries (f a)) (entries ∘ g) P)) ⟩
  lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries (f a) >>=ᴰ (entries ∘ g)) P)
    ≡⟨ sym (lookupᴰℚ-bind (entries μ) (λ a → entries (f a >>=ᴹ g)) P) ⟩
  lookupᴰℚ (entries μ >>=ᴰ (λ a → entries (f a >>=ᴹ g))) P ∎
  where open ≡-Reasoning

>>=ᴹ-comm : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (k : A → B → Dist-ℚ C)
          → (μ >>=ᴹ λ x → ν >>=ᴹ λ y → k x y)
          ≈Mℚ (ν >>=ᴹ λ y → μ >>=ᴹ λ x → k x y)
>>=ᴹ-comm μ ν k P = begin
  lookupᴰℚ (entries (μ >>=ᴹ (λ x → ν >>=ᴹ (λ y → k x y)))) P
    ≡⟨ lookupᴰℚ-bind (entries μ) _ P ⟩
  lookupᴰℚ (entries μ) (λ x → lookupᴰℚ (entries (ν >>=ᴹ (λ y → k x y))) P)
    ≡⟨ lookupᴰℚ-cong-P (entries μ) (λ x → lookupᴰℚ-bind (entries ν) _ P) ⟩
  lookupᴰℚ (entries μ) (λ x → lookupᴰℚ (entries ν) (λ y → lookupᴰℚ (entries (k x y)) P))
    ≡⟨ lookupᴰℚ-swap (entries μ) (entries ν) (λ x y → lookupᴰℚ (entries (k x y)) P) ⟩
  lookupᴰℚ (entries ν) (λ y → lookupᴰℚ (entries μ) (λ x → lookupᴰℚ (entries (k x y)) P))
    ≡⟨ sym (lookupᴰℚ-cong-P (entries ν) (λ y → lookupᴰℚ-bind (entries μ) _ P)) ⟩
  lookupᴰℚ (entries ν) (λ y → lookupᴰℚ (entries (μ >>=ᴹ (λ x → k x y))) P)
    ≡⟨ sym (lookupᴰℚ-bind (entries ν) _ P) ⟩
  lookupᴰℚ (entries (ν >>=ᴹ (λ y → μ >>=ᴹ (λ x → k x y)))) P ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Dmap

Dmap : (A → B) → Dist-ℚ A → Dist-ℚ B
Dmap f μ = μ >>=ᴹ return-ℚ ∘ f

lookupᴰℚ-Dmap : (f : A → B) (μ : Dist-ℚ A) (Q : B → ℚ)
              → lookupᴰℚ (entries (Dmap f μ)) Q ≡ lookupᴰℚ (entries μ) (Q ∘′ f)
lookupᴰℚ-Dmap f μ Q = trans
  (lookupᴰℚ-bind (entries μ) (λ a → entries (return-ℚ (f a))) Q)
  (lookupᴰℚ-cong-P (entries μ) λ a → ret-eval (Q (f a)))

-- Functor laws for `Dmap` (in the `_≈Mℚ_` setoid).

Dmap-id : (μ : Dist-ℚ A) → Dmap (λ x → x) μ ≈Mℚ μ
Dmap-id = lookupᴰℚ-Dmap id

Dmap-∘ : (f : A → B) (g : B → C) (μ : Dist-ℚ A) → Dmap (λ a → g (f a)) μ ≈Mℚ Dmap g (Dmap f μ)
Dmap-∘ f g μ P = trans (lookupᴰℚ-Dmap (g ∘ f) μ P)
  (sym (trans (lookupᴰℚ-Dmap g (Dmap f μ) P) (lookupᴰℚ-Dmap f μ (P ∘′ g))))

Dmap-cong-fn : {f g : A → B} → (∀ a → f a ≡ g a)
             → ∀ (μ : Dist-ℚ A) → Dmap f μ ≈Mℚ Dmap g μ
Dmap-cong-fn {f = f} {g} f≗g μ P = trans (lookupᴰℚ-Dmap f μ P)
  (trans (lookupᴰℚ-cong-P (entries μ) (cong P ∘ f≗g)) (sym (lookupᴰℚ-Dmap g μ P)))

Dmap->>= : (f : A → B) (μ : Dist-ℚ A) (k : B → Dist-ℚ C)
         → (Dmap f μ >>=ᴹ k) ≈Mℚ (μ >>=ᴹ (k ∘ f))
Dmap->>= f μ k P = trans
  (lookupᴰℚ-bind (entries μ >>=ᴰ (entries ∘ return-ℚ ∘ f)) (entries ∘ k) P)
  (trans
    (lookupᴰℚ-bind (entries μ) (entries ∘ return-ℚ ∘ f) (λ b → lookupᴰℚ (entries (k b)) P))
    (trans
      (lookupᴰℚ-cong-P (entries μ) λ a →
        ret-eval (lookupᴰℚ (entries (k (f a))) P))
      (sym (lookupᴰℚ-bind (entries μ) (λ a → entries (k (f a))) P))))

------------------------------------------------------------------------
-- Class instances: `Dist-ℚ`
--
-- Note we don't provide `MonadLaws Dist-ℚ` because the laws only hold
-- up to `_≈Mℚ_`, not `_≡_`; the setoid analogue lives in
-- `ProbabilisticLogic.Distribution.RationalDist.Setoid`.

instance
  Functor-Dist-ℚ : Functor Dist-ℚ
  Functor-Dist-ℚ ._<$>_ = Dmap

  Applicative-Dist-ℚ : Applicative Dist-ℚ
  Applicative-Dist-ℚ .pure = return-ℚ
  Applicative-Dist-ℚ ._<*>_ fs xs = fs >>=ᴹ λ f → xs >>=ᴹ return-ℚ ∘ f

  Monad-Dist-ℚ : Monad Dist-ℚ
  Monad-Dist-ℚ .return = return-ℚ
  Monad-Dist-ℚ ._>>=_  = _>>=ᴹ_

------------------------------------------------------------------------
-- Markov category structure: Kleisli morphisms, comonoid laws,
-- discard naturality.
--
-- An abstract `MarkovCategory` instance assembled from these is in
-- `ProbabilisticLogic.Distribution.RationalDist.MarkovInstance`.

infix 4 _∼_

_∼_ : (f g : X → Dist-ℚ Y) → Type _
f ∼ g = ∀ x → f x ≈Mℚ g x

idᴷ : A → Dist-ℚ A
idᴷ = return-ℚ

infixr 9 _∘ᴷ_
_∘ᴷ_ : (B → Dist-ℚ C) → (A → Dist-ℚ B) → (A → Dist-ℚ C)
(g ∘ᴷ f) x = f x >>=ᴹ g

infixr 5 _⊗ᴷ_
_⊗ᴷ_ : (A → Dist-ℚ B) → (C → Dist-ℚ D) → (A × C → Dist-ℚ (B × D))
(f ⊗ᴷ g) (a , c) = f a >>=ᴹ λ b → g c >>=ᴹ λ d → return-ℚ (b , d)

------------------------------------------------------------------------
-- Comonoid laws

private
  ⊗ᴷ-on-copy : (a : A) (b₀ : B) (d₀ : D) (f : A → Dist-ℚ B) (g : A → Dist-ℚ D)
             → f a ≡ return-ℚ b₀ → g a ≡ return-ℚ d₀
             → ((f ⊗ᴷ g) ∘ᴷ copy-ℚ) a ≈Mℚ return-ℚ (b₀ , d₀)
  ⊗ᴷ-on-copy a b₀ d₀ f g fa≡ ga≡ P = begin
    lookupᴰℚ (entries (return-ℚ (a , a) >>=ᴹ (f ⊗ᴷ g))) P
      ≡⟨ >>=ᴹ-identityˡ (a , a) (f ⊗ᴷ g) P ⟩
    lookupᴰℚ (entries (f a >>=ᴹ (λ b → g a >>=ᴹ return-ℚ ∘ (b ,_)))) P
      ≡⟨ cong (λ x → lookupᴰℚ (entries (x >>=ᴹ (λ b → g a >>=ᴹ return-ℚ ∘ (b ,_)))) P) fa≡ ⟩
    lookupᴰℚ (entries (return-ℚ b₀ >>=ᴹ (λ b → g a >>=ᴹ return-ℚ ∘ (b ,_)))) P
      ≡⟨ >>=ᴹ-identityˡ b₀ (λ b → g a >>=ᴹ return-ℚ ∘ (b ,_)) P ⟩
    lookupᴰℚ (entries (g a >>=ᴹ return-ℚ ∘ (b₀ ,_))) P
      ≡⟨ cong (λ x → lookupᴰℚ (entries (x >>=ᴹ return-ℚ ∘ (b₀ ,_))) P) ga≡ ⟩
    lookupᴰℚ (entries (return-ℚ d₀ >>=ᴹ return-ℚ ∘ (b₀ ,_))) P
      ≡⟨ >>=ᴹ-identityˡ d₀ (return-ℚ ∘ (b₀ ,_)) P ⟩
    lookupᴰℚ (entries (return-ℚ (b₀ , d₀))) P ∎
    where open ≡-Reasoning

counit-left : ((del-ℚ ⊗ᴷ idᴷ {A = A}) ∘ᴷ copy-ℚ) ∼ (λ a → return-ℚ (tt , a))
counit-left a = ⊗ᴷ-on-copy a tt a del-ℚ idᴷ refl refl

counit-right : ((idᴷ {A = A} ⊗ᴷ del-ℚ) ∘ᴷ copy-ℚ) ∼ (λ a → return-ℚ (a , tt))
counit-right a = ⊗ᴷ-on-copy a a tt idᴷ del-ℚ refl refl

coassoc-l : ((copy-ℚ ⊗ᴷ idᴷ {A = A}) ∘ᴷ copy-ℚ) ∼ (λ a → return-ℚ ((a , a) , a))
coassoc-l a = ⊗ᴷ-on-copy a (a , a) a copy-ℚ idᴷ refl refl

coassoc-r : ((idᴷ {A = A} ⊗ᴷ copy-ℚ) ∘ᴷ copy-ℚ) ∼ (λ a → return-ℚ (a , (a , a)))
coassoc-r a = ⊗ᴷ-on-copy a a (a , a) idᴷ copy-ℚ refl refl

swap-pure : A × A → Dist-ℚ (A × A)
swap-pure (x , y) = return-ℚ (y , x)

cocomm : (swap-pure {A = A} ∘ᴷ copy-ℚ) ∼ copy-ℚ
cocomm a P = >>=ᴹ-identityˡ (a , a) swap-pure P

mid-swap : (A × A) × (B × B) → Dist-ℚ ((A × B) × (A × B))
mid-swap ((a₁ , a₂) , (b₁ , b₂)) = return-ℚ ((a₁ , b₁) , (a₂ , b₂))

copy-monoidal : (mid-swap ∘ᴷ (copy-ℚ {A = A} ⊗ᴷ copy-ℚ {A = B})) ∼ copy-ℚ
copy-monoidal (a , b) P = begin
  lookupᴰℚ (entries ((copy-ℚ ⊗ᴷ copy-ℚ) (a , b) >>=ᴹ mid-swap)) P
    ≡⟨ >>=ᴹ-assoc (copy-ℚ a) (λ x → copy-ℚ b >>=ᴹ return-ℚ ∘ (x ,_)) mid-swap P ⟩
  lookupᴰℚ (entries (copy-ℚ a >>=ᴹ λ x → copy-ℚ b >>=ᴹ return-ℚ ∘ (x ,_) >>=ᴹ mid-swap)) P
    ≡⟨ >>=ᴹ-identityˡ (a , a) (λ x → copy-ℚ b >>=ᴹ return-ℚ ∘ (x ,_) >>=ᴹ mid-swap) P ⟩
  lookupᴰℚ (entries ((copy-ℚ b >>=ᴹ return-ℚ ∘ ((a , a) ,_)) >>=ᴹ mid-swap)) P
    ≡⟨ >>=ᴹ-assoc (copy-ℚ b) (return-ℚ ∘ ((a , a) ,_)) mid-swap P ⟩
  lookupᴰℚ (entries (copy-ℚ b >>=ᴹ (λ y → return-ℚ ((a , a) , y) >>=ᴹ mid-swap))) P
    ≡⟨ >>=ᴹ-identityˡ (b , b) (λ y → return-ℚ ((a , a) , y) >>=ᴹ mid-swap) P ⟩
  lookupᴰℚ (entries (return-ℚ ((a , a) , (b , b)) >>=ᴹ mid-swap)) P
    ≡⟨ >>=ᴹ-identityˡ ((a , a) , (b , b)) mid-swap P ⟩
  lookupᴰℚ (entries (return-ℚ ((a , b) , (a , b)))) P ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Markov axiom

discard-natural : (f : A → Dist-ℚ B) → (del-ℚ ∘ᴷ f) ∼ del-ℚ {A = A}
discard-natural f a P = begin
  lookupᴰℚ (entries (f a >>=ᴹ del-ℚ)) P
    ≡⟨ lookupᴰℚ-bind (entries (f a)) (λ _ → entries (del-ℚ tt)) P ⟩
  lookupᴰℚ (entries (f a)) (λ _ → 1ℚ ℚ.* P tt ℚ.+ 0ℚ)
    ≡⟨ lookupᴰℚ-cong-P (entries (f a)) (λ _ → ret-eval (P tt)) ⟩
  lookupᴰℚ (entries (f a)) (λ _ → P tt)
    ≡⟨ mass-as-const (entries (f a)) (P tt) ⟩
  mass (entries (f a)) ℚ.* P tt
    ≡⟨ cong (ℚ._* P tt) (mass-1 (f a)) ⟩
  1ℚ ℚ.* P tt
    ≡⟨ sym (+-identityʳ (1ℚ ℚ.* P tt)) ⟩
  1ℚ ℚ.* P tt ℚ.+ 0ℚ ∎
  where open ≡-Reasoning

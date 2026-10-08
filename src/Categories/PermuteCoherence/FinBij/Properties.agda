{-# OPTIONS --safe --without-K #-}

module Categories.PermuteCoherence.FinBij.Properties where

open import Categories.PermuteCoherence.FinBij

open import Data.Fin.Base renaming (suc to fsuc)
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open P using (remove)
open import Data.Fin.Properties using (punchOut-cong; suc-injective)
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality

private
  variable
    n m k N M p q r : ℕ

------------------------------------------------------------------------
-- Structural coherence
------------------------------------------------------------------------

cons-fb-functor-id : cons-fb (id-fb {n = n}) ≈-fb id-fb {n = suc n}
cons-fb-functor-id = P.lift₀-id

cons²-fb-id : cons-fb (cons-fb (id-fb {n = n})) ≈-fb id-fb {n = suc (suc n)}
cons²-fb-id 0F             = refl
cons²-fb-id (fsuc 0F)      = refl
cons²-fb-id (fsuc (fsuc i)) = refl

cons-fb-functor-comp : (g : FinBij m k) (f : FinBij n m) →
                      cons-fb (g ∘-fb f) ≈-fb cons-fb g ∘-fb cons-fb f
cons-fb-functor-comp g f i = sym (P.lift₀-comp f g i)

swap-fb-involutive : swap-fb n ∘-fb swap-fb n ≈-fb id-fb
swap-fb-involutive 0F             = refl
swap-fb-involutive (fsuc 0F)      = refl
swap-fb-involutive (fsuc (fsuc i)) = refl

swap-fb-natural : (f : FinBij n m) →
                  swap-fb m ∘-fb cons-fb (cons-fb f)
                  ≈-fb cons-fb (cons-fb f) ∘-fb swap-fb n
swap-fb-natural f 0F              = refl
swap-fb-natural f (fsuc 0F)       = refl
swap-fb-natural f (fsuc (fsuc i)) = refl

yang-baxter :
  swap-fb (suc n) ∘-fb cons-fb (swap-fb n) ∘-fb swap-fb (suc n)
  ≈-fb
  cons-fb (swap-fb n) ∘-fb swap-fb (suc n) ∘-fb cons-fb (swap-fb n)
yang-baxter 0F                          = refl
yang-baxter (fsuc 0F)                   = refl
yang-baxter (fsuc (fsuc 0F))             = refl
yang-baxter (fsuc (fsuc (fsuc i)))       = refl

------------------------------------------------------------------------
-- Pointwise congruence
------------------------------------------------------------------------

∘-fb-cong : {g g′ : FinBij m k} {f f′ : FinBij n m} →
            g ≈-fb g′ → f ≈-fb f′ → (g ∘-fb f) ≈-fb (g′ ∘-fb f′)
∘-fb-cong {g = g} {g′} {f} {f′} g≈ f≈ i
  rewrite f≈ i = g≈ (f′ P.⟨$⟩ʳ i)

-- `_≈-fb_` constrains only the noninjective forward projection, so it
-- cannot infer the intermediate `FinBij` records.  Explicit factors pin them.
∘-fb-congˡ : (g g′ : FinBij m k) (f : FinBij n m) →
             g ≈-fb g′ → (g ∘-fb f) ≈-fb (g′ ∘-fb f)
∘-fb-congˡ _ _ f g≈ i = g≈ (f P.⟨$⟩ʳ i)

∘-fb-congʳ : (g : FinBij m k) (f f′ : FinBij n m) →
             f ≈-fb f′ → (g ∘-fb f) ≈-fb (g ∘-fb f′)
∘-fb-congʳ g _ _ f≈ i = cong (g P.⟨$⟩ʳ_) (f≈ i)

cons-fb-cong : {f f′ : FinBij n m} →
               f ≈-fb f′ → cons-fb f ≈-fb cons-fb f′
cons-fb-cong eq 0F       = refl
cons-fb-cong eq (fsuc i) = cong fsuc (eq i)

-- `remove` is opaque under `_≡_`; pointwise equality uses congruence of
-- `punchOut` in both arguments (stdlib supplies the `j` half).
private
  punchOut-cong-both : {i i′ j j′ : Fin (suc n)} → i ≡ i′ → j ≡ j′
                     → {p : i ≢ j} {p′ : i′ ≢ j′} → punchOut p ≡ punchOut p′
  punchOut-cong-both {i = i} refl ej = punchOut-cong i ej

residual-pw-cong : (b b′ : FinBij (suc n) (suc n)) → b ≈-fb b′
                 → remove 0F b ≈-fb remove 0F b′
residual-pw-cong b b′ eq i = punchOut-cong-both (eq 0F) (eq (fsuc i))

-- `≈-fb` (about `_⟨$⟩ʳ_`) also equates `_⟨$⟩ˡ_`, since the backward map
-- is determined by the forward one.
≈ˡ : {f g : FinBij N M} → f ≈-fb g → ∀ j → f P.⟨$⟩ˡ j ≡ g P.⟨$⟩ˡ j
≈ˡ {f = f} {g} eq j =
  trans (sym (P.inverseˡ g {f P.⟨$⟩ˡ j}))
        (cong (g P.⟨$⟩ˡ_) (trans (sym (eq (f P.⟨$⟩ˡ j))) (P.inverseʳ f {j})))

cons-fb-injective : {f g : FinBij n m}
                  → cons-fb f ≈-fb cons-fb g → f ≈-fb g
cons-fb-injective h j = suc-injective (h (fsuc j))

remove-0-of-id : remove 0F (id-fb {n = suc n} ∘-fb inv-fb id-fb) ≈-fb id-fb
remove-0-of-id {n} =
  cons-fb-injective
    (λ j → trans (P.lift₀-remove (id-fb {n = suc n} ∘-fb inv-fb id-fb) refl j)
                 (sym (cons-fb-functor-id j)))

------------------------------------------------------------------------
-- Endpoint transport
------------------------------------------------------------------------

castFB : p ≡ suc n → q ≡ suc n → FinBij p q → FinBij (suc n) (suc n)
castFB e₁ e₂ b = subst₂ P.Permutation e₁ e₂ b

cast-push : (e₁ : p ≡ suc n) (e₂ : q ≡ suc n)
            (b : FinBij p q) (k : Fin (suc n))
          → castFB e₁ e₂ b P.⟨$⟩ʳ k
            ≡ subst Fin e₂ (b P.⟨$⟩ʳ subst Fin (sym e₁) k)
cast-push refl refl b k = refl

-- Arbitrary endpoint proofs can be peeled directly by `suc-injective`.
cons-cast : (e₁ : suc p ≡ suc (suc n)) (e₂ : suc q ≡ suc (suc n))
            (b : FinBij p q)
          → castFB e₁ e₂ (cons-fb b)
            ≈-fb cons-fb (castFB (ℕₚ.suc-injective e₁) (ℕₚ.suc-injective e₂) b)
cons-cast refl refl b k = refl

comp-cast : (e₁ : p ≡ suc n) (e₂ : q ≡ suc n) (e₃ : r ≡ suc n)
            (g : FinBij q r) (f : FinBij p q)
          → castFB e₁ e₃ (g ∘-fb f)
            ≈-fb (castFB e₂ e₃ g ∘-fb castFB e₁ e₂ f)
comp-cast refl refl refl g f k = refl

cast-id : (e : p ≡ suc n) → castFB e e (id-fb {n = p}) ≈-fb id-fb
cast-id refl _ = refl

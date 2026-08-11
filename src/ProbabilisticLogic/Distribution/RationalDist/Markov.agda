{-# OPTIONS --safe --without-K #-}

-- `Dist-ℚ` as a Monad on `Setoids 0ℓ 0ℓ`, and the resulting Kleisli
-- category. `Kl Dist-ℚ` is a Markov category.

module ProbabilisticLogic.Distribution.RationalDist.Markov where

open import Categories.Category
import Categories.Category.Cartesian.SymmetricMonoidal as CartSym
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Kleisli
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric
open import Categories.Category.Monoidal.Instance.Setoids
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Markov
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative
open import Categories.Monad.Strong
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Level using (suc; 0ℓ; Lift; lift)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚP

open import categorical-crypto.Prelude hiding (Monad; suc)
open import ProbabilisticLogic.Distribution.RationalDist

------------------------------------------------------------------------
-- The Setoid-valued action of `Dist-ℚ` on objects of `Setoids 0ℓ 0ℓ`.

≈*-data : ∀ {A : Type} → (A → A → Set) → Dist-ℚ A → Dist-ℚ A → Set
≈*-data {A} _≈ₐ_ μ ν =
  ∀ (P : A → ℚ) → (∀ {a₁ a₂} → a₁ ≈ₐ a₂ → P a₁ ≡ P a₂)
  → lookupᴰℚ (entries μ) P ≡ lookupᴰℚ (entries ν) P

Dist-ℚ-Setoid : Setoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ
Dist-ℚ-Setoid S = record
  { Carrier = Dist-ℚ (Setoid.Carrier S)
  ; _≈_     = ≈*-data (Setoid._≈_ S)
  ; isEquivalence = record
      { refl  = λ _ _ → refl
      ; sym   = λ μ≈ν P P-cong → sym (μ≈ν P P-cong)
      ; trans = λ μ≈ν ν≈ρ P P-cong → trans (μ≈ν P P-cong) (ν≈ρ P P-cong)
      }
  }

------------------------------------------------------------------------
-- `Dist-ℚ` as a Functor on `Setoids 0ℓ 0ℓ`.

Dist-ℚ-Functor : Endofunctor (Setoids 0ℓ 0ℓ)
Dist-ℚ-Functor = record
  { F₀ = Dist-ℚ-Setoid
  ; F₁ = λ {S} f → record
      { to   = Dmap (Func.to f)
      ; cong = λ {μ} {ν} μ≈ν Q Q-cong → trans
          (lookupᴰℚ-Dmap (Func.to f) μ Q)
          (trans (μ≈ν (Q ∘′ Func.to f) (λ p → Q-cong (Func.cong f p)))
                 (sym (lookupᴰℚ-Dmap (Func.to f) ν Q)))
      }
  ; identity     = λ {_} {μ} P _ → lookupᴰℚ-Dmap id μ P
  ; homomorphism = λ {_} {_} {_} {f} {g} {μ} P _ → trans
      (lookupᴰℚ-Dmap (Func.to g ∘′ Func.to f) μ P)
      (sym (trans (lookupᴰℚ-Dmap (Func.to g) (Dmap (Func.to f) μ) P)
                  (lookupᴰℚ-Dmap (Func.to f) μ (P ∘′ Func.to g))))
  ; F-resp-≈ = λ {_} {_} {f} {g} f≈g {μ} P P-cong → trans
      (lookupᴰℚ-Dmap (Func.to f) μ P)
      (trans (lookupᴰℚ-cong-P (entries μ) (λ _ → P-cong f≈g))
             (sym (lookupᴰℚ-Dmap (Func.to g) μ P)))
  }

------------------------------------------------------------------------
-- η and μ as natural transformations.

lookupᴰℚ-join : ∀ {A : Type} (μ : Dist-ℚ (Dist-ℚ A)) (P : A → ℚ)
              → lookupᴰℚ (entries (μ >>=ᴹ id)) P
              ≡ lookupᴰℚ (entries μ) (λ ν → lookupᴰℚ (entries ν) P)
lookupᴰℚ-join μ P = lookupᴰℚ-bind (entries μ) entries P

η-NT : NaturalTransformation idF Dist-ℚ-Functor
η-NT = ntHelper record
  { η = λ S → record
      { to   = return-ℚ
      ; cong = λ {a₁ a₂} a₁≈a₂ P P-cong → cong (λ b → 1ℚ ℚ.* b ℚ.+ 0ℚ) (P-cong a₁≈a₂)
      }
  ; commute = λ {S} {T} f {x} P P-cong → refl
  }

μ-NT : NaturalTransformation (Dist-ℚ-Functor ∘F Dist-ℚ-Functor) Dist-ℚ-Functor
μ-NT = ntHelper record
  { η = λ _ → record
      { to   = _>>=ᴹ id
      ; cong = λ {μμ νν} μμ≈νν P P-cong → trans
          (lookupᴰℚ-join μμ P)
          (trans (μμ≈νν (λ ν → lookupᴰℚ (entries ν) P) (λ ν₁≈ν₂ → ν₁≈ν₂ P P-cong))
                 (sym (lookupᴰℚ-join νν P)))
      }
  ; commute = λ f {μμ} P _ → trans
      (Dmap->>= (Dmap (Func.to f)) μμ id P)
      (sym (>>=ᴹ-assoc μμ id (return-ℚ ∘′ Func.to f) P))
  }

------------------------------------------------------------------------
-- The Dist-ℚ Monad on Setoids.

Dist-ℚ-Monad : Monad (Setoids 0ℓ 0ℓ)
Dist-ℚ-Monad = record
  { F = Dist-ℚ-Functor
  ; η = η-NT
  ; μ = μ-NT
  ; assoc      = λ {S} {μμμ} P P-cong → sym (assoc-pf {S} {μμμ} P P-cong)
  ; sym-assoc  = λ {S} {μμμ} P P-cong → assoc-pf {S} {μμμ} P P-cong
  ; identityˡ  = λ {_} {μ} P _ → trans (Dmap->>= return-ℚ μ id P) (>>=ᴹ-identityʳ μ P)
  ; identityʳ  = λ {_} {x} P _ → >>=ᴹ-identityˡ x id P
  }
  where
    assoc-pf : ∀ {S : Setoid 0ℓ 0ℓ} {μμμ : Dist-ℚ (Dist-ℚ (Dist-ℚ (Setoid.Carrier S)))}
               (P : Setoid.Carrier S → ℚ)
             → (∀ {a₁ a₂ : Setoid.Carrier S} → Setoid._≈_ S a₁ a₂ → P a₁ ≡ P a₂)
             → lookupᴰℚ (entries ((μμμ >>=ᴹ id) >>=ᴹ id)) P
             ≡ lookupᴰℚ (entries (Dmap (_>>=ᴹ id) μμμ >>=ᴹ id)) P
    assoc-pf {μμμ = μμμ} P _ =
      trans (>>=ᴹ-assoc μμμ id id P) (sym (Dmap->>= (_>>=ᴹ id) μμμ id P))

Dist-ℚ-Kleisli-Cat : Category (suc 0ℓ) 0ℓ 0ℓ
Dist-ℚ-Kleisli-Cat = Kleisli Dist-ℚ-Monad

setoids-symmetric : Symmetric Setoids-Monoidal
setoids-symmetric = CartSym.symmetric (Setoids 0ℓ 0ℓ) Setoids-Cartesian

private
  t-pure : ∀ {X Y : Type} → X × Dist-ℚ Y → Dist-ℚ (X × Y)
  t-pure (x , μ) = Dmap (x ,_) μ

  lookupᴰℚ-t-pure : ∀ {X Y : Type} (x : X) (μ : Dist-ℚ Y) (Q : X × Y → ℚ)
                  → lookupᴰℚ (entries (t-pure (x , μ))) Q
                  ≡ lookupᴰℚ (entries μ) (λ y → Q (x , y))
  lookupᴰℚ-t-pure x μ Q = lookupᴰℚ-Dmap (x ,_) μ Q

Dist-ℚ-Strength : Strength Setoids-Monoidal Dist-ℚ-Monad
Dist-ℚ-Strength = record
  { strengthen = ntHelper record
      { η = λ (S , T) → record
          { to   = t-pure
          ; cong = λ {p₁ p₂} (x≈ , μ≈) → cong-pf {S} {T} {p₁} {p₂} x≈ μ≈
          }
      ; commute = λ {S₁S₂} {T₁T₂} (f , g) {p} →
          commute-pf {proj₁ S₁S₂} {proj₂ S₁S₂} {proj₁ T₁T₂} {proj₂ T₁T₂} f g {p}
      }
  ; identityˡ = λ {A} {p} → identityˡ-pf {A} {p}
  ; η-comm = λ {A} {B} {p} → η-comm-pf {A} {B} {p}
  ; μ-η-comm = λ {A} {B} {p} → μ-η-comm-pf {A} {B} {p}
  ; strength-assoc = λ {A} {B} {C} {p} → strength-assoc-pf {A} {B} {C} {p}
  }
  where
    cong-pf : ∀ {S T : Setoid 0ℓ 0ℓ} {p₁ p₂ : Setoid.Carrier S × Dist-ℚ (Setoid.Carrier T)}
            → Setoid._≈_ S (proj₁ p₁) (proj₁ p₂)
            → ≈*-data (Setoid._≈_ T) (proj₂ p₁) (proj₂ p₂)
            → ≈*-data (λ p p′ → Setoid._≈_ S (proj₁ p) (proj₁ p′) × Setoid._≈_ T (proj₂ p) (proj₂ p′))
                       (t-pure p₁) (t-pure p₂)
    cong-pf {S} {T} {x₁ , μ₁} {x₂ , μ₂} x≈ μ≈ Q Q-cong = trans
      (lookupᴰℚ-t-pure x₁ μ₁ Q)
      (trans (μ≈ (Q ∘ (x₁ ,_)) (Q-cong ∘ (Setoid.refl S ,_)))
             (sym (trans (lookupᴰℚ-t-pure x₂ μ₂ Q)
                         (lookupᴰℚ-cong-P (entries μ₂) λ y →
                           Q-cong (Setoid.sym S x≈ , Setoid.refl T)))))

    commute-pf : ∀ {S₁ S₂ T₁ T₂ : Setoid 0ℓ 0ℓ}
                 (f : Func S₁ T₁) (g : Func S₂ T₂)
                 {p : Setoid.Carrier S₁ × Dist-ℚ (Setoid.Carrier S₂)}
                 (P : Setoid.Carrier T₁ × Setoid.Carrier T₂ → ℚ)
               → (∀ {p₁ p₂} →
                    Setoid._≈_ T₁ (proj₁ p₁) (proj₁ p₂)
                    × Setoid._≈_ T₂ (proj₂ p₁) (proj₂ p₂)
                    → P p₁ ≡ P p₂)
               → lookupᴰℚ (entries (t-pure (Func.to f (proj₁ p) , Dmap (Func.to g) (proj₂ p)))) P
               ≡ lookupᴰℚ (entries (Dmap (λ q → Func.to f (proj₁ q) , Func.to g (proj₂ q))
                                     (t-pure (proj₁ p , (proj₂ p))))) P
    commute-pf f g {p = x , μ} P _ = trans
      (sym (Dmap-∘ (Func.to g) (Func.to f x ,_) μ P))
      (Dmap-∘ (x ,_) (λ q → Func.to f (proj₁ q) , Func.to g (proj₂ q)) μ P)

    identityˡ-pf : ∀ {A : Setoid 0ℓ 0ℓ} {p : Lift 0ℓ ⊤ × Dist-ℚ (Setoid.Carrier A)}
                   (P : Setoid.Carrier A → ℚ)
                 → (∀ {a₁ a₂} → Setoid._≈_ A a₁ a₂ → P a₁ ≡ P a₂)
                 → lookupᴰℚ (entries (Dmap proj₂ (t-pure p))) P ≡ lookupᴰℚ (entries (proj₂ p)) P
    identityˡ-pf {p = _ , μ} P _ = trans (sym (Dmap-∘ (_ ,_) proj₂ μ P)) (Dmap-id μ P)

    η-comm-pf : ∀ {A B : Setoid 0ℓ 0ℓ}
                 {p : Setoid.Carrier A × Setoid.Carrier B}
                 (P : Setoid.Carrier A × Setoid.Carrier B → ℚ)
               → (∀ {p₁ p₂} → Setoid._≈_ A (proj₁ p₁) (proj₁ p₂) × Setoid._≈_ B (proj₂ p₁) (proj₂ p₂)
                    → P p₁ ≡ P p₂)
               → lookupᴰℚ (entries (t-pure (proj₁ p , return-ℚ (proj₂ p)))) P
               ≡ lookupᴰℚ (entries (return-ℚ p)) P
    η-comm-pf {p = x , y} P _ = refl

    μ-η-comm-pf : ∀ {A B : Setoid 0ℓ 0ℓ}
                   {p : Setoid.Carrier A × Dist-ℚ (Dist-ℚ (Setoid.Carrier B))}
                   (P : Setoid.Carrier A × Setoid.Carrier B → ℚ)
                 → (∀ {p₁ p₂} → Setoid._≈_ A (proj₁ p₁) (proj₁ p₂) × Setoid._≈_ B (proj₂ p₁) (proj₂ p₂)
                      → P p₁ ≡ P p₂)
                 → lookupᴰℚ (entries ((Dmap t-pure (t-pure p)) >>=ᴹ (λ x → x))) P
                 ≡ lookupᴰℚ (entries (t-pure (proj₁ p , (proj₂ p >>=ᴹ (λ x → x))))) P
    μ-η-comm-pf {p = x , μμ} P _ = trans
      (Dmap->>= t-pure (t-pure (x , μμ)) id P)
      (trans (Dmap->>= (x ,_) μμ t-pure P) (sym (>>=ᴹ-assoc μμ id (return-ℚ ∘′ (x ,_)) P)))

    strength-assoc-pf : ∀ {A B C : Setoid 0ℓ 0ℓ}
        {p : (Setoid.Carrier A × Setoid.Carrier B) × Dist-ℚ (Setoid.Carrier C)}
        (P : Setoid.Carrier A × Setoid.Carrier B × Setoid.Carrier C → ℚ)
      → (∀ {p₁ p₂} → Setoid._≈_ A (proj₁ p₁) (proj₁ p₂)
                     × Setoid._≈_ B (proj₁ (proj₂ p₁)) (proj₁ (proj₂ p₂))
                       × Setoid._≈_ C (proj₂ (proj₂ p₁)) (proj₂ (proj₂ p₂))
           → P p₁ ≡ P p₂)
      → lookupᴰℚ (entries (Dmap (λ p → proj₁ (proj₁ p) , proj₂ (proj₁ p) , proj₂ p) (t-pure p))) P
      ≡ lookupᴰℚ (entries (t-pure ((proj₁ (proj₁ p)) , t-pure (proj₂ (proj₁ p) , proj₂ p)))) P
    strength-assoc-pf {p = (a , b) , μ} P _ = trans
      (sym (Dmap-∘ ((a , b) ,_) (λ p → proj₁ (proj₁ p) , proj₂ (proj₁ p) , proj₂ p) μ P))
      (Dmap-∘ (b ,_) (a ,_) μ P)

------------------------------------------------------------------------
-- Strong monad and commutative monad.

Dist-ℚ-StrongMonad : StrongMonad Setoids-Monoidal
Dist-ℚ-StrongMonad = record
  { M        = Dist-ℚ-Monad
  ; strength = Dist-ℚ-Strength
  }

Dist-ℚ-Commutative : Commutative (Symmetric.braided setoids-symmetric) Dist-ℚ-StrongMonad
Dist-ℚ-Commutative = record
  { commutes = λ {X} {Y} {p} → commutes-pf {X} {Y} p
  }
  where
    swap-fn : ∀ {A B : Type} → A × B → B × A
    swap-fn (a , b) = b , a

    commutes-pf : ∀ {X Y : Setoid 0ℓ 0ℓ}
        (p : Dist-ℚ (Setoid.Carrier X) × Dist-ℚ (Setoid.Carrier Y))
        (P : Setoid.Carrier X × Setoid.Carrier Y → ℚ)
      → (∀ {p₁ p₂} → Setoid._≈_ X (proj₁ p₁) (proj₁ p₂) × Setoid._≈_ Y (proj₂ p₁) (proj₂ p₂)
           → P p₁ ≡ P p₂)
      → lookupᴰℚ (entries ((Dmap (λ q → Dmap swap-fn (Dmap (proj₂ q ,_) (proj₁ q)))
             (Dmap (proj₁ p ,_) (proj₂ p))) >>=ᴹ id)) P
      ≡ lookupᴰℚ (entries ((Dmap (λ q → Dmap (proj₁ q ,_) (proj₂ q))
             (Dmap swap-fn (Dmap (proj₂ p ,_) (proj₁ p)))) >>=ᴹ id)) P
    commutes-pf (μ , ν) P _ = begin
      lookupᴰℚ (entries
        ((Dmap (λ q → Dmap swap-fn (Dmap (proj₂ q ,_) (proj₁ q))) (Dmap (μ ,_) ν)) >>=ᴹ id)) P
        ≡⟨ Dmap->>= (λ q → Dmap swap-fn (Dmap (proj₂ q ,_) (proj₁ q))) (Dmap (μ ,_) ν) id P ⟩
      lookupᴰℚ (entries
        ((Dmap (μ ,_) ν) >>=ᴹ (λ q → Dmap swap-fn (Dmap (proj₂ q ,_) (proj₁ q))))) P
        ≡⟨ Dmap->>= (μ ,_) ν (λ q → Dmap swap-fn (Dmap (proj₂ q ,_) (proj₁ q))) P ⟩
      lookupᴰℚ (entries (ν >>=ᴹ (λ y → Dmap swap-fn (Dmap (y ,_) μ)))) P
        ≡⟨ >>=ᴹ-cong {μ = ν} {ν = ν}
              {f = λ y → Dmap swap-fn (Dmap (y ,_) μ)} {g = λ y → μ >>=ᴹ (λ x → return-ℚ (x , y))}
              (λ _ → refl) (λ y P′ → sym (Dmap-∘ (y ,_) swap-fn μ P′)) P ⟩
      lookupᴰℚ (entries (ν >>=ᴹ (λ y → μ >>=ᴹ (λ x → return-ℚ (x , y))))) P
        ≡⟨ sym (>>=ᴹ-comm μ ν (λ x y → return-ℚ (x , y)) P) ⟩
      lookupᴰℚ (entries (μ >>=ᴹ (λ x → ν >>=ᴹ (λ y → return-ℚ (x , y))))) P
        ≡⟨ sym (Dmap->>= (ν ,_) μ (λ p → Dmap (proj₁ (swap-fn p) ,_) (proj₂ (swap-fn p))) P) ⟩
      lookupᴰℚ (entries
        ((Dmap (ν ,_) μ) >>=ᴹ (λ p → Dmap (proj₁ (swap-fn p) ,_) (proj₂ (swap-fn p))))) P
        ≡⟨ sym (Dmap->>= swap-fn (Dmap (ν ,_) μ) (λ q → Dmap (proj₁ q ,_) (proj₂ q)) P) ⟩
      lookupᴰℚ (entries
        ((Dmap swap-fn (Dmap (ν ,_) μ)) >>=ᴹ (λ q → Dmap (proj₁ q ,_) (proj₂ q)))) P
        ≡⟨ sym (Dmap->>= (λ q → Dmap (proj₁ q ,_) (proj₂ q)) (Dmap swap-fn (Dmap (ν ,_) μ)) id P) ⟩
      lookupᴰℚ (entries
        ((Dmap (λ q → Dmap (proj₁ q ,_) (proj₂ q)) (Dmap swap-fn (Dmap (ν ,_) μ))) >>=ᴹ id)) P ∎
      where open ≡-Reasoning

Dist-ℚ-CommutativeMonad : CommutativeMonad (Symmetric.braided setoids-symmetric)
Dist-ℚ-CommutativeMonad = record
  { strongMonad = Dist-ℚ-StrongMonad
  ; commutative = Dist-ℚ-Commutative
  }

------------------------------------------------------------------------
-- Symmetric Monoidal structure on the Kleisli

Dist-ℚ-Kleisli-Monoidal : Monoidal Dist-ℚ-Kleisli-Cat
Dist-ℚ-Kleisli-Monoidal = Kleisli-Monoidal setoids-symmetric Dist-ℚ-CommutativeMonad

Dist-ℚ-Kleisli-Symmetric : Symmetric Dist-ℚ-Kleisli-Monoidal
Dist-ℚ-Kleisli-Symmetric = Kleisli-Symmetric setoids-symmetric Dist-ℚ-CommutativeMonad

------------------------------------------------------------------------
-- MarkovCategory structure on the Kleisli of `Dist-ℚ`.

private
  unit-setoid : Setoid 0ℓ 0ℓ
  unit-setoid = Monoidal.unit Setoids-Monoidal

  del-fn : ∀ {X : Type} → X → Dist-ℚ (Lift 0ℓ ⊤)
  del-fn _ = return-ℚ (lift tt)

  copy-K : ∀ {X : Setoid 0ℓ 0ℓ} → Func X (Dist-ℚ-Setoid (X ×ₛ X))
  copy-K = record
    { to   = λ x → return-ℚ (x , x)
    ; cong = λ x₁≈x₂ P P-cong → cong (λ b → 1ℚ ℚ.* b ℚ.+ 0ℚ) (P-cong (x₁≈x₂ , x₁≈x₂))
    }

  del-K : ∀ {X : Setoid 0ℓ 0ℓ} → Func X (Dist-ℚ-Setoid unit-setoid)
  del-K = record
    { to   = del-fn
    ; cong = λ _ _ _ → refl
    }

  discard-≈Mℚ : ∀ {Y : Type} (μ : Dist-ℚ Y)
                (P : Lift 0ℓ ⊤ → ℚ)
              → lookupᴰℚ (entries (Dmap del-fn μ >>=ᴹ id)) P
              ≡ lookupᴰℚ (entries (return-ℚ (lift tt))) P
  discard-≈Mℚ μ P = begin
    lookupᴰℚ (entries (Dmap del-fn μ >>=ᴹ id)) P
      ≡⟨ lookupᴰℚ-bind (entries (Dmap del-fn μ)) _ P ⟩
    lookupᴰℚ (entries (Dmap del-fn μ)) (λ ν → lookupᴰℚ (entries ν) P)
      ≡⟨ lookupᴰℚ-Dmap del-fn μ (λ ν → lookupᴰℚ (entries ν) P) ⟩
    lookupᴰℚ (entries μ) (λ _ → lookupᴰℚ (entries (return-ℚ (lift tt))) P)
      ≡⟨ mass-as-const (entries μ) _ ⟩
    mass (entries μ) ℚ.* (1ℚ ℚ.* P (lift tt) ℚ.+ 0ℚ)
      ≡⟨ cong (ℚ._* (1ℚ ℚ.* P (lift tt) ℚ.+ 0ℚ)) (Dist-ℚ.mass-1 μ) ⟩
    1ℚ ℚ.* (1ℚ ℚ.* P (lift tt) ℚ.+ 0ℚ)
      ≡⟨ ℚP.*-identityˡ _ ⟩
    1ℚ ℚ.* P (lift tt) ℚ.+ 0ℚ ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- The MarkovCategory instance for `Dist-ℚ`'s Kleisli.

Dist-ℚ-MarkovCategory : MarkovCategory Dist-ℚ-Kleisli-Symmetric
Dist-ℚ-MarkovCategory = record
  { copy            = copy-K
  ; del             = del-K
  ; counit-l        = λ _ _ → refl
  ; counit-r        = λ _ _ → refl
  ; coassoc         = λ _ _ → refl
  ; cocomm          = λ _ _ → refl
  ; copy-⊗          = λ _ _ → refl
  ; del-⊗           = λ _ _ → refl
  ; del-𝟙           = λ _ _ → refl
  ; copy-𝟙          = λ _ _ → refl
  ; discard-natural = λ f P _ → discard-≈Mℚ (Func.to f _) P
  }

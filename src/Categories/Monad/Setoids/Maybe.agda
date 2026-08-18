{-# OPTIONS --safe --without-K #-}

-- `Maybe` as a monad on `Setoids`, up to the element setoid's own equality.

open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Monad.Construction.Kleisli
import Categories.Monad.Setoids.Discrete as Discrete

open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Relation.Binary.Pointwise as Pw using (Pointwise)
open import Function.Bundles
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module Categories.Monad.Setoids.Maybe where

open Setoid using (Carrier)

private
  variable
    ℓ ℓ′ ℓ″ : Level
    S : Setoid ℓ ℓ
    S′ : Setoid ℓ′ ℓ′
    S″ : Setoid ℓ″ ℓ″

  ≈ᴹᵇ : (S : Setoid ℓ ℓ) → Maybe (Carrier S) → Maybe (Carrier S) → Set ℓ
  ≈ᴹᵇ S = Pointwise (Setoid._≈_ S)

  >>=-congᴹᵇ : {x y : Maybe (Carrier S)} {f g : Carrier S → Maybe (Carrier S′)}
             → ≈ᴹᵇ S x y → (∀ {a b} → Setoid._≈_ S a b → ≈ᴹᵇ S′ (f a) (g b))
             → ≈ᴹᵇ S′ (x >>= f) (y >>= g)
  >>=-congᴹᵇ (Pw.just a≈b) f≈g = f≈g a≈b
  >>=-congᴹᵇ Pw.nothing    _   = Pw.nothing

Maybe-KleisliTriple : KleisliTriple (Setoids ℓ ℓ)
Maybe-KleisliTriple = record
  { F₀        = Pw.setoid
  ; unit      = record { to = just ; cong = Pw.just }
  ; extend    = λ {S} {S′} f → record
      { to   = _>>= (f ⟨$⟩_)
      ; cong = λ x≈y → >>=-congᴹᵇ {S = S} {S′ = S′} x≈y (Func.cong f)
      }
  ; identityʳ = λ {_} {S′} → Pw.refl (Setoid.refl S′)
  ; identityˡ = λ {S} {x} → identityˡᴹᵇ {S = S} x
  ; assoc     = λ {S} {S′} {S″} {k} {l} {x} → Setoid.sym (Pw.setoid S″)
      (assocᴹᵇ {S = S} {S′ = S′} {S″ = S″} {k = k} {l = l} x)
  ; sym-assoc = λ {S} {S′} {S″} {k} {l} {x} →
      assocᴹᵇ {S = S} {S′ = S′} {S″ = S″} {k = k} {l = l} x
  ; extend-≈  = λ {S} {S′} {k} {h} k≈h {x} →
      >>=-congᴹᵇ {S = S} {S′ = S′} {x = x} {y = x} {f = k ⟨$⟩_} {g = h ⟨$⟩_}
                 (Pw.refl (Setoid.refl S)) λ a≈b →
        Setoid.trans (Pw.setoid S′) k≈h (Func.cong h a≈b)
  }
  where
  identityˡᴹᵇ : (x : Maybe (Carrier S)) → ≈ᴹᵇ S (x >>= just) x
  identityˡᴹᵇ {S = S} (just _) = Pw.just (Setoid.refl S)
  identityˡᴹᵇ         nothing  = Pw.nothing

  assocᴹᵇ : {k : Func S (Pw.setoid S′)} {l : Func S′ (Pw.setoid S″)}
            (x : Maybe (Carrier S))
          → ≈ᴹᵇ S″ ((x >>= (k ⟨$⟩_)) >>= (l ⟨$⟩_)) (x >>= λ a → (k ⟨$⟩ a) >>= (l ⟨$⟩_))
  assocᴹᵇ {S″ = S″} (just _) = Pw.refl (Setoid.refl S″)
  assocᴹᵇ           nothing  = Pw.nothing

Maybe-commutative : Discrete.Commutative (Maybe-KleisliTriple {ℓ})
Maybe-commutative = record { >>=-comm = λ {A} {B} {x} {y} → commᴹᵇ _ x y }
  where
  commᴹᵇ : {A B C : Set ℓ} (f : A → B → Maybe C) (x : Maybe A) (y : Maybe B)
         → ≈ᴹᵇ (≡-setoid C) (x >>= λ a → y >>= f a) (y >>= λ b → x >>= λ a → f a b)
  commᴹᵇ {C = C} _ (just _) (just _) = Pw.refl (Setoid.refl (≡-setoid C))
  commᴹᵇ         _ (just _) nothing  = Pw.nothing
  commᴹᵇ         _ nothing  (just _) = Pw.nothing
  commᴹᵇ         _ nothing  nothing  = Pw.nothing

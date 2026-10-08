{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Adjacent-transposition words for `Sₙ`.
--
-- A `Word n` has indices `Fin n` acting on positions `Fin (suc n)`;
-- generator `i` swaps `i, suc i`.  Evaluation is right-to-left:
-- `evalW (g ∷ w) = genFB g ∘-fb evalW w`, so the head acts last.
-- This is opposite to `Data.Fin.Permutation.Transposition.List.eval`,
-- whose diagrammatic `_∘ₚ_` applies the head transposition first.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Coxeter.Word where

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.FinBij.Properties as Snd

open import Data.Fin.Base renaming (suc to fsuc)
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open P
open import Data.List.Base
open import Data.List.Properties
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

private
  variable
    n m k : ℕ

genFB : Fin n → FinBij (suc n) (suc n)
genFB {suc n} 0F       = swap-fb n
genFB {suc n} (fsuc j) = cons-fb (genFB j)

------------------------------------------------------------------------
-- Words and evaluation
------------------------------------------------------------------------
Word : ℕ → Set
Word n = List (Fin n)

evalW : Word n → FinBij (suc n) (suc n)
evalW []      = id-fb
evalW (i ∷ w) = genFB i ∘-fb evalW w

------------------------------------------------------------------------
-- Concatenation and lifting
------------------------------------------------------------------------
evalW-++ : (v w : Word n) → evalW (v ++ w) ≈-fb (evalW v ∘-fb evalW w)
evalW-++ []      w i = refl
evalW-++ (g ∷ v) w i = cong (genFB g P.⟨$⟩ʳ_) (evalW-++ v w i)

liftW : Word n → Word (suc n)
liftW = map fsuc

eval-liftW : (w : Word n) → evalW (liftW w) ≈-fb cons-fb (evalW w)
eval-liftW []      0F       = refl
eval-liftW []      (fsuc i) = refl
eval-liftW (g ∷ w) i =
  trans (cong (cons-fb (genFB g) P.⟨$⟩ʳ_) (eval-liftW w i))
        (sym (Snd.cons-fb-functor-comp (genFB g) (evalW w) i))

------------------------------------------------------------------------
-- Head-bubbling rotations
------------------------------------------------------------------------

rotate-fb : Fin (suc n) → FinBij (suc n) (suc n)
rotate-fb {n}     0F       = id-fb
rotate-fb {suc n} (fsuc m) = swap-fb n ∘-fb cons-fb (rotate-fb m)

rotateW : Fin (suc n) → Word n
rotateW {n}     0F       = []
rotateW {suc n} (fsuc m) = 0F ∷ liftW (rotateW m)

rotateW-sound : (m : Fin (suc n)) → evalW (rotateW m) ≈-fb rotate-fb m
rotateW-sound {n}     0F       i = refl
rotateW-sound {suc n} (fsuc m) =
  ∘-fb-congʳ (swap-fb n) (evalW (liftW (rotateW m))) (cons-fb (rotate-fb m))
    (λ j → trans (eval-liftW (rotateW m) j) (cons-fb-cong (rotateW-sound m) j))

rotate-fb-front : (m : Fin (suc n)) → rotate-fb m P.⟨$⟩ʳ m ≡ 0F
rotate-fb-front {n}     0F       = refl
rotate-fb-front {suc n} (fsuc m) = cong (λ z → swap-fb n P.⟨$⟩ʳ fsuc z) (rotate-fb-front m)

inv-rotate-fb-0 : (m : Fin (suc n)) → inv-fb (rotate-fb m) P.⟨$⟩ʳ 0F ≡ m
inv-rotate-fb-0 m =
  trans (cong (rotate-fb m P.⟨$⟩ˡ_) (sym (rotate-fb-front m)))
        (P.inverseˡ (rotate-fb m))

------------------------------------------------------------------------
-- Bubble-sort canonical words
------------------------------------------------------------------------

-- Mirrors `Data.Fin.Permutation.Transposition.List.decompose`, replacing
-- its head transposition with an adjacent-swap rotation.

canonW : FinBij (suc n) (suc n) → Word n
canonW {zero}  b = []
canonW {suc n} b =
  let m    = b P.⟨$⟩ˡ 0F
      rest = remove 0F (b ∘-fb inv-fb (rotate-fb m))
  in liftW (canonW rest) ++ rotateW m

peel : (b : FinBij (suc n) (suc n))
     → b ≈-fb (cons-fb (remove 0F (b ∘-fb inv-fb (rotate-fb (b P.⟨$⟩ˡ 0F))))
               ∘-fb rotate-fb (b P.⟨$⟩ˡ 0F))
peel {n} b i = sym (trans stepC stepD)
  where
  m₀   = b P.⟨$⟩ˡ 0F
  ρ    = rotate-fb m₀
  bρ⁻¹ = b ∘-fb inv-fb ρ
  rest = remove 0F bρ⁻¹

  fix0 : bρ⁻¹ P.⟨$⟩ʳ 0F ≡ 0F
  fix0 = trans (cong (b P.⟨$⟩ʳ_) (inv-rotate-fb-0 m₀)) (P.inverseʳ b)

  stepC : (cons-fb rest ∘-fb ρ) P.⟨$⟩ʳ i ≡ (bρ⁻¹ ∘-fb ρ) P.⟨$⟩ʳ i
  stepC = ∘-fb-congˡ (cons-fb rest) bρ⁻¹ ρ (P.lift₀-remove bρ⁻¹ fix0) i

  stepD : (bρ⁻¹ ∘-fb ρ) P.⟨$⟩ʳ i ≡ b P.⟨$⟩ʳ i
  stepD = cong (b P.⟨$⟩ʳ_) (P.inverseˡ ρ)

------------------------------------------------------------------------
-- Coxeter relations
------------------------------------------------------------------------

-- Relations are generated at the front; `lift~` propagates them to depth.
data Far : {n : ℕ} → Fin n → Fin n → Set where
  far0ˡ : {j : Fin n} → Far {suc (suc n)} 0F (fsuc (fsuc j))
  farS  : {i j : Fin n} → Far i j → Far (fsuc i) (fsuc j)

data Adj : {n : ℕ} → Fin n → Fin n → Set where
  adj0 : Adj {suc (suc n)} 0F (fsuc 0F)
  adjS : {i k : Fin n} → Adj i k → Adj (fsuc i) (fsuc k)

infix 4 _~ʷ_

data _~ʷ_ : {n : ℕ} → Word n → Word n → Set where

  ~refl  : {w : Word n} → w ~ʷ w
  ~sym   : {v w : Word n} → v ~ʷ w → w ~ʷ v
  ~trans : {u v w : Word n} → u ~ʷ v → v ~ʷ w → u ~ʷ w

  ∷c : {i : Fin n} {v w : Word n} → v ~ʷ w → (i ∷ v) ~ʷ (i ∷ w)

  c1 : (i : Fin n) {w : Word n} → (i ∷ i ∷ w) ~ʷ w

  c2 : {i j : Fin n} {w : Word n} → Far i j → (i ∷ j ∷ w) ~ʷ (j ∷ i ∷ w)

  c3 : {i k : Fin n} {w : Word n} → Adj i k → (i ∷ k ∷ i ∷ w) ~ʷ (k ∷ i ∷ k ∷ w)

------------------------------------------------------------------------
-- Derived congruences
------------------------------------------------------------------------

∷-cong : (i : Fin n) {v w : Word n} → v ~ʷ w → (i ∷ v) ~ʷ (i ∷ w)
∷-cong _ = ∷c

lift~ : {v w : Word n} → v ~ʷ w → liftW v ~ʷ liftW w
lift~ ~refl          = ~refl
lift~ (~sym r)       = ~sym (lift~ r)
lift~ (~trans r₁ r₂) = ~trans (lift~ r₁) (lift~ r₂)
lift~ (∷c r)         = ∷c (lift~ r)
lift~ (c1 i)         = c1 (fsuc i)
lift~ (c2 far)       = c2 (farS far)
lift~ (c3 adj)       = c3 (adjS adj)

++c-r : {v v′ : Word n} (w : Word n) → v ~ʷ v′ → (v ++ w) ~ʷ (v′ ++ w)
++c-r w ~refl          = ~refl
++c-r w (~sym r)       = ~sym (++c-r w r)
++c-r w (~trans r₁ r₂) = ~trans (++c-r w r₁) (++c-r w r₂)
++c-r w (∷c r)         = ∷c (++c-r w r)
++c-r w (c1 i)         = c1 i
++c-r w (c2 far)       = c2 far
++c-r w (c3 adj)       = c3 adj

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------
genFB-involutive : (i : Fin n) → (genFB i ∘-fb genFB i) ≈-fb id-fb
genFB-involutive {suc n} 0F       = Snd.swap-fb-involutive
genFB-involutive {suc n} (fsuc j) =
  λ p → trans (sym (Snd.cons-fb-functor-comp (genFB j) (genFB j) p))
        (trans (cons-fb-cong (genFB-involutive j) p)
               (Snd.cons-fb-functor-id p))

genFB-far : {i j : Fin n} → Far i j
          → (genFB i ∘-fb genFB j) ≈-fb (genFB j ∘-fb genFB i)
genFB-far (far0ˡ {j = j}) = Snd.swap-fb-natural (genFB j)
genFB-far (farS {i = i} {j = j} far) =
  λ p → trans (sym (Snd.cons-fb-functor-comp (genFB i) (genFB j) p))
        (trans (cons-fb-cong (genFB-far far) p)
               (Snd.cons-fb-functor-comp (genFB j) (genFB i) p))

genFB-braid : {i k : Fin n} → Adj i k
            → (genFB i ∘-fb genFB k ∘-fb genFB i)
              ≈-fb (genFB k ∘-fb genFB i ∘-fb genFB k)
genFB-braid (adj0 {n = n}) = Snd.yang-baxter
genFB-braid (adjS {i = i} {k = k} adj) =
  λ p → trans (push-out-lhs p)
        (trans (cons-fb-cong (genFB-braid adj) p)
               (sym (push-out-rhs p)))
  where
  push-out-lhs
    : (cons-fb (genFB i) ∘-fb cons-fb (genFB k) ∘-fb cons-fb (genFB i))
      ≈-fb cons-fb (genFB i ∘-fb genFB k ∘-fb genFB i)
  push-out-lhs p =
    trans (cong (cons-fb (genFB i) P.⟨$⟩ʳ_)
                (sym (Snd.cons-fb-functor-comp (genFB k) (genFB i) p)))
          (sym (Snd.cons-fb-functor-comp (genFB i) (genFB k ∘-fb genFB i) p))
  push-out-rhs
    : (cons-fb (genFB k) ∘-fb cons-fb (genFB i) ∘-fb cons-fb (genFB k))
      ≈-fb cons-fb (genFB k ∘-fb genFB i ∘-fb genFB k)
  push-out-rhs p =
    trans (cong (cons-fb (genFB k) P.⟨$⟩ʳ_)
                (sym (Snd.cons-fb-functor-comp (genFB i) (genFB k) p)))
          (sym (Snd.cons-fb-functor-comp (genFB k) (genFB i ∘-fb genFB k) p))

~ʷ⇒≈ : {v w : Word n} → v ~ʷ w → evalW v ≈-fb evalW w
~ʷ⇒≈ ~refl          _ = refl
~ʷ⇒≈ (~sym r)       p = sym (~ʷ⇒≈ r p)
~ʷ⇒≈ (~trans r₁ r₂) p = trans (~ʷ⇒≈ r₁ p) (~ʷ⇒≈ r₂ p)
~ʷ⇒≈ (∷c {i = i} {v = v} {w = w} r) =
  ∘-fb-congʳ (genFB i) (evalW v) (evalW w) (~ʷ⇒≈ r)
~ʷ⇒≈ (c1 i {w = w}) =
  ∘-fb-congˡ (genFB i ∘-fb genFB i) id-fb (evalW w) (genFB-involutive i)
~ʷ⇒≈ (c2 {i = i} {j = j} {w = w} far) =
  ∘-fb-congˡ (genFB i ∘-fb genFB j) (genFB j ∘-fb genFB i) (evalW w)
             (genFB-far far)
~ʷ⇒≈ (c3 {i = i} {k = k} {w = w} adj) =
  ∘-fb-congˡ (genFB i ∘-fb genFB k ∘-fb genFB i)
             (genFB k ∘-fb genFB i ∘-fb genFB k) (evalW w) (genFB-braid adj)

------------------------------------------------------------------------
-- Canonical-word congruence and identity
------------------------------------------------------------------------

canonW-resp-≈ : {b b′ : FinBij (suc n) (suc n)}
              → b ≈-fb b′ → canonW b ~ʷ canonW b′
canonW-resp-≈ {zero}      eq = ~refl
canonW-resp-≈ {suc n} {b} {b′} eq =
  subst (λ z → canonW b ~ʷ (liftW (canonW rest′) ++ rotateW z)) m≡
        (++c-r (rotateW (b P.⟨$⟩ˡ 0F)) (lift~ rec))
  where
  m≡ : b P.⟨$⟩ˡ 0F ≡ b′ P.⟨$⟩ˡ 0F
  m≡ = ≈ˡ {f = b} {g = b′} eq 0F

  restb rest′ : FinBij (suc n) (suc n)
  restb = remove 0F (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
  rest′ = remove 0F (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))

  rest≈ : restb ≈-fb rest′
  rest≈ = residual-pw-cong (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
                           (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))
            (∘-fb-cong {g = b} {g′ = b′}
                       {f = inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F))}
                       {f′ = inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F))}
                       eq (λ i → cong (λ z → inv-fb (rotate-fb z) P.⟨$⟩ʳ i) m≡))

  rec : canonW restb ~ʷ canonW rest′
  rec = canonW-resp-≈ {b = restb} {b′ = rest′} rest≈

canonW-id : canonW (id-fb {n = suc n}) ~ʷ []
canonW-id {zero}  = ~refl
canonW-id {suc n} =
  subst (_~ʷ []) (sym (++-identityʳ (liftW (canonW _))))
    (~trans (lift~ (canonW-resp-≈ {b = remove 0F (id-fb ∘-fb inv-fb id-fb)}
                                  {b′ = id-fb {n = suc n}}
                                  remove-0-of-id))
            (lift~ canonW-id))


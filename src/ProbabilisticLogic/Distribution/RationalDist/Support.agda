{-# OPTIONS --safe --without-K #-}

-- The support map as a setoid monad morphism `Dist-ℚ ⇒ 𝒫` (and `Dist⊥ ⇒ 𝒫`):
-- the possibilistic abstraction of probability, into the possibility monad of
-- `ProbabilisticLogic.Distribution.Possibility`.
--
-- `supp` keeps the entries of STRICTLY POSITIVE weight rather than the raw
-- representation support: `mk-Dist ((1ℚ , a) ∷ (0ℚ , b) ∷ …)` is `_≈Mℚ_` to
-- `return-ℚ a`, so a representation support would not be `_≈Mℚ_`-invariant and
-- `supp-cong` — the fact that makes the abstraction a functor — would be false.
--
-- The last two sections witness that the abstraction is lossy in both
-- directions: it forgets perfect secrecy (`pad-not-perfect`) and it is not
-- controlled by closeness (`close-supp-differs`).

-- `Data.List`'s `any` is the deprecated alias of `Data.Bool.ListAction.any`.
open import categorical-crypto.Prelude hiding (any)

open import Algebra using (CommutativeRing)
open import Data.Bool using (if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-comm; ∨-identityʳ)
open import Data.Integer using (+_)
open import Data.List.Base using (fromMaybe)
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties
  using ( +-*-commutativeRing; +-comm; +-identityʳ; +-inverseʳ
        ; +-mono-≤; +-mono-<-≤; +-mono-≤-<
        ; *-identityʳ; *-monoˡ-≤-nonNeg; *-zeroˡ; *-zeroʳ
        ; ≤-antisym; ≤-refl; ≤-reflexive; ≤-trans; <-irrefl; <⇒≤; ≮⇒≥
        ; pos*pos⇒pos; positive⁻¹; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p )
open import Data.Rational.Properties.Ext
open import Data.Rational.Solver using (module +-*-Solver)
open import Relation.Nullary.Decidable using (dec-false; dec-true; does)

open import ProbabilisticLogic.Distribution.Possibility
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
import ProbabilisticLogic.Distribution.Linearity as Linearity

module ProbabilisticLogic.Distribution.RationalDist.Support where

private
  -- the same instantiation as `RationalDist`'s, so `Lin.lookup-L` is
  -- definitionally `lookupᴰℚ` on the underlying list
  module Lin = Linearity (CommutativeRing.commutativeSemiring +-*-commutativeRing)

private variable
  ℓ : Level
  A B : Type ℓ

------------------------------------------------------------------------
-- Positivity of ℚ, reflected into `Bool`.

0<1ℚ : 0ℚ ℚ.< 1ℚ
0<1ℚ = toWitness {a? = 0ℚ ℚ.<? 1ℚ} tt

private
  0≤+ : {x y : ℚ} → 0ℚ ℚ.≤ x → 0ℚ ℚ.≤ y → 0ℚ ℚ.≤ x ℚ.+ y
  0≤+ {x} {y} 0≤x 0≤y = subst (ℚ._≤ x ℚ.+ y) (+-identityʳ 0ℚ) (+-mono-≤ 0≤x 0≤y)

  ≮⇒≡0 : {q : ℚ} → 0ℚ ℚ.≤ q → ¬ (0ℚ ℚ.< q) → q ≡ 0ℚ
  ≮⇒≡0 0≤q ¬0<q = ≤-antisym (≮⇒≥ ¬0<q) 0≤q

  -- The decisions are passed as ARGUMENTS: `with (0ℚ ℚ.<? x)` would not
  -- abstract, since `_<?_` unfolds and the goal no longer mentions it.
  dec-∨ : {P Q R : Type} (p : Dec P) (q : Dec Q) (r : Dec R)
        → (Q → P) → (R → P) → (¬ Q → ¬ R → ¬ P) → does p ≡ does q ∨ does r
  dec-∨ p (yes q) r       f _ _ = dec-true p (f q)
  dec-∨ p (no ¬q) (yes r) _ g _ = dec-true p (g r)
  dec-∨ p (no ¬q) (no ¬r) _ _ h = dec-false p (h ¬q ¬r)

  dec-∧ : {P Q R : Type} (p : Dec P) (q : Dec Q) (r : Dec R)
        → (Q → R → P) → (¬ Q → ¬ P) → (¬ R → ¬ P) → does p ≡ does q ∧ does r
  dec-∧ p (yes q) (yes r) f _ _ = dec-true p (f q r)
  dec-∧ p (yes q) (no ¬r) _ _ h = dec-false p (h ¬r)
  dec-∧ p (no ¬q) r       _ g _ = dec-false p (g ¬q)

  pos-+ : {x y : ℚ} → 0ℚ ℚ.≤ x → 0ℚ ℚ.≤ y
        → does (0ℚ ℚ.<? (x ℚ.+ y)) ≡ does (0ℚ ℚ.<? x) ∨ does (0ℚ ℚ.<? y)
  pos-+ {x} {y} 0≤x 0≤y = dec-∨ (0ℚ ℚ.<? (x ℚ.+ y)) (0ℚ ℚ.<? x) (0ℚ ℚ.<? y)
    (λ 0<x → subst (ℚ._< x ℚ.+ y) (+-identityʳ 0ℚ) (+-mono-<-≤ 0<x 0≤y))
    (λ 0<y → subst (ℚ._< x ℚ.+ y) (+-identityʳ 0ℚ) (+-mono-≤-< 0≤x 0<y))
    (λ ¬0<x ¬0<y → <-irrefl (sym (trans (cong₂ ℚ._+_ (≮⇒≡0 0≤x ¬0<x) (≮⇒≡0 0≤y ¬0<y))
                                        (+-identityʳ 0ℚ))))

  pos-* : {x y : ℚ} → 0ℚ ℚ.≤ x → 0ℚ ℚ.≤ y
        → does (0ℚ ℚ.<? (x ℚ.* y)) ≡ does (0ℚ ℚ.<? x) ∧ does (0ℚ ℚ.<? y)
  pos-* {x} {y} 0≤x 0≤y = dec-∧ (0ℚ ℚ.<? (x ℚ.* y)) (0ℚ ℚ.<? x) (0ℚ ℚ.<? y)
    (λ 0<x 0<y → positive⁻¹ (x ℚ.* y)
                   {{pos*pos⇒pos x {{ℚ.positive 0<x}} y {{ℚ.positive 0<y}}}})
    (λ ¬0<x → <-irrefl (sym (trans (cong (ℚ._* y) (≮⇒≡0 0≤x ¬0<x)) (*-zeroˡ y))))
    (λ ¬0<y → <-irrefl (sym (trans (cong (x ℚ.*_) (≮⇒≡0 0≤y ¬0<y)) (*-zeroʳ x))))

------------------------------------------------------------------------
-- The support map.

suppL : List (ℚ × A) → List A
suppL []             = []
suppL ((q , a) ∷ xs) = if does (0ℚ ℚ.<? q) then a ∷ suppL xs else suppL xs

supp : Dist-ℚ A → List A
supp μ = suppL (NE.toList (entries μ))

suppL-cons-pos : (q : ℚ) → 0ℚ ℚ.< q → (a : A) (xs : List (ℚ × A))
               → suppL ((q , a) ∷ xs) ≡ a ∷ suppL xs
suppL-cons-pos q 0<q a xs =
  cong (λ b → if b then a ∷ suppL xs else suppL xs) (dec-true (0ℚ ℚ.<? q) 0<q)

private
  lookup-L-nonneg : (xs : List (ℚ × A)) → NonNeg-L xs → (F : A → ℚ) → (∀ a → 0ℚ ℚ.≤ F a)
                  → 0ℚ ℚ.≤ Lin.lookup-L xs F
  lookup-L-nonneg []             All.[]         F 0≤F = ≤-refl
  lookup-L-nonneg ((q , a) ∷ xs) (0≤q All.∷ ws) F 0≤F =
    0≤+ (0≤* 0≤q (0≤F a)) (lookup-L-nonneg xs ws F 0≤F)

lookupᴰℚ-nonneg : (μ : DistData A) → NonNegᴰ μ → (F : A → ℚ) → (∀ a → 0ℚ ℚ.≤ F a)
                → 0ℚ ℚ.≤ lookupᴰℚ μ F
lookupᴰℚ-nonneg (h NE.∷ t) = lookup-L-nonneg (h ∷ t)

private
  if-∷ : (P : A → Bool) (b : Bool) (x : A) (l : List A)
       → (b ∧ P x) ∨ any P l ≡ any P (if b then x ∷ l else l)
  if-∷ P true  x l = refl
  if-∷ P false x l = refl

  supp-pos-L : (xs : List (ℚ × A)) → NonNeg-L xs → (F : A → ℚ) → (∀ a → 0ℚ ℚ.≤ F a)
             → does (0ℚ ℚ.<? Lin.lookup-L xs F)
             ≡ any (λ a → does (0ℚ ℚ.<? F a)) (suppL xs)
  supp-pos-L []             All.[]         F 0≤F = dec-false (0ℚ ℚ.<? 0ℚ) (<-irrefl refl)
  supp-pos-L ((q , a) ∷ xs) (0≤q All.∷ ws) F 0≤F = begin
    does (0ℚ ℚ.<? (q ℚ.* F a ℚ.+ Lin.lookup-L xs F))
      ≡⟨ pos-+ (0≤* 0≤q (0≤F a)) (lookup-L-nonneg xs ws F 0≤F) ⟩
    does (0ℚ ℚ.<? (q ℚ.* F a)) ∨ does (0ℚ ℚ.<? Lin.lookup-L xs F)
      ≡⟨ cong₂ _∨_ (pos-* 0≤q (0≤F a)) (supp-pos-L xs ws F 0≤F) ⟩
    (does (0ℚ ℚ.<? q) ∧ does (0ℚ ℚ.<? F a)) ∨ any (λ a′ → does (0ℚ ℚ.<? F a′)) (suppL xs)
      ≡⟨ if-∷ (λ a′ → does (0ℚ ℚ.<? F a′)) (does (0ℚ ℚ.<? q)) a (suppL xs) ⟩
    any (λ a′ → does (0ℚ ℚ.<? F a′)) (suppL ((q , a) ∷ xs)) ∎
    where open ≡-Reasoning

-- For a NON-NEGATIVE test, the integral is positive exactly when the test is
-- positive somewhere on the support.  Everything below is a corollary.
supp-pos : (μ : DistData A) → NonNegᴰ μ → (F : A → ℚ) → (∀ a → 0ℚ ℚ.≤ F a)
         → does (0ℚ ℚ.<? lookupᴰℚ μ F) ≡ any (λ a → does (0ℚ ℚ.<? F a)) (suppL (NE.toList μ))
supp-pos (h NE.∷ t) = supp-pos-L (h ∷ t)

private
  χ : (A → Bool) → A → ℚ
  χ P a = if P a then 1ℚ else 0ℚ

  0≤χ : (P : A → Bool) (a : A) → 0ℚ ℚ.≤ χ P a
  0≤χ P a with P a
  ... | true  = 0≤1ℚ
  ... | false = ≤-refl

  χ-pos : (P : A → Bool) (a : A) → does (0ℚ ℚ.<? χ P a) ≡ P a
  χ-pos P a with P a
  ... | true  = dec-true (0ℚ ℚ.<? 1ℚ) 0<1ℚ
  ... | false = dec-false (0ℚ ℚ.<? 0ℚ) (<-irrefl refl)

------------------------------------------------------------------------
-- `supp` is a setoid monad morphism `Dist-ℚ ⇒ 𝒫`.

supp-cong : {μ ν : Dist-ℚ A} → μ ≈Mℚ ν → supp μ ≈𝒫 supp ν
supp-cong {μ = μ} {ν} e P = begin
  any P (supp μ)
    ≡⟨ any-cong (λ a → sym (χ-pos P a)) (supp μ) ⟩
  any (λ a → does (0ℚ ℚ.<? χ P a)) (supp μ)
    ≡⟨ sym (supp-pos (entries μ) (weights-nn μ) (χ P) (0≤χ P)) ⟩
  does (0ℚ ℚ.<? lookupᴰℚ (entries μ) (χ P))
    ≡⟨ cong (λ x → does (0ℚ ℚ.<? x)) (e (χ P)) ⟩
  does (0ℚ ℚ.<? lookupᴰℚ (entries ν) (χ P))
    ≡⟨ supp-pos (entries ν) (weights-nn ν) (χ P) (0≤χ P) ⟩
  any (λ a → does (0ℚ ℚ.<? χ P a)) (supp ν)
    ≡⟨ any-cong (χ-pos P) (supp ν) ⟩
  any P (supp ν) ∎
  where open ≡-Reasoning

supp-return-≡ : (a : A) → supp (return-ℚ a) ≡ a ∷ []
supp-return-≡ a = suppL-cons-pos 1ℚ 0<1ℚ a []

supp-return : (a : A) → supp (return-ℚ a) ≈𝒫 (a ∷ [])
supp-return a P = cong (any P) (supp-return-≡ a)

supp-bind : (μ : Dist-ℚ A) (k : A → Dist-ℚ B)
          → supp (μ >>=ᴹ k) ≈𝒫 concatMap (λ a → supp (k a)) (supp μ)
supp-bind μ k P = begin
  any P (supp (μ >>=ᴹ k))
    ≡⟨ any-cong (λ b → sym (χ-pos P b)) (supp (μ >>=ᴹ k)) ⟩
  any (λ b → does (0ℚ ℚ.<? χ P b)) (supp (μ >>=ᴹ k))
    ≡⟨ sym (supp-pos (entries (μ >>=ᴹ k)) (weights-nn (μ >>=ᴹ k)) (χ P) (0≤χ P)) ⟩
  does (0ℚ ℚ.<? lookupᴰℚ (entries μ >>=ᴰ (entries ∘ k)) (χ P))
    ≡⟨ cong (λ x → does (0ℚ ℚ.<? x)) (lookupᴰℚ-bind (entries μ) (entries ∘ k) (χ P)) ⟩
  does (0ℚ ℚ.<? lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries (k a)) (χ P)))
    ≡⟨ supp-pos (entries μ) (weights-nn μ) _
         (λ a → lookupᴰℚ-nonneg (entries (k a)) (weights-nn (k a)) (χ P) (0≤χ P)) ⟩
  any (λ a → does (0ℚ ℚ.<? lookupᴰℚ (entries (k a)) (χ P))) (supp μ)
    ≡⟨ any-cong (λ a → trans (supp-pos (entries (k a)) (weights-nn (k a)) (χ P) (0≤χ P))
                             (any-cong (χ-pos P) (supp (k a)))) (supp μ) ⟩
  any (λ a → any P (supp (k a))) (supp μ)
    ≡⟨ sym (any-concatMap P (λ a → supp (k a)) (supp μ)) ⟩
  any P (concatMap (λ a → supp (k a)) (supp μ)) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The partial layer: a computation that certainly diverges has no
-- possible outcome.

supp⊥ : Dist⊥ A → List A
supp⊥ μ = concatMap fromMaybe (supp μ)

supp⊥-cong : {μ ν : Dist⊥ A} → μ ≈Mℚ ν → supp⊥ μ ≈𝒫 supp⊥ ν
supp⊥-cong {μ = μ} {ν} e P = trans (any-concatMap P fromMaybe (supp μ))
  (trans (supp-cong {μ = μ} {ν} e (λ ma → any P (fromMaybe ma)))
         (sym (any-concatMap P fromMaybe (supp ν))))

supp⊥-return : (a : A) → supp⊥ (return⊥ a) ≈𝒫 (a ∷ [])
supp⊥-return a P = cong (λ l → any P (concatMap fromMaybe l)) (supp-return-≡ (just a))

supp⊥-nothing : supp⊥ {A = A} (return-ℚ nothing) ≡ []
supp⊥-nothing = cong (concatMap fromMaybe) (supp-return-≡ nothing)

supp⊥-bind : (μ : Dist⊥ A) (k : A → Dist⊥ B)
           → supp⊥ (μ >>=⊥ k) ≈𝒫 concatMap (λ a → supp⊥ (k a)) (supp⊥ μ)
supp⊥-bind {A = A} μ k P = begin
  any P (concatMap fromMaybe (supp (μ >>=ᴹ kmaybe k)))
    ≡⟨ any-concatMap P fromMaybe (supp (μ >>=ᴹ kmaybe k)) ⟩
  any (λ mb → any P (fromMaybe mb)) (supp (μ >>=ᴹ kmaybe k))
    ≡⟨ supp-bind μ (kmaybe k) (λ mb → any P (fromMaybe mb)) ⟩
  any (λ mb → any P (fromMaybe mb)) (concatMap (λ ma → supp (kmaybe k ma)) (supp μ))
    ≡⟨ any-concatMap (λ mb → any P (fromMaybe mb)) (λ ma → supp (kmaybe k ma)) (supp μ) ⟩
  any (λ ma → any (λ mb → any P (fromMaybe mb)) (supp (kmaybe k ma))) (supp μ)
    ≡⟨ any-cong (λ ma → trans (sym (any-concatMap P fromMaybe (supp (kmaybe k ma)))) (step ma))
                (supp μ) ⟩
  any (λ ma → any (λ a → any P (supp⊥ (k a))) (fromMaybe ma)) (supp μ)
    ≡⟨ sym (any-concatMap (λ a → any P (supp⊥ (k a))) fromMaybe (supp μ)) ⟩
  any (λ a → any P (supp⊥ (k a))) (concatMap fromMaybe (supp μ))
    ≡⟨ sym (any-concatMap P (λ a → supp⊥ (k a)) (supp⊥ μ)) ⟩
  any P (concatMap (λ a → supp⊥ (k a)) (supp⊥ μ)) ∎
  where
    open ≡-Reasoning
    step : (ma : Maybe A)
         → any P (supp⊥ (kmaybe k ma)) ≡ any (λ a → any P (supp⊥ (k a))) (fromMaybe ma)
    step (just a) = sym (∨-identityʳ (any P (supp⊥ (k a))))
    step nothing  = cong (any P) supp⊥-nothing

------------------------------------------------------------------------
-- The abstraction forgets security: a biased one-time pad.

¾ : ℚ
¾ = (+ 3) ℚ./ 4

0<¾ : 0ℚ ℚ.< ¾
0<¾ = toWitness {a? = 0ℚ ℚ.<? ¾} tt

0<¼ : 0ℚ ℚ.< (1ℚ ℚ.- ¾)
0<¼ = toWitness {a? = 0ℚ ℚ.<? (1ℚ ℚ.- ¾)} tt

0≤¾ : 0ℚ ℚ.≤ ¾
0≤¾ = <⇒≤ 0<¾

0≤¼ : 0ℚ ℚ.≤ (1ℚ ℚ.- ¾)
0≤¼ = <⇒≤ 0<¼

-- The one-time-pad ciphertext of `m` under a key that is `true` with
-- probability `q`:  `enc k m = k xor m`.
pad : (q : ℚ) → 0ℚ ℚ.≤ q → 0ℚ ℚ.≤ (1ℚ ℚ.- q) → Bool → Dist-ℚ Bool
pad q 0≤q 0≤1-q m = mk-Dist ((q , not m) NE.∷ (1ℚ ℚ.- q , m) ∷ [])
  (trans (cong (q ℚ.+_) (+-identityʳ (1ℚ ℚ.- q)))
         (trans (+-comm q (1ℚ ℚ.- q)) (−-+-cancel 1ℚ q)))
  (0≤q All.∷ 0≤1-q All.∷ All.[])

pad-supp : (q : ℚ) (0≤q : 0ℚ ℚ.≤ q) (0≤1-q : 0ℚ ℚ.≤ (1ℚ ℚ.- q))
         → 0ℚ ℚ.< q → 0ℚ ℚ.< (1ℚ ℚ.- q) → (m : Bool)
         → supp (pad q 0≤q 0≤1-q m) ≡ not m ∷ m ∷ []
pad-supp q 0≤q 0≤1-q 0<q 0<1-q m =
  trans (suppL-cons-pos q 0<q (not m) ((1ℚ ℚ.- q , m) ∷ []))
        (cong (not m ∷_) (suppL-cons-pos (1ℚ ℚ.- q) 0<1-q m []))

-- Possibilistically the biased pad is PERFECTLY secure: whatever the message,
-- the support of the ciphertext is the whole ciphertext space.
pad-supp-perfect : (m : Bool) → supp (pad ¾ 0≤¾ 0≤¼ m) ≈𝒫 (true ∷ false ∷ [])
pad-supp-perfect true  P = trans (cong (any P) (pad-supp ¾ 0≤¾ 0≤¼ 0<¾ 0<¼ true))
  (trans (cong (P false ∨_) (∨-identityʳ (P true)))
         (trans (∨-comm (P false) (P true)) (cong (P true ∨_) (sym (∨-identityʳ (P false))))))
pad-supp-perfect false P = cong (any P) (pad-supp ¾ 0≤¾ 0≤¼ 0<¾ 0<¼ false)

-- …yet the two ciphertext distributions differ, so `supp` does not reflect
-- security: the possibilistic abstraction exists and is lossy.
pad-not-perfect : ¬ (pad ¾ 0≤¾ 0≤¼ true ≈Mℚ pad ¾ 0≤¾ 0≤¼ false)
pad-not-perfect e with e (χ id)
... | ()

------------------------------------------------------------------------
-- Closeness does not control the support.

Close : ℚ → Dist-ℚ A → Dist-ℚ A → Type _
Close {A = A} ε μ ν = (P : A → ℚ) → (∀ a → 0ℚ ℚ.≤ P a) → (∀ a → P a ℚ.≤ 1ℚ)
                    → ℚ.∣ lookupᴰℚ (entries μ) P ℚ.- lookupᴰℚ (entries ν) P ∣ ℚ.≤ ε

private
  diff-eq : ∀ e t f c z
          → (e ℚ.* t ℚ.+ ((c ℚ.- e) ℚ.* f ℚ.+ z)) ℚ.- (c ℚ.* f ℚ.+ z) ≡ e ℚ.* (t ℚ.- f)
  diff-eq = solve 5 (λ e t f c z →
    (e :* t :+ ((c :- e) :* f :+ z)) :- (c :* f :+ z) := e :* (t :- f)) refl
    where open +-*-Solver

-- However small ε, `ε·true + (1-ε)·false` is ε-close to the point mass at
-- `false` and still has a strictly larger support: a vanishing-distance
-- kernel has no possibilistic shadow.
close-supp-differs :
    (ε : ℚ) → 0ℚ ℚ.< ε → ε ℚ.≤ 1ℚ
  → Σ[ μ ∈ Dist-ℚ Bool ] Σ[ ν ∈ Dist-ℚ Bool ] Close ε μ ν × ¬ (supp μ ≈𝒫 supp ν)
close-supp-differs ε 0<ε ε≤1 = pad ε 0≤ε 0≤1-ε false , return-ℚ false , close , differ
  where
    0≤ε : 0ℚ ℚ.≤ ε
    0≤ε = <⇒≤ 0<ε

    0≤1-ε : 0ℚ ℚ.≤ (1ℚ ℚ.- ε)
    0≤1-ε = subst (ℚ._≤ 1ℚ ℚ.- ε) (+-inverseʳ ε) (+-mono-≤ ε≤1 ≤-refl)

    close : Close ε (pad ε 0≤ε 0≤1-ε false) (return-ℚ false)
    close P 0≤P P≤1 = ≤-trans (≤-reflexive shape) bound
      where
        shape : ℚ.∣ lookupᴰℚ (entries (pad ε 0≤ε 0≤1-ε false)) P
                    ℚ.- lookupᴰℚ (entries (return-ℚ false)) P ∣
              ≡ ε ℚ.* ℚ.∣ P true ℚ.- P false ∣
        shape = trans (cong ℚ.∣_∣ (diff-eq ε (P true) (P false) 1ℚ 0ℚ))
          (trans (∣p*q∣≡∣p∣*∣q∣ ε (P true ℚ.- P false))
                 (cong (ℚ._* ℚ.∣ P true ℚ.- P false ∣) (0≤p⇒∣p∣≡p 0≤ε)))

        bound : ε ℚ.* ℚ.∣ P true ℚ.- P false ∣ ℚ.≤ ε
        bound = ≤-trans
          (*-monoˡ-≤-nonNeg ε {{ℚ.nonNegative 0≤ε}}
            (∣diff∣≤1 (0≤P true) (P≤1 true) (0≤P false) (P≤1 false)))
          (≤-reflexive (*-identityʳ ε))

    head-true : any id (supp (pad ε 0≤ε 0≤1-ε false)) ≡ true
    head-true = cong (any id) (suppL-cons-pos ε 0<ε true ((1ℚ ℚ.- ε , false) ∷ []))

    tail-false : any id (supp (return-ℚ false)) ≡ false
    tail-false = cong (any id) (supp-return-≡ false)

    differ : ¬ (supp (pad ε 0≤ε 0≤1-ε false) ≈𝒫 supp (return-ℚ false))
    differ e with trans (sym head-true) (trans (e id) tail-false)
    ... | ()

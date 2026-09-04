{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite rational sub-distribution as a coin tree — the link between the two
-- probability carriers `Dp`'s header asserts exists.
--
-- `Dₚ`'s step is a single biased coin (see its header), so a `Dist⊥` — a
-- weighted list over `Maybe A` — enters the delay monad as a right-nested
-- cascade of CONDITIONAL coins: at the entry `(w , x)` the coin is
-- `(w/M , R/M)` for `M` the mass of the list from that entry on and `R` that of
-- the rest, so the two weights sum to one on the nose and `choiceₚ`'s invariants
-- are met with no renormalization of the list itself.  The recursion is
-- structural on the list and the coin's branches are arguments, so nothing
-- corecursive is mixed with it.
--
-- `Dist-ℚ`'s non-negativity is spent twice: it makes the two conditional weights
-- non-negative, and it makes a suffix of total mass zero — the one place the
-- normalization is undefined — carry no mass at all, so `botₚ` is exact there
-- rather than merely convenient.
--
-- `nothing` becomes `botₚ` and not a value, which is what makes the agreement
-- EXACT: `cum` never counts divergence and `E⊥` never counts the sink.  Past
-- the cascade's own depth `cum` is constant at the partial expectation
-- (`embed-cum`), which is the shape `Protocol.Machine.PrAgree` compares.

open import Algebra using (CommutativeRing)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base as ℕ using (ℕ; suc)
open import Data.Nat.Properties using (m≤n+m)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; 1/_; positive; >-nonZero)
open import Data.Rational.Properties as ℚP using
  ( *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+; *-identityʳ; *-identityˡ
  ; *-inverseʳ; *-zeroˡ; +-identityˡ; +-identityʳ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤
  ; 1/pos⇒pos; positive⁻¹; <⇒≤; ≤-antisym; ≤-refl; ≤-reflexive; ≤-trans; ≮⇒≥; _<?_ )
open import Data.Rational.Properties.Ext using (0≤*)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E⊥; maybeℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (Dist⊥; mass-L-toList)
open import ProbabilisticLogic.Dp

import Data.List.NonEmpty as NE
import ProbabilisticLogic.Distribution.Linearity as Linearity

module ProbabilisticLogic.Dp.Embed where

private
  -- The same instantiation as `RationalDist`'s own private `Lin`, so
  -- `Lin.lookup-L` below IS the function `lookupᴰℚ` — hence `E⊥` — is built from.
  module Lin = Linearity (CommutativeRing.commutativeSemiring ℚP.+-*-commutativeRing)

private variable
  ℓ : Level
  A : Set ℓ

------------------------------------------------------------------------
-- The conditional weight

private
  recip : {M : ℚ} → 0ℚ ℚ.< M → ℚ
  recip {M} 0<M = (1/ M) ⦃ >-nonZero 0<M ⦄

  0≤recip : {M : ℚ} (0<M : 0ℚ ℚ.< M) → 0ℚ ℚ.≤ recip 0<M
  0≤recip {M} 0<M = <⇒≤ (positive⁻¹ (recip 0<M) ⦃ 1/pos⇒pos M ⦃ positive 0<M ⦄ ⦄)

  -- An entry's and its suffix's conditional weights sum to one.
  cond-1 : (w R : ℚ) (0<M : 0ℚ ℚ.< w ℚ.+ R)
         → w ℚ.* recip 0<M ℚ.+ R ℚ.* recip 0<M ≡ 1ℚ
  cond-1 w R 0<M = trans (sym (*-distribʳ-+ (recip 0<M) w R))
                         (*-inverseʳ (w ℚ.+ R) ⦃ >-nonZero 0<M ⦄)

  -- …and multiplying by the total mass undoes the normalization.
  cond-cancel : (M w : ℚ) (0<M : 0ℚ ℚ.< M) → M ℚ.* (w ℚ.* recip 0<M) ≡ w
  cond-cancel M w 0<M = trans (sym (*-assoc M w (recip 0<M)))
    (trans (cong (ℚ._* recip 0<M) (*-comm M w))
      (trans (*-assoc w M (recip 0<M))
        (trans (cong (w ℚ.*_) (*-inverseʳ M ⦃ >-nonZero 0<M ⦄)) (*-identityʳ w))))

------------------------------------------------------------------------
-- A zero-mass suffix contributes nothing

private
  nn-mass : (xs : List (ℚ × A)) → NonNeg-L xs → 0ℚ ℚ.≤ mass-L xs
  nn-mass []             _  = ≤-refl
  nn-mass ((w , _) ∷ xs) nn = subst (ℚ._≤ w ℚ.+ mass-L xs) (+-identityʳ 0ℚ)
    (+-mono-≤ (All.head nn) (nn-mass xs (All.tail nn)))

  zero-split : {w R : ℚ} → 0ℚ ℚ.≤ w → 0ℚ ℚ.≤ R → w ℚ.+ R ≡ 0ℚ → w ≡ 0ℚ × R ≡ 0ℚ
  zero-split {w} {R} 0≤w 0≤R eq
    =   ≤-antisym (subst (w ℚ.≤_) eq
          (subst (ℚ._≤ w ℚ.+ R) (+-identityʳ w) (+-monoʳ-≤ w 0≤R))) 0≤w
    ,   ≤-antisym (subst (R ℚ.≤_) eq
          (subst (ℚ._≤ w ℚ.+ R) (+-identityˡ R) (+-monoˡ-≤ R 0≤w))) 0≤R

  mass0⇒lookup0 : (xs : List (ℚ × A)) → NonNeg-L xs → mass-L xs ≡ 0ℚ
                → (f : A → ℚ) → Lin.lookup-L xs f ≡ 0ℚ
  mass0⇒lookup0 []             _  _  f = refl
  mass0⇒lookup0 ((w , x) ∷ xs) nn eq f =
    let w≡0 , R≡0 = zero-split (All.head nn) (nn-mass xs (All.tail nn)) eq
    in trans (cong₂ ℚ._+_ (trans (cong (ℚ._* f x) w≡0) (*-zeroˡ (f x)))
                          (mass0⇒lookup0 xs (All.tail nn) R≡0 f))
             (+-identityʳ 0ℚ)

------------------------------------------------------------------------
-- The cascade

leafOf : Maybe A → Dₚ A
leafOf (just p) = returnₚ p
leafOf nothing  = botₚ

leafOf-cum : (x : Maybe A) (n : ℕ) (P : A → ℚ) → cum (suc n) (leafOf x) P ≡ maybeℚ P x
leafOf-cum (just p) n P = returnₚ-cum n p P
leafOf-cum nothing  n P = botₚ-cum (suc n) P

private
  -- One node: the coin at the conditional weights, its two branches this
  -- entry's leaf and the rest of the cascade.  Where the total mass is zero
  -- there is no coin to build and no mass to carry either.
  node : (w R : ℚ) → 0ℚ ℚ.≤ w → 0ℚ ℚ.≤ R → Dec (0ℚ ℚ.< w ℚ.+ R)
       → Dₚ A → Dₚ A → Dₚ A
  node w R 0≤w 0≤R (yes 0<M) l r =
    choiceₚ (w ℚ.* recip 0<M) (R ℚ.* recip 0<M)
            (0≤* 0≤w (0≤recip 0<M)) (0≤* 0≤R (0≤recip 0<M)) (cond-1 w R 0<M) l r
  node w R 0≤w 0≤R (no _)    l r = botₚ

  -- Scaled by the total mass, a node's cumulative mass is the unnormalized
  -- two-term sum — which is what makes the induction below divisor-free.
  node-cum : (w R : ℚ) (0≤w : 0ℚ ℚ.≤ w) (0≤R : 0ℚ ℚ.≤ R) (d : Dec (0ℚ ℚ.< w ℚ.+ R))
             (l r : Dₚ A) (n : ℕ) (P : A → ℚ)
           → (w ℚ.+ R) ℚ.* cum (suc n) (node w R 0≤w 0≤R d l r) P
             ≡ w ℚ.* cum n l P ℚ.+ R ℚ.* cum n r P
  node-cum w R 0≤w 0≤R (yes 0<M) l r n P =
    trans (*-distribˡ-+ (w ℚ.+ R) _ _)
          (cong₂ ℚ._+_ (pull w (cum n l P)) (pull R (cum n r P)))
    where
    pull : (u x : ℚ) → (w ℚ.+ R) ℚ.* (u ℚ.* recip 0<M ℚ.* x) ≡ u ℚ.* x
    pull u x = trans (sym (*-assoc (w ℚ.+ R) (u ℚ.* recip 0<M) x))
                     (cong (ℚ._* x) (cond-cancel (w ℚ.+ R) u 0<M))
  node-cum w R 0≤w 0≤R (no ¬0<M) l r n P =
    trans (cong₂ ℚ._*_ M≡0 (botₚ-cum (suc n) P)) (trans (*-zeroˡ 0ℚ) (sym rhs≡0))
    where
    M≡0 : w ℚ.+ R ≡ 0ℚ
    M≡0 = ≤-antisym (≮⇒≥ ¬0<M)
      (subst (ℚ._≤ w ℚ.+ R) (+-identityʳ 0ℚ) (+-mono-≤ 0≤w 0≤R))

    rhs≡0 : w ℚ.* cum n l P ℚ.+ R ℚ.* cum n r P ≡ 0ℚ
    rhs≡0 = let w≡0 , R≡0 = zero-split 0≤w 0≤R M≡0
            in trans (cong₂ ℚ._+_ (trans (cong (ℚ._* cum n l P) w≡0) (*-zeroˡ (cum n l P)))
                                  (trans (cong (ℚ._* cum n r P) R≡0) (*-zeroˡ (cum n r P))))
                     (+-identityʳ 0ℚ)

cascade : (xs : List (ℚ × Maybe A)) → NonNeg-L xs → Dₚ A
cascade []             nn = botₚ
cascade ((w , x) ∷ ys) nn =
  node w (mass-L ys) (All.head nn) (nn-mass ys (All.tail nn))
       (0ℚ <? w ℚ.+ mass-L ys) (leafOf x) (cascade ys (All.tail nn))

-- One step per entry plus one for the leaf reaches every value the list holds,
-- and the statement is scaled by the mass so that no division appears in it.
cascade-cum : (xs : List (ℚ × Maybe A)) (nn : NonNeg-L xs) (m : ℕ) (P : A → ℚ)
            → mass-L xs ℚ.* cum (suc (length xs) ℕ.+ m) (cascade xs nn) P
              ≡ Lin.lookup-L xs (maybeℚ P)
cascade-cum []             nn m P = *-zeroˡ (cum (suc m) (cascade [] nn) P)
cascade-cum ((w , x) ∷ ys) nn m P =
  trans (node-cum w (mass-L ys) (All.head nn) (nn-mass ys (All.tail nn))
                  (0ℚ <? w ℚ.+ mass-L ys) (leafOf x) (cascade ys (All.tail nn))
                  (suc (length ys) ℕ.+ m) P)
        (cong₂ ℚ._+_ (cong (w ℚ.*_) (leafOf-cum x (length ys ℕ.+ m) P))
                     (cascade-cum ys (All.tail nn) m P))

------------------------------------------------------------------------
-- The embedding

embed : Dist⊥ A → Dₚ A
embed μ = cascade (NE.toList (entries μ)) (weights-nn μ)

-- Past the cascade's depth the coin tree's cumulative mass IS the partial
-- expectation.  Exact, and at every larger budget — the shape `PrAgree` wants.
embed-cum : (μ : Dist⊥ A) (P : A → ℚ)
          → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n ℕ.+ m) (embed μ) P ≡ E⊥ μ P)
embed-cum μ P = n , step
  where
  xs : List (ℚ × Maybe _)
  xs = NE.toList (entries μ)

  n : ℕ
  n = suc (length xs)

  mass≡1 : mass-L xs ≡ 1ℚ
  mass≡1 = trans (mass-L-toList (entries μ)) (mass-1 μ)

  step : (m : ℕ) → cum (n ℕ.+ m) (embed μ) P ≡ E⊥ μ P
  step m = trans (sym (*-identityˡ (cum (n ℕ.+ m) (embed μ) P)))
                 (trans (cong (ℚ._* cum (n ℕ.+ m) (embed μ) P) (sym mass≡1))
                        (cascade-cum xs (weights-nn μ) m P))

-- Both cumulative masses are eventually constant, so a `Dist⊥` equality no test
-- detects is invisible to the coin trees as well.
embed-cong : (μ ν : Dist⊥ A) → μ ≈Mℚ ν → embed μ ≈ₚ embed ν
embed-cong μ ν e = dom μ ν (λ P → e (maybeℚ P)) , dom ν μ (λ P → sym (e (maybeℚ P)))
  where
  dom : (ρ σ : Dist⊥ A) → ((P : A → ℚ) → E⊥ ρ P ≡ E⊥ σ P) → embed ρ ≼ₚ embed σ
  dom ρ σ eq P nn k =
    let nρ , hρ = embed-cum ρ P
        nσ , hσ = embed-cum σ P
    in nσ ℕ.+ 0
     , ≤-trans (cum-mono (m≤n+m k nρ) (embed ρ) P nn)
               (≤-reflexive (trans (hρ k) (trans (eq P) (sym (hσ 0)))))

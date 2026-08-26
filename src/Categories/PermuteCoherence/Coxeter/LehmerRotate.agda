{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Lehmer-peel machinery for `insert-thm`, part 2: the rotation algebra
-- and the `canonW`-peel lemmas that turn the staircase identities of
-- `LehmerStaircase` into a direct proof of the Insertion Lemma.
--
-- The one clean observation the module rests on:
--
--   * the pointwise `remove`/`rotate` range computation the plan feared is
--     never needed as a raw Fin computation.  The one FinBij identity we
--     use (`rot-comp`, a composition of two rotations) is obtained *for
--     free* as the SOUNDNESS (`~ʷ⇒≈`) shadow of the very staircase word
--     identity that closes the proof — see `wglue`/`rot-comp` below.
--
------------------------------------------------------------------------

module Categories.PermuteCoherence.Coxeter.LehmerRotate where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-trans; m≤n⇒m≤1+n; _≤?_; ≰⇒>; ≤-pred)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ≤pred[n])
open import Data.List.Base using (_∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Nullary using (yes; no)
import Data.Fin.Permutation as P
open P using (remove)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; cong₂; trans; subst; subst₂)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Coxeter.EvalSoundness as Snd
  using (cons-fb-functor-comp; swap-fb-natural)
open import Categories.PermuteCoherence.Coxeter.Word
open import Categories.PermuteCoherence.Coxeter.LehmerStaircase

private
  variable
    n N : ℕ

------------------------------------------------------------------------
-- 1. `canonW` of a `cons-fb X ∘ rotate-fb k`:  the peel is realised at
--    the word level as `liftW (canonW X) ++ rotateW k`.

canonW-cons-rotate : (X : FinBij (suc n) (suc n)) (k : Fin (suc (suc n)))
                   → canonW (cons-fb X ∘-fb rotate-fb k)
                     ~ʷ (liftW (canonW X) ++ rotateW k)
canonW-cons-rotate {n} X k =
  subst (λ z → canonW Y ~ʷ (liftW (canonW X) ++ rotateW z)) mY≡k
        (++c-r (rotateW mY) (lift~ rec))
  where
  Y  = cons-fb X ∘-fb rotate-fb k
  mY = Y P.⟨$⟩ˡ 0F

  mY≡k : mY ≡ k
  mY≡k = inv-rotate-fb-0 k

  resid = remove 0F (Y ∘-fb inv-fb (rotate-fb mY))

  -- Y ∘ ρ_mY⁻¹ ≈ cons-fb X  (with mY substituted to k, the ρ's cancel), and
  -- `remove 0F` of that lift is `X` again (`cons-fb-injective`, upstream in
  -- `Word`, shared with `remove-0-of-≈id`).
  resid≈X : resid ≈-fb X
  resid≈X = ≈-fb-trans {b = resid} {b′ = remove 0F (cons-fb X)} {b″ = X}
              (residual-pw-cong (Y ∘-fb inv-fb (rotate-fb mY)) (cons-fb X) collapse)
              (cons-fb-injective (P.lift₀-remove (cons-fb X) refl))
    where
    collapse : ∀ i → (Y ∘-fb inv-fb (rotate-fb mY)) P.⟨$⟩ʳ i ≡ cons-fb X P.⟨$⟩ʳ i
    collapse i =
      trans (cong (λ z → (Y ∘-fb inv-fb (rotate-fb z)) P.⟨$⟩ʳ i) mY≡k)
            (cong (cons-fb X P.⟨$⟩ʳ_) (P.inverseʳ (rotate-fb k)))

  rec : canonW resid ~ʷ canonW X
  rec = canonW-resp-≈ {b = resid} {b′ = X} resid≈X

------------------------------------------------------------------------
-- 2. Bridges: `rotateW`/`liftW` in terms of the staircase run `runF`.
--    (Bounds are irrelevant, so proofs are supplied ad libitum.)

liftW-runF : (s ℓ : ℕ) .(p : s + ℓ ≤ N) .(q : suc s + ℓ ≤ suc N)
           → liftW (runF {N} s ℓ p) ≡ runF {suc N} (suc s) ℓ q
liftW-runF s zero    p q = refl
liftW-runF {N} s (suc ℓ) p q =
  cong (fromℕ< (head< (suc s) ℓ q) ∷_) (liftW-runF (suc s) ℓ _ _)

rotateW-runF : (m : Fin (suc n)) .(p : toℕ m ≤ n)
             → rotateW m ≡ runF {n} 0 (toℕ m) p
rotateW-runF 0F           p = refl
rotateW-runF {suc n} (fsuc m) p =
  cong (0F ∷_)
    (trans (cong liftW (rotateW-runF {n} m (toℕ≤pred[n] m)))
           (liftW-runF {n} 0 (toℕ m) (toℕ≤pred[n] m) (s≤s (toℕ≤pred[n] m))))

------------------------------------------------------------------------
-- 3. The rotation-composition glue.
--
-- Given the two head-data `r`, `m` of a doubly-peeled bijection, the
-- dichotomy `toℕ m ≤? toℕ r` chooses replacement indices `r′`, `m′` and a
-- STAIRCASE WORD IDENTITY `wglue`.  Its `~ʷ⇒≈` shadow (`rot-comp`) is the
-- ONLY FinBij fact the crux needs — no pointwise `remove`/`punchOut`.

-- `rotateW x` as a base-0 run of its numeric value.  The run's bound is
-- irrelevant, so re-lengthing it is exactly the value equation's `refl`.
rotateW-val : (x : Fin (suc n)) (v : ℕ) → toℕ x ≡ v → .(bv : v ≤ n)
            → rotateW x ≡ runF {n} 0 v bv
rotateW-val x .(toℕ x) refl bv = rotateW-runF x bv

record Glue (r : Fin (suc (suc n))) (m : Fin (suc (suc (suc n)))) : Set where
  field
    r′    : Fin (suc (suc n))
    m′    : Fin (suc (suc (suc n)))
    wglue : (liftW (rotateW r′) ++ rotateW m′) ~ʷ (rotateW (fsuc r) ++ rotateW m)

mkGlue : (r : Fin (suc (suc n))) (m : Fin (suc (suc (suc n)))) → Glue r m
mkGlue {n} r m with toℕ m ≤? toℕ r
-- Branch B (r ≥ m): identity (B).
... | yes M≤a = record { r′ = r′ ; m′ = m′ ; wglue = wg }
  where
  a  = toℕ r
  M  = toℕ m
  ra : a ≤ suc n
  ra = toℕ≤pred[n] r
  r′ : Fin (suc (suc n))
  r′ = fromℕ< {M} {suc (suc n)} (s≤s (≤-trans M≤a ra))
  m′ : Fin (suc (suc (suc n)))
  m′ = fromℕ< {suc a} {suc (suc (suc n))} (s≤s (s≤s ra))
  lr′ : liftW (rotateW r′) ≡ runF {suc (suc n)} 1 M (s≤s (≤-trans M≤a ra))
  lr′ = trans (cong liftW (rotateW-val r′ M (toℕ-fromℕ< (s≤s (≤-trans M≤a ra)))
                                          (≤-trans M≤a ra)))
              (liftW-runF 0 M (≤-trans M≤a ra) (s≤s (≤-trans M≤a ra)))
  rm′ : rotateW m′ ≡ runF {suc (suc n)} 0 (suc a) (s≤s ra)
  rm′ = rotateW-val m′ (suc a) (toℕ-fromℕ< (s≤s (s≤s ra))) (s≤s ra)
  rfr : rotateW (fsuc r) ≡ runF {suc (suc n)} 0 (suc a) (s≤s ra)
  rfr = rotateW-val (fsuc r) (suc a) refl (s≤s ra)
  rmm : rotateW m ≡ runF {suc (suc n)} 0 M (m≤n⇒m≤1+n (≤-trans M≤a ra))
  rmm = rotateW-val m M refl (m≤n⇒m≤1+n (≤-trans M≤a ra))
  wg : (liftW (rotateW r′) ++ rotateW m′) ~ʷ (rotateW (fsuc r) ++ rotateW m)
  wg = subst₂ _~ʷ_ (sym (cong₂ _++_ lr′ rm′)) (sym (cong₂ _++_ rfr rmm))
                   (~sym (stairBW 0 M a M≤a (s≤s ra) _ _))
-- Branch A (r < m): identity (A); m = fsuc m₀ (m = 0F is absurd).
mkGlue {n} r 0F        | no  a≮ with () ← a≮ z≤n
mkGlue {n} r (fsuc m₀) | no  a≮ = record { r′ = r′ ; m′ = m′ ; wglue = wg }
  where
  a  = toℕ r
  M₀ = toℕ m₀
  ra : a ≤ suc n
  ra = toℕ≤pred[n] r
  a≤M₀ : a ≤ M₀
  a≤M₀ = ≤-pred (≰⇒> a≮)
  Mb : suc M₀ ≤ suc (suc n)
  Mb = toℕ≤pred[n] (fsuc m₀)
  r′ : Fin (suc (suc n))
  r′ = fromℕ< {M₀} {suc (suc n)} Mb
  m′ : Fin (suc (suc (suc n)))
  m′ = fromℕ< {a} {suc (suc (suc n))} (s≤s (m≤n⇒m≤1+n ra))
  lr′ : liftW (rotateW r′) ≡ runF {suc (suc n)} 1 M₀ (s≤s (≤-pred Mb))
  lr′ = trans (cong liftW (rotateW-val r′ M₀ (toℕ-fromℕ< Mb) (≤-pred Mb)))
              (liftW-runF 0 M₀ (≤-pred Mb) (s≤s (≤-pred Mb)))
  rm′ : rotateW m′ ≡ runF {suc (suc n)} 0 a (m≤n⇒m≤1+n ra)
  rm′ = rotateW-val m′ a (toℕ-fromℕ< (s≤s (m≤n⇒m≤1+n ra))) (m≤n⇒m≤1+n ra)
  rfr : rotateW (fsuc r) ≡ runF {suc (suc n)} 0 (suc a) (s≤s ra)
  rfr = rotateW-val (fsuc r) (suc a) refl (s≤s ra)
  rmm : rotateW (fsuc m₀) ≡ runF {suc (suc n)} 0 (suc M₀) Mb
  rmm = rotateW-val (fsuc m₀) (suc M₀) refl Mb
  wg : (liftW (rotateW r′) ++ rotateW m′) ~ʷ (rotateW (fsuc r) ++ rotateW (fsuc m₀))
  wg = subst₂ _~ʷ_ (sym (cong₂ _++_ lr′ rm′)) (sym (cong₂ _++_ rfr rmm))
                   (~sym (stairAW 0 M₀ a a≤M₀ Mb (s≤s ra) _ _))

-- The FinBij composition-of-rotations identity, obtained *for free* as
-- the `~ʷ⇒≈` shadow of `wglue` — no pointwise `remove`/`punchOut` at all.
rot-comp : (r : Fin (suc (suc n))) (m : Fin (suc (suc (suc n)))) (g : Glue r m)
         → (rotate-fb (fsuc r) ∘-fb rotate-fb m)
           ≈-fb (cons-fb (rotate-fb (Glue.r′ g)) ∘-fb rotate-fb (Glue.m′ g))
rot-comp r m g i =
  trans (sym (evalRHS i)) (trans (sym (~ʷ⇒≈ (Glue.wglue g) i)) (evalLHS i))
  where
  r′ = Glue.r′ g
  m′ = Glue.m′ g
  evalRHS : ∀ i → evalW (rotateW (fsuc r) ++ rotateW m) P.⟨$⟩ʳ i
                ≡ (rotate-fb (fsuc r) ∘-fb rotate-fb m) P.⟨$⟩ʳ i
  evalRHS i =
    trans (evalW-++ (rotateW (fsuc r)) (rotateW m) i)
          (∘-fb-cong {g = evalW (rotateW (fsuc r))} {g′ = rotate-fb (fsuc r)}
                     {f = evalW (rotateW m)} {f′ = rotate-fb m}
                     (rotateW-sound (fsuc r)) (rotateW-sound m) i)
  evalLHS : ∀ i → evalW (liftW (rotateW r′) ++ rotateW m′) P.⟨$⟩ʳ i
                ≡ (cons-fb (rotate-fb r′) ∘-fb rotate-fb m′) P.⟨$⟩ʳ i
  evalLHS i =
    trans (evalW-++ (liftW (rotateW r′)) (rotateW m′) i)
          (∘-fb-cong {g = evalW (liftW (rotateW r′))} {g′ = cons-fb (rotate-fb r′)}
                     {f = evalW (rotateW m′)} {f′ = rotate-fb m′}
                     (λ j → trans (eval-liftW (rotateW r′) j)
                                  (cons-fb-cong (rotateW-sound r′) j))
                     (rotateW-sound m′) i)

------------------------------------------------------------------------
-- 4. The crux factorisation:  `genFB 0F ∘ (cons² Z ∘ ρr ∘ ρm)` puts into
--    `cons X ∘ ρ` form via cons-functoriality, swap-naturality and the
--    definition `rotate-fb (fsuc r) = swap ∘ cons (rotate-fb r)`, closing
--    the double rotation with `rot-comp`.

factor : (Z : FinBij (suc n) (suc n)) (r : Fin (suc (suc n)))
         (m : Fin (suc (suc (suc n)))) (g : Glue r m)
       → (swap-fb (suc n) ∘-fb (cons-fb (cons-fb Z ∘-fb rotate-fb r) ∘-fb rotate-fb m))
         ≈-fb (cons-fb (cons-fb Z ∘-fb rotate-fb (Glue.r′ g)) ∘-fb rotate-fb (Glue.m′ g))
factor {n} Z r m g i =
  trans (trans (cong (swap-fb (suc n) P.⟨$⟩ʳ_) (cons-fb-functor-comp CZ ρr y))
               (swap-fb-natural Z z))
        (trans (cong (CCZ P.⟨$⟩ʳ_) (rot-comp r m g i))
               (sym (cons-fb-functor-comp CZ ρr′ w)))
  where
  CZ  = cons-fb Z
  CCZ = cons-fb CZ
  ρr  = rotate-fb r
  ρr′ = rotate-fb (Glue.r′ g)
  ρm′ = rotate-fb (Glue.m′ g)
  y = rotate-fb m P.⟨$⟩ʳ i
  z = cons-fb ρr P.⟨$⟩ʳ y
  w = ρm′ P.⟨$⟩ʳ i

------------------------------------------------------------------------
-- 5. The crux equation (`i = 0F` case of `insert-thm`), IH-free:
--    peel a doubly-`cons`ed / doubly-rotated bijection past `genFB 0F`.

-- LHS: fold via `factor` + `canonW-cons-rotate` (twice) + reshaping.
lhs-eq : (Z : FinBij (suc n) (suc n)) (r : Fin (suc (suc n)))
         (m : Fin (suc (suc (suc n)))) (g : Glue r m)
       → canonW (swap-fb (suc n) ∘-fb (cons-fb (cons-fb Z ∘-fb rotate-fb r)
                                        ∘-fb rotate-fb m))
         ~ʷ (liftW (liftW (canonW Z))
             ++ (liftW (rotateW (Glue.r′ g)) ++ rotateW (Glue.m′ g)))
lhs-eq {n} Z r m g =
  ~trans (canonW-resp-≈
            {b = swap-fb (suc n) ∘-fb (cons-fb (cons-fb Z ∘-fb rotate-fb r)
                                       ∘-fb rotate-fb m)}
            {b′ = cons-fb (cons-fb Z ∘-fb rotate-fb r′) ∘-fb rotate-fb m′}
            (factor Z r m g))
    (~trans (canonW-cons-rotate (cons-fb Z ∘-fb rotate-fb r′) m′)
      (subst ((liftW (canonW (cons-fb Z ∘-fb rotate-fb r′)) ++ rotateW m′) ~ʷ_)
             (++-assoc LZ L1 (rotateW m′))
             (++c-r (rotateW m′) step-in)))
  where
  r′ = Glue.r′ g
  m′ = Glue.m′ g
  LZ = liftW (liftW (canonW Z))
  L1 = liftW (rotateW r′)
  step-in : liftW (canonW (cons-fb Z ∘-fb rotate-fb r′)) ~ʷ (LZ ++ L1)
  step-in = subst (liftW (canonW (cons-fb Z ∘-fb rotate-fb r′)) ~ʷ_)
                  (liftW-++ (liftW (canonW Z)) (rotateW r′))
                  (lift~ (canonW-cons-rotate Z r′))

-- RHS: reshape then absorb the head `0F` via `comm₀`.
rhs-eq : (Z : FinBij (suc n) (suc n)) (r : Fin (suc (suc n)))
         (m : Fin (suc (suc (suc n))))
       → (0F ∷ (liftW (liftW (canonW Z) ++ rotateW r) ++ rotateW m))
         ~ʷ (liftW (liftW (canonW Z)) ++ (rotateW (fsuc r) ++ rotateW m))
rhs-eq {n} Z r m =
  subst (λ u → (0F ∷ (u ++ rotateW m)) ~ʷ (LZ ++ (rotateW (fsuc r) ++ rotateW m)))
        (sym (liftW-++ (liftW (canonW Z)) (rotateW r)))
  (subst (λ u → (0F ∷ u) ~ʷ (LZ ++ (rotateW (fsuc r) ++ rotateW m)))
         (sym (++-assoc LZ R1 (rotateW m)))
         (comm₀ (canonW Z) (R1 ++ rotateW m)))
  where
  LZ = liftW (liftW (canonW Z))
  R1 = liftW (rotateW r)

crux-core : (Z : FinBij (suc n) (suc n)) (r : Fin (suc (suc n)))
            (m : Fin (suc (suc (suc n)))) (g : Glue r m)
          → canonW (swap-fb (suc n) ∘-fb (cons-fb (cons-fb Z ∘-fb rotate-fb r)
                                          ∘-fb rotate-fb m))
            ~ʷ (0F ∷ (liftW (liftW (canonW Z) ++ rotateW r) ++ rotateW m))
crux-core {n} Z r m g =
  ~trans (lhs-eq Z r m g)
    (~trans (++c-l (liftW (liftW (canonW Z))) (Glue.wglue g))
            (~sym (rhs-eq Z r m)))

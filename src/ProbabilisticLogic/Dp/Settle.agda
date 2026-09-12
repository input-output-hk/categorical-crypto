{-# OPTIONS --safe --without-K --guardedness #-}

-- When a `Dₚ` computation has finished, and what it then scores.
--
-- `Settles n d ν` says two things: within `n` steps every branch of `d` has
-- produced a value or run into mass that never will (`Halts`), and at that
-- budget `d` scores exactly the partial distribution `ν` (`Dist⊥`, the
-- `Dₚ`-free reading `Dp`'s header calls the same thing).  `Dp.Stable` is the
-- second half at ONE test; the uniformity in the test is what makes the notion
-- closed under `_>>=ₚ_`, and a bind junction is where every transport out of
-- `Dₚ` has to pass.
--
-- Divergence is the `Null` disjunct rather than a missing case: `botₚ` never
-- halts and never scores, so a run that reaches it still settles — which is
-- what lets an off-protocol activation, whose machine image is `botₚ`, be
-- transported like any other.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (m+[n∸m]≡n; m∸n+n≡m; m≤n+m)
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-antisym; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

module ProbabilisticLogic.Dp.Settle where

-- Everything is at `Set`: `RationalDist.Expectation`'s algebra is, and the
-- machine layer this serves lives at `𝒱ₚ 0ℓ`.
private variable
  A B C : Set
  P : A → ℚ
  d : Dₚ A
  n m j : ℕ
  μ : Dist-ℚ A
  ν ν′ : Dist⊥ A

------------------------------------------------------------------------
-- Halting

-- Mass that never reaches a value, at any budget and any non-negative test.
Null : Dₚ A → Set
Null {A = A} d = (Q : A → ℚ) → NNF Q → (i : ℕ) → cum i d Q ≡ 0ℚ

-- Every branch has produced a value within `n` steps, or carries no mass.
mutual
  Halts : ℕ → Dₚ A → Set
  Halts zero    d = Null d
  Halts (suc n) d = Null d ⊎ ((c : Bool) → HaltsL n (br d c))

  HaltsL : ℕ → A ⊎ Dₚ A → Set
  HaltsL n (inj₁ p)  = ⊤
  HaltsL n (inj₂ d′) = Halts n d′

Null⇒Halts : (n : ℕ) (d : Dₚ A) → Null d → Halts n d
Null⇒Halts zero    d z = z
Null⇒Halts (suc n) d z = inj₁ z

mutual
  Halts-suc : (n : ℕ) (d : Dₚ A) → Halts n d → Halts (suc n) d
  Halts-suc zero    d z        = inj₁ z
  Halts-suc (suc n) d (inj₁ z) = inj₁ z
  Halts-suc (suc n) d (inj₂ h) = inj₂ λ c → HaltsL-suc n (br d c) (h c)

  HaltsL-suc : (n : ℕ) (x : A ⊎ Dₚ A) → HaltsL n x → HaltsL (suc n) x
  HaltsL-suc n (inj₁ p)  h = tt
  HaltsL-suc n (inj₂ d′) h = Halts-suc n d′ h

Halts-plus : (j n : ℕ) (d : Dₚ A) → Halts n d → Halts (j + n) d
Halts-plus zero    n d h = h
Halts-plus (suc j) n d h = Halts-suc (j + n) d (Halts-plus j n d h)

Halts-mono : n ≤ m → (d : Dₚ A) → Halts n d → Halts m d
Halts-mono {n = n} {m = m} le d h =
  subst (λ i → Halts i d) (m∸n+n≡m le) (Halts-plus (m ∸ n) n d h)

-- Past the halting budget the cumulative mass no longer moves.
mutual
  Halts-cum : (n j : ℕ) (d : Dₚ A) (Q : A → ℚ) → NNF Q → Halts n d
            → cum (n + j) d Q ≡ cum n d Q
  Halts-cum zero    j d Q nn z        = z Q nn j
  Halts-cum (suc n) j d Q nn (inj₁ z) = trans (z Q nn (suc n + j)) (sym (z Q nn (suc n)))
  Halts-cum (suc n) j d Q nn (inj₂ h) =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_)  (HaltsL-cum n j (br d true)  Q nn (h true)))
                (cong (wt d false ℚ.*_) (HaltsL-cum n j (br d false) Q nn (h false)))

  HaltsL-cum : (n j : ℕ) (x : A ⊎ Dₚ A) (Q : A → ℚ) → NNF Q → HaltsL n x
             → leafₚ (n + j) x Q ≡ leafₚ n x Q
  HaltsL-cum n j (inj₁ p)  Q nn h = refl
  HaltsL-cum n j (inj₂ d′) Q nn h = Halts-cum n j d′ Q nn h

-- A junction on mass that never lands is again mass that never lands.
Null-bind : (d : Dₚ A) (f : A → Dₚ B) → Null d → Null (d >>=ₚ f)
Null-bind d f z Q nn i = ≤-antisym
  (≤-trans (>>=ₚ-boundA i d f Q nn)
           (≤-reflexive (z (λ p → cum i (f p) Q) (λ p → cum-nn i (f p) Q nn) i)))
  (cum-nn i (d >>=ₚ f) Q nn)

------------------------------------------------------------------------
-- What `E⊥` makes of the three value-level rearrangements a run performs

Eⱼ : (μ : Dist-ℚ A) (Q : A → ℚ) → E⊥ (Dmap just μ) Q ≡ E μ Q
Eⱼ μ Q = lookupᴰℚ-Dmap just μ (maybeℚ Q)

E⊥-map : (f : A → B) (ν : Dist⊥ A) (G : B → ℚ)
       → E⊥ (Dmap⊥ f ν) G ≡ E⊥ ν (λ p → G (f p))
E⊥-map f ν G =
  trans (E⊥-bind ν (λ p → return⊥ (f p)) G)
        (lookupᴰℚ-cong-P (entries ν) λ where
          (just p) → E⊥-return (f p) G
          nothing  → refl)

E⊥-map-bind : (f : A → B) (ν : Dist⊥ A) (κ : B → Dist⊥ C) (G : C → ℚ)
            → E⊥ (Dmap⊥ f ν >>=⊥ κ) G ≡ E⊥ (ν >>=⊥ λ p → κ (f p)) G
E⊥-map-bind f ν κ G =
  trans (E⊥-bind (Dmap⊥ f ν) κ G)
        (trans (E⊥-map f ν (λ p → E⊥ (κ p) G))
               (sym (E⊥-bind ν (λ p → κ (f p)) G)))

E⊥-coin : (μ : Dist-ℚ Bool) (κ : Bool → Dist⊥ A) (G : A → ℚ)
        → E⊥ (Dmap just μ >>=⊥ κ) G ≡ E⊥ (μ >>=ᴹ κ) G
E⊥-coin μ κ G =
  trans (E⊥-bind (Dmap just μ) κ G)
        (trans (lookupᴰℚ-Dmap just μ (maybeℚ λ c → E⊥ (κ c) G))
               (sym (E-bind μ κ (maybeℚ G))))

------------------------------------------------------------------------
-- Settling

-- A RECORD rather than a pair: `Dist-ℚ` is itself a record and `E⊥` projects
-- it, so where the type unfolds to a `Σ` the value is compared through `E⊥`, a
-- value left implicit eta-expands into entries and weights, and unification
-- blocks on a weight.  With a rigid head the value is solved by the type.
record Settles (n : ℕ) (d : Dₚ A) (ν : Dist⊥ A) : Set where
  constructor settles
  field
    halts : Halts n d
    score : (Q : A → ℚ) → NNF Q → cum n d Q ≡ E⊥ ν Q

open Settles public

E⊥-nn : (ν : Dist⊥ A) (Q : A → ℚ) → NNF Q → 0ℚ ℚ.≤ E⊥ ν Q
E⊥-nn ν Q nn = ≤-trans (≤-reflexive (sym (E-const ν 0ℚ)))
                       (E-mono ν (λ _ → 0ℚ) (maybeℚ Q) λ where
                         (just p) → nn p
                         nothing  → ≤-refl)

Settles-cum : Settles n d ν → NNF P → (m : ℕ) → n ≤ m → cum m d P ≡ E⊥ ν P
Settles-cum {n = n} {d = d} {P = P} (settles h e) nn m le =
  trans (trans (cong (λ i → cum i d P) (sym (m+[n∸m]≡n le)))
               (Halts-cum n (m ∸ n) d P nn h))
        (e P nn)

Settles-mono : n ≤ m → Settles n d ν → Settles m d ν
Settles-mono {d = d} le s = settles (Halts-mono le d (halts s)) λ Q nn → Settles-cum s nn _ le

-- Only what `E⊥` reads of the value is pinned, so a consumer holding an
-- `_≈Mℚ_` supplies `λ Q → eq (maybeℚ Q)`.  Both values are EXPLICIT: `Dist-ℚ`
-- is a record and `E⊥` projects it, so a value left implicit is a meta that
-- eta-expands into entries and weights, and unification blocks on the weight.
Settles-resp : (ν ν′ : Dist⊥ A) → ((Q : A → ℚ) → E⊥ ν Q ≡ E⊥ ν′ Q)
             → Settles n d ν → Settles n d ν′
Settles-resp _ _ eq (settles h e) = settles h λ Q nn → trans (e Q nn) (eq Q)

------------------------------------------------------------------------
-- The four ways a run is built

Settles-return : (p : A) → Settles 1 (returnₚ p) (return⊥ p)
Settles-return p = settles (inj₂ λ _ → tt)
                           λ Q nn → trans (returnₚ-cum 0 p Q) (sym (E⊥-return p Q))

Settles-bot : Settles 0 (botₚ {A = A}) (return-ℚ nothing)
Settles-bot = settles (λ Q nn i → botₚ-cum i Q)
                      λ Q nn → sym (lookupᴰℚ-return nothing (maybeℚ Q))

Settles-coin : (μ : Dist-ℚ Bool) → Settles 2 (coinₚ μ) (Dmap just μ)
Settles-coin μ = settles hlt λ Q nn → trans (coinₚ-cum μ 0 Q) (sym (Eⱼ μ Q))
  where
  hlt : Halts 2 (coinₚ μ)
  hlt = inj₂ λ where
    true  → inj₂ λ _ → tt
    false → inj₂ λ _ → tt

mutual
  Halts-bind : (n j : ℕ) (d : Dₚ A) (f : A → Dₚ B) (κ : A → Dist⊥ B)
             → Halts n d → Supp n d (λ p → Settles j (f p) (κ p))
             → Halts (n + j) (d >>=ₚ f)
  Halts-bind zero    j d f κ z sp =
    Null⇒Halts j (d >>=ₚ f) (Null-bind d f z)
  Halts-bind (suc n) j d f κ (inj₁ z) sp =
    Null⇒Halts (suc n + j) (d >>=ₚ f) (Null-bind d f z)
  Halts-bind (suc n) j d f κ (inj₂ h) (s₁ , s₂) = inj₂ λ where
    true  → HaltsL-bind n j (br d true)  f κ (h true)  s₁
    false → HaltsL-bind n j (br d false) f κ (h false) s₂

  HaltsL-bind : (n j : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B) (κ : A → Dist⊥ B)
              → HaltsL n x → SuppL n x (λ p → Settles j (f p) (κ p))
              → HaltsL (n + j) (tagₚ x f)
  HaltsL-bind n j (inj₁ p)  f κ h s = Halts-plus n j (f p) (halts s)
  HaltsL-bind n j (inj₂ d′) f κ h s = Halts-bind n j d′ f κ h s

mutual
  cum-bind : (n j : ℕ) (d : Dₚ A) (f : A → Dₚ B) (κ : A → Dist⊥ B) (Q : B → ℚ) → NNF Q
           → Halts n d → Supp n d (λ p → Settles j (f p) (κ p))
           → cum (n + j) (d >>=ₚ f) Q ≡ cum n d (λ p → E⊥ (κ p) Q)
  cum-bind zero    j d f κ Q nn z sp = Null-bind d f z Q nn j
  cum-bind (suc n) j d f κ Q nn (inj₁ z) sp =
    trans (Null-bind d f z Q nn (suc n + j))
          (sym (z (λ p → E⊥ (κ p) Q) (λ p → E⊥-nn (κ p) Q nn) (suc n)))
  cum-bind (suc n) j d f κ Q nn (inj₂ h) (s₁ , s₂) =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_)  (leafₚ-bind n j (br d true)  f κ Q nn (h true)  s₁))
                (cong (wt d false ℚ.*_) (leafₚ-bind n j (br d false) f κ Q nn (h false) s₂))

  leafₚ-bind : (n j : ℕ) (x : A ⊎ Dₚ A) (f : A → Dₚ B) (κ : A → Dist⊥ B) (Q : B → ℚ) → NNF Q
             → HaltsL n x → SuppL n x (λ p → Settles j (f p) (κ p))
             → leafₚ (n + j) (tagₚ x f) Q ≡ leafₚ n x (λ p → E⊥ (κ p) Q)
  leafₚ-bind n j (inj₁ p)  f κ Q nn h s = Settles-cum s nn (n + j) (m≤n+m j n)
  leafₚ-bind n j (inj₂ d′) f κ Q nn h s = cum-bind n j d′ f κ Q nn h s

Settles-bind : (n j : ℕ) (d : Dₚ A) (f : A → Dₚ B) (ν : Dist⊥ A) (κ : A → Dist⊥ B)
             → Settles n d ν → Supp n d (λ p → Settles j (f p) (κ p))
             → Settles (n + j) (d >>=ₚ f) (ν >>=⊥ κ)
Settles-bind n j d f ν κ (settles h e) sp =
  settles (Halts-bind n j d f κ h sp)
          λ Q nn → trans (cum-bind n j d f κ Q nn h sp)
                         (trans (e (λ p → E⊥ (κ p) Q) (λ p → E⊥-nn (κ p) Q nn))
                                (sym (E⊥-bind ν κ Q)))

------------------------------------------------------------------------
-- …and the form a consumer meets it in

-- The continuation settles at every value, at its own budget; `Dp.uniformize`
-- maxes those over the finitely many values the junction can reach.
Settles-bind⋆ : (n : ℕ) (d : Dₚ A) (f : A → Dₚ B) (ν : Dist⊥ A) (κ : A → Dist⊥ B)
              → Settles n d ν → ((p : A) → Σ[ i ∈ ℕ ] Settles i (f p) (κ p))
              → Σ[ i ∈ ℕ ] Settles i (d >>=ₚ f) (ν >>=⊥ κ)
Settles-bind⋆ n d f ν κ s w =
  let j , sp = uniformize (λ p i → Settles i (f p) (κ p)) (λ p le → Settles-mono le) w n d
  in n + j , Settles-bind n j d f ν κ s sp

------------------------------------------------------------------------
-- Settling on a TOTAL distribution
--
-- No branch diverges, so the `Maybe` sink carries no mass and the value is an
-- ordinary `Dist-ℚ`.  This is the form a closed game's kernel is written in.

Settlesᵀ : ℕ → Dₚ A → Dist-ℚ A → Set
Settlesᵀ n d μ = Settles n d (Dmap just μ)

Settlesᵀ-cum : Settlesᵀ n d μ → NNF P → (m : ℕ) → n ≤ m → cum m d P ≡ E μ P
Settlesᵀ-cum {μ = μ} {P = P} s nn m le = trans (Settles-cum s nn m le) (Eⱼ μ P)

Settlesᵀ-return : (p : A) → Settlesᵀ 1 (returnₚ p) (return-ℚ p)
Settlesᵀ-return p =
  Settles-resp (return⊥ p) (Dmap just (return-ℚ p))
    (λ Q → trans (E⊥-return p Q)
                 (trans (sym (lookupᴰℚ-return p Q)) (sym (Eⱼ (return-ℚ p) Q))))
    (Settles-return p)

Settlesᵀ-coin : (μ : Dist-ℚ Bool) → Settlesᵀ 2 (coinₚ μ) μ
Settlesᵀ-coin = Settles-coin

Settlesᵀ-bind⋆ : (n : ℕ) (d : Dₚ A) (f : A → Dₚ B) (μ : Dist-ℚ A) (κ : A → Dist-ℚ B)
               → Settlesᵀ n d μ → ((p : A) → Σ[ i ∈ ℕ ] Settlesᵀ i (f p) (κ p))
               → Σ[ i ∈ ℕ ] Settlesᵀ i (d >>=ₚ f) (μ >>=ᴹ κ)
Settlesᵀ-bind⋆ n d f μ κ s w =
  let i , t = Settles-bind⋆ n d f (Dmap just μ) (λ p → Dmap just (κ p)) s w
  in i , Settles-resp (Dmap just μ >>=⊥ λ p → Dmap just (κ p)) (Dmap just (μ >>=ᴹ κ)) value t
  where
  value : (Q : _ → ℚ) → E⊥ (Dmap just μ >>=⊥ λ p → Dmap just (κ p)) Q
                      ≡ E⊥ (Dmap just (μ >>=ᴹ κ)) Q
  value Q = trans (E⊥-bind (Dmap just μ) (λ p → Dmap just (κ p)) Q)
            (trans (Eⱼ μ (λ p → E⊥ (Dmap just (κ p)) Q))
            (trans (lookupᴰℚ-cong-P (entries μ) (λ p → Eⱼ (κ p) Q))
            (trans (sym (E-bind μ κ Q)) (sym (Eⱼ (μ >>=ᴹ κ) Q)))))

-- …and the tagged form a machine step settles at: the kernel is total, the
-- machine's answer is the kernel's relabelled, and the sink is still empty.
Settlesᵀ-tag : {d : Dₚ B} (f : A → B) (μ : Dist-ℚ A)
             → Settlesᵀ n d (Dmap f μ) → Settles n d (Dmap⊥ f (Dmap just μ))
Settlesᵀ-tag f μ = Settles-resp (Dmap just (Dmap f μ)) (Dmap⊥ f (Dmap just μ)) λ Q →
  trans (Eⱼ (Dmap f μ) Q)
        (trans (lookupᴰℚ-Dmap f μ Q)
               (trans (sym (Eⱼ μ (λ p → Q (f p)))) (sym (E⊥-map f (Dmap just μ) Q))))

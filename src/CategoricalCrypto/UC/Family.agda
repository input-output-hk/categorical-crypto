{-# OPTIONS --safe --without-K #-}

-- `𝒞^ω`, the indexed family layer: objects are `Ix`-indexed object families and
-- homs carry a query budget polynomial in the security parameter.
--
-- The index is a PARAMETER `Ix` with a security-parameter projection
-- `κ : Ix → ℕ`, where the reference arc hardwired `Ix = ℕ`.  Only three things
-- ever needed `ℕ` there: the polynomial's argument, the asymptotics' order, and
-- the budget arithmetic — and all three read the index through `κ` alone.  So a
-- second axis costs nothing: `Ix = ℕ × ℕ` with `κ = proj₁` gives a family
-- graded by the security parameter and anything else, and `(ℕ , id)` recovers
-- the reference.
--
-- `κ` must be COFINAL, and that is a soundness requirement rather than
-- bookkeeping: eventual closeness quantifies over the indices above a
-- threshold, so a bounded `κ` (constantly zero, say) makes every eventual
-- statement — hence the whole UC preorder — vacuously true.  `κ-cofinal` is
-- what `≈^ω-witness` spends.  It is an ASYMPTOTIC-INSTANCE requirement and not
-- a requirement of general UC: nothing in the core, the environment layer or
-- the emulation metatheory mentions an index at all.
--
-- This layer is where the notes' quantitative-to-qualitative arrow runs.
-- Everything categorical is levelwise, so the whole `UCBase` transports; the
-- observation, however, is CONSTRUCTED rather than transported — the base's
-- ε-closeness becomes *eventual* ε-closeness in `κ`, and
-- `UC.Approximate.Induced` turns that into the qualitative agreement the core
-- consumes, which is then literally the vanishing-advantage relation (its ε/2
-- transitivity proved once, there).  `absorb` is that construction's `induces`
-- read at a vanishing error.
--
-- Vanishing is all `absorb` spends, but it is not what a cryptographic bound
-- must satisfy: that is NEGLIGIBILITY, eventually below every inverse
-- polynomial (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`).
-- Hence the negligible layer below, over the same `PolyQB` allowance.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)

open import CategoricalCrypto.UC.Approximate
  using ( Approximation; ApproximateObservation; Negligible; NegligibleBound
        ; NegligibleBound⇒VanishingBound; VanishingBound; ℚ-errors; module Induced )
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Core using (UCBase; Grading; Observation)
import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Family
  {o ℓ e os ℓs ℓa qs : Level} (base : UCBase o ℓ e os ℓs)
  (qapx : ApproximateObservation (UCBase.observation base) ℚ-errors ℓa)
  (bud : Budget (UCBase.𝒞 base) (UCBase.grading base) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open UCBase base
open ApproximateObservation qapx
open Budget bud

------------------------------------------------------------------------
-- Objects, homs and their budgets

Obj^ω : Set o
Obj^ω = Ix → Obj

Δ : Obj → Obj^ω
Δ X _ = X

private variable A B : Obj^ω

-- Polynomial in the SECURITY PARAMETER, which is what `κ` reads off the index.
PolyQB : ((i : Ix) → A i ⇒ B i) → Set qs
PolyQB f = Σ[ p ∈ (ℕ → ℕ) ] Poly p × ((i : Ix) → QB (p (κ i)) (f i))

qb1 : {f : (i : Ix) → A i ⇒ B i} → ((i : Ix) → QB 1 (f i)) → PolyQB f
qb1 w = (λ _ → 1) , poly-const 1 , w

infix 10 _⇒^ω_
infix 4 _≈^ω_

_⇒^ω_ : Obj^ω → Obj^ω → Set (ℓ ⊔ qs)
A ⇒^ω B = Σ ((i : Ix) → A i ⇒ B i) PolyQB

_≈^ω_ : (f g : A ⇒^ω B) → Set e
f ≈^ω g = (i : Ix) → proj₁ f i ≈ proj₁ g i

-- The budget a hom CARRIES, as opposed to one an obligation invents: this is
-- what makes a query bound contribute to a statement about a hom.
qbOf : A ⇒^ω B → ℕ → ℕ
qbOf f = proj₁ (proj₂ f)

qbOf-poly : (f : A ⇒^ω B) → Poly (qbOf f)
qbOf-poly f = proj₁ (proj₂ (proj₂ f))

Fam : Category o (ℓ ⊔ qs) e
Fam = record
  { Obj       = Obj^ω
  ; _⇒_       = _⇒^ω_
  ; _≈_       = _≈^ω_
  ; id        = (λ _ → id) , qb1 (λ _ → qb-id)
  ; _∘_       = λ (g , p , Pp , wg) (f , q , Pq , wf) →
      (λ i → g i ∘ f i) , (λ n → p n ℕ.* q n) , poly-* Pp Pq , λ i → qb-∘ (wg i) (wf i)
  ; assoc     = λ _ → assoc
  ; sym-assoc = λ _ → sym-assoc
  ; identityˡ = λ _ → identityˡ
  ; identityʳ = λ _ → identityʳ
  ; identity² = λ _ → identity²
  ; equiv     = record
    { refl  = λ _ → Equiv.refl
    ; sym   = λ f≈g i → Equiv.sym (f≈g i)
    ; trans = λ f≈g g≈h i → Equiv.trans (f≈g i) (g≈h i)
    }
  ; ∘-resp-≈  = λ g≈i f≈h i → ∘-resp-≈ (g≈i i) (f≈h i)
  }

------------------------------------------------------------------------
-- The grading, levelwise

infixr 8 _⊛ω_

_⊛ω_ : Obj^ω → Obj^ω → Obj^ω
(A ⊛ω B) i = A i ⊛ B i

Grading^ω : Grading Fam
Grading^ω = record
  { _⊛_ = _⊛ω_
  ; 𝟭   = Δ 𝟭
  ; T₁  = λ Y (f , p , Pp , w) → (λ i → T₁ (Y i) (f i))
        , (λ n → p n ℕ.⊔ 1) , poly-⊔ Pp (poly-const 1) , λ i → qb-T₁ (w i)
  ; sub = λ (s , p , Pp , w) → (λ i → sub (s i))
        , (λ n → p n ℕ.⊔ 1) , poly-⊔ Pp (poly-const 1) , λ i → qb-sub (w i)
  ; a⇒  = (λ _ → a⇒) , qb1 (λ _ → qb-a⇒)
  ; a⇐  = (λ _ → a⇐) , qb1 (λ _ → qb-a⇐)
  ; λ⇒  = (λ _ → λ⇒) , qb1 (λ _ → qb-λ⇒)
  ; λ⇐  = (λ _ → λ⇐) , qb1 (λ _ → qb-λ⇐)
  ; ρ⇒  = (λ _ → ρ⇒) , qb1 (λ _ → qb-ρ⇒)
  ; ρ⇐  = (λ _ → ρ⇐) , qb1 (λ _ → qb-ρ⇐)

  ; T₁-resp-≈  = λ eq i → T₁-resp-≈ (eq i)
  ; T₁-id      = λ _ → T₁-id
  ; T₁-∘       = λ _ → T₁-∘
  ; sub-resp-≈ = λ eq i → sub-resp-≈ (eq i)
  ; sub-id     = λ _ → sub-id
  ; sub-∘      = λ _ → sub-∘
  ; a-isoˡ     = λ _ → a-isoˡ
  ; a-nat      = λ _ → a-nat
  }

------------------------------------------------------------------------
-- The observation, asymptotically

infix 4 _≈^ω[_]_

-- Eventually ε-close in the security parameter.
_≈^ω[_]_ : (Ix → Obs) → ℚ → (Ix → Obs) → Set ℓa
μ ≈^ω[ ε ] ν = Σ[ N ∈ ℕ ] ((i : Ix) → N ℕ.≤ κ i → μ i ≈[ ε ] ν i)

-- Cofinality is what keeps the eventual relation from being satisfiable by
-- fiat: every threshold is met by some index, so an eventual closeness is
-- witnessed by an actual one.
≈^ω-witness : {μ ν : Ix → Obs} {ε : ℚ} → μ ≈^ω[ ε ] ν → Σ[ i ∈ Ix ] μ i ≈[ ε ] ν i
≈^ω-witness (N , h) = let i , le = κ-cofinal N in i , h i le

Approximation^ω : Approximation (Ix → Obs) ℚ-errors ℓa
Approximation^ω = record
  { _≈[_]_    = _≈^ω[_]_
  ; ≈[]-refl  = 0 , λ _ _ → ≈[]-refl
  ; ≈[]-sym   = λ (N , h) → N , λ i le → ≈[]-sym (h i le)
  ; ≈[]-trans = λ (N₁ , h₁) (N₂ , h₂) → N₁ ℕ.⊔ N₂ , λ i le →
      ≈[]-trans (h₁ i (≤-trans (m≤m⊔n N₁ N₂) le)) (h₂ i (≤-trans (m≤n⊔m N₁ N₂) le))
  ; ≈[]-mono  = λ le (N , h) → N , λ i le′ → ≈[]-mono le (h i le′)
  }

private
  module I = Induced Fam Approximation^ω (Δ 𝟙) (Δ Ω) (λ u i → ⟦ proj₁ u i ⟧)
                     (λ eq → 0 , λ i _ → ⟦⟧-resp-≈₀ (eq i))

-- The qualitative observation the core consumes: `_∼_` is vanishing advantage.
Observation^ω : Observation Fam os ℓa
Observation^ω = I.observation

-- …and the family is again a quantitative model, so the construction iterates.
Approximate^ω : ApproximateObservation Observation^ω ℚ-errors ℓa
Approximate^ω = I.approximate

UCBase^ω : UCBase o (ℓ ⊔ qs) e os ℓa
UCBase^ω = record { 𝒞 = Fam ; grading = Grading^ω ; observation = Observation^ω }

------------------------------------------------------------------------
-- Ingestion: a concrete bound, and its collapse

private module E = Em UCBase^ω

open E public using
  ( Test; Closure; obs; SameTV; same; same-≈; Tests; tv₁; ℰᵗᵛ
  ; _≈ℰ_; ≈ℰ-refl; ≈ℰ-sym; ≈ℰ-trans; ≈ℰ-setoid; ≈⇒≈ℰ; ≈ℰ-congˡ; ≈ℰ-congʳ
  ; grade-stable; _≤UC_; _≤UC⁺_; ≤UC-refl; ≤UC-trans; dummy-complete )
  renaming (ℰᴼ to ℰ^ω)

-- `ℰ^ω` and `Fam` are two of `UCSetup`'s four fields; the other two are a
-- MONOIDAL structure on `Fam` and the graded Kleisli triple over it, which
-- `UC.Family.Monoidal` assembles at a monoidal base.  They do not belong here:
-- a `Grading` has the two one-sided actions and no bifunctor, so the tensor of
-- two `Fam`-homs would have no budget.

infix 4 _≈ℰ[_]_

-- The budget a context's two legs CARRY, as one polynomial: `ctxBudget`
-- levelwise, so a closure certifying at `QB 0` cannot evaluate a concrete bound
-- at budget zero against a context that genuinely queries (`UC.Budget`'s comment
-- has the accounting).
ctxQB : (p q : ℕ → ℕ) → ℕ → ℕ
ctxQB p q n = ctxBudget (p n) (q n)

ctxQB-poly : {p q : ℕ → ℕ} → Poly p → Poly q → Poly (ctxQB p q)
ctxQB-poly Pp Pq = poly-* Pp (poly-⊔ Pq (poly-const 1))

-- The shape a concrete security theorem has: at every ancilla context, the
-- level-`i` advantage is at most `ε` of the security parameter and of the
-- polynomial budget the context's two legs CARRY.  This is the only place the
-- query bound earns its keep — an unbudgeted context would make `ε` a function
-- of nothing, and `absorb` below would have no polynomial to close over.
_≈ℰ[_]_ : {A B : Obj^ω} → A ⇒^ω B → (ℕ → ℕ → ℚ) → A ⇒^ω B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≈ℰ[_]_ {A} {B} f ε g =
  (Y : Obj^ω) (Et : Test (Y ⊛ω B)) (m : Closure (Y ⊛ω A)) (i : Ix)
  → obs (tv₁ Y f Et) m i ≈[ ε (κ i) (ctxQB (qbOf Et) (qbOf m) (κ i)) ]
    obs (tv₁ Y g Et) m i

-- A vanishing bound collapses the quantitative statement to environment
-- agreement.  The context supplies the polynomial; `poly-*` closes it.
absorb : {A B : Obj^ω} {f g : A ⇒^ω B} {ε : ℕ → ℕ → ℚ}
       → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
absorb {f = f} {g} {ε} bnd van Y Et m δ δ>0 =
  let N , hN = van (ctxQB (qbOf Et) (qbOf m))
                   (ctxQB-poly (qbOf-poly Et) (qbOf-poly m)) δ δ>0
  in N , λ i le → ≈[]-mono (hN (κ i) le) (bnd Y Et m i)

------------------------------------------------------------------------
-- The negligible layer

-- `VanishingBound` is the WEAKER enrichment, and stays: `absorb` spends nothing
-- more than convergence.  A cryptographic bound is held to `Negligible` instead
-- (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`), and the
-- allowance it is negligible at is the one the model already supplies —
-- `PolyQB`, the polynomial a context's two legs carry.

-- The §3 discipline read at exactly the budgets `_≈ℰ[_]_` evaluates `ε` on.
CarriedNegligible : (ℕ → ℕ → ℚ) → Set (o ⊔ ℓ ⊔ qs)
CarriedNegligible ε = {A B : Obj^ω} (Y : Obj^ω) (Et : Test (Y ⊛ω B))
                      (m : Closure (Y ⊛ω A))
                    → Negligible (λ n → ε n (ctxQB (qbOf Et) (qbOf m) n))

-- …and it is no extra assumption: `ctxQB-poly` is the polynomial witness.
carried-negligible : {ε : ℕ → ℕ → ℚ} → NegligibleBound ε → CarriedNegligible ε
carried-negligible neg Y Et m =
  neg (ctxQB (qbOf Et) (qbOf m)) (ctxQB-poly (qbOf-poly Et) (qbOf-poly m))

absorb-negl : {A B : Obj^ω} {f g : A ⇒^ω B} {ε : ℕ → ℕ → ℚ}
            → f ≈ℰ[ ε ] g → NegligibleBound ε → f ≈ℰ g
absorb-negl {A} {B} {f} {g} {ε} bnd neg =
  absorb {A} {B} {f} {g} {ε} bnd (NegligibleBound⇒VanishingBound {ε} neg)

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
-- The base is a MONOIDAL category at its standard grading, so `Fam` carries a
-- monoidal structure too and the family's grading is again the standard one.
-- The whole gap is the budget: a `Fam`-hom is a base hom plus a polynomial
-- bound and `_≈^ω_` ignores the bound, so every monoidal LAW is the base's read
-- levelwise and the only content is a `QB` certificate per structural
-- morphism.  `UC.Budget.Budget`'s four unitor fields are what that costs; the
-- bifunctor costs nothing extra, because `f ⊗₁ g` factors as `sub f ∘ T₁ _ g`.
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
-- Hence the negligible layer below, over the same `PolyQB` allowance — which
-- grades the PREMISE and nothing else.  `_≈ℰ_` is vanishing agreement whichever
-- grade goes in, so it does not transport a property whose slack must stay
-- negligible: a bad bit of probability `1/(n+1)` is `≈ℰ`-equal to an
-- always-safe one.  A statement of that kind keeps its error witness instead —
-- `_≈ℰⁿ_` here, `UC.Saturated._≈negl_` at layer 1.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (monoidalHelper)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Functor.Bifunctor using (Bifunctor)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Approximate
  using ( Approximation; ApproximateObservation; Negligible; Negligible-+; Negligible-0
        ; Negligible⇒→0; NegligibleBound; NegligibleBound⇒VanishingBound; VanishingBound
        ; ℚ-errors; module Induced )
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Core using (Observation; UCBase)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Environment as Env

module CategoricalCrypto.UC.Family
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

private module 𝕄 = MonoidalCategory M

-- The base the family layer is taken over: the standard grading of `M`, which
-- is where the four unitor certificates land.
baseᴹ : UCBase o ℓ e os ℓs
baseᴹ = record { 𝒞 = 𝕄.U ; grading = Std.gradingᵗ M ; observation = obsᴹ }

open UCBase baseᴹ
open ApproximateObservation qapx
open Budget bud
open MonR 𝕄.monoidal using (serialize₁₂)

------------------------------------------------------------------------
-- Objects, homs and their budgets

Obj^ω : Set o
Obj^ω = Ix → Obj

Δ : Obj → Obj^ω
Δ X _ = X

private variable A B C D : Obj^ω

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
-- The monoidal structure, levelwise

infixr 8 _⊛ω_
infixr 10 _⊗^ω_

_⊛ω_ : Obj^ω → Obj^ω → Obj^ω
(A ⊛ω B) i = A i ⊛ B i

-- The product certificate the reference arc asked as a field: `f ⊗₁ g` is
-- `(f ⊗₁ id) ∘ (id ⊗₁ g)`, which the action's two one-sided halves certify.
qb-⊗₁ : {X Y Z W : Obj} {c c′ : ℕ} {f : X ⇒ Y} {g : Z ⇒ W}
      → QB c f → QB c′ g → QB ((c ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1)) (𝕄._⊗₁_ f g)
qb-⊗₁ qf qg = qb-resp-≈ (Equiv.sym serialize₁₂) (qb-∘ (qb-sub qf) (qb-T₁ qg))

_⊗^ω_ : A ⇒^ω B → C ⇒^ω D → (A ⊛ω C) ⇒^ω (B ⊛ω D)
(f , p , Pp , wf) ⊗^ω (g , q , Pq , wg) =
    (λ i → 𝕄._⊗₁_ (f i) (g i))
  , (λ n → (p n ℕ.⊔ 1) ℕ.* (q n ℕ.⊔ 1))
  , poly-* (poly-⊔ Pp (poly-const 1)) (poly-⊔ Pq (poly-const 1))
  , λ i → qb-⊗₁ (wf i) (wg i)

⊗^ω-bifunctor : Bifunctor Fam Fam Fam
⊗^ω-bifunctor = record
  { F₀           = λ (A , B) → A ⊛ω B
  ; F₁           = λ (f , g) → f ⊗^ω g
  ; identity     = λ _ → 𝕄.⊗.identity
  ; homomorphism = λ _ → 𝕄.⊗.homomorphism
  ; F-resp-≈     = λ (ef , eg) i → 𝕄.⊗.F-resp-≈ (ef i , eg i)
  }

Famᴹ : MonoidalCategory o (ℓ ⊔ qs) e
Famᴹ = record
  { U        = Fam
  ; monoidal = monoidalHelper Fam record
    { ⊗          = ⊗^ω-bifunctor
    ; unit       = Δ 𝟭
    ; unitorˡ    = record
      { from = (λ _ → λ⇒) , qb1 (λ _ → qb-λ⇒)
      ; to   = (λ _ → λ⇐) , qb1 (λ _ → qb-λ⇐)
      ; iso  = record { isoˡ = λ _ → 𝕄.unitorˡ.isoˡ ; isoʳ = λ _ → 𝕄.unitorˡ.isoʳ }
      }
    ; unitorʳ    = record
      { from = (λ _ → ρ⇒) , qb1 (λ _ → qb-ρ⇒)
      ; to   = (λ _ → ρ⇐) , qb1 (λ _ → qb-ρ⇐)
      ; iso  = record { isoˡ = λ _ → 𝕄.unitorʳ.isoˡ ; isoʳ = λ _ → 𝕄.unitorʳ.isoʳ }
      }
    ; associator = record
      { from = (λ _ → a⇐) , qb1 (λ _ → qb-a⇐)
      ; to   = (λ _ → a⇒) , qb1 (λ _ → qb-a⇒)
      ; iso  = record { isoˡ = λ _ → 𝕄.associator.isoˡ ; isoʳ = λ _ → 𝕄.associator.isoʳ }
      }
    ; unitorˡ-commute = λ _ → 𝕄.unitorˡ-commute-from
    ; unitorʳ-commute = λ _ → 𝕄.unitorʳ-commute-from
    ; assoc-commute   = λ _ → 𝕄.assoc-commute-from
    ; triangle        = λ _ → 𝕄.triangle
    ; pentagon        = λ _ → 𝕄.pentagon
    }
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
UCBase^ω = record
  { 𝒞 = Fam ; grading = Std.gradingᵗ Famᴹ ; observation = Observation^ω }

------------------------------------------------------------------------
-- Ingestion: a concrete bound, and its collapse

private module E = Env UCBase^ω

open E public using
  ( Test; Closure; obs; SameTV; same; same-≈; Tests; tv₁; ℰᵗᵛ; grade-stable
  ; _≈ℰ_; ≈ℰ-refl; ≈ℰ-sym; ≈ℰ-trans; ≈ℰ-setoid; ≈⇒≈ℰ; ≈ℰ-congˡ; ≈ℰ-congʳ )
  renaming (ℰᴼ to ℰ^ω)

-- P6 of `docs/stduc-supersession-plan.md`: the four fields of `UCSetup` at
-- `Fam`.  `ℳ` is the curried tensor of `Famᴹ` and `ℰ` is `UC.Environment`'s
-- `Observation → Presheaf` construction at `Observation^ω`, so the whole of
-- `Abstract2.AbstractUC` — `≤UC-refl`, `dummy-complete`, `≤UC-trans`,
-- `UC-compose`, `≈ᵁ⇒≈ℰ` — is available at the asymptotic family.
ucSetup^ω : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetup^ω = Std2.StdUC.StdSetup Famᴹ ℰ^ω

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

-- A sufficient condition into the SAME `≈ℰ`: the grade is spent going in and
-- cannot be read back out (header).
absorb-negl : {A B : Obj^ω} {f g : A ⇒^ω B} {ε : ℕ → ℕ → ℚ}
            → f ≈ℰ[ ε ] g → NegligibleBound ε → f ≈ℰ g
absorb-negl {A} {B} {f} {g} {ε} bnd neg =
  absorb {A} {B} {f} {g} {ε} bnd (NegligibleBound⇒VanishingBound {ε} neg)

infix 4 _≈ℰⁿ_

-- Reading the grade back out means not throwing the witness away: `_≈ℰⁿ_` is
-- `absorb-negl`'s premise with its `ε` KEPT, so a property whose slack must
-- stay negligible survives it where `_≈ℰ_` loses it.  `UC.Saturated._≈negl_`
-- is the same move at layer 1.
_≈ℰⁿ_ : {A B : Obj^ω} → A ⇒^ω B → A ⇒^ω B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
f ≈ℰⁿ g = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] CarriedNegligible ε × f ≈ℰ[ ε ] g

≈ℰⁿ-refl : {A B : Obj^ω} {f : A ⇒^ω B} → f ≈ℰⁿ f
≈ℰⁿ-refl = (λ _ _ → 0ℚ) , (λ _ _ _ → Negligible-0) , λ _ _ _ _ → ≈[]-refl

≈ℰⁿ-sym : {A B : Obj^ω} {f g : A ⇒^ω B} → f ≈ℰⁿ g → g ≈ℰⁿ f
≈ℰⁿ-sym (ε , neg , bnd) = ε , neg , λ Y Et m i → ≈[]-sym (bnd Y Et m i)

≈ℰⁿ-trans : {A B : Obj^ω} {f g h : A ⇒^ω B} → f ≈ℰⁿ g → g ≈ℰⁿ h → f ≈ℰⁿ h
≈ℰⁿ-trans (ε₁ , neg₁ , bnd₁) (ε₂ , neg₂ , bnd₂) =
  (λ n q → ε₁ n q ℚ.+ ε₂ n q) , (λ Y Et m → Negligible-+ (neg₁ Y Et m) (neg₂ Y Et m))
  , λ Y Et m i → ≈[]-trans (bnd₁ Y Et m i) (bnd₂ Y Et m i)

-- It refines the vanishing agreement — `absorb` read at the allowance the
-- context carries, which is the only allowance either ever evaluates `ε` on.
≈ℰⁿ⇒≈ℰ : {A B : Obj^ω} {f g : A ⇒^ω B} → f ≈ℰⁿ g → f ≈ℰ g
≈ℰⁿ⇒≈ℰ (ε , neg , bnd) Y Et m δ δ>0 =
  let N , hN = Negligible⇒→0 (neg Y Et m) δ δ>0
  in N , λ i le → ≈[]-mono (hN (κ i) le) (bnd Y Et m i)

-- What is NOT delivered here is an `Observation` whose `_∼_` is `_≈ℰⁿ_`:
-- `Induced` builds `_∼_` by quantifying an ambient ε AWAY, and retaining the
-- witness is the opposite move.  That would mean either a second `Observation`
-- on `Fam` carrying this relation, with every emulation notion re-derived
-- over it (`≤UC` included), or an `Observation` interface parameterized by its
-- grade — redesigns of the core's observation interface rather than of this
-- module, which is why the negligible tier consumers use lives at layer 1.
--
-- Of the two, the first proved NOT to be a core redesign: `UC.Core.Observation`
-- asks for an arbitrary equivalence, so `UC.Family.Negligible` builds that
-- second `Observation` on `Fam` and inherits the emulation notions at it with
-- nothing in the qualitative core moving.  Neither is owed by the ε-RETAINING
-- composition law any more: `UC.Asymptotic.Compose` proves it directly over the
-- contextual relation, carrying the simulator witness and charging each plugged
-- morphism's allowance substitution, and only forgets into `_≈ℰⁿ_`/`_≈ℰ_` at
-- the end.

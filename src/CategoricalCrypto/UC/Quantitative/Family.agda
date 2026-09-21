{-# OPTIONS --safe --without-K #-}

-- The quantitative contextual relation on FAMILIES of graded morphisms, the
-- simulator-bearing emulation witness over it and its composition laws, at any
-- monoidal base carrying a `UC.Budget.Budget` and an approximate observation.
-- `UC.Asymptotic.Contextual`/`.Compose` are this module at the sealed machine.
--
-- `_≈ctx[ ε ]_` compares arbitrary `f n : A n ⇒ T₀ (X n) (B n)` through the
-- very context `_≈ᵁ_` quantifies over, at the allowance the context's two legs
-- CARRY; `_≈ctxᴬ[ ε ]_` is `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` at every
-- level, the same experiment at the operational bracket `W ⊗ (X ⊗ B)` where a
-- model's ingestion and extraction lemmas live.
--
-- Both relations are `UC.Quantitative.Contextual.Agreeᵠ` — the admitted
-- agreement of two test-pullbacks — at their two brackets, so every move that
-- plugs a morphism into a context is one of that module's two absorptions and
-- costs the allowance rescaled by the plugged morphism's own budget,
-- `UC.Budget.simCost`.  Every such substitution is EXACT, so no theorem below
-- reads `ε` at an inequality of allowances.
--
-- Neither relation reads the compared homs' own query bounds, only the
-- context's.  `Certified` is where a bound on a hom appears, and only on
-- morphisms a theorem actually moves into a context.
-- `docs/quantitative-family.md` is the design note.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗; μ-α⇐)
import Categories.Category.Monoidal.Reasoning as MonR

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties
  using (*-identityʳ; *-identityˡ; ⊔-assoc; ⊔-idem)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered; ≈[]-resp₀)
open import CategoricalCrypto.UC.Approximate
  using ( Approximation; GradedBound-+[_]; GradedBound-reindex; Negligible
        ; Negligible-+; NegligibleBound; ℚ-errors )
open import CategoricalCrypto.UC.Budget
  using (Budget; ctxBudget; simCost)
open import CategoricalCrypto.UC.Core using (Observation)

import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.UC.Quantitative.Family
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e) (O : Observation (MonoidalCategory.U M) os ℓs)
  (Bg : Budget M qs) (Ap : Approximation (Observation.Obs O) ℚ-errors ℓa)
  (reflects : {x y : Observation.Obs O}
            → Observation._∼_ O x y → Approximation._∼ᵃ_ Ap x y)
  (obs-resp : {u v : MonoidalCategory._⇒_ M (Observation.𝟙 O) (Observation.Ω O)}
            → MonoidalCategory._≈_ M u v
            → Approximation._≈[_]_ Ap (Observation.⟦_⟧ O u) 0ℚ
                                      (Observation.⟦_⟧ O v))
  where

open import CategoricalCrypto.UC.Core.Bridge M O
open import CategoricalCrypto.UC.Quantitative.Contextual M Bg Ap
  (Observation.𝟙 O) (Observation.Ω O) (Observation.⟦_⟧ O) obs-resp
open import CategoricalCrypto.UC.Quantitative.Query using (module Fl)

open Approximation Ap
open Budget Bg
open Fl
open HomReasoning
open MonR monoidal using (split₂ʳ)
open Observation O using (𝟙; Ω; ⟦_⟧)

private variable A B C X Y Z P Q : ℕ → Channel

------------------------------------------------------------------------
-- Families of graded morphisms, and the contextual relation

Homᶠ : (A X B : ℕ → Channel) → Set ℓ
Homᶠ A X B = (n : ℕ) → A n ⇒ T₀ (X n) (B n)

-- `Abstract2.Action.prefix`, spelled out: naming the generic action instead
-- costs a module application of `Abstract2.Action` at the consuming setup —
-- measured, +22 s at the machine — and the lemmas that consume it are stated
-- at this spelling anyway.
prefixᵒ : (W : Channel) {A′ B′ X′ : Channel} → A′ ⇒ T₀ X′ B′ → T₀ W A′ ⇒ T₀ (W ⊗₀ X′) B′
prefixᵒ W {X′ = X′} f = μ W X′ ∘ T₁ W f

infix 4 _≈ctx[_]_ _≈ctxᴬ[_]_

-- At each level, no budgeted ancilla context separates the two homs by more
-- than `ε` read at the budget the context's two legs CARRY.  `W`, the test and
-- the closure are quantified per LEVEL, not as a family of contexts — that is
-- the uniform refinement the ledger consumer needs.
_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≈ctx[_]_ {A} {X} {B} f ε g =
    (n : ℕ) (W : Channel) (E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω) (m : 𝟙 ⇒ T₀ W (A n))
    {c c′ : ℕ} → QB c E → QB c′ m
  → ⟦ (E ∘ prefixᵒ W (f n)) ∘ m ⟧ ≈[ ε n (ctxBudget c c′) ]
    ⟦ (E ∘ prefixᵒ W (g n)) ∘ m ⟧

-- …and the same experiment with the test's domain bracketed the other way,
-- which is the single-level relation at each `n`.
_≈ctxᴬ[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
f ≈ctxᴬ[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n

-- `UC.Quantitative.Contextual.Agreeᵠ` at the `prefixᵒ` bracket: the same
-- identification `ctx⇒agree`/`agree⇒ctx` make at the operational one, which is
-- what lets that module's two absorptions serve this relation too.
≈ctx⇒agreeᵠ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
            → (n : ℕ) (W : Channel)
            → Agreeᵠ (ε n) (_∘ prefixᵒ W (f n)) (_∘ prefixᵒ W (g n))
≈ctx⇒agreeᵠ _ h n W = agree λ qE m _ qm → h n W _ m qE qm

agreeᵠ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B}
            → ((n : ℕ) (W : Channel)
               → Agreeᵠ (ε n) (_∘ prefixᵒ W (f n)) (_∘ prefixᵒ W (g n)))
            → f ≈ctx[ ε ] g
agreeᵠ⇒≈ctx _ h n W E m qE qm = admitted (h n W) qE m _ qm

private
  -- A bound survives a zero-error change of either endpoint (`obs-resp`).
  splice : {u u′ v v′ : 𝟙 ⇒ Ω} {ε : ℚ}
         → u ≈ u′ → v ≈ v′ → ⟦ u ⟧ ≈[ ε ] ⟦ v ⟧ → ⟦ u′ ⟧ ≈[ ε ] ⟦ v′ ⟧
  splice p q = ≈[]-resp₀ ℚ-ordered Ap (obs-resp (⟺ p)) (obs-resp q)

------------------------------------------------------------------------
-- Rebracketing, with its cost

-- The adapter is `UC.Core.Bridge`'s associator shuffle, and what it costs the
-- context is one structural morphism in front of the test — `QB 1`, so the
-- test's budget `c` becomes `c * 1` and the allowance is unchanged
-- (`*-identityʳ`), which is why the two relations carry the same `ε`.  The
-- query certificates are transported, not assumed to survive the isomorphism.

≈ctx⇒≈ctxᴬ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → f ≈ctxᴬ[ ε ] g
≈ctx⇒≈ctxᴬ ε {f} {g} h n W E m {c} {c′} qE qm =
  subst (λ k → _ ≈[ ε n (ctxBudget k c′) ] _) (*-identityʳ c)
    (splice (shuffle⇒ (f n) E m ○ sym-assoc) (shuffle⇒ (g n) E m ○ sym-assoc)
            (h n W (E ∘ α⇒) m (qb-∘ qE qb-a⇐) qm))

≈ctxᴬ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctxᴬ[ ε ] g → f ≈ctx[ ε ] g
≈ctxᴬ⇒≈ctx ε {f} {g} h n W E m {c} {c′} qE qm =
  subst (λ k → _ ≈[ ε n (ctxBudget k c′) ] _) (*-identityʳ c)
    (splice (⟺ (shuffle⇐ (f n) E m ○ sym-assoc))
            (⟺ (shuffle⇐ (g n) E m ○ sym-assoc))
            (h n W (E ∘ α⇐) m (qb-∘ qE qb-a⇒) qm))

------------------------------------------------------------------------
-- The enrichment kit

private
  ctx-cong : {A′ B′ X′ : Channel} {f g : A′ ⇒ T₀ X′ B′} (W : Channel)
             (E : T₀ (W ⊗₀ X′) B′ ⇒ Ω) (m : 𝟙 ⇒ T₀ W A′)
           → f ≈ g → (E ∘ prefixᵒ W f) ∘ m ≈ (E ∘ prefixᵒ W g) ∘ m
  ctx-cong _ _ _ eq = ∘-resp-≈ˡ (∘-resp-≈ʳ (∘-resp-≈ʳ (T-resp-≈ eq)))

≈ctx-resp : (ε : ℕ → ℕ → ℚ) {f f′ g g′ : Homᶠ A X B}
          → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
          → f ≈ctx[ ε ] g → f′ ≈ctx[ ε ] g′
≈ctx-resp _ ef eg h n W E m qE qm =
  splice (ctx-cong W E m (ef n)) (ctx-cong W E m (eg n)) (h n W E m qE qm)

-- Zero error is exactly the ambient hom equality, which the base observes
-- EXACTLY.  The inherited `_≈ᵁ_` does NOT give it: it only puts the two runs
-- within every POSITIVE error, so it has no zero instance to hand over —
-- `≈ᵁ⇒≈ctx` is where that schedule is paid for.
≈C⇒≈ctx : {f g : Homᶠ A X B} → ((n : ℕ) → f n ≈ g n) → f ≈ctx[ (λ _ _ → 0ℚ) ] g
≈C⇒≈ctx e n W E m _ _ = obs-resp (ctx-cong W E m (e n))

≈ctx-refl : {f : Homᶠ A X B} → f ≈ctx[ (λ _ _ → 0ℚ) ] f
≈ctx-refl _ _ _ _ _ _ = ≈[]-refl

≈ctx-sym : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → g ≈ctx[ ε ] f
≈ctx-sym _ h n W E m qE qm = ≈[]-sym (h n W E m qE qm)

≈ctx-trans : (ε δ : ℕ → ℕ → ℚ) {f g h : Homᶠ A X B} → f ≈ctx[ ε ] g → g ≈ctx[ δ ] h
           → f ≈ctx[ (λ n q → ε n q ℚ.+ δ n q) ] h
≈ctx-trans _ _ p q n W E m qE qm = ≈[]-trans (p n W E m qE qm) (q n W E m qE qm)

-- Reading the same agreement at a larger SCHEDULE, which needs nothing of `ε`.
≈ctx-≤ : (ε δ : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → ((n q : ℕ) → ε n q ℚ.≤ δ n q)
       → f ≈ctx[ ε ] g → f ≈ctx[ δ ] g
≈ctx-≤ _ _ le h n W E m qE qm = ≈[]-mono (le n _) (h n W E m qE qm)

-- The inherited `_≈ᵁ_` at every level, ingested at a chosen POSITIVE schedule.
≈ᵁ⇒≈ctx : {f g : Homᶠ A X B} (ν : ℕ → ℚ) → ((n : ℕ) → 0ℚ ℚ.< ν n)
        → ((n : ℕ) → f n ≈ᵁ g n) → f ≈ctx[ (λ n _ → ν n) ] g
≈ᵁ⇒≈ctx ν pos u n W E m _ _ = reflects (KE.run∼ (u n W) {E} m) (ν n) (pos n)

------------------------------------------------------------------------
-- Certified families of grade morphisms

-- A grade-morphism family with a polynomial query certificate: the asymptotic
-- spelling of `UC.Audit._≤UC[_]_`'s `sim`/`sim-qb` pair.
--
-- A Σ and not a record, for a MEASURED reason: a record field
-- `sim-qb : (n : ℕ) → QB (cost n) (sim n)` depending on two earlier fields
-- exhausts a 20 GiB heap at the sealed machine, where the Σ whose second
-- component binds those two checks in seconds.
Certified : (A B : ℕ → Channel) → Set (ℓ ⊔ qs)
Certified A B =
  Σ[ s ∈ ((n : ℕ) → A n ⇒ B n) ] Σ[ q ∈ (ℕ → ℕ) ] Poly q × ((n : ℕ) → QB (q n) (s n))

sim : Certified A B → (n : ℕ) → A n ⇒ B n
sim = proj₁

cost : Certified A B → ℕ → ℕ
cost s = proj₁ (proj₂ s)

cost-poly : (s : Certified A B) → Poly (cost s)
cost-poly s = proj₁ (proj₂ (proj₂ s))

sim-qb : (s : Certified A B) (n : ℕ) → QB (cost s n) (sim s n)
sim-qb s = proj₂ (proj₂ (proj₂ s))

infixr 9 _∘ᶜ_

idᶜ : Certified X X
idᶜ = (λ _ → id) , (λ _ → 1) , poly-const 1 , λ _ → qb-id

_∘ᶜ_ : Certified Y Z → Certified X Y → Certified X Z
(a , p , Pp , qa) ∘ᶜ (s , q , Pq , qs) =
  (λ n → a n ∘ s n) , (λ n → p n ℕ.* q n) , poly-* Pp Pq , λ n → qb-∘ (qa n) (qs n)

-- The unit regrading and its retraction, which `≈ctx-sub`/`≤UC^ωᵉ-sub` need to
-- make a grade a Kleisli composition introduced invisible.  Structural, `QB 1`.
λ⇒ᶜ : (X : ℕ → Channel) → Certified (λ n → unit ⊗₀ X n) X
λ⇒ᶜ _ = (λ _ → λ⇒) , (λ _ → 1) , poly-const 1 , λ _ → qb-λ⇒

λ⇐ᶜ : (X : ℕ → Channel) → Certified X (λ n → unit ⊗₀ X n)
λ⇐ᶜ _ = (λ _ → λ⇐) , (λ _ → 1) , poly-const 1 , λ _ → qb-λ⇐

-- The presheaf action, levelwise.
subᶠ : Certified Y X → Homᶠ A Y B → Homᶠ A X B
subᶠ {B = B} s g n = sub (sim s n) {B n} ∘ g n

------------------------------------------------------------------------
-- Context pullback, with its cost

-- Absorbing a certified family into the context is `ctx-sub` at every level,
-- rebracketed: the EXACT substitution `simCost _ (cost s n)` in the allowance,
-- so it needs nothing of `ε`.
≈ctx-sub : (s : Certified Y X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (simCost q (cost s n))) ] subᶠ s g
≈ctx-sub s ε h =
  ≈ctxᴬ⇒≈ctx (λ n q → ε n (simCost q (cost s n)))
    λ n → ctx-sub (ε n) (cost s n) (sim-qb s n) (≈ctx⇒≈ctxᴬ ε h n)

-- Negligibility AFTER that substitution: `simCost _ cs` is polynomial in its
-- allowance whenever `cs` is, so the reindexed schedule has the same grade.
-- Proved, not assumed — the composition theorems reindex before they conclude.
NegligibleBound-simCost : (cs : ℕ → ℕ) → Poly cs → (ε : ℕ → ℕ → ℚ)
                        → NegligibleBound ε
                        → NegligibleBound (λ n q → ε n (simCost q (cs n)))
NegligibleBound-simCost cs Pcs =
  GradedBound-reindex Negligible (λ _ q → simCost q (cs _))
                      (λ p Pp → poly-* Pp (poly-⊔ Pcs (poly-const 1)))

------------------------------------------------------------------------
-- The emulation witness

infix 4 _≤UC^ωᵉ_ _≤UC^ωᵉ⁺_

-- Quantitative realization with everything the conclusion is derived from
-- KEPT: a certified simulator family, a negligible schedule, and the
-- contextual agreement at it.
_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Certified Y X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g

≤UC^ωᵉ-resp : {f f′ : Homᶠ A X B} {g g′ : Homᶠ A Y B}
            → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
            → f ≤UC^ωᵉ g → f′ ≤UC^ωᵉ g′
≤UC^ωᵉ-resp ef eg (s , ε , neg , e) =
  s , ε , neg , ≈ctx-resp ε ef (λ n → ∘-resp-≈ʳ (eg n)) e

-- …and the adversary-quantified form, at `Abstract2._≤UC_`'s quantifier order.
-- The adversary carries a certificate because absorbing it is what the
-- equivalence below costs: an uncertified adversary has no allowance
-- substitution to charge, where `Abstract2`'s qualitative order needs none.
_≤UC^ωᵉ⁺_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ⁺_ {X = X} {Y = Y} f g =
    {X′ : ℕ → Channel} (a : Certified X X′)
  → Σ[ s ∈ Certified Y X′ ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ]
      NegligibleBound ε × subᶠ a f ≈ctx[ ε ] subᶠ s g

-- `dummy-complete` with its cost: the adversary is absorbed into the test, so
-- the schedule the composite is read at is the witness's reindexed along
-- `simCost _ (cost a n)`, and that is the whole difference from the qualitative
-- statement.
≤UC^ωᵉ⇒⁺ : {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g → f ≤UC^ωᵉ⁺ g
≤UC^ωᵉ⇒⁺ {B = B} {g = g} (s , ε , neg , e) a =
    a ∘ᶜ s
  , (λ n q → ε n (simCost q (cost a n)))
  , NegligibleBound-simCost (cost a) (cost-poly a) ε neg
  , ≈ctx-resp (λ n q → ε n (simCost q (cost a n))) (λ _ → Equiv.refl) merge
              (≈ctx-sub a ε e)
  where
  merge : (n : ℕ) → sub (sim a n) {B n} ∘ sub (sim s n) {B n} ∘ g n
                  ≈ sub (sim a n ∘ sim s n) {B n} ∘ g n
  merge _ = sym-assoc ○ ∘-resp-≈ˡ (⟺ sub-homomorphism)

-- …and back, at the identity adversary, with the `sub id` it leaves in front
-- normalized away — `Abstract2.≤UC⇒dummy`'s step, the schedule untouched.
≤UC^ωᵉ⁺⇒ : {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ⁺ g → f ≤UC^ωᵉ g
≤UC^ωᵉ⁺⇒ {f = f} h =
  let s , ε , neg , e = h idᶜ
  in s , ε , neg , ≈ctx-resp ε (λ n → sub-identityˡ (f n)) (λ _ → Equiv.refl) e

------------------------------------------------------------------------
-- Composition, with the error kept

-- Sequential composition follows `Abstract2.≤UC-trans`'s simulator
-- construction and graded composition `Abstract2.UC-compose`'s, each `≈ᵁ` step
-- replaced by the kit above and each morphism the proof moves into a context
-- carrying a certificate.  Those two are untouched and stay unconditional.
module Compose where

  -- The second comparison is pulled back along the first simulator, so what is
  -- added to `ε₁` is `ε₂` read at `simCost _ (cost s₁)` and not `ε₂` itself;
  -- that, and the merged simulator, are `at-trans` at every level.
  ≤UC^ωᵉ-trans : {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
               → f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h
  ≤UC^ωᵉ-trans (s₁ , ε₁ , n₁ , e₁) (s₂ , ε₂ , n₂ , e₂) =
      s₁ ∘ᶜ s₂
    , (λ n q → ε₁ n q ℚ.+ ε₂′ n q)
    , GradedBound-+[ Negligible ] Negligible-+ ε₁ ε₂′ n₁
        (NegligibleBound-simCost (cost s₁) (cost-poly s₁) ε₂ n₂)
    , ≈ctxᴬ⇒≈ctx (λ n q → ε₁ n q ℚ.+ ε₂′ n q)
        λ n → at-trans (ε₁ n) (ε₂ n) (cost s₁ n) (sim-qb s₁ n)
                (≈ctx⇒≈ctxᴬ ε₁ e₁ n) (≈ctx⇒≈ctxᴬ ε₂ e₂ n)
    where
    ε₂′ : ℕ → ℕ → ℚ
    ε₂′ n q = ε₂ n (simCost q (cost s₁ n))

  -- A SPLIT regrading acts on a witness, which `Abstract2.Factor.≤UC-sub` is
  -- for the qualitative order and for the same reason: post-composing `sub c`
  -- is no congruence unless the simulator commutes with `c`, and a retraction
  -- `r` conjugates it.  The allowance substitution is `≈ctx-sub`'s — EXACT,
  -- `c` being absorbed into the test.
  ≤UC^ωᵉ-sub : (c : Certified X Z) (r : Certified Z X)
             → ((n : ℕ) → sim r n ∘ sim c n ≈ id)
             → {f g : Homᶠ A X B} → f ≤UC^ωᵉ g → subᶠ c f ≤UC^ωᵉ subᶠ c g
  ≤UC^ωᵉ-sub {B = B} c r inv {g = g} (s , ε , neg , e) =
      c ∘ᶜ s ∘ᶜ r
    , (λ n q → ε n (simCost q (cost c n)))
    , NegligibleBound-simCost (cost c) (cost-poly c) ε neg
    , ≈ctx-resp (λ n q → ε n (simCost q (cost c n))) (λ _ → Equiv.refl) strict
                (≈ctx-sub c ε e)
    where
    -- The conjugation, which is where the retraction is spent.
    grade : (n : ℕ) → (sim c n ∘ sim s n ∘ sim r n) ∘ sim c n ≈ sim c n ∘ sim s n
    grade n = assoc ○ ∘-resp-≈ʳ (assoc ○ (∘-resp-≈ʳ (inv n) ○ identityʳ))

    strict : (n : ℕ) → sub (sim c n) {B n} ∘ sub (sim s n) {B n} ∘ g n
                     ≈ sub (sim (c ∘ᶜ s ∘ᶜ r) n) {B n} ∘ sub (sim c n) {B n} ∘ g n
    strict n = begin
        sub (sim c n) ∘ sub (sim s n) ∘ g n            ≈⟨ sym-assoc ⟩
        (sub (sim c n) ∘ sub (sim s n)) ∘ g n          ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
        sub (sim c n ∘ sim s n) ∘ g n                  ≈⟨ sub-resp-≈ (⟺ (grade n)) ⟩∘⟨refl ⟩
        sub (sim (c ∘ᶜ s ∘ᶜ r) n ∘ sim c n) ∘ g n      ≈⟨ sub-homomorphism ⟩∘⟨refl ⟩
        (sub (sim (c ∘ᶜ s ∘ᶜ r) n) ∘ sub (sim c n)) ∘ g n  ≈⟨ assoc ⟩
        sub (sim (c ∘ᶜ s ∘ᶜ r) n) ∘ sub (sim c n) ∘ g n    ∎

  ----------------------------------------------------------------------
  -- Plugging processes around a relation

  infixr 8 _⊗ᶠ_
  infixr 9 _∙ᶠ_

  _⊗ᶠ_ : (ℕ → Channel) → (ℕ → Channel) → ℕ → Channel
  (X ⊗ᶠ P) n = X n ⊗₀ P n

  -- `Abstract2._∙_`, levelwise.
  _∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊗ᶠ P) C
  _∙ᶠ_ {X = X} k f n = ext (X n) (k n) ∘ f n

  -- Moving a CONTINUATION into the test: `ctx-absorb` at the continuation's own
  -- ancilla action, whose certificate `qb-T₁`/`qb-a⇒` pin at `ck ⊔ 1`, so the
  -- allowance moves by exactly `simCost _ ck`.
  ≈ctx-ext : (k : Homᶠ B P C) (ck : ℕ → ℕ) → ((n : ℕ) → QB (ck n) (k n))
           → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
           → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (ck n))) ] (k ∙ᶠ g)
  ≈ctx-ext {P = P} {C = C} {X = X} k ck qk ε h =
    ≈ctxᴬ⇒≈ctx (λ n q → ε n (simCost q (ck n))) λ n →
      ctx-absorb (ε n) (ck n) (λ W → id {W} ⊗₁ ext (X n) (k n)) (λ _ → qκ n)
                 (λ _ → split₂ʳ) (λ _ → split₂ʳ) (≈ctx⇒≈ctxᴬ ε h n)
    where
    norm : (n : ℕ) → (1 ℕ.* (ck n ℕ.⊔ 1)) ℕ.⊔ 1 ≡ ck n ℕ.⊔ 1
    norm n = trans (cong (ℕ._⊔ 1) (*-identityˡ (ck n ℕ.⊔ 1)))
                   (trans (⊔-assoc (ck n) 1 1) (cong (ck n ℕ.⊔_) (⊔-idem 1)))

    qκ : (n : ℕ) {W : Channel} → QB (ck n ℕ.⊔ 1) (id {W} ⊗₁ ext (X n) (k n))
    qκ n {W} = subst (λ j → QB j (id {W} ⊗₁ ext (X n) (k n))) (norm n)
                 (qb-T₁ (qb-∘ (qb-a⇒ {X n} {P n} {C n}) (qb-T₁ (qk n))))

  -- Moving the earlier PROCESS into the closure, `absorb-closureᵠ` at
  -- `∙-decomp` read the other way: the context of `u ∙ᶠ f` at ancilla `W` IS
  -- `u`'s context at ancilla `W ⊗ X`, with `f`'s own prefix pushed into the
  -- closure and the test rebracketed by `sub α⇒`.
  ≈ctx-pre : (f : Homᶠ A X B) (cf : ℕ → ℕ) → ((n : ℕ) → QB (cf n) (f n))
           → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
           → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (cf n))) ] (v ∙ᶠ f)
  ≈ctx-pre {A = A} {X = X} {B = B} {P = P} {C = C} f cf qf ε {u} {v} hy =
    agreeᵠ⇒≈ctx (λ n q → ε n (simCost q (cf n))) λ n W →
      absorb-closureᵠ (ε n) (cf n) (qb-sub {A = C n} (qb-a⇐ {W} {X n} {P n}))
        (qθ n W) (λ _ → cut n W (u n)) (λ _ → cut n W (v n))
        (≈ctx⇒agreeᵠ ε hy n (W ⊗₀ X n))
    where
    cut : (n : ℕ) (W : Channel) {E : T₀ (W ⊗₀ (X n ⊗₀ P n)) (C n) ⇒ Ω}
          (x : B n ⇒ T₀ (P n) (C n))
        → E ∘ prefixᵒ W (ext (X n) x ∘ f n)
        ≈ ((E ∘ sub (α⇒ {W} {X n} {P n}) {C n}) ∘ prefixᵒ (W ⊗₀ X n) x)
          ∘ prefixᵒ W (f n)
    cut n W x = (refl⟩∘⟨ ∙-decomp x (f n) W)
              ○ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ (μT x)) ⟩∘⟨refl)) ○ (refl⟩∘⟨ assoc)
              ○ sym-assoc ○ sym-assoc

    -- The bump past `ctxBudget`'s guard is `Query.guardᵠ`'s, so all that is
    -- left here is the prefix's own certificate.
    qθ : (n : ℕ) (W : Channel) → QB (cf n ℕ.⊔ 1) (prefixᵒ W (f n))
    qθ n W = subst (λ j → QB j (prefixᵒ W (f n))) (*-identityˡ (cf n ℕ.⊔ 1))
               (qb-∘ qμ qT)
      where
      qμ : QB 1 (μ W (X n) {B n})
      qμ = qb-resp-≈ (Equiv.sym (μ-α⇐ M W (X n))) (qb-a⇒ {W} {X n} {B n})

      qT : QB (cf n ℕ.⊔ 1) (T₁ W (f n))
      qT = qb-resp-≈ (Equiv.sym (T₁-⊗ M W (f n))) (qb-T₁ {W} (qf n))

  -- Plugging a process under the DOMAIN, where `≈ctx-pre` plugs one under the
  -- SUBROUTINE.  The closure absorbs it and at rate `0` that is free: the
  -- closure's budget becomes `(0 ⊔ 1) * c′`, which `ctxBudget` reads as `c′`
  -- itself, so the schedule is unchanged rather than reindexed.
  -- This is what puts a comparison at a CLOSED domain, with the resource the
  -- two sides must agree about moved out of the context's control
  -- (`docs/coin-toss.md` §5).
  ≈ctx-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
           → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ A X B} → u ≈ctx[ ε ] v
           → (λ n → u n ∘ p n) ≈ctx[ ε ] (λ n → v n ∘ p n)
  ≈ctx-dom {A = A} {X = X} {B = B} p qp ε {u} {v} hy = agreeᵠ⇒≈ctx ε λ n W →
    ≈ᵃ-resp₀ (λ _ → cast₀ (cut n W)) (λ _ → cast₀ (⟺ (cut n W)))
      (≈ᵃ-mono (λ q c′ → ℚₚ.≤-reflexive (cong (λ j → ε n (ctxBudget q j))
                                              (*-identityˡ c′)))
        (≈ᵃ-post (Tᵠ.pullᵠ (bud 1 (qθ n W))) (≈ctx⇒agreeᵠ ε hy n W)))
    where
    cut : (n : ℕ) (W : Channel) {x : A n ⇒ T₀ (X n) (B n)}
          {E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω}
        → E ∘ prefixᵒ W (x ∘ p n) ≈ (E ∘ prefixᵒ W x) ∘ T₁ W (p n)
    cut _ _ = (refl⟩∘⟨ ((refl⟩∘⟨ T-homomorphism) ○ sym-assoc)) ○ sym-assoc

    qθ : (n : ℕ) (W : Channel) → QB 1 (T₁ W (p n))
    qθ n W = qb-resp-≈ (Equiv.sym (T₁-⊗ M W (p n))) (qb-T₁ {W} (qp n))

  -- …hence on a whole witness, with the simulator and the schedule untouched.
  ≤UC^ωᵉ-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
             → {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g
             → (λ n → f n ∘ p n) ≤UC^ωᵉ (λ n → g n ∘ p n)
  ≤UC^ωᵉ-dom p qp (s , ε , neg , e) =
    s , ε , neg , ≈ctx-resp ε (λ _ → Equiv.refl) (λ _ → assoc) (≈ctx-dom p qp ε e)

  ----------------------------------------------------------------------
  -- Graded composition

  -- The ε-analogue of `Abstract2.UC-compose`, step by step.  Its two extra
  -- hypotheses are the certificates for the morphisms it moves: `f`, into the
  -- closure, and `v`, which with the simulator `t` in front of it goes into
  -- the test.
  UC-composeᵉ :
      {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
      (sf : Certified Y X) (εf : ℕ → ℕ → ℚ) → NegligibleBound εf
    → f ≈ctx[ εf ] subᶠ sf g
    → (t : Certified Q P) (εu : ℕ → ℕ → ℚ) → NegligibleBound εu
    → u ≈ctx[ εu ] subᶠ t v
    → (cf : ℕ → ℕ) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
    → (cv : ℕ → ℕ) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
    → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
  UC-composeᵉ {X = X} {B = B} {Y = Y} {P = P} {C = C} {Q = Q} {f = f} {g} {u} {v}
              sf εf nf ef t εu nu eu cf Pcf qf cv Pcv qv =
      s , (λ n q → εu′ n q ℚ.+ εf′ n q)
    , GradedBound-+[ Negligible ] Negligible-+ εu′ εf′
        (NegligibleBound-simCost cf Pcf εu nu)
        (NegligibleBound-simCost ctv Pctv εf nf)
    , ≈ctx-trans εu′ εf′ (≈ctx-pre f cf qf εu eu)
        (≈ctx-resp εf′ (λ _ → Equiv.refl) strict-final
                   (≈ctx-ext (subᶠ t v) ctv qtv εf ef))
    where
    ctv : ℕ → ℕ
    ctv n = (cost t n ℕ.⊔ 1) ℕ.* cv n

    εu′ εf′ : ℕ → ℕ → ℚ
    εu′ n q = εu n (simCost q (cf n))
    εf′ n q = εf n (simCost q (ctv n))

    Pctv : Poly ctv
    Pctv = poly-* (poly-⊔ (cost-poly t) (poly-const 1)) Pcv

    qtv : (n : ℕ) → QB (ctv n) (subᶠ t v n)
    qtv n = qb-∘ (qb-sub {A = C n} (sim-qb t n)) (qv n)

    s : Certified (Y ⊗ᶠ Q) (X ⊗ᶠ P)
    s = (λ n → id {X n} ⊗₁ sim t n ∘ sim sf n ⊗₁ id {Q n})
      , (λ n → (cost t n ℕ.⊔ 1) ℕ.* (cost sf n ℕ.⊔ 1))
      , poly-* (poly-⊔ (cost-poly t) (poly-const 1)) (poly-⊔ (cost-poly sf) (poly-const 1))
      , λ n → qb-∘ (qb-T₁ {X n} (sim-qb t n)) (qb-sub {A = Q n} (sim-qb sf n))

    strict-final : (n : ℕ)
                 → ext (X n) (sub (sim t n) {C n} ∘ v n) ∘ sub (sim sf n) {B n} ∘ g n
                   ≈ sub (sim s n) {C n} ∘ ext (Y n) (v n) ∘ g n
    strict-final n = begin
        ext (X n) (sub (sim t n) ∘ v n) ∘ sub (sim sf n) ∘ g n
          ≈⟨ sub-commute₂ ⟩∘⟨refl ⟩
        (sub (id ⊗₁ sim t n) ∘ ext (X n) (v n)) ∘ sub (sim sf n) ∘ g n
          ≈⟨ assoc ⟩
        sub (id ⊗₁ sim t n) ∘ ext (X n) (v n) ∘ sub (sim sf n) ∘ g n
          ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        sub (id ⊗₁ sim t n) ∘ (ext (X n) (v n) ∘ sub (sim sf n)) ∘ g n
          ≈⟨ refl⟩∘⟨ (sub-commute₁ ⟩∘⟨refl) ⟩
        sub (id ⊗₁ sim t n) ∘ (sub (sim sf n ⊗₁ id) ∘ ext (Y n) (v n)) ∘ g n
          ≈⟨ refl⟩∘⟨ assoc ⟩
        sub (id ⊗₁ sim t n) ∘ sub (sim sf n ⊗₁ id) ∘ ext (Y n) (v n) ∘ g n
          ≈⟨ sym-assoc ⟩
        (sub (id ⊗₁ sim t n) ∘ sub (sim sf n ⊗₁ id)) ∘ ext (Y n) (v n) ∘ g n
          ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
        sub (sim s n) ∘ ext (Y n) (v n) ∘ g n  ∎

  -- …and packaged at the witnesses, which nothing but the schedules' order
  -- stood in the way of.  What stays explicit is the certificates for the two
  -- moved morphisms: `_≤UC^ωᵉ_` bounds the SIMULATOR, not the homs compared.
  ≤UC^ωᵉ-∙ : {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
             (cf : ℕ → ℕ) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
           → (cv : ℕ → ℕ) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
           → f ≤UC^ωᵉ g → u ≤UC^ωᵉ v → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
  ≤UC^ωᵉ-∙ cf Pcf qf cv Pcv qv (sf , εf , nf , ef) (t , εu , nu , eu) =
    UC-composeᵉ sf εf nf ef t εu nu eu cf Pcf qf cv Pcv qv

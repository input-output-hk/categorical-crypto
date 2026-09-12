{-# OPTIONS --safe --without-K --guardedness #-}

-- The quantitative contextual relation on FAMILIES OF GRADED morphisms, and
-- the simulator-bearing emulation witness over it.
--
-- `_≈ctx[ ε ]_` is `UC.Asymptotic.Family._≈ᶠ[_]_` with its two restrictions
-- lifted — closed domain, unit grade — so the compared homs are arbitrary
-- `f n : A n ⇒ T₀ (X n) (B n)` and the context is the very one `_≈ᵁ_`
-- quantifies over.  `_≈ctxᴬ[ ε ]_` is the same experiment at the operational
-- bracket `W ⊗ (X ⊗ B)`, where the model's ingestion and extraction lemmas
-- live; `≈ctx⇒≈ctxᴬ`/`≈ctxᴬ⇒≈ctx` rebracket between them through
-- `UC.Model.Reading`, at a PROVED cost of `QB 1` on the test — the allowance
-- moves by `c * 1`, which is why the two carry the same `ε`.
--
-- Every other move a quantitative proof makes plugs a morphism into the
-- context, and each costs the same substitution: the allowance rescaled by that
-- morphism's own budget, `UC.Budget.simCost`.  `≈ctx-sub` is that for a
-- simulator; `UC.Asymptotic.Compose` has it for a continuation and for a
-- process moved into the closure.
--
-- Neither relation reads the compared homs' own query bounds — only the
-- context's, as `_≈ᶠ[_]_` already did.  `Certified` is where a bound on a hom
-- appears, and only on morphisms a theorem actually moves into a context.
-- `docs/quantitative-family.md` is the design note, including the two measured
-- reasons this module is spelled as it is.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const; poly-⊔)
open import Data.Nat.Properties using (*-identityʳ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import ProbabilisticLogic.Dp.Advantage
  using (_≈ₚ[_]_; ≈ₚ[]-mono; ≈ₚ[]-refl; ≈ₚ[]-resp; ≈ₚ[]-sym; ≈ₚ[]-trans; ≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.UC.Approximate
  using (GradedBound-reindex; Negligible; NegligibleBound)
open import CategoricalCrypto.UC.Budget
  using (Budget; ctxBudget; ctxBudget-absorb; simCost)
open import CategoricalCrypto.UC.Model.Dominated using (T₁ᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; obs-resp; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Reading using (shuffle⇐; shuffle⇒)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Asymptotic.Contextual where

open Budget budgetᵒ using (QB; qb-id; qb-∘; qb-a⇒; qb-a⇐; qb-sub; qb-T₁)
open HomReasoning

private variable
  A B X Y Z : ℕ → Channel
  ε δ : ℕ → ℕ → ℚ

------------------------------------------------------------------------
-- Families of graded morphisms, and the contextual relation

-- One hom of the model per level, each at its own domain, adversary grade and
-- codomain.  `UC.Asymptotic.Family`'s protocol images are the special case
-- `A = Δ 𝟘ᵒ`, `X = Δ 𝟘ᴳ`.
Homᶠ : (A X B : ℕ → Channel) → Set₁
Homᶠ A X B = (n : ℕ) → A n ⇒ T₀ (X n) (B n)

-- `Abstract2.Action.prefix` at this setup, spelled out.  Naming the generic
-- action instead costs a module application of `Abstract2.Action` at
-- `StdSetup` — measured, +22 s on this module — and the lemmas that consume it
-- (`sub-decomp`, `∙-decomp`, `UC.Model.Reading`'s shuffles) are stated at this
-- spelling anyway.
prefixᵒ : (W : Channel) {A′ B′ X′ : Channel} → A′ ⇒ T₀ X′ B′ → T₀ W A′ ⇒ T₀ (W ⊗₀ X′) B′
prefixᵒ W {X′ = X′} f = μ W X′ ∘ T₁ W f

infix 4 _≈ctx[_]_ _≈ctxᴬ[_]_

-- At each level, no budgeted ancilla context separates the two homs by more
-- than `ε` read at the budget the context's two legs CARRY.  `W`, the test and
-- the closure are quantified per LEVEL, not as a family of contexts — that is
-- the uniform refinement `_≈ᶠ[_]_` already took and the ledger consumer needs.
_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set₁
_≈ctx[_]_ {A} {X} {B} f ε g =
    (n : ℕ) (W : Channel) (E : T₀ (W ⊗₀ X n) (B n) ⇒ Ωᵒ) (m : 𝟘ᵒ ⇒ T₀ W (A n))
    {c c′ : ℕ} → QB c E → QB c′ m
  → Obs ((E ∘ prefixᵒ W (f n)) ∘ m) ≈ₚ[ ε n (ctxBudget c c′) ]
    Obs ((E ∘ prefixᵒ W (g n)) ∘ m)

-- …and the same experiment with the test's domain bracketed the other way,
-- which is the bracket the model's ingestion (`UC.Model.Dominated`) and
-- extraction (`UC.Seam.Audit.Context`) lemmas are stated at.
_≈ctxᴬ[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set₁
_≈ctxᴬ[_]_ {A} {X} {B} f ε g =
    (n : ℕ) (W : Channel) (E : T₀ W (T₀ (X n) (B n)) ⇒ Ωᵒ) (m : 𝟘ᵒ ⇒ T₀ W (A n))
    {c c′ : ℕ} → QB c E → QB c′ m
  → Obs ((E ∘ T₁ᵒ W (f n)) ∘ m) ≈ₚ[ ε n (ctxBudget c c′) ]
    Obs ((E ∘ T₁ᵒ W (g n)) ∘ m)

------------------------------------------------------------------------
-- Rebracketing, with its cost

-- The adapter is `UC.Model.Reading`'s associator shuffle, and what it costs the
-- context is one structural morphism in front of the test — `QB 1`, so the
-- test's own budget `c` becomes `c * 1` and the allowance `ctxBudget c c′` is
-- unchanged (`*-identityʳ`).  The query certificates are transported with the
-- observation, not assumed to survive the isomorphism.

≈ctx⇒≈ctxᴬ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → f ≈ctxᴬ[ ε ] g
≈ctx⇒≈ctxᴬ ε {f} {g} h n W E m {c} {c′} qE qm =
  subst (λ k → _ ≈ₚ[ ε n (ctxBudget k c′) ] _) (*-identityʳ c)
    (≈ₚ[]-resp (obs-resp (shuffle⇒ (f n) E m ○ sym-assoc))
               (obs-resp (shuffle⇒ (g n) E m ○ sym-assoc))
               (h n W (E ∘ α⇒) m (qb-∘ qE qb-a⇐) qm))

≈ctxᴬ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctxᴬ[ ε ] g → f ≈ctx[ ε ] g
≈ctxᴬ⇒≈ctx ε {f} {g} h n W E m {c} {c′} qE qm =
  subst (λ k → _ ≈ₚ[ ε n (ctxBudget k c′) ] _) (*-identityʳ c)
    (≈ₚ[]-resp (obs-resp (⟺ (shuffle⇐ (f n) E m ○ sym-assoc)))
               (obs-resp (⟺ (shuffle⇐ (g n) E m ○ sym-assoc)))
               (h n W (E ∘ α⇐) m (qb-∘ qE qb-a⇒) qm))

------------------------------------------------------------------------
-- The enrichment kit

private
  -- The whole context respects the ambient hom equality, `prefixᵒ` included.
  ctx-resp : {A′ B′ X′ : Channel} {f g : A′ ⇒ T₀ X′ B′} (W : Channel)
             (E : T₀ (W ⊗₀ X′) B′ ⇒ Ωᵒ) (m : 𝟘ᵒ ⇒ T₀ W A′)
           → f ≈ g → (E ∘ prefixᵒ W f) ∘ m ≈ (E ∘ prefixᵒ W g) ∘ m
  ctx-resp _ _ _ eq = ∘-resp-≈ˡ (∘-resp-≈ʳ (∘-resp-≈ʳ (T-resp-≈ eq)))

≈ctx-resp : (ε : ℕ → ℕ → ℚ) {f f′ g g′ : Homᶠ A X B}
          → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
          → f ≈ctx[ ε ] g → f′ ≈ctx[ ε ] g′
≈ctx-resp _ ef eg h n W E m qE qm =
  ≈ₚ[]-resp (obs-resp (ctx-resp W E m (ef n))) (obs-resp (ctx-resp W E m (eg n)))
            (h n W E m qE qm)

-- Zero error is exactly the ambient hom equality, which the model observes
-- EXACTLY (`obs-resp`).  The inherited `_≈ᵁ_` does NOT give it: at this model
-- it only puts the two runs within every POSITIVE error, so it has no zero
-- instance to hand over — `≈ᵁ⇒≈ctx` is where that schedule is paid for.
≈C⇒≈ctx : {f g : Homᶠ A X B} → ((n : ℕ) → f n ≈ g n) → f ≈ctx[ (λ _ _ → 0ℚ) ] g
≈C⇒≈ctx e n W E m _ _ = ≈ₚ⇒≈ₚ[0] (obs-resp (ctx-resp W E m (e n)))

≈ctx-refl : {f : Homᶠ A X B} → f ≈ctx[ (λ _ _ → 0ℚ) ] f
≈ctx-refl _ _ _ _ _ _ = ≈ₚ[]-refl

≈ctx-sym : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → g ≈ctx[ ε ] f
≈ctx-sym _ h n W E m qE qm = ≈ₚ[]-sym (h n W E m qE qm)

≈ctx-trans : (ε δ : ℕ → ℕ → ℚ) {f g h : Homᶠ A X B} → f ≈ctx[ ε ] g → g ≈ctx[ δ ] h
           → f ≈ctx[ (λ n q → ε n q ℚ.+ δ n q) ] h
≈ctx-trans _ _ p q n W E m qE qm = ≈ₚ[]-trans (p n W E m qE qm) (q n W E m qE qm)

-- Reading the same agreement at a larger SCHEDULE, which needs nothing of `ε`.
-- Reading it at a larger ALLOWANCE is the move that needs `Allowance-mono`.
≈ctx-≤ : (ε δ : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → ((n q : ℕ) → ε n q ℚ.≤ δ n q)
       → f ≈ctx[ ε ] g → f ≈ctx[ δ ] g
≈ctx-≤ _ _ le h n W E m qE qm = ≈ₚ[]-mono (le n _) (h n W E m qE qm)

-- The inherited `_≈ᵁ_` at every level, ingested at a chosen POSITIVE schedule;
-- `UC.Asymptotic.Family.uc-≈ᶠ[_]` is this read at the protocol images.
≈ᵁ⇒≈ctx : {f g : Homᶠ A X B} (ν : ℕ → ℚ) → ((n : ℕ) → 0ℚ ℚ.< ν n)
        → ((n : ℕ) → f n ≈ᵁ g n) → f ≈ctx[ (λ n _ → ν n) ] g
≈ᵁ⇒≈ctx ν pos u n W E m _ _ = KE.run∼ (u n W) {E} m (ν n) (pos n)

------------------------------------------------------------------------
-- Certified families of grade morphisms

-- A grade-morphism family with a polynomial query certificate: the asymptotic
-- spelling of `UC.Audit._≤UC[_]_`'s `sim`/`sim-qb` pair, and exactly the data a
-- `UC.Family`-hom is a hom plus.
--
-- A Σ and not a record, for a MEASURED reason: a record field
-- `sim-qb : (n : ℕ) → QB (cost n) (sim n)` depending on two earlier fields
-- exhausts a 20 GiB heap here, where the Σ whose second component binds those
-- two checks in seconds.  `UC.Audit`'s record is fine because its `QB` is a
-- module parameter; at this model `QB` is `budgetᵒ`'s, whose transport across
-- the seal cannot be inverted.
Certified : (A B : ℕ → Channel) → Set₁
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

-- The presheaf action on a certified family, levelwise.
subᶠ : Certified Y X → Homᶠ A Y B → Homᶠ A X B
subᶠ {B = B} s g n = sub (sim s n) {B n} ∘ g n

------------------------------------------------------------------------
-- Context pullback, with its cost

-- Absorbing a certified family into the context.  `sub-decomp` slides it off
-- the process and in front of the test, where `qb-T₁`/`qb-sub` certify it at
-- `(cs ⊔ 1) ⊔ 1`; the allowance the context's two legs then afford is
-- `simCost _ (cost s n)` of the old one (`UC.Budget.ctxBudget-absorb`).  This
-- is the EXACT substitution, not a bound, so it needs nothing of `ε`.
≈ctx-sub : (s : Certified Y X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (simCost q (cost s n))) ] subᶠ s g
≈ctx-sub {A = A} {B = B} s ε {f} {g} h n W E m {c} {c′} qE qm =
  ≈ₚ[]-resp (obs-resp (⟺ (slide (f n)))) (obs-resp (⟺ (slide (g n)))) inner
  where
  E′ : T₀ (W ⊗₀ _) (B n) ⇒ Ωᵒ
  E′ = E ∘ sub (ℐ.id {W} ⊗₁ sim s n) {B n}

  slide : (x : A n ⇒ T₀ _ (B n))
        → (E ∘ prefixᵒ W (sub (sim s n) {B n} ∘ x)) ∘ m ≈ (E′ ∘ prefixᵒ W x) ∘ m
  slide x = ∘-resp-≈ˡ (∘-resp-≈ʳ (sub-decomp (sim s n) x W) ○ sym-assoc)

  inner : Obs ((E′ ∘ prefixᵒ W (f n)) ∘ m)
            ≈ₚ[ ε n (simCost (ctxBudget c c′) (cost s n)) ]
          Obs ((E′ ∘ prefixᵒ W (g n)) ∘ m)
  inner = subst (λ k → Obs ((E′ ∘ prefixᵒ W (f n)) ∘ m) ≈ₚ[ ε n k ]
                       Obs ((E′ ∘ prefixᵒ W (g n)) ∘ m))
                (ctxBudget-absorb c c′ (cost s n))
                (h n W E′ m (qb-∘ qE (qb-sub (qb-T₁ (sim-qb s n)))) qm)

-- Negligibility AFTER that substitution: `simCost _ cs` is polynomial in its
-- allowance whenever `cs` is, so the reindexed schedule has the same grade.
-- Proved, not assumed — the composition theorems reindex before they conclude.
NegligibleBound-simCost : (cs : ℕ → ℕ) → Poly cs → (ε : ℕ → ℕ → ℚ)
                        → NegligibleBound ε
                        → NegligibleBound (λ n q → ε n (simCost q (cs n)))
NegligibleBound-simCost cs Pcs =
  GradedBound-reindex Negligible (λ _ q → simCost q (cs _))
                      (λ p Pp → poly-* Pp (poly-⊔ Pcs (poly-const 1)))

-- What reindexing along an INEQUALITY of allowances spends.  It is a premise
-- and not a fact: `NegligibleBound` constrains `ε` at each allowance separately
-- and says nothing about their order, so an arbitrary schedule is not monotone
-- by fiat.  Only the horizontal composition needs it — the absorptions above
-- substitute exactly.
Allowance-mono : (ℕ → ℕ → ℚ) → Set
Allowance-mono ε = (n : ℕ) {q q′ : ℕ} → q ℕ.≤ q′ → ε n q ℚ.≤ ε n q′

------------------------------------------------------------------------
-- The emulation witness

infix 4 _≤UC^ωᵉ_ _≤UC^ωᵉ⁺_

-- Quantitative realization with everything the conclusion is derived from
-- KEPT: a certified simulator family, a negligible schedule, and the
-- contextual agreement at it.  `UC.Asymptotic.Family._≤UC^ωⁿ_` is this with no
-- simulator to absorb (`≤UC^ωⁿ⇒≤UC^ωᵉ` there).
_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set₁
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Certified Y X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g

-- …and the adversary-quantified form, at `Abstract2._≤UC_`'s quantifier order.
-- The adversary carries a certificate because absorbing it is what the
-- equivalence below costs: an uncertified adversary has no allowance
-- substitution to charge, where `Abstract2`'s qualitative order needs none.
_≤UC^ωᵉ⁺_ : Homᶠ A X B → Homᶠ A Y B → Set₁
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

-- …and back, at the identity adversary, with the `sub ℐ.id` it leaves in front
-- normalized away — `Abstract2.≤UC⇒dummy`'s step, with the schedule untouched
-- (the identity adversary substitutes nothing).
≤UC^ωᵉ⁺⇒ : {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ⁺ g → f ≤UC^ωᵉ g
≤UC^ωᵉ⁺⇒ {f = f} h =
  let s , ε , neg , e = h idᶜ
  in s , ε , neg , ≈ctx-resp ε (λ n → sub-identityˡ (f n)) (λ _ → Equiv.refl) e

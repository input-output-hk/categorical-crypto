{-# OPTIONS --safe --without-K #-}

-- The quantitative contextual relation on FAMILIES of graded morphisms, the
-- simulator-bearing emulation witness over it and its composition laws, at any
-- monoidal base carrying a graded subcategory of rate-certified morphisms and
-- an approximate observation.
-- `UC.Model.Family.Contextual`/`.Compose` are this module at the sealed
-- machine.
--
-- `_≈ctx[ ε ]_` compares arbitrary `f n : A n ⇒ T₀ (X n) (B n)` through the
-- very context `_≈ᵁ_` quantifies over, at the allowance the context affords —
-- its test's rate scaled by its closure's; `_≈ctxᴬ[ ε ]_` is
-- `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` at every level, the same experiment at the operational bracket `W ⊗ (X ⊗ B)` where a
-- model's ingestion and extraction lemmas live.
--
-- Both relations are `UC.Quantitative.Contextual.Agreeᵠ` — the admitted
-- agreement of two test-pullbacks — at their two brackets, so every move that
-- plugs a morphism into a context is one of that module's two absorptions and
-- costs the allowance rescaled by the plugged morphism's own rate,
-- `Data.Nat.Positive.scale`.  Every such substitution is EXACT, so no theorem
-- below reads `ε` at an inequality of allowances.
--
-- Neither relation reads the compared homs' own rates, only the context's.
-- `Certified` is where a rate on a hom appears, and a moved morphism is asked
-- for an `Image` certificate while the theorem stays about the bare
-- morphism.
--
-- The primary quantitative interface is `_≤UC[ s , ε ]_`, the agreement at a
-- NAMED simulator family and a NAMED schedule; every composition theorem is
-- proved there, at a published error formula (`seqError`, `composeError`),
-- and `_≤UC^ωᵉ_` packages one with its negligibility classification.
-- `docs/quantitative-family.md` is the design note.

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.LocallyGraded
open import Categories.LocallyGraded.Family using (module Families)
open import Categories.LocallyGraded.Monoidal
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
  using (ℕ⁺; 1⁺; _·_; poly⁺-1; poly⁺-·; poly-scale; Poly⁺; scale; scale-unit; value)
open import Data.Nat.Properties using (*-identityʳ; *-identityˡ; ≤-refl; ≤-reflexive)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered; ≈[]-resp₀)
open import CategoricalCrypto.UC.Approximate
  using ( Approximation; GradedBound-+[_]; GradedBound-reindex; Negligible
        ; Negligible-+; NegligibleBound; ℚ-errors )
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)

import CategoricalCrypto.Approx.Evaluation as Evaluationᴹ
import CategoricalCrypto.Standard2 as Std2
import Data.Rational.Properties as ℚₚ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Quantitative.Family
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : Evaluationᴹ.QEvaluation ℚ-ordered (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  {_∼_ : Rel (Evaluationᴹ.QEvaluation.Carrier qro) ℓs}
  (∼-isEquivalence : IsEquivalence _∼_)
  (∼-from-zero : {x y : Evaluationᴹ.QEvaluation.Carrier qro}
               → Evaluationᴹ.QEvaluation._≈[_]_ qro x 0ℚ y → x ∼ y)
  (reflects : {x y : Evaluationᴹ.QEvaluation.Carrier qro}
            → x ∼ y → Evaluationᴹ.QEvaluation._∼ᵃ_ qro x y)
  where

private module Qr = Evaluationᴹ.QEvaluation qro

Ap : Approximation Qr.Carrier ℚ-errors ℓa
Ap = Qr.approx

readout : Evaluation (MonoidalCategory.U M) os ℓs
readout = Evaluationᴹ.qualBy ℚ-ordered qro ∼-isEquivalence ∼-from-zero

open import CategoricalCrypto.UC.Quantitative.Contextual M Rg Ap
  Qr.J Qr.Ω Qr.read Qr.read-resp₀
open import CategoricalCrypto.UC.Quantitative.Query using (module Fl)

open Evaluation readout
open Std2.StdUC M (Observable.ℰᴼ observable)
open Approximation Ap
open GradedSubCat Rg
open GradedMonoidal (monoidalᴸ Rates.braided) using () renaming
  (_⊗₁_ to _⊗ʰ_; α⇒ to α⇒ʰ; α⇐ to α⇐ʰ; λ⇒ to λ⇒ʰ)
open Fl
open HomReasoning
open MonR monoidal using (split₂ʳ)
open MR ∣machines∣

private variable A B C X Y Z P Q : ℕ → Channel

------------------------------------------------------------------------
-- Families of graded morphisms, and the contextual relation

Homᶠ : (A X B : ℕ → Channel) → Set ℓ
Homᶠ A X B = (n : ℕ) → A n ⇒ T₀ (X n) (B n)

-- `UCSetup.prefix`, spelled out: naming the generic action instead costs a
-- module application of `AbstractUC` at the consuming setup — measured, +22 s
-- at the machine — and the lemmas that consume it are stated at this spelling
-- anyway.
prefixᵒ : (W : Channel) {A′ B′ X′ : Channel} → A′ ⇒ T₀ X′ B′ → T₀ W A′ ⇒ T₀ (W ⊗₀ X′) B′
prefixᵒ W {X′ = X′} f = μ W X′ ∘ T₁ W f

infix 4 _≈ctx[_]_ _≈ctxᴬ[_]_

-- At each level, no certified ancilla context separates the two homs by more
-- than `ε` read at the allowance the context affords.  `W`, the test and
-- the closure are quantified per LEVEL, not as a family of contexts — that is
-- the uniform refinement the ledger consumer needs.
_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≈ctx[_]_ {A} {X} {B} f ε g =
    (n : ℕ) (W : Channel) (E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω) (m : J ⇒ T₀ W (A n))
    {c r′ : ℕ⁺} → Image forget c E → Image forget r′ m
  → read ((E ∘ prefixᵒ W (f n)) ∘ m) ≈[ ε n (value (c · r′)) ]
    read ((E ∘ prefixᵒ W (g n)) ∘ m)

-- …and the same experiment with the test's domain bracketed the other way,
-- which is the single-level relation at each `n`.
_≈ctxᴬ[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
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
  -- A bound survives a zero-error change of either endpoint (`read-resp₀`).
  splice : {u u′ v v′ : J ⇒ Ω} {ε : ℚ}
         → u ≈ u′ → v ≈ v′ → read u ≈[ ε ] read v → read u′ ≈[ ε ] read v′
  splice p q = ≈[]-resp₀ ℚ-ordered Ap (Qr.read-resp₀ (⟺ p)) (Qr.read-resp₀ q)

------------------------------------------------------------------------
-- Rebracketing, with its cost

-- The adapter is an associator, and what it costs the context is one
-- structural morphism in front of the test — rate `1⁺`, so the test's
-- certificate at `c` composes to one at `1⁺ · c`, regraded back to `c`, which is
-- why the two relations carry the same `ε`.  The certificates are transported,
-- not assumed to survive the isomorphism.

≈ctx⇒≈ctxᴬ : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g → f ≈ctxᴬ[ ε ] g
≈ctx⇒≈ctxᴬ ε {f} {g} h n W E m {c} (Ê , Ê≈E) qm =
  splice (pullʳ (cancelˡ associator.isoʳ) ⟩∘⟨refl)
         (pullʳ (cancelˡ associator.isoʳ) ⟩∘⟨refl)
         (h n W (E ∘ α⇒) m {c}
            (L.sub[ ≤-reflexive (*-identityˡ (value c)) ] (Ê L.∙ α⇒ʰ) , ∘-resp-≈ˡ Ê≈E) qm)

≈ctxᴬ⇒≈ctx : (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctxᴬ[ ε ] g → f ≈ctx[ ε ] g
≈ctxᴬ⇒≈ctx ε {f} {g} h n W E m {c} (Ê , Ê≈E) qm =
  splice (assoc ⟩∘⟨refl) (assoc ⟩∘⟨refl)
         (h n W (E ∘ α⇐) m {c}
            (L.sub[ ≤-reflexive (*-identityˡ (value c)) ] (Ê L.∙ α⇐ʰ) , ∘-resp-≈ˡ Ê≈E) qm)

------------------------------------------------------------------------
-- The enrichment kit

private
  ctx-cong : {A′ B′ X′ : Channel} {f g : A′ ⇒ T₀ X′ B′} (W : Channel)
             (E : T₀ (W ⊗₀ X′) B′ ⇒ Ω) (m : J ⇒ T₀ W A′)
           → f ≈ g → (E ∘ prefixᵒ W f) ∘ m ≈ (E ∘ prefixᵒ W g) ∘ m
  ctx-cong _ _ _ eq = ∘-resp-≈ˡ (∘-resp-≈ʳ (∘-resp-≈ʳ (T-resp-≈ eq)))

≈ctx-resp : (ε : ℕ → ℕ → ℚ) {f f′ g g′ : Homᶠ A X B}
          → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
          → f ≈ctx[ ε ] g → f′ ≈ctx[ ε ] g′
≈ctx-resp _ ef eg h n W E m qE qm =
  splice (ctx-cong W E m (ef n)) (ctx-cong W E m (eg n)) (h n W E m qE qm)

-- Zero error is exactly the ambient hom equality, which the base reads
-- EXACTLY.  The inherited `_≈ᵁ_` does NOT give it: it only puts the two runs
-- within every POSITIVE error, so it has no zero instance to hand over —
-- `≈ᵁ⇒≈ctx` is where that schedule is paid for.
≈C⇒≈ctx : {f g : Homᶠ A X B} → ((n : ℕ) → f n ≈ g n) → f ≈ctx[ (λ _ _ → 0ℚ) ] g
≈C⇒≈ctx e n W E m _ _ = Qr.read-resp₀ (ctx-cong W E m (e n))

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

-- A grade-morphism family with a polynomial rate schedule: the asymptotic
-- spelling of `UC.Audit._≤UC[_]_`'s `sim`, and `Categories.LocallyGraded.Family`'s
-- family hom at `(ℕ , id)`, whose composite and unit it reuses.  A Σ and not a
-- record, for a MEASURED reason: a record field depending on two earlier fields
-- exhausts a 20 GiB heap at the sealed machine, where the Σ whose second
-- component binds those two checks in seconds.
private module Cᶠ = Families Rg ℕ (λ n → n) Poly⁺ poly⁺-1 (λ {s} {t} → poly⁺-· {s} {t})

Certified : (A B : ℕ → Channel) → Set (ℓ ⊔ qs)
Certified = Cᶠ._⇒^ω_

sim : Certified A B → (n : ℕ) → A n ⇒ B n
sim s n = ⌊ Cᶠ.hom s n ⌋

cost : Certified A B → ℕ → ℕ⁺
cost = Cᶠ.schedOf

cost-poly : (s : Certified A B) → Poly⁺ (cost s)
cost-poly = Cᶠ.schedOf-adm

infixr 9 _∘ᶜ_

idᶜ : Certified X X
idᶜ = Category.id Cᶠ.Fam

_∘ᶜ_ : Certified Y Z → Certified X Y → Certified X Z
_∘ᶜ_ = Category._∘_ Cᶠ.Fam

-- The unit regrading, which `≈ctx-sub` needs to make a grade a Kleisli
-- composition introduced invisible.  Structural, at rate `1⁺`.
λ⇒ᶜ : (X : ℕ → Channel) → Certified (λ n → unit ⊗₀ X n) X
λ⇒ᶜ _ = Cᶠ.unit^ω λ _ → λ⇒ʰ

-- The presheaf action, levelwise.
subᶠ : Certified Y X → Homᶠ A Y B → Homᶠ A X B
subᶠ {B = B} s g n = sub (sim s n) {B n} ∘ g n

------------------------------------------------------------------------
-- Context pullback, with its cost

-- Absorbing a certified family into the context is `ctx-sub` at every level,
-- rebracketed: the EXACT substitution `scale _ (cost s n)` in the allowance,
-- so it needs nothing of `ε`.
≈ctx-sub : (s : Certified Y X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (scale q (cost s n))) ] subᶠ s g
≈ctx-sub s ε h =
  ≈ctxᴬ⇒≈ctx (λ n q → ε n (scale q (cost s n)))
    λ n → ctx-sub (ε n) (cost s n) (Cᶠ.hom s n , Equiv.refl) (≈ctx⇒≈ctxᴬ ε h n)

-- Negligibility AFTER that substitution: `scale _ r` is polynomial in its
-- allowance whenever `r` is, so the reindexed schedule has the same grade.
-- Proved, not assumed — the composition theorems reindex before they conclude.
NegligibleBound-scale : (r : ℕ → ℕ⁺) → Poly⁺ r → (ε : ℕ → ℕ → ℚ)
                      → NegligibleBound ε
                      → NegligibleBound (λ n q → ε n (scale q (r n)))
NegligibleBound-scale r Pr =
  GradedBound-reindex Negligible (λ n q → scale q (r n)) (λ p Pp → poly-scale {p} {r} Pp Pr)

------------------------------------------------------------------------
-- Fixed-data simulation bounds

infix 4 _≤UC[_,_]_

-- The quantitative certificate with BOTH its data NAMED — the simulator family
-- and the schedule are parameters here, not existentials, and no negligibility
-- is asked of `ε`: a finite-parameter bound means what it says on its own.
-- Every theorem below is proved at this relation and packaged into `_≤UC^ωᵉ_`
-- afterwards.  `UC.Quantitative.Witness.At` is a different construction — the
-- nonexpansive single-level one at a `QUCSetup` — and is not identified here.
_≤UC[_,_]_ : Homᶠ A X B → Certified Y X → (ℕ → ℕ → ℚ) → Homᶠ A Y B
           → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≤UC[ s , ε ] g = f ≈ctx[ ε ] subᶠ s g

≤UC[]-resp : (s : Certified Y X) (ε : ℕ → ℕ → ℚ)
             {f f′ : Homᶠ A X B} {g g′ : Homᶠ A Y B}
           → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
           → f ≤UC[ s , ε ] g → f′ ≤UC[ s , ε ] g′
≤UC[]-resp _ ε ef eg = ≈ctx-resp ε ef λ n → ∘-resp-≈ʳ (eg n)

------------------------------------------------------------------------
-- The emulation witness

infix 4 _≤UC^ωᵉ_ _≤UC^ωᵉ⁺_

-- The bound above with its two data hidden and the schedule classified:
-- quantitative realization with everything the conclusion is derived from
-- KEPT.
_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Certified Y X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≤UC[ s , ε ] g

≤UC^ωᵉ-resp : {f f′ : Homᶠ A X B} {g g′ : Homᶠ A Y B}
            → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
            → f ≤UC^ωᵉ g → f′ ≤UC^ωᵉ g′
≤UC^ωᵉ-resp ef eg (s , ε , neg , e) = s , ε , neg , ≤UC[]-resp s ε ef eg e

-- …and the adversary-quantified form, at `Abstract2._≤UC_`'s quantifier order.
-- The adversary carries a certificate because absorbing it is what the
-- equivalence below costs: an uncertified adversary has no allowance
-- substitution to charge, where `Abstract2`'s qualitative order needs none.
_≤UC^ωᵉ⁺_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ⁺_ {X = X} {Y = Y} f g =
    {X′ : ℕ → Channel} (a : Certified X X′)
  → Σ[ s ∈ Certified Y X′ ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ]
      NegligibleBound ε × subᶠ a f ≈ctx[ ε ] subᶠ s g

-- `dummy-complete` with its cost: the adversary is absorbed into the test, so
-- the schedule the composite is read at is the witness's reindexed along
-- `scale _ (cost a n)`, and that is the whole difference from the qualitative
-- statement.
≤UC^ωᵉ⇒⁺ : {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g → f ≤UC^ωᵉ⁺ g
≤UC^ωᵉ⇒⁺ {B = B} {g = g} (s , ε , neg , e) a =
    a ∘ᶜ s
  , (λ n q → ε n (scale q (cost a n)))
  , NegligibleBound-scale (cost a) (cost-poly a) ε neg
  , ≈ctx-resp (λ n q → ε n (scale q (cost a n))) (λ _ → Equiv.refl) merge
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
--
-- Each is proved at `_≤UC[_,_]_`, where the composed simulator and the
-- composed schedule are the theorem's OUTPUT DATA and no negligibility is
-- asked; the `_≤UC^ωᵉ_` form below it adds only the classification of that
-- schedule, and is where the two polynomials are spent.
module Compose where

  -- The second comparison is pulled back along the first simulator, so what is
  -- added to `ε` is `δ` read at `scale _ (cost s)` and not `δ` itself.
  seqError : Certified Y X → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
  seqError s ε δ n q = ε n q ℚ.+ δ n (scale q (cost s n))

  seqError-negligible : (s : Certified Y X) (ε δ : ℕ → ℕ → ℚ)
                      → NegligibleBound ε → NegligibleBound δ
                      → NegligibleBound (seqError s ε δ)
  seqError-negligible s ε δ nε nδ =
    GradedBound-+[ Negligible ] Negligible-+ ε (λ n q → δ n (scale q (cost s n))) nε
      (NegligibleBound-scale (cost s) (cost-poly s) δ nδ)

  -- …and that, with the merged simulator, is `at-trans` at every level.
  ≤UC[]-trans : (s : Certified Y X) (t : Certified Z Y) (ε δ : ℕ → ℕ → ℚ)
                {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
              → f ≤UC[ s , ε ] g → g ≤UC[ t , δ ] h
              → f ≤UC[ s ∘ᶜ t , seqError s ε δ ] h
  ≤UC[]-trans s _ ε δ e₁ e₂ =
    ≈ctxᴬ⇒≈ctx (seqError s ε δ)
      λ n → at-trans (ε n) (δ n) (cost s n) (Cᶠ.hom s n , Equiv.refl)
              (≈ctx⇒≈ctxᴬ ε e₁ n) (≈ctx⇒≈ctxᴬ δ e₂ n)

  ≤UC^ωᵉ-trans : {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
               → f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h
  ≤UC^ωᵉ-trans (s₁ , ε₁ , n₁ , e₁) (s₂ , ε₂ , n₂ , e₂) =
      s₁ ∘ᶜ s₂ , seqError s₁ ε₁ ε₂ , seqError-negligible s₁ ε₁ ε₂ n₁ n₂
    , ≤UC[]-trans s₁ s₂ ε₁ ε₂ e₁ e₂

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
  -- ancilla action, certified by whiskering its certificate at rate `1⁺`, so
  -- the allowance moves by exactly `scale _ (rk n)`.
  ≈ctx-ext : (k : Homᶠ B P C) (rk : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rk n) (k n))
           → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
           → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rk n))) ] (k ∙ᶠ g)
  ≈ctx-ext {P = P} {C = C} {X = X} k rk ck ε h =
    ≈ctxᴬ⇒≈ctx (λ n q → ε n (scale q (rk n))) λ n →
      ctx-absorb (ε n) (rk n) (λ W → id {W} ⊗₁ ext (X n) (k n)) (λ _ → cκ n)
                 (λ _ → split₂ʳ) (λ _ → split₂ʳ) (≈ctx⇒≈ctxᴬ ε h n)
    where
    cκ : (n : ℕ) {W : Channel} → Image forget (rk n) (id {W} ⊗₁ ext (X n) (k n))
    cκ n = L.sub[ ≤-reflexive (trans (*-identityˡ _) (trans (*-identityʳ _) (*-identityˡ _))) ]
             (L.id ⊗ʰ (α⇐ʰ L.∙ (L.id ⊗ʰ Tᵠ.certifiedᴴ (ck n))))
         , Equiv.refl

  -- Moving the earlier PROCESS into the closure, `absorb-closureᵠ` at
  -- `∙-decomp` read the other way: the context of `u ∙ᶠ f` at ancilla `W` IS
  -- `u`'s context at ancilla `W ⊗ X`, with `f`'s own prefix pushed into the
  -- closure and the test rebracketed by `sub α⇒`.
  ≈ctx-pre : (f : Homᶠ A X B) (rf : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rf n) (f n))
           → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
           → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rf n))) ] (v ∙ᶠ f)
  ≈ctx-pre {A = A} {X = X} {B = B} {P = P} {C = C} f rf cf ε {u} {v} hy =
    agreeᵠ⇒≈ctx (λ n q → ε n (scale q (rf n))) λ n W →
      absorb-closureᵠ (ε n) (rf n)
        (L.sub[ ≤-refl ] (α⇒ʰ {W} {X n} {P n} ⊗ʰ L.id {C n}) , Equiv.refl)
        (cθ n W) (λ _ → cut n W (u n)) (λ _ → cut n W (v n))
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

    cθ : (n : ℕ) (W : Channel) → Image forget (rf n) (prefixᵒ W (f n))
    cθ n W = L.sub[ ≤-reflexive (trans (*-identityʳ _) (*-identityˡ _)) ]
               (α⇐ʰ {W} {X n} {B n} L.∙ (L.id {W} ⊗ʰ Tᵠ.certifiedᴴ (cf n)))
           , Equiv.refl

  -- Plugging a process under the DOMAIN, where `≈ctx-pre` plugs one under the
  -- SUBROUTINE.  The closure absorbs it, and at rate `1⁺` that is free: the
  -- pullback's control is `reindex (_· 1⁺)`, so the schedule is unchanged
  -- rather than reindexed.  This is what puts a comparison at a CLOSED domain,
  -- with the resource the two sides must agree about moved out of the context's
  -- control (`docs/coin-toss.md` §5).
  ≈ctx-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n)
           → ((n : ℕ) → Image forget 1⁺ (p n))
           → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ A X B} → u ≈ctx[ ε ] v
           → (λ n → u n ∘ p n) ≈ctx[ ε ] (λ n → v n ∘ p n)
  ≈ctx-dom {A = A} {X = X} {B = B} p cp ε {u} {v} hy = agreeᵠ⇒≈ctx ε λ n W →
    ≈ᵃ-resp₀ (λ _ → cast₀ (cut n W)) (λ _ → cast₀ (⟺ (cut n W)))
      (≈ᵃ-mono (λ q r′ → ℚₚ.≤-reflexive (cong (λ j → ε n (value q ℕ.* j)) (scale-unit (value r′))))
        (≈ᵃ-post (Tᵠ.pullᵠ (1⁺ , L.sub[ ≤-refl ] (L.id {W} ⊗ʰ Tᵠ.certifiedᴴ (cp n))))
                 (≈ctx⇒agreeᵠ ε hy n W)))
    where
    cut : (n : ℕ) (W : Channel) {x : A n ⇒ T₀ (X n) (B n)}
          {E : T₀ (W ⊗₀ X n) (B n) ⇒ Ω}
        → E ∘ prefixᵒ W (x ∘ p n) ≈ (E ∘ prefixᵒ W x) ∘ T₁ W (p n)
    cut _ _ = (refl⟩∘⟨ ((refl⟩∘⟨ T-homomorphism) ○ sym-assoc)) ○ sym-assoc

  -- …hence on a whole bound, with the simulator and the schedule untouched.
  ≤UC[]-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n)
            → ((n : ℕ) → Image forget 1⁺ (p n))
            → (s : Certified Y X) (ε : ℕ → ℕ → ℚ) {f : Homᶠ A X B} {g : Homᶠ A Y B}
            → f ≤UC[ s , ε ] g
            → (λ n → f n ∘ p n) ≤UC[ s , ε ] (λ n → g n ∘ p n)
  ≤UC[]-dom p cp _ ε e =
    ≈ctx-resp ε (λ _ → Equiv.refl) (λ _ → assoc) (≈ctx-dom p cp ε e)

  ≤UC^ωᵉ-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n)
             → ((n : ℕ) → Image forget 1⁺ (p n))
             → {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g
             → (λ n → f n ∘ p n) ≤UC^ωᵉ (λ n → g n ∘ p n)
  ≤UC^ωᵉ-dom p cp (s , ε , neg , e) = s , ε , neg , ≤UC[]-dom p cp s ε e

  ----------------------------------------------------------------------
  -- Graded composition

  -- `Abstract2.UC-compose`'s simulator, certified: the two whiskered halves
  -- compose at the product of their rates.
  composeSim : Certified Y X → Certified Q P → Certified (Y ⊗ᶠ Q) (X ⊗ᶠ P)
  composeSim {X = X} {Q = Q} sf t =
      (λ n → cost sf n · cost t n)
    , poly⁺-· {cost sf} {cost t} (cost-poly sf) (cost-poly t)
    , λ n → L.sub[ ≤-reflexive (cong₂ ℕ._*_ (*-identityʳ (value (cost sf n)))
                                            (*-identityˡ (value (cost t n)))) ]
              ((L.id {X n} ⊗ʰ Cᶠ.hom t n) L.∙ (Cᶠ.hom sf n ⊗ʰ L.id {Q n}))

  -- …and the two EXACT allowance substitutions it spends: `f` goes into the
  -- closure, so `εu` is read at `scale _ (rf n)`, and the SIMULATED
  -- continuation goes into the test, so `εf` is read at its rate `rtv n`.
  composeError : (rf rtv : ℕ → ℕ⁺) → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
  composeError rf rtv εf εu n q = εu n (scale q (rf n)) ℚ.+ εf n (scale q (rtv n))

  -- `≤UC[]-compose` needs neither polynomial; both are spent HERE, where the
  -- two reindexed schedules are classified.
  composeError-negligible : (rf rtv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
                          → Poly⁺ rf → Poly⁺ rtv
                          → NegligibleBound εf → NegligibleBound εu
                          → NegligibleBound (composeError rf rtv εf εu)
  composeError-negligible rf rtv εf εu Prf Prtv nf nu =
    GradedBound-+[ Negligible ] Negligible-+
      (λ n q → εu n (scale q (rf n))) (λ n q → εf n (scale q (rtv n)))
      (NegligibleBound-scale rf Prf εu nu) (NegligibleBound-scale rtv Prtv εf nf)

  -- The ε-analogue of `Abstract2.UC-compose`, step by step.  Its two extra
  -- hypotheses are the certificates for the morphisms it moves: `f`, into the
  -- closure, and `v` with the simulator `t` in front of it, into the test.  The
  -- second is asked of the COMPOSITE, so a sharper certificate for it than the
  -- product rule gives is used as it stands (`≤UC[]-compose′` is the product).
  ≤UC[]-compose :
      {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
      (sf : Certified Y X) (t : Certified Q P) (rf rtv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
    → ((n : ℕ) → Image forget (rf n) (f n))
    → ((n : ℕ) → Image forget (rtv n) (subᶠ t v n))
    → f ≤UC[ sf , εf ] g → u ≤UC[ t , εu ] v
    → (u ∙ᶠ f) ≤UC[ composeSim sf t , composeError rf rtv εf εu ] (v ∙ᶠ g)
  ≤UC[]-compose {X = X} {B = B} {Y = Y} {C = C} {f = f} {g} {u} {v}
                sf t rf rtv εf εu cf ctv ef eu =
    ≈ctx-trans εu′ εf′ (≈ctx-pre f rf cf εu eu)
      (≈ctx-resp εf′ (λ _ → Equiv.refl) strict-final
                 (≈ctx-ext (subᶠ t v) rtv ctv εf ef))
    where
    εu′ εf′ : ℕ → ℕ → ℚ
    εu′ n q = εu n (scale q (rf n))
    εf′ n q = εf n (scale q (rtv n))

    strict-final : (n : ℕ)
                 → ext (X n) (sub (sim t n) {C n} ∘ v n) ∘ sub (sim sf n) {B n} ∘ g n
                   ≈ sub (sim (composeSim sf t) n) {C n} ∘ ext (Y n) (v n) ∘ g n
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
        sub (sim (composeSim sf t) n) ∘ ext (Y n) (v n) ∘ g n  ∎

  -- …from a certificate for `v` alone, the composite certified by the product
  -- rule at `rv n · cost t n`.  Coarser than a direct certificate of the
  -- composite whenever one is sharper, and never finer.
  ≤UC[]-compose′ :
      {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
      (sf : Certified Y X) (t : Certified Q P) (rf rv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
    → ((n : ℕ) → Image forget (rf n) (f n)) → ((n : ℕ) → Image forget (rv n) (v n))
    → f ≤UC[ sf , εf ] g → u ≤UC[ t , εu ] v
    → (u ∙ᶠ f) ≤UC[ composeSim sf t , composeError rf (λ n → rv n · cost t n) εf εu ] (v ∙ᶠ g)
  ≤UC[]-compose′ {C = C} sf t rf rv εf εu cf cv =
    ≤UC[]-compose sf t rf (λ n → rv n · cost t n) εf εu cf λ n →
        L.sub[ ≤-reflexive (cong (value (rv n) ℕ.*_) (*-identityʳ _)) ]
          ((Cᶠ.hom t n ⊗ʰ L.id {C n}) L.∙ Tᵠ.certifiedᴴ (cv n))
      , Equiv.refl

  -- …packaged at the witnesses: the bound above with the two schedules
  -- classified, which is the only thing the polynomials are spent on.
  UC-composeᵉ :
      {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
      (sf : Certified Y X) (εf : ℕ → ℕ → ℚ) → NegligibleBound εf
    → f ≤UC[ sf , εf ] g
    → (t : Certified Q P) (εu : ℕ → ℕ → ℚ) → NegligibleBound εu
    → u ≤UC[ t , εu ] v
    → (rf : ℕ → ℕ⁺) → Poly⁺ rf → ((n : ℕ) → Image forget (rf n) (f n))
    → (rv : ℕ → ℕ⁺) → Poly⁺ rv → ((n : ℕ) → Image forget (rv n) (v n))
    → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
  UC-composeᵉ sf εf nf ef t εu nu eu rf Prf cf rv Prv cv =
      composeSim sf t , composeError rf (λ n → rv n · cost t n) εf εu
    , composeError-negligible rf (λ n → rv n · cost t n) εf εu Prf
        (poly⁺-· {rv} {cost t} Prv (cost-poly t)) nf nu
    , ≤UC[]-compose′ sf t rf rv εf εu cf cv ef eu

  -- …and at both witnesses, which nothing but the schedules' order stood in
  -- the way of.  What stays explicit is the certificates for the two moved
  -- morphisms: `_≤UC^ωᵉ_` bounds the SIMULATOR, not the homs compared.
  ≤UC^ωᵉ-∙ : {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
             (rf : ℕ → ℕ⁺) → Poly⁺ rf → ((n : ℕ) → Image forget (rf n) (f n))
           → (rv : ℕ → ℕ⁺) → Poly⁺ rv → ((n : ℕ) → Image forget (rv n) (v n))
           → f ≤UC^ωᵉ g → u ≤UC^ωᵉ v → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
  ≤UC^ωᵉ-∙ rf Prf cf rv Prv cv (sf , εf , nf , ef) (t , εu , nu , eu) =
    UC-composeᵉ sf εf nf ef t εu nu eu rf Prf cf rv Prv cv

{-# OPTIONS --safe --without-K --guardedness #-}

-- The asymptotic-family UC premise, with its error KEPT: `_≤UC^ωⁿ_`.
--
-- `UC.Asymptotic._≤UC^ω_` is the POINTWISE, unit-grade specialization — a
-- separate single-level emulation for every `n` — and with the real side total
-- it hands back agreement at every positive error at each FIXED level
-- (`pointwise-exact`).  Two systems whose verdict probabilities differ by
-- exactly `2⁻ⁿ` are negligibly different and fail that, so the pointwise
-- premise excludes them (`pointwise-rejects`); this one admits them
-- (`admits-inv-pow-2`) and still rejects a `1/(n+1)` difference
-- (`rejects-inv-suc`).  Those are review §1's two acceptance criteria;
-- `UC.Approximate.LocalTests` states the same pair for the LOCAL relation
-- `_∼ᴺ_`, in the same shape and against the same instruments.
--
-- What replaces the per-level emulation is that same collapse stopped one step
-- earlier — `UC.Seam.Grounded.emulAgreeᵁ`, the direct `≈ᵁ` agreement, which is
-- CONTEXTUAL closeness at a chosen error rather than at every positive one —
-- with the error retained and held to the allowance-uniform negligible
-- discipline.  That is the `_≈ℰⁿ_` tier of `UC.Family`, and `≤UC^ωⁿ⇒≈ℰⁿ` is the
-- identification: `_≈ᶠ[_]_` is `UC.Model.Family._≈ℰ[_]_` at the `ι`-inflated
-- images with the Σ-packaging of a `Fam`-hom peeled off.  That relation reads
-- the CONTEXT's carried budgets and never the compared homs' own, so the
-- premise need not exhibit a query bound for the systems it compares; only the
-- corollaries that enter the family category ask for one.  Peeling it off also
-- makes the premise the explicitly stronger uniform refinement review §1
-- permits — a per-level context need not come from a polynomially budgeted
-- FAMILY of contexts — and that is the direction the ledger consumer needs.
--
-- Both halves of the seam are theorems elsewhere: `UC.Model.Family.Ingest`
-- ingests a per-level advantage bound INTO the family relation, and
-- `UC.Seam.Audit.Context` reads one back OUT at the embedded-strategy contexts,
-- which is `≈ᶠ-runs` — how the premise becomes `UC.Saturated._≈negl_`, the
-- layer-1 relation a saturated conclusion consumes, with no exact agreement
-- anywhere in between.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Nat.Properties using (*-identityʳ; ≤-refl)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties using (+-identityʳ; +-monoʳ-<; <-irrefl; ≤-<-trans)
open import Data.Rational.Properties.Ext using (0<½*; ½*+½*)
open import Relation.Binary.PropositionalEquality using (refl; subst; subst₂)
open import Relation.Nullary using (¬_)

open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2)
open import ProbabilisticLogic.Dp.Advantage
  using (_≈ₚ[_]_; ≈ₚ[]-refl; ≈ₚ[]-resp; ≈ₚ[]-sym; ≈ₚ[]-trans)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate
  using (GradedBound-+[_]; Negligible; Negligible-+; Negligible-0; NegligibleBound)
open import CategoricalCrypto.UC.Approximate.Decay
  using (Negligible-≤; negligible-slack; 0<inv-pow-2)
open import CategoricalCrypto.UC.Approximate.Separating
  using (inv-suc; ¬negligible-inv-suc)
open import CategoricalCrypto.UC.Asymptotic using (_≤UC^ω_)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget)
open import CategoricalCrypto.UC.Model.Bridge using (≈ᵁ⇒≈ℰᶜ)
open import CategoricalCrypto.UC.Model.Dominated using (T₁ᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Family
  using ( Obj^ω; Δ; _⇒^ω_; _⊛ω_; PolyQB; _≈ℰ[_]_; _≈ℰⁿ_; carried-negligible
        ; ≈ℰⁿ⇒≈ℰ )
  renaming (_≈ℰ_ to _≈ℰᶠ_; _≤UC_ to _≤UCᶠ_; ≈ℰ⇒≤UC to ≈ℰᶠ⇒≤UCᶠ)
open import CategoricalCrypto.UC.Model.Family.Uniform
  using (≈ℰ^ω⇒≤UC) renaming (_≤UC_ to _≤UCᵁ_)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated using (_≈negl_; Systems)
open import CategoricalCrypto.UC.Seam.Audit.Context
  using (auditClose; auditTest; audit-qb; audit-run)
open import CategoricalCrypto.UC.Seam.Carry.Graded using (adv-from-runs)

import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Asymptotic.Family where

open Budget budgetᵒ using (QB; qb-λ⇐)

private variable B : ℕ → Iface
                 R I J : Systems B

------------------------------------------------------------------------
-- The images and the ε-approximate family agreement

ifaceᶠ : (B : ℕ → Iface) → Obj^ω
ifaceᶠ B n = ifaceᵒ (B n)

-- The codomain the compared homs live at: the trivial grade over the
-- interfaces, which is the codomain `_≤UC^ω_`'s premise is stated at too.
gradedᶠ : (B : ℕ → Iface) → Obj^ω
gradedᶠ B = Δ Gr.𝟘ᴳ ⊛ω ifaceᶠ B

imgᶠ : (B : ℕ → Iface) (R : Systems B) (n : ℕ) → 𝟘ᵒ ⇒ gradedᶠ B n
imgᶠ B R n = Gr.closedᵒ (morphism (R n))

infix 4 _≈ᶠ[_]_

-- `UC.Model.Family._≈ℰ[_]_` at those images, unpackaged (header): at each
-- level, no budgeted ancilla context separates the two images by more than `ε`
-- read at the budget the context's two legs CARRY.
_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁
_≈ᶠ[_]_ {B} R ε I =
    (n : ℕ) (Y : Channel) (Et : T₀ Y (gradedᶠ B n) ⇒ Ωᵒ) (m : 𝟘ᵒ ⇒ T₀ Y 𝟘ᵒ)
    {c c′ : ℕ} → QB c Et → QB c′ m
  → Obs ((Et ∘ T₁ᵒ Y (imgᶠ B R n)) ∘ m) ≈ₚ[ ε n (ctxBudget c c′) ]
    Obs ((Et ∘ T₁ᵒ Y (imgᶠ B I n)) ∘ m)

infix 4 _≤UC^ωⁿ_

-- The premise: the agreement above with its `ε` kept and graded, the grade
-- being the allowance-uniform one the saturated conclusion is stated at
-- (`UC.Saturated`'s `SaturatedBoundedᴺ`, via `_≈negl_`).
_≤UC^ωⁿ_ : Systems B → Systems B → Set₁
R ≤UC^ωⁿ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I

≤UC^ωⁿ-refl : R ≤UC^ωⁿ R
≤UC^ωⁿ-refl = (λ _ _ → 0ℚ) , (λ _ _ → Negligible-0) , λ _ _ _ _ _ _ → ≈ₚ[]-refl

≤UC^ωⁿ-sym : R ≤UC^ωⁿ I → I ≤UC^ωⁿ R
≤UC^ωⁿ-sym (ε , neg , h) = ε , neg , λ n Y Et m qE qm → ≈ₚ[]-sym (h n Y Et m qE qm)

-- The composition law: two family emulations compose and the εs ADD, the sum
-- staying negligible because the grade is closed under sums.  This is
-- `UC.Family.≈ℰⁿ-trans`'s arithmetic read one layer out, and it is the only
-- composition that RETAINS the error — `UC-compose` is the inherited
-- metatheorem and is stated in the qualitative order, so composing the premise
-- with a second protocol goes through `≤UC^ωⁿ⇒≤UCᵁ` below and spends the
-- witness.  An ε-retaining `UC-compose` needs a graded `_≤UC[ ε ]_` with graded
-- `≈ℰ` congruences and a graded `sub`/`T₁` interchange, which is the
-- observation-interface redesign `UC.Family`'s closing comment prices.
≤UC^ωⁿ-trans : R ≤UC^ωⁿ I → I ≤UC^ωⁿ J → R ≤UC^ωⁿ J
≤UC^ωⁿ-trans (ε₁ , neg₁ , h₁) (ε₂ , neg₂ , h₂) =
    (λ n q → ε₁ n q ℚ.+ ε₂ n q)
  , GradedBound-+[ Negligible ] Negligible-+ ε₁ ε₂ neg₁ neg₂
  , λ n Y Et m qE qm → ≈ₚ[]-trans (h₁ n Y Et m qE qm) (h₂ n Y Et m qE qm)

------------------------------------------------------------------------
-- The premise IS the `_≈ℰⁿ_` tier

-- Entering the family category costs a carried query bound for each image,
-- which is what a `Fam`-hom is a base hom plus.  Nothing above needs it: the
-- relation reads only the context's budgets.
Imageᶠ : (B : ℕ → Iface) → Systems B → Set₁
Imageᶠ B R = PolyQB {Δ 𝟘ᵒ} {gradedᶠ B} (imgᶠ B R)

imageᶠ : (R : Systems B) → Imageᶠ B R → Δ 𝟘ᵒ ⇒^ω gradedᶠ B
imageᶠ {B} R q = imgᶠ B R , q

-- The bound is EXPLICIT here and in `≈ᶠ-runs` below, for
-- `UC.Approximate.GradedBound-+[_]`'s reason: both relations read it under an
-- application, so no value of one determines it by unification.
≈ᶠ⇒≈ℰ[] : (ε : ℕ → ℕ → ℚ) (qR : Imageᶠ B R) (qI : Imageᶠ B I) → R ≈ᶠ[ ε ] I
        → _≈ℰ[_]_ {Δ 𝟘ᵒ} {gradedᶠ B} (imageᶠ R qR) ε (imageᶠ I qI)
≈ᶠ⇒≈ℰ[] _ _ _ h Y (Et , _ , _ , wE) (m , _ , _ , wm) n =
  h n (Y n) (Et n) (m n) (wE n) (wm n)

-- `carried-negligible` is the whole of the grade's translation: the allowance a
-- context carries is polynomial, which is the witness `CarriedNegligible` wants.
≤UC^ωⁿ⇒≈ℰⁿ : (qR : Imageᶠ B R) (qI : Imageᶠ B I) → R ≤UC^ωⁿ I
           → imageᶠ R qR ≈ℰⁿ imageᶠ I qI
≤UC^ωⁿ⇒≈ℰⁿ qR qI (ε , neg , h) =
  ε , carried-negligible {ε = ε} neg , ≈ᶠ⇒≈ℰ[] ε qR qI h

≤UC^ωⁿ⇒≈ℰᶠ : (qR : Imageᶠ B R) (qI : Imageᶠ B I) → R ≤UC^ωⁿ I
           → imageᶠ R qR ≈ℰᶠ imageᶠ I qI
≤UC^ωⁿ⇒≈ℰᶠ {R = R} {I = I} qR qI p =
  ≈ℰⁿ⇒≈ℰ {f = imageᶠ R qR} {imageᶠ I qI} (≤UC^ωⁿ⇒≈ℰⁿ qR qI p)

≤UC^ωⁿ⇒≤UCᶠ : (qR : Imageᶠ B R) (qI : Imageᶠ B I) → R ≤UC^ωⁿ I
            → imageᶠ R qR ≤UCᶠ imageᶠ I qI
≤UC^ωⁿ⇒≤UCᶠ {R = R} {I = I} qR qI p =
  ≈ℰᶠ⇒≤UCᶠ {f = imageᶠ R qR} {imageᶠ I qI} (≤UC^ωⁿ⇒≈ℰᶠ qR qI p)

-- …and in the INHERITED order, which is where `UC-compose` is
-- (`UC.Model.Family.Uniform`, over the generic `UC.Core.Bridge`).
≤UC^ωⁿ⇒≤UCᵁ : (qR : Imageᶠ B R) (qI : Imageᶠ B I) → R ≤UC^ωⁿ I
            → imageᶠ R qR ≤UCᵁ imageᶠ I qI
≤UC^ωⁿ⇒≤UCᵁ {R = R} {I = I} qR qI p =
  ≈ℰ^ω⇒≤UC (imageᶠ R qR) (imageᶠ I qI) (≤UC^ωⁿ⇒≈ℰᶠ qR qI p)

------------------------------------------------------------------------
-- Reading it at the embedded strategies

-- The context is `UC.Seam.Audit.Context`'s: an embedded strategy behind the two
-- unitors that kill the grade and the ancilla, its budget the strategy's own
-- ask-depth (`ctxBudget q 1 = q · 1`) and its observation layer 1's run
-- (`audit-run`).  So the premise's contextual `ε` lands on the DIRECT runs at
-- the strategy's allowance, which is the layer the conclusion's slack lives at.
≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I
        → (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
        → runᴹ (morphism (R n)) d ≈ₚ[ ε n q ] runᴹ (morphism (I n)) d
≈ᶠ-runs ε h n q d a =
  subst (λ k → _ ≈ₚ[ ε n k ] _) (*-identityʳ q)
        (≈ₚ[]-resp (audit-run _ d _) (audit-run _ d _)
                   (h n Gr.𝟘ᴳ (auditTest _ d) auditClose (audit-qb _ d q a) qb-λ⇐))

-- …and that is layer 1's negligibly graded relation, which is what the
-- saturated conclusion transports (`UC.Saturated.≈negl-respects`).  No exact
-- agreement is passed through: `Agreeˢ` appears nowhere above.
≤UC^ωⁿ⇒≈negl : R ≤UC^ωⁿ I → R ≈negl I
≤UC^ωⁿ⇒≈negl {R = R} {I = I} (ε , neg , h) =
  ε , neg , λ n → adv-from-runs (R n) (I n) (ε n) λ q d a → ≈ᶠ-runs ε h n q d a

------------------------------------------------------------------------
-- Review §1's acceptance criteria

-- A one-shot `2⁻ⁿ` difference is ADMITTED: `2⁻ⁿ` is an admissible error
-- schedule, and it is exactly the one the pointwise inclusion below produces.
admits-inv-pow-2 : R ≈ᶠ[ (λ n _ → inv-pow-2 n) ] I → R ≤UC^ωⁿ I
admits-inv-pow-2 h =
  (λ n _ → inv-pow-2 n) , (λ _ _ → negligible-slack λ _ → ≤-refl) , h

-- …and a one-shot `1/(n+1)` one is REJECTED.  The instrument is the one
-- `UC.Approximate.Separating`'s header prices: no abstract approximation bounds
-- a difference from BELOW, so the rejection is stated against a separation —
-- here a family of budgeted strategies at which closeness implies the gap is at
-- most the error.  The premise's `ε` then dominates `1/(n+1)`, and
-- negligibility passes down to what it dominates while `1/(n+1)` is not
-- negligible.
rejects-inv-suc :
    (p : ℕ → ℕ) → Poly p
  → (d : (n : ℕ) → Strat (Neg (B n)) (Pos (B n))) → ((n : ℕ) → asks≤ (p n) (d n))
  → ((n : ℕ) {e : ℚ} → runᴹ (morphism (R n)) (d n) ≈ₚ[ e ] runᴹ (morphism (I n)) (d n)
     → inv-suc n ℚ.≤ e)
  → ¬ (R ≤UC^ωⁿ I)
rejects-inv-suc p Pp d ad sep (ε , neg , h) =
  ¬negligible-inv-suc
    (Negligible-≤ (λ n → sep n (≈ᶠ-runs ε h n (p n) (d n) (ad n))) (neg p Pp))

------------------------------------------------------------------------
-- The pointwise premise includes into it

-- `UC.Seam.Grounded.emulAgreeᵁ` is the whole content: at the trivial grade a
-- total real side turns an emulation into the direct `≈ᵁ` agreement, which is
-- contextual closeness at EVERY positive error — hence at any positive schedule
-- one cares to name.  `UC.Asymptotic.uc-agree` is the same collapse read one
-- step further along, into `Agreeˢ`; stopping here is what keeps the error.
uc-≈ᶠ[_] : (ν : ℕ → ℚ) → ((n : ℕ) → 0ℚ ℚ.< ν n)
         → ((n : ℕ) → TotalRun (B n) (morphism (R n))) → R ≤UC^ω I
         → R ≈ᶠ[ (λ n _ → ν n) ] I
uc-≈ᶠ[ ν ] pos tR em n Y Et m _ _ =
  ≈ᵁ⇒≈ℰᶜ (Gr.emulAgreeᵁ _ _ _ (tR n) (em n)) Y Et m (ν n) (pos n)

-- …so the pointwise theorems are specializations of the family ones, the
-- schedule being `2⁻ⁿ` — the same slack `uc-≈negl` spends, and for the same
-- reason (an ε-quantified agreement has no zero instance to give).
uc-≤UC^ωⁿ : ((n : ℕ) → TotalRun (B n) (morphism (R n))) → R ≤UC^ω I → R ≤UC^ωⁿ I
uc-≤UC^ωⁿ tR em = admits-inv-pow-2 (uc-≈ᶠ[ inv-pow-2 ] 0<inv-pow-2 tR em)

-- What the pointwise premise says that the family one does not: closeness of
-- the direct runs at every positive error AT A FIXED LEVEL.
pointwise-exact : ((n : ℕ) → TotalRun (B n) (morphism (R n))) → R ≤UC^ω I
                → (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
                → (e : ℚ) → 0ℚ ℚ.< e
                → runᴹ (morphism (R n)) d ≈ₚ[ e ] runᴹ (morphism (I n)) d
pointwise-exact tR em n q d a e e>0 =
  ≈ᶠ-runs (λ _ _ → e) (uc-≈ᶠ[ (λ _ → e) ] (λ _ → e>0) tR em) n q d a

-- …hence it REJECTS what the family premise admits: a pair separated at some
-- level by exactly `2⁻ⁿ`.  `2⁻⁽ⁿ⁺¹⁾` is positive, so the pointwise premise puts
-- the gap below it, and `2⁻ⁿ ≤ 2⁻⁽ⁿ⁺¹⁾` is false.
pointwise-rejects :
    (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
  → ({e : ℚ} → runᴹ (morphism (R n)) d ≈ₚ[ e ] runᴹ (morphism (I n)) d
     → inv-pow-2 n ℚ.≤ e)
  → ¬ (((k : ℕ) → TotalRun (B k) (morphism (R k))) × R ≤UC^ω I)
pointwise-rejects n q d a sep (tR , em) = <-irrefl refl
  (≤-<-trans (sep (pointwise-exact tR em n q d a (inv-pow-2 (ℕ.suc n))
                                   (0<inv-pow-2 (ℕ.suc n))))
             (subst₂ ℚ._<_ (+-identityʳ (½ ℚ.* inv-pow-2 n)) (½*+½* (inv-pow-2 n))
                     (+-monoʳ-< (½ ℚ.* inv-pow-2 n) (0<½* (0<inv-pow-2 n)))))

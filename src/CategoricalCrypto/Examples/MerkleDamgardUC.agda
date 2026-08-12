--------------------------------------------------------------------------------
-- The Merkle-Damgård artifact as a `MachineAxioms` model.
--
-- Track A develops the UC metatheory over an AXIOMATIZED machine layer
-- (`CategoricalCrypto.MachineAxioms`).  This module supplies the model at the
-- concrete `Examples.MerkleDamgard` layer, and it is where the one genuine
-- modelling step of the instantiation happens: MD's advantage is TERNARY
-- (`adv f g d`, carrying an adaptive distinguisher `d`), whereas
-- `MachineAxioms.adv` is BINARY on observations.  The distinguisher is absorbed
-- into the morphism: a closed run is a machine `𝟙 ⇒ Ω` at the verdict channel
-- `Ω = Bool ⇿ ⊤`, whose observation is its answer to the one-shot distinguisher
-- `askOnce`; a general adaptive distinguisher is recovered as the CONTEXT that
-- plugs a machine into such an experiment.  Everything on the observation side
-- is then proven: `Obs`, `adv⊥` and its three laws come from `Pr₁⊥` and
-- ℚ-absolute-value facts.
--
-- What is NOT proven here, and why it is a hypothesis rather than a `postulate`
-- (house standard: axioms are record fields):
--   • the CATEGORY laws of the 𝒢-composition `_⊚_` — MD postulates `⊚` with no
--     laws at all, since the trace operator they hold of lives on the
--     g-construction branch (plan debt 1/2);
--   • the MONOIDAL structure over `_⊗ₚ_` (plan debt 1);
--   • the query-bound instrument `QB` and its laws (plan debt 3).
-- `MachineHyp` is exactly that debt, as one record.

--------------------------------------------------------------------------------

module CategoricalCrypto.Examples.MerkleDamgardUC where

open import Data.Bool.Base using (Bool)
open import Data.Nat as ℕ using (ℕ; NonZero)
open import Data.Nat.Poly using (Poly)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ)
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( +-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ
  ; neg-distrib-+; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣ )
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec)
open import Level using (0ℓ; suc)
open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; I)
open import CategoricalCrypto.Examples.MerkleDamgard
import CategoricalCrypto.FamilyCategory
open import CategoricalCrypto.MachineAxioms using (MachineAxioms)
import CategoricalCrypto.RandomOracle2
open import CategoricalCrypto.SFunM using (_≈ᵉ_; ≈ᵉ-isEquivalence)
import CategoricalCrypto.StandardTV
import CategoricalCrypto.VanishingTV

------------------------------------------------------------------------
-- Observational hom-equality of machines
--
-- Every equational fact MD proves about machines goes through `⟦_⟧` into the
-- trace setoid `_≈ᵉ_` of `SFun⊥`, so that is the machine category's hom-equality.

infix 4 _≈ₚ_

_≈ₚ_ : {A B : Channel} → PMachine A B → PMachine A B → Set
f ≈ₚ g = (_≈ᵉ_ {M = Dist⊥}) ⟦ f ⟧ ⟦ g ⟧

≈ₚ-isEquivalence : {A B : Channel} → IsEquivalence (_≈ₚ_ {A} {B})
≈ₚ-isEquivalence = On.isEquivalence ⟦_⟧ (≈ᵉ-isEquivalence {M = Dist⊥})

------------------------------------------------------------------------
-- The verdict channel and the closed run
--
-- `Ω` receives one trigger (`⊤`) and answers with a verdict bit, so a machine
-- `𝟙 ⇒ Ω` is a complete closed experiment.

Ω : Channel
Ω = Bool ⇿ ⊤

askOnce : Dgr ⊤ Bool
askOnce = ask tt out

Obs : Setoid 0ℓ 0ℓ
Obs = record { Carrier = Dist⊥ Bool ; _≈_ = _≈Mℚ_ ; isEquivalence = ≈Mℚ-isEquivalence }

------------------------------------------------------------------------
-- The advantage pseudometric on observations, and its three laws.
-- `MerkleDamgard.adv f g d` is `adv⊥ (run⊥ f d) (run⊥ g d)` on the nose.

adv⊥ : Dist⊥ Bool → Dist⊥ Bool → ℚ
adv⊥ μ ν = ∣ Pr₁⊥ μ -ℚ Pr₁⊥ ν ∣ℚ

private
  -- `Data.Rational.Properties` has no negation involution; derive it in the group.
  neg-neg : ∀ p → -ℚ (-ℚ p) ≡ p
  neg-neg p = trans (sym (+-identityʳ (-ℚ (-ℚ p))))
              (trans (cong ((-ℚ (-ℚ p)) +ℚ_) (sym (+-inverseˡ p)))
              (trans (sym (+-assoc (-ℚ (-ℚ p)) (-ℚ p) p))
              (trans (cong (_+ℚ p) (+-inverseˡ (-ℚ p))) (+-identityˡ p))))

  p-q≡-[q-p] : ∀ p q → p -ℚ q ≡ -ℚ (q -ℚ p)
  p-q≡-[q-p] p q = sym (trans (neg-distrib-+ q (-ℚ p))
                         (trans (cong ((-ℚ q) +ℚ_) (neg-neg p)) (+-comm (-ℚ q) p)))

  telescope : ∀ a b c → (a -ℚ b) +ℚ (b -ℚ c) ≡ a -ℚ c
  telescope a b c = trans (+-assoc a (-ℚ b) (b -ℚ c))
    (cong (a +ℚ_) (trans (sym (+-assoc (-ℚ b) b (-ℚ c)))
                    (trans (cong (_+ℚ (-ℚ c)) (+-inverseˡ b)) (+-identityˡ (-ℚ c)))))

adv⊥-cong : {μ μ′ ν ν′ : Dist⊥ Bool} → μ ≈Mℚ μ′ → ν ≈Mℚ ν′ → adv⊥ μ ν ≡ adv⊥ μ′ ν′
adv⊥-cong {μ} {μ′} {ν} {ν′} e f =
  cong₂ (λ a b → ∣ a -ℚ b ∣ℚ) (Pr₁⊥-cong μ μ′ e) (Pr₁⊥-cong ν ν′ f)

adv⊥-sym : ∀ μ ν → adv⊥ μ ν ≡ adv⊥ ν μ
adv⊥-sym μ ν = trans (cong ∣_∣ℚ (p-q≡-[q-p] (Pr₁⊥ μ) (Pr₁⊥ ν))) (∣-p∣≡∣p∣ _)

adv⊥-triangle : ∀ μ ν ρ → adv⊥ μ ρ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ
adv⊥-triangle μ ν ρ =
  subst (λ z → ∣ z ∣ℚ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ)
        (telescope (Pr₁⊥ μ) (Pr₁⊥ ν) (Pr₁⊥ ρ))
        (∣p+q∣≤∣p∣+∣q∣ (Pr₁⊥ μ -ℚ Pr₁⊥ ν) (Pr₁⊥ ν -ℚ Pr₁⊥ ρ))

adv⊥-≈⇒0 : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → adv⊥ μ ν ≡ 0ℚ
adv⊥-≈⇒0 {μ} {ν} e = trans (cong (λ z → ∣ Pr₁⊥ μ -ℚ z ∣ℚ) (sym (Pr₁⊥-cong μ ν e)))
                           (cong ∣_∣ℚ (+-inverseʳ (Pr₁⊥ μ)))

------------------------------------------------------------------------
-- The machine layer's outstanding debt, as hypotheses

-- The 𝒢-composition's category laws.  MD postulates `_⊚_` with no laws at all:
-- the trace operator these hold of lives on the g-construction branch.
record MachineCatHyp : Set (suc 0ℓ) where
  field
    ⊚-assoc     : ∀ {A B C D} {f : PMachine A B} {g : PMachine B C} {h : PMachine C D}
                → ((h ⊚ g) ⊚ f) ≈ₚ (h ⊚ (g ⊚ f))
    ⊚-identityˡ : ∀ {A B} {f : PMachine A B} → (pid ⊚ f) ≈ₚ f
    ⊚-identityʳ : ∀ {A B} {f : PMachine A B} → (f ⊚ pid) ≈ₚ f
    ⊚-resp-≈    : ∀ {A B C} {g i : PMachine B C} {f h : PMachine A B}
                → g ≈ₚ i → f ≈ₚ h → (g ⊚ f) ≈ₚ (i ⊚ h)

machinesOf : MachineCatHyp → Category (suc 0ℓ) (suc 0ℓ) 0ℓ
machinesOf mc = categoryHelper record
  { Obj = Channel ; _⇒_ = PMachine ; _≈_ = _≈ₚ_ ; id = pid ; _∘_ = _⊚_
  ; assoc = ⊚-assoc ; identityˡ = ⊚-identityˡ ; identityʳ = ⊚-identityʳ
  ; equiv = ≈ₚ-isEquivalence ; ∘-resp-≈ = ⊚-resp-≈ }
  where open MachineCatHyp mc

𝕄of : (mc : MachineCatHyp) → Monoidal (machinesOf mc)
    → MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
𝕄of mc mono = record { U = machinesOf mc ; monoidal = mono }

record MachineHyp : Set (suc (suc 0ℓ)) where
  field
    cat : MachineCatHyp
    -- `_⊗ₚ_` extends to a monoidal structure whose unit is the empty channel
    -- `I`: the channel-level tensor and unit are already concrete, only the
    -- machine-level structural morphisms and all the laws are outstanding.
    mono   : Monoidal (machinesOf cat)
    unit≡I : Monoidal.unit mono ≡ I

  open MachineCatHyp cat public
  module M = MonoidalCategory (𝕄of cat mono)
  open MonoidalUtilities.Shorthands mono

  field
    -- The query-bound instrument: `QB c h` reads "one codomain-side activation
    -- of `h` causes at most `c` completed domain-side events".
    QB        : ℕ → ∀ {A B} → PMachine A B → Set
    qb-id     : ∀ {A} → QB 1 (pid {A})
    qb-∘      : ∀ {A B C c c′} {g : PMachine B C} {f : PMachine A B}
              → QB c g → QB c′ f → QB (c ℕ.* c′) (g ⊚ f)
    qb-⊗      : ∀ {A B C D c c′} {f : PMachine A B} {h : PMachine C D}
              → QB c f → QB c′ h → QB (c ℕ.⊔ c′) (f M.⊗₁ h)
    qb-resp-≈ : ∀ {A B c} {f g : PMachine A B} → f ≈ₚ g → QB c f → QB c g
    qb-mono   : ∀ {A B c c′} {f : PMachine A B} → c ℕ.≤ c′ → QB c f → QB c′ f
    qb-α⇒     : ∀ {A B C} → QB 1 (α⇒ {A} {B} {C})
    qb-α⇐     : ∀ {A B C} → QB 1 (α⇐ {A} {B} {C})
    qb-λ⇒     : ∀ {A} → QB 1 (λ⇒ {A})
    qb-λ⇐     : ∀ {A} → QB 1 (λ⇐ {A})
    qb-ρ⇒     : ∀ {A} → QB 1 (ρ⇒ {A})
    qb-ρ⇐     : ∀ {A} → QB 1 (ρ⇐ {A})

  𝕄 : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
  𝕄 = 𝕄of cat mono

  -- The transport along `unit≡I` is what lets a `𝟙 ⇒ Ω` machine be read as the
  -- subroutine-free `PMachine I Ω` whose closed semantics `⟦_⟧cl` computes.
  toI : ∀ {C} → PMachine M.unit C → PMachine I C
  toI {C} = subst (λ U → PMachine U C) unit≡I

  obs : PMachine M.unit Ω → Dist⊥ Bool
  obs u = run⊥ ⟦ toI u ⟧cl askOnce

  obs-cong : {u u′ : PMachine M.unit Ω} → u ≈ₚ u′ → obs u ≈Mℚ obs u′
  obs-cong = go unit≡I
    where
    go : ∀ {U} (p : U ≡ I) {u u′ : PMachine U Ω} → u ≈ₚ u′
       → run⊥ ⟦ subst (λ V → PMachine V Ω) p u  ⟧cl askOnce
     ≈Mℚ run⊥ ⟦ subst (λ V → PMachine V Ω) p u′ ⟧cl askOnce
    go refl e = ≈ᵉ⇒run (strip⊥-cong e) askOnce

  axioms : MachineAxioms (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ 0ℓ 0ℓ
  axioms = record
    { 𝕄 = 𝕄 ; Ω = Ω ; Obs = Obs ; ⟦_⟧ = obs ; adv = adv⊥ ; QB = QB
    ; ⟦⟧-resp-≈ = λ {f} {g} → obs-cong {f} {g}
    ; adv-sym = adv⊥-sym ; adv-triangle = adv⊥-triangle ; adv-≈⇒0 = λ {x} {y} → adv⊥-≈⇒0 {x} {y}
    ; qb-id = qb-id ; qb-∘ = qb-∘ ; qb-⊗ = qb-⊗ ; qb-resp-≈ = qb-resp-≈
    ; qb-mono = qb-mono
    ; qb-α⇒ = qb-α⇒ ; qb-α⇐ = qb-α⇐ ; qb-λ⇒ = qb-λ⇒ ; qb-λ⇐ = qb-λ⇐
    ; qb-ρ⇒ = qb-ρ⇒ ; qb-ρ⇐ = qb-ρ⇐
    }

------------------------------------------------------------------------
-- The MD security artifact, level by level

-- What the UC payoff consumes of `Examples.MerkleDamgard`: a compression
-- resource, the MD protocol machine on top of it, the ideal variable-length
-- random oracle, and MD's output-only concrete-security theorem.  Packaging it
-- keeps the family plumbing below independent of MD's module parameters.
record ROArtifact : Set (suc 0ℓ) where
  field
    Comp-If Gen-If : Channel
    compM : PMachine I Comp-If
    mdM   : PMachine Comp-If Gen-If
    genM  : PMachine I Gen-If
    bnd   : ℕ → ℚ
    secure : ∀ q (d : Dgr (Channel.outType Gen-If) (Channel.inType Gen-If))
           → asks≤ q d → adv ⟦ genM ⟧cl ⟦ mdM ⊚ compM ⟧cl d ≤ℚ bnd q

mdArtifact : (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) → ROArtifact
mdArtifact n k IV = record
  { Comp-If = MD.Comp.Interface n k IV ; Gen-If = MD.General.Interface n k IV
  ; compM = MD.Comp.M n k IV ; mdM = MD.MD n k IV ; genM = MD.General.M n k IV
  ; bnd = MD.bound n k IV ; secure = MD.indistinguishable n k IV
  }

------------------------------------------------------------------------
-- The degenerate-grade UC payoff
--
-- MD's theorem is OUTPUT-ONLY: its interfaces carry no adversary wire and it
-- has no simulator.  Instantiating `RandomOracle2.RO` at `Jre = Kid = 𝟙` lifts
-- it into the ≤UC formulation honestly — the simulator is the identity and
-- `ideal-bridge` collapses to `sub id ∘ General-M ≈ℰ General-M` — at the cost
-- that the UC statement obtained is the no-adversary-interface degenerate
-- case.  The public-RO shape (a real indifferentiability simulator) is the one
-- item with genuinely new cryptographic content, and is out of scope here.

module AtUnitGrade
  (mh : MachineHyp)
  (hom-triv : MachineAxioms.HomTransportTrivial (MachineHyp.axioms mh))
  (art : ℕ → ROArtifact)
  where
  open MachineHyp mh
  open MonoidalUtilities.Shorthands mono

  private
    module A (j : ℕ) = ROArtifact (art j)
    module FC = CategoricalCrypto.FamilyCategory axioms
    module VT = CategoricalCrypto.VanishingTV axioms
    module ST = CategoricalCrypto.StandardTV axioms hom-triv
    module Cω = MonoidalCategory FC.𝒞^ω

  GenIf Mid : FC.Obj^ω
  GenIf = A.Gen-If
  Mid   = A.Comp-If

  private
    module RO = CategoricalCrypto.RandomOracle2.RO {ℓr = suc 0ℓ} {ℓv = 0ℓ}
                  FC.𝒞^ω VT.ℰᵗᵛ (ℕ → ℚ) GenIf Mid FC.𝟙^ω FC.𝟙^ω

    _⊗ω_ : FC.Obj^ω → FC.Obj^ω → FC.Obj^ω
    (Y ⊗ω B) j = Y j M.⊗₀ B j

    -- `unit ≡ I` read the other way round: a subroutine-free machine as a
    -- morphism out of the monoidal unit.
    fromI : ∀ {C} → PMachine I C → PMachine M.unit C
    fromI {C} = subst (λ U → PMachine U C) (sym unit≡I)

  -- The unitor conjugation into the degenerate grade.
  conj : ∀ {C} → PMachine I C → PMachine (M.unit M.⊗₀ M.unit) (M.unit M.⊗₀ C)
  conj u = λ⇐ ⊚ (fromI u ⊚ λ⇒)

  private
    subst-⊚ : ∀ {U B C} (p : I ≡ U) (g : PMachine B C) (f : PMachine I B)
            → subst (λ V → PMachine V C) p (g ⊚ f) ≡ g ⊚ subst (λ V → PMachine V B) p f
    subst-⊚ refl g f = refl

    -- The composite of the two conjugated legs IS the conjugated composite.
    conj-∘ : ∀ {B C} (g : PMachine B C) (f : PMachine I B)
           → ((λ⇐ ⊚ g) ⊚ (fromI f ⊚ λ⇒)) ≈ₚ conj (g ⊚ f)
    conj-∘ g f = M.Equiv.trans M.assoc (M.∘-resp-≈ʳ inner)
      where
      inner : (g ⊚ (fromI f ⊚ λ⇒)) ≈ₚ (fromI (g ⊚ f) ⊚ λ⇒)
      inner = M.Equiv.trans M.sym-assoc
                (M.Equiv.reflexive (cong (λ z → z ⊚ λ⇒) (sym (subst-⊚ (sym unit≡I) g f))))

  -- The closed run of a machine plugged into a budgeted ancilla context.  This
  -- is `VanishingTV.run` of the context composite, spelled level by level.
  ctxRun : (Y : FC.Obj^ω) → FC.Test^ω (Y ⊗ω RO.Bo) → FC.Closure^ω (Y ⊗ω RO.Ao)
         → ∀ j → PMachine (RO.Ao j) (RO.Bo j) → Dist⊥ Bool
  ctxRun Y E m j f = obs (proj₁ E j ⊚ ((M.id M.⊗₁ f) ⊚ proj₁ m j))

  private
    ctxRun-cong : ∀ Y E m j {f g} → f ≈ₚ g → ctxRun Y E m j f ≈Mℚ ctxRun Y E m j g
    ctxRun-cong Y E m j e =
      obs-cong (M.∘-resp-≈ʳ (M.∘-resp-≈ˡ (M.⊗.F-resp-≈ (M.Equiv.refl , e))))

  -- Every budgeted ancilla context around a subroutine-free machine is realized
  -- by ONE adaptive distinguisher, whose query count is bounded by the context's
  -- polynomial budget.  This is what `QB` MEANS at the machine layer, and the
  -- reason `MachineAxioms.QB` can stay an abstract instrument: it is the
  -- machine-layer obligation that lets MD's `∀ d`-quantified theorem be read as
  -- an ℰᵗᵛ-statement.  Not provable while `⟦_⟧`/`_⊚_` carry no laws.
  Reflects : Set (suc 0ℓ)
  Reflects = ∀ (Y : FC.Obj^ω) (E : FC.Test^ω (Y ⊗ω RO.Bo)) (m : FC.Closure^ω (Y ⊗ω RO.Ao))
           → Σ[ p ∈ (ℕ → ℕ) ] Poly p ×
             (∀ j → Σ[ d ∈ Dgr (Channel.outType (GenIf j)) (Channel.inType (GenIf j)) ]
                      asks≤ (p j) d ×
                      (∀ (u : PMachine I (GenIf j)) →
                         ctxRun Y E m j (conj u) ≈Mℚ run⊥ ⟦ u ⟧cl d))

  -- The three artifact legs as morphism FAMILIES; their polynomial query budgets
  -- are the one deferred item (`Nfuel = double k` makes them look mechanical, but
  -- discharging them needs a concrete `QB`, so they stay hypotheses).
  compFam : ∀ j → PMachine (RO.Ao j) (Mid j)
  compFam j = fromI (A.compM j) ⊚ λ⇒

  mdFam : ∀ j → PMachine (Mid j) (RO.Bo j)
  mdFam j = λ⇐ ⊚ A.mdM j

  genFam : ∀ j → PMachine (RO.Ao j) (RO.Bo j)
  genFam j = conj (A.genM j)

  module Assemble
    (qbComp : FC.PolyQB compFam)
    (qbMD   : FC.PolyQB mdFam)
    (qbGen  : FC.PolyQB genFam)
    (reflects : Reflects)
    (van : VT.VanishingBound A.bnd)
    where

    Comp-M : FC._⇒^ω_ RO.Ao Mid
    Comp-M = compFam , qbComp

    MD-mach : FC._⇒^ω_ Mid RO.Bo
    MD-mach = mdFam , qbMD

    General-M : FC._⇒^ω_ RO.Ao RO.Bo
    General-M = genFam , qbGen

    private
      advEq : ∀ Y E m j d → (∀ u → ctxRun Y E m j (conj u) ≈Mℚ run⊥ ⟦ u ⟧cl d)
            → adv⊥ (ctxRun Y E m j (proj₁ General-M j))
                   (ctxRun Y E m j (proj₁ (MD-mach Cω.∘ Comp-M) j))
            ≡ adv ⟦ A.genM j ⟧cl ⟦ A.mdM j ⊚ A.compM j ⟧cl d
      -- Every implicit here is pinned by an ascribed statement: the `≈Mℚ`
      -- relation mentions only `entries`, so an inferred distribution strands
      -- `mass-1` as a meta (cf. the `>>=⊥-cong` note in `MerkleDamgard`).
      advEq Y E m j d eq = cong₂ (λ a b → ∣ a -ℚ b ∣ℚ) real ideal
        where
        real : Pr₁⊥ (ctxRun Y E m j (proj₁ General-M j))
             ≡ Pr₁⊥ (run⊥ ⟦ A.genM j ⟧cl d)
        real = Pr₁⊥-cong (ctxRun Y E m j (conj (A.genM j)))
                         (run⊥ ⟦ A.genM j ⟧cl d) (eq (A.genM j))

        ideal : Pr₁⊥ (ctxRun Y E m j (proj₁ (MD-mach Cω.∘ Comp-M) j))
              ≡ Pr₁⊥ (run⊥ ⟦ A.mdM j ⊚ A.compM j ⟧cl d)
        ideal = trans (Pr₁⊥-cong (ctxRun Y E m j (mdFam j ⊚ compFam j))
                                 (ctxRun Y E m j (conj (A.mdM j ⊚ A.compM j)))
                                 (ctxRun-cong Y E m j (conj-∘ (A.mdM j) (A.compM j))))
                      (Pr₁⊥-cong (ctxRun Y E m j (conj (A.mdM j ⊚ A.compM j)))
                                 (run⊥ ⟦ A.mdM j ⊚ A.compM j ⟧cl d)
                                 (eq (A.mdM j ⊚ A.compM j)))

    MD-secure : General-M VT.≈ℰ[ A.bnd ] (MD-mach Cω.∘ Comp-M)
    MD-secure Y E m =
      let (p , Pp , h) = reflects Y E m
      in p , Pp , λ j → let (d , le , eq) = h j in
         subst (λ z → z ≤ℚ A.bnd j (p j)) (sym (advEq Y E m j d eq))
               (A.secure j (p j) d le)

    roData : RO.ROData
    roData = record
      { _≈ℰ[_]_        = VT._≈ℰ[_]_
      ; bound          = A.bnd
      ; Comp-M         = Comp-M
      ; MD-mach        = MD-mach
      ; General-M      = General-M
      ; MD-secure      = MD-secure
      ; VanishingBound = VT.VanishingBound
      ; van            = van
      -- `ε` must be pinned: it occurs applied (`ε n (p n)`) inside `≈ℰ[_]`, so
      -- inferring it strands a non-pattern constraint.
      ; absorb         = λ {_} {_} {_} {_} {ε} → VT.absorb {ε = ε}
      ; roIdeal        = General-M
      ; roSimulator    = Cω.id
      ; ideal-bridge   = ST.≈C⇒≈ℰ (ST.sub-identityˡ General-M)
      ; stable         = ST.grade-stableᵗᵛ
      }

    MD≤UC-ROᵗᵛ : (MD-mach Cω.∘ Comp-M) ST.≤UC General-M
    MD≤UC-ROᵗᵛ = RO.Payoff.MD≤UC-RO roData

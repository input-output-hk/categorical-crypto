{-# OPTIONS --safe --without-K #-}

-- A → B does not reflect ≤UC at SSP (`docs/uc-setup-nondeterministic.md` §4).
-- `once` answers with one pick from its one site; `twice` takes one pick from
-- each of two sites and answers with the first.  In B the simulator `copy`
-- forwards each real pick to both ideal sites, so the queues stay equal
-- (`copy-ᵖ`).  In A the simulator is u ⊗ ⌈ ρ ⌉ up to SSP's U-kernel
-- (`ND.SSP.Setup.≤UC⇒relabel`), and ρ routes the one real site to at most one
-- ideal site: after one pick and a query `twice` finds a site empty and dies,
-- while `once` answers.  The run is computed for each value of ρ's route on
-- that site, which `pin` freezes; u never runs.  Statements of `_≤UC_` pass
-- its interfaces and bind its X′, as `ND.SSP.Laws.pick-≤UC` explains.

module CategoricalCrypto.ND.SSP.Reflect where

open import Data.Bool.Base using (Bool; true)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as Pointwise
open import Data.Product
open import Data.Rational using (½; 0ℚ)
open import Data.Rational.Properties using (_≤?_; _<?_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False; toWitness; toWitnessFalse)

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import ProbabilisticLogic.Distribution.RationalDist.Advantage using (advᵇ⊥)

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.ND.SSP.Laws using (at; at-sub)
open import CategoricalCrypto.ND.SSP.Setup using (NDA; NDB; ≤UC-B⇔≤UC; ≤UC⇒relabel)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (runᵖ)
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.SSP.Setup using (module KE; _≈ℰ_; dummy-complete; ≈C⇒≈ᵁ; ≈C⇒≈ℰ; ≈ℰ-trans; ≈ᵁ⇒≈ℰ)

open MonoidalCategory Protᴹ using (module Equiv; module HomReasoning)
open HomReasoning

once : Protocol⁺ (Bool ∷ []) unitᴵ Ωᴵ
once = record { St = ⊤ ; init = tt ; step = λ _ _ _ → choose (inj₁ tt) λ p → ret (tt , p) }

twice : Protocol⁺ (Bool ∷ Bool ∷ []) unitᴵ Ωᴵ
twice = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → choose (inj₁ tt) λ p → choose (inj₂ (inj₁ tt)) λ _ → ret (tt , p) }

f : Protocol unitᴵ ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ)
f = at {B = Ωᴵ} (Bool ∷ []) ⌈ once ⌉

g : Protocol unitᴵ ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ)
g = at {B = Ωᴵ} (Bool ∷ Bool ∷ []) ⌈ twice ⌉

------------------------------------------------------------------------
-- B: copy each real pick to both ideal sites
------------------------------------------------------------------------

copy : Protocol Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧ Cᴵ⟦ Bool ∷ [] ⟧
copy = record
  { St = ⊤ ; init = tt
  ; step = λ where
      _ (inj₁ _) p  → call (inj₁ tt) p λ _ → call (inj₂ (inj₁ tt)) p λ _ → ret (tt , tt)
      _ (inj₂ ()) _ }

copy-ᵖ : ⌈ once ⌉ ≈ᵖ copy ⊗ᵖ wireᵖ {Ωᴵ} ∘ᵖ ⌈ twice ⌉
copy-ᵖ = ≲⇒≈ᵖ record
  { θ = λ (s , q , _) → (tt , tt) , s , q , q , tt
  ; θ-init = refl
  ; θ-step = λ where
      (s , q , _)     (inj₁ (inj₁ _)) p → ret refl
      (s , q , _)     (inj₁ (inj₂ ())) _
      (s , [] , _)    (inj₂ _) _        → dead
      (s , p ∷ q , _) (inj₂ _) _        → ret refl }

B-half : AbstractUC._≤UC_ NDB {A = unitᴵ} {X = unitᴵ , Bool ∷ []} {B = Ωᴵ} {Y = unitᴵ , Bool ∷ Bool ∷ []} f g
B-half {X′} =
  Equivalence.from (≤UC-B⇔≤UC {A = unitᴵ} {B = Ωᴵ} {a = unitᴵ , Bool ∷ []} {b = unitᴵ , Bool ∷ Bool ∷ []} {f = f} {g = g})
    (λ {X″} → dummy-complete (wireᵖ {unitᴵ} ⊗ᵖ copy , ≈C⇒≈ᵁ hom) {X″}) {X′}
  where
  hom : f ≈ᵖ (wireᵖ {unitᴵ} ⊗ᵖ copy) ⊗ᵖ wireᵖ {Ωᴵ} ∘ᵖ g
  hom = Equiv.trans (refl⟩∘⟨_ {f = ⌜ λᴵ {Cᴵ⟦ Bool ∷ [] ⟧} ⌝ ⊗ᵖ wireᵖ {Ωᴵ}} copy-ᵖ)
                    (at-sub {B = Ωᴵ} (Bool ∷ []) (Bool ∷ Bool ∷ []) copy ⌈ twice ⌉)

------------------------------------------------------------------------
-- A: a relabelling feeds at most one ideal site
------------------------------------------------------------------------

Route : Set
Route = Maybe (Σ[ k ∈ Ch Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧ ] (Bool → Q Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧ k))

-- The relabelling routing the one real site by v.
pin : Route → Bool ∷ [] ⇝ Bool ∷ Bool ∷ []
pin v = record
  { route = λ where
      (inj₁ _)  → v
      (inj₂ ())
  ; injective = λ where
      {inj₁ _}  {inj₁ _} _ _ → refl
      {inj₂ ()}
      {inj₁ _}  {inj₂ ()} }

pin-≈ʳ : (ρ : Bool ∷ [] ⇝ Bool ∷ Bool ∷ []) → ρ ≈ʳ pin (route ρ (inj₁ tt))
pin-≈ʳ ρ = mk≈ʳ λ where
  (inj₁ _)  → Pointwise.refl ≐-refl
  (inj₂ ())

-- Push `true`, query, answer with the reply.
test : Protocol ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ) Ωᴵ
test = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → call (inj₁ (inj₂ (inj₁ tt))) true λ _ → call (inj₂ tt) tt λ b → ret (tt , b) }

-- One pick and a query tell `f` from h when their `true` masses are more than
-- ½ apart.
distinguish : {h : Protocol unitᴵ ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ)} → f ≈ℰ h
            → False (advᵇ⊥ true (runᵖ ((test ∘ᵖ f) ∘ᵖ wireᵖ)) (runᵖ ((test ∘ᵖ h) ∘ᵖ wireᵖ)) ≤? ½) → ⊥
distinguish e far = toWitnessFalse far (KE.run∼ e {test} (wireᵖ {unitᴵ}) ½ (toWitness {a? = 0ℚ <? ½} tt) true)

refute : (u : Protocol unitᴵ unitᴵ) (v : Route) → f ≈ℰ (u ⊗ᵖ ⌈ pin v ⌉ʳ) ⊗ᵖ wireᵖ {Ωᴵ} ∘ᵖ g → ⊥
refute u nothing                     e = distinguish e tt
refute u (just (inj₁ _ , _))         e = distinguish e tt
refute u (just (inj₂ (inj₁ _) , _))  e = distinguish e tt
refute u (just (inj₂ (inj₂ ()) , _)) e

A-half : ¬ AbstractUC._≤UC_ NDA {A = unitᴵ} {X = unitᴵ , Bool ∷ []} {B = Ωᴵ} {Y = unitᴵ , Bool ∷ Bool ∷ []} f g
A-half le =
  let s , (u , ρ , s≈) , e = ≤UC⇒relabel {A = unitᴵ} {B = Ωᴵ} {a = unitᴵ , Bool ∷ []} {b = unitᴵ , Bool ∷ Bool ∷ []}
                                          {f = f} {g = g} (λ {X′} → le {X′})
  in refute u (route ρ (inj₁ tt))
       (≈ℰ-trans (≈ᵁ⇒≈ℰ e)
                 (≈C⇒≈ℰ (∘ᵖ-resp-≈ᵖ (⊗ᵖ-resp-≈ᵖ (Equiv.trans s≈ (⊗ᵖ-resp-≈ᵖ (Equiv.refl {x = u})
                                                                         (≲⇒≈ᵖ (⌈⌉ʳ-resp (pin-≈ʳ ρ)))))
                                                (Equiv.refl {x = wireᵖ {Ωᴵ}}))
                                    (Equiv.refl {x = g}))))

-- A → B does not reflect ≤UC: B-emulation by copying, no A-emulation.
¬reflect : Σ[ f ∈ Protocol unitᴵ ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ) ]
           Σ[ g ∈ Protocol unitᴵ ((unitᴵ ⊗ᴵ Cᴵ⟦ Bool ∷ Bool ∷ [] ⟧) ⊗ᴵ Ωᴵ) ]
             AbstractUC._≤UC_ NDB {A = unitᴵ} {X = unitᴵ , Bool ∷ []} {B = Ωᴵ} {Y = unitᴵ , Bool ∷ Bool ∷ []} f g
           × ¬ AbstractUC._≤UC_ NDA {A = unitᴵ} {X = unitᴵ , Bool ∷ []} {B = Ωᴵ} {Y = unitᴵ , Bool ∷ Bool ∷ []} f g
¬reflect = f , g , (λ {X′} → B-half {X′}) , A-half

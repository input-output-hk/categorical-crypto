{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
import Categories.Morphism as Mor

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Function.Base
open import Function.Bundles using (Equivalence)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import ProbabilisticLogic.Dp.Reasoning using (bindᶠ; ≈refl)

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.PM.Choice
open import CategoricalCrypto.ND.PM.Choice.Initialization
open import CategoricalCrypto.ND.PM.Choice.Compose
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Factor.Read
open import CategoricalCrypto.ND.PM.Read
open import CategoricalCrypto.ND.PM.Setup
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction using (≈ᵁ⇒≈ᴿ)
open import CategoricalCrypto.UC.RandomSystems.Morphism using (≈ᴿ⇒≈ᵁ)
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.ND.Grade as Grade
import CategoricalCrypto.UC.Model.Setup as PM

module CategoricalCrypto.ND.PM.Choice.Initialization.Graded where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module N = Grade 𝔾ˢ C
  module P = Category 𝒫ᴵ
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module Q = MonoidalCongruence congᴿ
  variable
    A B : Iface
    S : Set
    S⃗ : List Set

open Mor G.U
open N using (C⟦_⟧; ⌊_⌋)
open import Categories.Morphism.Reasoning G.U
open G.HomReasoning

at : (S⃗ : List Set) → Proc⁺ S⃗ A B → ifaceᵒ A G.⇒ ⌊ G.unit , S⃗ ⌋ G.⊗₀ ifaceᵒ B
at {A} {B} S⃗ p = (G.unitorˡ.to G.⊗₁ G.id) G.∘ ⌈_⌉ {S⃗} {A} {B} p

private
  discard : Pos (Cᶠ []) ⊎ Pos B → Pos B
  discard (inj₁ ())
  discard (inj₂ b) = b

  erase-wire : P._≈_ {Cᶠ [] ⊗ᴵ B} {B}
    (plugᴹ {Cᶠ []} {B} nilᶠ⁻¹) (wireᴹ {Cᶠ [] ⊗ᴵ B} {B} (discard {B}) inj₂)
  erase-wire = ∘-wire MS.reflᴹ (sub-wire _ _)
    MS.○ᴹ wire-cong (λ { (inj₁ ()) ; (inj₂ _) → Eq.refl })
      (λ _ → Eq.refl)

  reads-hom : {f : ifaceᵒ A G.⇒ ifaceᵒ B} {p : Proc A B} →
    Reads (ifaceᶠ A) (ifaceᶠ B) f p → f G.≈ procᵒ p
  reads-hom e = ⟺ G.identityˡ ○ e ○ G.identityʳ

  reads-close : (resolver : Proc (Cᶠ S⃗) 𝟭ᴵ) (p : Proc⁺ S⃗ A B) →
    G.unitorˡ.from G.∘ (conjugate (flat S⃗) unitᶠ resolver G.⊗₁ G.id) G.∘ ⌈_⌉ {S⃗} {A} {B} p
    G.≈ procᵒ (P._∘_ {A} {Cᶠ S⃗ ⊗ᴵ B} {B} (plugᴹ resolver) p)
  reads-close {S⃗} {A} {B} resolver p = reads-hom
    (reads-resp {x = ifaceᶠ A} {y = ifaceᶠ B} G.Equiv.refl
      (P.sym-assoc {A} {Cᶠ S⃗ ⊗ᴵ B} {𝟭ᴵ ⊗ᴵ B} {B})
      (reads-∘ {x = ifaceᶠ A} {y = unitᶠ ⊗ᶠ ifaceᶠ B} {z = ifaceᶠ B}
        (reads-λ (ifaceᶠ B))
        (reads-∘ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B} {z = unitᶠ ⊗ᶠ ifaceᶠ B}
          (reads-sub {x = flat S⃗} {y = unitᶠ} {z = ifaceᶠ B}
            (reads-conjugate (flat S⃗) unitᶠ resolver)) (reads-compile {S⃗} {A} {B} p))))

  branch-close : (branches : S → Proc⁺ [] A B) (s : S) (resolver : Proc (Cᶠ (S ∷ [])) 𝟭ᴵ) →
    G.unitorˡ.from G.∘ ⌈_⌉ {[]} {A} {B} (branches s)
    G.≈ procᵒ (Resolution.branch branches resolver s)
  branch-close {S} {A} {B} branches s resolver =
    ⟺ (refl⟩∘⟨ ((G.⊗.F-resp-≈
      (reads⇒≈ {x = flat []} {y = unitᶠ}
        (reads-conjugate (flat []) unitᶠ nilᶠ⁻¹) reads-nil⁻¹ , G.Equiv.refl)
      ○ G.⊗.identity) ⟩∘⟨refl ○ G.identityˡ))
    ○ reads-close {[]} {A} {B} nilᶠ⁻¹ (branches s)
    ○ ≈ᴹ⇒≈ᵒ (P.∘-resp-≈ˡ {A} {Cᶠ [] ⊗ᴵ B} {B} erase-wire
      MS.○ᴹ wire-∘ᴹ (discard {B}) inj₂ (branches s)
      MS.○ᴹ MS.≲⇒≈ᴹ (MS.mk-cong λ _ → bindᶠ λ where
        (_ , inj₁ _) → ≈refl
        (_ , inj₂ (inj₁ ()))
        (_ , inj₂ (inj₂ _)) → ≈refl))

  insert-sim : (k : C⟦ S⃗ ⟧ G.⇒ G.unit) → ⌊ G.unit , S⃗ ⌋ G.⇒ ⌊ G.unit , [] ⌋
  insert-sim k = G.unitorˡ.to G.∘ k G.∘ G.unitorˡ.from

  insert-factor : (k : C⟦ S⃗ ⟧ G.⇒ G.unit) (p : Proc⁺ S⃗ A B) →
    (insert-sim {S⃗} k G.⊗₁ G.id) G.∘ at {A} {B} S⃗ p
    G.≈ (G.unitorˡ.to G.⊗₁ G.id) G.∘ (k G.⊗₁ G.id) G.∘ ⌈_⌉ {S⃗} {A} {B} p
  insert-factor k p = G.sym-assoc
    ○ ⟺ G.⊗.homomorphism ⟩∘⟨refl
    ○ G.⊗.F-resp-≈ ((G.assoc ○ refl⟩∘⟨ cancelʳ G.unitorˡ.isoʳ) , G.Equiv.refl) ⟩∘⟨refl
    ○ G.⊗.homomorphism ⟩∘⟨refl ○ G.assoc

  cancel-unit : {f g : ifaceᵒ A G.⇒ G.unit G.⊗₀ ifaceᵒ B} →
    (G.unitorˡ.from G.∘ f) Q.∼ (G.unitorˡ.from G.∘ g) → f Q.∼ g
  cancel-unit e = Q.∼.trans (Q.≈⇒∼ (⟺ (cancelˡ G.unitorˡ.isoˡ)))
    (Q.∼.trans (Q.∘-resp-∼ Q.∼.refl e) (Q.≈⇒∼ (cancelˡ G.unitorˡ.isoˡ)))

constant-pick-≤UC-B : (branches : S → Proc⁺ [] A B) (s : S) → Constant.TotalInitialization branches s →
  AbstractUC._≤UC_ NDB {A = ifaceᵒ A} {X = G.unit , []} {B = ifaceᵒ B} {Y = G.unit , S ∷ []}
    (at [] (branches s)) (at (S ∷ []) (choose {S} {[]} {A} {B} branches))
constant-pick-≤UC-B {S} {A} {B} branches s total {X′} =
  Equivalence.from (≤UC-B⇔≤UC {A = ifaceᵒ A} {B = ifaceᵒ B}
    {a = G.unit , []} {b = G.unit , S ∷ []}
    {f = at [] (branches s)} {g = at (S ∷ []) (choose {S} {[]} {A} {B} branches)})
    (PM.dummy-complete (insert-sim {S ∷ []} k , ≈ᴿ⇒≈ᵁ at-agreement)) {X′}
  where
  k = conjugate (flat (S ∷ [])) unitᶠ (constant-pick s)

  closed-agreement : (G.unitorˡ.from G.∘ ⌈_⌉ {[]} {A} {B} (branches s)) Q.∼
    (G.unitorˡ.from G.∘ (k G.⊗₁ G.id) G.∘ ⌈_⌉ {S ∷ []} {A} {B} (choose {S} {[]} {A} {B} branches))
  closed-agreement = Q.∼.trans (Q.≈⇒∼ (branch-close branches s (constant-pick s)))
    (Q.∼.trans (Q.∼.sym (≈ᴿ⇒∼ᴿ (Constant.constant-pick-≈ᴿ branches s total)))
      (Q.≈⇒∼ (⟺ (reads-close {S ∷ []} {A} {B} (constant-pick s)
        (choose {S} {[]} {A} {B} branches)))))

  at-agreement : at [] (branches s) Q.∼
    ((insert-sim {S ∷ []} k G.⊗₁ G.id) G.∘ at (S ∷ []) (choose {S} {[]} {A} {B} branches))
  at-agreement = Q.∼.trans (Q.∘-resp-∼ Q.∼.refl (cancel-unit closed-agreement))
    (Q.≈⇒∼ (⟺ (insert-factor {S ∷ []} {A} {B} k (choose {S} {[]} {A} {B} branches))))

private
  opaque
    unfolding procᵒ unprocᵒ

    proc-unproc : {f : ifaceᵒ A G.⇒ ifaceᵒ B} → f G.≈ procᵒ (unprocᵒ f)
    proc-unproc = G.Equiv.refl

    images⇒≈ : {p q : Proc A B} → procᵒ p G.≈ procᵒ q → P._≈_ {A} {B} p q
    images⇒≈ = ≈ᵒ⇒≈ᴹ

    images⇒≈ᴿ : {p q : Proc A B} → procᵒ p Q.∼ procᵒ q → p ≈ᴿ q
    images⇒≈ᴿ = ∼ᴿ⇒≈ᴿ

  unresolver : C⟦ S⃗ ⟧ G.⇒ G.unit → Proc (Cᶠ S⃗) 𝟭ᴵ
  unresolver {S⃗} k = unprocᵒ (_≅_.from 𝟭ᵒ≅ G.∘ k G.∘ ψ.to S⃗)

  unresolver-reads : (k : C⟦ S⃗ ⟧ G.⇒ G.unit) → Reads (flat S⃗) unitᶠ k (unresolver {S⃗} k)
  unresolver-reads {S⃗} k = ⟺ (⟺ proc-unproc ⟩∘⟨refl ○ G.assoc
    ○ refl⟩∘⟨ cancelʳ (ψ.isoˡ S⃗))

  close-unresolver : (k : C⟦ S⃗ ⟧ G.⇒ G.unit) (p : Proc⁺ S⃗ A B) →
    G.unitorˡ.from G.∘ (k G.⊗₁ G.id) G.∘ ⌈_⌉ {S⃗} {A} {B} p
    G.≈ procᵒ (P._∘_ {A} {Cᶠ S⃗ ⊗ᴵ B} {B} (plugᴹ (unresolver {S⃗} k)) p)
  close-unresolver {S⃗} {A} {B} k p = reads-hom
    (reads-resp {x = ifaceᶠ A} {y = ifaceᶠ B} G.Equiv.refl
      (P.sym-assoc {A} {Cᶠ S⃗ ⊗ᴵ B} {𝟭ᴵ ⊗ᴵ B} {B})
      (reads-∘ {x = ifaceᶠ A} {y = unitᶠ ⊗ᶠ ifaceᶠ B} {z = ifaceᶠ B} (reads-λ (ifaceᶠ B))
        (reads-∘ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B} {z = unitᶠ ⊗ᶠ ifaceᶠ B}
          (reads-sub {x = flat S⃗} {y = unitᶠ} {z = ifaceᶠ B} (unresolver-reads {S⃗} k))
          (reads-compile {S⃗} {A} {B} p))))

plain-branch : (p : Proc A B) (s : S) (resolver : Proc (Cᶠ (S ∷ [])) 𝟭ᴵ) →
  P._≈_ {A} {B} (Resolution.branch (λ _ → plain p) resolver s) p
plain-branch p s resolver = images⇒≈ (⟺ (branch-close (λ _ → plain p) s resolver)
  ○ refl⟩∘⟨ ⌈⌉-plain p ○ cancelˡ G.unitorˡ.isoʳ)

B-emulation⇒closed-resolver : (p : Proc A B) (q : Proc⁺ S⃗ A B) →
  AbstractUC._≤UC_ NDB {A = ifaceᵒ A} {X = G.unit , []} {B = ifaceᵒ B} {Y = G.unit , S⃗}
    (at [] (plain p)) (at S⃗ q) →
  Σ[ resolver ∈ Proc (Cᶠ S⃗) 𝟭ᴵ ] p ≈ᴿ P._∘_ {A} {Cᶠ S⃗ ⊗ᴵ B} {B} (plugᴹ resolver) q
B-emulation⇒closed-resolver {A} {B} {S⃗} p q emulation = unresolver {S⃗} k ,
  images⇒≈ᴿ (Q.∼.trans (Q.≈⇒∼ (⟺ left))
    (Q.∼.trans (Q.∘-resp-∼ Q.∼.refl (≈ᵁ⇒≈ᴿ equality))
      (Q.≈⇒∼ (right ○ close-unresolver {S⃗} {A} {B} k q))))
  where
  witness = PM.≤UC⇒dummy (Equivalence.to
    (≤UC-B⇔≤UC {A = ifaceᵒ A} {B = ifaceᵒ B} {a = G.unit , []} {b = G.unit , S⃗}
      {f = at [] (plain p)} {g = at S⃗ q}) emulation)
  simulator = proj₁ witness
  equality = proj₂ witness
  k = G.unitorˡ.from G.∘ simulator G.∘ G.unitorˡ.to
  project = G.unitorˡ.from G.∘ (G.unitorˡ.from G.⊗₁ G.id {ifaceᵒ B})

  left : project G.∘ at [] (plain p) G.≈ procᵒ p
  left = G.assoc ○ refl⟩∘⟨ cancelˡ (⟺ G.⊗.homomorphism
    ○ G.⊗.F-resp-≈ (G.unitorˡ.isoʳ , G.identity²) ○ G.⊗.identity)
    ○ refl⟩∘⟨ ⌈⌉-plain p ○ cancelˡ G.unitorˡ.isoʳ

  right : project G.∘ (simulator G.⊗₁ G.id) G.∘ at S⃗ q
    G.≈ G.unitorˡ.from G.∘ (k G.⊗₁ G.id) G.∘ ⌈_⌉ {S⃗} {A} {B} q
  right = G.assoc ○ refl⟩∘⟨ (G.sym-assoc ○ ⟺ G.⊗.homomorphism ⟩∘⟨refl
    ○ G.sym-assoc ○ ⟺ G.⊗.homomorphism ⟩∘⟨refl
    ○ G.⊗.F-resp-≈ (G.assoc , (G.identityʳ ○ G.identity²)) ⟩∘⟨refl)

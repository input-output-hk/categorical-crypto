{-# OPTIONS --safe --without-K --guardedness #-}

-- The choice factors of ND at PM (`docs/uc-setup-nondeterministic.md` §2.1):
-- `C S` is the interface ⊤ ⇿ S of `𝔾ᵒ` — a request up, a pick down — and the
-- choice part of a grade, C⟦ S⃗ ⟧, is `ND.Grade`'s fold of them.  A process
-- sees the sites flat, `Cᶠ S⃗`: a request names a site and a pick is a site
-- with its value (`ND.Relabel.Pick`), in the site indices relabellings route.
-- `ψ` reads the fold flat, one wire per factor, and carries the regrouping
-- `C++` to the flat concatenation `joinᶠ`, its inverse to `splitᶠ`
-- (`ψ-C++`, `ψ-C++⁻¹`).
--
-- Measured warm: 44 s, 1.5 GB residency; `-M3G` exhausts (the two proofs
-- under the seal), `-M6G -H1G` checks, as `UC.Bracket.Monoidal` does.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
import Categories.Morphism as Mor

open import Data.Empty.Polymorphic as P using ()
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.Relabel using (Pick; splitPick; joinPick; splitPick-cons)
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧; join; split)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire

import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Utilities as MU
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.ND.Grade as Grade
import CategoricalCrypto.SSP.Iface as SSP

module CategoricalCrypto.ND.PM.Factor where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module 𝒫 = Category 𝒫ᴵ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open Mor G.U
open MR G.monoidal
open MU G.monoidal using (_⊗ᵢ_)
open import Categories.Morphism.Reasoning G.U using (pullˡ; pushˡ)

C : Set → G.Obj
C S = ifaceᵒ (⊤ ⇿ S)

private module 𝔹 = Grade 𝔾ˢ C

open 𝔹 using (C⟦_⟧)

Cᶠ : List Set → Iface
Cᶠ S⃗ = SSP.Ch Cᴵ⟦ S⃗ ⟧ ⇿ Pick S⃗

------------------------------------------------------------------------
-- The flat wires

nilᶠ : Proc 𝟭ᴵ (Cᶠ [])
nilᶠ = wireᴹ P.⊥-elim λ { (() , _) }

nilᶠ⁻¹ : Proc (Cᶠ []) 𝟭ᴵ
nilᶠ⁻¹ = wireᴹ (λ ()) P.⊥-elim

private
  unconsPick : (S : Set) (S⃗ : List Set) → Pick (S ∷ S⃗) → S ⊎ Pick S⃗
  unconsPick _ _ (inj₁ _ , s) = inj₁ s
  unconsPick _ _ (inj₂ i , p) = inj₂ (i , p)

  consPick : (S : Set) (S⃗ : List Set) → S ⊎ Pick S⃗ → Pick (S ∷ S⃗)
  consPick _ _ (inj₁ s)       = inj₁ tt , s
  consPick _ _ (inj₂ (i , p)) = inj₂ i , p

consᶠ : (S : Set) (S⃗ : List Set) → Proc ((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗) (Cᶠ (S ∷ S⃗))
consᶠ S S⃗ = wireᴹ (λ c → c) (unconsPick S S⃗)

unconsᶠ : (S : Set) (S⃗ : List Set) → Proc (Cᶠ (S ∷ S⃗)) ((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗)
unconsᶠ S S⃗ = wireᴹ (λ c → c) (consPick S S⃗)

joinᶠ : (S⃗ T⃗ : List Set) → Proc (Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) (Cᶠ (S⃗ ++ T⃗))
joinᶠ S⃗ T⃗ = wireᴹ (SSP.ch (join S⃗ T⃗)) (splitPick S⃗ T⃗)

splitᶠ : (S⃗ T⃗ : List Set) → Proc (Cᶠ (S⃗ ++ T⃗)) (Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗)
splitᶠ S⃗ T⃗ = wireᴹ (SSP.ch (split S⃗ T⃗)) (joinPick S⃗ T⃗)

private
  wire² : {A : Iface} {up : Pos A → Pos A} {down : Neg A → Neg A}
        → (∀ p → up p ≡ p) → (∀ n → down n ≡ n) → 𝒫._≈_ {A} {A} (wireᴹ up down) (𝒫.id {A})
  wire² eu ed = wire-cong eu ed S.○ᴹ wire-id

  nil-isoˡ : 𝒫._≈_ {𝟭ᴵ} {𝟭ᴵ} (nilᶠ⁻¹ 𝒫.∘ nilᶠ) (𝒫.id {𝟭ᴵ})
  nil-isoˡ = wire∘wire {B = Cᶠ []} {C = 𝟭ᴵ} {A = 𝟭ᴵ} _ _ _ _ S.○ᴹ wire² (λ p → P.⊥-elim p) (λ n → P.⊥-elim n)

  nil-isoʳ : 𝒫._≈_ {Cᶠ []} {Cᶠ []} (nilᶠ 𝒫.∘ nilᶠ⁻¹) (𝒫.id {Cᶠ []})
  nil-isoʳ = wire∘wire {B = 𝟭ᴵ} {C = Cᶠ []} {A = Cᶠ []} _ _ _ _ S.○ᴹ wire² (λ ()) λ { (() , _) }

  cons-isoˡ : (S : Set) (S⃗ : List Set)
            → 𝒫._≈_ {(⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} {(⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} (unconsᶠ S S⃗ 𝒫.∘ consᶠ S S⃗) 𝒫.id
  cons-isoˡ S S⃗ = wire∘wire {B = Cᶠ (S ∷ S⃗)} {C = (⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} {A = (⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} _ _ _ _
    S.○ᴹ wire² (λ _ → refl) λ where
    (inj₁ _)       → refl
    (inj₂ (_ , _)) → refl

  cons-isoʳ : (S : Set) (S⃗ : List Set) → 𝒫._≈_ {Cᶠ (S ∷ S⃗)} {Cᶠ (S ∷ S⃗)} (consᶠ S S⃗ 𝒫.∘ unconsᶠ S S⃗) 𝒫.id
  cons-isoʳ S S⃗ = wire∘wire {B = (⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} {C = Cᶠ (S ∷ S⃗)} {A = Cᶠ (S ∷ S⃗)} _ _ _ _
    S.○ᴹ wire² (λ _ → refl) λ where
    (inj₁ _ , _) → refl
    (inj₂ _ , _) → refl

------------------------------------------------------------------------
-- The fold, read flat

ψ : (S⃗ : List Set) → C⟦ S⃗ ⟧ ≅ ifaceᵒ (Cᶠ S⃗)
ψ []      = ≅.trans 𝟭ᵒ≅ (procᵒ-≅ nilᶠ nilᶠ⁻¹ nil-isoˡ nil-isoʳ)
ψ (S ∷ S⃗) = ≅.trans (≅.refl ⊗ᵢ ψ S⃗)
                    (≅.trans (⊗ᵒ≅ (⊤ ⇿ S) (Cᶠ S⃗)) (procᵒ-≅ (consᶠ S S⃗) (unconsᶠ S S⃗) (cons-isoˡ S S⃗) (cons-isoʳ S S⃗)))

module ψ (S⃗ : List Set) = _≅_ (ψ S⃗)

------------------------------------------------------------------------
-- The regrouping, flat

private
  -- The unitor and associator steps of `C++`'s recursion, as wires.
  nil-join : (T⃗ : List Set) → 𝒫._≈_ {𝟭ᴵ ⊗ᴵ Cᶠ T⃗} {Cᶠ T⃗} λᴵ (joinᶠ [] T⃗ 𝒫.∘ subᴵ nilᶠ)
  nil-join T⃗ = S.⟺ᴹ (∘-wire {𝟭ᴵ ⊗ᴵ Cᶠ T⃗} {Cᶠ [] ⊗ᴵ Cᶠ T⃗} {Cᶠ T⃗} S.reflᴹ (sub-wire _ _) S.○ᴹ wire-cong
    (λ { (inj₁ p) → P.⊥-elim p ; (inj₂ _) → refl })
    (λ _ → refl))

  nil-split : (T⃗ : List Set)
            → 𝒫._≈_ {Cᶠ T⃗} {Cᶠ [] ⊗ᴵ Cᶠ T⃗} (subᴵ nilᶠ 𝒫.∘ wireᴹ {Cᶠ T⃗} {𝟭ᴵ ⊗ᴵ Cᶠ T⃗} inj₂ drop⇒ˡ) (splitᶠ [] T⃗)
  nil-split T⃗ = ∘-wire {Cᶠ T⃗} {𝟭ᴵ ⊗ᴵ Cᶠ T⃗} {Cᶠ [] ⊗ᴵ Cᶠ T⃗} (sub-wire _ _) S.reflᴹ S.○ᴹ wire-cong
    (λ _ → refl)
    (λ { (inj₁ (() , _)) ; (inj₂ _) → refl })

  cons-join : (S : Set) (S⃗ T⃗ : List Set)
            → 𝒫._≈_ {((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗) ⊗ᴵ Cᶠ T⃗} {Cᶠ (S ∷ S⃗ ++ T⃗)}
                (consᶠ S (S⃗ ++ T⃗) 𝒫.∘ (T₁ᴵ (⊤ ⇿ S) (joinᶠ S⃗ T⃗) 𝒫.∘ a⇒ᴵ {⊤ ⇿ S} {Cᶠ S⃗} {Cᶠ T⃗}))
                (joinᶠ (S ∷ S⃗) T⃗ 𝒫.∘ subᴵ (consᶠ S S⃗))
  cons-join S S⃗ T⃗ =
       ∘-wire {X₀} {(⊤ ⇿ S) ⊗ᴵ Cᶠ (S⃗ ++ T⃗)} {Cᶠ (S ∷ S⃗ ++ T⃗)} S.reflᴹ
         (∘-wire {X₀} {(⊤ ⇿ S) ⊗ᴵ (Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗)} {(⊤ ⇿ S) ⊗ᴵ Cᶠ (S⃗ ++ T⃗)} (T₁-wire _ _) S.reflᴹ)
    S.○ᴹ wire-cong up down
    S.○ᴹ S.⟺ᴹ (∘-wire {X₀} {Cᶠ (S ∷ S⃗) ⊗ᴵ Cᶠ T⃗} {Cᶠ (S ∷ S⃗ ++ T⃗)} S.reflᴹ (sub-wire _ _))
    where
    X₀ = ((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗) ⊗ᴵ Cᶠ T⃗

    up : (x : (⊤ ⊎ SSP.Ch Cᴵ⟦ S⃗ ⟧) ⊎ SSP.Ch Cᴵ⟦ T⃗ ⟧)
       → Sum.map (λ y → y) (SSP.ch (join S⃗ T⃗)) (Sum.assocʳ x) ≡ SSP.ch (join (S ∷ S⃗) T⃗) (Sum.map (λ y → y) (λ y → y) x)
    up (inj₁ (inj₁ _)) = refl
    up (inj₁ (inj₂ _)) = refl
    up (inj₂ _)        = refl

    shift : (z : Pick S⃗ ⊎ Pick T⃗)
          → Sum.assocˡ (inj₂ z) ≡ Sum.map (unconsPick S S⃗) (λ y → y) (Sum.map₁ (λ (i , q) → inj₂ i , q) z)
    shift (inj₁ _) = refl
    shift (inj₂ _) = refl

    down : (n : Pick (S ∷ S⃗ ++ T⃗))
         → Sum.assocˡ (Sum.map (λ y → y) (splitPick S⃗ T⃗) (unconsPick S (S⃗ ++ T⃗) n))
           ≡ Sum.map (unconsPick S S⃗) (λ y → y) (splitPick (S ∷ S⃗) T⃗ n)
    down (inj₁ _ , _) = refl
    down (inj₂ c , p) = trans (shift (splitPick S⃗ T⃗ (c , p)))
                              (sym (cong (Sum.map (unconsPick S S⃗) (λ y → y)) (splitPick-cons S S⃗ T⃗ c p)))

  cons-split : (S : Set) (S⃗ T⃗ : List Set)
             → 𝒫._≈_ {(⊤ ⇿ S) ⊗ᴵ Cᶠ (S⃗ ++ T⃗)} {Cᶠ (S ∷ S⃗) ⊗ᴵ Cᶠ T⃗}
                 (subᴵ (consᶠ S S⃗) 𝒫.∘ (a⇐ᴵ {⊤ ⇿ S} {Cᶠ S⃗} {Cᶠ T⃗} 𝒫.∘ T₁ᴵ (⊤ ⇿ S) (splitᶠ S⃗ T⃗)))
                 (splitᶠ (S ∷ S⃗) T⃗ 𝒫.∘ consᶠ S (S⃗ ++ T⃗))
  cons-split S S⃗ T⃗ =
       ∘-wire {Y₀} {((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗) ⊗ᴵ Cᶠ T⃗} {Cᶠ (S ∷ S⃗) ⊗ᴵ Cᶠ T⃗} (sub-wire _ _)
         (∘-wire {Y₀} {(⊤ ⇿ S) ⊗ᴵ (Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗)} {((⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗) ⊗ᴵ Cᶠ T⃗} S.reflᴹ (T₁-wire _ _))
    S.○ᴹ wire-cong up down
    S.○ᴹ S.⟺ᴹ (∘-wire {Y₀} {Cᶠ (S ∷ S⃗ ++ T⃗)} {Cᶠ (S ∷ S⃗) ⊗ᴵ Cᶠ T⃗} S.reflᴹ S.reflᴹ)
    where
    Y₀ = (⊤ ⇿ S) ⊗ᴵ Cᶠ (S⃗ ++ T⃗)

    up : (x : ⊤ ⊎ SSP.Ch Cᴵ⟦ S⃗ ++ T⃗ ⟧)
       → Sum.map (λ y → y) (λ y → y) (Sum.assocˡ (Sum.map (λ y → y) (SSP.ch (split S⃗ T⃗)) x))
         ≡ SSP.ch (split (S ∷ S⃗) T⃗) x
    up (inj₁ _) = refl
    up (inj₂ c) with SSP.ch (split S⃗ T⃗) c
    ... | inj₁ _ = refl
    ... | inj₂ _ = refl

    down : (n : Pick (S ∷ S⃗) ⊎ Pick T⃗)
         → Sum.map (λ y → y) (joinPick S⃗ T⃗) (Sum.assocʳ (Sum.map (unconsPick S S⃗) (λ y → y) n))
           ≡ unconsPick S (S⃗ ++ T⃗) (joinPick (S ∷ S⃗) T⃗ n)
    down (inj₁ (inj₁ _ , _)) = refl
    down (inj₁ (inj₂ _ , _)) = refl
    down (inj₂ (_ , _))      = refl

-- Under the seal `procᵒ` and the comparisons are identities, so the flat
-- wires meet `C++`'s unitor and associator steps as `UC.Machine.Dictionary`
-- reads them.  Processes stay wrapped in `procᵒ` so that no object of `𝔾ᵒ` is
-- inferred from a `Proc` type (`UC.Machine.𝒫ᴵ`'s comment).
opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ ⊗ᵒ≅ 𝟭ᵒ≅

  ψ-C++ : (S⃗ T⃗ : List Set)
        → ψ.from (S⃗ ++ T⃗) G.∘ 𝔹.C++.from S⃗ T⃗
          G.≈ procᵒ (joinᶠ S⃗ T⃗) G.∘ _≅_.from (⊗ᵒ≅ (Cᶠ S⃗) (Cᶠ T⃗)) G.∘ (ψ.from S⃗ G.⊗₁ ψ.from T⃗)
  ψ-C++ [] T⃗ = begin
    ψ.from T⃗ G.∘ G.unitorˡ.from
      ≈˘⟨ G.unitorˡ-commute-from ⟩
    G.unitorˡ.from G.∘ G.id G.⊗₁ ψ.from T⃗
      ≈⟨ (S.⟺ᴹ (λ⇒-λᴳ {Cᶠ T⃗}) S.○ᴹ nil-join T⃗
          S.○ᴹ G.∘-resp-≈ʳ (sub-⊗₁ {𝟭ᴵ} {Cᶠ []} {Cᶠ T⃗} nilᶠ)) ⟩∘⟨refl ⟩
    (procᵒ (joinᶠ [] T⃗) G.∘ procᵒ nilᶠ G.⊗₁ G.id) G.∘ G.id G.⊗₁ ψ.from T⃗
      ≈⟨ G.assoc ○ refl⟩∘⟨ ⟺ serialize₁₂ ⟩
    procᵒ (joinᶠ [] T⃗) G.∘ procᵒ nilᶠ G.⊗₁ ψ.from T⃗
      ≈˘⟨ refl⟩∘⟨ (G.identityˡ ○ (G.identityʳ ⟩⊗⟨refl)) ⟩
    procᵒ (joinᶠ [] T⃗) G.∘ G.id G.∘ (procᵒ nilᶠ G.∘ G.id) G.⊗₁ ψ.from T⃗ ∎
  ψ-C++ (S ∷ S⃗) T⃗ = begin
    ((procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id) G.∘ G.id G.⊗₁ ψ.from (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ 𝔹.C++.from S⃗ T⃗ G.∘ G.associator.from
      ≈⟨ G.identityʳ ⟩∘⟨refl ⟩∘⟨refl ○ G.assoc ○ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ (ψ.from (S⃗ ++ T⃗) G.∘ 𝔹.C++.from S⃗ T⃗) G.∘ G.associator.from
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (ψ-C++ S⃗ T⃗ ○ refl⟩∘⟨ G.identityˡ)) ⟩∘⟨refl ⟩
    procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ (procᵒ (joinᶠ S⃗ T⃗) G.∘ ψ.from S⃗ G.⊗₁ ψ.from T⃗) G.∘ G.associator.from
      ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ procᵒ (joinᶠ S⃗ T⃗) G.∘ G.id G.⊗₁ (ψ.from S⃗ G.⊗₁ ψ.from T⃗) G.∘ G.associator.from
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ G.assoc-commute-from ⟩
    procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ procᵒ (joinᶠ S⃗ T⃗) G.∘ G.associator.from G.∘ (G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗
      ≈⟨ refl⟩∘⟨ G.sym-assoc ○ G.sym-assoc ⟩
    (procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id G.⊗₁ procᵒ (joinᶠ S⃗ T⃗) G.∘ G.associator.from) G.∘ (G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗
      ≈⟨ (G.∘-resp-≈ʳ (G.∘-resp-≈ (S.⟺ᴹ (T₁-⊗₁ {⊤ ⇿ S} {Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗} {Cᶠ (S⃗ ++ T⃗)} (joinᶠ S⃗ T⃗)))
                                   (S.⟺ᴹ (a⇒-α⇒ {⊤ ⇿ S} {Cᶠ S⃗} {Cᶠ T⃗})))
          ○ cons-join S S⃗ T⃗ ○ refl⟩∘⟨ sub-⊗₁ {(⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} {Cᶠ (S ∷ S⃗)} {Cᶠ T⃗} (consᶠ S S⃗)) ⟩∘⟨refl ⟩
    (procᵒ (joinᶠ (S ∷ S⃗) T⃗) G.∘ procᵒ (consᶠ S S⃗) G.⊗₁ G.id) G.∘ (G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗
      ≈⟨ G.assoc ○ refl⟩∘⟨ ⟺ G.⊗.homomorphism ⟩
    procᵒ (joinᶠ (S ∷ S⃗) T⃗) G.∘ (procᵒ (consᶠ S S⃗) G.∘ G.id G.⊗₁ ψ.from S⃗) G.⊗₁ (G.id G.∘ ψ.from T⃗)
      ≈˘⟨ refl⟩∘⟨ (G.identityˡ ○ ((G.identityʳ ⟩∘⟨refl) ⟩⊗⟨ ⟺ G.identityˡ)) ⟩
    procᵒ (joinᶠ (S ∷ S⃗) T⃗) G.∘ G.id G.∘ ((procᵒ (consᶠ S S⃗) G.∘ G.id) G.∘ G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗ ∎

  ψ-C++⁻¹ : (S⃗ T⃗ : List Set)
          → (ψ.from S⃗ G.⊗₁ ψ.from T⃗) G.∘ 𝔹.C++.to S⃗ T⃗
            G.≈ _≅_.to (⊗ᵒ≅ (Cᶠ S⃗) (Cᶠ T⃗)) G.∘ procᵒ (splitᶠ S⃗ T⃗) G.∘ ψ.from (S⃗ ++ T⃗)
  ψ-C++⁻¹ [] T⃗ = begin
    ((procᵒ nilᶠ G.∘ G.id) G.⊗₁ ψ.from T⃗) G.∘ G.unitorˡ.to
      ≈⟨ (G.identityʳ ⟩⊗⟨refl ○ serialize₁₂) ⟩∘⟨refl ○ G.assoc ⟩
    procᵒ nilᶠ G.⊗₁ G.id G.∘ G.id G.⊗₁ ψ.from T⃗ G.∘ G.unitorˡ.to
      ≈˘⟨ refl⟩∘⟨ G.unitorˡ-commute-to ⟩
    procᵒ nilᶠ G.⊗₁ G.id G.∘ G.unitorˡ.to G.∘ ψ.from T⃗
      ≈⟨ G.sym-assoc ○ (G.∘-resp-≈ (S.⟺ᴹ (sub-⊗₁ {𝟭ᴵ} {Cᶠ []} {Cᶠ T⃗} nilᶠ)) (S.⟺ᴹ (λ⇐-λᴳ {Cᶠ T⃗}))
                        S.○ᴹ nil-split T⃗) ⟩∘⟨refl ⟩
    procᵒ (splitᶠ [] T⃗) G.∘ ψ.from T⃗
      ≈˘⟨ G.identityˡ ⟩
    G.id G.∘ procᵒ (splitᶠ [] T⃗) G.∘ ψ.from T⃗ ∎
  ψ-C++⁻¹ (S ∷ S⃗) T⃗ = begin
    (((procᵒ (consᶠ S S⃗) G.∘ G.id) G.∘ G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗) G.∘ G.associator.to G.∘ G.id G.⊗₁ 𝔹.C++.to S⃗ T⃗
      ≈⟨ (((G.identityʳ ⟩∘⟨refl) ⟩⊗⟨ ⟺ G.identityˡ) ○ G.⊗.homomorphism) ⟩∘⟨refl ○ G.assoc ⟩
    procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ (G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗ G.∘ G.associator.to G.∘ G.id G.⊗₁ 𝔹.C++.to S⃗ T⃗
      ≈⟨ refl⟩∘⟨ G.sym-assoc ⟩
    procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ ((G.id G.⊗₁ ψ.from S⃗) G.⊗₁ ψ.from T⃗ G.∘ G.associator.to) G.∘ G.id G.⊗₁ 𝔹.C++.to S⃗ T⃗
      ≈˘⟨ refl⟩∘⟨ G.assoc-commute-to ⟩∘⟨refl ⟩
    procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ (G.associator.to G.∘ G.id G.⊗₁ (ψ.from S⃗ G.⊗₁ ψ.from T⃗)) G.∘ G.id G.⊗₁ 𝔹.C++.to S⃗ T⃗
      ≈⟨ refl⟩∘⟨ G.assoc ○ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ G.associator.to G.∘ G.id G.⊗₁ ((ψ.from S⃗ G.⊗₁ ψ.from T⃗) G.∘ 𝔹.C++.to S⃗ T⃗)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ (ψ-C++⁻¹ S⃗ T⃗ ○ G.identityˡ)) ⟩
    procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ G.associator.to G.∘ G.id G.⊗₁ (procᵒ (splitᶠ S⃗ T⃗) G.∘ ψ.from (S⃗ ++ T⃗))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ○ G.sym-assoc ○ G.sym-assoc ⟩
    ((procᵒ (consᶠ S S⃗) G.⊗₁ G.id G.∘ G.associator.to) G.∘ G.id G.⊗₁ procᵒ (splitᶠ S⃗ T⃗)) G.∘ G.id G.⊗₁ ψ.from (S⃗ ++ T⃗)
      ≈⟨ (G.assoc ○ G.∘-resp-≈ (S.⟺ᴹ (sub-⊗₁ {(⊤ ⇿ S) ⊗ᴵ Cᶠ S⃗} {Cᶠ (S ∷ S⃗)} {Cᶠ T⃗} (consᶠ S S⃗)))
                                (G.∘-resp-≈ (S.⟺ᴹ (a⇐-α⇐ {⊤ ⇿ S} {Cᶠ S⃗} {Cᶠ T⃗}))
                                            (S.⟺ᴹ (T₁-⊗₁ {⊤ ⇿ S} {Cᶠ (S⃗ ++ T⃗)} {Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗} (splitᶠ S⃗ T⃗))))
          ○ cons-split S S⃗ T⃗) ⟩∘⟨refl ⟩
    (procᵒ (splitᶠ (S ∷ S⃗) T⃗) G.∘ procᵒ (consᶠ S (S⃗ ++ T⃗))) G.∘ G.id G.⊗₁ ψ.from (S⃗ ++ T⃗)
      ≈˘⟨ G.identityˡ ○ (refl⟩∘⟨ (G.identityʳ ⟩∘⟨refl)) ○ G.sym-assoc ⟩
    G.id G.∘ procᵒ (splitᶠ (S ∷ S⃗) T⃗) G.∘ (procᵒ (consᶠ S (S⃗ ++ T⃗)) G.∘ G.id) G.∘ G.id G.⊗₁ ψ.from (S⃗ ++ T⃗) ∎

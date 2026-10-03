{-# OPTIONS --safe --without-K #-}

-- Admitted elements as a second index.
--
-- A distance between tests says nothing about what running them costs, so an
-- allowance-restricted model needs one more datum than `Approx.Controlled`
-- carries: which elements a given allowance admits.  The two indices are
-- independent — an allowance transformation is not determined by an error
-- control — so a filtered map carries its own allowance map, a monotone
-- endomap of the allowance poset (stdlib's `PosetHomomorphism`).
--
-- Allowances range over a poset `I`; the query model's is `ℕ⁺`, the rates of its
-- certificates (`UC.Quantitative.Query.filteredᵠ`).

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Morphism.Bundles

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Filtered
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) {i ℓ≈ ℓ≤ : Level} (I : Poset i ℓ≈ ℓ≤) where

open OrderedErrorAlgebra E
open Poset I using (_≈_; _≤_) renaming (Carrier to Ix)
open PosetHomomorphism
open import CategoricalCrypto.Approx.Controlled E
open import CategoricalCrypto.Approx.Space E

private variable c ℓa ℓd : Level

record FilteredSpace (c ℓa ℓd : Level) : Set (suc (c ⊔ ℓa ⊔ ℓd) ⊔ es ⊔ ℓe ⊔ i ⊔ ℓ≤) where
  field
    space : ApproxSpace c ℓa

  open ApproxSpace space public
    using (Carrier; _≈[_]_; ≈[]-refl; ≈[]-sym; ≈[]-trans; ≈[]-trans₀; ≈[]-mono)

  field
    Admit      : Ix → Carrier → Set ℓd
    admit-mono : {q q′ : Ix} {x : Carrier} → q ≤ q′ → Admit q x → Admit q′ x

  admit-resp : {q q′ : Ix} {x : Carrier} → q ≈ q′ → Admit q x → Admit q′ x
  admit-resp eq = admit-mono (Poset.reflexive I eq)

record Filtered (X Y : FilteredSpace c ℓa ℓd) : Set (c ⊔ es ⊔ ℓe ⊔ ℓa ⊔ ℓd ⊔ i ⊔ ℓ≈ ⊔ ℓ≤) where
  private
    module X = FilteredSpace X
    module Y = FilteredSpace Y

  field
    underlying : Controlled X.space Y.space
    allowance  : PosetHomomorphism I I

  map = Controlled.map underlying

  field
    admits : {q : Ix} {x : X.Carrier}
           → X.Admit q x → Y.Admit (⟦ allowance ⟧ q) (map x)

------------------------------------------------------------------------
-- Agreement on the admitted elements

-- What an allowance-restricted model states its bounds about: two maps agree
-- to within an error that may depend on the allowance their argument was
-- admitted at.  `≈ᵃ-pre` and `≈ᵃ-post` are why a filtered map carries two
-- data and not one — each of them moves such a bound in its own way, and
-- neither is derivable from the other.

module _ {X Y : FilteredSpace c ℓa ℓd} where
  private
    module X = FilteredSpace X
    module Y = FilteredSpace Y

  infix 4 _≈ᵃ[_]_

  -- A record and not a definition: the two spaces are projections of the
  -- unfolded quantifier, so nothing would recover them at a use site.
  record _≈ᵃ[_]_ (u : X.Carrier → Y.Carrier) (Ε : Ix → Error)
                 (v : X.Carrier → Y.Carrier) : Set (c ⊔ ℓa ⊔ ℓd ⊔ i) where
    constructor agree
    field admitted : {q : Ix} {x : X.Carrier} → X.Admit q x → u x Y.≈[ Ε q ] v x

  open _≈ᵃ[_]_ public

  private variable
    Ε Δ : Ix → Error
    u u′ v v′ w : X.Carrier → Y.Carrier

  ≈ᵃ-refl : u ≈ᵃ[ (λ _ → ε₀) ] u
  ≈ᵃ-refl = agree λ _ → Y.≈[]-refl

  ≈ᵃ-sym : u ≈ᵃ[ Ε ] v → v ≈ᵃ[ Ε ] u
  ≈ᵃ-sym h = agree λ a → Y.≈[]-sym (admitted h a)

  ≈ᵃ-trans : u ≈ᵃ[ Ε ] v → v ≈ᵃ[ Δ ] w → u ≈ᵃ[ (λ q → Ε q ⊕ Δ q) ] w
  ≈ᵃ-trans h k = agree λ a → Y.≈[]-trans (admitted h a) (admitted k a)

  ≈ᵃ-mono : ((q : Ix) → Ε q ⊑ Δ q) → u ≈ᵃ[ Ε ] v → u ≈ᵃ[ Δ ] v
  ≈ᵃ-mono le h = agree λ a → Y.≈[]-mono (le _) (admitted h a)

  ≈ᵃ-resp₀ : ((x : X.Carrier) → u′ x Y.≈[ ε₀ ] u x)
           → ((x : X.Carrier) → v x Y.≈[ ε₀ ] v′ x) → u ≈ᵃ[ Ε ] v → u′ ≈ᵃ[ Ε ] v′
  ≈ᵃ-resp₀ p q h = agree λ a → resp₀ Y.space (p _) (q _) (admitted h a)

-- Precomposing with a filtered map reindexes the ALLOWANCE the bound is read
-- at, by that map's allowance map and nothing else…
≈ᵃ-pre : {X′ X Y : FilteredSpace c ℓa ℓd} (κ : Filtered X′ X) {Ε : Ix → Error}
         {u v : FilteredSpace.Carrier X → FilteredSpace.Carrier Y}
       → _≈ᵃ[_]_ {X = X} {Y = Y} u Ε v
       → _≈ᵃ[_]_ {X = X′} {Y = Y} (λ x → u (Filtered.map κ x))
                 (λ q → Ε (⟦ Filtered.allowance κ ⟧ q))
                 (λ x → v (Filtered.map κ x))
≈ᵃ-pre κ h = agree λ a → admitted h (Filtered.admits κ a)

-- …and postcomposing with one transforms the ERROR, by its control.
≈ᵃ-post : {X Y Y′ : FilteredSpace c ℓa ℓd} (k : Filtered Y Y′) {Ε : Ix → Error}
          {u v : FilteredSpace.Carrier X → FilteredSpace.Carrier Y}
        → _≈ᵃ[_]_ {X = X} {Y = Y} u Ε v
        → _≈ᵃ[_]_ {X = X} {Y = Y′} (λ x → Filtered.map k (u x))
                  (λ q → Control.at (Controlled.control (Filtered.underlying k)) (Ε q))
                  (λ x → Filtered.map k (v x))
≈ᵃ-post k h = agree λ a → Controlled.preserves (Filtered.underlying k) (admitted h a)

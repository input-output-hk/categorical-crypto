{-# OPTIONS --safe --without-K #-}

-- Exactly what the two inherited theories are, in quantitative terms
-- (`docs/quantitative-uc-setup-plan.typ` §5.3).
--
-- `underlying₀`'s relations are the ε₀ instances of the quantitative ones, and
-- `underlying₊`'s are their all-positive closure — in both cases by commuting
-- quantifiers past `Abstract2.Action`'s element-level reading of the U-kernel,
-- with no new UC axiom.
--
-- `Witness₊` is where the care goes.  It carries ONE simulator good at every
-- positive error, which is what the dummy-adversary theorem hands back; the
-- weaker `(ε : Error) → Positive ε → Witness ε f g` would let the simulator
-- depend on the accuracy and is NOT what `≤UC₊` means.  Fixed positive-error
-- closeness is not transitive at the same error, so it is not itself the
-- equality of any `UCSetup` — only its all-positive closure is.

open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

import CategoricalCrypto.Abstract2.Action as Action

module CategoricalCrypto.UC.Quantitative.Bridge
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Small E
open import CategoricalCrypto.UC.Quantitative E
open import CategoricalCrypto.UC.Quantitative.Witness E

module QBridge {o ℓ e o′ ℓ′ e′ c ℓb : Level}
               (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb) where

  open QWitness S public

  private variable
    A B : 𝒞.Obj
    X Y : ℐ.Obj

  ------------------------------------------------------------------------
  -- Contextual agreement

  -- The ε₀ instance is the U-kernel read at elements, which is what
  -- `Abstract2.Action` already proves in both directions.
  zero-agreement⇒ : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → f ≈ᵁ[ ε₀ ] g
  zero-agreement⇒ = run-resp-≈ᵁ

  zero-agreement⇐ : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ[ ε₀ ] g → f ≈ᵁ g
  zero-agreement⇐ = runs⇒≈ᵁ

  zero-agreement : {f g : A 𝒞.⇒ T₀ X B} → (f ≈ᵁ g) ⇔ (f ≈ᵁ[ ε₀ ] g)
  zero-agreement = mk⇔ zero-agreement⇒ zero-agreement⇐

  positive-agreement⇒ : {f g : A 𝒞.⇒ T₀ X B}
                      → f A₊.≈ᵁ g → (ε : Error) → Positive ε → f ≈ᵁ[ ε ] g
  positive-agreement⇒ h ε pos W e = A₊.run-resp-≈ᵁ h W e ε pos

  positive-agreement⇐ : {f g : A 𝒞.⇒ T₀ X B}
                      → ((ε : Error) → Positive ε → f ≈ᵁ[ ε ] g) → f A₊.≈ᵁ g
  positive-agreement⇐ h = A₊.runs⇒≈ᵁ λ W e ε pos → h ε pos W e

  positive-agreement : {f g : A 𝒞.⇒ T₀ X B}
                     → (f A₊.≈ᵁ g) ⇔ ((ε : Error) → Positive ε → f ≈ᵁ[ ε ] g)
  positive-agreement = mk⇔ positive-agreement⇒ positive-agreement⇐

  ------------------------------------------------------------------------
  -- Emulation

  Witness₊ : (f : A 𝒞.⇒ T₀ X B) (g : A 𝒞.⇒ T₀ Y B)
           → Set (o ⊔ ℓ ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  Witness₊ {X = X} {Y = Y} f g =
    Σ[ s ∈ Y ℐ.⇒ X ] ((ε : Error) → Positive ε → At s ε f g)

  -- Both directions are the existing dummy-adversary theorem, carried across
  -- the agreement equivalence above; the simulator is never re-chosen.
  zero-emulation⇒ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  → f ≤UC g → Witness ε₀ f g
  zero-emulation⇒ le = let s , h = ≤UC⇒dummy le in s , zero-agreement⇒ h

  zero-emulation⇐ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  → Witness ε₀ f g → f ≤UC g
  zero-emulation⇐ (s , h) = dummy-complete (s , zero-agreement⇐ h)

  zero-emulation : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                 → (f ≤UC g) ⇔ Witness ε₀ f g
  zero-emulation = mk⇔ zero-emulation⇒ zero-emulation⇐

  positive-emulation⇒ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                      → f A₊.≤UC g → Witness₊ f g
  positive-emulation⇒ le =
    let s , h = A₊.≤UC⇒dummy le in s , positive-agreement⇒ h

  positive-emulation⇐ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                      → Witness₊ f g → f A₊.≤UC g
  positive-emulation⇐ (s , h) = A₊.dummy-complete (s , positive-agreement⇐ h)

  positive-emulation : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                     → (f A₊.≤UC g) ⇔ Witness₊ f g
  positive-emulation = mk⇔ positive-emulation⇒ positive-emulation⇐

  -- The direction that holds, recorded so the asymmetry this module's header
  -- describes is a checked statement and not only a remark.
  Witness₊⇒Witness : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                   → Witness₊ f g → (ε : Error) → Positive ε → Witness ε f g
  Witness₊⇒Witness (s , h) ε pos = s , h ε pos

  ------------------------------------------------------------------------
  -- Small-error agreement

  -- `underlyingSmall`'s environment equality has its error quantifier INSIDE
  -- the contexts and the hypothesis below has it outside, so only one
  -- direction is a theorem here: the converse is the uniformization
  -- `docs/quantitative-uc-setup-plan.typ` §8 leaves open.  Where the two orders
  -- meet a concrete family, that same asymmetry is
  -- `UC.Approximate.Local.∼ᴺ⇒pointwise`.
  module Small {ℓs : Level} (Sm : SmallClass ℓs) where

    open Collapse Sm c (es ⊔ ℓe ⊔ ℓb) using (Small)

    module Aˢ = Action (underlyingSmall Sm)

    small-agreement⇐ : {f g : A 𝒞.⇒ T₀ X B}
                     → Σ[ ε ∈ Error ] Small ε × f ≈ᵁ[ ε ] g → f Aˢ.≈ᵁ g
    small-agreement⇐ (ε , sε , h) = Aˢ.runs⇒≈ᵁ λ W e → ε , sε , h W e

    small-agreement⇒ : {f g : A 𝒞.⇒ T₀ X B} → f Aˢ.≈ᵁ g
                     → (W : ℐ.Obj) (e : Env (T₀ (W ⊗₀ X) B))
                     → Σ[ ε ∈ Error ] Small ε × run W f e ≈[ ε ] run W g e
    small-agreement⇒ = Aˢ.run-resp-≈ᵁ

    -- …and the simulator crosses unchanged, `dummy-complete` being the only
    -- thing spent.
    small-emulation⇐ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                     → Σ[ s ∈ Y ℐ.⇒ X ] Σ[ ε ∈ Error ] Small ε × At s ε f g
                     → f Aˢ.≤UC g
    small-emulation⇐ (s , ε , sε , h) =
      Aˢ.dummy-complete (s , small-agreement⇐ (ε , sε , h))

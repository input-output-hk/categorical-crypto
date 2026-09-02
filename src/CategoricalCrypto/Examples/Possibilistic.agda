{-# OPTIONS --safe --without-K #-}

-- Possibilistic functionalities: `SFunᵉ` morphisms at the possibility monad,
-- with nondeterminism standing for the adversary's scheduling and corruption
-- choices.
--
-- These are `SFun` morphisms, not UC functionalities.

open import categorical-crypto.Prelude hiding (_>>=_; return)

import Categories.Monad.Setoids.Discrete as Discrete

open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Binary.BagAndSetEquality.Ext
open import Data.List.Relation.Unary.Any

import CategoricalCrypto.SFunM.Kleisli as SFun
import CategoricalCrypto.SFunM.Kleisli.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Kleisli.Properties as SFunProperties
open import ProbabilisticLogic.Distribution.Possibility.Setoids

module CategoricalCrypto.Examples.Possibilistic where

open Discrete (𝒫-KleisliTriple {0ℓ})
open SFun 𝒫-KleisliTriple
open SFunMonoidal 𝒫-KleisliTriple 𝒫-commutative
open SFunProperties 𝒫-KleisliTriple

private variable Msg : Type

-- The link to the original type-level `Machine`: at the discrete setoids the possibility
-- monad is `List` on the nose, so a machine kernel is a `List`-valued function on TYPES —
-- a finitely supported relation `S × A → S × B` — and not a map of setoids.  The other
-- half of the link, that `_≈ᴹ_` here is stdlib set equality, is pinned by `refl` in
-- `Possibility.agda`; the discrete objects sit in the Kleisli category as the *full*
-- subcategory `Discrete.Kleisliᴹ`, so nothing about the type-level notion is lost by
-- taking the monad on `Setoids`.
kernel-on-Types : {A B S : Type} → SFunType A B S ≡ (S × A → List (S × B))
kernel-on-Types = refl

------------------------------------------------------------------------
-- Lossy links

-- A link carries at most one message per round; `nothing` is an idle round.
-- Each round the adversary either lets the message through or blanks it.
lossy : Maybe Msg → List (Maybe Msg)
lossy m = m ∷ nothing ∷ []

Lossy : SFunᵉ (Maybe Msg) (Maybe Msg)
Lossy = kleisliᵉ lossy

_ : eval Lossy (just 1 ∷ []) ≡ (just 1 ∷ []) ∷ (nothing ∷ []) ∷ []
_ = refl

-- Two lossy links in series are one lossy link
Lossy-idempotent : (Lossy {Msg} ∘ᵉ Lossy) ≈ᵉ Lossy
Lossy-idempotent = ≈ᵉ.trans (≈ᵉ.sym (kleisliᵉ-∘ lossy lossy)) (kleisliᵉ-cong step)
  where
  step : (m : Maybe Msg) → (lossy m >>= lossy) ≈ᴹ lossy m
  step m = ∷-cong refl (𝒫.trans (∷-absorb (here refl)) (∷-absorb (here refl)))

-- Decides once and for all whether messages are forwarded (state = true) or
-- dropped (state = false)
Cut : SFunᵉ (Maybe Msg) (Maybe Msg)
Cut = mkᵉ nothing λ where
  (nothing    , m) → (just true , m) ∷ (just false , nothing) ∷ []
  (just true  , m) → return (just true , m)
  (just false , _) → return (just false , nothing)

_ : eval Cut (just 1 ∷ just 2 ∷ [])
  ≡ (just 1 ∷ just 2 ∷ []) ∷ (nothing ∷ nothing ∷ []) ∷ []
_ = refl

Network : SFunᵉ (Maybe Msg ⊎ Maybe Msg) (Maybe Msg ⊎ Maybe Msg)
Network = Lossy ⊗ᵉ Cut

------------------------------------------------------------------------
-- An adversarially scheduled buffer

Buffer : SFunᵉ (Msg ⊎ ⊤) (⊤ ⊎ Maybe Msg)
Buffer = mkᵉ [] [ send ∣ schedule ]ᵏ
  where
  send : SFunType Msg ⊤ (List Msg)
  send (q , m) = return (q ∷ʳ m , tt)

  schedule : SFunType ⊤ (Maybe Msg) (List Msg)
  schedule ([]    , _) = return ([] , nothing)
  schedule (m ∷ q , _) = (q , just m) ∷ (m ∷ q , nothing) ∷ []

_ : eval Buffer (inj₁ 1 ∷ inj₂ tt ∷ [])
  ≡ (inj₁ tt ∷ inj₂ (just 1) ∷ []) ∷ (inj₁ tt ∷ inj₂ nothing ∷ []) ∷ []
_ = refl

------------------------------------------------------------------------
-- A common reference bit

CRS : SFunᵉ ⊤ Bool
CRS = mkᵉ nothing λ where
  (just b  , _) → return (just b , b)
  (nothing , _) → do
    b ← true ∷ false ∷ []
    return (just b , b)

_ : eval CRS (tt ∷ tt ∷ []) ≡ (true ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
_ = refl

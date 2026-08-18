{-# OPTIONS --safe --without-K #-}

-- Possibilistic functionalities: `SFunᵉ` morphisms at the possibility monad,
-- with nondeterminism standing for the adversary's scheduling and corruption
-- choices.  `_≈ᵉ_` compares possibility *sets* of traces.
--
-- These are `SFun` morphisms, not UC functionalities: the G-construction is not
-- applied here, so nothing pairs up ports for us.  A functionality with several
-- ports routes them by hand — `[_∣_]ᵏ` for ports sharing one state, `_⊗ᵉ_` for
-- machines whose states stay apart.

open import categorical-crypto.Prelude

open import Class.Monad.Ext.Setoid

open import Data.List.Relation.Binary.BagAndSetEquality using (∷-cong)
open import Data.List.Relation.Binary.BagAndSetEquality.Ext
open import Data.List.Relation.Unary.Any using (here)

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Properties as SFunProperties
open import ProbabilisticLogic.Distribution.Possibility

module CategoricalCrypto.Examples.Possibilistic where

-- Instantiating the generic layer once keeps `{M = List}` out of every signature.
open SFun {List}
open SFunMonoidal {List}
open SFunProperties {List}

private variable Msg : Type

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

-- Two lossy links in series are one lossy link: the extra blanks the composite
-- can produce are already possible for a single link, and `_≈ᵉ_` is set equality.
Lossy-idempotent : (Lossy {Msg} ∘ᵉ Lossy) ≈ᵉ Lossy
Lossy-idempotent = ≈ᵉ.trans (≈ᵉ.sym (kleisliᵉ-∘ lossy lossy)) (kleisliᵉ-cong step)
  where
  step : (m : Maybe Msg) → (lossy m >>= lossy) ≈ᴹ lossy m
  step m = ∷-cong refl (𝒫.trans (∷-absorb (here refl)) (∷-absorb (here refl)))

-- The link is cut once and for all rather than per round, so the state is what
-- keeps `Cut` apart from `Lossy`: it has two traces of every length, not 2ⁿ.
Cut : SFunᵉ (Maybe Msg) (Maybe Msg)
Cut = mkᵉ nothing λ where
  (nothing    , m) → (just true , m) ∷ (just false , nothing) ∷ []
  (just true  , m) → return (just true , m)
  (just false , _) → return (just false , nothing)

_ : eval Cut (just 1 ∷ just 2 ∷ [])
  ≡ (just 1 ∷ just 2 ∷ []) ∷ (nothing ∷ nothing ∷ []) ∷ []
_ = refl

-- Two links side by side, one dropping per round and one cut once: `_⊗ᵉ_` keeps
-- their states apart, so neither one's losses constrain the other's.
Network : SFunᵉ (Maybe Msg ⊎ Maybe Msg) (Maybe Msg ⊎ Maybe Msg)
Network = Lossy ⊗ᵉ Cut

------------------------------------------------------------------------
-- An adversarially scheduled buffer

-- `F_auth`'s ideal behaviour: the sender port queues a message and is acked, the
-- adversary port asks for the next delivery and may stall instead.  Both ports
-- read and write the one queue, which is why they are joined by `[_∣_]ᵏ` and not
-- by the tensor.
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
-- A common reference string

-- `F_CRS` at one bit: the first query fixes the bit nondeterministically, every
-- later query answers with the same bit.
CRS : SFunᵉ ⊤ Bool
CRS = mkᵉ nothing λ where
  (just b  , _) → return (just b , b)
  (nothing , _) → do
    b ← true ∷ false ∷ []
    return (just b , b)

_ : eval CRS (tt ∷ tt ∷ []) ≡ (true ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
_ = refl

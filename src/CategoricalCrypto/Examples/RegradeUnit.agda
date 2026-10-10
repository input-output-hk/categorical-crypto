{-# OPTIONS --safe --without-K --guardedness #-}

-- `docs/uc-setup-nondeterministic.md` §1.3(e) at PM, the part that needs no run
-- of a scalar.  The reveal pair is ≈ℰ-equal and not ≈ᵁ-equal
-- (`UC.RandomSystems.FullAbstraction`), so along the unit, where ≤UC is ≈ℰ
-- (`Abstract2.Regrade.Unit`), it emulates, while PM's U-kernel separates it:
-- (b) of §1.3 needs its hypothesis.  `Regrade.Unit` is applied by qualified
-- name: copying it as `module PM = Unit Sᵒ.StdSetup` measured 51.6 s and
-- 2.7 GB residency against 13.5 s and 1.2 GB.

open import Data.Bool.Base
open import Function.Bundles
open import Relation.Nullary.Negation.Core

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Quotient
import Categories.Morphism.Reasoning as MR

import CategoricalCrypto.Abstract2.Regrade.Unit as Unit
open import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.UC.Model.Setup as Sᵒ
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction
open import CategoricalCrypto.UC.RandomSystems.Seal

module CategoricalCrypto.Examples.RegradeUnit where

private
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ

r : Bool → ifaceᵒ Aʳ G.⇒ G.unit G.⊗₀ ifaceᵒ Bʳ
r b = Sᵒ.return G.∘ procᵒ (revealᴹ b)

reveal-≈ᵁ|𝟙 : Unit.U.R._≈ᵁ_ Sᵒ.StdSetup (r true) (r false)
reveal-≈ᵁ|𝟙 = Unit.≈ℰ⇒≈ᵁ|𝟙 Sᵒ.StdSetup G.unitorˡ.from G.unitorˡ.isoˡ (Sᵒ.≈ℰ-cong-post Sᵒ.return reveal-≈ℰ)

reveal-≤UC|𝟙 : Unit.U.R._≤UC_ Sᵒ.StdSetup (r true) (r false)
reveal-≤UC|𝟙 = Equivalence.from (Unit.≤UC|𝟙⇔≈ℰ Sᵒ.StdSetup G.unitorˡ.from G.unitorˡ.isoˡ)
                                (Sᵒ.≈ℰ-cong-post Sᵒ.return reveal-≈ℰ)

reveal-≉ᵁ : ¬ (r true Sᵒ.≈ᵁ r false)
reveal-≉ᵁ e = reveal-≁ᴿ (Q.∼.trans (Q.≈⇒∼ (G.Equiv.sym (unr true)))
                          (Q.∼.trans (Q.∘-resp-∼ Q.∼.refl (≈ᵁ⇒≈ᴿ e)) (Q.≈⇒∼ (unr false))))
  where
    unr : (b : Bool) → G.unitorˡ.from G.∘ r b G.≈ procᵒ (revealᴹ b)
    unr _ = MR.cancelˡ G.U G.unitorˡ.isoʳ

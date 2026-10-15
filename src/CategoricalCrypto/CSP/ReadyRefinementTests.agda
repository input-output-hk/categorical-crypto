{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ReadyRefinementTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.Process as Core
import CategoricalCrypto.CSP.ReadyRefinement as Refinement

module P = Core ⊤ Bool ⊤
module R = Refinement ⊤ Bool ⊤
open P
open P.Tree
open R

spec impl : Tree
spec = menu (λ _ → nothing) (λ { false → just stop ; true → just div })
impl = silent stop

strict-refinement : spec ⊑ impl
_⊑_.match strict-refinement (sSil refl) = stop , sTau {i = false} refl refl , reflexive
_⊑_.ready strict-refinement (t , sRet ())
_⊑_.ready strict-refinement (t , sSil ())
_⊑_.ready strict-refinement (t , sVis refl ())
_⊑_.ready strict-refinement (t , sTau refl offered) = stop , sSil refl

spec-divergence : Divergence spec []
spec-divergence = div , silent-step (sTau {i = true} refl refl) done , divergent-div

impl-no-diverges : ¬ (Diverges impl)
impl-no-diverges d = reject (Diverges.step d) (Diverges.rest d)
  where
  reject : ∀ {t} → impl ─[ τ ]→ t → Diverges t → ⊥
  reject (sSil refl) tail = stop-not-divergent tail

stop-end : ∀ {xs t} → Executes stop xs t → t ≡ stop
stop-end done = refl
stop-end (silent-step move rest) = ⊥-elim (stop-no-step move)
stop-end (visible-step move rest) = ⊥-elim (stop-no-step move)

impl-no-divergence : ∀ {xs} → ¬ (Divergence impl xs)
impl-no-divergence (_ , done , d) = impl-no-diverges d
impl-no-divergence (_ , silent-step (sSil refl) rest , d) = stop-not-divergent (subst Diverges (stop-end rest) d)
impl-no-divergence (_ , visible-step (sRet ()) rest , d)
impl-no-divergence (_ , visible-step (sVis () _) rest , d)

not-raw-equality : ¬ (RawAgreement spec impl)
not-raw-equality eq = impl-no-divergence (proj₁ (RawAgreement.divergence-agreement eq []) spec-divergence)

not-reverse : ¬ (impl ⊑ spec)
not-reverse reverse = impl-no-divergence (divergences reverse spec-divergence)

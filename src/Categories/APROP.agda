{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROP (Autonomous PROP) term language, following TensorRocq
-- (arXiv:2604.17592). Thin wrapper around `Categories.FreeMonoidal`
-- specialised to `v = Symm`: the free symmetric monoidal category over a
-- signature `(X , mor)` of atoms and generators.
--
-- Define a signature `mySig : APROPSignature` and `open APROP mySig` to
-- access the term constructors. The generator injection is exposed as
-- `Agen` to match the paper's notation (elsewhere `var`).
--------------------------------------------------------------------------------

module Categories.APROP where

open import Categories.FreeMonoidal public

-- Propositional equality for the whole APROP tree: 47 of the 51 modules that
-- blanket-open this one imported it themselves.  The hidden names are the four
-- the island prelude hides (`[_]` clashes with `Data.List`'s) plus `J`, which
-- `Strict/Embed` defines as a lemma of its own — a name this re-export would
-- otherwise make undefinable there.
open import Relation.Binary.PropositionalEquality public
  hiding (preorder; isPreorder; setoid; [_]; J)

-- `Data.List` for the whole tree: 46 of the 51 blanket-openers imported it
-- themselves, 44 of them with a `using` list.  Only two names are hidden, and
-- in both cases because a scope module wants a DIFFERENT module's function of
-- that name: `splitAt` is `Data.Fin`'s in `Model/FromAPROP`, and `zipWith` is
-- `Data.Maybe.Base`'s in `Solver/Split`.
open import Data.List public
  hiding (splitAt; zipWith)

-- `Data.Product` likewise, for 36 of the openers, all with a `using` list;
-- between them they need only `_,_`, `proj₁`, `proj₂`, `Σ`, `Σ-syntax`,
-- `∃-syntax` and `_×_`.  Eight of the hidden names are the ones
-- `categorical-crypto.Prelude` hides for this same module; `zip`/`zipWith`
-- join them because the `Data.List` re-export above already binds them.
-- NOTE this list is load bearing for that re-export: hiding `map` here is what
-- leaves `Data.List.map`, which 25 scope modules use, unambiguous.
open import Data.Product public
  hiding (assocʳ; assocˡ; map; map₁; map₂; map₂′; swap; _<*>_; zip; zipWith)

-- `Perm` as a re-exported module ALIAS: 36 of the 51 modules that blanket-open
-- this one spell exactly
-- `import Data.List.Relation.Binary.Permutation.Propositional as Perm`.
-- An alias adds no unqualified name, so unlike the re-export above it cannot
-- make a use site ambiguous — but every sibling alias of the name must go,
-- including indented and multi-line spellings, or Agda reports an
-- `AmbiguousName` between two aliases denoting the same module.
import Data.List.Relation.Binary.Permutation.Propositional
module Perm = Data.List.Relation.Binary.Permutation.Propositional

-- `PermProp` likewise, for 25 of the same modules.
import Data.List.Relation.Binary.Permutation.Propositional.Properties
module PermProp = Data.List.Relation.Binary.Permutation.Propositional.Properties

-- For the decidable-equality layer of the signature below.  Deliberately NOT
-- `public`, unlike the re-exports above: these four names are used only by the
-- derivation that follows, and the modules that want them import them
-- themselves (mostly with `using` lists of their own).
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)

--------------------------------------------------------------------------------
-- Structural decidable equality on `ObjTerm` over an atom set `X`, derived
-- from decidable equality on `X`.  Factored out (parameterised over `_≟X_`)
-- so it can be reused independently of the `APROPSignature` record — e.g.
-- to discharge UIP obligations when building `mor` out of `ObjTerm` proofs.

module ObjTermDec {X : Set} (_≟X_ : DecidableEquality X) where
  open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var) public

  private
    ⊗-injˡ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → A ≡ A'
    ⊗-injˡ refl = refl

    ⊗-injʳ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → B ≡ B'
    ⊗-injʳ refl = refl

    Var-inj : ∀ {x y : X} → Var x ≡ Var y → x ≡ y
    Var-inj refl = refl

  ≟-ObjTerm : DecidableEquality ObjTerm
  ≟-ObjTerm unit     unit       = yes refl
  ≟-ObjTerm unit     (_ ⊗₀ _)   = no λ ()
  ≟-ObjTerm unit     (Var _)    = no λ ()
  ≟-ObjTerm (_ ⊗₀ _) unit       = no λ ()
  ≟-ObjTerm (A ⊗₀ B) (A' ⊗₀ B') with ≟-ObjTerm A A' | ≟-ObjTerm B B'
  ... | yes p | yes q = yes (cong₂ _⊗₀_ p q)
  ... | yes _ | no ¬q = no (λ eq → ¬q (⊗-injʳ eq))
  ... | no ¬p | _     = no (λ eq → ¬p (⊗-injˡ eq))
  ≟-ObjTerm (_ ⊗₀ _) (Var _)    = no λ ()
  ≟-ObjTerm (Var _)  unit       = no λ ()
  ≟-ObjTerm (Var _)  (_ ⊗₀ _)   = no λ ()
  ≟-ObjTerm (Var x)  (Var y)    = map′ (cong Var) Var-inj (x ≟X y)

  -- UIP on `ObjTerm` (decidable equality ⇒ UIP, no `K`): collapses the
  -- reflexive endpoint equations that `--without-K` unification refuses to
  -- delete when matching index-constrained constructors twice.
  open Decidable⇒UIP ≟-ObjTerm public using () renaming (≡-irrelevant to uip-ObjTerm)

record APROPSignature : Set₁ where
  field X : Set

  open FreeMonoidalHelper Symm X using (ObjTerm)

  field mor : ObjTerm → ObjTerm → Set

  -- The hypergraph-isomorphism decision procedure `findIso` (TensorRocq §4.2,
  -- arXiv:2604.17592) needs decidable equality on `X` (atom labels) and on
  -- `mor A B` (edge labels); `_≟-ObjTerm_` below (used for comparing labelled
  -- arities when matching edges) then comes for free.
  --
  -- Decidable equality on `FlatGen` itself is avoided (its `flat` constructor
  -- is generalised in `A, B` and `flatten` is not injective in general);
  -- label comparison is handled at edge-matching time instead.
  field
    _≟X_    : DecidableEquality X
    _≟-mor_ : ∀ {A B} → DecidableEquality (mor A B)

  -- ONLY `uip-ObjTerm`: re-exporting `ObjTermDec`'s `ObjTerm` as well would
  -- bind that name twice in this record (the `FreeMonoidalHelper` application
  -- above is the other binding), and again downstream in `module APROP`, whose
  -- `FreeMonoidal` re-export is a third.  Consumers that need the object
  -- language take it from `APROP`/`FreeMonoidalHelper` directly.
  open ObjTermDec _≟X_ public using (uip-ObjTerm)

  _≟-ObjTerm_ : DecidableEquality ObjTerm
  _≟-ObjTerm_ = ObjTermDec.≟-ObjTerm _≟X_

  asFreeMonoidalData : FreeMonoidalData
  asFreeMonoidalData = record { v = Symm ; X = X ; mor = mor }

module APROP (sig : APROPSignature) where
  -- `_≟X_` is withheld from this re-export for exactly one commit: the strict
  -- cone still binds it as a module parameter, and a blanket `open APROP sig`
  -- there would make the name ambiguous (a parameter does not shadow an opened
  -- field).  The next commit deletes those parameters and this `hiding`.
  open APROPSignature sig public hiding (_≟X_)
  open FreeMonoidal asFreeMonoidalData public renaming (var to Agen)

  -- `Symm ≤ Symm` for instance search, so `σ` needs no explicit `⦃ v≤v ⦄`.
  instance
    Symm≤Symm : Symm ≤ Symm
    Symm≤Symm = v≤v

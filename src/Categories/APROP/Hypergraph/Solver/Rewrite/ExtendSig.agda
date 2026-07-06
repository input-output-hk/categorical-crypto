{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Signature extension with a single *hole* generator (first stage of the
-- `subMatch → decode` rewrite bridge).
--
-- To carve a rewrite context out of a hypergraph, we replace the matched
-- redex edges by one fresh edge — the hole `h : P → Q` — and decode the
-- result back to a term over the *extended* signature `sig⁺ = sig + h`.
-- The atom alphabet `X` is unchanged, so `ObjTerm`, `flatten`, `unflatten`
-- all coincide between `sig` and `sig⁺`; only the generator type grows.
--
-- Provides, for a base `sig-dec` and hole arity `P Q`:
--   * `Mor⁺`/`sig⁺`/`sig⁺-dec` — the extended signature (with decidable eq);
--   * `relabel` — `FlatGen → FlatGen⁺` edge-label inclusion (for the carved
--     graph's complement edges);
--   * `retract` — `HomTerm⁺ A B → Maybe (HomTerm A B)`, total on hole-free
--     terms (for extracting `pre`/`post` from the decoded context).
--
-- All of this is *unverified* plumbing for the carve; engine soundness rests
-- solely on the final `findIso` certification at the base signature.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig
  (sig-dec : APROPSignatureDec)
  (let open APROPSignatureDec sig-dec
         using (sig; _≟X_; _≟-mor_; _≟-ObjTerm_; ObjTerm; unit; _⊗₀_; Var))
  (let open APROPSignature sig)
  (P Q : ObjTerm)
  where

open import Data.List.Base
open import Data.Maybe.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Relation.Nullary.Decidable

--------------------------------------------------------------------------------
-- The extended generator type: every base generator, plus one hole `P → Q`.
-- `hole` carries its indices as explicit equality proofs (rather than as a
-- constructor indexed directly at `P Q`) so that case splits stay possible
-- under `--without-K`; the proofs are unique by UIP on `ObjTerm` (decidable
-- equality ⇒ UIP), so this changes nothing up to propositional equality.

data Mor⁺ : ObjTerm → ObjTerm → Set where
  old  : ∀ {A B} → mor A B → Mor⁺ A B
  hole : ∀ {A B} → A ≡ P → B ≡ Q → Mor⁺ A B

-- The canonical hole at its own arity.
hole! : Mor⁺ P Q
hole! = hole refl refl

sig⁺ : APROPSignature
sig⁺ = record { X = X ; mor = Mor⁺ }

private
  old-inj : ∀ {A B} {f g : mor A B} → old f ≡ old g → f ≡ g
  old-inj refl = refl

  open import Axiom.UniquenessOfIdentityProofs

  uipObj : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q
  uipObj = Decidable⇒UIP.≡-irrelevant _≟-ObjTerm_

_≟-Mor⁺_ : ∀ {A B} → DecidableEquality (Mor⁺ A B)
old f    ≟-Mor⁺ old g     = map′ (cong old) old-inj (f ≟-mor g)
old f    ≟-Mor⁺ hole _ _  = no λ ()
hole _ _ ≟-Mor⁺ old g     = no λ ()
hole p q ≟-Mor⁺ hole p' q' =
  yes (cong₂ hole (uipObj p p') (uipObj q q'))

sig⁺-dec : APROPSignatureDec
sig⁺-dec = record { sig = sig⁺ ; _≟X_ = _≟X_ ; _≟-mor_ = _≟-Mor⁺_ }

--------------------------------------------------------------------------------
-- Edge-label inclusion.  `flatten` depends only on `X`, so the two `FlatGen`s
-- are indexed by the same atom lists and `flat f ↦ flat (old f)` is direct.

open import Categories.APROP.Hypergraph.Model.FromAPROP sig

import Categories.APROP.Hypergraph.Model.FromAPROP sig⁺ as F⁺

-- `flatten` depends only on `X`, but the two module instantiations are
-- distinct neutrals on an abstract `A`; bridge them propositionally.
flatten-agree : ∀ A → F⁺.flatten A ≡ flatten A
flatten-agree unit     = refl
flatten-agree (A ⊗₀ B) = cong₂ _++_ (flatten-agree A) (flatten-agree B)
flatten-agree (Var x)  = refl

-- Rebuild the `sig⁺` record directly at the same boundaries, folding the
-- (erased) original linking proof together with `flatten-agree`.
relabel : ∀ {As Bs} → FlatGen As Bs → F⁺.FlatGen As Bs
relabel (flat-rec {A} {B} oa ob f) =
  F⁺.flat-rec (trans (flatten-agree A) oa) (trans (flatten-agree B) ob) (old f)

--------------------------------------------------------------------------------
-- Term retraction `sig⁺ → sig`: total on hole-free terms, `nothing` on any
-- term containing the hole.  `ObjTerm` is shared, so types carry over as-is.

open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐; σ)
open APROP sig⁺ using ()
  renaming ( HomTerm to HomTerm⁺ ; Agen to Agen⁺ ; id to id⁺ ; _∘_ to _∘⁺_
           ; _⊗₁_ to _⊗₁⁺_ ; λ⇒ to λ⇒⁺ ; λ⇐ to λ⇐⁺ ; ρ⇒ to ρ⇒⁺ ; ρ⇐ to ρ⇐⁺
           ; α⇒ to α⇒⁺ ; α⇐ to α⇐⁺ ; σ to σ⁺ )

retract : ∀ {A B} → HomTerm⁺ A B → Maybe (HomTerm A B)
retract (Agen⁺ (old f))    = just (Agen f)
retract (Agen⁺ (hole _ _)) = nothing
retract id⁺             = just id
retract (g ∘⁺ f)        with retract g | retract f
... | just g' | just f' = just (g' ∘ f')
... | _       | _       = nothing
retract (f ⊗₁⁺ g)       with retract f | retract g
... | just f' | just g' = just (f' ⊗₁ g')
... | _       | _       = nothing
retract λ⇒⁺             = just λ⇒
retract λ⇐⁺             = just λ⇐
retract ρ⇒⁺             = just ρ⇒
retract ρ⇐⁺             = just ρ⇐
retract α⇒⁺             = just α⇒
retract α⇐⁺             = just α⇐
retract σ⁺              = just σ

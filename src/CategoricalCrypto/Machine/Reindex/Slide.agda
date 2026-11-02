{-# OPTIONS --safe #-}

-- ============================================================================
-- Sliding a channel relabelling past a trace, and what it buys.
--
-- `CategoricalCrypto.Machine.Reindex` reduced `_∘_` to `Reindex`/`Pair`/`Trc`,
-- in `∘-Reindex`.  One fact about that algebra is missing there:
--
--   `Trc-slide` — a relabelling that FIXES THE TRACED CHANNEL commutes with
--     `Trc`.  A trace chain only ever touches the traced ports, so relabelling
--     the external ones cannot change which chains exist.
--
-- From it: a forwarder is a reindexed identity (`Xfwd-dom`/`Xfwd-cod`, both
-- in `Reindex.Post`), a relabelling slides out of either argument of `_∘_`
-- (`∘-collapse-dom`/`∘-collapse-cod`), and hence composing with a forwarder
-- is just a relabelling.  `Trc-slide`'s only users are `Reindex.Collapse` and
-- `Reindex.Post`, and through them the three naturality proofs of
-- `Machine.Monoidal`.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex

open import categorical-crypto.Prelude hiding (id; _∘_)
import Data.Sum.Base as ⊎
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Message
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.Slide where

open Channel

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ

  -- The four traced-channel ports of a machine `Machine (X ⊗₀ Z) (Y ⊗₀ Z)`.
  -- `X ⊗ᵀ Y` is `X ⊗₀ Y ᵀ`, so the codomain's out-messages are in-messages of
  -- the pair and its in-messages are out-messages of the pair; that is why the
  -- modes are crossed in `cZₒ` and `cZᵢ`.
  dZᵢ : ∀ {X Y Z} → inType Z → inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  dZᵢ z = inj₁ (inj₂ z)

  cZₒ : ∀ {X Y Z} → outType Z → inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  cZₒ z = inj₂ (inj₂ z)

  dZₒ : ∀ {X Y Z} → outType Z → outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  dZₒ z = inj₁ (inj₂ z)

  cZᵢ : ∀ {X Y Z} → inType Z → outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
  cZᵢ z = inj₂ (inj₂ z)

  Trc-slide : ∀ {X Y Z X' Y' : Channel} (W : Machine (X ⊗₀ Z) (Y ⊗₀ Z))
              (p : inType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                 → inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
              (q : outType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                 → outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
            → (∀ z → p (dZᵢ {X'} {Y'} {Z} z) ≡ dZᵢ {X} {Y} {Z} z)
            → (∀ z → p (cZₒ {X'} {Y'} {Z} z) ≡ cZₒ {X} {Y} {Z} z)
            → (∀ z → q (dZₒ {X'} {Y'} {Z} z) ≡ dZₒ {X} {Y} {Z} z)
            → (∀ z → q (cZᵢ {X'} {Y'} {Z} z) ≡ cZᵢ {X} {Y} {Z} z)
            → Trc (Reindex W p q) ≅ᴹ Reindex (Trc W) p q
  Trc-slide {X} {Y} {Z} {X'} {Y'} W p q pi po qo qi =
    MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) t
          (λ {_} {i} {o} x → f x i o refl refl)
    where
    t : ∀ {s I MO s'} → TraceRel (Reindex W p q) s I MO s'
      → TraceRel W s (p I) (mapᴹ q MO) s'
    t Trace[ x ] = Trace[ x ]
    t (_Trace∷ₒ_ {outC = zc} x rest) =
      subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qo zc) x
      Trace∷ₒ subst (λ y → TraceRel W _ y _ _) (po zc) (t rest)
    t (_Trace∷ᵢ_ {inC = zc} x rest) =
      subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qi zc) x
      Trace∷ᵢ subst (λ y → TraceRel W _ y _ _) (pi zc) (t rest)
    -- The indices are generalised and re-tied by equations, so that the
    -- recursion is on the `TraceRel` itself and the termination checker sees it.
    f : ∀ {s I₀ MO₀ s'} → TraceRel W s I₀ MO₀ s'
      → ∀ I MO → I₀ ≡ p I → MO₀ ≡ mapᴹ q MO
      → TraceRel (Reindex W p q) s I MO s'
    f Trace[ x ] I MO ieq oeq =
      Trace[ subst₂ (λ a b → Machine.stepRel W _ a b _) ieq oeq x ]
    f (_Trace∷ₒ_ {outC = zc} x rest) I MO ieq oeq =
      subst₂ (λ a b → Machine.stepRel W _ a (just b) _) ieq (sym (qo zc)) x
      Trace∷ₒ f rest (cZₒ {X'} {Y'} {Z} zc) MO (sym (po zc)) oeq
    f (_Trace∷ᵢ_ {inC = zc} x rest) I MO ieq oeq =
      subst₂ (λ a b → Machine.stepRel W _ a (just b) _) ieq (sym (qi zc)) x
      Trace∷ᵢ f rest (dZᵢ {X'} {Y'} {Z} zc) MO (sym (pi zc)) oeq

  -- Relabel the codomain of `Machine B C`, leaving the domain alone.
  -- `B ⊗ᵀ C = B ⊗₀ C ᵀ`, so an in-map on the pair is built from an out-map on
  -- `C`; that is why `cdᵢ` takes a map on out-messages.
  cdᵢ : ∀ {B C C'} → (outType C' → outType C)
      → inType (B ⊗ᵀ C') → inType (B ⊗ᵀ C)
  cdᵢ = ⊎.map₂

  cdₒ : ∀ {B C C'} → (inType C' → inType C)
      → outType (B ⊗ᵀ C') → outType (B ⊗ᵀ C)
  cdₒ = ⊎.map₂

  dmᵢ : ∀ {A A' B} → (inType A' → inType A)
      → inType (A' ⊗ᵀ B) → inType (A ⊗ᵀ B)
  dmᵢ = ⊎.map₁

  dmₒ : ∀ {A A' B} → (outType A' → outType A)
      → outType (A' ⊗ᵀ B) → outType (A ⊗ᵀ B)
  dmₒ = ⊎.map₁

  -- The same, at the traced machine's channel.  These fix the traced ports,
  -- which is what lets `Trc-slide` apply.
  wcᵢ : ∀ {A B C C'} → (outType C' → outType C)
      → inType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)) → inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wcᵢ uC = ⊎.map₂ (⊎.map₁ uC)

  wcₒ : ∀ {A B C C'} → (inType C' → inType C)
      → outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)) → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wcₒ vC = ⊎.map₂ (⊎.map₁ vC)

  wdᵢ : ∀ {A A' B C} → (inType A' → inType A)
      → inType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wdᵢ uA = ⊎.map₁ (⊎.map₁ uA)

  wdₒ : ∀ {A A' B C} → (outType A' → outType A)
      → outType ((A' ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  wdₒ vA = ⊎.map₁ (⊎.map₁ vA)

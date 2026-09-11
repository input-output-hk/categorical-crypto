{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Core.Bridge` at the machine family: the ingested agreement read in the
-- INHERITED `_≈ᵁ_`, so `ucSetup^ω`'s metatheory — `UC-compose` in particular —
-- applies to a concrete family.
--
-- `UC.Family.Monoidal` assembles `ucSetup^ω` and notes that its own statements
-- land in `Em UCBase^ω`'s ancilla-quantified `_≈ℰ_` rather than in `_≈ᵁ_`.
-- This module is the step between: `UC.Core.Bridge` proves the implication
-- generically, and here it is applied at `Famᴹ`.
--
-- The two gradings the step crosses are `UC.Family.Grading^ω` and the monoidal
-- `gradingᵗ Famᴹ`.  They differ only in the polynomial a relayed hom carries —
-- `p ⊔ 1` against `(1 ⊔ 1) * (p ⊔ 1)` — and `_≈^ω_` and the observation both
-- read a `Fam`-hom through `proj₁`, so the two agreements are the same type and
-- `≈ℰ^ω⇒≈ℰᶜ` is the identity.
--
-- Measured warm cost: 40 s for 33 lines.  It is the inherited tower read at
-- `Famᴹ` — `UC-compose`'s `ext`/`sub` chain over a hom that carries a
-- polynomial — and not any statement written here.

import CategoricalCrypto.UC.Model.Family as F

module CategoricalCrypto.UC.Model.Family.Uniform where

open import CategoricalCrypto.UC.Core.Bridge F.Famᴹ F.Observation^ω public

-- `Grading^ω`'s agreement is the monoidal grading's, on the nose.
≈ℰ^ω⇒≈ℰᶜ : {A B : Channel} {f g : A ⇒ B} → F._≈ℰ_ f g → f ≈ℰᶜ g
≈ℰ^ω⇒≈ℰᶜ h = h

-- …so a family agreement enters the inherited order, and two of them compose.
-- `UC-compose` is the metatheorem the core layer could only state
-- (`UC.Emulation`'s header); at the family it is inherited, and this is where an
-- ingested bound (`UC.Model.Family.Ingest`) meets it.
--
-- The homs are EXPLICIT: an agreement reads them under an application, so no
-- value of one determines them by unification, and left to inference the
-- polynomial each carries is elaborated as a meta — measured, 2m25 s of `Poly`
-- arithmetic against 8 s.
≈ℰ^ω⇒≤UC : {A B X : Channel} (f g : A ⇒ T₀ X B) → F._≈ℰ_ f g → f ≤UC g
≈ℰ^ω⇒≤UC f g h = ≈ℰᶜ⇒≤UC {f = f} {g} (≈ℰ^ω⇒≈ℰᶜ {f = f} {g} h)

uc-compose-agree : {A B C X P : Channel} (f g : A ⇒ T₀ X B) (h k : B ⇒ T₀ P C)
                 → F._≈ℰ_ f g → F._≈ℰ_ h k → (h ∙ f) ≤UC (k ∙ g)
uc-compose-agree f g h k e d =
  UC-compose {f = f} {g} {h} {k} (≈ℰ^ω⇒≤UC f g e) (≈ℰ^ω⇒≤UC h k d)

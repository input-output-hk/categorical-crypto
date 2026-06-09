{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Solving symmetric-monoidal equations in an *arbitrary* target SMC.
--
-- `solveM` (Categories.MonoidalCoherence) discharges a *monoidal* coherence
-- equation in any monoidal category by proving it in the free monoidal
-- category and transporting it along the interpreting functor.  This module
-- is the symmetric / string-diagram analogue.
--
-- Given a signature `(X , mor)` of atoms and generators, the free symmetric
-- monoidal category `FreeMonoidal` is the syntax.  An equation `f ≈ g`
-- between two such terms is witnessed by a hypergraph isomorphism
-- `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` (typically produced by `findIso`), which
-- `soundness-full-wired` turns into a genuine `f ≈Term g`.  We then transport
-- that equation into the target SMC `C` along the free functor `freeFunctor`
-- that interprets atoms via `⟦_⟧ᵖ₀` and generators via `⟦_⟧ᵖ₁`.
--
-- The interface mirrors `solveM`: `solveH` takes the two terms `f g`
-- explicitly (so the goal need not pin them down through the non-injective
-- `⟦_⟧₁`), plus the hypergraph isomorphism.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Interpret (sig-dec : APROPSignatureDec) where

open import Categories.APROP using (module APROP)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor)

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso sig-dec using (findIso)
open import Categories.APROP.Hypergraph.Solver.Carve sig-dec using (focusAt; Foc)
open import Categories.APROP.Hypergraph.SoundnessFullWired sig-dec
  using (soundness-full-wired)

open import Level using (Level)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (T)
open import Data.Product.Base using (_,_; proj₁; proj₂)

private
  -- Extract the value of a `Maybe` from a proof (`T (is-just _)`) that it is
  -- `just`.  Unlike `from-just`, the proof is a separate argument, so this
  -- can be applied to an *abstract* `Maybe` and still type-check; the proof is
  -- the unit value `tt` (filled implicitly) whenever the `Maybe` is concretely
  -- `just`, and uninhabitable when it is `nothing`.
  fromWitness! : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
  fromWitness! (just x) _ = x

  -- The frame `post ∘ (id {k} ⊗₁ mid) ∘ pre` for the focus `focusAt s lᵗ`
  -- located in `s` (when it succeeds).  `mid := lᵗ` gives the L-frame whose
  -- iso to `s` certifies the carve; `mid := rᵗ` gives the rewritten target.
  focFrame : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) (mid : HomTerm P Q)
           → T (is-just (focusAt s lᵗ)) → HomTerm A B
  focFrame s lᵗ mid found =
    let (k , pre , post) = fromWitness! (focusAt s lᵗ) found
    in post ∘ (id {k} ⊗₁ mid) ∘ pre

--------------------------------------------------------------------------------
-- The object interpretation `⟦_⟧₀ : ObjTerm → C.Obj`, which depends only on
-- the atom interpretation `⟦_⟧ᵖ₀`.  Exposed separately from `Solver` so that
-- callers can *name the type* of a generator-interpretation table —
-- `(i : Fin n) → ⟦ dom i ⟧₀ C.⇒ ⟦ cod i ⟧₀` — before committing the table
-- itself (which `Solver` needs as its `⟦_⟧ᵖ₁` argument).

module ObjInterp {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ : ⟦ Symm ⟧ᵥ {o} {ℓ} {e}
       ⟦v⟧ = record
         { C           = C.U
         ; Monoidal-C  = C.monoidal
         ; Symmetric-C = λ ⦃ _ ⦄ → C.symmetric
         })
  (⟦_⟧ᵖ₀ : X → C.Obj)
  where
  open FreeFunctorHelper asFreeMonoidalData ⟦v⟧ using (module Go)
  open Go ⟦_⟧ᵖ₀ public using (⟦_⟧₀)

--------------------------------------------------------------------------------
-- The solver, parameterised by a target SMC `C` and an interpretation of the
-- signature: `⟦_⟧ᵖ₀` on atoms, `⟦_⟧ᵖ₁` on generators.  The `let`-bindings in
-- the telescope assemble the `⟦ Symm ⟧ᵥ` package and bring the object
-- interpretation `⟦_⟧₀` into scope so the type of `⟦_⟧ᵖ₁` can mention it.

module Solver {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ : ⟦ Symm ⟧ᵥ {o} {ℓ} {e}
       ⟦v⟧ = record
         { C           = C.U
         ; Monoidal-C  = C.monoidal
         ; Symmetric-C = λ ⦃ _ ⦄ → C.symmetric
         })
  (⟦_⟧ᵖ₀ : X → C.Obj)
  (let open FreeFunctorHelper asFreeMonoidalData ⟦v⟧ using (module Go))
  (let open Go ⟦_⟧ᵖ₀ using (⟦_⟧₀))
  (⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀)
  where

  ffd : FreeFunctorData asFreeMonoidalData {o} {ℓ} {e}
  ffd = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦_⟧ᵖ₁ }

  open FreeFunctor ffd public using (⟦_⟧₁; freeFunctor)

  -- The target category, with its monoidal/symmetric shorthands (`_∘_`, `id`,
  -- `_⊗₁_`, `λ⇒`, `α⇒`, `σ`, …).  `⟦_⟧₁` is defined compositionally into this
  -- module, so `⟦ t ⟧₁` is *definitionally* the corresponding `Tgt`-expression
  -- — letting callers state goals as equations in `C` directly, with no
  -- mention of `⟦_⟧₁`.
  module Tgt = ⟦_⟧ᵥ.Cat ⟦v⟧

  -- Discharge a free-SMC equation `f ≈ g` — given as a hypergraph iso
  -- `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` between the translations — into the target category `C`.
  solveH
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH f g iso =
    Functor.F-resp-≈ freeFunctor (soundness-full-wired {f = f} {g = g} iso)

  -- Same, but the witnessing iso is located internally by `findIso`, so the
  -- two free-SMC terms `f g` need only be written once.  The implicit
  -- `T (is-just …)` argument is discharged automatically (it reduces to the
  -- unit type `⊤`) exactly when `findIso ⟪ f ⟫ ⟪ g ⟫` succeeds at type-check
  -- time; if the search fails it reduces to `⊥` and the call is rejected.
  solveH!
    : ∀ {A B} (f g : HomTerm A B)
    → {_ : T (is-just (findIso ⟪ f ⟫ ⟪ g ⟫))}
    → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH! f g {pf} = solveH f g (fromWitness! (findIso ⟪ f ⟫ ⟪ g ⟫) pf)

  --------------------------------------------------------------------------------
  -- Diagrammatic *rewriting* in `C`, in the style of `solveH!` but with a
  -- rewrite rule as the extra input.  This is the string-diagram analogue of
  -- TensorRocq's `srw`/`zxrw` tactics, and the soundness analogue of its
  -- double-pushout rewrite `H ≅ C₁ ; (I ⊗ L) ; C₂`.
  --
  -- A *rule* is an equation `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁` in `C` between the
  -- interpretations of two free-SMC terms `lᵗ rᵗ : HomTerm P Q` (definitionally
  -- whatever raw `C`-equation the caller already has, e.g. a generator law).
  -- A *position* is a free-SMC context: an input-side term `pre : A → k ⊗ P`
  -- and an output-side term `post : k ⊗ Q → B`, so that the rule fires inside
  -- the frame `post ∘ (id {k} ⊗₁ –) ∘ pre`.  The `id {k} ⊗₁ –` padding makes
  -- this frame general for any *connected single-subdiagram* occurrence: σ/α
  -- can reshape the occurrence into this shape, and the two `findIso` searches
  -- below absorb exactly that reshaping.
  --
  -- The caller writes *both* endpoints `s t : HomTerm A B` in any SMC-equivalent
  -- form they like; the two implicit `findIso` witnesses reconcile each side to
  -- the corresponding frame.  Soundness (`soundness-full-wired`, via `solveH`)
  -- discharges the two coherence reconciliations; the rule is transported across
  -- by `C`'s `∘`/`⊗₁` congruence — no completeness and no hypergraph→term
  -- extraction is needed, so this rests only on the proven, postulate-free half
  -- of the triangle.
  rewriteH!
    : ∀ {A B P Q k}
    → (s t : HomTerm A B)
    → (pre : HomTerm A (k ⊗₀ P)) (post : HomTerm (k ⊗₀ Q) B)
    → (lᵗ rᵗ : HomTerm P Q)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {_ : T (is-just (findIso ⟪ s ⟫ ⟪ post ∘ (id {k} ⊗₁ lᵗ) ∘ pre ⟫))}
    → {_ : T (is-just (findIso ⟪ t ⟫ ⟪ post ∘ (id {k} ⊗₁ rᵗ) ∘ pre ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  rewriteH! s t pre post lᵗ rᵗ rule {p₁} {p₂} =
    C.Equiv.trans (solveH! s (post ∘ (id ⊗₁ lᵗ) ∘ pre) {p₁})
      (C.Equiv.trans
        (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule))))
        (C.Equiv.sym (solveH! t (post ∘ (id ⊗₁ rᵗ) ∘ pre) {p₂})))

  --------------------------------------------------------------------------------
  -- Fully automatic rewriting: like `rewriteH!`, but the position (`pre`/`post`)
  -- is *found* by `focusAt` (term-level focusing) rather than supplied.  The
  -- caller gives only the term `s`, the rule `lᵗ ≈ rᵗ`, and the rule proof; the
  -- rewritten target is computed as `focFrame s lᵗ rᵗ found`.
  --
  -- Two typecheck-time obligations, both discharged by reduction at the call
  -- site (where `s`, `lᵗ` are concrete): `found` — `focusAt` located the redex;
  -- `cert` — the located L-frame is hypergraph-iso to `s`.  The target is *by
  -- construction* the R-frame, so no second iso search is needed: we transport
  -- the rule across the located frame by `C`'s `∘`/`⊗₁` congruence directly.
  rewriteAuto!
    : ∀ {A B P Q}
    → (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (focusAt s lᵗ))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ focFrame s lᵗ lᵗ found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ focFrame s lᵗ rᵗ found ⟧₁
  rewriteAuto! s lᵗ rᵗ rule {found} {cert} =
    C.Equiv.trans
      (solveH s (focFrame s lᵗ lᵗ found)
              (fromWitness! (findIso ⟪ s ⟫ ⟪ focFrame s lᵗ lᵗ found ⟫) cert))
      (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule))))

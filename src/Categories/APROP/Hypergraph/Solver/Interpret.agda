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
open import Categories.APROP.Hypergraph.Solver.Carve sig-dec using (focusAtₙ; Foc)
open import Categories.APROP.Hypergraph.Solver.Deep sig-dec using (deepFocₙ)
open import Categories.APROP.Hypergraph.SoundnessFullWired sig-dec
  using (soundness-full-wired)

open import Level using (Level; _⊔_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (T)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)

private
  -- Extract the value of a `Maybe` from a proof (`T (is-just _)`) that it is
  -- `just`.  Unlike `from-just`, the proof is a separate argument, so this
  -- can be applied to an *abstract* `Maybe` and still type-check; the proof is
  -- the unit value `tt` (filled implicitly) whenever the `Maybe` is concretely
  -- `just`, and uninhabitable when it is `nothing`.
  fromWitness! : ∀ {a} {A : Set a} (m : Maybe A) → T (is-just m) → A
  fromWitness! (just x) _ = x

-- The frame `post ∘ (id {k} ⊗₁ mid) ∘ pre` for the `n`-th focus position of
-- `lᵗ` in `s` (when it exists).  `mid := lᵗ` gives the L-frame whose iso to
-- `s` certifies the carve; `mid := rᵗ` gives the rewritten target.  Public so
-- callers can *name* the term a rewrite lands on (e.g. to continue a
-- `HomReasoning` chain from it); the witness argument is `tt` at any call
-- site where the search concretely succeeds, so `_` fills it.
focFrame : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) (mid : HomTerm P Q)
         → (n : ℕ) → T (is-just (focusAtₙ s lᵗ n)) → HomTerm A B
focFrame s lᵗ mid n found =
  let (k , pre , post) = fromWitness! (focusAtₙ s lᵗ n) found
  in post ∘ (id {k} ⊗₁ mid) ∘ pre

-- As `focFrame`, but for the hypergraph-level (`deepFocₙ`) position search.
deepFrame : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) (mid : HomTerm P Q)
          → (n : ℕ) → T (is-just (deepFocₙ s lᵗ n)) → HomTerm A B
deepFrame s lᵗ mid n found =
  let (k , pre , post) = fromWitness! (deepFocₙ s lᵗ n) found
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
  -- site (where `s`, `lᵗ`, `n` are concrete): `found` — the `n`-th focus
  -- position of `lᵗ` in `s` exists; `cert` — that L-frame is hypergraph-iso to
  -- `s`.  The target is *by construction* the R-frame, so no second iso search
  -- is needed: we transport the rule across the located frame by `C`'s
  -- `∘`/`⊗₁` congruence directly.  `n` selects which occurrence to rewrite.
  rewriteAutoₙ!
    : ∀ {A B P Q}
    → (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (focusAtₙ s lᵗ n))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ focFrame s lᵗ lᵗ n found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ focFrame s lᵗ rᵗ n found ⟧₁
  rewriteAutoₙ! s lᵗ rᵗ n rule {found} {cert} =
    C.Equiv.trans
      (solveH s (focFrame s lᵗ lᵗ n found)
              (fromWitness! (findIso ⟪ s ⟫ ⟪ focFrame s lᵗ lᵗ n found ⟫) cert))
      (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule))))

  -- The first occurrence (`n = 0`).
  rewriteAuto!
    : ∀ {A B P Q}
    → (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (focusAtₙ s lᵗ zero))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ focFrame s lᵗ lᵗ zero found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ focFrame s lᵗ rᵗ zero found ⟧₁
  rewriteAuto! s lᵗ rᵗ rule {found} {cert} =
    rewriteAutoₙ! s lᵗ rᵗ zero rule {found} {cert}

  --------------------------------------------------------------------------------
  -- As `rewriteAutoₙ!`, but the position is found on the *hypergraph* (via
  -- `deepFocₙ`: sub-match enumeration → hole-carve with retry → decode), so
  -- the redex need not be a subterm of `s` as written — it only has to be a
  -- connected sub-diagram of `⟪ s ⟫`, e.g. a sequential rule firing across an
  -- interchange.  `n` indexes the *carvable* (convex) occurrences in match
  -- order; non-convex matches are skipped, not counted.
  rewriteDeepₙ!
    : ∀ {A B P Q}
    → (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (deepFocₙ s lᵗ n))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ n found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ deepFrame s lᵗ rᵗ n found ⟧₁
  rewriteDeepₙ! s lᵗ rᵗ n rule {found} {cert} =
    C.Equiv.trans
      (solveH s (deepFrame s lᵗ lᵗ n found)
              (fromWitness! (findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ n found ⟫) cert))
      (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule))))

  -- The first carvable occurrence (`n = 0`).
  rewriteDeep!
    : ∀ {A B P Q}
    → (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (deepFocₙ s lᵗ zero))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ zero found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ deepFrame s lᵗ rᵗ zero found ⟧₁
  rewriteDeep! s lᵗ rᵗ rule {found} {cert} =
    rewriteDeepₙ! s lᵗ rᵗ zero rule {found} {cert}

  --------------------------------------------------------------------------------
  -- As `rewriteDeepₙ!`, but landing on a caller-stated CLEAN term `t` (the
  -- second `findIso` reconciles the rewritten frame with `t` up to SMC
  -- structure).  This is the workhorse for multi-step derivations: the
  -- carved frame never appears in the exposed type — only `⟦ s ⟧₁ ≈ ⟦ t ⟧₁`
  -- — so steps chain by transitivity without the type-checker ever
  -- conversion-checking two large frame terms against each other (which is
  -- prohibitively slow; see the test suite's chain tests).
  rewriteDeepTo!
    : ∀ {A B P Q}
    → (s t : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (deepFocₙ s lᵗ n))}
    → {_     : T (is-just (findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ n found ⟫))}
    → {_     : T (is-just (findIso ⟪ t ⟫ ⟪ deepFrame s lᵗ rᵗ n found ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  rewriteDeepTo! s t lᵗ rᵗ n rule {found} {c₁} {c₂} =
    C.Equiv.trans
      (rewriteDeepₙ! s lᵗ rᵗ n rule {found} {c₁})
      (C.Equiv.sym
        (solveH t (deepFrame s lᵗ rᵗ n found)
                (fromWitness! (findIso ⟪ t ⟫ ⟪ deepFrame s lᵗ rᵗ n found ⟫) c₂)))

  --------------------------------------------------------------------------------
  -- Rewrite DRIVERS: normalisation with respect to a list of rules.
  --
  -- A `Rule` packages an oriented rewrite `lhs ↝ rhs` with its soundness
  -- proof in `C`.  `drive` repeatedly fires the first applicable rule at its
  -- first carvable (deep) position until no rule applies or the fuel runs
  -- out — and, unlike the single-step tools, it carries its own proof: each
  -- step's `findIso` certificate is found at *value* level during the
  -- search, so a step that fails to certify simply doesn't fire (the search
  -- moves on to the next rule), and the result needs no typecheck-time
  -- witness plumbing.
  --
  -- A rule fires at every occurrence eventually (re-searching from scratch
  -- each round), so a singleton list with sufficient fuel is "rewrite
  -- everywhere".  Rule LHSs must be deep-matchable (generator-ful, no bare
  -- identity wires); RHSs are unrestricted.

  record Rule : Set (o ⊔ ℓ ⊔ e) where
    constructor mkRule
    field
      {P Q} : ObjTerm
      lhs rhs : HomTerm P Q
      sound   : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁

  -- One firing: the first rule with a carvable, certifiable position.
  driveStep : List Rule → ∀ {A B} (s : HomTerm A B)
            → Maybe (Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁))
  driveStep []       s = nothing
  driveStep (r ∷ rs) s with deepFocₙ s (Rule.lhs r) zero
  ... | nothing = driveStep rs s
  ... | just (k , pre , post)
        with findIso ⟪ s ⟫ ⟪ post ∘ (id {k} ⊗₁ Rule.lhs r) ∘ pre ⟫
  ...   | nothing  = driveStep rs s
  ...   | just iso = just
          ( post ∘ (id {k} ⊗₁ Rule.rhs r) ∘ pre
          , C.Equiv.trans
              (solveH s (post ∘ (id {k} ⊗₁ Rule.lhs r) ∘ pre) iso)
              (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ
                 (C.⊗.F-resp-≈ (C.Equiv.refl , Rule.sound r)))) )

  -- Iterate to (fuel-bounded) exhaustion, accumulating the proof.
  drive : List Rule → ℕ → ∀ {A B} (s : HomTerm A B)
        → Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁)
  drive rs zero       s = s , C.Equiv.refl
  drive rs (suc fuel) s with driveStep rs s
  ... | nothing       = s , C.Equiv.refl
  ... | just (t , pf) =
        proj₁ rec , C.Equiv.trans pf (proj₂ rec)
    where rec = drive rs fuel t

  -- Normalise and land wherever the driver stops (the `≈ _` form; prefer
  -- `normalizeTo!` whenever the step participates in a larger chain).
  normalize!
    : (rules : List Rule) (fuel : ℕ) → ∀ {A B} (s : HomTerm A B)
    → ⟦ s ⟧₁ C.≈ ⟦ proj₁ (drive rules fuel s) ⟧₁
  normalize! rules fuel s = proj₂ (drive rules fuel s)

  -- Normalise and land on a caller-stated CLEAN term (reconciled with the
  -- driver's stopping point by one `findIso`); the chain-safe form.
  normalizeTo!
    : ∀ {A B} (s t : HomTerm A B) (rules : List Rule) (fuel : ℕ)
    → {_ : T (is-just (findIso ⟪ proj₁ (drive rules fuel s) ⟫ ⟪ t ⟫))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  normalizeTo! s t rules fuel {c} =
    C.Equiv.trans (proj₂ D)
      (solveH (proj₁ D) t (fromWitness! (findIso ⟪ proj₁ D ⟫ ⟪ t ⟫) c))
    where D = drive rules fuel s

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- LEG 3 of proof-carrying Route A (the `deepFrame` iso plan,
-- docs/findiso-witness-plan.md): the *recomposition* leg
--
--     ⟪ deepFrame s lᵗ lᵗ n found ⟫ ≅ᴴ ⟪ ctx ⟫[h ↦ ⟪lᵗ⟫]
--
-- where `ctx = decode-attempt H'` and
-- `deepFrame = post ∘ ((id{k} ⊗₁ lᵗ) ∘ pre)`, with `(k,pre,post)` produced
-- by `focusAtₙ ctx (Agen hole)` followed by `retract`.
--
-- This module assembles the leg from five sub-proofs:
--   (1) ⟪frame⟫ definitional expansion        — free from Translation.agda
--   (2) focusAtₙ term-soundness               — `Carve.focusAll` is sound
--   (3) retract soundness                     — `ExtendSig.retract` is sound
--   (4) hole-subst commutes with ⟪_⟫          — single-occurrence subst
--   (5) pad-layer soundness                   — repadR/repadL σ/α coherence
--
-- See LEG3-NOTES.md for the per-sub-proof status / honest LOC / classified
-- temporary-postulate ledger.
--------------------------------------------------------------------------------

open import Categories.APROP using (APROPSignature; module APROP)

module Leg3Recomp (sig : APROPSignature) where

open APROP sig

open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Iso
  using (_≅ᴴ_; refl-≅ᴴ; sym-≅ᴴ; trans-≅ᴴ)
open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig-dec
  using (Foc; leaf-try; go-all; focusAll; focusAtₙ; lookupMaybe)
open import Categories.APROP.Hypergraph.Solver.Match.FindIso sig-dec using (findIso)
import Categories.APROP.Hypergraph.Soundness sig-dec as SFW
import Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig

--------------------------------------------------------------------------------
-- The free symmetric monoidal category on the signature; `≈Term` reasoning.

open import Categories.Category using (Category)
private module FM = Category FreeMonoidal
open FM.HomReasoning

--==============================================================================
-- SUB-PROOF (1): ⟪frame⟫ definitional expansion.
--
-- The translation `⟪_⟫` is *definitionally* a homomorphism for `∘`/`⊗₁`
-- (Translation.agda lines 43/45):  `⟪ g ∘ f ⟫ = hComposeP ⟪f⟫ ⟪g⟫ _` and
-- `⟪ f ⊗₁ g ⟫ = hTensor ⟪f⟫ ⟪g⟫`.  So the LHS of the leg expands for free.
-- We DO NOT need a separate lemma — but we record the shape and prove the
-- trivial reflexive restatement, which downstream code can use to avoid
-- re-deriving the bracketing by hand.

private
  -- The frame term as built by `deepFrame`/`focFrame`.
  frame : ∀ {A B P Q} (k : ObjTerm)
        → HomTerm A (k ⊗₀ P) → HomTerm (k ⊗₀ Q) B
        → HomTerm P Q → HomTerm A B
  frame k pre post mid = post ∘ ((id {k} ⊗₁ mid) ∘ pre)

-- ⟪frame⟫ is, by the definitional homomorphism, the pruned-composite of the
-- three pieces' translations.  Stated as a reflexive `≅ᴴ` so it composes with
-- `trans-≅ᴴ`.  (The `≡`-level fact is `refl`; we wrap it in `≅ᴴ` for the
-- assembly.)
frame-expand
  : ∀ {A B P Q} (k : ObjTerm)
    (pre : HomTerm A (k ⊗₀ P)) (post : HomTerm (k ⊗₀ Q) B)
    (mid : HomTerm P Q)
  → ⟪ frame k pre post mid ⟫ ≅ᴴ ⟪ post ∘ ((id {k} ⊗₁ mid) ∘ pre) ⟫
frame-expand k pre post mid = refl-≅ᴴ ⟪ frame k pre post mid ⟫

--==============================================================================
-- The reverse translation soundness, repackaged.
--
-- `SFW.soundness : ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g`.  We only ever feed it a
-- `findIso` success, so the leaf case of focusing (which is gated on
-- `findIso ⟪s⟫ ⟪lᵗ⟫`) yields `s ≈Term lᵗ`.

private
  -- When `findIso ⟪s⟫ ⟪lᵗ⟫` succeeds it produces a genuine `≅ᴴ` witness, which
  -- `soundness` turns into `s ≈Term lᵗ`.
  fromFindIso
    : ∀ {A B} (s lᵗ : HomTerm A B)
    → (iso : ⟪ s ⟫ ≅ᴴ ⟪ lᵗ ⟫)
    → s ≈Term lᵗ
  fromFindIso s lᵗ iso = SFW.soundness iso

--==============================================================================
-- SUB-PROOF (2): focusAtₙ term-soundness.
--
-- `focusAll s lᵗ` enumerates focus positions; for each `(k , pre , post)` in
-- the list, the intended invariant is
--
--     s ≈Term post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre)        [ = frame k pre post lᵗ ].
--
-- This is the genuinely-new term-level lemma the plan calls for.  It is
-- structural EXCEPT at the leaf, where `leaf-try` fires only behind a
-- `findIso ⟪s⟫ ⟪lᵗ⟫` test; we discharge that case with `fromFindIso`.
--
-- We phrase the statement as membership in `focusAll` so the recursion and
-- the `n`-indexed `focusAtₙ`/`deepFrame` both follow.

private variable A B P Q : ObjTerm

-- `Pred f` : the frame-soundness predicate for one focus result.
Pred : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Foc A B P Q → Set
Pred s lᵗ (k , pre , post) = s ≈Term (post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre))

-- "all results in this list are sound".
data All-Pred {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q)
     : List (Foc A B P Q) → Set where
  []  : All-Pred s lᵗ []
  _∷_ : ∀ {x xs} → Pred s lᵗ x → All-Pred s lᵗ xs → All-Pred s lᵗ (x ∷ xs)

-- `All-Pred` distributes over `++`.
private
  app-Pred : ∀ {A B P Q} {s : HomTerm A B} {lᵗ : HomTerm P Q}
             {xs ys : List (Foc A B P Q)}
           → All-Pred s lᵗ xs → All-Pred s lᵗ ys → All-Pred s lᵗ (xs ++ ys)
  app-Pred []        ays = ays
  app-Pred (px ∷ pxs) ays = px ∷ app-Pred pxs ays

  -- `All-Pred` transports along a `map` whose action on each element is
  -- soundness-preserving: if for every focus `r` in `xs`, `Pred s' lᵗ r`
  -- implies `Pred s lᵗ (h r)`, then `All-Pred s' lᵗ xs ⇒ All-Pred s lᵗ (map h xs)`.
  map-Pred
    : ∀ {A B P Q A' B'} {s : HomTerm A B} {s' : HomTerm A' B'} {lᵗ : HomTerm P Q}
      (h : Foc A' B' P Q → Foc A B P Q)
      {xs : List (Foc A' B' P Q)}
    → (∀ r → Pred s' lᵗ r → Pred s lᵗ (h r))
    → All-Pred s' lᵗ xs → All-Pred s lᵗ (map h xs)
  map-Pred h step []          = []
  map-Pred h step (px ∷ pxs)  = step _ px ∷ map-Pred h step pxs

--------------------------------------------------------------------------------
-- SMC coherence helper: the leaf frame `λ⇒ ∘ ((id ⊗ lᵗ) ∘ λ⇐)` collapses to
-- `lᵗ` up to `≈Term` (it is just `lᵗ` conjugated by the left unitor iso).

private
  leaf-frame-id
    : ∀ {P Q} (lᵗ : HomTerm P Q)
    → (λ⇒ ∘ ((id {unit} ⊗₁ lᵗ) ∘ λ⇐)) ≈Term lᵗ
  leaf-frame-id lᵗ = begin
    λ⇒ ∘ ((id ⊗₁ lᵗ) ∘ λ⇐)   ≈⟨ ≈-Term-sym assoc ⟩
    (λ⇒ ∘ (id ⊗₁ lᵗ)) ∘ λ⇐   ≈⟨ ∘-resp-≈ λ⇒∘id⊗f≈f∘λ⇒ ≈-Term-refl ⟩
    (lᵗ ∘ λ⇒) ∘ λ⇐           ≈⟨ assoc ⟩
    lᵗ ∘ (λ⇒ ∘ λ⇐)           ≈⟨ ∘-resp-≈ ≈-Term-refl λ⇒∘λ⇐≈id ⟩
    lᵗ ∘ id                  ≈⟨ idʳ ⟩
    lᵗ                       ∎

--------------------------------------------------------------------------------
-- Reflecting on a Boolean `is-just` test back to a `just` witness.

private
  is-just-true→just
    : ∀ {a} {A : Set a} (m : Maybe A)
    → is-just m ≡ true → Σ A (λ x → m ≡ just x)
  is-just-true→just (just x) _    = x , refl
  is-just-true→just nothing  ()

--------------------------------------------------------------------------------
-- Leaf soundness: whenever `leaf-try s lᵗ ≡ just r`, `Pred s lᵗ r` holds.
-- This is the ONLY place the (proven, reverse) translation soundness enters.

private
  -- The leaf result, when it fires, is always `(unit , λ⇐ , λ⇒)`, and the
  -- guard is `is-just (findIso ⟪s⟫ ⟪lᵗ⟫) ≡ true`; re-run findIso to recover
  -- the iso witness, feed it to `soundness`, and chain with the
  -- coherence collapse `leaf-frame-id`.
  just-inj : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  leaf-try-sound
    : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q)
    → (r : Foc A B P Q) → leaf-try s lᵗ ≡ just r → Pred s lᵗ r
  leaf-try-sound {A} {B} {P} {Q} s lᵗ r eq
    with A ≟-ObjTerm P | B ≟-ObjTerm Q
  leaf-try-sound s lᵗ r eq | yes refl | yes refl
    with findIso ⟪ s ⟫ ⟪ lᵗ ⟫
  ... | just iso =
        -- `leaf-try` fired with `r ≡ (unit , λ⇐ , λ⇒)`; recover `s ≈Term lᵗ`.
        subst (Pred s lᵗ) (just-inj eq)
          (≈-Term-trans (SFW.soundness iso)
                        (≈-Term-sym (leaf-frame-id lᵗ)))
  ... | nothing  with eq
  ...   | ()
  leaf-try-sound s lᵗ r eq | yes refl | no _  with eq
  ... | ()
  leaf-try-sound s lᵗ r eq | no _ | _  with eq
  ... | ()

--------------------------------------------------------------------------------
-- Per-factor coherence chases for the `⊗` cases of `go-all`.
--
-- Right factor: the redex sits in `b`, so the frame wraps `a` (its parallel
-- wire) into `post` with associators.  We must show the assembled frame
-- equals `a ⊗₁ mb`, where `mb` is the inner frame for `b`.

private
  -- functoriality of ⊗ specialised: id ⊗ (g ∘ f) ≈ (id ⊗ g) ∘ (id ⊗ f)
  id⊗-∘ : ∀ {A B C D} {g : HomTerm C D} {f : HomTerm B C}
        → (id {A} ⊗₁ (g ∘ f)) ≈Term ((id {A} ⊗₁ g) ∘ (id {A} ⊗₁ f))
  id⊗-∘ {g = g} {f = f} =
    ≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist

  ⊗id-∘ : ∀ {A B C D} {g : HomTerm C D} {f : HomTerm B C}
        → ((g ∘ f) ⊗₁ id {A}) ≈Term ((g ⊗₁ id {A}) ∘ (f ⊗₁ id {A}))
  ⊗id-∘ {g = g} {f = f} =
    ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

  -- `a ⊗₁ m ≈ frame` for the right-factor wrapper, with
  -- `frame = ((a ⊗ post) ∘ α⇒) ∘ ((id ⊗ lᵗ) ∘ (α⇐ ∘ (id ⊗ pre)))`
  -- and `m = post ∘ ((id{k} ⊗ lᵗ) ∘ pre)`.
  rfactor-coh
    : ∀ {A₁ B₁ A B P Q} (k : ObjTerm)
      (a : HomTerm A₁ B₁) (pre : HomTerm A (k ⊗₀ P)) (post : HomTerm (k ⊗₀ Q) B)
      (lᵗ : HomTerm P Q)
    → (a ⊗₁ (post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre)))
      ≈Term
      (((a ⊗₁ post) ∘ α⇒) ∘ ((id {A₁ ⊗₀ k} ⊗₁ lᵗ) ∘ (α⇐ ∘ (id {A₁} ⊗₁ pre))))
  rfactor-coh {A₁} {B₁} {A} {B} {P} {Q} k a pre post lᵗ = begin
    a ⊗₁ (post ∘ ((id ⊗₁ lᵗ) ∘ pre))
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idʳ) ≈-Term-refl ⟩
    (a ∘ id) ⊗₁ (post ∘ ((id ⊗₁ lᵗ) ∘ pre))
      ≈⟨ ⊗-∘-dist ⟩
    (a ⊗₁ post) ∘ (id ⊗₁ ((id ⊗₁ lᵗ) ∘ pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl id⊗-∘ ⟩
    (a ⊗₁ post) ∘ ((id ⊗₁ (id ⊗₁ lᵗ)) ∘ (id ⊗₁ pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒-nat ≈-Term-refl) ⟩
    (a ⊗₁ post) ∘ ((α⇒ ∘ ((id ⊗₁ lᵗ) ∘ α⇐)) ∘ (id ⊗₁ pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    (a ⊗₁ post) ∘ (α⇒ ∘ (((id ⊗₁ lᵗ) ∘ α⇐) ∘ (id ⊗₁ pre)))
      ≈⟨ ≈-Term-sym assoc ⟩
    ((a ⊗₁ post) ∘ α⇒) ∘ (((id ⊗₁ lᵗ) ∘ α⇐) ∘ (id ⊗₁ pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    ((a ⊗₁ post) ∘ α⇒) ∘ ((id ⊗₁ lᵗ) ∘ (α⇐ ∘ (id ⊗₁ pre)))  ∎
    where
      -- naturality square of the associator, in the form we need:
      --   id {A₁} ⊗ (id {k} ⊗ lᵗ)  ≈  α⇒ ∘ ((id {A₁⊗k} ⊗ lᵗ) ∘ α⇐)
      -- i.e. `α⇒ ∘ ((id⊗id)⊗lᵗ) ≈ (id⊗(id⊗lᵗ)) ∘ α⇒` (assoc-commute), massaged.
      α⇒-nat : (id {A₁} ⊗₁ (id {k} ⊗₁ lᵗ))
               ≈Term (α⇒ ∘ ((id {A₁ ⊗₀ k} ⊗₁ lᵗ) ∘ α⇐))
      α⇒-nat = begin
        id ⊗₁ (id ⊗₁ lᵗ)
          ≈⟨ ≈-Term-sym idʳ ⟩
        (id ⊗₁ (id ⊗₁ lᵗ)) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
        (id ⊗₁ (id ⊗₁ lᵗ)) ∘ (α⇒ ∘ α⇐)
          ≈⟨ ≈-Term-sym assoc ⟩
        ((id ⊗₁ (id ⊗₁ lᵗ)) ∘ α⇒) ∘ α⇐
          ≈⟨ ∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl ⟩
        (α⇒ ∘ ((id ⊗₁ id) ⊗₁ lᵗ)) ∘ α⇐
          ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ id⊗id≈id ≈-Term-refl))
                      ≈-Term-refl ⟩
        (α⇒ ∘ (id ⊗₁ lᵗ)) ∘ α⇐
          ≈⟨ assoc ⟩
        α⇒ ∘ ((id ⊗₁ lᵗ) ∘ α⇐)  ∎

--------------------------------------------------------------------------------
-- Left-factor coherence chase (redex in `a`, parallel wire `b` routed left
-- past P/Q with σ).  This is the σ+α chase; the assembled frame equals the
-- inner frame for `a`, tensored with `b`.
--
-- `lfactor-coh` (PROVEN, no postulate): both sides are the same string
-- diagram — `ma ⊗ b` with the redex `lᵗ` routed to the rightmost wire by a
-- σ-braid and re-bracketed by associators; the braids cancel because σ∘σ≈id.
-- Proved by the same chase style as `rfactor-coh`, factored through
-- `braid-nat` (braid naturality) + `braid-conj` (braid conjugation of lᵗ).
private
  -- The braid `b_Z = α⇐ ∘ (id{k} ⊗ σ) ∘ α⇒ : (k ⊗ A₂) ⊗ Z → (k ⊗ Z) ⊗ A₂`
  -- (move the parallel wire `A₂` rightward past `Z`).  Core coherence:
  -- conjugating `id{k⊗A₂} ⊗ lᵗ` by the two braids is `(id{k} ⊗ lᵗ) ⊗ id{A₂}`.
  --
  -- We prove the bidirectional naturality square
  --   (id{k⊗A₂} ⊗ lᵗ) ∘ braidP⁻ ≈ braidQ⁻ ∘ ((id{k} ⊗ lᵗ) ⊗ id{A₂})
  -- where braidZ⁻ = α⇐ ∘ (id{k} ⊗ σ) ∘ α⇒ : (k⊗Z)⊗A₂ → (k⊗A₂)⊗Z, and use it.
  braid-nat
    : ∀ {k A₂ P Q} (lᵗ : HomTerm P Q)
    → ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒))
      ≈Term
      ((α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒) ∘ ((id {k} ⊗₁ lᵗ) ⊗₁ id {A₂}))
  braid-nat {k} {A₂} {P} {Q} lᵗ = begin
    (id ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    (id ⊗₁ lᵗ) ∘ ((α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒)
      ≈⟨ ≈-Term-sym assoc ⟩
    ((id ⊗₁ lᵗ) ∘ (α⇐ ∘ (id ⊗₁ σ))) ∘ α⇒
      ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
    (((id ⊗₁ lᵗ) ∘ α⇐) ∘ (id ⊗₁ σ)) ∘ α⇒
      -- naturality of α⇐ : (id{k⊗A₂} ⊗ lᵗ) ∘ α⇐ ≈ α⇐ ∘ (id{k} ⊗ (id{A₂} ⊗ lᵗ))
      ≈⟨ ∘-resp-≈ (∘-resp-≈ αinv-nat ≈-Term-refl) ≈-Term-refl ⟩
    ((α⇐ ∘ (id ⊗₁ (id ⊗₁ lᵗ))) ∘ (id ⊗₁ σ)) ∘ α⇒
      ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
    (α⇐ ∘ ((id ⊗₁ (id ⊗₁ lᵗ)) ∘ (id ⊗₁ σ))) ∘ α⇒
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym id⊗-∘)) ≈-Term-refl ⟩
    (α⇐ ∘ (id ⊗₁ ((id ⊗₁ lᵗ) ∘ σ))) ∘ α⇒
      -- σ-naturality on the inner wire: (id{A₂} ⊗ lᵗ) ∘ σ ≈ σ ∘ (lᵗ ⊗ id{A₂})
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl σ∘[id⊗lᵗ])) ≈-Term-refl ⟩
    (α⇐ ∘ (id ⊗₁ (σ ∘ (lᵗ ⊗₁ id {A₂})))) ∘ α⇒
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl id⊗-∘) ≈-Term-refl ⟩
    (α⇐ ∘ ((id ⊗₁ σ) ∘ (id ⊗₁ (lᵗ ⊗₁ id)))) ∘ α⇒
      ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
    ((α⇐ ∘ (id ⊗₁ σ)) ∘ (id ⊗₁ (lᵗ ⊗₁ id))) ∘ α⇒
      ≈⟨ assoc ⟩
    (α⇐ ∘ (id ⊗₁ σ)) ∘ ((id ⊗₁ (lᵗ ⊗₁ id)) ∘ α⇒)
      -- naturality of α⇒ : (id{k} ⊗ (lᵗ ⊗ id)) ∘ α⇒ ≈ α⇒ ∘ ((id{k} ⊗ lᵗ) ⊗ id)
      ≈⟨ ∘-resp-≈ ≈-Term-refl α⇒-nat2 ⟩
    (α⇐ ∘ (id ⊗₁ σ)) ∘ (α⇒ ∘ ((id ⊗₁ lᵗ) ⊗₁ id))
      ≈⟨ ≈-Term-sym assoc ⟩
    ((α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒) ∘ ((id ⊗₁ lᵗ) ⊗₁ id)
      ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
    (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ ((id ⊗₁ lᵗ) ⊗₁ id)  ∎
    where
      -- σ-naturality: (id{A₂} ⊗ lᵗ) ∘ σ ≈ σ ∘ (lᵗ ⊗ id{A₂}), where
      -- σ : P ⊗ A₂ → A₂ ⊗ P.  This is `sym` of `σ∘(lᵗ⊗id) ≈ (id⊗lᵗ)∘σ`.
      σ∘[id⊗lᵗ] : ((id {A₂} ⊗₁ lᵗ) ∘ σ) ≈Term (σ ∘ (lᵗ ⊗₁ id {A₂}))
      σ∘[id⊗lᵗ] = ≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ
      -- α⇐ naturality (inverse associator commute), derived from α-comm:
      --   (id{k⊗A₂} ⊗ lᵗ) ∘ α⇐  ≈  α⇐ ∘ (id{k} ⊗ (id{A₂} ⊗ lᵗ))
      αinv-nat : ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ α⇐)
                 ≈Term (α⇐ ∘ (id {k} ⊗₁ (id {A₂} ⊗₁ lᵗ)))
      αinv-nat = begin
        (id ⊗₁ lᵗ) ∘ α⇐
          ≈⟨ ≈-Term-sym idˡ ⟩
        id ∘ ((id ⊗₁ lᵗ) ∘ α⇐)
          ≈⟨ ∘-resp-≈ (≈-Term-sym α⇐∘α⇒≈id) ≈-Term-refl ⟩
        (α⇐ ∘ α⇒) ∘ ((id ⊗₁ lᵗ) ∘ α⇐)
          ≈⟨ assoc ⟩
        α⇐ ∘ (α⇒ ∘ ((id ⊗₁ lᵗ) ∘ α⇐))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        α⇐ ∘ ((α⇒ ∘ (id ⊗₁ lᵗ)) ∘ α⇐)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α-comm-inv ≈-Term-refl) ⟩
        α⇐ ∘ (((id ⊗₁ (id ⊗₁ lᵗ)) ∘ α⇒) ∘ α⇐)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        α⇐ ∘ ((id ⊗₁ (id ⊗₁ lᵗ)) ∘ (α⇒ ∘ α⇐))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇒∘α⇐≈id) ⟩
        α⇐ ∘ ((id ⊗₁ (id ⊗₁ lᵗ)) ∘ id)
          ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
        α⇐ ∘ (id ⊗₁ (id ⊗₁ lᵗ))  ∎
        where
          -- α⇒ ∘ ((id{k}⊗id{A₂}) ⊗ lᵗ) ≈ (id{k} ⊗ (id{A₂} ⊗ lᵗ)) ∘ α⇒, then
          -- absorb id⊗id≈id to get α⇒ ∘ (id ⊗ lᵗ) ≈ (id ⊗ (id ⊗ lᵗ)) ∘ α⇒.
          α-comm-inv : (α⇒ ∘ (id {k ⊗₀ A₂} ⊗₁ lᵗ))
                       ≈Term ((id {k} ⊗₁ (id {A₂} ⊗₁ lᵗ)) ∘ α⇒)
          α-comm-inv = begin
            α⇒ ∘ (id ⊗₁ lᵗ)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ (≈-Term-sym id⊗id≈id) ≈-Term-refl) ⟩
            α⇒ ∘ ((id ⊗₁ id) ⊗₁ lᵗ)
              ≈⟨ α-comm ⟩
            (id ⊗₁ (id ⊗₁ lᵗ)) ∘ α⇒  ∎
      -- α⇒ naturality: (id{k} ⊗ (lᵗ ⊗ id)) ∘ α⇒ ≈ α⇒ ∘ ((id{k} ⊗ lᵗ) ⊗ id)
      α⇒-nat2 : ((id {k} ⊗₁ (lᵗ ⊗₁ id {A₂})) ∘ α⇒)
                ≈Term (α⇒ ∘ ((id {k} ⊗₁ lᵗ) ⊗₁ id {A₂}))
      α⇒-nat2 = ≈-Term-sym α-comm

  -- The core middle identity: conjugation of `id{k⊗A₂} ⊗ lᵗ` by the braids.
  braid-conj
    : ∀ {k A₂ P Q} (lᵗ : HomTerm P Q)
    → ((α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒)
        ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒)))
      ≈Term
      ((id {k} ⊗₁ lᵗ) ⊗₁ id {A₂})
  braid-conj {k} {A₂} {P} {Q} lᵗ = begin
    (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ ((id ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (braid-nat lᵗ) ⟩
    (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
      ∘ ((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ ((id ⊗₁ lᵗ) ⊗₁ id))
      ≈⟨ ≈-Term-sym assoc ⟩
    ((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))) ∘ ((id ⊗₁ lᵗ) ⊗₁ id)
      ≈⟨ ∘-resp-≈ braid-cancel ≈-Term-refl ⟩
    id ∘ ((id ⊗₁ lᵗ) ⊗₁ id)
      ≈⟨ idˡ ⟩
    (id ⊗₁ lᵗ) ⊗₁ id  ∎
    where
      -- The two A₂-braids are mutually inverse (σ∘σ≈id + associators cancel);
      -- their composite on (k⊗Q)⊗A₂ is the identity.
      braid-cancel
        : ((α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒)) ∘ (α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒)))
          ≈Term id
      braid-cancel = begin
        (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
          ≈⟨ assoc ⟩
        α⇐ ∘ (((id ⊗₁ σ) ∘ α⇒) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
        α⇐ ∘ ((id ⊗₁ σ) ∘ ((α⇒ ∘ α⇐) ∘ ((id ⊗₁ σ) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl)) ⟩
        α⇐ ∘ ((id ⊗₁ σ) ∘ (id ∘ ((id ⊗₁ σ) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
        α⇐ ∘ ((id ⊗₁ σ) ∘ ((id ⊗₁ σ) ∘ α⇒))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        α⇐ ∘ (((id ⊗₁ σ) ∘ (id ⊗₁ σ)) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
        α⇐ ∘ (((id ∘ id) ⊗₁ (σ ∘ σ)) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ σ∘σ≈id) ≈-Term-refl) ⟩
        α⇐ ∘ ((id ⊗₁ id) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
        α⇐ ∘ (id ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
        α⇐ ∘ α⇒
          ≈⟨ α⇐∘α⇒≈id ⟩
        id  ∎

  lfactor-coh
    : ∀ {A₂ B₂ A B P Q} (k : ObjTerm)
      (b : HomTerm A₂ B₂) (pre : HomTerm A (k ⊗₀ P)) (post : HomTerm (k ⊗₀ Q) B)
      (lᵗ : HomTerm P Q)
    → ((post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre)) ⊗₁ b)
      ≈Term
      (((post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒)
       ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
          ∘ (α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂}))))
  lfactor-coh {A₂} {B₂} {A} {B} {P} {Q} k b pre post lᵗ = begin
    (post ∘ ((id ⊗₁ lᵗ) ∘ pre)) ⊗₁ b
      -- functoriality: split post off the left, and pre⊗id off the right.
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
    (post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre)) ⊗₁ (b ∘ id)
      ≈⟨ ⊗-∘-dist ⟩
    (post ⊗₁ b) ∘ (((id {k} ⊗₁ lᵗ) ∘ pre) ⊗₁ id)
      ≈⟨ ∘-resp-≈ ≈-Term-refl ⊗id-∘ ⟩
    (post ⊗₁ b) ∘ (((id {k} ⊗₁ lᵗ) ⊗₁ id {A₂}) ∘ (pre ⊗₁ id))
      -- replace (id{k}⊗lᵗ)⊗id by the braid conjugation of id{k⊗A₂}⊗lᵗ.
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym (braid-conj lᵗ)) ≈-Term-refl) ⟩
    (post ⊗₁ b)
      ∘ (((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
           ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))))
         ∘ (pre ⊗₁ id))
      -- re-associate into the target bracketing.
      ≈⟨ ∘-resp-≈ ≈-Term-refl reassoc ⟩
    (post ⊗₁ b)
      ∘ ((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
         ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
            ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id))))))
      ≈⟨ ≈-Term-sym assoc ⟩
    ((post ⊗₁ b) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)))
      ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
         ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id)))))  ∎
    where
      -- Push `pre⊗id` inward past the braid associators, to match the goal's
      -- right-associated `α⇐ ∘ (id⊗σ) ∘ α⇒ ∘ (pre⊗id)` bracketing.
      reassoc
        : ((α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒))
            ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒))))
            ∘ (pre ⊗₁ id {A₂})
          ≈Term
          (α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒))
            ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
               ∘ (α⇐ ∘ ((id {k} ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id {A₂})))))
      reassoc = begin
        ((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
          ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))))
          ∘ (pre ⊗₁ id)
          ≈⟨ assoc ⟩
        (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
          ∘ (((id {k ⊗₀ A₂} ⊗₁ lᵗ) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))) ∘ (pre ⊗₁ id))
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
          ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
             ∘ ((α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ (pre ⊗₁ id)))
          -- now re-bracket the braid∘(pre⊗id) tail to right-associated form
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl braid-tail) ⟩
        (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒))
          ∘ ((id {k ⊗₀ A₂} ⊗₁ lᵗ)
             ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id)))))  ∎
        where
          braid-tail
            : ((α⇐ ∘ ((id {k} ⊗₁ σ) ∘ α⇒)) ∘ (pre ⊗₁ id {A₂}))
              ≈Term (α⇐ ∘ ((id {k} ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id {A₂}))))
          braid-tail = begin
            (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)) ∘ (pre ⊗₁ id)
              ≈⟨ assoc ⟩
            α⇐ ∘ (((id ⊗₁ σ) ∘ α⇒) ∘ (pre ⊗₁ id))
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (pre ⊗₁ id)))  ∎

--==============================================================================
-- The mutual soundness recursion mirroring `Carve.focusAll`/`go-all`.

focusAll-sound : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q)
               → All-Pred s lᵗ (focusAll s lᵗ)
go-all-sound   : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q)
               → All-Pred s lᵗ (go-all s lᵗ)

-- `∘` : redex in `f` (left summand) then in `g` (right summand).
go-all-sound (g ∘ f) lᵗ =
  app-Pred
    (map-Pred (λ { (k , pre , post) → (k , pre , g ∘ post) })
              step-f (focusAll-sound f lᵗ))
    (map-Pred (λ { (k , pre , post) → (k , pre ∘ f , post) })
              step-g (focusAll-sound g lᵗ))
  where
    -- redex in `f`: from  f ≈ post ∘ ((id⊗lᵗ)∘pre)  conclude
    --   g ∘ f ≈ (g ∘ post) ∘ ((id⊗lᵗ)∘pre).
    step-f : ∀ r → Pred f lᵗ r
           → Pred (g ∘ f) lᵗ (proj₁ r , proj₁ (proj₂ r) , g ∘ proj₂ (proj₂ r))
    step-f (k , pre , post) ih = begin
      g ∘ f
        ≈⟨ ∘-resp-≈ ≈-Term-refl ih ⟩
      g ∘ (post ∘ ((id ⊗₁ lᵗ) ∘ pre))
        ≈⟨ ≈-Term-sym assoc ⟩
      (g ∘ post) ∘ ((id ⊗₁ lᵗ) ∘ pre)  ∎
    -- redex in `g`: from  g ≈ post ∘ ((id⊗lᵗ)∘pre)  conclude
    --   g ∘ f ≈ post ∘ ((id⊗lᵗ)∘(pre∘f)).
    step-g : ∀ r → Pred g lᵗ r
           → Pred (g ∘ f) lᵗ (proj₁ r , proj₁ (proj₂ r) ∘ f , proj₂ (proj₂ r))
    step-g (k , pre , post) ih = begin
      g ∘ f
        ≈⟨ ∘-resp-≈ ih ≈-Term-refl ⟩
      (post ∘ ((id ⊗₁ lᵗ) ∘ pre)) ∘ f
        ≈⟨ assoc ⟩
      post ∘ (((id ⊗₁ lᵗ) ∘ pre) ∘ f)
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      post ∘ ((id ⊗₁ lᵗ) ∘ (pre ∘ f))  ∎

-- `⊗` : redex in the right factor `b`, then in the left factor `a`.
go-all-sound (_⊗₁_ {A₁} {_} {A₂} a b) lᵗ =
  app-Pred
    (map-Pred (λ { (k , pre , post) →
                 (A₁ ⊗₀ k , α⇐ ∘ (id {A₁} ⊗₁ pre) , (a ⊗₁ post) ∘ α⇒) })
              step-b (focusAll-sound b lᵗ))
    (map-Pred (λ { (k , pre , post) →
                 ( k ⊗₀ A₂
                 , α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂})
                 , (post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ) })
              step-a (focusAll-sound a lᵗ))
  where
    step-b : ∀ r → Pred b lᵗ r
           → Pred (a ⊗₁ b) lᵗ
               ( A₁ ⊗₀ proj₁ r
               , α⇐ ∘ (id {A₁} ⊗₁ proj₁ (proj₂ r))
               , (a ⊗₁ proj₂ (proj₂ r)) ∘ α⇒ )
    step-b (k , pre , post) ih = begin
      a ⊗₁ b
        ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
      a ⊗₁ (post ∘ ((id ⊗₁ lᵗ) ∘ pre))
        ≈⟨ rfactor-coh k a pre post lᵗ ⟩
      ((a ⊗₁ post) ∘ α⇒) ∘ ((id ⊗₁ lᵗ) ∘ (α⇐ ∘ (id ⊗₁ pre)))  ∎
    step-a : ∀ r → Pred a lᵗ r
           → Pred (a ⊗₁ b) lᵗ
               ( proj₁ r ⊗₀ A₂
               , α⇐ ∘ (id {proj₁ r} ⊗₁ σ) ∘ α⇒ ∘ (proj₁ (proj₂ r) ⊗₁ id {A₂})
               , (proj₂ (proj₂ r) ⊗₁ b) ∘ α⇐ ∘ (id {proj₁ r} ⊗₁ σ) ∘ α⇒ )
    step-a (k , pre , post) ih = begin
      a ⊗₁ b
        ≈⟨ ⊗-resp-≈ ih ≈-Term-refl ⟩
      (post ∘ ((id ⊗₁ lᵗ) ∘ pre)) ⊗₁ b
        ≈⟨ lfactor-coh k b pre post lᵗ ⟩
      ((post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒)
        ∘ ((id ⊗₁ lᵗ) ∘ (α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂})))  ∎

-- remaining heads (`Agen`, `id`, λ/ρ/α/σ): `go-all _ _ = []`.
go-all-sound (Agen _) lᵗ = []
go-all-sound id      lᵗ = []
go-all-sound λ⇒      lᵗ = []
go-all-sound λ⇐      lᵗ = []
go-all-sound ρ⇒      lᵗ = []
go-all-sound ρ⇐      lᵗ = []
go-all-sound α⇒      lᵗ = []
go-all-sound α⇐      lᵗ = []
go-all-sound σ       lᵗ = []

-- `focusAll s lᵗ` prepends the leaf (when it fires) to `go-all s lᵗ`.
focusAll-sound s lᵗ with leaf-try s lᵗ in eqLeaf
... | just r  = leaf-try-sound s lᵗ r eqLeaf ∷ go-all-sound s lᵗ
... | nothing = go-all-sound s lᵗ

--==============================================================================
-- Corollary: `focusAtₙ`-level soundness.  Looking up the `n`-th focus result
-- and recovering its `Pred` from `All-Pred (focusAll s lᵗ)`.

private
  -- `lookupMaybe` of an `All-Pred` list: a hit yields the element's `Pred`.
  lookup-Pred
    : ∀ {A B P Q} {s : HomTerm A B} {lᵗ : HomTerm P Q}
      {xs : List (Foc A B P Q)} → All-Pred s lᵗ xs
    → ∀ n {r} → lookupMaybe xs n ≡ just r → Pred s lᵗ r
  lookup-Pred []         n        ()
  lookup-Pred (px ∷ pxs) zero     refl = px
  lookup-Pred (px ∷ pxs) (suc n)  eq   = lookup-Pred pxs n eq

-- The headline term-soundness of `focusAtₙ`: for the `n`-th focus position,
-- `s ≈Term post ∘ ((id{k} ⊗₁ lᵗ) ∘ pre)` — i.e. `s ≈Term frame k pre post lᵗ`.
-- This is exactly the term-level content of LEG 3 sub-proof (2), specialised
-- to `mid = lᵗ` (the case the `deepFrame`/`focFrame` iso uses).
focusAtₙ-sound
  : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) (n : ℕ)
    {k : ObjTerm} {pre : HomTerm A (k ⊗₀ P)} {post : HomTerm (k ⊗₀ Q) B}
  → focusAtₙ s lᵗ n ≡ just (k , pre , post)
  → s ≈Term (post ∘ ((id {k} ⊗₁ lᵗ) ∘ pre))
focusAtₙ-sound s lᵗ n eq =
  lookup-Pred (focusAll-sound s lᵗ) n eq

--==============================================================================
-- SUB-PROOF (3): retract soundness.
--
-- `ExtendSig.retract : HomTerm⁺ A B → Maybe (HomTerm A B)` strips the hole
-- signature; it is total on hole-free terms.  The verifiable soundness content
-- is that `retract` is a faithful RIGHT INVERSE to the signature inclusion
-- `incl : HomTerm A B → HomTerm⁺ A B` (`Agen f ↦ Agen⁺ (old f)`, all coherence
-- preserved): `retract (incl p) ≡ just p` for every base term `p`.  This is
-- what lets the assembly replace `retract pre⁺`/`retract post⁺` by genuine
-- base-signature terms whose translation is controlled.  Proven by structural
-- induction; ZERO postulates.

module RetractSound (P Q : ObjTerm) where

  module Ext = Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig sig-dec P Q
  open Ext using (old; sig⁺; retract)
  open APROP sig⁺ using ()
    renaming ( HomTerm to HomTerm⁺ ; Agen to Agen⁺ ; id to id⁺ ; _∘_ to _∘⁺_
             ; _⊗₁_ to _⊗₁⁺_ ; λ⇒ to λ⇒⁺ ; λ⇐ to λ⇐⁺ ; ρ⇒ to ρ⇒⁺ ; ρ⇐ to ρ⇐⁺
             ; α⇒ to α⇒⁺ ; α⇐ to α⇐⁺ ; σ to σ⁺ )

  -- The signature inclusion on terms (the section retract right-inverts).
  incl : ∀ {A B} → HomTerm A B → HomTerm⁺ A B
  incl (Agen f) = Agen⁺ (old f)
  incl id       = id⁺
  incl (g ∘ f)  = incl g ∘⁺ incl f
  incl (f ⊗₁ g) = incl f ⊗₁⁺ incl g
  incl λ⇒       = λ⇒⁺
  incl λ⇐       = λ⇐⁺
  incl ρ⇒       = ρ⇒⁺
  incl ρ⇐       = ρ⇐⁺
  incl α⇒       = α⇒⁺
  incl α⇐       = α⇐⁺
  incl (σ {A} {B} ⦃ inst ⦄) = σ⁺ {A} {B} ⦃ inst ⦄

  -- Retract section: `retract` is a left inverse of `incl`.  Structural
  -- induction; the `∘`/`⊗₁` cases rewrite both recursive `retract`s to `just`.
  retract-incl : ∀ {A B} (p : HomTerm A B) → retract (incl p) ≡ just p
  retract-incl (Agen f) = refl
  retract-incl id       = refl
  retract-incl (g ∘ f)
    rewrite retract-incl g | retract-incl f = refl
  retract-incl (f ⊗₁ g)
    rewrite retract-incl f | retract-incl g = refl
  retract-incl λ⇒       = refl
  retract-incl λ⇐       = refl
  retract-incl ρ⇒       = refl
  retract-incl ρ⇐       = refl
  retract-incl α⇒       = refl
  retract-incl α⇐       = refl
  retract-incl (σ ⦃ _ ⦄) = refl

  -- Conversely, where `retract` succeeds it inverts `incl`: from
  -- `retract p ≡ just p₀` we get `p ≡ incl p₀` (so `p` was hole-free and is
  -- exactly the inclusion of its retract).  Structural induction on `p`.
  retract-faithful
    : ∀ {A B} (p : HomTerm⁺ A B) {p₀ : HomTerm A B}
    → retract p ≡ just p₀ → p ≡ incl p₀
  retract-faithful (Agen⁺ (old f))    refl = refl
  retract-faithful (Agen⁺ (Ext.hole _ _)) ()
  retract-faithful id⁺ refl = refl
  retract-faithful (g ∘⁺ f) eq        = ∘-case g f eq
    where
      ∘-case : ∀ {A B C} (g : HomTerm⁺ B C) (f : HomTerm⁺ A B) {p₀}
             → retract (g ∘⁺ f) ≡ just p₀ → (g ∘⁺ f) ≡ incl p₀
      ∘-case g f eq with retract g | retract-faithful g
                       | retract f | retract-faithful f
      ∘-case g f refl | just g₀ | rg | just f₀ | rf
        rewrite rg refl | rf refl = refl
  retract-faithful (f ⊗₁⁺ g) eq       = ⊗-case f g eq
    where
      ⊗-case : ∀ {A B C D} (f : HomTerm⁺ A B) (g : HomTerm⁺ C D) {p₀}
             → retract (f ⊗₁⁺ g) ≡ just p₀ → (f ⊗₁⁺ g) ≡ incl p₀
      ⊗-case f g eq with retract f | retract-faithful f
                       | retract g | retract-faithful g
      ⊗-case f g refl | just f₀ | rf | just g₀ | rg
        rewrite rf refl | rg refl = refl
  retract-faithful λ⇒⁺ refl = refl
  retract-faithful λ⇐⁺ refl = refl
  retract-faithful ρ⇒⁺ refl = refl
  retract-faithful ρ⇐⁺ refl = refl
  retract-faithful α⇒⁺ refl = refl
  retract-faithful α⇐⁺ refl = refl
  retract-faithful (σ⁺ ⦃ _ ⦄)  refl = refl

--==============================================================================
-- SUB-PROOF (5): pad-layer soundness (peel wrappers are isos).
--
-- The pad layer (`Deep.repadR`/`repadL`) wraps a frame with peel maps
-- `r Xo : k ⊗ Xo → k₁ ⊗ place Xo` and `u Xo : k₁ ⊗ place Xo → k ⊗ Xo` built
-- from σ/α coherence.  Their verifiable soundness content is that they are
-- mutually inverse (`u Xo ∘ r Xo ≈Term id`): this is what makes repadding sound
-- (the repadded frame is the old frame conjugated by an iso, so it represents
-- the same morphism).  We re-derive the `peelR`-base round-trip here (the
-- `Var w` leaf, the only place σ/λ enters); the recursive α-lifts preserve a
-- round-trip by the same `α⇐∘α⇒≈id` / functoriality bookkeeping.  PROVEN.

private
  -- `peelR` leaf maps for the `Var w` pad (place Xo = Xo ⊗ Var w):
  --   r Xo = λ⇐ ∘ σ : (Var w) ⊗ Xo → unit ⊗ (Xo ⊗ Var w)
  --   u Xo = σ ∘ λ⇒ : unit ⊗ (Xo ⊗ Var w) → (Var w) ⊗ Xo
  -- (here k = Var w, k₁ = unit).  They are mutually inverse.
  peelR-leaf-iso
    : ∀ {w} (Xo : ObjTerm)
    → ((σ ∘ λ⇒) ∘ (λ⇐ ∘ σ)) ≈Term id {Var w ⊗₀ Xo}
  peelR-leaf-iso {w} Xo = begin
    (σ ∘ λ⇒) ∘ (λ⇐ ∘ σ)
      ≈⟨ assoc ⟩
    σ ∘ (λ⇒ ∘ (λ⇐ ∘ σ))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    σ ∘ ((λ⇒ ∘ λ⇐) ∘ σ)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ λ⇒∘λ⇐≈id ≈-Term-refl) ⟩
    σ ∘ (id ∘ σ)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    σ ∘ σ
      ≈⟨ σ∘σ≈id ⟩
    id  ∎

  -- And the other direction (`r Xo ∘ u Xo ≈ id`), completing the iso.
  peelR-leaf-iso'
    : ∀ {w} (Xo : ObjTerm)
    → ((λ⇐ ∘ σ) ∘ (σ ∘ λ⇒)) ≈Term id {unit ⊗₀ (Xo ⊗₀ Var w)}
  peelR-leaf-iso' {w} Xo = begin
    (λ⇐ ∘ σ) ∘ (σ ∘ λ⇒)
      ≈⟨ assoc ⟩
    λ⇐ ∘ (σ ∘ (σ ∘ λ⇒))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    λ⇐ ∘ ((σ ∘ σ) ∘ λ⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ∘σ≈id ≈-Term-refl) ⟩
    λ⇐ ∘ (id ∘ λ⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    λ⇐ ∘ λ⇒
      ≈⟨ λ⇐∘λ⇒≈id ⟩
    id  ∎

  -- `peelL` leaf maps (place Xo = Var w ⊗ Xo): r Xo = λ⇐, u Xo = λ⇒.
  -- Trivially inverse by the left-unitor iso.
  peelL-leaf-iso : ∀ {A} → (λ⇒ ∘ (λ⇐ {A})) ≈Term id
  peelL-leaf-iso = λ⇒∘λ⇐≈id
  peelL-leaf-iso' : ∀ {A} → (λ⇐ ∘ (λ⇒ {A})) ≈Term id
  peelL-leaf-iso' = λ⇐∘λ⇒≈id

  -- The recursive α-lift wrappers preserve the round-trip: if `u ∘ r ≈ id`
  -- then `(α⇐ ∘ (id ⊗ u') ∘ α⇒) ∘ (α⇐ ∘ (id ⊗ r') ∘ α⇒) ≈ id`, for the
  -- `liftR`-shaped lifts, where `u' ∘ r' ≈ id`.  This is the generic
  -- associator-conjugation iso (no σ; the σ is confined to the leaf).
  liftR-iso
    : ∀ {kl kr Xo Za Zb}
      {r' : HomTerm (kr ⊗₀ Xo) (Za ⊗₀ Zb)} {u' : HomTerm (Za ⊗₀ Zb) (kr ⊗₀ Xo)}
    → (u' ∘ r') ≈Term id
    → ((α⇐ ∘ ((id {kl} ⊗₁ u') ∘ α⇒)) ∘ (α⇐ ∘ ((id {kl} ⊗₁ r') ∘ α⇒)))
      ≈Term id {(kl ⊗₀ kr) ⊗₀ Xo}
  liftR-iso {kl} {kr} {Xo} {Za} {Zb} {r'} {u'} ur = begin
    (α⇐ ∘ ((id ⊗₁ u') ∘ α⇒)) ∘ (α⇐ ∘ ((id ⊗₁ r') ∘ α⇒))
      ≈⟨ assoc ⟩
    α⇐ ∘ (((id ⊗₁ u') ∘ α⇒) ∘ (α⇐ ∘ ((id ⊗₁ r') ∘ α⇒)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    α⇐ ∘ ((id ⊗₁ u') ∘ (α⇒ ∘ (α⇐ ∘ ((id ⊗₁ r') ∘ α⇒))))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    α⇐ ∘ ((id ⊗₁ u') ∘ ((α⇒ ∘ α⇐) ∘ ((id ⊗₁ r') ∘ α⇒)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl)) ⟩
    α⇐ ∘ ((id ⊗₁ u') ∘ (id ∘ ((id ⊗₁ r') ∘ α⇒)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
    α⇐ ∘ ((id ⊗₁ u') ∘ ((id ⊗₁ r') ∘ α⇒))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    α⇐ ∘ (((id ⊗₁ u') ∘ (id ⊗₁ r')) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
    α⇐ ∘ (((id ∘ id) ⊗₁ (u' ∘ r')) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ ur) ≈-Term-refl) ⟩
    α⇐ ∘ ((id ⊗₁ id) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    α⇐ ∘ (id ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    α⇐ ∘ α⇒
      ≈⟨ α⇐∘α⇒≈id ⟩
    id  ∎

--==============================================================================
-- SUB-PROOF (4) + final assembly: STATUS / blocker.
--
-- The headline leg is
--     ⟪ deepFrame s lᵗ lᵗ n found ⟫ ≅ᴴ ⟪ ctx ⟫[h ↦ ⟪lᵗ⟫].
-- Assembly recipe from the proven pieces:
--   * (1) frame-expand: LHS = ⟪post ∘ ((id{k}⊗lᵗ)∘pre)⟫ (definitional).
--   * (4) hole-subst-commutes: ⟪ctx⟫[h↦⟪lᵗ⟫] ≅ᴴ ⟪ ctx[h↦lᵗ] ⟫ where ctx[h↦lᵗ]
--         is the TERM-level single-hole substitution (replace `Agen⁺ hole!` by
--         `incl lᵗ`, then `retract`).  This reduces the graph-level RHS to a
--         base-sig translation.
--   * (2) focusAtₙ-sound (over sig⁺): ctx ≈Term⁺ post⁺ ∘ ((id{k}⊗Agen⁺ hole!)∘pre⁺),
--         and substituting `Agen⁺ hole! ↦ incl lᵗ` is a ≈Term⁺-congruence, giving
--         ctx[h↦lᵗ] ≈Term post₀ ∘ ((id{k}⊗lᵗ)∘pre₀) after (3) retract.
--   * (3) retract-faithful: pre⁺ = incl pre₀, post⁺ = incl post₀, so the
--         substituted/retracted contexts ARE the base-sig pre₀/post₀.
--   * Land the ≈Term equality as ≅ᴴ.
--
-- BLOCKER (documented in LEG3-NOTES.md): the last step needs the FORWARD
-- translation soundness  `f ≈Term g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫`  (the "Hypergraph
-- completeness" direction), which does NOT yet exist in the tree (only the
-- reverse `soundness` does).  Building it is the per-axiom
-- graph-identity induction (every coherence axiom translates to an `hId`/`hSwap`
-- collapse, plus `hComposeP`/`hTensor` congruences) — a separate, sizeable
-- effort (~the unwritten `Hypergraph.Completeness` module).
--
-- We therefore expose the term-level content that DOES compose (proven above)
-- as the reusable kernel; the graph-level ≅ᴴ wrap-up is gated on that one
-- forward lemma.  The honest LEG-3 statement we CAN discharge right now is the
-- term-level recomposition identity:
--   `focusAtₙ-sound` gives `ctx ≈Term frame⁺`, and (after subst+retract) the
--   base-sig `s ≈Term deepFrame`.  See LEG3-NOTES.md for the precise ledger.

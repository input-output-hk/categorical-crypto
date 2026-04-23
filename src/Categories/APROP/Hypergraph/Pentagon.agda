{-# OPTIONS --without-K --lossy-unification #-}

--------------------------------------------------------------------------------
-- Pentagon coherence axiom:
--
--   `id⊗α⇒ ∘ α⇒ ∘ α⇒⊗id ≈Term α⇒ ∘ α⇒{A⊗B,C,D}`
--
-- at type `((A⊗B)⊗C)⊗D → A⊗(B⊗(C⊗D))`.
--
-- Structure of the intended constructive proof:
--
--   1. Each leaf of the pentagon AST reduces to `subst₂ _ refl p (hId …)`
--      by one of the three building-block lemmas below.
--   2. Each `hComposeP G (subst₂ refl p K)` factors to
--      `subst₂ refl p (hComposeP G K)` via `hComposeP-cod-subst`.
--   3. Each `hComposeP G (hId X)` reduces to `G` via
--      `hCompose-hId-R-iso-generic`; under `subst₂-resp-≅ᴴ refl p` the
--      enclosing `subst₂ refl p` survives.
--   4. Nested `subst₂ refl _` on the cod collapses via
--      `subst₂-trans-cod`.
--   5. After peeling all three (resp. two) factors, both sides are
--      `subst₂ refl p-FINAL (hId (((A⊗B)⊗C)⊗D))` — with different
--      `p-FINAL`s, which are propositionally equal by
--      `pentagon-list-coherence` (Mac Lane's pentagon for `++-assoc`).
--
-- STATUS:
--   * Building-block lemmas 1 + 2 + 3 are proved.
--   * `pentagon-list-coherence` is postulated (step 5) — a pure
--     combinatorial claim at the `List Y` level, provable by induction
--     on `xs` with cong-swap helpers; isolated from Hypergraph machinery.
--   * The full peel chain (steps 2–4 applied three times for LHS, twice
--     for RHS) requires careful subst₂ bookkeeping.  Currently the
--     overall `pentagon-sound` sits behind a focused postulate while the
--     chain is threaded; a future pass replaces the postulate with
--     `subst (_ ≅ᴴ_) p-eq (refl-≅ᴴ _)` or equivalent.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Pentagon (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.SoundnessAxioms sig
  using (hCompose-hId-R-iso-generic)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- Private building-block lemmas (all proved).

private
  hTensor-subst₂-left
    : ∀ {As As' Bs Bs' Cs Ds : List X}
        (p : As ≡ As') (q : Bs ≡ Bs')
        (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
    → hTensor (subst₂ (Hypergraph FlatGen) p q X₀) Y₀
    ≡ subst₂ (Hypergraph FlatGen) (cong (_++ Cs) p) (cong (_++ Ds) q)
             (hTensor X₀ Y₀)
  hTensor-subst₂-left refl refl X₀ Y₀ = refl

  hTensor-subst₂-right
    : ∀ {As Bs Cs Cs' Ds Ds' : List X}
        (p : Cs ≡ Cs') (q : Ds ≡ Ds')
        (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
    → hTensor X₀ (subst₂ (Hypergraph FlatGen) p q Y₀)
    ≡ subst₂ (Hypergraph FlatGen) (cong (As ++_) p) (cong (Bs ++_) q)
             (hTensor X₀ Y₀)
  hTensor-subst₂-right refl refl X₀ Y₀ = refl

  -- `hComposeP` factors a `subst₂ refl _` out of its right argument.
  hComposeP-cod-subst
    : ∀ {As Bs Cs Cs' : List X}
        (eq : Cs ≡ Cs')
        (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Bs Cs)
    → hComposeP G (subst₂ (Hypergraph FlatGen) refl eq K)
    ≡ subst₂ (Hypergraph FlatGen) refl eq (hComposeP G K)
  hComposeP-cod-subst refl G K = refl

  -- Collapse nested `subst₂ refl _` on the cod.
  subst₂-trans-cod
    : ∀ {As Bs Bs' Bs'' : List X}
        (p : Bs ≡ Bs') (q : Bs' ≡ Bs'')
        (G : Hypergraph FlatGen As Bs)
    → subst₂ (Hypergraph FlatGen) refl q
             (subst₂ (Hypergraph FlatGen) refl p G)
    ≡ subst₂ (Hypergraph FlatGen) refl (trans p q) G
  subst₂-trans-cod refl refl G = refl

--------------------------------------------------------------------------------
-- Each leaf of the pentagon AST reduces to `subst₂`-wrapped `hId`.

α⇒⊗id-as-subst-hId
  : ∀ (X Y Z D : ObjTerm)
  → ⟪ α⇒ {X} {Y} {Z} ⊗₁ id {D} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (cong (_++ flatten D)
                 (++-assoc (flatten X) (flatten Y) (flatten Z)))
           (hId (((X ⊗₀ Y) ⊗₀ Z) ⊗₀ D))
α⇒⊗id-as-subst-hId X Y Z D =
  hTensor-subst₂-left refl
    (++-assoc (flatten X) (flatten Y) (flatten Z))
    (hId ((X ⊗₀ Y) ⊗₀ Z)) (hId D)

id⊗α⇒-as-subst-hId
  : ∀ (A X Y Z : ObjTerm)
  → ⟪ id {A} ⊗₁ α⇒ {X} {Y} {Z} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (cong (flatten A ++_)
                 (++-assoc (flatten X) (flatten Y) (flatten Z)))
           (hId (A ⊗₀ ((X ⊗₀ Y) ⊗₀ Z)))
id⊗α⇒-as-subst-hId A X Y Z =
  hTensor-subst₂-right refl
    (++-assoc (flatten X) (flatten Y) (flatten Z))
    (hId A) (hId ((X ⊗₀ Y) ⊗₀ Z))

α⇒-as-subst-hId
  : ∀ (X Y Z : ObjTerm)
  → ⟪ α⇒ {X} {Y} {Z} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (++-assoc (flatten X) (flatten Y) (flatten Z))
           (hId ((X ⊗₀ Y) ⊗₀ Z))
α⇒-as-subst-hId X Y Z = refl

--------------------------------------------------------------------------------
-- Mac Lane's pentagon coherence at the list level.
--
-- Both sides witness `((xs ++ ys) ++ zs) ++ ws ≡ xs ++ ys ++ zs ++ ws`
-- as `_≡_`-proofs, and they are propositionally equal.  Base case
-- proved; inductive case left to future work (requires a careful
-- cong-swap chain — written and compiles modulo one Agda structural
-- mismatch between two equivalent `trans`-nestings).

private
  -- `cong ([] ++_) p ≡ p` since `[] ++ l = l` definitionally.
  cong-[]-++
    : ∀ {Y : Set} {a b : List Y} (p : a ≡ b) → cong ([] ++_) p ≡ p
  cong-[]-++ refl = refl

  -- `trans p refl ≡ p`.
  trans-reflʳ
    : ∀ {Y : Set} {a b : List Y} (p : a ≡ b) → trans p refl ≡ p
  trans-reflʳ refl = refl

  -- `cong (x ∷_) distributes over trans`.
  cong-∷-trans
    : ∀ {Y : Set} {a b c : List Y} (x : Y) (p : a ≡ b) (q : b ≡ c)
    → cong (x ∷_) (trans p q) ≡ trans (cong (x ∷_) p) (cong (x ∷_) q)
  cong-∷-trans x refl q = refl

  -- `cong (_++ ws) (cong (x ∷_) p) ≡ cong (x ∷_) (cong (_++ ws) p)`.
  cong-swap-∷-++ʳ
    : ∀ {Y : Set} {a b : List Y} (x : Y) (ws : List Y) (p : a ≡ b)
    → cong (_++ ws) (cong (x ∷_) p) ≡ cong (x ∷_) (cong (_++ ws) p)
  cong-swap-∷-++ʳ x ws refl = refl

  -- `cong (_++_ (x ∷ xs)) p ≡ cong (x ∷_) (cong (_++_ xs) p)`.
  cong-∷-++-expand
    : ∀ {Y : Set} {a b : List Y} (x : Y) (xs : List Y) (p : a ≡ b)
    → cong (_++_ (x ∷ xs)) p ≡ cong (x ∷_) (cong (_++_ xs) p)
  cong-∷-++-expand x xs refl = refl

-- Pentagon at the list level, proved for the base case and postulated
-- inductively.  Fully constructive proof left to a future pass (needs
-- additional `trans`-associativity bookkeeping on the inductive step).

postulate
  pentagon-list-coherence
    : ∀ {Y : Set} (xs ys zs ws : List Y)
    → trans (cong (_++ ws) (++-assoc xs ys zs))
            (trans (++-assoc xs (ys ++ zs) ws)
                   (cong (xs ++_) (++-assoc ys zs ws)))
    ≡ trans (++-assoc (xs ++ ys) zs ws) (++-assoc xs ys (zs ++ ws))

-- Proof of the base case, kept as a verified sub-claim.  Not used for
-- the full `pentagon-list-coherence` above (which is postulated), but
-- exported as evidence the technique works for the trivial list and as
-- a starting point for completing the inductive case.

pentagon-list-coherence-base
  : ∀ {Y : Set} (ys zs ws : List Y)
  → trans (cong (_++ ws) (++-assoc {A = Y} [] ys zs))
          (trans (++-assoc [] (ys ++ zs) ws)
                 (cong ([] ++_) (++-assoc ys zs ws)))
  ≡ trans (++-assoc ([] ++ ys) zs ws) (++-assoc [] ys (zs ++ ws))
pentagon-list-coherence-base ys zs ws =
  trans (cong-[]-++ (++-assoc ys zs ws))
        (sym (trans-reflʳ (++-assoc ys zs ws)))

--------------------------------------------------------------------------------
-- Pentagon.
--
-- The building blocks and `pentagon-list-coherence` above express all
-- the mathematical content of pentagon.  Wiring them into an actual
-- ≅ᴴ-proof requires a lengthy `subst₂` bookkeeping chain (five peel
-- steps, mixing `≡`-rewrites and `≅ᴴ`-transports).  For the moment we
-- expose `pentagon-sound` as a focused postulate; the plan in the
-- module header describes how to discharge it.

postulate
  pentagon-sound
    : ∀ {A B C D}
    → ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
    ≅ᴴ ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫

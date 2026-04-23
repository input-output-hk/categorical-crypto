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
-- STATUS: `pentagon-sound` is **fully constructive** modulo the one
-- pure-list-level postulate `pentagon-list-coherence` (Mac Lane's
-- pentagon for `++-assoc`).  All hypergraph-level reasoning is proved.
--
-- Verified pieces:
--   * 3 leaf-reduction lemmas (α⇒⊗id-, id⊗α⇒-, α⇒-as-subst-hId).
--   * 4 `subst₂` + `hComposeP` manipulation lemmas
--     (hComposeP-cod-subst, subst₂-trans-cod, hTensor-subst₂-{left,right}).
--   * LHS ≅ᴴ mid via a 6-step peel chain using `hCompose-hId-R-iso-generic`.
--   * RHS ≅ᴴ mid via a 4-step peel chain.
--   * `pentagon-sound = trans-≅ᴴ LHS≅mid (sym-≅ᴴ RHS≅mid)`.
--
-- Outstanding postulate:
--   * `pentagon-list-coherence` — proven for the base case
--     (`pentagon-list-coherence-base`); inductive case requires a careful
--     `cong-swap`/`trans-assoc` chain (all component helpers are proved;
--     only the final assembly needs more `trans`-associativity bookkeeping).
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
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

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

pentagon-sound
  : ∀ {A B C D}
  → ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
  ≅ᴴ ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫
pentagon-sound {A} {B} {C} {D} = trans-≅ᴴ LHS≅mid (sym-≅ᴴ RHS≅mid)
  where
    dom-type : List X
    dom-type = ((flatten A ++ flatten B) ++ flatten C) ++ flatten D

    cod-type : List X
    cod-type = flatten A ++ flatten B ++ flatten C ++ flatten D

    hId-root : Hypergraph FlatGen dom-type dom-type
    hId-root = hId (((A ⊗₀ B) ⊗₀ C) ⊗₀ D)

    p₁ : dom-type ≡ (flatten A ++ flatten B ++ flatten C) ++ flatten D
    p₁ = cong (_++ flatten D) (++-assoc (flatten A) (flatten B) (flatten C))

    p₂ : (flatten A ++ flatten B ++ flatten C) ++ flatten D
       ≡ flatten A ++ (flatten B ++ flatten C) ++ flatten D
    p₂ = ++-assoc (flatten A) (flatten B ++ flatten C) (flatten D)

    p₃ : flatten A ++ (flatten B ++ flatten C) ++ flatten D ≡ cod-type
    p₃ = cong (flatten A ++_) (++-assoc (flatten B) (flatten C) (flatten D))

    q₁ : dom-type ≡ (flatten A ++ flatten B) ++ flatten C ++ flatten D
    q₁ = ++-assoc (flatten A ++ flatten B) (flatten C) (flatten D)

    q₂ : (flatten A ++ flatten B) ++ flatten C ++ flatten D ≡ cod-type
    q₂ = ++-assoc (flatten A) (flatten B) (flatten C ++ flatten D)

    -- Common middle form: both LHS and RHS are ≅ᴴ to this.
    mid : Hypergraph FlatGen dom-type cod-type
    mid = subst₂ (Hypergraph FlatGen) refl (trans p₁ (trans p₂ p₃)) hId-root

    ----------------------------------------------------------------------------
    -- LHS ≅ᴴ mid.
    --
    -- Chain (each step is ≡ or ≅ᴴ, threaded through `subst` /
    -- `trans-≅ᴴ`).  Let:
    --   T₁ = subst₂ refl p₁ hId-root
    --   T₂ = subst₂ refl p₂ (hId ((A ⊗ (B ⊗ C)) ⊗ D))
    --   T₃ = subst₂ refl p₃ (hId (A ⊗ ((B ⊗ C) ⊗ D)))
    --
    -- Chain (LHS-A = ⟪α⇒⊗id⟫, LHS-B = ⟪α⇒⟫, LHS-C = ⟪id⊗α⇒⟫):
    --
    --  lhs
    --   ≡ hComposeP (hComposeP LHS-A LHS-B) LHS-C                [def]
    --   ≡ hComposeP (hComposeP T₁ T₂) T₃                          [3× α⇒-as-subst-hId via cong₂]
    --   ≡ hComposeP (hComposeP T₁ T₂) (subst refl p₃ hId₃)        [def, T₃]
    --   ≡ subst₂ refl p₃ (hComposeP (hComposeP T₁ T₂) hId₃)       [hComposeP-cod-subst]
    --   ≅ᴴ subst₂ refl p₃ (hComposeP T₁ T₂)                       [subst₂-resp-≅ᴴ + hCompose-hId-R]
    --   ≡ subst₂ refl p₃ (hComposeP T₁ (subst refl p₂ hId₂))      [def, T₂]
    --   ≡ subst₂ refl p₃ (subst₂ refl p₂ (hComposeP T₁ hId₂))     [hComposeP-cod-subst, under cong]
    --   ≅ᴴ subst₂ refl p₃ (subst₂ refl p₂ T₁)                     [subst₂-resp-≅ᴴ² + hCompose-hId-R]
    --   ≡ subst₂ refl p₃ (subst₂ refl p₂ (subst₂ refl p₁ hId-root)) [def, T₁]
    --   ≡ subst₂ refl p₃ (subst₂ refl (trans p₁ p₂) hId-root)     [cong (subst _ refl p₃) (subst₂-trans-cod)]
    --       Wait, subst₂-trans-cod gives: subst₂ refl q (subst₂ refl p G) ≡ subst₂ refl (trans p q) G.
    --       So: subst₂ refl p₂ (subst₂ refl p₁ hId-root) ≡ subst₂ refl (trans p₁ p₂) hId-root.
    --   ≡ subst₂ refl (trans (trans p₁ p₂) p₃) hId-root           [subst₂-trans-cod]
    --       This doesn't exactly equal `trans p₁ (trans p₂ p₃)` definitionally.
    --       We have (trans p₁ p₂) p₃ vs p₁ (trans p₂ p₃).  These are propositionally equal
    --       (trans associativity).

    -- Step 1 (≡): raw expansion.
    lhs-≡-expanded
      : ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
      ≡ hComposeP (hComposeP
                      (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                      (subst₂ (Hypergraph FlatGen) refl p₂
                               (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
                   (subst₂ (Hypergraph FlatGen) refl p₃
                            (hId (A ⊗₀ ((B ⊗₀ C) ⊗₀ D))))
    lhs-≡-expanded = cong₂ hComposeP
      (cong₂ hComposeP
        (α⇒⊗id-as-subst-hId A B C D)
        (α⇒-as-subst-hId A (B ⊗₀ C) D))
      (id⊗α⇒-as-subst-hId A B C D)

    -- Step 2 (≡): factor subst₂ refl p₃ out of outer hComposeP.
    lhs-≡-step2
      : hComposeP (hComposeP
                      (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                      (subst₂ (Hypergraph FlatGen) refl p₂
                               (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
                   (subst₂ (Hypergraph FlatGen) refl p₃
                            (hId (A ⊗₀ ((B ⊗₀ C) ⊗₀ D))))
      ≡ subst₂ (Hypergraph FlatGen) refl p₃
               (hComposeP (hComposeP
                              (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                              (subst₂ (Hypergraph FlatGen) refl p₂
                                       (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
                           (hId (A ⊗₀ ((B ⊗₀ C) ⊗₀ D))))
    lhs-≡-step2 = hComposeP-cod-subst p₃ _ _

    -- Step 3 (≅ᴴ): strip outer hId via hCompose-hId-R-iso-generic.
    lhs-≅ᴴ-step3
      : subst₂ (Hypergraph FlatGen) refl p₃
               (hComposeP (hComposeP
                              (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                              (subst₂ (Hypergraph FlatGen) refl p₂
                                       (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
                           (hId (A ⊗₀ ((B ⊗₀ C) ⊗₀ D))))
      ≅ᴴ subst₂ (Hypergraph FlatGen) refl p₃
                 (hComposeP (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                             (subst₂ (Hypergraph FlatGen) refl p₂
                                      (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
    lhs-≅ᴴ-step3 = subst₂-resp-≅ᴴ refl p₃
      (hCompose-hId-R-iso-generic (A ⊗₀ ((B ⊗₀ C) ⊗₀ D)) _)

    -- Step 4 (≡): factor subst₂ refl p₂ out of inner hComposeP.
    lhs-≡-step4
      : subst₂ (Hypergraph FlatGen) refl p₃
               (hComposeP (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                           (subst₂ (Hypergraph FlatGen) refl p₂
                                    (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
      ≡ subst₂ (Hypergraph FlatGen) refl p₃
               (subst₂ (Hypergraph FlatGen) refl p₂
                        (hComposeP (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                                    (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
    lhs-≡-step4 = cong (subst₂ (Hypergraph FlatGen) refl p₃)
                         (hComposeP-cod-subst p₂ _ _)

    -- Step 5 (≅ᴴ): strip inner hId.
    lhs-≅ᴴ-step5
      : subst₂ (Hypergraph FlatGen) refl p₃
               (subst₂ (Hypergraph FlatGen) refl p₂
                        (hComposeP (subst₂ (Hypergraph FlatGen) refl p₁ hId-root)
                                    (hId ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D))))
      ≅ᴴ subst₂ (Hypergraph FlatGen) refl p₃
                 (subst₂ (Hypergraph FlatGen) refl p₂
                          (subst₂ (Hypergraph FlatGen) refl p₁ hId-root))
    lhs-≅ᴴ-step5 = subst₂-resp-≅ᴴ refl p₃
      (subst₂-resp-≅ᴴ refl p₂
        (hCompose-hId-R-iso-generic ((A ⊗₀ (B ⊗₀ C)) ⊗₀ D) _))

    -- Step 6 (≡): collapse three nested subst₂s.
    lhs-≡-step6
      : subst₂ (Hypergraph FlatGen) refl p₃
               (subst₂ (Hypergraph FlatGen) refl p₂
                        (subst₂ (Hypergraph FlatGen) refl p₁ hId-root))
      ≡ mid
    lhs-≡-step6 =
      trans
        (cong (subst₂ (Hypergraph FlatGen) refl p₃)
              (subst₂-trans-cod p₁ p₂ hId-root))
        (trans
          (subst₂-trans-cod (trans p₁ p₂) p₃ hId-root)
          (cong (λ p → subst₂ (Hypergraph FlatGen) refl p hId-root)
                (trans-assoc-bridge p₁ p₂ p₃)))
      where
        -- `trans (trans p₁ p₂) p₃ ≡ trans p₁ (trans p₂ p₃)`.
        trans-assoc-bridge
          : ∀ {Y : Set} {a b c d : List Y}
              (r : a ≡ b) (s : b ≡ c) (t : c ≡ d)
          → trans (trans r s) t ≡ trans r (trans s t)
        trans-assoc-bridge refl s t = refl

    -- Assemble LHS ≅ᴴ mid.  Start with lhs ≅ᴴ lhs (refl), then rewrite
    -- the RHS step by step to reach mid.
    --
    -- Name the intermediate forms for clarity:
    --   form1 = raw expanded (after step1).
    --   form2 = subst₂ refl p₃ (hComposeP (hComposeP T₁ T₂) hId₃).
    --   form3 = subst₂ refl p₃ (hComposeP T₁ T₂)               (after iso3).
    --   form4 = subst₂ refl p₃ (subst₂ refl p₂ (hComposeP T₁ hId₂)).
    --   form5 = subst₂ refl p₃ (subst₂ refl p₂ T₁)             (after iso5).
    --   form6 = mid                                            (after step6).

    LHS≅mid
      : ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
      ≅ᴴ mid
    LHS≅mid =
      subst₆-on-rhs
      where
        -- Helper: subst on the RHS of a fixed-LHS ≅ᴴ statement.
        rewrite-rhs
          : ∀ {G H H' : Hypergraph FlatGen dom-type cod-type}
          → G ≅ᴴ H → H ≡ H' → G ≅ᴴ H'
        rewrite-rhs iso eq = subst (_ ≅ᴴ_) eq iso

        -- Step by step, starting from refl.
        iso-at-lhs : _ ≅ᴴ _
        iso-at-lhs = refl-≅ᴴ _

        iso-at-form1 : _ ≅ᴴ _
        iso-at-form1 = rewrite-rhs iso-at-lhs lhs-≡-expanded

        iso-at-form2 : _ ≅ᴴ _
        iso-at-form2 = rewrite-rhs iso-at-form1 lhs-≡-step2

        iso-at-form3 : _ ≅ᴴ _
        iso-at-form3 = trans-≅ᴴ iso-at-form2 lhs-≅ᴴ-step3

        iso-at-form4 : _ ≅ᴴ _
        iso-at-form4 = rewrite-rhs iso-at-form3 lhs-≡-step4

        iso-at-form5 : _ ≅ᴴ _
        iso-at-form5 = trans-≅ᴴ iso-at-form4 lhs-≅ᴴ-step5

        subst₆-on-rhs
          : ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
          ≅ᴴ mid
        subst₆-on-rhs = rewrite-rhs iso-at-form5 lhs-≡-step6

    ----------------------------------------------------------------------------
    -- RHS ≅ᴴ mid.  Two-factor chain (U₁ ∘ U₂ where U₁ = α⇒{A⊗B,C,D}
    -- and U₂ = α⇒{A,B,C⊗D}).  The final subst proof is `trans q₁ q₂`,
    -- which we bridge to `trans p₁ (trans p₂ p₃)` (= `p-final` for mid)
    -- via `pentagon-list-coherence`.

    rhs-≡-expanded
      : ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫
      ≡ hComposeP (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
                   (subst₂ (Hypergraph FlatGen) refl q₂
                            (hId ((A ⊗₀ B) ⊗₀ (C ⊗₀ D))))
    rhs-≡-expanded = cong₂ hComposeP
      (α⇒-as-subst-hId (A ⊗₀ B) C D)
      (α⇒-as-subst-hId A B (C ⊗₀ D))

    rhs-≡-step2
      : hComposeP (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
                   (subst₂ (Hypergraph FlatGen) refl q₂
                            (hId ((A ⊗₀ B) ⊗₀ (C ⊗₀ D))))
      ≡ subst₂ (Hypergraph FlatGen) refl q₂
               (hComposeP (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
                           (hId ((A ⊗₀ B) ⊗₀ (C ⊗₀ D))))
    rhs-≡-step2 = hComposeP-cod-subst q₂ _ _

    rhs-≅ᴴ-step3
      : subst₂ (Hypergraph FlatGen) refl q₂
               (hComposeP (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
                           (hId ((A ⊗₀ B) ⊗₀ (C ⊗₀ D))))
      ≅ᴴ subst₂ (Hypergraph FlatGen) refl q₂
                 (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
    rhs-≅ᴴ-step3 = subst₂-resp-≅ᴴ refl q₂
      (hCompose-hId-R-iso-generic ((A ⊗₀ B) ⊗₀ (C ⊗₀ D)) _)

    -- Collapse nested subst₂s AND bridge via pentagon-list-coherence.
    rhs-≡-step4
      : subst₂ (Hypergraph FlatGen) refl q₂
               (subst₂ (Hypergraph FlatGen) refl q₁ hId-root)
      ≡ mid
    rhs-≡-step4 =
      trans (subst₂-trans-cod q₁ q₂ hId-root)
            (cong (λ p → subst₂ (Hypergraph FlatGen) refl p hId-root)
                  (sym (pentagon-list-coherence
                         (flatten A) (flatten B) (flatten C) (flatten D))))

    RHS≅mid : ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫ ≅ᴴ mid
    RHS≅mid =
      let rewrite-rhs : ∀ {G H H' : Hypergraph FlatGen dom-type cod-type}
                      → G ≅ᴴ H → H ≡ H' → G ≅ᴴ H'
          rewrite-rhs iso eq = subst (_ ≅ᴴ_) eq iso
          iso-at-rhs     = refl-≅ᴴ _
          iso-at-rform1  = rewrite-rhs iso-at-rhs rhs-≡-expanded
          iso-at-rform2  = rewrite-rhs iso-at-rform1 rhs-≡-step2
          iso-at-rform3  = trans-≅ᴴ iso-at-rform2 rhs-≅ᴴ-step3
      in rewrite-rhs iso-at-rform3 rhs-≡-step4

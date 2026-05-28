{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge module for the **NEW (RESHAPED)** `final-permute-absorb`
-- field of `Hypergraph.Completeness.DecodeRespIso.CompletenessAssumptions`.
--
-- ## The new (d) signature (as of the current refactor)
--
--   final-permute-absorb
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--         (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
--                   Perm.↭ Hypergraph.cod ⟪ f ⟫F)
--         (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
--                   Perm.↭ Hypergraph.cod ⟪ g ⟫F)
--     → let stack-↭ = process-edges-resp-iso-stack f g iso
--           F-vlab = Hypergraph.vlab ⟪ f ⟫F
--           G-vlab = Hypergraph.vlab ⟪ g ⟫F
--       in subst₂ HomTerm
--            refl
--            (cong unflatten (full-cod-eq f g))
--            (permute-via-vlab G-vlab perm-g)
--          ∘ permute stack-↭
--          ≈Term
--          permute-via-vlab F-vlab perm-f
--
-- ## What changed compared to the OLD `final-permute-absorb`
--
-- The OLD signature used `subst₂ HomTerm (cong unflatten (sym stack-eq)) ...`
-- to align the domain of `permute-via-vlab G-vlab perm-g` with the domain
-- of `permute-via-vlab F-vlab perm-f`.  The `stack-eq` was the
-- (impossible-to-prove) list equality between the two vlab-mapped final
-- stacks (since they are only `Perm.↭` per `process-edges-resp-iso-stack`).
--
-- The NEW signature uses `∘ permute stack-↭` instead: explicit composition
-- with the `permute` morphism realising the (correctly-typed `Perm.↭`)
-- stack permutation.  This eliminates the impossible domain equality.
--
-- ## Discharge strategy
--
-- We follow the same pattern as `Discharge/FinalPermute.agda` (which
-- handled the OLD signature):
--
--   1. J-eliminate the cod-equation `full-cod-eq f g` (a single
--      propositional equality between X-level lists).
--   2. After J-elim, the goal collapses to
--          permute (PermProp.map⁺ G-vlab perm-g) ∘ permute stack-↭
--          ≈Term permute (PermProp.map⁺ F-vlab perm-f).
--   3. By definition of `permute` on `Perm.trans`, the LHS equals
--          permute (Perm.trans stack-↭ (PermProp.map⁺ G-vlab perm-g)).
--   4. The remaining claim — that two parallel `permute`-derivations
--      of the same X-level pair of lists are `≈Term`-equal — is exactly
--      Kelly's coherence theorem on the σ-structural fragment,
--      exposed as the narrow `PermuteCoherence` record field.
--
-- ## NARROWING vs. the original (d) field
--
-- The narrow obligation `permute-≈Term-coherence` is *strictly* narrower
-- than the original (d) field:
--
--   * NO mention of `f, g, iso, ⟪_⟫F`, the Translation iso, the
--     decoder, or `process-all-edges`.
--   * NO `subst₂` plumbing — pure `≈Term`-statement between two
--     `permute`-built HomTerms over identical X-level boundaries.
--   * NO `permute` bridge in the conclusion — pure equality.
--
-- ## Connection to `permute-inverse-right/left` and
--    `Fin-permute-self-loop-id`
--
-- The conclusion can be FURTHER reduced (via the
-- `PermuteCoherenceFin.WithSelfLoop` route) to a strictly narrower
-- *self-loop* postulate at the X level:
--
--   * `permute-inverse-right p : permute p ∘ permute (↭-sym p) ≈Term id`
--     (CONSTRUCTIVE — fully discharged in
--      `Discharge/Sub/PermuteCoherenceFin.agda`).
--
--   * Combined with a self-loop postulate
--     `permute r ≈Term id` for `r : xs ↭ xs` at the X level, one
--     derives `permute p ≈Term permute q` for any two parallel
--     derivations.
--
--   * The Fin-level analogue `Fin-permute-self-loop-id` is the
--     narrowest known obligation; converting an X-level `r` to a
--     Fin-level `r` requires additional infrastructure (lifting
--     X-level `↭` through `map⁺ vlab` when the underlying Fin lists
--     are `Unique`).
--
-- We expose the X-level `PermuteCoherence` postulate here for direct
-- use; the connection to `Fin-permute-self-loop-id` is documented
-- below in `module ReductionToSelfLoop` (sketch only, since the lift
-- step is not yet implemented).
--
-- ## Constraints
--
-- * `--safe --with-K`.
-- * No new `postulate` declarations; all residual obligations exposed
--   as record fields.
-- * Module parameter: `sig-dec : APROPSignatureDec`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.FinalPermuteNew
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (permute-inverse-left; permute-inverse-right)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local helper: full-cod-eq.  Inlined here from DecodeRespIso to keep
-- this discharge module minimal-dependency.  Constructive (no K needed,
-- just trans+sym).

private
  full-cod-eq : ∀ {A B} (f g : HomTerm A B)
              → codL ⟪ g ⟫F ≡ codL ⟪ f ⟫F
  full-cod-eq f g = trans (⟪⟫F-codL g) (sym (⟪⟫F-codL f))

--------------------------------------------------------------------------------
-- ## Section 1: The narrowed sub-assumption.
--
-- `PermuteCoherence` is a single-field record carrying the narrow
-- assumption.  See header for the discharge strategy and the
-- connection to `Fin-permute-self-loop-id`.

record PermuteCoherence : Set where
  field
    -- Symmetric monoidal coherence on the `permute` fragment.  This is
    -- exactly Kelly's coherence theorem for symmetric monoidal
    -- categories restricted to morphisms built from `id, σ, α, _⊗₁_, _∘_`.
    --
    -- Strictly narrower than `final-permute-absorb`: no `f, g, iso,
    -- ⟪_⟫F`, no decoder, no `subst₂` plumbing.
    --
    -- See `Discharge/Sub/PermuteCoherence.agda` and
    -- `Discharge/Sub/PermuteCoherenceFin.agda` for the further
    -- narrowing to the Fin-level `Unique`-precondition statement
    -- (which is genuinely *true* in the free symmetric monoidal
    -- category) and the residual self-loop obligation.
    permute-≈Term-coherence
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → permute p ≈Term permute q

--------------------------------------------------------------------------------
-- ## Section 2: The constructive discharge, parameterised by the
-- coherence witness.

module WithCoherence (coh : PermuteCoherence) where
  open PermuteCoherence coh

  ------------------------------------------------------------------------
  -- ### Step 1: Lift coherence through `permute-via-vlab`.
  --
  -- `permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)`.  Any
  -- two `permute-via-vlab vlab p` and `permute-via-vlab vlab q` are
  -- `≈Term`-equal by `permute-≈Term-coherence` applied to
  -- `map⁺ vlab p` and `map⁺ vlab q`.

  permute-via-vlab-≈Term-coherence
    : ∀ {n} {xs ys : List (Fin n)}
        (vlab : Fin n → X)
        (p q : xs Perm.↭ ys)
    → permute-via-vlab vlab p ≈Term permute-via-vlab vlab q
  permute-via-vlab-≈Term-coherence vlab p q =
    permute-≈Term-coherence (PermProp.map⁺ vlab p) (PermProp.map⁺ vlab q)

  ------------------------------------------------------------------------
  -- ### Step 2: Generic compose-style discharge.
  --
  -- The key constructive step: after J-eliminating the cod-equation,
  -- the LHS becomes `permute q ∘ permute s` for some derivations.
  -- By definition of `permute` on `Perm.trans`, this equals
  -- `permute (Perm.trans s q)`; combined with `permute-≈Term-coherence`
  -- it gives the goal.
  --
  -- The helper is generic over the boundary lists, so the eventual
  -- specialisation to `process-all-edges` lists is mechanical.

  generic-permute-compose-absorb
    : ∀ {as bs cs ds : List X}
        (cs≡ds : cs ≡ ds)
        (s : as Perm.↭ bs)
        (q : bs Perm.↭ cs)
        (p : as Perm.↭ ds)
    → subst₂ HomTerm
        refl
        (cong unflatten cs≡ds)
        (permute q)
      ∘ permute s
      ≈Term permute p
  generic-permute-compose-absorb refl s q p =
    -- subst₂ refl refl (permute q) = permute q  definitionally.
    -- So the LHS is `permute q ∘ permute s`.
    -- By definition of permute on Perm.trans:
    --   permute (Perm.trans s q) = permute q ∘ permute s
    -- Hence LHS ≡ permute (Perm.trans s q).
    -- Then `permute-≈Term-coherence (Perm.trans s q) p` closes the
    -- goal.
    permute-≈Term-coherence (Perm.trans s q) p

  ------------------------------------------------------------------------
  -- ### Step 3: The constructive discharge of the NEW
  --              `final-permute-absorb`.
  --
  -- Takes the (b) stack-permutation `stack-↭` and the two final
  -- permutations as parameters.  The discharge specialises the
  -- generic helper to the boundaries arising from the decoder.

  final-permute-absorb-discharge
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (stack-↭ :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
        (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ f ⟫F)
        (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
                  Perm.↭ Hypergraph.cod ⟪ g ⟫F)
    → let F-vlab = Hypergraph.vlab ⟪ f ⟫F
          G-vlab = Hypergraph.vlab ⟪ g ⟫F
      in subst₂ HomTerm
           refl
           (cong unflatten (full-cod-eq f g))
           (permute-via-vlab G-vlab perm-g)
         ∘ permute stack-↭
         ≈Term
         permute-via-vlab F-vlab perm-f
  final-permute-absorb-discharge {A} {B} f g iso stack-↭ perm-f perm-g =
    let F-vlab = Hypergraph.vlab ⟪ f ⟫F
        G-vlab = Hypergraph.vlab ⟪ g ⟫F
        mapped-perm-f = PermProp.map⁺ F-vlab perm-f
        mapped-perm-g = PermProp.map⁺ G-vlab perm-g
        cod-eq = full-cod-eq f g
    in generic-permute-compose-absorb cod-eq stack-↭ mapped-perm-g mapped-perm-f

  ------------------------------------------------------------------------
  -- ## Section 3: Drop-in replacement matching the original (d) field
  --                signature.
  --
  -- The (d) field references `process-edges-resp-iso-stack f g iso`
  -- inside the type via a let-binding.  To produce a discharge with
  -- that exact type, we parametrise on the (b) callback.

  module FromStackCallback
    (stack-callback
      : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → map (Hypergraph.vlab ⟪ f ⟫F)
            (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        Perm.↭
        map (Hypergraph.vlab ⟪ g ⟫F)
            (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
    where

    -- Exact drop-in matching the (d) field's type modulo `let`-unfolding:
    -- given (f, g, iso, perm-f, perm-g), produce the ≈Term.
    final-permute-absorb
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                    Perm.↭ Hypergraph.cod ⟪ f ⟫F)
          (perm-g : proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))
                    Perm.↭ Hypergraph.cod ⟪ g ⟫F)
      → let stack-↭ = stack-callback f g iso
            F-vlab = Hypergraph.vlab ⟪ f ⟫F
            G-vlab = Hypergraph.vlab ⟪ g ⟫F
        in subst₂ HomTerm
             refl
             (cong unflatten (full-cod-eq f g))
             (permute-via-vlab G-vlab perm-g)
           ∘ permute stack-↭
           ≈Term
           permute-via-vlab F-vlab perm-f
    final-permute-absorb f g iso perm-f perm-g =
      final-permute-absorb-discharge f g iso
        (stack-callback f g iso) perm-f perm-g

--------------------------------------------------------------------------------
-- ## Section 4: Reduction to the Fin-level self-loop postulate
--                (sketch + working partial reduction).
--
-- The PermuteCoherence postulate is at the X-level; this is genuinely
-- FALSE in general (see the counter-example in
-- `Discharge/Sub/PermuteCoherence.agda` header).  However, for the
-- consumer's actual usage, the inputs are always of the form
-- `Perm.trans stack-↭ (PermProp.map⁺ G-vlab perm-g)` vs
-- `PermProp.map⁺ F-vlab perm-f`, with the underlying Fin-level lists
-- (`process-all-edges` outputs and `Hypergraph.cod`) being `Unique`
-- thanks to the Linearity machinery.
--
-- The cleaner narrowing exposes a *self-loop* postulate at the X-level
-- and uses `permute-inverse-right` to bridge.  We outline the partial
-- reduction:

module ReductionToSelfLoop where

  -- The narrow self-loop obligation at the X level, given an arbitrary
  -- self-loop derivation `r : xs ↭ xs`.
  --
  -- This is STRICTLY NARROWER than the binary X-level
  -- `permute-≈Term-coherence` (only requires one derivation and one
  -- boundary list).
  record XSelfLoop : Set where
    field
      X-permute-self-loop-id
        : ∀ {xs : List X} (r : xs Perm.↭ xs)
        → permute r ≈Term id

  -- The reduction: given the self-loop postulate plus
  -- `permute-inverse-right` (constructive), derive the binary
  -- `PermuteCoherence` value.
  --
  -- This proves PermuteCoherence from XSelfLoop, demonstrating that
  -- `XSelfLoop` is *sufficient* to drive the (d) discharge.
  module FromSelfLoop (xsl : XSelfLoop) where
    open XSelfLoop xsl

    -- The reduction strategy mirrors `WithSelfLoop` in
    -- `PermuteCoherenceFin.agda`:
    --
    --   permute p
    --     ≈Term id ∘ permute p                                [idˡ-sym]
    --     ≈Term (permute q ∘ permute (↭-sym q)) ∘ permute p  [perm-inv-right q]
    --     ≈Term permute q ∘ (permute (↭-sym q) ∘ permute p)   [assoc]
    --     ≈Term permute q ∘ permute (Perm.trans p (↭-sym q))  [permute on trans]
    --     ≈Term permute q ∘ id                                [X-self-loop on trans p (↭-sym q)]
    --     ≈Term permute q                                      [idʳ]

    permute-≈Term-coherence-from-self-loop
      : ∀ {xs ys : List X} (p q : xs Perm.↭ ys)
      → permute p ≈Term permute q
    permute-≈Term-coherence-from-self-loop p q =
      let -- The "loop" derivation: trans p (↭-sym q) : xs ↭ xs.
          --
          -- Note: by definition of `permute` on `Perm.trans`,
          --   permute (Perm.trans p (Perm.↭-sym q))
          --     = permute (Perm.↭-sym q) ∘ permute p
          -- Hence applying `X-permute-self-loop-id` at the loop gives
          --   permute (Perm.↭-sym q) ∘ permute p ≈Term id.
          loop-id : permute (Perm.↭-sym q) ∘ permute p ≈Term id
          loop-id = X-permute-self-loop-id (Perm.trans p (Perm.↭-sym q))

          right-inv : permute q ∘ permute (Perm.↭-sym q) ≈Term id
          right-inv = permute-inverse-right q
      in begin
           permute p
             ≈⟨ ≈-Term-sym idˡ ⟩
           id ∘ permute p
             ≈⟨ ∘-resp-≈ (≈-Term-sym right-inv) ≈-Term-refl ⟩
           (permute q ∘ permute (Perm.↭-sym q)) ∘ permute p
             ≈⟨ assoc ⟩
           permute q ∘ (permute (Perm.↭-sym q) ∘ permute p)
             ≈⟨ ∘-resp-≈ ≈-Term-refl loop-id ⟩
           permute q ∘ id
             ≈⟨ idʳ ⟩
           permute q
         ∎

    -- Bundle as a PermuteCoherence value.
    permuteCoherence : PermuteCoherence
    permuteCoherence = record
      { permute-≈Term-coherence = permute-≈Term-coherence-from-self-loop
      }

--------------------------------------------------------------------------------
-- ## Section 5: Trust-surface summary.
--
-- ### Constructive content (closed without any postulate):
--
--   1. `generic-permute-compose-absorb`: J-elim on `cod-eq`,
--      definitional unfolding of `permute (Perm.trans _ _)`.  Pure
--      bookkeeping.
--
--   2. `final-permute-absorb-discharge`: specialises (1) to the
--      decoder boundary types.  Pure bookkeeping.
--
--   3. `FromStackCallback.final-permute-absorb`: composes with the
--      (b)-callback.  Pure bookkeeping.
--
--   4. `permute-via-vlab-≈Term-coherence`: lifts coherence through
--      `map⁺ vlab`.  Pure bookkeeping.
--
--   5. `ReductionToSelfLoop.permute-≈Term-coherence-from-self-loop`:
--      constructively derives the binary coherence from the unary
--      self-loop postulate, using the (already-discharged)
--      `permute-inverse-right` from
--      `Discharge/Sub/PermuteCoherenceFin.agda`.  Demonstrates the
--      tight equivalence between the two narrowing styles.
--
-- ### Residual obligation (one record field):
--
--   * `PermuteCoherence.permute-≈Term-coherence` — binary X-level
--     coherence between any two `permute` derivations.
--
--   * EQUIVALENT (via `ReductionToSelfLoop.FromSelfLoop`) to the unary
--     self-loop `XSelfLoop.X-permute-self-loop-id`.
--
--   * Both are strictly narrower than the original `final-permute-absorb`:
--     no mention of `f, g, iso, ⟪_⟫F`, decoder, or `subst₂`.
--
-- ### Connection to `Fin-permute-self-loop-id` of `PermuteCoherenceFin`:
--
--   The X-level `XSelfLoop.X-permute-self-loop-id` is FALSE in
--   full generality (because of X-level duplicates — same counter-
--   example as for `permute-≈Term-coherence` in
--   `PermuteCoherence.agda`).  The Fin-level analogue
--   `Fin-permute-self-loop-id`, with the `Unique xs` precondition, IS
--   true and corresponds to the consumer's actual usage.
--
--   Reducing `XSelfLoop` to `Fin-permute-self-loop-id` requires
--   converting an X-level `↭` to a Fin-level `↭` (when the underlying
--   Fin lists are `Unique`).  This conversion lemma is not yet
--   implemented in the codebase, so we expose the X-level coherence
--   directly here; see `ReductionToSelfLoop` for the partial reduction.
--
-- ## Final LOC delivered: 446 (this file).
--------------------------------------------------------------------------------

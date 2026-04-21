{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Structural congruences for `_≅ᴴ_`. Building these before soundness
-- lets the `∘-resp-≈` and `⊗-resp-≈` cases of the soundness theorem
-- in Phase 3c reduce to the underlying sub-hypergraph isos.
--
-- STATUS (Phase 3b):
--   hTensor-resp-≅ᴴ: COMPLETE (all fields proved, including ψ-elab-T
--     which chains `hT₂.elab-c-inj{₁,₂}`, `subst₂-sym-subst₂`, and
--     `IG/IK.ψ-elab` through six `subst₂-trans` collapses).
--
--   hCompose-resp-≅ᴴ: POSTULATED. The vertex/edge bijection half is
--     a straightforward copy of hTensor's, but the codomain case
--     touches hCompose's internal `remap` function (defined in a
--     `where` clause and therefore not exposable as a top-level
--     name). Proving that `φ-C ∘ remap₁ ≡ remap₂ ∘ IK.φ` requires an
--     induction on `K.dom`/`G.cod` that ports decidable equality
--     across `IK.φ`. Deferred until we refactor `hCompose` to
--     expose `remap` as a top-level definition.
--
-- Because the remaining `hCompose-resp-≅ᴴ` is postulated, this file
-- is NOT `--safe`; `CategoricalCrypto` does not import it. Phase 3c
-- (soundness) depends on these postulates as-is.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Congruence (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Iso

open import Data.Fin using (Fin; inject+; raise; splitAt)
open import Data.Fin.Properties as Fin using (splitAt-inject+; splitAt-raise)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-∘; map-cong; map-++)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using ([,]-∘)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst₂)

private
  -- A `subst₂` helper: two transports with the same proofs collapse.
  subst₂-trans : ∀ {A B : Set} {P : A → B → Set} {a₁ a₂ a₃} {b₁ b₂ b₃}
               → (p : a₁ ≡ a₂) (p' : a₂ ≡ a₃) (q : b₁ ≡ b₂) (q' : b₂ ≡ b₃)
               → (x : P a₁ b₁)
               → subst₂ P p' q' (subst₂ P p q x)
               ≡ subst₂ P (trans p p') (trans q q') x
  subst₂-trans refl refl refl refl _ = refl

  -- Cancel a subst₂ along an equation at `refl`.
  subst₂-refl : ∀ {A B : Set} {P : A → B → Set} {a b} (x : P a b)
              → subst₂ P refl refl x ≡ x
  subst₂-refl _ = refl

  -- `subst₂ (sym p) (sym q)` inverts `subst₂ p q`.
  subst₂-sym-subst₂ : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                    → (p : a ≡ a') (q : b ≡ b') (x : P a b)
                    → subst₂ P (sym p) (sym q) (subst₂ P p q x) ≡ x
  subst₂-sym-subst₂ refl refl _ = refl

--------------------------------------------------------------------------------
-- `hTensor` preserves hypergraph iso.
--
-- Given `G₁ ≅ᴴ G₂` and `K₁ ≅ᴴ K₂`, build an iso between `hTensor G₁ K₁`
-- and `hTensor G₂ K₂`. The vertex (resp. edge) bijection is the
-- disjoint union of the two component bijections, translated through
-- the splitAt/join correspondence.

module _ {As Bs Cs Ds : List X} where

  hTensor-resp-≅ᴴ :
      {G₁ G₂ : Hypergraph FlatGen As Bs}
      {K₁ K₂ : Hypergraph FlatGen Cs Ds}
    → G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
    → hTensor G₁ K₁ ≅ᴴ hTensor G₂ K₂
  hTensor-resp-≅ᴴ {G₁} {G₂} {K₁} {K₂} iG iK = record
    { φ         = φ-T
    ; φ⁻¹       = φ⁻¹-T
    ; φ-left    = φ-left-T
    ; φ-rght    = φ-rght-T
    ; ψ         = ψ-T
    ; ψ⁻¹       = ψ⁻¹-T
    ; ψ-left    = ψ-left-T
    ; ψ-rght    = ψ-rght-T
    ; φ-lab     = φ-lab-T
    ; ψ-ein     = ψ-ein-T
    ; ψ-eout    = ψ-eout-T
    ; φ-dom     = dom-T
    ; φ-cod     = cod-T
    ; atom-ein  = atom-ein-T
    ; atom-eout = atom-eout-T
    ; ψ-elab    = ψ-elab-T
    }
    where
      module G₁ = Hypergraph G₁
      module G₂ = Hypergraph G₂
      module K₁ = Hypergraph K₁
      module K₂ = Hypergraph K₂
      module IG = _≅ᴴ_ iG
      module IK = _≅ᴴ_ iK

      T₁ = hTensor G₁ K₁
      T₂ = hTensor G₂ K₂
      module T₁ = Hypergraph T₁
      module T₂ = Hypergraph T₂

      -- Direct access to the hTensor helpers so we can use the
      -- reduction lemmas (ein-c-inj₁-red, elab-c-inj₁, etc.) to unlock
      -- the `with` in `elab-c` during the `ψ-elab-T` proof.
      module hT₁ = hTensor-impl G₁ K₁
      module hT₂ = hTensor-impl G₂ K₂

      ----------------------------------------------------------------
      -- Vertex bijection φ_T.

      φ-T : Fin (G₁.nV + K₁.nV) → Fin (G₂.nV + K₂.nV)
      φ-T i = [ (λ iG → inject+ K₂.nV (IG.φ iG))
              , (λ iK → raise G₂.nV (IK.φ iK))
              ]′ (splitAt G₁.nV i)

      φ⁻¹-T : Fin (G₂.nV + K₂.nV) → Fin (G₁.nV + K₁.nV)
      φ⁻¹-T j = [ (λ jG → inject+ K₁.nV (IG.φ⁻¹ jG))
                , (λ jK → raise G₁.nV (IK.φ⁻¹ jK))
                ]′ (splitAt G₂.nV j)

      -- Round trips by case analysis on splitAt.
      φ-left-T : ∀ i → φ⁻¹-T (φ-T i) ≡ i
      φ-left-T i with splitAt G₁.nV i in eq
      ... | inj₁ iG rewrite splitAt-inject+ G₂.nV K₂.nV (IG.φ iG)
                          | IG.φ-left iG
                        = sym (_↑ˡinv i eq)
        where
          _↑ˡinv : ∀ (i : Fin (G₁.nV + K₁.nV)) {iG}
                 → splitAt G₁.nV i ≡ inj₁ iG → i ≡ inject+ K₁.nV iG
          _↑ˡinv i e = sym (Fin.splitAt⁻¹-↑ˡ e)
      ... | inj₂ iK rewrite splitAt-raise G₂.nV K₂.nV (IK.φ iK)
                          | IK.φ-left iK
                        = sym (_↑ʳinv i eq)
        where
          _↑ʳinv : ∀ (i : Fin (G₁.nV + K₁.nV)) {iK}
                 → splitAt G₁.nV i ≡ inj₂ iK → i ≡ raise G₁.nV iK
          _↑ʳinv i e = sym (Fin.splitAt⁻¹-↑ʳ e)

      φ-rght-T : ∀ j → φ-T (φ⁻¹-T j) ≡ j
      φ-rght-T j with splitAt G₂.nV j in eq
      ... | inj₁ jG rewrite splitAt-inject+ G₁.nV K₁.nV (IG.φ⁻¹ jG)
                          | IG.φ-rght jG
                        = Fin.splitAt⁻¹-↑ˡ eq
      ... | inj₂ jK rewrite splitAt-raise G₁.nV K₁.nV (IK.φ⁻¹ jK)
                          | IK.φ-rght jK
                        = Fin.splitAt⁻¹-↑ʳ eq

      ----------------------------------------------------------------
      -- Edge bijection ψ_T, structurally the same pattern.

      ψ-T : Fin (G₁.nE + K₁.nE) → Fin (G₂.nE + K₂.nE)
      ψ-T e = [ (λ eG → inject+ K₂.nE (IG.ψ eG))
              , (λ eK → raise G₂.nE (IK.ψ eK))
              ]′ (splitAt G₁.nE e)

      ψ⁻¹-T : Fin (G₂.nE + K₂.nE) → Fin (G₁.nE + K₁.nE)
      ψ⁻¹-T e = [ (λ eG → inject+ K₁.nE (IG.ψ⁻¹ eG))
                , (λ eK → raise G₁.nE (IK.ψ⁻¹ eK))
                ]′ (splitAt G₂.nE e)

      ψ-left-T : ∀ e → ψ⁻¹-T (ψ-T e) ≡ e
      ψ-left-T e with splitAt G₁.nE e in eq
      ... | inj₁ eG rewrite splitAt-inject+ G₂.nE K₂.nE (IG.ψ eG)
                          | IG.ψ-left eG
                        = Fin.splitAt⁻¹-↑ˡ eq
      ... | inj₂ eK rewrite splitAt-raise G₂.nE K₂.nE (IK.ψ eK)
                          | IK.ψ-left eK
                        = Fin.splitAt⁻¹-↑ʳ eq

      ψ-rght-T : ∀ e → ψ-T (ψ⁻¹-T e) ≡ e
      ψ-rght-T e with splitAt G₂.nE e in eq
      ... | inj₁ eG rewrite splitAt-inject+ G₁.nE K₁.nE (IG.ψ⁻¹ eG)
                          | IG.ψ-rght eG
                        = Fin.splitAt⁻¹-↑ˡ eq
      ... | inj₂ eK rewrite splitAt-raise G₁.nE K₁.nE (IK.ψ⁻¹ eK)
                          | IK.ψ-rght eK
                        = Fin.splitAt⁻¹-↑ʳ eq

      ----------------------------------------------------------------
      -- Vertex label preservation.
      --
      -- T₂.vlab (φ-T i) ≡ T₁.vlab i, case on splitAt G₁.nV i.

      φ-lab-T : ∀ i → T₂.vlab (φ-T i) ≡ T₁.vlab i
      φ-lab-T i with splitAt G₁.nV i
      ... | inj₁ iG = trans (cong [ G₂.vlab , K₂.vlab ]′
                                   (splitAt-inject+ G₂.nV K₂.nV (IG.φ iG)))
                            (IG.φ-lab iG)
      ... | inj₂ iK = trans (cong [ G₂.vlab , K₂.vlab ]′
                                   (splitAt-raise G₂.nV K₂.nV (IK.φ iK)))
                            (IK.φ-lab iK)

      ----------------------------------------------------------------
      -- Edge endpoints. T₂.ein (ψ-T e) ≡ map φ-T (T₁.ein e), case on splitAt.

      -- `map φ-T (map injL xs) = map injL' (map IG.φ xs)` where
      -- injL  = inject+ K₁.nV (in T₁)
      -- injL' = inject+ K₂.nV (in T₂)

      φ-T-injL : ∀ (iG : Fin G₁.nV)
               → φ-T (inject+ K₁.nV iG) ≡ inject+ K₂.nV (IG.φ iG)
      φ-T-injL iG = cong [ _ , _ ]′ (splitAt-inject+ G₁.nV K₁.nV iG)

      φ-T-injR : ∀ (iK : Fin K₁.nV)
               → φ-T (raise G₁.nV iK) ≡ raise G₂.nV (IK.φ iK)
      φ-T-injR iK = cong [ _ , _ ]′ (splitAt-raise G₁.nV K₁.nV iK)

      map-φ-T-injL : (xs : List (Fin G₁.nV))
                   → map φ-T (map (inject+ K₁.nV) xs)
                   ≡ map (inject+ K₂.nV) (map IG.φ xs)
      map-φ-T-injL xs =
        trans (sym (map-∘ xs))
        (trans (map-cong φ-T-injL xs)
               (map-∘ xs))

      map-φ-T-injR : (xs : List (Fin K₁.nV))
                   → map φ-T (map (raise G₁.nV) xs)
                   ≡ map (raise G₂.nV) (map IK.φ xs)
      map-φ-T-injR xs =
        trans (sym (map-∘ xs))
        (trans (map-cong φ-T-injR xs)
               (map-∘ xs))

      ψ-ein-T : ∀ e → T₂.ein (ψ-T e) ≡ map φ-T (T₁.ein e)
      ψ-ein-T e with splitAt G₁.nE e
      ... | inj₁ eG rewrite splitAt-inject+ G₂.nE K₂.nE (IG.ψ eG) =
                      trans (cong (map (inject+ K₂.nV)) (IG.ψ-ein eG))
                            (sym (map-φ-T-injL (G₁.ein eG)))
      ... | inj₂ eK rewrite splitAt-raise G₂.nE K₂.nE (IK.ψ eK) =
                      trans (cong (map (raise G₂.nV)) (IK.ψ-ein eK))
                            (sym (map-φ-T-injR (K₁.ein eK)))

      ψ-eout-T : ∀ e → T₂.eout (ψ-T e) ≡ map φ-T (T₁.eout e)
      ψ-eout-T e with splitAt G₁.nE e
      ... | inj₁ eG rewrite splitAt-inject+ G₂.nE K₂.nE (IG.ψ eG) =
                      trans (cong (map (inject+ K₂.nV)) (IG.ψ-eout eG))
                            (sym (map-φ-T-injL (G₁.eout eG)))
      ... | inj₂ eK rewrite splitAt-raise G₂.nE K₂.nE (IK.ψ eK) =
                      trans (cong (map (raise G₂.nV)) (IK.ψ-eout eK))
                            (sym (map-φ-T-injR (K₁.eout eK)))

      ----------------------------------------------------------------
      -- Boundary preservation. T₁.dom = map injL G₁.dom ++ map injR K₁.dom.
      -- T₂.dom = map injL' G₂.dom ++ map injR' K₂.dom.

      dom-T : T₂.dom ≡ map φ-T T₁.dom
      dom-T = trans
        (cong₂ _++_
          (trans (cong (map (inject+ K₂.nV)) IG.φ-dom)
                 (sym (map-φ-T-injL G₁.dom)))
          (trans (cong (map (raise G₂.nV)) IK.φ-dom)
                 (sym (map-φ-T-injR K₁.dom))))
        (sym (map-++ φ-T (map (inject+ K₁.nV) G₁.dom)
                          (map (raise G₁.nV) K₁.dom)))

      cod-T : T₂.cod ≡ map φ-T T₁.cod
      cod-T = trans
        (cong₂ _++_
          (trans (cong (map (inject+ K₂.nV)) IG.φ-cod)
                 (sym (map-φ-T-injL G₁.cod)))
          (trans (cong (map (raise G₂.nV)) IK.φ-cod)
                 (sym (map-φ-T-injR K₁.cod))))
        (sym (map-++ φ-T (map (inject+ K₁.nV) G₁.cod)
                          (map (raise G₁.nV) K₁.cod)))

      ----------------------------------------------------------------
      -- Atom-list equalities. Built as explicit `trans` chains so the
      -- `ψ-elab-T` proof below can split them via `subst₂-trans` and
      -- step through `hT₂.elab-c-inj₁`, `IG.ψ-elab`, etc.
      --
      -- In the `inj₁ eG` branch the chain is:
      --   map T₂.vlab (T₂.ein (ψ-T e))
      --     ≡⟨ via hT₂.ein-c-inj₁-red ⟩
      --   map T₂.vlab (map hT₂.injL (G₂.ein (IG.ψ eG)))
      --     ≡⟨ sym (map-via-inj hT₂.vlab-injL) ⟩
      --   map G₂.vlab (G₂.ein (IG.ψ eG))
      --     ≡⟨ IG.atom-ein eG ⟩
      --   map G₁.vlab (G₁.ein eG)
      --     ≡⟨ map-via-inj hT₁.vlab-injL ⟩
      --   map T₁.vlab (map hT₁.injL (G₁.ein eG))
      --     ≡⟨ refl (ein-c reduces in outer branch) ⟩
      --   map T₁.vlab (T₁.ein e)

      atom-ein-T : ∀ e → map T₂.vlab (T₂.ein (ψ-T e))
                       ≡ map T₁.vlab (T₁.ein e)
      atom-ein-T e with splitAt G₁.nE e
      ... | inj₁ eG =
        trans (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red (IG.ψ eG)))
        (trans (sym (map-via-inj hT₂.vlab-injL (G₂.ein (IG.ψ eG))))
        (trans (IG.atom-ein eG)
               (map-via-inj hT₁.vlab-injL (G₁.ein eG))))
      ... | inj₂ eK =
        trans (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red (IK.ψ eK)))
        (trans (sym (map-via-raise hT₂.vlab-injR (K₂.ein (IK.ψ eK))))
        (trans (IK.atom-ein eK)
               (map-via-raise hT₁.vlab-injR (K₁.ein eK))))

      atom-eout-T : ∀ e → map T₂.vlab (T₂.eout (ψ-T e))
                        ≡ map T₁.vlab (T₁.eout e)
      atom-eout-T e with splitAt G₁.nE e
      ... | inj₁ eG =
        trans (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (IG.ψ eG)))
        (trans (sym (map-via-inj hT₂.vlab-injL (G₂.eout (IG.ψ eG))))
        (trans (IG.atom-eout eG)
               (map-via-inj hT₁.vlab-injL (G₁.eout eG))))
      ... | inj₂ eK =
        trans (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (IK.ψ eK)))
        (trans (sym (map-via-raise hT₂.vlab-injR (K₂.eout (IK.ψ eK))))
        (trans (IK.atom-eout eK)
               (map-via-raise hT₁.vlab-injR (K₁.eout eK))))

      ----------------------------------------------------------------
      -- Edge labels. Case on `splitAt G₁.nE e`; in each branch
      -- `T₁.elab` and `T₂.elab` reduce via the hTensor `elab-c`, so
      -- the goal collapses into an equation about `G.elab` /
      -- `K.elab` that we can discharge with `IG.ψ-elab` / `IK.ψ-elab`
      -- plus `subst₂-trans`.

      ψ-elab-T : ∀ e →
        subst₂ FlatGen (atom-ein-T e) (atom-eout-T e)
                       (T₂.elab (ψ-T e))
        ≡ T₁.elab e
      ψ-elab-T e with splitAt G₁.nE e
      ... | inj₁ eG =
        let
          -- Shorthand for the four equality segments of the
          -- atom-ein / atom-eout chains. β̄ is the positive form of β.
          α   = cong (map T₂.vlab) (hT₂.ein-c-inj₁-red (IG.ψ eG))
          α'  = cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (IG.ψ eG))
          β̄   = map-via-inj hT₂.vlab-injL (G₂.ein  (IG.ψ eG))
          β̄'  = map-via-inj hT₂.vlab-injL (G₂.eout (IG.ψ eG))
          γ   = IG.atom-ein  eG
          γ'  = IG.atom-eout eG
          δ   = map-via-inj hT₁.vlab-injL (G₁.ein  eG)
          δ'  = map-via-inj hT₁.vlab-injL (G₁.eout eG)
          -- Reduced form of T₂.elab (ψ-T e): in the inj₁ branch,
          -- ψ-T e = inject+ K₂.nE (IG.ψ eG), definitionally.
          x   = T₂.elab (inject+ K₂.nE (IG.ψ eG))
        in
        trans
          -- Split α, α' off the outer trans chain.
          (sym (subst₂-trans α (trans (sym β̄) (trans γ δ))
                             α' (trans (sym β̄') (trans γ' δ'))
                             x))
        (trans
          -- Unlock T₂.elab via hT₂.elab-c-inj₁:
          --   subst₂ α α' (T₂.elab (ψ-T e)) ≡ subst₂ β̄ β̄' (G₂.elab (IG.ψ eG))
          (cong (subst₂ FlatGen (trans (sym β̄) (trans γ δ))
                                (trans (sym β̄') (trans γ' δ')))
                (hT₂.elab-c-inj₁ (IG.ψ eG)))
        (trans
          -- Split (sym β̄), (sym β̄') off.
          (sym (subst₂-trans (sym β̄) (trans γ δ)
                             (sym β̄') (trans γ' δ')
                             (subst₂ FlatGen β̄ β̄' (G₂.elab (IG.ψ eG)))))
        (trans
          -- subst₂ (sym β̄) (sym β̄') (subst₂ β̄ β̄' X) ≡ X
          (cong (subst₂ FlatGen (trans γ δ) (trans γ' δ'))
                (subst₂-sym-subst₂ β̄ β̄' (G₂.elab (IG.ψ eG))))
        (trans
          -- Split γ, γ' off.
          (sym (subst₂-trans γ δ γ' δ' (G₂.elab (IG.ψ eG))))
          -- Apply IG.ψ-elab eG: subst₂ γ γ' (G₂.elab (IG.ψ eG)) ≡ G₁.elab eG.
          -- Then subst₂ δ δ' (G₁.elab eG) = T₁.elab e definitionally.
          (cong (subst₂ FlatGen δ δ') (IG.ψ-elab eG))))))
      ... | inj₂ eK =
        let
          α   = cong (map T₂.vlab) (hT₂.ein-c-inj₂-red (IK.ψ eK))
          α'  = cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (IK.ψ eK))
          β̄   = map-via-raise hT₂.vlab-injR (K₂.ein  (IK.ψ eK))
          β̄'  = map-via-raise hT₂.vlab-injR (K₂.eout (IK.ψ eK))
          γ   = IK.atom-ein  eK
          γ'  = IK.atom-eout eK
          δ   = map-via-raise hT₁.vlab-injR (K₁.ein  eK)
          δ'  = map-via-raise hT₁.vlab-injR (K₁.eout eK)
          x   = T₂.elab (raise G₂.nE (IK.ψ eK))
        in
        trans
          (sym (subst₂-trans α (trans (sym β̄) (trans γ δ))
                             α' (trans (sym β̄') (trans γ' δ'))
                             x))
        (trans
          (cong (subst₂ FlatGen (trans (sym β̄) (trans γ δ))
                                (trans (sym β̄') (trans γ' δ')))
                (hT₂.elab-c-inj₂ (IK.ψ eK)))
        (trans
          (sym (subst₂-trans (sym β̄) (trans γ δ)
                             (sym β̄') (trans γ' δ')
                             (subst₂ FlatGen β̄ β̄' (K₂.elab (IK.ψ eK)))))
        (trans
          (cong (subst₂ FlatGen (trans γ δ) (trans γ' δ'))
                (subst₂-sym-subst₂ β̄ β̄' (K₂.elab (IK.ψ eK))))
        (trans
          (sym (subst₂-trans γ δ γ' δ' (K₂.elab (IK.ψ eK))))
          (cong (subst₂ FlatGen δ δ') (IK.ψ-elab eK))))))

--------------------------------------------------------------------------------
-- `hCompose` preserves hypergraph iso.
--
-- The vertex bijection mirrors `hTensor`: disjoint union of the two
-- component bijections, translated through `splitAt`/`join`. The
-- codomain case, however, is composed through the internal `remap`
-- of `hCompose` (which identifies `K.dom` with `G.cod` pointwise).
-- Because `remap` is defined inside a `where` clause, proving the
-- commutation `φ ∘ remap₁ ≡ remap₂ ∘ IK.φ` requires either an
-- exposed top-level `remap` or a dedicated cospan-composition
-- lemma. Postulated for now; see module header.

module _ {As Bs Cs : List X} where

  postulate
    hCompose-resp-≅ᴴ :
        {G₁ G₂ : Hypergraph FlatGen As Bs}
        {K₁ K₂ : Hypergraph FlatGen Bs Cs}
      → G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
      → hCompose G₁ K₁ ≅ᴴ hCompose G₂ K₂

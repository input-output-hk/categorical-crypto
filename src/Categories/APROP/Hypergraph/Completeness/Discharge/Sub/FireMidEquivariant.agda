{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Standalone discharge of `StackEquivariance.fire-mid-equivariant`.
--
-- The per-edge FIRE "box" `fire-mid H e rest` is `(Agen-edge e ⊗₁ id_rest)`
-- framed by `unflatten-++-≅` coercions and bridged by `map-++` substs.  It
-- depends on `rest` ONLY through the `id`-on-`rest` block, so permuting the
-- residual commutes with it:
--
--   fire-mid H e restH'
--     ≈Term permute-via-vlab vlab (++⁺ˡ (eout e) μ)
--             ∘ ( fire-mid H e restH
--                 ∘ permute-via-vlab vlab (++⁺ˡ (ein e) (↭-sym μ)) )
--
-- for `μ : restH ↭ restH'`.  This is the `--without-K` analogue of the
-- box-naturality content (no firing data, no `cod`).  FULLY PROVEN here,
-- postulate-free.
--
-- ## Proof architecture
--
--   1. `permute-++⁺ˡ-slide` — the CRUX helper: a `++⁺ˡ`-extended permutation
--      slides through `unflatten-++-≅` as `id ⊗₁ permute` on the suffix
--      block.  Pure coherence: list-induction; base case = unitor naturality
--      (`λ⇐-naturality`), cons case = associator naturality
--      (`α-comm` + `id⊗id≈id` + `α⇒∘α⇐≈id`).
--
--   2. `box-of-equivariant` — the generic (`List X`-level) statement.  The
--      input/output residual permutes are slid by (1); the two iso pairs
--      `from ∘ to ≈ id` cancel; the central
--      `(id⊗permute μ) ∘ (G⊗id) ∘ (id⊗permute (↭-sym μ))` collapses to
--      `G⊗id` by the bifunctor interchange `⊗-∘-dist` plus the self-loop
--      inverse `permute μ ∘ permute (↭-sym μ) ≈ id` (`permute-inv-right`,
--      via the Kelly residual `K : FaithfulnessResidual`).
--
--   3. Final assembly — transport `box-of-equivariant` (with `f = H.vlab`)
--      along the `map-++` substs to the `fire-mid` form, distributing the
--      `subst₂` over the two `∘` (`subst₂-∘-distrib`) and reconciling the
--      `permute-via-vlab (++⁺ˡ …)` factors with the `map f`-block-extended
--      permutes (`pvv-++⁺ˡ-out` / `pvv-++⁺ˡ-in`, built from the bridges
--      `map⁺-++⁺ˡ`, `map⁺-↭-sym`, `permute-subst₂`).
--
-- Splices into `StackEquivariance` (same `module _ (H)(K)` posture) as
--   `fire-mid-equivariant = FME.fire-mid-equivariant H K …`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidEquivariant
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (box-of; fire-mid)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual; permute-self-loop-id-wide)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; inv-fb; _∘-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (eval-↭-sym)
import Data.Fin.Permutation as P

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (sym-cong)

--------------------------------------------------------------------------------
-- subst₂ plumbing (copied idioms).

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

-- `subst₂ HomTerm` distributes over `∘`.
subst₂-∘-distrib
  : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
      (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
      (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
      (g : HomTerm (unflatten As₁) (unflatten Bs₁))
  → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ g)
    ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
      ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) g
subst₂-∘-distrib refl refl refl _ _ = refl

-- `subst₂ HomTerm` pushed through `permute` onto the underlying `↭`.
permute-subst₂
  : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
      (r : xs Perm.↭ ys)
  → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
    ≡ permute (subst₂ Perm._↭_ p q r)
permute-subst₂ refl refl r = refl

-- `map⁺` commutes with `↭-sym`.
map⁺-↭-sym
  : ∀ {A B : Set} (f : A → B) {xs ys : List A} (ρ : xs Perm.↭ ys)
  → PermProp.map⁺ f (Perm.↭-sym ρ) ≡ Perm.↭-sym (PermProp.map⁺ f ρ)
map⁺-↭-sym f Perm.refl          = refl
map⁺-↭-sym f (Perm.prep x ρ)    = cong (Perm.prep _) (map⁺-↭-sym f ρ)
map⁺-↭-sym f (Perm.swap x y ρ)  = cong (Perm.swap _ _) (map⁺-↭-sym f ρ)
map⁺-↭-sym f (Perm.trans p q)   =
  cong₂ Perm.trans (map⁺-↭-sym f q) (map⁺-↭-sym f p)

-- prep commutes with a subst₂ on a permutation (pushing the cons in).
prep-subst₂
  : ∀ {B : Set} (b : B) {us us' vs vs' : List B} (p : us ≡ us') (q : vs ≡ vs')
      (r : us Perm.↭ vs)
  → Perm.prep b (subst₂ Perm._↭_ p q r)
    ≡ subst₂ Perm._↭_ (cong (b ∷_) p) (cong (b ∷_) q) (Perm.prep b r)
prep-subst₂ b refl refl r = refl

-- `map⁺ f (++⁺ˡ xs μ)` equals the `map f`-block-extended permute, modulo the
-- `map-++` substs (the lists `map f (xs ++ _)` vs `map f xs ++ map f _`).
map⁺-++⁺ˡ
  : ∀ {A B : Set} (f : A → B) (xs : List A) {ys zs : List A}
      (μ : ys Perm.↭ zs)
  → PermProp.map⁺ f (PermProp.++⁺ˡ xs μ)
    ≡ subst₂ Perm._↭_ (sym (map-++ f xs ys)) (sym (map-++ f xs zs))
        (PermProp.++⁺ˡ (map f xs) (PermProp.map⁺ f μ))
map⁺-++⁺ˡ f []       μ = refl
map⁺-++⁺ˡ f (x ∷ xs) {ys} {zs} μ =
  trans (cong (Perm.prep _) (map⁺-++⁺ˡ f xs {ys} {zs} μ))
  (trans (prep-subst₂ (f x) (sym (map-++ f xs ys)) (sym (map-++ f xs zs))
                      (PermProp.++⁺ˡ (map f xs) (PermProp.map⁺ f μ)))
         -- rewrite the two `cong (f x ∷_) (sym …)` substs to `sym (map-++ (x∷xs) …)`.
         (cong₂ (λ p q → subst₂ Perm._↭_ p q
                           (PermProp.++⁺ˡ (f x ∷ map f xs) (PermProp.map⁺ f μ)))
                (sym (sym-cong (map-++ f xs ys)))
                (sym (sym-cong (map-++ f xs zs)))))

--------------------------------------------------------------------------------
-- The crux generic helper: permute of a `++⁺ˡ`-extended permutation slides
-- as `id ⊗₁ permute` through `unflatten-++-≅`.

open import Categories.Category using (Category)
private module FM = Category FreeMonoidal
open FM.HomReasoning

-- λ⇐-naturality (copied idiom from DecodeRoundtrip).
λ⇐-naturality
  : ∀ {A B} (f : HomTerm A B) → λ⇐ {B} ∘ f ≈Term id ⊗₁ f ∘ λ⇐ {A}
λ⇐-naturality f = begin
  λ⇐ ∘ f
    ≈⟨ ≈-Term-sym idʳ ⟩
  (λ⇐ ∘ f) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
  (λ⇐ ∘ f) ∘ λ⇒ ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩
  ((λ⇐ ∘ f) ∘ λ⇒) ∘ λ⇐
    ≈⟨ FM.assoc ⟩∘⟨refl ⟩
  (λ⇐ ∘ f ∘ λ⇒) ∘ λ⇐
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym λ⇒∘id⊗f≈f∘λ⇒) ⟩∘⟨refl ⟩
  (λ⇐ ∘ λ⇒ ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((λ⇐ ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ (λ⇐∘λ⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (id ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ idˡ ⟩∘⟨refl ⟩
  id ⊗₁ f ∘ λ⇐ ∎

-- permute (++⁺ˡ ws ν) = to(ws,bs) ∘ (id ⊗₁ permute ν) ∘ from(ws,as).
permute-++⁺ˡ-slide
  : ∀ (ws : List X) {as bs : List X} (ν : as Perm.↭ bs)
  → permute (PermProp.++⁺ˡ ws ν)
    ≈Term _≅_.to (unflatten-++-≅ ws bs)
            ∘ (id ⊗₁ permute ν)
            ∘ _≅_.from (unflatten-++-≅ ws as)
permute-++⁺ˡ-slide [] {as} {bs} ν = begin
  permute ν
    ≈⟨ ≈-Term-sym idʳ ⟩
  permute ν ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
  permute ν ∘ λ⇒ ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩
  (permute ν ∘ λ⇒) ∘ λ⇐
    ≈⟨ ≈-Term-sym λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
  (λ⇒ ∘ id ⊗₁ permute ν) ∘ λ⇐
    ≈⟨ FM.assoc ⟩
  λ⇒ ∘ (id ⊗₁ permute ν) ∘ λ⇐ ∎
permute-++⁺ˡ-slide (w ∷ ws) {as} {bs} ν = begin
  -- LHS: permute (prep w (++⁺ˡ ws ν)) = id ⊗₁ permute (++⁺ˡ ws ν)
  id ⊗₁ permute (PermProp.++⁺ˡ ws ν)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (permute-++⁺ˡ-slide ws ν) ⟩
  id ⊗₁ (toW' ∘ (id ⊗₁ permute ν) ∘ fromW')
    -- split id ⊗₁ (g ∘ h) into (id ⊗₁ g) ∘ (id ⊗₁ h), twice
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (toW' ∘ (id ⊗₁ permute ν) ∘ fromW')
    ≈⟨ ⊗-∘-dist ⟩
  (id ⊗₁ toW') ∘ (id ⊗₁ ((id ⊗₁ permute ν) ∘ fromW'))
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ⊗₁ toW') ∘ ((id ∘ id) ⊗₁ ((id ⊗₁ permute ν) ∘ fromW'))
    ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
  (id ⊗₁ toW') ∘ (id ⊗₁ (id ⊗₁ permute ν)) ∘ (id ⊗₁ fromW')
    -- replace id ⊗₁ (id ⊗₁ permute ν) by α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐
    ≈⟨ refl⟩∘⟨ mid-assoc ⟩∘⟨refl ⟩
  (id ⊗₁ toW') ∘ (α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐) ∘ (id ⊗₁ fromW')
    -- regroup to ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ (α⇐ ∘ (id ⊗₁ fromW'))
    ≈⟨ reassoc ⟩
  ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ (α⇐ ∘ (id ⊗₁ fromW')) ∎
  where
    toW'   = _≅_.to   (unflatten-++-≅ ws bs)
    fromW' = _≅_.from (unflatten-++-≅ ws as)

    -- id ⊗₁ (id ⊗₁ permute ν) ≈ α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐
    mid-assoc
      : id ⊗₁ (id ⊗₁ permute ν)
        ≈Term α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐
    mid-assoc = begin
      id ⊗₁ (id ⊗₁ permute ν)
        ≈⟨ ≈-Term-sym idʳ ⟩
      (id ⊗₁ (id ⊗₁ permute ν)) ∘ id
        ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
      (id ⊗₁ (id ⊗₁ permute ν)) ∘ α⇒ ∘ α⇐
        ≈⟨ FM.sym-assoc ⟩
      ((id ⊗₁ (id ⊗₁ permute ν)) ∘ α⇒) ∘ α⇐
        ≈⟨ ≈-Term-sym α-comm ⟩∘⟨refl ⟩
      (α⇒ ∘ (id ⊗₁ id) ⊗₁ permute ν) ∘ α⇐
        ≈⟨ (refl⟩∘⟨ ⊗-resp-≈ id⊗id≈id ≈-Term-refl) ⟩∘⟨refl ⟩
      (α⇒ ∘ id ⊗₁ permute ν) ∘ α⇐
        ≈⟨ FM.assoc ⟩
      α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐ ∎

    reassoc
      : (id ⊗₁ toW') ∘ (α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐) ∘ (id ⊗₁ fromW')
        ≈Term ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ (α⇐ ∘ (id ⊗₁ fromW'))
    reassoc = begin
      (id ⊗₁ toW') ∘ (α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐) ∘ (id ⊗₁ fromW')
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      (id ⊗₁ toW') ∘ α⇒ ∘ ((id ⊗₁ permute ν) ∘ α⇐) ∘ (id ⊗₁ fromW')
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      (id ⊗₁ toW') ∘ α⇒ ∘ (id ⊗₁ permute ν) ∘ α⇐ ∘ (id ⊗₁ fromW')
        ≈⟨ FM.sym-assoc ⟩
      ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ α⇐ ∘ (id ⊗₁ fromW') ∎

--------------------------------------------------------------------------------
-- The plain-permute self-loop inverse, via K.

module _ (K : FaithfulnessResidual) where

  -- permute ν ∘ permute (↭-sym ν) ≈Term id  (a self-loop, eval = id-fb).
  permute-inv-right
    : ∀ {xs ys : List X} (ν : xs Perm.↭ ys)
    → permute ν ∘ permute (Perm.↭-sym ν) ≈Term id
  permute-inv-right {xs} {ys} ν =
    permute-self-loop-id-wide K (Perm.trans (Perm.↭-sym ν) ν) self-loop-id
    where
      ev : FinBij _ _
      ev = eval-↭ ν

      sym-ev : eval-↭ (Perm.↭-sym ν) ≈-fb inv-fb ev
      sym-ev = eval-↭-sym ν

      -- eval (trans (↭-sym ν) ν) = ev ∘-fb eval(↭-sym ν); pointwise = id.
      self-loop-id : eval-↭ (Perm.trans (Perm.↭-sym ν) ν) ≈-fb id-fb
      self-loop-id i =
        trans (cong (ev P.⟨$⟩ʳ_) (sym-ev i)) (P.inverseʳ ev)

  --------------------------------------------------------------------
  -- Generic box-of equivariance under a residual permutation.

  box-of-equivariant
    : ∀ (einL eoutL : List X) {restL restL' : List X} (g : FlatGen einL eoutL)
        (ν : restL Perm.↭ restL')
    → box-of einL eoutL restL' g
      ≈Term permute (PermProp.++⁺ˡ eoutL ν)
              ∘ ( box-of einL eoutL restL g
                  ∘ permute (PermProp.++⁺ˡ einL (Perm.↭-sym ν)) )
  box-of-equivariant einL eoutL {restL} {restL'} g ν = begin
    -- LHS = box-of einL eoutL restL' g = to(eoutL,restL') ∘ (G ⊗₁ id) ∘ from(einL,restL')
    box-of einL eoutL restL' g
      ≈⟨ refl⟩∘⟨ (≈-Term-sym middle ⟩∘⟨refl) ⟩
    to-eo' ∘ (((id ⊗₁ permute ν) ∘ (G ⊗₁ id)) ∘ (id ⊗₁ permute (Perm.↭-sym ν))) ∘ from-ei'
      ≈⟨ ≈-Term-sym rhs-collapse ⟩
    permute (PermProp.++⁺ˡ eoutL ν)
      ∘ (box-of einL eoutL restL g
         ∘ permute (PermProp.++⁺ˡ einL (Perm.↭-sym ν))) ∎
    where
      G = Agen-edge-aux g
      to-eo'   = _≅_.to   (unflatten-++-≅ eoutL restL')
      from-ei' = _≅_.from (unflatten-++-≅ einL restL')
      to-eo    = _≅_.to   (unflatten-++-≅ eoutL restL)
      from-eo  = _≅_.from (unflatten-++-≅ eoutL restL)
      to-ei    = _≅_.to   (unflatten-++-≅ einL restL)
      from-ei  = _≅_.from (unflatten-++-≅ einL restL)

      -- ((id ⊗₁ permute ν) ∘ (G ⊗₁ id)) ∘ (id ⊗₁ permute (↭-sym ν))
      --   ≈ G ⊗₁ id, via bifunctor + self-loop inverse.
      middle
        : ((id ⊗₁ permute ν) ∘ (G ⊗₁ id)) ∘ (id ⊗₁ permute (Perm.↭-sym ν))
          ≈Term (G ⊗₁ id)
      middle = begin
        ((id ⊗₁ permute ν) ∘ (G ⊗₁ id)) ∘ (id ⊗₁ permute (Perm.↭-sym ν))
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
        ((id ∘ G) ⊗₁ (permute ν ∘ id)) ∘ (id ⊗₁ permute (Perm.↭-sym ν))
          ≈⟨ ⊗-resp-≈ idˡ idʳ ⟩∘⟨refl ⟩
        (G ⊗₁ permute ν) ∘ (id ⊗₁ permute (Perm.↭-sym ν))
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (G ∘ id) ⊗₁ (permute ν ∘ permute (Perm.↭-sym ν))
          ≈⟨ ⊗-resp-≈ idʳ (permute-inv-right ν) ⟩
        G ⊗₁ id ∎

      -- Expand the three permutes in the RHS via the slide helper, then
      -- cancel the two iso pairs `from ∘ to ≈ id`, collapsing to the LHS form.
      rhs-collapse
        : permute (PermProp.++⁺ˡ eoutL ν)
            ∘ (box-of einL eoutL restL g
               ∘ permute (PermProp.++⁺ˡ einL (Perm.↭-sym ν)))
          ≈Term to-eo'
                  ∘ (((id ⊗₁ permute ν) ∘ (G ⊗₁ id))
                     ∘ (id ⊗₁ permute (Perm.↭-sym ν)))
                  ∘ from-ei'
      rhs-collapse = begin
        permute (PermProp.++⁺ˡ eoutL ν)
          ∘ (box-of einL eoutL restL g
             ∘ permute (PermProp.++⁺ˡ einL (Perm.↭-sym ν)))
          ≈⟨ ∘-resp-≈ (permute-++⁺ˡ-slide eoutL ν)
                      (∘-resp-≈ ≈-Term-refl (permute-++⁺ˡ-slide einL (Perm.↭-sym ν))) ⟩
        (to-eo' ∘ (id ⊗₁ permute ν) ∘ from-eo)
          ∘ ((to-eo ∘ (G ⊗₁ id) ∘ from-ei)
             ∘ (to-ei ∘ (id ⊗₁ permute (Perm.↭-sym ν)) ∘ from-ei'))
          ≈⟨ collapse ⟩
        to-eo' ∘ (((id ⊗₁ permute ν) ∘ (G ⊗₁ id))
                  ∘ (id ⊗₁ permute (Perm.↭-sym ν))) ∘ from-ei' ∎
        where
          P  = id ⊗₁ permute ν
          Q  = G ⊗₁ id
          R  = id ⊗₁ permute (Perm.↭-sym ν)
          collapse
            : (to-eo' ∘ P ∘ from-eo)
                ∘ ((to-eo ∘ Q ∘ from-ei)
                   ∘ (to-ei ∘ R ∘ from-ei'))
              ≈Term to-eo' ∘ ((P ∘ Q) ∘ R) ∘ from-ei'
          collapse = begin
            (to-eo' ∘ P ∘ from-eo) ∘ ((to-eo ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei'))
              ≈⟨ FM.assoc ⟩
            to-eo' ∘ ((P ∘ from-eo) ∘ ((to-eo ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei')))
              ≈⟨ refl⟩∘⟨ inner ⟩
            to-eo' ∘ ((P ∘ Q) ∘ R) ∘ from-ei' ∎
            where
              inner
                : (P ∘ from-eo) ∘ ((to-eo ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei'))
                  ≈Term ((P ∘ Q) ∘ R) ∘ from-ei'
              inner = begin
                (P ∘ from-eo) ∘ ((to-eo ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei'))
                  -- regroup: P ∘ (from-eo ∘ to-eo) ∘ Q ∘ (from-ei ∘ to-ei) ∘ R ∘ from-ei'
                  ≈⟨ FM.assoc ⟩
                P ∘ from-eo ∘ ((to-eo ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei'))
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                P ∘ (from-eo ∘ (to-eo ∘ Q ∘ from-ei)) ∘ (to-ei ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
                P ∘ ((from-eo ∘ to-eo) ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ (_≅_.isoʳ (unflatten-++-≅ eoutL restL) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                P ∘ (id ∘ Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ idˡ ⟩∘⟨refl ⟩
                P ∘ (Q ∘ from-ei) ∘ (to-ei ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                P ∘ Q ∘ (from-ei ∘ (to-ei ∘ R ∘ from-ei'))
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
                P ∘ Q ∘ ((from-ei ∘ to-ei) ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (_≅_.isoʳ (unflatten-++-≅ einL restL) ⟩∘⟨refl) ⟩
                P ∘ Q ∘ (id ∘ R ∘ from-ei')
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
                P ∘ Q ∘ (R ∘ from-ei')
                  -- now reassociate to ((P ∘ Q) ∘ R) ∘ from-ei'
                  ≈⟨ FM.sym-assoc ⟩
                (P ∘ Q) ∘ (R ∘ from-ei')
                  ≈⟨ FM.sym-assoc ⟩
                ((P ∘ Q) ∘ R) ∘ from-ei' ∎

--------------------------------------------------------------------------------
-- FINAL ASSEMBLY: transport `box-of-equivariant` (with f = H.vlab) along the
-- `map-++` substs to the `fire-mid` form, reconciling the permute factors.

module _ (H : Hypergraph FlatGen) (K : FaithfulnessResidual) where
  private module H = Hypergraph H

  -- The output-side permute reconciliation:
  --   permute-via-vlab vlab (++⁺ˡ eout μ)
  --     = subst₂ (map-++ eout restH)(map-++ eout restH')
  --              (permute (++⁺ˡ (map vlab eout) (map⁺ vlab μ)))
  pvv-++⁺ˡ-out
    : ∀ (eout : List (Fin H.nV)) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → permute-via-vlab H.vlab (PermProp.++⁺ˡ eout μ)
      ≡ subst₂ HomTerm
          (cong unflatten (sym (map-++ H.vlab eout restH)))
          (cong unflatten (sym (map-++ H.vlab eout restH')))
          (permute (PermProp.++⁺ˡ (map H.vlab eout) (PermProp.map⁺ H.vlab μ)))
  pvv-++⁺ˡ-out eout {restH} {restH'} μ =
    trans (cong permute (map⁺-++⁺ˡ H.vlab eout μ))
          (sym (permute-subst₂ (sym (map-++ H.vlab eout restH))
                               (sym (map-++ H.vlab eout restH'))
                               (PermProp.++⁺ˡ (map H.vlab eout) (PermProp.map⁺ H.vlab μ))))

  -- The input-side permute reconciliation (note ↭-sym μ : restH' ↭ restH):
  pvv-++⁺ˡ-in
    : ∀ (ein : List (Fin H.nV)) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → permute-via-vlab H.vlab (PermProp.++⁺ˡ ein (Perm.↭-sym μ))
      ≡ subst₂ HomTerm
          (cong unflatten (sym (map-++ H.vlab ein restH')))
          (cong unflatten (sym (map-++ H.vlab ein restH)))
          (permute (PermProp.++⁺ˡ (map H.vlab ein)
                     (Perm.↭-sym (PermProp.map⁺ H.vlab μ))))
  pvv-++⁺ˡ-in ein {restH} {restH'} μ =
    trans (cong permute (map⁺-++⁺ˡ H.vlab ein (Perm.↭-sym μ)))
    (trans (cong (λ z → permute
                   (subst₂ Perm._↭_ (sym (map-++ H.vlab ein restH'))
                                    (sym (map-++ H.vlab ein restH))
                     (PermProp.++⁺ˡ (map H.vlab ein) z)))
                 (map⁺-↭-sym H.vlab μ))
           (sym (permute-subst₂ (sym (map-++ H.vlab ein restH'))
                                (sym (map-++ H.vlab ein restH))
                                (PermProp.++⁺ˡ (map H.vlab ein)
                                  (Perm.↭-sym (PermProp.map⁺ H.vlab μ))))))

  fire-mid-equivariant
    : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → fire-mid H e restH'
      ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.eout e) μ)
              ∘ ( fire-mid H e restH
                  ∘ permute-via-vlab H.vlab (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)) )
  fire-mid-equivariant e {restH} {restH'} μ = goal
    where
      ein  = H.ein e
      eout = H.eout e
      f    = H.vlab

      -- boundary `map-++` paths.
      aein'  = sym (map-++ f ein  restH')   -- f ein ++ f restH' ≡ f (ein ++ restH')
      aeout' = sym (map-++ f eout restH')
      aein   = sym (map-++ f ein  restH)
      aeout  = sym (map-++ f eout restH)

      box' = box-of (map f ein) (map f eout) (map f restH') (H.elab e)
      boxr = box-of (map f ein) (map f eout) (map f restH ) (H.elab e)

      νf : map f restH Perm.↭ map f restH'
      νf = PermProp.map⁺ f μ

      -- RHS of box-of-equivariant (at f-level lists).
      out-p  = permute (PermProp.++⁺ˡ (map f eout) νf)
      in-p   = permute (PermProp.++⁺ˡ (map f ein) (Perm.↭-sym νf))

      -- box-of-equivariant transported by subst₂ aein' aeout'.
      beq : box' ≈Term out-p ∘ (boxr ∘ in-p)
      beq = box-of-equivariant K (map f ein) (map f eout) (H.elab e) νf

      -- LHS: fire-mid H e restH' = subst₂ aein' aeout' box'.
      lhs-eq : fire-mid H e restH'
               ≡ subst₂ HomTerm (cong unflatten aein') (cong unflatten aeout') box'
      lhs-eq = refl

      -- Transport `beq` and distribute the subst₂ over the two ∘.
      goal : fire-mid H e restH'
             ≈Term permute-via-vlab H.vlab (PermProp.++⁺ˡ eout μ)
                     ∘ ( fire-mid H e restH
                         ∘ permute-via-vlab H.vlab (PermProp.++⁺ˡ ein (Perm.↭-sym μ)) )
      goal =
        ≈-Term-trans
          (≡⇒≈Term lhs-eq)
          (≈-Term-trans
            -- subst₂ respects ≈Term: transport beq
            (subst₂-resp-≈ (cong unflatten aein') (cong unflatten aeout') beq)
            -- now: subst₂ aein' aeout' (out-p ∘ (boxr ∘ in-p)) ≈ RHS
            (≈-Term-trans
              (≡⇒≈Term
                (subst₂-∘-distrib aein' aeout aeout' out-p (boxr ∘ in-p)))
              (∘-resp-≈
                -- outer: subst₂ aeout aeout' out-p ≡ permute-via-vlab (++⁺ˡ eout μ)
                (≡⇒≈Term (sym (pvv-++⁺ˡ-out eout μ)))
                (≈-Term-trans
                  (≡⇒≈Term
                    (subst₂-∘-distrib aein' aein aeout boxr in-p))
                  (∘-resp-≈
                    -- middle: subst₂ aein aeout boxr ≡ fire-mid H e restH
                    (≡⇒≈Term refl)
                    -- inner: subst₂ aein' aein in-p ≡ permute-via-vlab (++⁺ˡ ein (↭-sym μ))
                    (≡⇒≈Term (sym (pvv-++⁺ˡ-in ein μ)))))))) 
        where
          -- subst₂ HomTerm respects ≈Term.
          subst₂-resp-≈
            : ∀ {A A' B B' : ObjTerm} (p : A ≡ A') (q : B ≡ B')
                {u v : HomTerm A B}
            → u ≈Term v
            → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
          subst₂-resp-≈ refl refl h = h

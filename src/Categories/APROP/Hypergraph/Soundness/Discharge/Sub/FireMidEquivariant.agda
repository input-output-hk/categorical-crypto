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
-- for `μ : restH ↭ restH'`.  The box-naturality content (no firing data,
-- no `cod`).
--
-- ## Proof architecture
--
--   1. `permute-++⁺ˡ-slide` — the CRUX: a `++⁺ˡ`-extended permutation slides
--      through `unflatten-++-≅` as `id ⊗₁ permute` on the suffix block.
--      List-induction; base = unitor naturality, cons = associator naturality.
--   2. `box-of-equivariant` — the generic statement.  The residual permutes
--      are slid by (1); the iso pairs `from ∘ to ≈ id` cancel; the central
--      `(id⊗permute μ) ∘ (G⊗id) ∘ (id⊗permute (↭-sym μ))` collapses to `G⊗id`
--      by bifunctor interchange + the self-loop inverse `permute-inv-right`
--      (via the Kelly residual `K`).
--   3. Final assembly — transport (2) (with `f = H.vlab`) along the `map-++`
--      substs to the `fire-mid` form, distributing the `subst₂` over the two
--      `∘` and reconciling the `permute-via-vlab (++⁺ˡ …)` factors.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidEquivariant
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeStepRelation sig
  using (box-of; fire-mid)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using (subst₂-∘-distrib)

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
-- subst₂ plumbing.  `≡⇒≈Term` comes from `Categories.FreeMonoidal` via
-- `open APROP sig`.

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
         (cong₂ (λ p q → subst₂ Perm._↭_ p q
                           (PermProp.++⁺ˡ (f x ∷ map f xs) (PermProp.map⁺ f μ)))
                (sym (sym-cong (map-++ f xs ys)))
                (sym (sym-cong (map-++ f xs zs)))))

--------------------------------------------------------------------------------
-- The crux generic helper: permute of a `++⁺ˡ`-extended permutation slides
-- as `id ⊗₁ permute` through `unflatten-++-≅`.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
-- Morphism-variable monoidal solver: discharges the free-fragment chases
-- (coherence + naturality + interchange around the opaque permutes and
-- `unflatten-++-≅` legs) as single `solveMor!` calls.
open import Categories.SolverFrontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F)
import Data.Vec as Vec

private
  module FM = Category FreeMonoidal

  -- the free monoidal category itself, as the solver's target bundle.
  FMC : MonoidalCategory _ _ _
  FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

open FM.HomReasoning

-- permute (++⁺ˡ ws ν) = to(ws,bs) ∘ (id ⊗₁ permute ν) ∘ from(ws,as).
permute-++⁺ˡ-slide
  : ∀ (ws : List X) {as bs : List X} (ν : as Perm.↭ bs)
  → permute (PermProp.++⁺ˡ ws ν)
    ≈Term _≅_.to (unflatten-++-≅ ws bs)
            ∘ (id ⊗₁ permute ν)
            ∘ _≅_.from (unflatten-++-≅ ws as)
permute-++⁺ˡ-slide [] {as} {bs} ν = solveMor! lhsᵗ rhsᵗ
  where
    -- atoms: 0 ↦ uf as, 1 ↦ uf bs; generator: permute ν
    open FinSetup FMC ( unflatten as Vec.∷ unflatten bs Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F
    open Sig {1} (λ { 0F → v0 , v1 })
    open WithGen (λ { (genS 0F) → permute ν })
    gν = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm v0 v1
    lhsᵗ = gν
    rhsᵗ = S._∘_ S.λ⇒ (S._∘_ (S._⊗₁_ S.id gν) S.λ⇐)
permute-++⁺ˡ-slide (w ∷ ws) {as} {bs} ν = begin
  id ⊗₁ permute (PermProp.++⁺ˡ ws ν)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (permute-++⁺ˡ-slide ws ν) ⟩
  id ⊗₁ (toW' ∘ (id ⊗₁ permute ν) ∘ fromW')
    ≈⟨ shuffle ⟩
  ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ (α⇐ ∘ (id ⊗₁ fromW')) ∎
  where
    toW'   = _≅_.to   (unflatten-++-≅ ws bs)
    fromW' = _≅_.from (unflatten-++-≅ ws as)

    -- the free part: associator naturality + interchange around the three
    -- opaque morphisms `toW'`, `fromW'`, `permute ν`.
    shuffle
      : id ⊗₁ (toW' ∘ (id ⊗₁ permute ν) ∘ fromW')
        ≈Term ((id ⊗₁ toW') ∘ α⇒) ∘ (id ⊗₁ permute ν) ∘ (α⇐ ∘ (id ⊗₁ fromW'))
    shuffle = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var w, 1 ↦ uf ws, 2 ↦ uf as, 3 ↦ uf bs,
        -- 4 ↦ uf (ws++as), 5 ↦ uf (ws++bs)
        open FinSetup FMC
          ( Var w Vec.∷ unflatten ws
              Vec.∷ unflatten as Vec.∷ unflatten bs
              Vec.∷ unflatten (ws ++ as) Vec.∷ unflatten (ws ++ bs) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
        v5 = V 5F
        -- generators: permute ν, toW', fromW'
        open Sig {3} (λ { 0F → v2 , v3
                        ; 1F → v1 ⊗ᵒ v3 , v5
                        ; 2F → v4 , v1 ⊗ᵒ v2 })
        open WithGen (λ { (genS 0F) → permute ν
                        ; (genS 1F) → toW'
                        ; (genS 2F) → fromW' })
        gν = gen 0F ; gto = gen 1F ; gfrom = gen 2F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v4) (v0 ⊗ᵒ v5)
        lhsᵗ = S._⊗₁_ S.id (S._∘_ gto (S._∘_ (S._⊗₁_ S.id gν) gfrom))
        rhsᵗ = S._∘_ (S._∘_ (S._⊗₁_ S.id gto) S.α⇒)
                     (S._∘_ (S._⊗₁_ S.id gν) (S._∘_ S.α⇐ (S._⊗₁_ S.id gfrom)))

--------------------------------------------------------------------------------
-- The plain-permute self-loop inverse, via K.

module _ (K : FaithfulnessResidual) where

  -- permute ν ∘ permute (↭-sym ν) ≈Term id (a self-loop, eval = id-fb).
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

      -- Expand the three permutes via the slide helper, cancel the iso pairs.
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
                  ≈⟨ FM.sym-assoc ⟩
                (P ∘ Q) ∘ (R ∘ from-ei')
                  ≈⟨ FM.sym-assoc ⟩
                ((P ∘ Q) ∘ R) ∘ from-ei' ∎

--------------------------------------------------------------------------------
-- FINAL ASSEMBLY: transport `box-of-equivariant` (with f = H.vlab) along the
-- `map-++` substs to the `fire-mid` form, reconciling the permute factors.

module _ (H : Hypergraph FlatGen) (K : FaithfulnessResidual) where
  private module H = Hypergraph H

  -- The output-side permute reconciliation.
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
      aein'  = sym (map-++ f ein  restH')
      aeout' = sym (map-++ f eout restH')
      aein   = sym (map-++ f ein  restH)
      aeout  = sym (map-++ f eout restH)

      box' = box-of (map f ein) (map f eout) (map f restH') (H.elab e)
      boxr = box-of (map f ein) (map f eout) (map f restH ) (H.elab e)

      νf : map f restH Perm.↭ map f restH'
      νf = PermProp.map⁺ f μ

      out-p  = permute (PermProp.++⁺ˡ (map f eout) νf)
      in-p   = permute (PermProp.++⁺ˡ (map f ein) (Perm.↭-sym νf))

      beq : box' ≈Term out-p ∘ (boxr ∘ in-p)
      beq = box-of-equivariant K (map f ein) (map f eout) (H.elab e) νf

      -- fire-mid H e restH' = subst₂ aein' aeout' box'.
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
            (subst₂-resp-≈ (cong unflatten aein') (cong unflatten aeout') beq)
            (≈-Term-trans
              (≡⇒≈Term
                (subst₂-∘-distrib aein' aeout aeout' out-p (boxr ∘ in-p)))
              (∘-resp-≈
                -- outer ≡ permute-via-vlab (++⁺ˡ eout μ)
                (≡⇒≈Term (sym (pvv-++⁺ˡ-out eout μ)))
                (≈-Term-trans
                  (≡⇒≈Term
                    (subst₂-∘-distrib aein' aein aeout boxr in-p))
                  (∘-resp-≈
                    -- middle ≡ fire-mid H e restH
                    (≡⇒≈Term refl)
                    -- inner ≡ permute-via-vlab (++⁺ˡ ein (↭-sym μ))
                    (≡⇒≈Term (sym (pvv-++⁺ˡ-in ein μ))))))))
        where
          subst₂-resp-≈
            : ∀ {A A' B B' : ObjTerm} (p : A ≡ A') (q : B ≡ B')
                {u v : HomTerm A B}
            → u ≈Term v
            → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
          subst₂-resp-≈ refl refl h = h

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Structural SHAPE LEMMAS of the strict decoder `decodePˢ` — the strict
-- analogue of the former non-strict `decode-rel`'s shape lemmas.  These feed the eventual
-- part-(I)ˢ roundtrip `st f ≈ˢ decodePˢ f`.
--
-- The strict Kelly residual is taken CONCRETELY from `Strict.Perm.PermK`
-- (discharged axiom-free for every vertex set, no parameter); `perm-rigidˢ`
-- is invoked at EXACTLY the points where the non-strict proof invokes
-- K-faithfulness.  No postulates, no holes.
--
-- Contents (in dependency order):
--   * `nE0-run`   : the structural-atom run (nE = 0) collapses to `idˢ`,
--                   leaving the final permutation;
--   * `Atom.shape` (with the `coe`-form `shape-coe`): a generic
--                   "nE = 0, dom ≡ cod" shape giving
--                   `decodePˢ f ≈ˢ coe (boundary cast)` via `perm-rigidˢ`;
--   * the concrete atomic shapes
--       `decodePˢ-id`, `decodePˢ-λ⇒`, `decodePˢ-λ⇐`,
--       `decodePˢ-ρ⇒`, `decodePˢ-ρ⇐`, `decodePˢ-α⇒`, `decodePˢ-α⇐`
--     each `≈ˢ st (atom)` (idˢ / coe casts);
--   * a closing comment RECORDING the ⊗/∘/σ shape statements, which are
--     proved elsewhere (`TensorBraid`, `DecodeCompose`, `DecodeSigma`) —
--     not here.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; hId)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (⟪⟫-cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using () renaming (_+_ to _+ⁿ_)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

--------------------------------------------------------------------------------
-- A `↭-reflexive` derivation is the boundary cast of `idˢ`.  Needs neither the
-- K-faithfulness residual nor a `DecidableEquality`, hence its home ABOVE the
-- residual block: that is what `DecodeSigma.Scr` can consume.

module Trivial (V : Set) (vlab : V → X) where
  open PK.Support V vlab

  refl-trivial
    : ∀ {xs ys : List V} (e : xs ≡ ys)
    → permuteˢ (Perm.↭-reflexive e)
      ≈ˢ castˢ refl (cong (map vlab) e) (idˢ {map vlab xs})
  refl-trivial refl = ≈-refl

--------------------------------------------------------------------------------
-- `nE = 0` collapse: a hypergraph with no edges has `runˢ ≡ (dom , idˢ)`.
-- Stated generically on an arbitrary `H` so the `nE ≡ 0` rewrite does
-- not have to cross the `⟪_⟫` abstraction.

nE0-run
  : (H : Hypergraph FlatGen) → Hypergraph.nE H ≡ 0
  → Σ[ s≡ ∈ Run.s-finˢ H ≡ Hypergraph.dom H ]
      (proj₂ (Run.runˢ H)
       ≡ subst (λ z → HomS (map (Hypergraph.vlab H) (Hypergraph.dom H))
                            (map (Hypergraph.vlab H) z))
               (sym s≡) idˢ)
nE0-run
  record { nV = nV ; vlab = vlab ; nE = .0 ; ein = ein ; eout = eout
         ; elab = elab ; dom = dom ; cod = cod } refl = refl , refl

--------------------------------------------------------------------------------
-- `perm-trivial`: a permutation between propositionally-equal endpoints
-- (with `Unique` target) evaluates to the corresponding boundary cast of
-- `idˢ`.  This is the single place K-faithfulness is consumed for the
-- structural atoms.

module Triv (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) where
  open PK.Support V vlab
  open Trivial V vlab

  K : PermK
  K = PK.permˢ-K V _≟V_ vlab

  perm-trivial
    : ∀ {xs ys : List V} (e : xs ≡ ys) → Unique ys → (p : xs ↭ ys)
    → permuteˢ p ≈ˢ castˢ refl (cong (map vlab) e) (idˢ {map vlab xs})
  perm-trivial e uniq p =
    ≈-trans (perm-rigidˢ K uniq p (Perm.↭-reflexive e)) (refl-trivial e)

--------------------------------------------------------------------------------
-- The generic structural-atom shape: `⟪ f ⟫` has no edges and its
-- `dom`/`cod` Fin-lists coincide PROPOSITIONALLY (true definitionally
-- for every `hId`-shaped atom).  Then `decodePˢ f ≈ˢ coe (boundary)`.
--
-- The final permutation is identified with the identity derivation by
-- `perm-rigidˢ` (the `Unique` codomain coming from linearity), exactly
-- where the non-strict `decode-id-is-id` invokes K-faithfulness.
--
-- `dc` is what confines this module to the *structural* atoms: it is FALSE
-- for `σ`, whose `⟪ σ ⟫` swaps its two boundary lists.  So the σ shape is
-- proved separately (`DecodeSigma`), and nothing here may be hoisted to a
-- level that quantifies over σ as well.

module Atom {A B : ObjTerm} (f : HomTerm A B)
  (nE≡0 : Hypergraph.nE ⟪ f ⟫ ≡ 0)
  (dc   : Hypergraph.dom ⟪ f ⟫ ≡ Hypergraph.cod ⟪ f ⟫)
  where
  private
    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫

    collapse = nE0-run ⟪ f ⟫ nE≡0
    s≡ : RF.s-finˢ ≡ Hf.dom
    s≡ = proj₁ collapse

    -- `proj₂ runˢ` is the cod-cast of `idˢ` coming from the collapse
    -- (`subst` over the `map vlab`-cod position IS a `castˢ refl (cong …)`).
    subst-cod≡cast
      : ∀ {u v v' : List (Fin Hf.nV)} (e : v ≡ v')
        (t : HomS (map Hf.vlab u) (map Hf.vlab v))
      → subst (λ z → HomS (map Hf.vlab u) (map Hf.vlab z)) e t
        ≡ castˢ refl (cong (map Hf.vlab) e) t
    subst-cod≡cast refl t = refl

    run≡ : proj₂ RF.runˢ
           ≡ castˢ refl (cong (map Hf.vlab) (sym s≡)) (idˢ {map Hf.vlab Hf.dom})
    run≡ = trans (proj₂ collapse) (subst-cod≡cast (sym s≡) idˢ)

    module T = Triv (Fin Hf.nV) _≟F_ Hf.vlab

    -- the boundary cast the atom collapses to
    bcast : map Hf.vlab Hf.dom ≡ map Hf.vlab Hf.cod
    bcast = cong (map Hf.vlab) dc

    -- `permuteˢ (finalPermˢ f)` is the cast of `idˢ` along `s≡ ∙ dc`
    sc : RF.s-finˢ ≡ Hf.cod
    sc = trans s≡ dc

    perm≡ : RF.permuteˢ (finalPermˢ f) ≈ˢ coe (cong (map Hf.vlab) sc)
    perm≡ = T.perm-trivial sc (⟪⟫-cod-Unique f) (finalPermˢ f)

    run≈ : proj₂ RF.runˢ ≈ˢ coe (cong (map Hf.vlab) (sym s≡))
    run≈ = ≡⇒≈ˢ run≡

    -- the inner term collapses to the boundary cast of `idˢ`
    inner≈ : RF.permuteˢ (finalPermˢ f) ∘ˢ proj₂ RF.runˢ ≈ˢ coe bcast
    inner≈ =
      ≈-trans (∘-resp perm≡ run≈)
      (≈-trans (coe-trans (cong (map Hf.vlab) (sym s≡))
                          (cong (map Hf.vlab) sc))
        (coe-uip (trans (cong (map Hf.vlab) (sym s≡))
                        (cong (map Hf.vlab) sc))
                 bcast))

  -- the structural-atom shape
  shape : decodePˢ f ≈ˢ castˢ (⟪⟫-domL f) (trans bcast (⟪⟫-codL f)) (idˢ {domL ⟪ f ⟫})
  shape =
    ≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f) inner≈)
      (≡⇒≈ˢ (cast-fuse refl (⟪⟫-domL f) bcast (⟪⟫-codL f) idˢ))

--------------------------------------------------------------------------------
-- `hId`-shape facts: every structural atom translates to an `hId`-shaped
-- graph, which has no edges and `dom ≡ cod`.

hId-nE : ∀ A → Hypergraph.nE (hId A) ≡ 0
hId-nE unit       = refl
hId-nE (Var x)    = refl
hId-nE (A ⊗₀ B)   = cong₂ _+ⁿ_ (hId-nE A) (hId-nE B)

hId-dc : ∀ A → Hypergraph.dom (hId A) ≡ Hypergraph.cod (hId A)
hId-dc unit       = refl
hId-dc (Var x)    = refl
hId-dc (A ⊗₀ B)   =
  cong₂ _++_
    (cong (map (_↑ˡ Hypergraph.nV (hId B))) (hId-dc A))
    (cong (map (Hypergraph.nV (hId A) ↑ʳ_)) (hId-dc B))

--------------------------------------------------------------------------------
-- A boundary cast of `idˢ` is the corresponding object-coercion `coe`.

cast-id-coe
  : ∀ {xs as bs} (p : xs ≡ as) (q : xs ≡ bs)
  → castˢ p q (idˢ {xs}) ≈ˢ coe (trans (sym p) q)
cast-id-coe refl q = ≈-refl

--------------------------------------------------------------------------------
-- The structural-atom shapes, each `≈ˢ st (atom)`.  `st (id)=st λ⇒=
-- st λ⇐ = idˢ`; the others are `coe` of the matching `List`-equality, so
-- `coe-uip` closes them against the shape's boundary `coe`.

shape-coe
  : ∀ {A B} (f : HomTerm A B) (nE≡0 : Hypergraph.nE ⟪ f ⟫ ≡ 0)
    (dc : Hypergraph.dom ⟪ f ⟫ ≡ Hypergraph.cod ⟪ f ⟫)
  → decodePˢ f
    ≈ˢ coe (trans (sym (⟪⟫-domL f))
                  (trans (cong (map (Hypergraph.vlab ⟪ f ⟫)) dc)
                         (⟪⟫-codL f)))
shape-coe f nE≡0 dc = ≈-trans (Atom.shape f nE≡0 dc) (cast-id-coe (⟪⟫-domL f) _)

module _ {A : ObjTerm} where
  -- id, λ⇒, λ⇐  →  idˢ
  decodePˢ-id : decodePˢ (id {A}) ≈ˢ st (id {A})
  decodePˢ-id = ≈-trans (shape-coe (id {A}) (hId-nE A) (hId-dc A)) (coe-id≈ _)

  decodePˢ-λ⇒ : decodePˢ (λ⇒ {A}) ≈ˢ st (λ⇒ {A})
  decodePˢ-λ⇒ = ≈-trans (shape-coe (λ⇒ {A}) (hId-nE A) (hId-dc A)) (coe-id≈ _)

  decodePˢ-λ⇐ : decodePˢ (λ⇐ {A}) ≈ˢ st (λ⇐ {A})
  decodePˢ-λ⇐ = ≈-trans (shape-coe (λ⇐ {A}) (hId-nE A) (hId-dc A)) (coe-id≈ _)

  -- ρ⇒, ρ⇐  →  coe (±++-identityʳ)
  decodePˢ-ρ⇒ : decodePˢ (ρ⇒ {A}) ≈ˢ st (ρ⇒ {A})
  decodePˢ-ρ⇒ =
    ≈-trans (shape-coe (ρ⇒ {A}) (hId-nE (A ⊗₀ unit)) (hId-dc (A ⊗₀ unit)))
            (coe-uip _ (++-identityʳ (flatten A)))

  decodePˢ-ρ⇐ : decodePˢ (ρ⇐ {A}) ≈ˢ st (ρ⇐ {A})
  decodePˢ-ρ⇐ =
    ≈-trans (shape-coe (ρ⇐ {A}) (hId-nE (A ⊗₀ unit)) (hId-dc (A ⊗₀ unit)))
            (coe-uip _ (sym (++-identityʳ (flatten A))))

-- α⇒, α⇐  →  coe (±++-assoc)
module _ {A B C : ObjTerm} where
  decodePˢ-α⇒ : decodePˢ (α⇒ {A} {B} {C}) ≈ˢ st (α⇒ {A} {B} {C})
  decodePˢ-α⇒ =
    ≈-trans (shape-coe (α⇒ {A} {B} {C})
               (hId-nE ((A ⊗₀ B) ⊗₀ C)) (hId-dc ((A ⊗₀ B) ⊗₀ C)))
            (coe-uip _ (++-assoc (flatten A) (flatten B) (flatten C)))

  decodePˢ-α⇐ : decodePˢ (α⇐ {A} {B} {C}) ≈ˢ st (α⇐ {A} {B} {C})
  decodePˢ-α⇐ =
    ≈-trans (shape-coe (α⇐ {A} {B} {C})
               (hId-nE ((A ⊗₀ B) ⊗₀ C)) (hId-dc ((A ⊗₀ B) ⊗₀ C)))
            (coe-uip _ (sym (++-assoc (flatten A) (flatten B) (flatten C))))

--------------------------------------------------------------------------------
-- COMPOUND AND σ SHAPES.  The boundary objects align DEFINITIONALLY (flatten
-- distributes over ⊗₀ as `_++_`), so these are cast-free statements:
--
--   decodePˢ-⊗-shape : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
--   decodePˢ-∘-shape : decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
--   decodePˢ-σ       : decodePˢ (σ {A} {B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- discharged in `Strict/Decode/DecodeCompose`(+`DecodeComposeAssembly`),
-- `Tensor/TensorReconcile` + `TensorBraid`, and
-- `DecodeSigma`(+`Interchange/BlockSwapComm`) respectively.
--------------------------------------------------------------------------------

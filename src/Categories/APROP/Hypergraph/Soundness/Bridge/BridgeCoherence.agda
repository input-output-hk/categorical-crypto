{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Bridge-level coherence toolkit: bridge distributivity (`bridge-∘`,
-- `bridge-⊗`), the `bridge-X-is-id` lemmas, the ρ bridge form and its
-- list-coherence, assorted Mac Lane / solver helpers, and the `α⇒` cast
-- worker (`Worker.work`, §last).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-flatten-≈; unflatten-++-≅; bridge
        ; subst-id-cod; subst-id-dom; subst-cod-cons; cast-cancel′; cod-cancel )

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal
  using (cancelˡ; pullˡ; elim-center)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₃)
-- Morphism-variable monoidal solver: discharges the structural-coherence /
-- naturality / interchange chases as single `solveMor!` calls at the free
-- monoidal category itself (cf. `Base/UnflattenMonoidal.agda`).
open import Categories.Coherence.Monoidal.Frontend using (module FinSetup)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
import Data.Vec as Vec
open import Data.List.Properties using (++-assoc; ++-identityʳ)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- bridge-∘: bridge distributes over composition (modulo iso cancellation).

bridge-∘
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → bridge (g ∘ f) ≈Term bridge g ∘ bridge f
-- `bridge h = F-cod ∘ h ∘ T-dom` (`Unflatten`), so `bridge g ∘ bridge f` IS the
-- drawer's `cancel-mid-iso` shape with `isoˡ B` as the middle iso, whose
-- conclusion already brackets the middle run as `(g ∘ f)`.
bridge-∘ {B = B} g f =
  ⟺ (cancel-mid-iso _ _ _ _ _ _ (_≅_.isoˡ (unflatten-flatten-≈ B)))

-- bridge-⊗: bridge distributes over tensor (modulo unflatten-++-≅ coherence).
bridge-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge (f ⊗₁ g)
  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
       ∘ (bridge f ⊗₁ bridge g)
       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
bridge-⊗ {A} {B} {C} {D} f g = solveMor! lhsᵗ rhsᵗ
  where
    -- atoms: 0-3 ↦ A B C D, 4-7 ↦ their unflattens,
    -- 8 ↦ unflatten (fA++fC), 9 ↦ unflatten (fB++fD)
    open FinSetup FMC
      ( A Vec.∷ B Vec.∷ C Vec.∷ D
          Vec.∷ unflatten (flatten A) Vec.∷ unflatten (flatten B)
          Vec.∷ unflatten (flatten C) Vec.∷ unflatten (flatten D)
          Vec.∷ unflatten (flatten A ++ flatten C)
          Vec.∷ unflatten (flatten B ++ flatten D) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
    v5 = V 5F ; v6 = V 6F ; v7 = V 7F ; v8 = V 8F ; v9 = V 9F
    -- generators: f, g, F-B, F-D, T-A, T-C, cBD-to, cAC-from
    open Sig {8} (λ { 0F → v0 , v1
                    ; 1F → v2 , v3
                    ; 2F → v1 , v5
                    ; 3F → v3 , v7
                    ; 4F → v4 , v0
                    ; 5F → v6 , v2
                    ; 6F → v5 ⊗ᵒ v7 , v9
                    ; 7F → v8 , v4 ⊗ᵒ v6 })
    open WithGen (λ { (genS 0F) → f
                    ; (genS 1F) → g
                    ; (genS 2F) → _≅_.from (unflatten-flatten-≈ B)
                    ; (genS 3F) → _≅_.from (unflatten-flatten-≈ D)
                    ; (genS 4F) → _≅_.to   (unflatten-flatten-≈ A)
                    ; (genS 5F) → _≅_.to   (unflatten-flatten-≈ C)
                    ; (genS 6F) → _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                    ; (genS 7F) → _≅_.from (unflatten-++-≅ (flatten A) (flatten C)) })
    gf = gen 0F ; gg = gen 1F ; gFB = gen 2F ; gFD = gen 3F
    gTA = gen 4F ; gTC = gen 5F ; gcBD = gen 6F ; gcAC = gen 7F
    lhsᵗ rhsᵗ : S.HomTerm v8 v9
    lhsᵗ = S._∘_ (S._∘_ gcBD (S._⊗₁_ gFB gFD))
                 (S._∘_ (S._⊗₁_ gf gg) (S._∘_ (S._⊗₁_ gTA gTC) gcAC))
    rhsᵗ = S._∘_ gcBD
                 (S._∘_ (S._⊗₁_ (S._∘_ gFB (S._∘_ gf gTA))
                                (S._∘_ gFD (S._∘_ gg gTC)))
                        gcAC)

--------------------------------------------------------------------------------
-- `bridge (id {A}) ≈Term id`: the iso `unflatten-flatten-≈ A` cancels.

bridge-id-is-id : ∀ A → bridge (id {A}) ≈Term id
bridge-id-is-id A = (refl⟩∘⟨ idˡ) ○ _≅_.isoʳ (unflatten-flatten-≈ A)

-- `bridge` is a whiskering by the two `unflatten` legs, so it respects `≈Term`
-- and carries a one-sided inverse pair to a one-sided inverse pair.  With
-- `inv-resp` this is what derives every ⇐-direction lemma below from its ⇒ twin.
bridge-resp-≈Term : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → bridge f ≈Term bridge g
bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

bridge-inv-id
  : ∀ {A B} (g : HomTerm B A) (f : HomTerm A B)
  → g ∘ f ≈Term id → bridge g ∘ bridge f ≈Term id
bridge-inv-id {A} g f e =
  ≈-Term-trans (≈-Term-sym (bridge-∘ g f))
    (≈-Term-trans (bridge-resp-≈Term e) (bridge-id-is-id A))

--------------------------------------------------------------------------------
-- The shape shared by the two bridge-unitor lemmas below: the unitor `U` slides
-- the `to`-leg `T` out of its `⊗`-frame (`nat`), whereupon the `from`-leg
-- absorbs it (`iso`) and only `U ∘ W` survives.

absorb-slide
  : ∀ {A₀ A₁ A₂ A₃ A₄ : ObjTerm}
      {W : HomTerm A₀ A₁} {V : HomTerm A₁ A₂} {U₁ : HomTerm A₂ A₃}
      {U₂ : HomTerm A₁ A₄} {T : HomTerm A₄ A₃} {F : HomTerm A₃ A₄}
  → U₁ ∘ V ≈Term T ∘ U₂ → F ∘ T ≈Term id
  → F ∘ U₁ ∘ V ∘ W ≈Term U₂ ∘ W
absorb-slide nat iso = (refl⟩∘⟨ pullˡ nat) ○ (refl⟩∘⟨ FM.assoc) ○ cancelˡ iso

--------------------------------------------------------------------------------
-- bridge (λ⇒) and bridge (λ⇐) reduce to `id`.

bridge-λ⇒-is-id : ∀ A → bridge (λ⇒ {A}) ≈Term id
bridge-λ⇒-is-id A =
  absorb-slide λ⇒∘id⊗f≈f∘λ⇒ (_≅_.isoʳ (unflatten-flatten-≈ A)) ○ λ⇒∘λ⇐≈id

-- `flatten (unit ⊗₀ A)` reduces to `flatten A`, so both bridges are endo at
-- `unflatten (flatten A)` and `λ⇐` is `λ⇒`'s inverse there.
bridge-λ⇐-is-id : ∀ A → bridge (λ⇐ {A}) ≈Term id
bridge-λ⇐-is-id A =
  inv-resp (bridge-inv-id λ⇐ λ⇒ λ⇐∘λ⇒≈id) idˡ (bridge-λ⇒-is-id A)

--------------------------------------------------------------------------------
-- Bridge form for ρ⇒.

bridge-ρ⇒-form
  : ∀ A → bridge (ρ⇒ {A})
       ≈Term ρ⇒ {unflatten (flatten A)}
              ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
bridge-ρ⇒-form A =
  absorb-slide ρ⇒∘f⊗id≈f∘ρ⇒ (_≅_.isoʳ (unflatten-flatten-≈ A))

--------------------------------------------------------------------------------
-- List-coherence for ρ⇒.

ρ⇒-coh-list
  : ∀ (xs : List X)
  → subst-id-cod (++-identityʳ xs)
    ≈Term ρ⇒ {unflatten xs} ∘ _≅_.from (unflatten-++-≅ xs [])
ρ⇒-coh-list []       = ⟺ λ⇒∘λ⇐≈id ○ (coherence₃ ⟩∘⟨refl)
ρ⇒-coh-list (y ∷ ys) = begin
  subst-id-cod (++-identityʳ (y ∷ ys))
    ≈⟨ ≈-Term-sym (subst-cod-cons (++-identityʳ ys)) ⟩
  id {Var y} ⊗₁ subst-id-cod (++-identityʳ ys)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇒-coh-list ys) ⟩
  id ⊗₁ (ρ⇒ ∘ inner-from)
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  ρ⇒ ∘ α⇐ ∘ id ⊗₁ inner-from ∎
  where
    inner-from = _≅_.from (unflatten-++-≅ ys [])

    -- atoms: 0 ↦ Var y, 1 ↦ unflatten ys, 2 ↦ unflatten (ys ++ [])
    open FinSetup FMC
      ( Var y Vec.∷ unflatten ys Vec.∷ unflatten (ys ++ []) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F
    open Sig {1} (λ { 0F → v2 , v1 ⊗ᵒ unitᵒ })
    open WithGen (λ { (genS 0F) → inner-from })
    g0 = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v2) (v0 ⊗ᵒ v1)
    lhsᵗ = S._⊗₁_ S.id (S._∘_ S.ρ⇒ g0)
    rhsᵗ = S._∘_ S.ρ⇒ (S._∘_ S.α⇐ (S._⊗₁_ S.id g0))

--------------------------------------------------------------------------------
-- ρ⇒-coherence / ρ⇐-coherence: combine list-coherence with bridge-form.

ρ⇒-coherence
  : ∀ A → subst-id-cod (++-identityʳ (flatten A)) ≈Term bridge (ρ⇒ {A})
ρ⇒-coherence A =
  ≈-Term-trans (ρ⇒-coh-list (flatten A)) (≈-Term-sym (bridge-ρ⇒-form A))

-- the ⇐ direction is the ⇒ one transposed: both sides are inverse pairs at
-- `unflatten (flatten A ++ [])`, so `inv-resp` transports the equation.
ρ⇐-coherence
  : ∀ A → subst-id-dom (++-identityʳ (flatten A)) ≈Term bridge (ρ⇐ {A})
ρ⇐-coherence A =
  inv-resp (cast-cancel′ (++-identityʳ (flatten A)))
           (bridge-inv-id ρ⇒ ρ⇐ ρ⇒∘ρ⇐≈id)
           (ρ⇒-coherence A)

--------------------------------------------------------------------------------
-- Mac Lane / solver helpers.

-- (the object variables are `A`…`D`, not `X`…: `X` is the signature's atom
-- type, which this module quantifies over as `List X`.)
pentagon-rewrite
  : ∀ {A B C D}
  → α⇒ {A ⊗₀ B} {C} {D}
  ≈Term α⇐ {A} {B} {C ⊗₀ D}
        ∘ id {A} ⊗₁ α⇒ {B} {C} {D}
        ∘ α⇒ {A} {B ⊗₀ C} {D}
        ∘ α⇒ {A} {B} {C} ⊗₁ id {D}
pentagon-rewrite {A} {B} {C} {D} = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC ( A Vec.∷ B Vec.∷ C Vec.∷ D Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
    open Sig {0} (λ ())
    open WithGen (λ { (genS ()) })
    lhsᵗ rhsᵗ : S.HomTerm (((v0 ⊗ᵒ v1) ⊗ᵒ v2) ⊗ᵒ v3) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
    lhsᵗ = S.α⇒
    rhsᵗ = S._∘_ S.α⇐ (S._∘_ (S._⊗₁_ S.id S.α⇒) (S._∘_ S.α⇒ (S._⊗₁_ S.α⇒ S.id)))

--------------------------------------------------------------------------------
-- Shared iso-collapse for the two bridge-α⇒ base cases below: after the
-- solver shuffles all opaque generators adjacent, the paired
-- `unflatten-flatten-≈` / `unflatten-++-≅` legs cancel by the iso laws
-- (which lie OUTSIDE the free-monoidal fragment `solveMor!` decides).

private
  -- the six `unflatten-flatten-≈`/`unflatten-++-≅` legs the three lemmas below
  -- all name; opened in place at each one's own `B`/`C`.
  module FT (B C : ObjTerm) where
    F-B = _≅_.from (unflatten-flatten-≈ B)
    F-C = _≅_.from (unflatten-flatten-≈ C)
    T-B = _≅_.to   (unflatten-flatten-≈ B)
    T-C = _≅_.to   (unflatten-flatten-≈ C)
    cBC-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

  -- The six-generator solver setup BOTH base cases below run (the four
  -- `unflatten-flatten-≈` legs of `B`/`C` plus the `unflatten-++-≅` pair).  They
  -- differ only in the α⇒ prefix their `lhsᵗ` frames — `Var x` under ρ, `unit`
  -- under λ — so it is carried as the LAST atom: that shares the arity map, the
  -- interpretation and the `gen` aliases verbatim, and the unit case simply
  -- never mentions atom 5.
  module Setup6 (B C P : ObjTerm) where
    open FT B C public
    open FinSetup FMC
      ( B Vec.∷ C
          Vec.∷ unflatten (flatten B) Vec.∷ unflatten (flatten C)
          Vec.∷ unflatten (flatten B ++ flatten C) Vec.∷ P Vec.∷ Vec.[] )
      public using (V; _⊗ᵒ_; module Sig)
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F ; v5 = V 5F
    -- generators: F-B, F-C, T-B, T-C, cBC-to, cBC-from
    open Sig {6} (λ { 0F → v0 , v2
                    ; 1F → v1 , v3
                    ; 2F → v2 , v0
                    ; 3F → v3 , v1
                    ; 4F → v2 ⊗ᵒ v3 , v4
                    ; 5F → v4 , v2 ⊗ᵒ v3 })
      public using (module S; genS; gen; module WithGen)
    open WithGen (λ { (genS 0F) → F-B ; (genS 1F) → F-C
                    ; (genS 2F) → T-B ; (genS 3F) → T-C
                    ; (genS 4F) → cBC-to ; (genS 5F) → cBC-from })
      public using (solveMor!)
    gFB = gen 0F ; gFC = gen 1F ; gTB = gen 2F ; gTC = gen 3F
    gcto = gen 4F ; gcfrom = gen 5F

  module _ (B C : ObjTerm) where
   open FT B C

   collapse-c-FT : cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from ≈Term id
   collapse-c-FT =
    -- the ⊗ of two iso cancellations IS the identity, so `elim-center` drops it
    elim-center (⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ B))
                          (_≅_.isoʳ (unflatten-flatten-≈ C))
                 ○ id⊗id≈id)
    ○ _≅_.isoˡ (unflatten-++-≅ (flatten B) (flatten C))

--------------------------------------------------------------------------------
-- Var-base case of the bridge-α⇒ cast: `++-assoc (x ∷ []) _ _` is `refl`, so
-- the cast the worker wants IS `id`.

bridge-α⇒-is-id-Var
  : ∀ x B C → bridge (α⇒ {Var x} {B} {C}) ≈Term id
bridge-α⇒-is-id-Var x B C = begin
  bridge (α⇒ {Var x} {B} {C})
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  id {Var x} ⊗₁ (cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (collapse-c-FT B C) ⟩
  id {Var x} ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎
  where
    -- the free part of the chase: all coherence/naturality/interchange,
    -- bringing each `from`/`to` leg adjacent to its partner.  Atom 5 is the
    -- prefix `Var x`, which `lhsᵗ` frames by ρ.
    open Setup6 B C (Var x)
    lhsᵗ rhsᵗ : S.HomTerm (v5 ⊗ᵒ v4) (v5 ⊗ᵒ v4)
    lhsᵗ = S._∘_
             (S._∘_ (S._∘_ (S._⊗₁_ S.id S.λ⇒) S.α⇒)
                    (S._⊗₁_ S.ρ⇐ (S._∘_ gcto (S._⊗₁_ gFB gFC))))
             (S._∘_ S.α⇒
               (S._∘_
                 (S._⊗₁_ (S._∘_ (S._⊗₁_ S.ρ⇒ gTB)
                                (S._∘_ S.α⇐ (S._⊗₁_ S.id S.λ⇐)))
                         gTC)
                 (S._∘_ S.α⇐ (S._⊗₁_ S.id gcfrom))))
    rhsᵗ = S._⊗₁_ S.id
             (S._∘_ gcto
               (S._∘_ (S._⊗₁_ (S._∘_ gFB gTB) (S._∘_ gFC gTC)) gcfrom))

--------------------------------------------------------------------------------
-- Unit-base case of the bridge-α⇒ cast: `++-assoc [] _ _` is `refl`.

bridge-α⇒-is-id-unit
  : ∀ B C → bridge (α⇒ {unit} {B} {C}) ≈Term id
bridge-α⇒-is-id-unit B C = begin
  bridge (α⇒ {unit} {B} {C})
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from
    ≈⟨ collapse-c-FT B C ⟩
  id ∎
  where
    -- the free part of the chase: all coherence/naturality/interchange,
    -- bringing each `from`/`to` leg adjacent to its partner.  The prefix atom
    -- is `unit`, which λ absorbs, so nothing below mentions it.
    open Setup6 B C unit
    lhsᵗ rhsᵗ : S.HomTerm v4 v4
    lhsᵗ = S._∘_
             (S._∘_ S.λ⇒
                    (S._⊗₁_ S.id (S._∘_ gcto (S._⊗₁_ gFB gFC))))
             (S._∘_ S.α⇒
               (S._∘_
                 (S._⊗₁_ (S._∘_ (S._⊗₁_ S.id gTB) S.λ⇐) gTC)
                 gcfrom))
    rhsᵗ = S._∘_ gcto (S._∘_ (S._⊗₁_ (S._∘_ gFB gTB) (S._∘_ gFC gTC)) gcfrom)

--------------------------------------------------------------------------------
-- The `bridge`-form for `α⇒` at EVERY object:
--
--   bridge (α⇒ {A}{B}{C}) ≈Term subst-id-cod (++-assoc (flatten A) …)
--
-- i.e. the associator's bridge IS the transported identity along the LIST
-- associativity proof, via a single structural recursion (`Worker.work`) on the
-- first object index, with ONE tensor clause: `A₁ ⊗₀ A₂` applies
-- `pentagon-rewrite`, distributes via `bridge-∘`/`bridge-⊗`, and recurses on
-- the structural subterms `A₁` and `A₂` — the prefix `A₁` needs no case
-- analysis because every ingredient below is stated at an arbitrary prefix
-- LIST.  The α⇐ factor is derived non-recursively (`derive-⇐`).
--
-- Because the target is a CAST, the residue is discharged by eliminating
-- equality proofs (`cast-inˡ`/`cast-inʳ` are one `refl` split each) plus the
-- pentagon for `++-assoc` PROOF TERMS (`cast-pentagon`, induction on the
-- prefix list) — no free-monoidal coherence chase, hence no solver call.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- `derive-⇐`: the α⇐ cast derived from the α⇒ result at the SAME object, via
-- the α⇒/α⇐ iso.  Non-recursive (takes the α⇒ result as an explicit argument),
-- so it stays outside `work`'s recursion; exported because `Strict.Soundness`'s
-- α⇐ boundary case is exactly this instance.

derive-⇐
  : ∀ A B C
  → bridge (α⇒ {A} {B} {C})
    ≈Term subst-id-cod (++-assoc (flatten A) (flatten B) (flatten C))
  → bridge (α⇐ {A} {B} {C})
    ≈Term subst-id-cod (sym (++-assoc (flatten A) (flatten B) (flatten C)))
derive-⇐ A B C =
  inv-resp (bridge-inv-id α⇐ α⇒ α⇐∘α⇒≈id)
           (cod-cancel (++-assoc (flatten A) (flatten B) (flatten C)))

--------------------------------------------------------------------------------
-- The cast kit `work`'s tensor clause bottoms out in.  Every lemma here is a
-- `refl` split on an equality proof: a cast is the identity once its proof is
-- `refl`, so the laxator legs cancel by the iso law alone.

private
  cto : (as bs : List X) → HomTerm (unflatten as ⊗₀ unflatten bs) (unflatten (as ++ bs))
  cto as bs = _≅_.to (unflatten-++-≅ as bs)

  cfrom : (as bs : List X) → HomTerm (unflatten (as ++ bs)) (unflatten as ⊗₀ unflatten bs)
  cfrom as bs = _≅_.from (unflatten-++-≅ as bs)

  -- `bridge` of a tensor whose two factors are already known: `bridge-⊗`
  -- followed by the congruence in the middle.  Both `⊗`-factors of `work`'s
  -- tensor decomposition below are this shape (with `id` on one side).
  bridge-⊗-resp
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
        {rf : HomTerm (unflatten (flatten A)) (unflatten (flatten B))}
        {rg : HomTerm (unflatten (flatten C)) (unflatten (flatten D))}
    → bridge f ≈Term rf → bridge g ≈Term rg
    → bridge (f ⊗₁ g)
      ≈Term cto (flatten B) (flatten D) ∘ (rf ⊗₁ rg) ∘ cfrom (flatten A) (flatten C)
  bridge-⊗-resp f g ef eg = bridge-⊗ f g ○ (refl⟩∘⟨ ⊗-resp-≈ ef eg ⟩∘⟨refl)

  -- a cast in one ⊗-factor, framed by the laxator pair, IS the cast of the
  -- framed proof: at `refl` the pair cancels.
  cast-inʳ
    : ∀ (p : List X) {as bs : List X} (e : as ≡ bs)
    → cto p bs ∘ (id ⊗₁ subst-id-cod e) ∘ cfrom p as
      ≈Term subst-id-cod (cong (p ++_) e)
  cast-inʳ p refl = elim-center id⊗id≈id ○ _≅_.isoˡ (unflatten-++-≅ p _)

  cast-inˡ
    : ∀ {as bs : List X} (e : as ≡ bs) (p : List X)
    → cto bs p ∘ (subst-id-cod e ⊗₁ id) ∘ cfrom as p
      ≈Term subst-id-cod (cong (_++ p) e)
  cast-inˡ refl p = elim-center id⊗id≈id ○ _≅_.isoˡ (unflatten-++-≅ _ p)

  -- casts along equal proofs are equal
  cast-≡
    : ∀ {as bs : List X} {e e' : as ≡ bs} → e ≡ e'
    → subst-id-cod e ≈Term subst-id-cod e'
  cast-≡ refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- `cast-pentagon`: Mac Lane's pentagon for `++-assoc`, at the level of the
-- CASTS it induces.  Induction on the prefix list `p`; the cons step pushes
-- `cong (x ∷_)` out of all four legs (`sym-cong`/`cong-∘` on the proofs,
-- `subst-cod-cons` on the morphisms) and applies the IH under `id {Var x} ⊗₁ _`.
--
-- (The same statement one level down — the pentagon for the ++-assoc PROOF
-- TERMS — is NOT reachable without K: `trans` does not invert, so there is no
-- congruence to rewrite a leg of a `trans`-composite in place.  At the
-- morphism level `⟩∘⟨` is that congruence.)

private
  cast-pentagon
    : ∀ (p a b c : List X)
    → subst-id-cod (sym (++-assoc p a (b ++ c)))
      ∘ subst-id-cod (cong (p ++_) (++-assoc a b c))
      ∘ subst-id-cod (++-assoc p (a ++ b) c)
      ∘ subst-id-cod (cong (_++ c) (++-assoc p a b))
      ≈Term subst-id-cod (++-assoc (p ++ a) b c)
  -- Base p = []: three of the four proofs are `refl`, so three legs are `id`;
  -- the survivor is `cong id`.
  cast-pentagon [] a b c =
    idˡ ○ (refl⟩∘⟨ idˡ) ○ idʳ ○ cast-≡ (cong-id (++-assoc a b c))
  -- Cons p = x ∷ p′: all four legs peel to `id {Var x} ⊗₁ _`, the ⊗-factors
  -- merge (`id⊗-∘`), the IH fires under the frame, and `subst-cod-cons` puts
  -- the frame back into the proof.
  cast-pentagon (x ∷ p) a b c =
    (peel₁ ⟩∘⟨ (peel₂ ⟩∘⟨ (peel₃ ⟩∘⟨ peel₄)))
    ○ (refl⟩∘⟨ id⊗-∘3 _ _ _) ○ id⊗-∘ _ _
    ○ ⊗-resp-≈ ≈-Term-refl (cast-pentagon p a b c)
    ○ subst-cod-cons (++-assoc (p ++ a) b c)
    where
      P₁ = ++-assoc p a b
      P₂ = ++-assoc p (a ++ b) c
      P₃ = ++-assoc a b c
      P₄ = ++-assoc p a (b ++ c)

      -- each leg's proof is `cong (x ∷_)` of the corresponding leg at `p`
      peel₁ : subst-id-cod (sym (++-assoc (x ∷ p) a (b ++ c)))
              ≈Term id {Var x} ⊗₁ subst-id-cod (sym P₄)
      peel₁ = cast-≡ (sym-cong P₄) ○ ⟺ (subst-cod-cons (sym P₄))

      peel₂ : subst-id-cod (cong ((x ∷ p) ++_) (++-assoc a b c))
              ≈Term id {Var x} ⊗₁ subst-id-cod (cong (p ++_) P₃)
      peel₂ = cast-≡ (cong-∘ {f = x ∷_} {g = p ++_} P₃)
              ○ ⟺ (subst-cod-cons (cong (p ++_) P₃))

      peel₃ : subst-id-cod (++-assoc (x ∷ p) (a ++ b) c)
              ≈Term id {Var x} ⊗₁ subst-id-cod P₂
      peel₃ = ⟺ (subst-cod-cons P₂)

      peel₄ : subst-id-cod (cong (_++ c) (++-assoc (x ∷ p) a b))
              ≈Term id {Var x} ⊗₁ subst-id-cod (cong (_++ c) P₁)
      peel₄ = cast-≡ (trans (sym (cong-∘ {f = _++ c} {g = x ∷_} P₁))
                            (cong-∘ {f = x ∷_} {g = _++ c} P₁))
              ○ ⟺ (subst-cod-cons (cong (_++ c) P₁))

--------------------------------------------------------------------------------
-- The worker.  `work A B C` proves the α⇒ cast for `A` by structural
-- recursion on `A`.

module Worker where

  work
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
    ≈Term subst-id-cod (++-assoc (flatten A) (flatten B) (flatten C))

  -- `++-assoc [] ys zs` and `++-assoc (x ∷ []) ys zs` are both `refl`, so both
  -- base casts ARE `id` — which is what the two base lemmas prove.
  work unit    B C = bridge-α⇒-is-id-unit B C
  work (Var x) B C = bridge-α⇒-is-id-Var x B C

  -- `pentagon-rewrite` re-associates `α⇒ {A₁ ⊗₀ A₂}` into four legs whose
  -- bridges are the four recursive results; `bridge-∘`/`bridge-⊗` distribute,
  -- the two laxator sandwiches absorb their cast (`cast-inʳ`/`cast-inˡ`), and
  -- the residue is the list-level `cast-pentagon`.  The prefix needs NO case
  -- analysis: every ingredient is stated at an arbitrary prefix LIST, so the
  -- one clause covers `A₁ = unit`, `A₁ = Var x` and `A₁` compound alike.
  -- Each recursive call is on a structural subterm of the matched first
  -- argument (`A₁` or `A₂`) and sits in the clause's right-hand side, where the
  -- match is visible to the termination checker.
  work (A₁ ⊗₀ A₂) B C = begin
    bridge (α⇒ {A₁ ⊗₀ A₂} {B} {C})
      ≈⟨ bridge-resp-≈Term pentagon-rewrite ⟩
    bridge ( α⇐ {A₁} {A₂} {B ⊗₀ C}
           ∘ id {A₁} ⊗₁ α⇒ {A₂} {B} {C}
           ∘ α⇒ {A₁} {A₂ ⊗₀ B} {C}
           ∘ α⇒ {A₁} {A₂} {B} ⊗₁ id {C} )
      ≈⟨ bridge-∘ _ _ ○ (refl⟩∘⟨ bridge-∘ _ _) ○ (refl⟩∘⟨ refl⟩∘⟨ bridge-∘ _ _) ⟩
    bridge (α⇐ {A₁} {A₂} {B ⊗₀ C})
      ∘ bridge (id {A₁} ⊗₁ α⇒ {A₂} {B} {C})
      ∘ bridge (α⇒ {A₁} {A₂ ⊗₀ B} {C})
      ∘ bridge (α⇒ {A₁} {A₂} {B} ⊗₁ id {C})
      ≈⟨ derive-⇐ A₁ A₂ (B ⊗₀ C) (work A₁ A₂ (B ⊗₀ C))
         ⟩∘⟨ ( bridge-⊗-resp (id {A₁}) (α⇒ {A₂} {B} {C})
                             (bridge-id-is-id A₁) (work A₂ B C)
               ○ cast-inʳ (flatten A₁) (++-assoc (flatten A₂) (flatten B) (flatten C)) )
         ⟩∘⟨ work A₁ (A₂ ⊗₀ B) C
         ⟩∘⟨ ( bridge-⊗-resp (α⇒ {A₁} {A₂} {B}) (id {C})
                             (work A₁ A₂ B) (bridge-id-is-id C)
               ○ cast-inˡ (++-assoc (flatten A₁) (flatten A₂) (flatten B)) (flatten C) )
         ○ cast-pentagon (flatten A₁) (flatten A₂) (flatten B) (flatten C) ⟩
    subst-id-cod (++-assoc (flatten A₁ ++ flatten A₂) (flatten B) (flatten C)) ∎

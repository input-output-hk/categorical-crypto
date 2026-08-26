{-# OPTIONS --safe --without-K #-}

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

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Bridge.BridgeAlphaFormCompound
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-++-≅; bridge; subst-id-cod; subst-cod-cons; cod-cancel)
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-∘
        ; bridge-⊗
        ; bridge-id-is-id
        ; bridge-inv-id
        ; bridge-resp-≈Term
        ; pentagon-rewrite
        ; bridge-α⇒-is-id-Var
        ; bridge-α⇒-is-id-unit
        )

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal using (elim-center)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (cong-id; cong-∘; sym-cong)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

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

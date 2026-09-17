{-# OPTIONS --safe #-}

-- ============================================================================
-- The hand-rolled Kleisli composition of machines IS the abstract one.
--
-- `CategoricalCrypto.Standard2.StdUC` instantiates the abstract UC layer at
-- the REVERSED monoidal category of machines, and the graded Kleisli triple it
-- works with is the curried tensor of that category.  Unfolded, that triple is
-- the familiar bookkeeping of `Machine.Core`:
--
--   T₀ X B  = B ⊗₀ X          sub c   = id ⊗₁ c          return = ρ⇐
--   T₁ Y h  ≅ h ⊗₁ id         μ u v   ≅ ⊗-assoc          ext X h = ⊗-assoc ∘ (h ⊗₁ id)
--
-- and the abstract Kleisli composition `h ∙ f = ext X h ∘ f` differs from
-- `h ∘ᴷ f` only by the ORDER of the two grades: `∘ᴷ` lists the inner grade
-- first (`E₁ ⊗₀ E₂`), `∙` lists the outer one first (`E₂ ⊗₀ E₁`).  The bridge
-- `∘ᴷ-∙` says exactly that `_∘ᴷ_` is `_∙_` followed by the grade swap, and
-- `⊗ᴷ-∙` says that `_⊗ᴷ_` is a Kleisli composite of the two one-sided
-- liftings.  Everything proved about the abstract layer therefore transfers
-- to the concrete Kleisli builders; as a demonstration, the two laws
-- `∘ᴷ-assoc` and `unit-∘ᴷ` of `Machine.Monoidal.Kleisli` and `Machine.NAry`
-- are re-derived here from the graded-triple laws alone, with the residual
-- coherence discharged by the hexagons and the naturality of the symmetry.
--
-- Nothing here depends on `Machine.UC`; the triple is rebuilt verbatim so that
-- the statements are definitionally about `StdUC`'s `ℳ-standard`.
-- ============================================================================

module CategoricalCrypto.Machine.UC.Kleisli where

open import categorical-crypto.Prelude hiding (id; _∘_; return)
open import Data.Fin using (#_)
open import Data.Vec using (_∷_; [])

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)
open import Categories.Category.Monoidal.Construction.Reverse using (Reverse-MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
open import Categories.Functor.Monoidal.CurriedTensor using (curriedTensor)
import Categories.Functor.Monoidal.CurriedTensor.Properties as CurriedTensorProperties
open import Categories.Monad.Graded using (GradedKleisliTriple; GradedMonad⇒GradedKleisliTriple)
import Categories.Morphism.Reasoning as MR
open import Categories.Coherence.Monoidal using (module SymAtoms; module SymSolve)
open import Categories.FreeMonoidal using (v≤v)   -- the instance that enables `S.σ`

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Forwarder using (⊗₁-id; ρ-idᴷ)
open import CategoricalCrypto.Machine.Monoidal.Interchange using (⊗₁-interchange)
open import CategoricalCrypto.Machine.Monoidal.Coherence
  using (ρ-isoˡ; α-isoʳ; hexagon; ∘ᴷ-fwd-decomp; ⊗ᴷ-fwd-decomp; mid4-decomp; absorb-regroup-decomp)
open import CategoricalCrypto.Machine.Monoidal.Braiding using (σ-natural)
open import CategoricalCrypto.Machine.MonoidalCategory

open Category MachineCategory using (module HomReasoning; assoc; sym-assoc; identityˡ; identityʳ; identity²)
open HomReasoning
open MR MachineCategory
open Monoidal machine-monoidal using (assoc-commute-from)
open Symmetric machine-symmetric using (hexagon₂)

-- ----------------------------------------------------------------------------
-- The triple, exactly as `Standard2.StdUC` builds it.
-- ----------------------------------------------------------------------------

machines : MonoidalCategory _ _ _
machines = Reverse-MonoidalCategory machine-monoidal-category

-- The coercion of `curriedTensor M` to a `GradedMonad M (U M)` is done over
-- an abstract `M`, as `StdUC` does, and only then instantiated at `machines`.
-- Done directly at `machines`, the conversion check unfolds `Endofunctors`
-- down to the record literal of the machine category on both sides and takes
-- a quarter of an hour.
module _ {o ℓ e} (M : MonoidalCategory o ℓ e) where
  curriedTriple : GradedKleisliTriple M (MonoidalCategory.U M)
  curriedTriple = GradedMonad⇒GradedKleisliTriple (curriedTensor M)

-- Definitionally `StdUC.ℳ-standard machines ℰ`, for any `ℰ`.
ℳ : GradedKleisliTriple machines (MonoidalCategory.U machines)
ℳ = curriedTriple machines

open GradedKleisliTriple ℳ public
  using (T₀; ext; return; sub; T₁; μ; ext-resp-≈; sub-homomorphism; sub-commute₂; sub-commute′;
         _⊙_; ⊙-assoc; ⊙-identityˡ)

-- The abstract Kleisli composition, as in `CategoricalCrypto.Abstract2`.  Its
-- type is `A ⇒ T₀ (X ⊗ᵐ P) C` in the reversed category, which is the type
-- written below in machine notation.
infixr 9 _∙_
_∙_ : ∀ {A B C X P} → Machine B (C ⊗₀ P) → Machine A (B ⊗₀ X) → Machine A (C ⊗₀ (P ⊗₀ X))
_∙_ {X = X} h f = ext X h CC.∘ f

-- ----------------------------------------------------------------------------
-- 1.  The triple, unfolded.
-- ----------------------------------------------------------------------------

T₀-⊗ : ∀ X B → T₀ X B ≡ (B ⊗₀ X)
T₀-⊗ _ _ = refl

sub-⊗ˡ : ∀ {X X′ A} (c : Machine X X′) → sub c {A} ≅ᴹ (A ⊗ˡ c)
sub-⊗ˡ _ = ≅ᴹ-refl

return-ρ⇐ : ∀ {A} → return {A} ≅ᴹ ρ⇐ {A}
return-ρ⇐ = ≅ᴹ-refl

ext-⊗ : ∀ u {v A B} (h : Machine A (B ⊗₀ v)) → ext u h ≡ (⊗-assoc {B} {v} {u} CC.∘ (h ⊗ʳ u))
ext-⊗ _ _ = refl

-- `T₁` is derived from `ext`, `return` and `sub`, so it is only up to `≅ᴹ`.
T₁-⊗ʳ : ∀ Y {A B} (h : Machine A B) → T₁ Y h ≅ᴹ (h ⊗ʳ Y)
T₁-⊗ʳ = CurriedTensorProperties.T₁-⊗ machines

-- `μ u v = ext u id = ⊗-assoc ∘ (id ⊗₁ id)`.
μ-assoc : ∀ u v {A} → μ u v {A} ≅ᴹ ⊗-assoc {A} {v} {u}
μ-assoc u v = elimʳ ⊗₁-id

-- ----------------------------------------------------------------------------
-- 2.  The bridge: `_∘ᴷ_` is `_∙_` followed by the grade swap.
-- ----------------------------------------------------------------------------

∘ᴷ-∙ : ∀ {A B C E₁ E₂} (h : Machine B (C ⊗₀ E₂)) (f : Machine A (B ⊗₀ E₁))
     → (h ∘ᴷ f) ≅ᴹ (sub (⊗-symₘ {E₂} {E₁}) CC.∘ (h ∙ f))
∘ᴷ-∙ {A} {B} {C} {E₁} {E₂} h f = begin
    ∘ᴷ-fwd CC.∘ ((h ⊗₁ CC.id) CC.∘ f)
  ≈⟨ ∘ᴷ-fwd-decomp ⟩∘⟨refl ⟩
    ((CC.id ⊗₁ ⊗-symₘ) CC.∘ ⊗-assoc) CC.∘ ((h ⊗₁ CC.id) CC.∘ f)
  ≈⟨ assoc ⟩
    (CC.id ⊗₁ ⊗-symₘ) CC.∘ (⊗-assoc CC.∘ ((h ⊗₁ CC.id) CC.∘ f))
  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (CC.id ⊗₁ ⊗-symₘ) CC.∘ ((⊗-assoc CC.∘ (h ⊗₁ CC.id)) CC.∘ f)
  ∎

-- ----------------------------------------------------------------------------
-- 4a.  `unit-∘ᴷ`, from the left unit law of the triple.
-- ----------------------------------------------------------------------------

-- `idᴷ` is the unit of the triple.
idᴷ-return : ∀ {A} → idᴷ {A} ≅ᴹ return {A}
idᴷ-return = begin
    idᴷ                        ≈⟨ introˡ ρ-isoˡ ⟩
    (ρ⇐ CC.∘ ρ⇒) CC.∘ idᴷ      ≈⟨ pullʳ ρ-idᴷ ⟩
    ρ⇐ CC.∘ CC.id              ≈⟨ identityʳ ⟩
    ρ⇐                         ∎

-- The braiding is compatible with the unitors (`Braided.Properties`).
ρ⇒-σ : ∀ {X} → (ρ⇒ {X} CC.∘ ⊗-symₘ {I} {X}) ≅ᴹ λ⇒ {X}
ρ⇒-σ = BraidedProperties.inv-braiding-coherence (Symmetric.braided machine-symmetric)

unit-∘ᴷ′ : ∀ {A C E₁} (h : Machine A (C ⊗₀ E₁))
         → ((CC.id ⊗₁ ρ⇒) CC.∘ (idᴷ ∘ᴷ h)) ≅ᴹ h
unit-∘ᴷ′ {A} {C} {E₁} h = begin
    (CC.id ⊗₁ ρ⇒) CC.∘ (idᴷ ∘ᴷ h)
  ≈⟨ refl⟩∘⟨ ∘ᴷ-∙ idᴷ h ⟩
    (CC.id ⊗₁ ρ⇒) CC.∘ (sub (⊗-symₘ {I} {E₁}) CC.∘ (idᴷ ∙ h))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (ext-resp-≈ idᴷ-return ⟩∘⟨refl) ⟩
    (CC.id ⊗₁ ρ⇒) CC.∘ (sub (⊗-symₘ {I} {E₁}) CC.∘ (return ∙ h))
  ≈⟨ sym-assoc ⟩
    ((CC.id ⊗₁ ρ⇒) CC.∘ sub (⊗-symₘ {I} {E₁})) CC.∘ (return ∙ h)
  ≈⟨ merge-unitor ⟩∘⟨refl ⟩
    (CC.id ⊗₁ λ⇒) CC.∘ (return ∙ h)
  ≈⟨ ⊙-identityˡ ⟩
    h
  ∎
  where
  -- `(id ⊗₁ ρ⇒) ∘ sub σ` is `sub` of the reversed category's right unitor.
  merge-unitor : ((CC.id {C} ⊗₁ ρ⇒ {E₁}) CC.∘ (CC.id {C} ⊗₁ ⊗-symₘ {I} {E₁})) ≅ᴹ (CC.id {C} ⊗₁ λ⇒ {E₁})
  merge-unitor = ≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange CC.id CC.id ⊗-symₘ ρ⇒)) (⊗₁-resp-≅ᴹ identity² ρ⇒-σ)

-- ----------------------------------------------------------------------------
-- 4b.  `∘ᴷ-assoc`, from the associativity of the triple.
--
-- Both sides are brought to the form `sub c ∘ (F ⊙ (G ⊙ h))`: the right-hand
-- side by the bridge (twice), `sub-commute₂` and `⊙-assoc`; the left-hand side
-- by the bridge, the naturality of `sub` and one coherence law,
-- `regroup-coh`, which says what `absorb-regroup` does to the grades.  That
-- law is a three-atom symmetric coherence (`swap-coh`) surrounded by
-- bookkeeping; the coherence solver does not split crossing blocks, so
-- `swap-coh` is done by hand with the two hexagons and the naturality of the
-- symmetry.
-- ----------------------------------------------------------------------------

-- Tensoring with an identity on the left is functorial.
⊗ˡ-∘ : ∀ {D X Y Z} (p : Machine Y Z) (q : Machine X Y)
     → ((CC.id {D} ⊗₁ p) CC.∘ (CC.id {D} ⊗₁ q)) ≅ᴹ (CC.id {D} ⊗₁ (p CC.∘ q))
⊗ˡ-∘ p q = ≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange CC.id CC.id q p)) (⊗₁-resp-≅ᴹ identity² ≅ᴹ-refl)

-- Moving `E₂` past `E ⊗₀ E₁` after swapping `E₁` and `E` is the same as
-- swapping `E₂` and `E₁` and then moving `E₁ ⊗₀ E₂` past `E`.
swap-coh : ∀ {E E₁ E₂}
  → (⊗-assoc {E} {E₁} {E₂} CC.∘ (⊗-symₘ {E₂} {E ⊗₀ E₁} CC.∘ (CC.id {E₂} ⊗₁ ⊗-symₘ {E₁} {E})))
    ≅ᴹ (⊗-symₘ {E₁ ⊗₀ E₂} {E} CC.∘ ((⊗-symₘ {E₂} {E₁} ⊗₁ CC.id {E}) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E}))
swap-coh {E} {E₁} {E₂} = begin
    ⊗-assoc {E} {E₁} {E₂} CC.∘ (σ₁ CC.∘ (CC.id ⊗₁ σ₂))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introˡ (α-isoʳ {E₂} {E} {E₁}) ⟩
    ⊗-assoc {E} {E₁} {E₂} CC.∘ (σ₁ CC.∘ ((⊗-assoc {E₂} {E} {E₁} CC.∘ ⊗-assoc⃖ {E₂} {E} {E₁}) CC.∘ (CC.id ⊗₁ σ₂)))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    ⊗-assoc {E} {E₁} {E₂} CC.∘ (σ₁ CC.∘ (⊗-assoc {E₂} {E} {E₁} CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂))))
  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    ⊗-assoc {E} {E₁} {E₂} CC.∘ ((σ₁ CC.∘ ⊗-assoc {E₂} {E} {E₁}) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂)))
  ≈⟨ sym-assoc ⟩
    (⊗-assoc {E} {E₁} {E₂} CC.∘ (σ₁ CC.∘ ⊗-assoc {E₂} {E} {E₁})) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂))
  ≈⟨ ≅ᴹ-sym (hexagon {E₂} {E} {E₁}) ⟩∘⟨refl ⟩
    ((CC.id ⊗₁ σ₃) CC.∘ (⊗-assoc {E} {E₂} {E₁} CC.∘ (σ₄ ⊗₁ CC.id))) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂))
  ≈⟨ assoc ⟩
    (CC.id ⊗₁ σ₃) CC.∘ ((⊗-assoc {E} {E₂} {E₁} CC.∘ (σ₄ ⊗₁ CC.id)) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂)))
  ≈⟨ refl⟩∘⟨ assoc ⟩
    (CC.id ⊗₁ σ₃) CC.∘ (⊗-assoc {E} {E₂} {E₁} CC.∘ ((σ₄ ⊗₁ CC.id) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id ⊗₁ σ₂))))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ hex₂ ⟩
    (CC.id ⊗₁ σ₃) CC.∘ (⊗-assoc {E} {E₂} {E₁} CC.∘ (⊗-assoc⃖ {E} {E₂} {E₁} CC.∘ (σ₆ CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E})))
  ≈⟨ refl⟩∘⟨ cancelˡ (α-isoʳ {E} {E₂} {E₁}) ⟩
    (CC.id ⊗₁ σ₃) CC.∘ (σ₆ CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E})
  ≈⟨ sym-assoc ⟩
    ((CC.id ⊗₁ σ₃) CC.∘ σ₆) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E}
  ≈⟨ ≅ᴹ-sym (σ-natural σ₃ CC.id) ⟩∘⟨refl ⟩
    (σ₅ CC.∘ (σ₃ ⊗₁ CC.id)) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E}
  ≈⟨ assoc ⟩
    σ₅ CC.∘ ((σ₃ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E})
  ∎
  where
  σ₁ : Machine (E₂ ⊗₀ (E ⊗₀ E₁)) ((E ⊗₀ E₁) ⊗₀ E₂)
  σ₁ = ⊗-symₘ
  σ₂ : Machine (E₁ ⊗₀ E) (E ⊗₀ E₁)
  σ₂ = ⊗-symₘ
  σ₃ : Machine (E₂ ⊗₀ E₁) (E₁ ⊗₀ E₂)
  σ₃ = ⊗-symₘ
  σ₄ : Machine (E₂ ⊗₀ E) (E ⊗₀ E₂)
  σ₄ = ⊗-symₘ
  σ₅ : Machine ((E₁ ⊗₀ E₂) ⊗₀ E) (E ⊗₀ (E₁ ⊗₀ E₂))
  σ₅ = ⊗-symₘ
  σ₆ : Machine ((E₂ ⊗₀ E₁) ⊗₀ E) (E ⊗₀ (E₂ ⊗₀ E₁))
  σ₆ = ⊗-symₘ
  -- `hexagon₂` at `X = E₂`, `Y = E₁`, `Z = E`, rebracketed.
  hex₂ : ((σ₄ ⊗₁ CC.id {E₁}) CC.∘ (⊗-assoc⃖ {E₂} {E} {E₁} CC.∘ (CC.id {E₂} ⊗₁ σ₂)))
         ≅ᴹ (⊗-assoc⃖ {E} {E₂} {E₁} CC.∘ (σ₆ CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E}))
  hex₂ = sym-assoc ○ hexagon₂ ○ assoc

-- What `absorb-regroup` does to the grades, expressed through `sub`: the
-- right-hand side is `sub cr ∘ ⊗-assoc` for the grade morphism `cr` of
-- `∘ᴷ-assoc′` below.
regroup-coh : ∀ {D E E₁ E₂}
  → (absorb-regroup {D} {E₂} {E₁} {E} CC.∘ (CC.id {D ⊗₀ E₂} ⊗₁ ⊗-symₘ {E₁} {E}))
    ≅ᴹ ((CC.id {D} ⊗₁ (⊗-symₘ {E₁ ⊗₀ E₂} {E} CC.∘ ((⊗-symₘ {E₂} {E₁} ⊗₁ CC.id {E}) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E})))
        CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E})
regroup-coh {D} {E} {E₁} {E₂} = begin
    absorb-regroup CC.∘ (CC.id ⊗₁ σ₂)
  ≈⟨ absorb-regroup-decomp ⟩∘⟨refl ⟩
    ((CC.id ⊗₁ a) CC.∘ ((CC.id ⊗₁ σ₁) CC.∘ ⊗-assoc {D} {E₂} {E ⊗₀ E₁})) CC.∘ (CC.id ⊗₁ σ₂)
  ≈⟨ assoc ⟩
    (CC.id ⊗₁ a) CC.∘ (((CC.id ⊗₁ σ₁) CC.∘ ⊗-assoc {D} {E₂} {E ⊗₀ E₁}) CC.∘ (CC.id ⊗₁ σ₂))
  ≈⟨ refl⟩∘⟨ assoc ⟩
    (CC.id ⊗₁ a) CC.∘ ((CC.id ⊗₁ σ₁) CC.∘ (⊗-assoc {D} {E₂} {E ⊗₀ E₁} CC.∘ (CC.id ⊗₁ σ₂)))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-nat ⟩
    (CC.id ⊗₁ a) CC.∘ ((CC.id ⊗₁ σ₁) CC.∘ ((CC.id ⊗₁ (CC.id ⊗₁ σ₂)) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E}))
  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (CC.id ⊗₁ a) CC.∘ (((CC.id ⊗₁ σ₁) CC.∘ (CC.id ⊗₁ (CC.id ⊗₁ σ₂))) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E})
  ≈⟨ refl⟩∘⟨ (⊗ˡ-∘ σ₁ (CC.id ⊗₁ σ₂) ⟩∘⟨refl) ⟩
    (CC.id ⊗₁ a) CC.∘ ((CC.id ⊗₁ (σ₁ CC.∘ (CC.id ⊗₁ σ₂))) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E})
  ≈⟨ sym-assoc ⟩
    ((CC.id ⊗₁ a) CC.∘ (CC.id ⊗₁ (σ₁ CC.∘ (CC.id ⊗₁ σ₂)))) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E}
  ≈⟨ ⊗ˡ-∘ a (σ₁ CC.∘ (CC.id ⊗₁ σ₂)) ⟩∘⟨refl ⟩
    (CC.id ⊗₁ (a CC.∘ (σ₁ CC.∘ (CC.id ⊗₁ σ₂)))) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E}
  ≈⟨ ⊗₁-resp-≅ᴹ ≅ᴹ-refl swap-coh ⟩∘⟨refl ⟩
    (CC.id ⊗₁ (σ₅ CC.∘ ((σ₃ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖ {E₂} {E₁} {E}))) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E}
  ∎
  where
  a : Machine ((E ⊗₀ E₁) ⊗₀ E₂) (E ⊗₀ (E₁ ⊗₀ E₂))
  a = ⊗-assoc
  σ₁ : Machine (E₂ ⊗₀ (E ⊗₀ E₁)) ((E ⊗₀ E₁) ⊗₀ E₂)
  σ₁ = ⊗-symₘ
  σ₂ : Machine (E₁ ⊗₀ E) (E ⊗₀ E₁)
  σ₂ = ⊗-symₘ
  σ₃ : Machine (E₂ ⊗₀ E₁) (E₁ ⊗₀ E₂)
  σ₃ = ⊗-symₘ
  σ₅ : Machine ((E₁ ⊗₀ E₂) ⊗₀ E) (E ⊗₀ (E₁ ⊗₀ E₂))
  σ₅ = ⊗-symₘ
  -- The associator is natural in its last argument.
  α-nat : (⊗-assoc {D} {E₂} {E ⊗₀ E₁} CC.∘ (CC.id {D ⊗₀ E₂} ⊗₁ σ₂))
          ≅ᴹ ((CC.id {D} ⊗₁ (CC.id {E₂} ⊗₁ σ₂)) CC.∘ ⊗-assoc {D} {E₂} {E₁ ⊗₀ E})
  α-nat = ≅ᴹ-trans (refl⟩∘⟨ ⊗₁-resp-≅ᴹ (≅ᴹ-sym ⊗₁-id) ≅ᴹ-refl)
                   (assoc-commute-from {f = CC.id} {g = CC.id} {h = σ₂})

∘ᴷ-assoc′ : ∀ {A B C D E E₁ E₂}
  (F : Machine C (D ⊗₀ E₂)) (G : Machine B (C ⊗₀ E₁)) (h : Machine A (B ⊗₀ E))
  → ((absorb-regroup CC.∘ (F ⊗₁ CC.id)) CC.∘ (G ∘ᴷ h)) ≅ᴹ ((F ∘ᴷ G) ∘ᴷ h)
∘ᴷ-assoc′ {A} {B} {C} {D} {E} {E₁} {E₂} F G h = ≅ᴹ-trans lhs (≅ᴹ-sym rhs)
  where
  -- The grade morphisms involved.
  σ₁ : Machine ((E₁ ⊗₀ E₂) ⊗₀ E) (E ⊗₀ (E₁ ⊗₀ E₂))
  σ₁ = ⊗-symₘ
  σ₂ : Machine (E₂ ⊗₀ E₁) (E₁ ⊗₀ E₂)
  σ₂ = ⊗-symₘ
  σ₃ : Machine (E₁ ⊗₀ E) (E ⊗₀ E₁)
  σ₃ = ⊗-symₘ
  α⃖ : Machine (E₂ ⊗₀ (E₁ ⊗₀ E)) ((E₂ ⊗₀ E₁) ⊗₀ E)
  α⃖ = ⊗-assoc⃖
  cr : Machine (E₂ ⊗₀ (E₁ ⊗₀ E)) (E ⊗₀ (E₁ ⊗₀ E₂))
  cr = σ₁ CC.∘ ((σ₂ ⊗₁ CC.id) CC.∘ α⃖)

  -- The common core, `F ⊙ (G ⊙ h) = (⊗-assoc ∘ (F ⊗₁ id)) ∘ (G ∙ h)`.
  core : Machine A (D ⊗₀ (E₂ ⊗₀ (E₁ ⊗₀ E)))
  core = F ⊙ (G ⊙ h)

  target : Machine A (D ⊗₀ (E ⊗₀ (E₁ ⊗₀ E₂)))
  target = sub σ₁ CC.∘ (sub (σ₂ ⊗₁ CC.id) CC.∘ (sub α⃖ CC.∘ core))

  rhs : ((F ∘ᴷ G) ∘ᴷ h) ≅ᴹ target
  rhs = begin
      (F ∘ᴷ G) ∘ᴷ h
    ≈⟨ ∘ᴷ-∙ (F ∘ᴷ G) h ⟩
      sub σ₁ CC.∘ (ext E (F ∘ᴷ G) CC.∘ h)
    ≈⟨ refl⟩∘⟨ (ext-resp-≈ (∘ᴷ-∙ F G) ⟩∘⟨refl) ⟩
      sub σ₁ CC.∘ (ext E (sub σ₂ CC.∘ (F ∙ G)) CC.∘ h)
    ≈⟨ refl⟩∘⟨ (sub-commute₂ {u = E} {α = σ₂} {f = F ∙ G} ⟩∘⟨refl) ⟩
      sub σ₁ CC.∘ ((sub (σ₂ ⊗₁ CC.id) CC.∘ ext E (F ∙ G)) CC.∘ h)
    ≈⟨ refl⟩∘⟨ assoc ⟩
      sub σ₁ CC.∘ (sub (σ₂ ⊗₁ CC.id) CC.∘ (ext E (F ∙ G) CC.∘ h))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊙-assoc {f = F} {g = G} {h = h} ⟩
      sub σ₁ CC.∘ (sub (σ₂ ⊗₁ CC.id) CC.∘ (sub α⃖ CC.∘ core))
    ∎

  -- `F ⊗₁ id` is `T₁ _ F`, and `sub` is natural.
  slide : ((F ⊗₁ CC.id {E ⊗₀ E₁}) CC.∘ sub σ₃ {C}) ≅ᴹ (sub σ₃ {D ⊗₀ E₂} CC.∘ (F ⊗₁ CC.id {E₁ ⊗₀ E}))
  slide = begin
      (F ⊗₁ CC.id) CC.∘ sub σ₃          ≈⟨ ≅ᴹ-sym (T₁-⊗ʳ (E ⊗₀ E₁) F) ⟩∘⟨refl ⟩
      T₁ (E ⊗₀ E₁) F CC.∘ sub σ₃        ≈⟨ ≅ᴹ-sym (sub-commute′ {α = σ₃} {f = F}) ⟩
      sub σ₃ CC.∘ T₁ (E₁ ⊗₀ E) F        ≈⟨ refl⟩∘⟨ T₁-⊗ʳ (E₁ ⊗₀ E) F ⟩
      sub σ₃ CC.∘ (F ⊗₁ CC.id)          ∎

  lhs : ((absorb-regroup CC.∘ (F ⊗₁ CC.id)) CC.∘ (G ∘ᴷ h)) ≅ᴹ target
  lhs = begin
      (absorb-regroup CC.∘ (F ⊗₁ CC.id)) CC.∘ (G ∘ᴷ h)
    ≈⟨ refl⟩∘⟨ ∘ᴷ-∙ G h ⟩
      (absorb-regroup CC.∘ (F ⊗₁ CC.id)) CC.∘ (sub σ₃ CC.∘ (G ∙ h))
    ≈⟨ assoc ⟩
      absorb-regroup CC.∘ ((F ⊗₁ CC.id) CC.∘ (sub σ₃ CC.∘ (G ∙ h)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      absorb-regroup CC.∘ (((F ⊗₁ CC.id) CC.∘ sub σ₃) CC.∘ (G ∙ h))
    ≈⟨ refl⟩∘⟨ (slide ⟩∘⟨refl) ⟩
      absorb-regroup CC.∘ ((sub σ₃ CC.∘ (F ⊗₁ CC.id)) CC.∘ (G ∙ h))
    ≈⟨ refl⟩∘⟨ assoc ⟩
      absorb-regroup CC.∘ (sub σ₃ CC.∘ ((F ⊗₁ CC.id) CC.∘ (G ∙ h)))
    ≈⟨ sym-assoc ⟩
      (absorb-regroup CC.∘ sub σ₃) CC.∘ ((F ⊗₁ CC.id) CC.∘ (G ∙ h))
    ≈⟨ regroup-coh ⟩∘⟨refl ⟩
      (sub cr CC.∘ ⊗-assoc) CC.∘ ((F ⊗₁ CC.id) CC.∘ (G ∙ h))
    ≈⟨ assoc ⟩
      sub cr CC.∘ (⊗-assoc CC.∘ ((F ⊗₁ CC.id) CC.∘ (G ∙ h)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      sub cr CC.∘ core
    ≈⟨ sub-homomorphism {α = σ₁} {β = (σ₂ ⊗₁ CC.id) CC.∘ α⃖} ⟩∘⟨refl ⟩
      (sub σ₁ CC.∘ sub ((σ₂ ⊗₁ CC.id) CC.∘ α⃖)) CC.∘ core
    ≈⟨ (refl⟩∘⟨ sub-homomorphism {α = σ₂ ⊗₁ CC.id} {β = α⃖}) ⟩∘⟨refl ⟩
      (sub σ₁ CC.∘ (sub (σ₂ ⊗₁ CC.id) CC.∘ sub α⃖)) CC.∘ core
    ≈⟨ assoc ⟩
      sub σ₁ CC.∘ ((sub (σ₂ ⊗₁ CC.id) CC.∘ sub α⃖) CC.∘ core)
    ≈⟨ refl⟩∘⟨ assoc ⟩
      sub σ₁ CC.∘ (sub (σ₂ ⊗₁ CC.id) CC.∘ (sub α⃖ CC.∘ core))
    ∎

-- ----------------------------------------------------------------------------
-- 3.  `_⊗ᴷ_` is a Kleisli composite of the two one-sided liftings.
--
-- Run `M₂` on the right factor, with its grade pulled out by the associator
-- (a morphism into `T₀ E₂ (A₁ ⊗₀ B₂)`), then run `M₁` on the left factor and
-- pull its grade past `B₂` with the strength `st` (a morphism into
-- `T₀ E₁ (B₁ ⊗₀ B₂)`); the Kleisli composite lands in `T₀ (E₂ ⊗ᵐ E₁) _`, which
-- is `(B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂)`, so no grade swap is needed here.  After
-- `mid4-decomp` both sides share their single crossing, and the solver does
-- the rest.
-- ----------------------------------------------------------------------------

-- The strength `T₀ E₁ B₁ ⊗₀ B₂ → T₀ E₁ (B₁ ⊗₀ B₂)`.
st : ∀ {B₁ E₁ B₂} → Machine ((B₁ ⊗₀ E₁) ⊗₀ B₂) ((B₁ ⊗₀ B₂) ⊗₀ E₁)
st {B₁} {E₁} {B₂} =
  ⊗-assoc⃖ {B₁} {B₂} {E₁} CC.∘ ((CC.id {B₁} ⊗₁ ⊗-symₘ {E₁} {B₂}) CC.∘ ⊗-assoc {B₁} {E₁} {B₂})

⊗ᴷ-∙ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂} (M₁ : Machine A₁ (B₁ ⊗₀ E₁)) (M₂ : Machine A₂ (B₂ ⊗₀ E₂))
     → (M₁ ⊗ᴷ M₂) ≅ᴹ ((st CC.∘ (M₁ ⊗ʳ B₂)) ∙ (⊗-assoc⃖ {A₁} {B₂} {E₂} CC.∘ (A₁ ⊗ˡ M₂)))
⊗ᴷ-∙ {A₁} {B₁} {E₁} {A₂} {B₂} {E₂} M₁ M₂ = begin
    ⊗ᴷ-fwd CC.∘ (M₁ ⊗₁ M₂)
  ≈⟨ ≅ᴹ-trans ⊗ᴷ-fwd-decomp mid4-decomp ⟩∘⟨refl ⟩
    mid4-core CC.∘ (M₁ ⊗₁ M₂)
  ≈⟨ solveMorσ! lhs rhs ⟩
    (⊗-assoc {B₁ ⊗₀ B₂} {E₁} {E₂} CC.∘ ((st CC.∘ (M₁ ⊗₁ CC.id)) ⊗₁ CC.id))
      CC.∘ (⊗-assoc⃖ {A₁} {B₂} {E₂} CC.∘ (CC.id ⊗₁ M₂))
  ∎
  where
  mid4-core : Machine ((B₁ ⊗₀ E₁) ⊗₀ (B₂ ⊗₀ E₂)) ((B₁ ⊗₀ B₂) ⊗₀ (E₁ ⊗₀ E₂))
  mid4-core = ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))) CC.∘ ⊗-assoc)
  vars = A₁ ∷ B₁ ∷ E₁ ∷ A₂ ∷ B₂ ∷ E₂ ∷ []
  open SymAtoms machine-monoidal-category machine-symmetric vars
  open SymSolve machine-monoidal-category machine-symmetric vars
    ( ((V (# 0) , V (# 1) ⊗ᵒ V (# 2)) , M₁)
    ∷ ((V (# 3) , V (# 4) ⊗ᵒ V (# 5)) , M₂) ∷ [] )
  a₁ = V (# 0)
  b₁ = V (# 1)
  e₁ = V (# 2)
  a₂ = V (# 3)
  b₂ = V (# 4)
  e₂ = V (# 5)
  lhs = (S.α⇐ {b₁} {b₂} {e₁ ⊗ᵒ e₂}
         S.∘ ((S.id {b₁} S.⊗₁ (S.α⇒ {b₂} {e₁} {e₂} S.∘ ((S.σ {e₁} {b₂} S.⊗₁ S.id {e₂}) S.∘ S.α⇐ {e₁} {b₂} {e₂})))
              S.∘ S.α⇒ {b₁} {e₁} {b₂ ⊗ᵒ e₂}))
        S.∘ (gen (# 0) S.⊗₁ gen (# 1))
  rhs = (S.α⇒ {b₁ ⊗ᵒ b₂} {e₁} {e₂}
         S.∘ (((S.α⇐ {b₁} {b₂} {e₁} S.∘ ((S.id {b₁} S.⊗₁ S.σ {e₁} {b₂}) S.∘ S.α⇒ {b₁} {e₁} {b₂}))
                S.∘ (gen (# 0) S.⊗₁ S.id {b₂}))
               S.⊗₁ S.id {e₂}))
        S.∘ (S.α⇐ {a₁} {b₂} {e₂} S.∘ (S.id {a₁} S.⊗₁ gen (# 1)))

{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `normalize!` / `normalizeTo!` — rewrite DRIVERS.
--
-- A driver takes a LIST of oriented rules (each a `Rule`: free-SMC sides plus
-- the soundness proof in `C`) and fires the first applicable rule at its
-- first carvable deep position, repeatedly, until no rule applies or the
-- fuel runs out.  The search carries its own proof, so there are no
-- typecheck-time witnesses beyond `normalizeTo!`'s final reconciliation.
--
-- Because the driver re-searches from scratch after every firing, a
-- singleton rule list with sufficient fuel is "rewrite everywhere" — the
-- first test below fires the same rule at two occurrences.  The second test
-- normalises with a two-rule system, where firing one rule exposes the
-- other's redex.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.Drivers
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Categories.Coherence.Symmetric C

--------------------------------------------------------------------------------
-- Configuration: the monoid (m : a ⊗ a → a, u : unit → a), with both unit
-- laws as hypotheses.

module MonoidNormalize (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ)

  a : ObjTerm
  a = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

  arity : Fin 2 → ObjTerm × ObjTerm
  arity zero    = (a ⊗₀ a) , a
  arity (suc _) = unitᵗ , a

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero    → mᴹ
    (suc _) → uᴹ)

  private
    m u : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))

  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒)
           (unitLawʳ : mᴹ ∘ (id ⊗₁ uᴹ) ≈ ρ⇒)
    where

    private
      rules : List Rule
      rules = mkRule (m S.∘ (u S.⊗₁ S.id)) S.λ⇒ unitLawˡ
            ∷ mkRule (m S.∘ (S.id S.⊗₁ u)) S.ρ⇒ unitLawʳ
            ∷ []

    -- One rule, two occurrences: the driver re-searches after each firing,
    -- so both redexes are eliminated ("rewrite everywhere").  Extra fuel is
    -- harmless — the driver stops when no rule applies.
    test-normalize-pair
      : (mᴹ ∘ (uᴹ ⊗₁ id)) ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id)) ≈ λ⇒ ⊗₁ λ⇒
    test-normalize-pair =
      normalizeTo! ((m S.∘ (u S.⊗₁ S.id)) S.⊗₁ (m S.∘ (u S.⊗₁ S.id)))
                   (S.λ⇒ S.⊗₁ S.λ⇒)
                   rules 3

    -- Two rules interleaved: the outer redex is a `unitˡ` instance whose
    -- "second input" is the inner `unitʳ` redex; after the first firing the
    -- inner redex remains and the other rule picks it up.  The fully
    -- normalised diagram is pure wiring, stated as a coherence composite.
    test-normalize-both
      : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ λ⇒ ∘ (id ⊗₁ ρ⇒)
    test-normalize-both =
      normalizeTo! (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))
                   (S.λ⇒ S.∘ (S.id S.⊗₁ S.ρ⇒))
                   rules 3

    -- `normalize!`: land wherever the driver stops, with no stated target
    -- (the `≈ _` form).  Same rule system and fuel as the test above, so the
    -- two together pin the driver's stopping point from both sides.
    test-normalize-open : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ _
    test-normalize-open =
      normalize! rules 3 (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))

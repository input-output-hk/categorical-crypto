{-# OPTIONS --safe --without-K --guardedness #-}

-- A fixed-public-message channel over Σ₀/E₀. The honest receiver gets `n`;
-- Eve gets `enc(n, k, r)` for fresh key and coins. The ideal channel has no
-- Eve output. A non-identity simulator supplies `enc(0, k, r)` independently
-- of the honest wire, and `smt≤ideal` follows from a relational emitter span
-- and dummy completeness. The Eve-only theorems below are preserved.
--
-- This is not an environment-selected-message interactive channel:
-- its message is fixed at the definition site (docs/uc-setup-symbolic.md §6).

module CategoricalCrypto.Symbolic.Example.SecureChannel where

open import Categories.Category.Monoidal.Bundle

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_∘′_; case_of_)
open import Function.Bundles using (Equivalence)
open import Function.Construct.Identity using (↔-id)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Term.PairEnc.Cipher using (cipher-≈ₛ)

open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀ using (Foreign; _≈ₛ_)
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp; void)
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym; ≈ᵁ⇔≈ℰ)
open import CategoricalCrypto.Symbolic.Static Σ₀ E₀ using (≈ₛ⇒≈ℰ; emitter-emits)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀
open import CategoricalCrypto.Symbolic.Static.Relational Σ₀ E₀ using (Emits; module Apex; relsim⇒≈ℰ)
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀ using (Occ; ⟦_⟧[_])
open import CategoricalCrypto.UC.Model.Relational using (HSimᵒ-⊗)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

open Terms Σ₀

private
  module G = MonoidalCategory 𝔾ᵒ

-- The key and the coins.
keys : List ⊤
keys = tt ∷ tt ∷ []

-- The ciphertext of the public constant `n`.
ciphertext : ℕ → All (Rcp keys) (tt ∷ [])
ciphertext n = app enc (app (cst n) [] ∷ var (here refl) ∷ var (there (here refl)) ∷ []) ∷ []

private
  ciphertext-static : ∀ n κ → frame κ keys (ciphertext n) ≈ₛ frame κ keys (ciphertext 0)
  ciphertext-static n κ =
    cipher-≈ₛ {k = κ , 1} {m = app (cst n) []} {m′ = app (cst 0) []} {r = κ , 0} (λ ()) (λ ())

real≈simulated : (n : ℕ) → Emitter keys (ciphertext n) Sym.≈ℰ Emitter keys (ciphertext 0)
real≈simulated n = ≈ₛ⇒≈ℰ (ciphertext-static n)

real≤simulated : (n : ℕ) → Emitter keys (ciphertext n) Sym.≤UC Emitter keys (ciphertext 0)
real≤simulated n = Sym.≈ᵁ⇒≤UC (Equivalence.from ≈ᵁ⇔≈ℰ (real≈simulated n))

honest : ℕ → HomTerm (Var void) (Ports (tt ∷ []))
honest n = Emitter [] (app (cst n) [] ∷ [])

simulator : HomTerm (Var void) (Ports (tt ∷ []))
simulator = Emitter keys (ciphertext 0)

smt : ℕ → HomTerm (Var void ⊗₀ Var void) (Ports (tt ∷ []) ⊗₀ Ports (tt ∷ []))
smt n = Emitter keys (ciphertext n) ⊗₁ honest n

ideal : ℕ → HomTerm (Var void ⊗₀ Var void) (Var void ⊗₀ Ports (tt ∷ []))
ideal n = id ⊗₁ honest n

private
  protocol-emits : (n : ℕ) (ι : Occ (smt n) → ℕ) → Injective _≡_ _≡_ ι
                 → Emits (smt n) (simulator ⊗₁ honest n) (↔-id _) ι
  protocol-emits n ι inj = record
    { φ = P.φ
    ; ψ = P.ψ
    ; equiv = P.equiv
    ; held = λ p → inj₁ (proj₁ (P.held p)) , proj₂ (P.held p)
    ; apex = P.apex G.⊗₁ proj₁ other
    ; left = HSimᵒ-⊗ P.left (proj₁ (proj₂ other))
    ; right = HSimᵒ-⊗ P.right (proj₂ (proj₂ other)) }
    where
    κ = ι (inj₁ tt)
    module P = Emits (emitter-emits {Δ = tt ∷ []} {Ν = keys} {ζs = ciphertext n} {ζs′ = ciphertext 0}
      (ι ∘′ inj₁) (ciphertext-static n κ))

    foreign : ∀ j → Foreign P.φ P.ψ (ι (inj₂ tt) , j)
    foreign j =
      (λ p → case inj {x = inj₂ tt} {y = inj₁ tt} (frame-names κ keys (ciphertext n) p) of λ ())
      , (λ p → case inj {x = inj₂ tt} {y = inj₁ tt} (frame-names κ keys (ciphertext 0) p) of λ ())

    other : Apex.Rel P.φ P.ψ P.equiv (Var void) (Ports (tt ∷ [])) ⟦ honest n ⟧[ ι ∘′ inj₂ ]
    other = Apex.context P.φ P.ψ P.equiv (honest n) (ι ∘′ inj₂) λ _ → foreign

smt≈simulated : ∀ n → smt n Sym.≈ℰ (simulator ⊗₁ honest n)
smt≈simulated n = relsim⇒≈ℰ (↔-id _) (protocol-emits n)

private
  simulator-shape : ∀ n → Sym.sub simulator ∘ ideal n ≈Term simulator ⊗₁ honest n
  simulator-shape n = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ idʳ idˡ)

smt≤ideal : ∀ n → smt n Sym.≤UC ideal n
smt≤ideal n = Sym.dummy-complete
  (simulator , Sym.≈ᵁ-trans (Equivalence.from ≈ᵁ⇔≈ℰ (smt≈simulated n))
    (Sym.≈ᵁ-sym (Sym.≈C⇒≈ᵁ (simulator-shape n))))

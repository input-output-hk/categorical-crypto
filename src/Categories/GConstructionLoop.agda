{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Re-bracketing the loop object of a trace along the middle-four
-- interchange `mid`.  Splitting both loops into four single-wire traces
-- with `vanishing₂` leaves the same four wires in the orders P,R,Q,S and
-- P,Q,R,S; one `trace-comm` (Fubini) step transposes the middle two, and
-- the remaining residue is the pure coherence
-- `Categories.GConstructionLoopCoherence.LC`.
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced

module Categories.GConstructionLoop
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

open import Categories.Category.Monoidal.Bundle

import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionLoopCoherence as GLoopCoh
import Categories.GConstructionTrace as GT

open GT C Monoidal Traced using (β; mid)

private
  module C where
    open Category C public
    open Traced Traced public
    open U.Shorthands Monoidal public

  Cˢ : SymmetricMonoidalCategory a b c
  Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

open C.HomReasoning

module WithTrace
  (trace-resp-≈ : ∀ {X A B} {f g : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                  f C.≈ g → C.trace f C.≈ C.trace g)
  (trace-∘ˡ : ∀ {X A B B'} {g : B C.⇒ B'} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
              g C.∘ C.trace f C.≈ C.trace (g C.⊗₁ C.id C.∘ f))
  (trace-∘ʳ : ∀ {X A A' B} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} {h : A' C.⇒ A} →
              C.trace f C.∘ h C.≈ C.trace (f C.∘ h C.⊗₁ C.id))
  (trace-comm : ∀ {X Y A B} {f : (A C.⊗₀ X) C.⊗₀ Y C.⇒ (B C.⊗₀ X) C.⊗₀ Y} →
                C.trace (C.trace f) C.≈ C.trace (C.trace (β C.∘ f C.∘ β)))
  where

  -- Conjugating a trace by a pre- and a post-composition pushes both into
  -- the loop body; this is what turns each `vanishing₂` split's associators
  -- into a `_⊗₁ id`-padded pair inside the next body.
  trace-conj : ∀ {X A A' B B'} {t : A C.⊗₀ X C.⇒ B C.⊗₀ X}
                 {h : A' C.⇒ A} {k : B C.⇒ B'} →
               k C.∘ C.trace t C.∘ h C.≈ C.trace (k C.⊗₁ C.id C.∘ t C.∘ h C.⊗₁ C.id)
  trace-conj = (refl⟩∘⟨ trace-∘ʳ) ○ trace-∘ˡ

  trace-mid : ∀ {A B P Q R S : C.Obj}
                {f : A C.⊗₀ ((P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S)) C.⇒
                     B C.⊗₀ ((P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S))} →
              C.trace f C.≈
              C.trace (C.id C.⊗₁ mid {P} {R} {Q} {S} C.∘ f C.∘ C.id C.⊗₁ mid {P} {Q} {R} {S})
  trace-mid {A} {B} {P} {Q} {R} {S} {f} = begin
    C.trace f
      ≈⟨ ⟺ C.vanishing₂ ⟩
    C.trace (C.trace f₁)
      ≈⟨ ⟺ C.vanishing₂ ⟩
    C.trace (C.trace (C.α⇐ C.∘ C.trace f₁ C.∘ C.α⇒))
      ≈⟨ trace-resp-≈ (trace-resp-≈ trace-conj) ⟩
    C.trace (C.trace (C.trace f₂))
      ≈⟨ trace-resp-≈ (trace-resp-≈ (⟺ C.vanishing₂)) ⟩
    C.trace (C.trace (C.trace (C.trace f₃)))
      ≈⟨ trace-resp-≈ trace-comm ⟩
    C.trace (C.trace (C.trace (β C.∘ C.trace f₃ C.∘ β)))
      ≈⟨ trace-resp-≈ (trace-resp-≈ (trace-resp-≈ trace-conj)) ⟩
    C.trace (C.trace (C.trace (C.trace (β C.⊗₁ C.id C.∘ f₃ C.∘ β C.⊗₁ C.id))))
      ≈⟨ trace-resp-≈ (trace-resp-≈ (trace-resp-≈ (trace-resp-≈ residue))) ⟩
    C.trace (C.trace (C.trace (C.trace g₃)))
      ≈⟨ trace-resp-≈ (trace-resp-≈ C.vanishing₂) ⟩
    C.trace (C.trace (C.trace g₂))
      ≈⟨ trace-resp-≈ (trace-resp-≈ (⟺ trace-conj)) ⟩
    C.trace (C.trace (C.α⇐ C.∘ C.trace g₁ C.∘ C.α⇒))
      ≈⟨ C.vanishing₂ ⟩
    C.trace (C.trace g₁)
      ≈⟨ C.vanishing₂ ⟩
    C.trace g
    ∎
    where
      g : A C.⊗₀ ((P C.⊗₀ Q) C.⊗₀ (R C.⊗₀ S)) C.⇒
          B C.⊗₀ ((P C.⊗₀ Q) C.⊗₀ (R C.⊗₀ S))
      g = C.id C.⊗₁ mid C.∘ f C.∘ C.id C.⊗₁ mid
      f₁ = C.α⇐ C.∘ f C.∘ C.α⇒
      f₂ = C.α⇐ C.⊗₁ C.id C.∘ f₁ C.∘ C.α⇒ C.⊗₁ C.id
      f₃ = C.α⇐ C.∘ f₂ C.∘ C.α⇒
      g₁ = C.α⇐ C.∘ g C.∘ C.α⇒
      g₂ = C.α⇐ C.⊗₁ C.id C.∘ g₁ C.∘ C.α⇒ C.⊗₁ C.id
      g₃ = C.α⇐ C.∘ g₂ C.∘ C.α⇒
      residue = GLoopCoh.Transport.WithGen.LC Cˢ A B P Q R S f

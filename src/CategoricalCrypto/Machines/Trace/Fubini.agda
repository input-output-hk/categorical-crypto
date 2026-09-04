{-# OPTIONS --safe --without-K #-}

-- `trace-comm`, the ⊕-trace's Fubini law: two nested traces may be exchanged.
--
-- It needs no new iteration content.  `vanishing₂` already fuses each side into
-- a single trace — over `X + P` on the left, over `P + X` on the right — and
-- what is left is that the trace does not see a pure iso of its loop variable.
-- That last fact (`relabel-step`) is one `iter-transfer` at `id ⊗₁ s`: an
-- invertible pure reindexing of the loop wire is replayed on both sides of the
-- loop, and the two `id`s it inserts cancel.
--
-- `βᴹ` is a machine composite, so the first move is to recognize it as the pure
-- machine of `β+ = α+⇐ ∘ (id +₁ +-swap) ∘ α+⇒`; the two associators of the
-- fusion then cancel against `β+`'s own (`α+⇒-β+`, `β+-α+⇐`), which is why the
-- swap that survives is `+-swap` alone.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as Congruence
import CategoricalCrypto.Machines.Trace.Vanishing as Vanishing

module CategoricalCrypto.Machines.Trace.Fubini
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Congruence 𝒱 dist 𝒫 E
open Core 𝒱
open Equiv
open Frame 𝒱
open Iteration.Elgot E
open MCat 𝒱 𝒫 using (∘ᴹ-resp-≈ᴹ)
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E
open Vanishing 𝒱 dist 𝒫 E using ([]-δ⇐; vanish-step)

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

open CE U cocartesian

private variable A B P X : Obj

------------------------------------------------------------------------
-- The ⊕-side swap `βᴹ` acts by

β+ : {A B C : Obj} → (A + B) + C ⇒ (A + C) + B
β+ = α+⇐ ∘ (id +₁ +-swap) ∘ α+⇒

pure-swap : Pure (+-swap {A} {B})
pure-swap = pure-resp-≈ (+-unique +-swap-i₁ +-swap-i₂) (pure-[] pure-i₂ pure-i₁)

α+⇒-β+ : α+⇒ {A} {P} {X} ∘ β+ {A} {X} {P} ≈ (id +₁ +-swap) ∘ α+⇒
α+⇒-β+ = cancelˡ ⊕.associator.isoʳ

β+-α+⇐ : β+ {A} {P} {X} ∘ α+⇐ ≈ α+⇐ {A} {X} {P} ∘ (id +₁ +-swap)
β+-α+⇐ = assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ ⊕.associator.isoʳ) ○ identityʳ))

βᴹ-pure : βᴹ {A} {X} {P} ≈ᴹ pureᴹ β+
βᴹ-pure = ∘ᴹ-resp-≈ᴹ reflᴹ inner ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ α+⇐ _)
  where
    tensor : (idᴹ ⊗ᵉ σᴹ) ≈ᴹ pureᴹ (id +₁ +-swap)
    tensor = ≲⇒≈ᴹ˘ (⊗ᵉ-resp-≲ pureᴹ-id ≲-refl) ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ id +-swap)

    inner : ((idᴹ ⊗ᵉ σᴹ) ∘ᴹ α⇒ᴹ) ≈ᴹ pureᴹ ((id +₁ +-swap) ∘ α+⇒)
    inner = ∘ᴹ-resp-≈ᴹ tensor reflᴹ ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ (id +₁ +-swap) α+⇒)

------------------------------------------------------------------------
-- The trace does not see a pure iso of its loop variable

module _ (V : State) (A B X X′ : Obj) (s : X ⇒ X′) (s⁻ : X′ ⇒ X)
  (sᵖ : Pure s) (s-inv : s⁻ ∘ s ≈ id)
  (k : obj V ⊗₀ (A + X) ⇒ obj V ⊗₀ (B + X)) where

  private
    k♯ : obj V ⊗₀ (A + X′) ⇒ obj V ⊗₀ (B + X′)
    k♯ = id ⊗₁ (id +₁ s) ∘ (k ∘ id ⊗₁ (id +₁ s⁻))

    tstep-relabel : tstep (id {obj V ⊗₀ B}) (id ⊗₁ s) ≈ id ⊗₁ (id +₁ s)
    tstep-relabel = tstep-cong (⟺ ⊗.identity) refl ○ tstep-str id s

    loop-relabel : loopBody V A B X′ k♯
                 ≈ id ⊗₁ (id +₁ s) ∘ (loopBody V A B X k ∘ id ⊗₁ s⁻)
    loop-relabel = assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ shift))) ○ (refl⟩∘⟨ sym-assoc)
      where
        shift : id ⊗₁ (id +₁ s⁻) ∘ id ⊗₁ i₂ {A} {X′} ≈ id ⊗₁ i₂ {A} {X} ∘ id ⊗₁ s⁻
        shift = merge₂ˡ ○ (refl⟩⊗⟨ +₁∘i₂) ○ split₂ˡ

    iter-relabel : iter (loopBody V A B X′ k♯) ∘ id ⊗₁ s ≈ iter (loopBody V A B X k)
    iter-relabel =
      iter-transfer (id ⊗₁ s) id (pure-⊗₁ pure-id sᵖ) pure-id
                    {loopBody V A B X k} {loopBody V A B X′ k♯} hyp
      ○ identityˡ
      where
        cancel-s : id ⊗₁ s⁻ ∘ id ⊗₁ s ≈ id
        cancel-s = merge₂ˡ ○ (refl⟩⊗⟨ s-inv) ○ ⊗.identity

        hyp : loopBody V A B X′ k♯ ∘ id ⊗₁ s
            ≈ tstep id (id ⊗₁ s) ∘ loopBody V A B X k
        hyp = (loop-relabel ⟩∘⟨refl) ○ assoc
            ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ cancel-s) ○ identityʳ))
            ○ ⟺ (tstep-relabel ⟩∘⟨refl)

    solve-relabel : solve V A B X′ k♯ ∘ id ⊗₁ (id +₁ s) ≈ solve V A B X k
    solve-relabel = assoc ○ []-δ⇐ id s
                  ○ ([]-cong₂ (identityˡ ○ ⊗.identity) iter-relabel ⟩∘⟨refl)

  relabel-step : traceStep V A B X′ k♯ ≈ traceStep V A B X k
  relabel-step = (refl⟩∘⟨ enter) ○ sym-assoc ○ (solve-relabel ⟩∘⟨refl)
    where
      enter : k♯ ∘ id ⊗₁ i₁ {A} {X′} ≈ id ⊗₁ (id +₁ s) ∘ (k ∘ id ⊗₁ i₁ {A} {X})
      enter = assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ shift)))
        where
          shift : id ⊗₁ (id +₁ s⁻) ∘ id ⊗₁ i₁ {A} {X′} ≈ id ⊗₁ i₁ {A} {X}
          shift = merge₂ˡ ○ (refl⟩⊗⟨ (+₁∘i₁ ○ identityʳ))

------------------------------------------------------------------------
-- Exchanging the two loops

-- Both fusions and both `β+`s are two-sided interface relabellings, so each
-- side normalizes to the same shape before the ⊕-identities are applied.
norm : {S A₁ A₂ A₃ B₁ B₂ B₃ : Obj} (r₁ : A₁ ⇒ A₂) (r₂ : A₂ ⇒ A₃)
       (l₁ : B₁ ⇒ B₂) (l₂ : B₂ ⇒ B₃) (n : S ⊗₀ A₃ ⇒ S ⊗₀ B₁)
     → id ⊗₁ l₂ ∘ ((id ⊗₁ l₁ ∘ (n ∘ id ⊗₁ r₂)) ∘ id ⊗₁ r₁)
     ≈ id ⊗₁ (l₂ ∘ l₁) ∘ (n ∘ id ⊗₁ (r₂ ∘ r₁))
norm _ _ _ _ _ = (refl⟩∘⟨ assoc) ○ sym-assoc
               ○ (merge₂ˡ ⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ)))

module _ (V : State) (A B X P : Obj)
  (m : obj V ⊗₀ ((A + X) + P) ⇒ obj V ⊗₀ ((B + X) + P)) where

  private
    m′ : obj V ⊗₀ ((A + P) + X) ⇒ obj V ⊗₀ ((B + P) + X)
    m′ = id ⊗₁ β+ ∘ (m ∘ id ⊗₁ β+)

    k₁ : obj V ⊗₀ (A + (X + P)) ⇒ obj V ⊗₀ (B + (X + P))
    k₁ = id ⊗₁ α+⇒ ∘ (m ∘ id ⊗₁ α+⇐)

    k₂ : obj V ⊗₀ (A + (P + X)) ⇒ obj V ⊗₀ (B + (P + X))
    k₂ = id ⊗₁ α+⇒ ∘ (m′ ∘ id ⊗₁ α+⇐)

    -- The fusion's two associators cancel, so the fused body is `m` again.
    round : {A₀ B₀ X₀ P₀ : Obj}
            (n : obj V ⊗₀ ((A₀ + X₀) + P₀) ⇒ obj V ⊗₀ ((B₀ + X₀) + P₀))
          → id ⊗₁ α+⇐ ∘ ((id ⊗₁ α+⇒ ∘ (n ∘ id ⊗₁ α+⇐)) ∘ id ⊗₁ α+⇒) ≈ n
    round n = norm α+⇒ α+⇐ α+⇒ α+⇐ n
            ○ ((refl⟩⊗⟨ ⊕.associator.isoˡ) ⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ⊕.associator.isoˡ)))
            ○ (⊗.identity ⟩∘⟨ (refl⟩∘⟨ ⊗.identity)) ○ identityˡ ○ identityʳ

    left : traceStep V A B X (traceStep V (A + X) (B + X) P m)
         ≈ traceStep V A B (X + P) k₁
    left = traceStep-cong V A B X
             (traceStep-cong V (A + X) (B + X) P (⟺ (round m)))
         ○ vanish-step V A B X P k₁

    right : traceStep V A B P (traceStep V (A + P) (B + P) X m′)
          ≈ traceStep V A B (P + X) k₂
    right = traceStep-cong V A B P
              (traceStep-cong V (A + P) (B + P) X (⟺ (round m′)))
          ○ vanish-step V A B P X k₂

    k₂-relabel : k₂ ≈ id ⊗₁ (id +₁ +-swap) ∘ (k₁ ∘ id ⊗₁ (id +₁ +-swap))
    k₂-relabel = norm α+⇐ β+ β+ α+⇒ m
               ○ ((refl⟩⊗⟨ α+⇒-β+) ⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ β+-α+⇐)))
               ○ ⟺ (norm (id +₁ +-swap) α+⇐ α+⇒ (id +₁ +-swap) m)

    swap : traceStep V A B (X + P) k₁ ≈ traceStep V A B (P + X) k₂
    swap = ⟺ (relabel-step V A B (X + P) (P + X) +-swap +-swap pure-swap
                           +-swap∘swap k₁)
         ○ ⟺ (traceStep-cong V A B (P + X) k₂-relabel)

  comm-step : traceStep V A B X (traceStep V (A + X) (B + X) P m)
            ≈ traceStep V A B P
                (traceStep V (A + P) (B + P) X (id ⊗₁ β+ ∘ (m ∘ id ⊗₁ β+)))
  comm-step = left ○ swap ○ ⟺ right

trace-comm : {A B P X : Obj} (f : Machine ((A + X) + P) ((B + X) + P))
           → traceᴹ A B X (traceᴹ (A + X) (B + X) P f)
           ≈ᴹ traceᴹ A B P (traceᴹ (A + P) (B + P) X (βᴹ ∘ᴹ f ∘ᴹ βᴹ))
trace-comm {A} {B} {P} {X} f =
  ≲⇒≈ᴹ (mk-cong (comm-step (state f) A B X P (step f)))
  ○ᴹ ⟺ᴹ (trace-resp-≈ᴹ (trace-resp-≈ᴹ reduce))
  where
    reduce : (βᴹ ∘ᴹ f ∘ᴹ βᴹ) ≈ᴹ mk (state f) (id ⊗₁ β+ ∘ (step f ∘ id ⊗₁ β+))
    reduce = ∘ᴹ-resp-≈ᴹ βᴹ-pure (∘ᴹ-resp-≈ᴹ reflᴹ βᴹ-pure ○ᴹ ≲⇒≈ᴹ (pure-∘ʳ β+ f))
           ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ β+ (mk (state f) (step f ∘ id ⊗₁ β+)))

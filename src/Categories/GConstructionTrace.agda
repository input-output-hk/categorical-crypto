{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The wiring and the trace algebra the G construction runs on: the
-- structural morphisms `β`, `α`, `γ` of a G-composite's loop body, `mid`
-- for its monoidal structure, and the consequences of the trace
-- hypotheses that its laws need.
--
-- `β`, `α`, `γ` and the three yanking/superposing lemmas were
-- `where`-local to `Categories.GConstruction`'s category literal; the
-- monoidal layer needs the same lemmas, so they live here instead.
-- `right-superposing` is the mirror of `Traced.superposing` and is the
-- one that needs a coherence step (`RS`, solved in
-- `Categories.GConstructionIdentityCoherence`); `⊗-trace`/`⊗-trace-mid`
-- are the traced category's own "the trace is monoidal".
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced

module Categories.GConstructionTrace
  {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where


import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Interchange.Braided as IB
import Categories.Category.Monoidal.Interchange.Symmetric as IS
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionIdentityCoherence as GCohId
import Categories.GConstructionTraceCoherence as TCoh

private
  module C where
    open Category C public
    open Traced Traced public
    open U.Shorthands Monoidal public
    open import Categories.Category.Monoidal.Reasoning Monoidal public
      using (serialize₁₂; refl⟩⊗⟨_)
    open import Categories.Morphism.Reasoning C public using (introˡ; pullʳ; elimʳ)
    open BProps.Shorthands braided public

  Cˢ : SymmetricMonoidalCategory a b c
  Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

open C.HomReasoning

-- β swaps the last two factors: (A ⊗ Y) ⊗ X → (A ⊗ X) ⊗ Y
β : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (P C.⊗₀ R) C.⊗₀ Q
β = C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

-- The two coherence isomorphisms of the G-construction composition: `α`
-- routes the two loop ends together after the factors have acted, `γ`
-- feeds them in.
α : ∀ {A⁻ B⁺ B⁻ C⁺ : C.Obj} →
    (B⁻ C.⊗₀ C⁺) C.⊗₀ (A⁻ C.⊗₀ B⁺) C.⇒ (A⁻ C.⊗₀ C⁺) C.⊗₀ (B⁻ C.⊗₀ B⁺)
α = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id) C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒

γ : ∀ {A⁺ B⁺ B⁻ C⁻ : C.Obj} →
    (A⁺ C.⊗₀ C⁻) C.⊗₀ (B⁻ C.⊗₀ B⁺) C.⇒ (B⁺ C.⊗₀ C⁻) C.⊗₀ (A⁺ C.⊗₀ B⁻)
γ = C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐ C.∘ C.id C.⊗₁ (C.σ⇒ C.⊗₁ C.id)
  C.∘ C.id C.⊗₁ C.α⇐ C.∘ C.α⇒ C.∘ C.id C.⊗₁ C.σ⇒

-- The middle-four interchange, the only structural morphism the
-- G-construction's tensor of morphisms needs.  It is upstream's
-- `Interchange.Braided.swapInner.from`, spelled out so that the
-- conversion checker meets the composite directly; the involution, the
-- naturality and the braiding law below are upstream's, read at that
-- spelling.
mid : ∀ {P Q R S : C.Obj} →
      (P C.⊗₀ Q) C.⊗₀ (R C.⊗₀ S) C.⇒ (P C.⊗₀ R) C.⊗₀ (Q C.⊗₀ S)
mid = C.α⇐ C.∘ C.id C.⊗₁ (C.α⇒ C.∘ C.σ⇒ C.⊗₁ C.id C.∘ C.α⇐) C.∘ C.α⇒

mid-involutive : ∀ {P Q R S : C.Obj} → mid {P} {Q} {R} {S} C.∘ mid C.≈ C.id
mid-involutive = IS.swapInner-commutative C.symmetric

mid-natural : ∀ {P P′ Q Q′ R R′ S S′ : C.Obj}
                {f : P C.⇒ P′} {g : Q C.⇒ Q′} {h : R C.⇒ R′} {k : S C.⇒ S′} →
              mid C.∘ (f C.⊗₁ g) C.⊗₁ (h C.⊗₁ k)
              C.≈ (f C.⊗₁ h) C.⊗₁ (g C.⊗₁ k) C.∘ mid
mid-natural = IB.swapInner-natural C.braided

mid-braiding : ∀ {P Q R S : C.Obj} →
               mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒ C.∘ mid {P} {Q} {R} {S} C.≈ C.σ⇒
mid-braiding = IB.swapInner-braiding C.braided

-- `mid-braiding` with one copy of `mid` cancelled: `mid` intertwines the
-- braiding with its own tensor square.
mid-σ : ∀ {P Q R S : C.Obj} →
        mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒ C.≈ C.σ⇒ C.∘ mid {P} {R} {Q} {S}
mid-σ = begin
  mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒                       ≈˘⟨ C.identityʳ ⟩
  (mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒) C.∘ C.id            ≈˘⟨ refl⟩∘⟨ mid-involutive ⟩
  (mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒) C.∘ mid C.∘ mid     ≈⟨ C.sym-assoc ⟩
  ((mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒) C.∘ mid) C.∘ mid   ≈⟨ C.assoc ⟩∘⟨refl ⟩
  (mid C.∘ C.σ⇒ C.⊗₁ C.σ⇒ C.∘ mid) C.∘ mid     ≈⟨ mid-braiding ⟩∘⟨refl ⟩
  C.σ⇒ C.∘ mid                                 ∎

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

  -- trace of the yanking core: β at Q = R = X swaps the loop wire with a
  -- parallel copy of itself, so its trace is the identity.
  trace-βyank : ∀ {Y X : C.Obj} → C.trace (β {Y} {X} {X}) C.≈ C.id
  trace-βyank = C.superposing ○ (C.refl⟩⊗⟨ C.yanking) ○ C.⊗.identity

  -- framed yanking: a loop whose body is a yanking core followed by
  -- loop-independent processing g collapses to g.
  trace-gyank : ∀ {Y X B' : C.Obj} {g : Y C.⊗₀ X C.⇒ B'} →
                C.trace (g C.⊗₁ C.id C.∘ β {Y} {X} {X}) C.≈ g
  trace-gyank = ⟺ trace-∘ˡ ○ C.elimʳ trace-βyank

  -- Right superposing, the mirror of `Traced.superposing`.
  right-superposing : ∀ {X Y A' B'} {f' : A' C.⊗₀ X C.⇒ B' C.⊗₀ X} →
    C.trace f' C.⊗₁ C.id {Y} C.≈ C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
  right-superposing {X} {Y} {A'} {B'} {f'} = begin
    C.trace f' C.⊗₁ C.id
      ≈⟨ braiding-swap ⟩
    C.σ⇒ C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
      ≈⟨ refl⟩∘⟨ C.Equiv.sym C.superposing ⟩∘⟨refl ⟩
    C.σ⇒ C.∘ C.trace (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒
      ≈⟨ refl⟩∘⟨ trace-∘ʳ ⟩
    C.σ⇒ C.∘ C.trace ((C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
      ≈⟨ trace-∘ˡ ⟩
    C.trace (C.σ⇒ C.⊗₁ C.id C.∘ (C.α⇐ C.∘ C.id C.⊗₁ f' C.∘ C.α⇒) C.∘ C.σ⇒ C.⊗₁ C.id)
      ≈⟨ trace-resp-≈ (GCohId.Transport.WithGen.RS Cˢ A' B' X X Y f') ⟩
    C.trace (β C.∘ f' C.⊗₁ C.id C.∘ β)
    ∎
    where -- introduce σ⇒ ∘ σ⇒ ≈ id on the left, then braiding naturality
          braiding-swap : C.trace f' C.⊗₁ C.id C.≈
            C.σ⇒ {Y} {B'} C.∘ C.id C.⊗₁ C.trace f' C.∘ C.σ⇒
          braiding-swap = C.introˡ C.commutative
                        ○ C.pullʳ (C.braiding.⇒.commute _)

  -- A tensor of traces is one nested double trace: serialize, superpose
  -- each factor over the other's loop, then merge with the two
  -- naturalities.  No coherence step and no Fubini — the two loops keep
  -- the order the serialization gave them.
  ⊗-trace : ∀ {X Y A A' B B' : C.Obj}
              {u : A C.⊗₀ X C.⇒ B C.⊗₀ X} {v : A' C.⊗₀ Y C.⇒ B' C.⊗₀ Y} →
            C.trace u C.⊗₁ C.trace v C.≈
            C.trace (C.trace ((β C.∘ u C.⊗₁ C.id C.∘ β) C.⊗₁ C.id C.∘ β
                              C.∘ (C.α⇐ C.∘ C.id C.⊗₁ v C.∘ C.α⇒) C.⊗₁ C.id C.∘ β))
  ⊗-trace {X} {Y} {A} {A'} {B} {B'} {u} {v} = begin
    C.trace u C.⊗₁ C.trace v
      ≈⟨ C.serialize₁₂ ⟩
    C.trace u C.⊗₁ C.id C.∘ C.id C.⊗₁ C.trace v
      ≈⟨ right-superposing ⟩∘⟨ C.Equiv.sym C.superposing ⟩
    C.trace body₁ C.∘ C.trace body₂
      ≈⟨ trace-∘ʳ ⟩
    C.trace (body₁ C.∘ C.trace body₂ C.⊗₁ C.id)
      ≈⟨ trace-resp-≈ (refl⟩∘⟨ right-superposing) ⟩
    C.trace (body₁ C.∘ C.trace (β C.∘ body₂ C.⊗₁ C.id C.∘ β))
      ≈⟨ trace-resp-≈ trace-∘ˡ ⟩
    C.trace (C.trace (body₁ C.⊗₁ C.id C.∘ β C.∘ body₂ C.⊗₁ C.id C.∘ β))
    ∎
    where body₁ = β C.∘ u C.⊗₁ C.id {B'} C.∘ β
          body₂ = C.α⇐ C.∘ C.id {A} C.⊗₁ v C.∘ C.α⇒

  -- …and that double trace is one trace over `X ⊗ Y`: the β-conjugations
  -- `⊗-trace` leaves are the middle-four interchange of `u ⊗ v` (`TM`), so
  -- `vanishing₂` merges the loops.  This is the traced category's own
  -- "trace is monoidal", with no G-construction wiring in it.
  ⊗-trace-mid : ∀ {X Y A A' B B' : C.Obj}
                  {u : A C.⊗₀ X C.⇒ B C.⊗₀ X} {v : A' C.⊗₀ Y C.⇒ B' C.⊗₀ Y} →
                C.trace u C.⊗₁ C.trace v C.≈ C.trace (mid C.∘ u C.⊗₁ v C.∘ mid)
  ⊗-trace-mid {X} {Y} {A} {A'} {B} {B'} {u} {v} =
    ⊗-trace
    ○ trace-resp-≈ (trace-resp-≈ (TCoh.Transport.WithGens.TM Cˢ A A' B B' X Y u v))
    ○ C.vanishing₂

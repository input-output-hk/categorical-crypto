{-# OPTIONS --safe --without-K #-}

-- SPIKE: what the general `trace-∘` needs.
--
-- Composing machines pairs their states; unrolling them pairs their interfaces.
-- `trace-∘` says the two pairings commute, and its content is the interchange
-- of two actions that touch complementary tensor factors — at `𝒱 = Kleisli M`
-- that interchange IS the monad's commutativity, which is why the elementwise
-- layer needs `Discrete.Commutative` for exactly this lemma and nothing else.
--
-- The solver (`solveMorσ!`) discharges every step in which the generator's
-- padding is already on one side and no crossing block has to be split.  What
-- it leaves is exactly its two documented limitations: `lim-straddle` (moving a
-- padding across the generator) and `lim-hexagon` (splitting `σ` over a tensor);
-- `unbraid`/`repad` and `σ-splitˡ`/`σ-splitʳ` are those two by hand.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Frontend.Sigma
open import Categories.Coherence.Monoidal.Sigma
open import Categories.FreeMonoidal
import Categories.Coherence.Monoidal as Coh

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (_∷_; [])

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Interchange {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Mealy 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B K₁ K₂ L P Q R W W′ X Y Z : Obj

-- The solver front-end wants the `MonoidalCategory` bundle.
𝕄 : MonoidalCategory o ℓ e
𝕄 = record { U = U ; monoidal = monoidal }

------------------------------------------------------------------------
-- State-changing versions of `Spike.Mealy`'s slots
------------------------------------------------------------------------

-- `Mealy`'s `slot₁`/`slot₂` force the step to preserve the state object, so
-- they do not accept a state braiding; these are the same terms with the
-- codomain state freed, hence definitionally `slot₁`/`slot₂` where both apply.
slot₁ᵍ : (P ⊗₀ X ⇒ R ⊗₀ Y) → P ⊗₀ (X ⊗₀ Z) ⇒ R ⊗₀ (Y ⊗₀ Z)
slot₁ᵍ k = α⇒ ∘ k ⊗₁ id ∘ α⇐

slot₂ᵍ : (P ⊗₀ X ⇒ R ⊗₀ Y) → P ⊗₀ (Z ⊗₀ X) ⇒ R ⊗₀ (Z ⊗₀ Y)
slot₂ᵍ k = untuck ∘ k ⊗₁ id ∘ tuck

------------------------------------------------------------------------
-- The shuffles are involutions
------------------------------------------------------------------------

σ-pad-inv : id {L} ⊗₁ σ⇒ ∘ id ⊗₁ σ⇒ ≈ id {L ⊗₀ (Q ⊗₀ X)}
σ-pad-inv = merge₂ˡ ○ refl⟩⊗⟨ commutative ○ ⊗.identity

swp-swp : swp ∘ swp ≈ id {(P ⊗₀ Q) ⊗₀ X}
swp-swp = center (cancelʳ associator.isoʳ) ○ refl⟩∘⟨ cancelˡ σ-pad-inv ○ associator.isoˡ

untuck-tuck : untuck ∘ tuck ≈ id {P ⊗₀ (Q ⊗₀ X)}
untuck-tuck = cancelInner associator.isoʳ ○ σ-pad-inv

tuck-untuck : tuck ∘ untuck ≈ id {(P ⊗₀ X) ⊗₀ Q}
tuck-untuck = cancelInner σ-pad-inv ○ associator.isoˡ

Ω-involutive : Ω {P} {X} {Q} {Z} ∘ Ω {P} {Q} {X} {Z} ≈ id
Ω-involutive = center (cancelʳ associator.isoˡ)
             ○ (refl⟩∘⟨ pullˡ (merge₁ˡ ○ (swp-swp ⟩⊗⟨refl) ○ ⊗.identity))
             ○ (refl⟩∘⟨ identityˡ) ○ associator.isoʳ

------------------------------------------------------------------------
-- Padding a generator
------------------------------------------------------------------------

-- The solver decides a goal only when the generator's padding lies inside one
-- image block of every crossing it must cross; a straddling box does not slide
-- (`lim-straddle` in `Categories.Coherence.Monoidal.Test.Limitations`).  The
-- lemmas here are the hand steps that move a padding into that position, so
-- that what is left over for the solver is generator-free.

-- Both sides are `h ⊗₁ s`: the generator never sees its padding.
pad-transport : (h : K₁ ⇒ K₂) (s : W ⇒ W′) → id ⊗₁ s ∘ h ⊗₁ id ≈ h ⊗₁ id ∘ id ⊗₁ s
pad-transport _ _ = parallel id-comm-sym id-comm

-- A left padding is a braided right padding.
pad-braid : (L : Obj) (h : K₁ ⇒ K₂) → id {L} ⊗₁ h ≈ σ⇒ ∘ h ⊗₁ id ∘ σ⇒
pad-braid L h = begin
  id ⊗₁ h              ≈⟨ insertˡ commutative ⟩
  σ⇒ ∘ (σ⇒ ∘ id ⊗₁ h)  ≈⟨ refl⟩∘⟨ braiding.⇒.commute (id , h) ⟩
  σ⇒ ∘ (h ⊗₁ id ∘ σ⇒)  ∎

-- …and so a left-padded conjugate is a right-padded one.
unbraid : (h : K₁ ⇒ K₂) {i : A ⇒ L ⊗₀ K₁} {o : L ⊗₀ K₂ ⇒ B}
        → o ∘ id ⊗₁ h ∘ i ≈ (o ∘ σ⇒) ∘ h ⊗₁ id ∘ (σ⇒ ∘ i)
unbraid {L = L} h {i} {o} = begin
  o ∘ (id ⊗₁ h ∘ i)                ≈⟨ refl⟩∘⟨ pad-braid L h ⟩∘⟨refl ⟩
  o ∘ ((σ⇒ ∘ (h ⊗₁ id ∘ σ⇒)) ∘ i)  ≈⟨ refl⟩∘⟨ assoc ⟩
  o ∘ (σ⇒ ∘ ((h ⊗₁ id ∘ σ⇒) ∘ i))  ≈⟨ sym-assoc ⟩
  (o ∘ σ⇒) ∘ ((h ⊗₁ id ∘ σ⇒) ∘ i)  ≈⟨ refl⟩∘⟨ assoc ⟩
  (o ∘ σ⇒) ∘ (h ⊗₁ id ∘ (σ⇒ ∘ i))  ∎

-- Re-padding a conjugate: `s` transports the padding, and the two
-- obligations that remain are generator-free, hence solver food.
repad : (h : K₁ ⇒ K₂) {i : A ⇒ K₁ ⊗₀ W} {o : K₂ ⊗₀ W ⇒ B}
        {i′ : A ⇒ K₁ ⊗₀ W′} {o′ : K₂ ⊗₀ W′ ⇒ B} (s : W ⇒ W′)
      → i′ ≈ id ⊗₁ s ∘ i → o′ ∘ id ⊗₁ s ≈ o
      → o ∘ h ⊗₁ id ∘ i ≈ o′ ∘ h ⊗₁ id ∘ i′
repad h {i} {o} {i′} {o′} s i≈ o≈ = begin
  o ∘ (h ⊗₁ id ∘ i)                       ≈˘⟨ o≈ ⟩∘⟨refl ⟩
  (o′ ∘ id ⊗₁ s) ∘ (h ⊗₁ id ∘ i)          ≈⟨ assoc ⟩
  o′ ∘ (id ⊗₁ s ∘ (h ⊗₁ id ∘ i))          ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  o′ ∘ ((id ⊗₁ s ∘ h ⊗₁ id) ∘ i)          ≈⟨ refl⟩∘⟨ pad-transport h s ⟩∘⟨refl ⟩
  o′ ∘ ((h ⊗₁ id ∘ id ⊗₁ s) ∘ i)          ≈⟨ refl⟩∘⟨ assoc ⟩
  o′ ∘ (h ⊗₁ id ∘ (id ⊗₁ s ∘ i))          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ i≈ ⟩
  o′ ∘ (h ⊗₁ id ∘ i′)                     ∎

------------------------------------------------------------------------
-- Splitting a crossing block
------------------------------------------------------------------------

-- The solver's normalizer never splits or merges crossing blocks, so the
-- hexagon is not decided (`lim-hexagon`).  These two are that hexagon, solved
-- for the block crossing, which is the only genuinely braided content the
-- interchanges below need.

σ-splitˡ : σ⇒ {P} {Q ⊗₀ X} ≈ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐
σ-splitˡ {P} {Q} {X} = begin
  σ⇒                                        ≈⟨ insertʳ associator.isoʳ ⟩
  (σ⇒ ∘ α⇒) ∘ α⇐                            ≈˘⟨ cancelˡ associator.isoˡ ⟩∘⟨refl ⟩
  (α⇐ ∘ (α⇒ ∘ (σ⇒ ∘ α⇒))) ∘ α⇐              ≈˘⟨ (refl⟩∘⟨ hexagon₁ {P} {Q} {X}) ⟩∘⟨refl ⟩
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐  ∎

σ-splitʳ : σ⇒ {P ⊗₀ Q} {X} ≈ α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)
σ-splitʳ {P} {Q} {X} = begin
  σ⇒                                        ≈⟨ insertˡ associator.isoʳ ⟩
  α⇒ ∘ (α⇐ ∘ σ⇒)                            ≈⟨ refl⟩∘⟨ insertʳ associator.isoˡ ⟩
  α⇒ ∘ (((α⇐ ∘ σ⇒) ∘ α⇐) ∘ α⇒)              ≈˘⟨ refl⟩∘⟨ hexagon₂ {P} {Q} {X} ⟩∘⟨refl ⟩
  α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)  ∎

-- Braiding the padding of a conjugate; the special case of `repad` where the
-- two paddings are the two orders of the same pair.
repad-σ : (h : K₁ ⇒ K₂) {i : A ⇒ K₁ ⊗₀ (W ⊗₀ W′)} {o : K₂ ⊗₀ (W ⊗₀ W′) ⇒ B}
        → o ∘ h ⊗₁ id ∘ i ≈ (o ∘ id ⊗₁ σ⇒) ∘ h ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ i)
repad-σ h = repad h σ⇒ Equiv.refl (cancelʳ σ-pad-inv)

------------------------------------------------------------------------
-- The slots are functorial
------------------------------------------------------------------------

slot₁ᵍ-∘ : {h₂ : Q ⊗₀ Y ⇒ R ⊗₀ B} {h₁ : P ⊗₀ X ⇒ Q ⊗₀ Y}
         → slot₁ᵍ {Z = Z} (h₂ ∘ h₁) ≈ slot₁ᵍ h₂ ∘ slot₁ᵍ h₁
slot₁ᵍ-∘ {h₂ = h₂} {h₁} = begin
  α⇒ ∘ ((h₂ ∘ h₁) ⊗₁ id ∘ α⇐)
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  α⇒ ∘ ((h₂ ⊗₁ id ∘ h₁ ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ insertInner associator.isoˡ ⟩∘⟨refl ⟩
  α⇒ ∘ (((h₂ ⊗₁ id ∘ α⇐) ∘ (α⇒ ∘ h₁ ⊗₁ id)) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((h₂ ⊗₁ id ∘ α⇐) ∘ ((α⇒ ∘ h₁ ⊗₁ id) ∘ α⇐))
    ≈⟨ sym-assoc ⟩
  (α⇒ ∘ (h₂ ⊗₁ id ∘ α⇐)) ∘ ((α⇒ ∘ h₁ ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (α⇒ ∘ (h₂ ⊗₁ id ∘ α⇐)) ∘ (α⇒ ∘ (h₁ ⊗₁ id ∘ α⇐))  ∎

slot₂ᵍ-∘ : {h₂ : Q ⊗₀ Y ⇒ R ⊗₀ B} {h₁ : P ⊗₀ X ⇒ Q ⊗₀ Y}
         → slot₂ᵍ {Z = Z} (h₂ ∘ h₁) ≈ slot₂ᵍ h₂ ∘ slot₂ᵍ h₁
slot₂ᵍ-∘ {h₂ = h₂} {h₁} = begin
  untuck ∘ ((h₂ ∘ h₁) ⊗₁ id ∘ tuck)
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  untuck ∘ ((h₂ ⊗₁ id ∘ h₁ ⊗₁ id) ∘ tuck)
    ≈⟨ refl⟩∘⟨ insertInner tuck-untuck ⟩∘⟨refl ⟩
  untuck ∘ (((h₂ ⊗₁ id ∘ tuck) ∘ (untuck ∘ h₁ ⊗₁ id)) ∘ tuck)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  untuck ∘ ((h₂ ⊗₁ id ∘ tuck) ∘ ((untuck ∘ h₁ ⊗₁ id) ∘ tuck))
    ≈⟨ sym-assoc ⟩
  (untuck ∘ (h₂ ⊗₁ id ∘ tuck)) ∘ ((untuck ∘ h₁ ⊗₁ id) ∘ tuck)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (untuck ∘ (h₂ ⊗₁ id ∘ tuck)) ∘ (untuck ∘ (h₁ ⊗₁ id ∘ tuck))  ∎

onL-∘ : {h₂ : P ⊗₀ Y ⇒ P ⊗₀ B} {h₁ : P ⊗₀ X ⇒ P ⊗₀ Y}
      → onL {Q = Q} (h₂ ∘ h₁) ≈ onL h₂ ∘ onL h₁
onL-∘ {h₂ = h₂} {h₁} = begin
  swp ∘ ((h₂ ∘ h₁) ⊗₁ id ∘ swp)
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  swp ∘ ((h₂ ⊗₁ id ∘ h₁ ⊗₁ id) ∘ swp)
    ≈⟨ refl⟩∘⟨ insertInner swp-swp ⟩∘⟨refl ⟩
  swp ∘ (((h₂ ⊗₁ id ∘ swp) ∘ (swp ∘ h₁ ⊗₁ id)) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ ((h₂ ⊗₁ id ∘ swp) ∘ ((swp ∘ h₁ ⊗₁ id) ∘ swp))
    ≈⟨ sym-assoc ⟩
  (swp ∘ (h₂ ⊗₁ id ∘ swp)) ∘ ((swp ∘ h₁ ⊗₁ id) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (swp ∘ (h₂ ⊗₁ id ∘ swp)) ∘ (swp ∘ (h₁ ⊗₁ id ∘ swp))  ∎

onRᵍ : (Q ⊗₀ X ⇒ R ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ R) ⊗₀ Y
onRᵍ k = α⇐ ∘ id ⊗₁ k ∘ α⇒

onRᵍ-∘ : {S T : Obj} {h₂ : R ⊗₀ Y ⇒ S ⊗₀ T} {h₁ : Q ⊗₀ X ⇒ R ⊗₀ Y}
       → onRᵍ {P = P} (h₂ ∘ h₁) ≈ onRᵍ h₂ ∘ onRᵍ h₁
onRᵍ-∘ {h₂ = h₂} {h₁} = begin
  α⇐ ∘ (id ⊗₁ (h₂ ∘ h₁) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
  α⇐ ∘ ((id ⊗₁ h₂ ∘ id ⊗₁ h₁) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ insertInner associator.isoʳ ⟩∘⟨refl ⟩
  α⇐ ∘ (((id ⊗₁ h₂ ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ h₁)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ ((id ⊗₁ h₂ ∘ α⇒) ∘ ((α⇐ ∘ id ⊗₁ h₁) ∘ α⇒))
    ≈⟨ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ h₂ ∘ α⇒)) ∘ ((α⇐ ∘ id ⊗₁ h₁) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (α⇐ ∘ (id ⊗₁ h₂ ∘ α⇒)) ∘ (α⇐ ∘ (id ⊗₁ h₁ ∘ α⇒))  ∎

slot₁ᵍ-cong : {h h′ : P ⊗₀ X ⇒ R ⊗₀ Y} → h ≈ h′ → slot₁ᵍ {Z = Z} h ≈ slot₁ᵍ h′
slot₁ᵍ-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

slot₂ᵍ-cong : {h h′ : P ⊗₀ X ⇒ R ⊗₀ Y} → h ≈ h′ → slot₂ᵍ {Z = Z} h ≈ slot₂ᵍ h′
slot₂ᵍ-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

onL-cong : {h h′ : P ⊗₀ X ⇒ P ⊗₀ Y} → h ≈ h′ → onL {Q = Q} h ≈ onL h′
onL-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

onR-cong : {h h′ : Q ⊗₀ X ⇒ Q ⊗₀ Y} → h ≈ h′ → onR {P = P} h ≈ onR h′
onR-cong e = refl⟩∘⟨ refl⟩⊗⟨ e ⟩∘⟨refl

------------------------------------------------------------------------
-- The two interface slots differ by a braiding
------------------------------------------------------------------------

-- `swp` is natural in the interface factor, so an action on the interface
-- alone passes through `onL` untouched.
swp-natural : (g : X ⇒ Y) → swp {P} {Q} ∘ id ⊗₁ g ≈ (id ⊗₁ g) ⊗₁ id ∘ swp
swp-natural g = begin
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ id ⊗₁ g              ≈⟨ assoc ⟩
  α⇐ ∘ ((id ⊗₁ σ⇒ ∘ α⇒) ∘ id ⊗₁ g)              ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ id ⊗₁ g))              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ step-α ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (id ⊗₁ (id ⊗₁ g) ∘ α⇒))      ≈⟨ refl⟩∘⟨ pullˡ step-σ ⟩
  α⇐ ∘ ((id ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ σ⇒) ∘ α⇒)      ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ (g ⊗₁ id) ∘ (id ⊗₁ σ⇒ ∘ α⇒))      ≈⟨ pullˡ assoc-commute-to ⟩
  ((id ⊗₁ g) ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⇒ ∘ α⇒)      ≈⟨ assoc ⟩
  (id ⊗₁ g) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))      ∎
  where
    step-α : α⇒ ∘ id ⊗₁ g ≈ id ⊗₁ (id ⊗₁ g) ∘ α⇒
    step-α = (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from

    step-σ : id ⊗₁ σ⇒ ∘ id ⊗₁ (id ⊗₁ g) ≈ id ⊗₁ (g ⊗₁ id) ∘ id ⊗₁ σ⇒
    step-σ = merge₂ʳ ○ refl⟩⊗⟨ braiding.⇒.commute (id , g) ○ split₂ʳ

onL-str : (g : X ⇒ Y) → onL {Q = Q} (id {P} ⊗₁ g) ≈ id ⊗₁ g
onL-str g = (refl⟩∘⟨ (⟺ (swp-natural g))) ○ pullˡ swp-swp ○ identityˡ

slot₂-slot₁ : {h : P ⊗₀ X ⇒ R ⊗₀ Y} → slot₂ᵍ {Z = Z} h ≈ id ⊗₁ σ⇒ ∘ (slot₁ᵍ h ∘ id ⊗₁ σ⇒)
slot₂-slot₁ {h = h} = begin
  (id ⊗₁ σ⇒ ∘ α⇒) ∘ (h ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ σ⇒))   ≈⟨ assoc ⟩
  id ⊗₁ σ⇒ ∘ (α⇒ ∘ (h ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ σ⇒)))   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  id ⊗₁ σ⇒ ∘ (α⇒ ∘ ((h ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒))   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  id ⊗₁ σ⇒ ∘ ((α⇒ ∘ (h ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ σ⇒)   ∎

------------------------------------------------------------------------
-- `Ω`'s inner half
------------------------------------------------------------------------

-- `Categories.Category.Monoidal.Interchange.Braided` calls this `swapˡ`; `Ω`
-- is its `onRᵍ` (`Ω≈Ω′`), which is what makes the `onR` interchange an
-- `Ω`-conjugation.
swapˡ : P ⊗₀ (Q ⊗₀ X) ⇒ Q ⊗₀ (P ⊗₀ X)
swapˡ = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐

-- An action on the interface alone passes through `onRᵍ` untouched.
onRᵍ-id⊗ : (h : W ⇒ W′) → onRᵍ {Q = Q} {P = P} (id ⊗₁ h) ≈ id ⊗₁ h
onRᵍ-id⊗ h = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ ○ (⊗.identity ⟩⊗⟨refl)

-- An action on one factor of a paired state, and one on the interface alone,
-- both pass through `onRᵍ` as themselves.
onRᵍ-⊗id : (h : W ⇒ W′) → onRᵍ {P = P} (h ⊗₁ id {X}) ≈ (id ⊗₁ h) ⊗₁ id
onRᵍ-⊗id _ = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ

onRᵍ-⊗ : {U V : Obj} {g₂ : Z ⊗₀ W′ ⇒ Q ⊗₀ V} {h : W ⇒ W′} {g₁ : Q ⊗₀ U ⇒ Z ⊗₀ W}
       → onRᵍ {P = P} (g₂ ∘ (id ⊗₁ h ∘ g₁)) ≈ onRᵍ g₂ ∘ (id ⊗₁ h ∘ onRᵍ g₁)
onRᵍ-⊗ {h = h} = onRᵍ-∘ ○ (refl⟩∘⟨ onRᵍ-∘) ○ (refl⟩∘⟨ (onRᵍ-id⊗ h ⟩∘⟨refl))

------------------------------------------------------------------------
-- Closing off the state
------------------------------------------------------------------------

-- `Spike.Mealy`'s `eval f n` is `cl (discard (state f)) (point (state f))
-- (run f n)`.
cl : (K₁ ⇒ unit) → (unit ⇒ K₁) → (K₁ ⊗₀ X ⇒ K₁ ⊗₀ Y) → X ⇒ Y
cl d p R = λ⇒ ∘ d ⊗₁ id ∘ R ∘ p ⊗₁ id ∘ λ⇐

------------------------------------------------------------------------
-- Solver terms mirroring the combinators of `Spike.Mealy`
------------------------------------------------------------------------

-- One generator `k : P ⊗ X ⇒ P ⊗ Y`, four object atoms besides.
module OneGen (P Q X Y Z : Obj) (k : P ⊗₀ X ⇒ P ⊗₀ Y) where

  vars = P ∷ Q ∷ X ∷ Y ∷ Z ∷ []
  open Coh.SymAtoms 𝕄 symmetric vars

  private
    p q x y z : ObjTerm
    p = V zero
    q = V (suc zero)
    x = V (suc (suc zero))
    y = V (suc (suc (suc zero)))
    z = V (suc (suc (suc (suc zero))))

  open Coh.SymSolve 𝕄 symmetric vars (((p ⊗ᵒ x , p ⊗ᵒ y) , k) ∷ [])

  private
    k′ = gen zero

    swpT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ w) ((u ⊗ᵒ w) ⊗ᵒ v)
    swpT u v w = S.α⇐ S.∘ S.id S.⊗₁ S.σ {v} {w} S.∘ S.α⇒ {u} {v} {w}

    onLT : (u v s t : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
         → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ s) ((u ⊗ᵒ v) ⊗ᵒ t)
    onLT u v s t h = swpT u t v S.∘ h S.⊗₁ S.id {v} S.∘ swpT u v s

    tuckT : (u v w : ObjTerm) → S.HomTerm (u ⊗ᵒ (v ⊗ᵒ w)) ((u ⊗ᵒ w) ⊗ᵒ v)
    tuckT u v w = S.α⇐ {u} {w} {v} S.∘ S.id {u} S.⊗₁ S.σ {v} {w}

    untuckT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ w) ⊗ᵒ v) (u ⊗ᵒ (v ⊗ᵒ w))
    untuckT u v w = S.id {u} S.⊗₁ S.σ {w} {v} S.∘ S.α⇒ {u} {w} {v}

    slot₁T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (s ⊗ᵒ w)) (u ⊗ᵒ (t ⊗ᵒ w))
    slot₁T u s t w h = S.α⇒ {u} {t} {w} S.∘ h S.⊗₁ S.id {w} S.∘ S.α⇐ {u} {s} {w}

    slot₂T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (w ⊗ᵒ s)) (u ⊗ᵒ (w ⊗ᵒ t))
    slot₂T u s t w h = untuckT u w t S.∘ h S.⊗₁ S.id {w} S.∘ tuckT u w s

    ΩT : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    ΩT u v s w = S.α⇒ {u ⊗ᵒ s} {v} {w} S.∘ swpT u v s S.⊗₁ S.id {w}
           S.∘ S.α⇐ {u ⊗ᵒ v} {s} {w}

    Ω′T : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    Ω′T u v s w = S.α⇐ {u} {s} {v ⊗ᵒ w}
      S.∘ S.id {u} S.⊗₁ (S.α⇒ {s} {v} {w} S.∘ S.σ {v} {s} S.⊗₁ S.id {w} S.∘ S.α⇐ {v} {s} {w})
      S.∘ S.α⇒ {u} {v} {s ⊗ᵒ w}

  -- The left state factor acting on interface slot 1 is an `Ω`-conjugate: this
  -- is the half of the interchange the solver decides.
  slot₁-onL : slot₁ {Z = Z} (onL {Q = Q} k) ≈ Ω ∘ k ⊗₁ id ∘ Ω
  slot₁-onL = solveMorσ! (slot₁T (p ⊗ᵒ q) x y z (onLT p q x y k′))
                         (ΩT p y q z S.∘ k′ S.⊗₁ S.id {q ⊗ᵒ z} S.∘ ΩT p q x z)

  -- Going the other way round, the padding comes out as `Z ⊗ Q` instead of
  -- `Q ⊗ Z` (`repad-σ`), and `onL` crosses `Q` with the whole interface block —
  -- a crossing block the solver will not split, so `σ-splitˡ`/`σ-splitʳ` split
  -- it by hand first and only then is the goal solver food.
  private
    σsplitˡT : (u v w : ObjTerm) → S.HomTerm (u ⊗ᵒ (v ⊗ᵒ w)) ((v ⊗ᵒ w) ⊗ᵒ u)
    σsplitˡT u v w = (S.α⇐ {v} {w} {u}
                      S.∘ (S.id {v} S.⊗₁ S.σ {u} {w}
                           S.∘ (S.α⇒ {v} {u} {w} S.∘ S.σ {u} {v} S.⊗₁ S.id {w})))
                     S.∘ S.α⇐ {u} {v} {w}

    σsplitʳT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ w) (w ⊗ᵒ (u ⊗ᵒ v))
    σsplitʳT u v w = S.α⇒ {w} {u} {v}
      S.∘ (((S.σ {u} {w} S.⊗₁ S.id {v} S.∘ S.α⇐ {u} {w} {v})
            S.∘ S.id {u} S.⊗₁ S.σ {v} {w}) S.∘ S.α⇒ {u} {v} {w})

    swpSplitˡT : (u v s w : ObjTerm)
               → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ (s ⊗ᵒ w)) ⊗ᵒ v)
    swpSplitˡT u v s w = S.α⇐ {u} {s ⊗ᵒ w} {v}
      S.∘ (S.id {u} S.⊗₁ σsplitˡT v s w S.∘ S.α⇒ {u} {v} {s ⊗ᵒ w})

    swpSplitʳT : (u s w v : ObjTerm)
               → S.HomTerm ((u ⊗ᵒ (s ⊗ᵒ w)) ⊗ᵒ v) ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w))
    swpSplitʳT u s w v = S.α⇐ {u} {v} {s ⊗ᵒ w}
      S.∘ (S.id {u} S.⊗₁ σsplitʳT s w v S.∘ S.α⇒ {u} {s ⊗ᵒ w} {v})

    onL-split : {S₁ S₂ T₁ T₂ : Obj} (h : P ⊗₀ (S₁ ⊗₀ S₂) ⇒ P ⊗₀ (T₁ ⊗₀ T₂))
              → onL {Q = Q} h
              ≈ (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)) ∘ α⇒))
                ∘ h ⊗₁ id
                ∘ (α⇐ ∘ (id ⊗₁ ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ α⇒))
    onL-split _ = (refl⟩∘⟨ refl⟩⊗⟨ σ-splitʳ ⟩∘⟨refl)
                    ⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩⊗⟨ σ-splitˡ ⟩∘⟨refl)

    onL-slot₁ : onL {Q = Q} (slot₁ {Z = Z} k) ≈ (Ω ∘ id ⊗₁ σ⇒) ∘ k ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ Ω)
    onL-slot₁ = onL-split (slot₁ k)
      ○ solveMorσ! (swpSplitʳT p y z q S.∘ slot₁T p x y z k′ S.⊗₁ S.id {q}
                    S.∘ swpSplitˡT p q x z)
                   ((ΩT p y q z S.∘ S.id {p ⊗ᵒ y} S.⊗₁ S.σ {z} {q})
                    S.∘ k′ S.⊗₁ S.id {z ⊗ᵒ q}
                    S.∘ (S.id {p ⊗ᵒ x} S.⊗₁ S.σ {q} {z} S.∘ ΩT p q x z))

  -- The interface slots commute with the left state factor's action.
  slot₁-onL-comm : slot₁ {Z = Z} (onL {Q = Q} k) ≈ onL (slot₁ k)
  slot₁-onL-comm = slot₁-onL ○ repad-σ k ○ ⟺ onL-slot₁

  -- Slot 2 is slot 1 conjugated by an interface braiding, and `onL` leaves such
  -- a braiding alone (`onL-str`), so the second interchange follows from the
  -- first with no further coherence.
  slot₂-onL-comm : slot₂ {Z = Z} (onL {Q = Q} k) ≈ onL (slot₂ k)
  slot₂-onL-comm = begin
    slot₂ (onL k)
      ≈⟨ slot₂-slot₁ ⟩
    id ⊗₁ σ⇒ ∘ (slot₁ (onL k) ∘ id ⊗₁ σ⇒)
      ≈⟨ refl⟩∘⟨ slot₁-onL-comm ⟩∘⟨refl ⟩
    id ⊗₁ σ⇒ ∘ (onL (slot₁ k) ∘ id ⊗₁ σ⇒)
      ≈˘⟨ onL-str σ⇒ ⟩∘⟨ (refl⟩∘⟨ onL-str σ⇒) ⟩
    onL (id ⊗₁ σ⇒) ∘ (onL (slot₁ k) ∘ onL (id ⊗₁ σ⇒))
      ≈˘⟨ onL-∘ ○ (refl⟩∘⟨ onL-∘) ⟩
    onL (id ⊗₁ σ⇒ ∘ (slot₁ k ∘ id ⊗₁ σ⇒))
      ≈˘⟨ onL-cong slot₂-slot₁ ⟩
    onL (slot₂ k) ∎

  -- `Ω` agrees with upstream's `swapInner`, which braids inside the interface
  -- pair rather than the state pair.
  Ω≈Ω′ : Ω {P} {Q} {X} {Z} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
  Ω≈Ω′ = solveMorσ! (ΩT p q x z) (Ω′T p q x z)

-- The right state factor's actions commute with both interface slots.
module OneGenʳ (P Q X Y Z : Obj) (k : Q ⊗₀ X ⇒ Q ⊗₀ Y) where

  vars = P ∷ Q ∷ X ∷ Y ∷ Z ∷ []
  open Coh.SymAtoms 𝕄 symmetric vars

  private
    p q x y z : ObjTerm
    p = V zero
    q = V (suc zero)
    x = V (suc (suc zero))
    y = V (suc (suc (suc zero)))
    z = V (suc (suc (suc (suc zero))))

  open Coh.SymSolve 𝕄 symmetric vars (((q ⊗ᵒ x , q ⊗ᵒ y) , k) ∷ [])

  private
    k′ = gen zero

    onRT : (u v s t : ObjTerm) → S.HomTerm (v ⊗ᵒ s) (v ⊗ᵒ t)
         → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ s) ((u ⊗ᵒ v) ⊗ᵒ t)
    onRT u v s t h = S.α⇐ {u} {v} {t} S.∘ S.id {u} S.⊗₁ h S.∘ S.α⇒ {u} {v} {s}

    slot₁T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (s ⊗ᵒ w)) (u ⊗ᵒ (t ⊗ᵒ w))
    slot₁T u s t w h = S.α⇒ {u} {t} {w} S.∘ h S.⊗₁ S.id {w} S.∘ S.α⇐ {u} {s} {w}

    slot₂T : (u s t w : ObjTerm) → S.HomTerm (u ⊗ᵒ s) (u ⊗ᵒ t)
           → S.HomTerm (u ⊗ᵒ (w ⊗ᵒ s)) (u ⊗ᵒ (w ⊗ᵒ t))
    slot₂T u s t w h = (S.id {u} S.⊗₁ S.σ {t} {w} S.∘ S.α⇒ {u} {t} {w})
                 S.∘ h S.⊗₁ S.id {w} S.∘ (S.α⇐ {u} {s} {w} S.∘ S.id {u} S.⊗₁ S.σ {w} {s})

  slot₁-onR : slot₁ {Z = Z} (onR {P = P} k) ≈ onR (slot₁ k)
  slot₁-onR = solveMorσ! (slot₁T (p ⊗ᵒ q) x y z (onRT p q x y k′))
                         (onRT p q (x ⊗ᵒ z) (y ⊗ᵒ z) (slot₁T q x y z k′))

  slot₂-onR : slot₂ {Z = Z} (onR {P = P} k) ≈ onR (slot₂ k)
  slot₂-onR = solveMorσ! (slot₂T (p ⊗ᵒ q) x y z (onRT p q x y k′))
                         (onRT p q (z ⊗ᵒ x) (z ⊗ᵒ y) (slot₂T q x y z k′))

  private
    swpT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ w) ((u ⊗ᵒ w) ⊗ᵒ v)
    swpT u v w = S.α⇐ S.∘ S.id S.⊗₁ S.σ {v} {w} S.∘ S.α⇒ {u} {v} {w}

    tuckT : (u v w : ObjTerm) → S.HomTerm (u ⊗ᵒ (v ⊗ᵒ w)) ((u ⊗ᵒ w) ⊗ᵒ v)
    tuckT u v w = S.α⇐ {u} {w} {v} S.∘ S.id {u} S.⊗₁ S.σ {v} {w}

    untuckT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ w) ⊗ᵒ v) (u ⊗ᵒ (v ⊗ᵒ w))
    untuckT u v w = S.id {u} S.⊗₁ S.σ {w} {v} S.∘ S.α⇒ {u} {w} {v}

    swapˡT : (u v w : ObjTerm) → S.HomTerm (u ⊗ᵒ (v ⊗ᵒ w)) (v ⊗ᵒ (u ⊗ᵒ w))
    swapˡT u v w = S.α⇒ {v} {u} {w} S.∘ (S.σ {u} {v} S.⊗₁ S.id {w} S.∘ S.α⇐ {u} {v} {w})

    ΩT : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    ΩT u v s w = S.α⇒ {u ⊗ᵒ s} {v} {w} S.∘ swpT u v s S.⊗₁ S.id {w}
                 S.∘ S.α⇐ {u ⊗ᵒ v} {s} {w}

    Ω′T : (u v s w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ (s ⊗ᵒ w)) ((u ⊗ᵒ s) ⊗ᵒ (v ⊗ᵒ w))
    Ω′T u v s w = S.α⇐ {u} {s} {v ⊗ᵒ w}
                  S.∘ (S.id {u} S.⊗₁ swapˡT v s w S.∘ S.α⇒ {u} {v} {s ⊗ᵒ w})

    σsplitˡT : (u v w : ObjTerm) → S.HomTerm (u ⊗ᵒ (v ⊗ᵒ w)) ((v ⊗ᵒ w) ⊗ᵒ u)
    σsplitˡT u v w = (S.α⇐ {v} {w} {u}
                      S.∘ (S.id {v} S.⊗₁ S.σ {u} {w}
                           S.∘ (S.α⇒ {v} {u} {w} S.∘ S.σ {u} {v} S.⊗₁ S.id {w})))
                     S.∘ S.α⇐ {u} {v} {w}

    σsplitʳT : (u v w : ObjTerm) → S.HomTerm ((u ⊗ᵒ v) ⊗ᵒ w) (w ⊗ᵒ (u ⊗ᵒ v))
    σsplitʳT u v w = S.α⇒ {w} {u} {v}
      S.∘ (((S.σ {u} {w} S.⊗₁ S.id {v} S.∘ S.α⇐ {u} {w} {v})
            S.∘ S.id {u} S.⊗₁ S.σ {v} {w}) S.∘ S.α⇒ {u} {v} {w})

    -- `tuck`/`untuck` route the interface pair past the state through a single
    -- block crossing; `swapˡ` routes it through two atomic ones, so these two
    -- are hexagon instances (hence `σ-splitˡ`/`σ-splitʳ` first).
    tuck-swapˡ : tuck {P = Q} {Q = Z} {R = X} ≈ σ⇒ ∘ swapˡ
    tuck-swapˡ = solveMorσ! (tuckT q z x) (σsplitˡT z q x S.∘ swapˡT q z x)
               ○ ⟺ (σ-splitˡ ⟩∘⟨refl)

    untuck-swapˡ : untuck {P = Q} {R = Y} {Q = Z} ≈ swapˡ ∘ σ⇒
    untuck-swapˡ = solveMorσ! (untuckT q z y) (swapˡT z q y S.∘ σsplitʳT q y z)
                 ○ ⟺ (refl⟩∘⟨ σ-splitʳ)

    Ω≈Ω′ᵢ : Ω {P} {Q} {Z} {X} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
    Ω≈Ω′ᵢ = solveMorσ! (ΩT p q z x) (Ω′T p q z x)

    Ω≈Ω′ₒ : Ω {P} {Z} {Q} {Y} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
    Ω≈Ω′ₒ = solveMorσ! (ΩT p z q y) (Ω′T p z q y)

  -- Slot 2 acted on by the right state factor is a `swapˡ`-conjugate…
  slot₂-swapˡ : slot₂ {Z = Z} k ≈ swapˡ ∘ id ⊗₁ k ∘ swapˡ
  slot₂-swapˡ = (untuck-swapˡ ⟩∘⟨ (refl⟩∘⟨ tuck-swapˡ)) ○ ⟺ (unbraid k)

  -- …and `onR` turns that into the `Ω`-conjugate: the half of the interchange
  -- the solver declines (`lim-straddle`, the padding `P ⊗ Z` straddling `k`).
  slot₂-onR-Ω : slot₂ {Z = Z} (onR {P = P} k) ≈ Ω ∘ id ⊗₁ k ∘ Ω
  slot₂-onR-Ω = slot₂-onR ○ onR-cong slot₂-swapˡ ○ onRᵍ-⊗
              ○ ((⟺ Ω≈Ω′ₒ) ⟩∘⟨ (refl⟩∘⟨ (⟺ Ω≈Ω′ᵢ)))

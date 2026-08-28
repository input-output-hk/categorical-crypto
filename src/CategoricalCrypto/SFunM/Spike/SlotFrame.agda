{-# OPTIONS --safe --without-K #-}

-- SPIKE: the machine layer's coherence, in one file.
--
-- The interface tensor's congruence has to recognize "the step acts on the
-- `A`-subword of a mixed word" as "the step acts on slot 1", and the two differ
-- by a reshuffle that carries the untouched letters past the step.  Every such
-- goal is an equality of two `frame k i o` — `k` in slot 1, the rest of the
-- interface reshuffled on both sides — and `frame-pad` slides the untouched
-- factor from one side of the frame to the other, which is `repad` lifted
-- through `id ⊗₁ _`.  What is left is generator-free: `rot-in` and `rot-out`,
-- one hexagon each.
--
-- This is the point-free price of the elementwise `lefts`/`fillˡ` recursion, and
-- it is the only genuinely braided content in the congruence: `slot-α` merges
-- two paddings, `slot-σ` moves one letter out of the way.  The rest of the file
-- is the same class of bookkeeping — slot and frame transport, associator and
-- unitor padding, `σ`-split shuffles, the interchange arms the state pairing
-- needs — collected here so that the whole class sits in one place;
-- `Spike.Distributor`, `Spike.Laws` and `Spike.Tensor` are its consumers.
--
-- Every proof body here is hand-rolled and is to be replaced by a `solveH!`
-- call (`Categories.Coherence.Symmetric`) once the `string-diagram-solver`
-- branch is merged; the statements are the seam and stay fixed.  Evidence:
-- `solveH!` takes 100% (branch `spike/sds-slotframe-probe` @ e6a28168).
--
-- The σ arm the seam used to call is gone: the solver branch deleted the
-- braided engine and front-end, keeping only the Mon arm.  Most of what the σ
-- arm was doing here did not need it — a crossing that appears at the SAME
-- arity on both sides of a goal is just an opaque box, so `solve-mor` (the
-- reflection frontend of the Mon arm) still discharges it.  What it cannot do
-- is relate a BLOCK crossing to the atomic ones it splits into: those are
-- distinct boxes of different arity.  Hence `tuck-swapˡ`/`untuck-swapˡ` below
-- are hexagons proved by hand from `σ-splitˡ`/`σ-splitʳ`, and `onL-slot₁`
-- pre-splits with `onL-split` before handing the rest to the macro.

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Interchange.Braided as IntBraided
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Coherence.Monoidal using (module MorAtoms; module MorSolve)
open import Categories.Coherence.Monoidal.Tactic using (solve-mor)

open import Data.Fin using (#_)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_; [])

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.SlotFrame {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv
open Mealy 𝒱
open State

open import Categories.Category.Monoidal.Properties monoidal
  using (coherence₁; coherence₂; coherence₃; coherence-inv₁; coherence-inv₃)
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U
open BraidedProps braided using (braiding-coherence)
open IntBraided braided using (swapInner-coherent)
open MonoidalUtilities monoidal using (pentagon-inv; triangle-inv)

private variable A A′ B B′ C C′ K₁ K₂ L P Q R S W W′ X Y Z : Obj

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

-- `id ⊗₁ _` preserves invertibility.
pad-inv : {h : X ⇒ Y} {h⁻ : Y ⇒ X} → h ∘ h⁻ ≈ id → id {L} ⊗₁ h ∘ id ⊗₁ h⁻ ≈ id
pad-inv e = merge₂ˡ ○ refl⟩⊗⟨ e ○ ⊗.identity

σ-pad-inv : id {L} ⊗₁ σ⇒ ∘ id ⊗₁ σ⇒ ≈ id {L ⊗₀ (Q ⊗₀ X)}
σ-pad-inv = pad-inv commutative

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

-- Splitting a padding across the associator: the generator never sees it.
pad-α⇒ : (h : K₁ ⇒ K₂) → h ⊗₁ id {W ⊗₀ W′} ∘ α⇒ ≈ α⇒ ∘ (h ⊗₁ id {W}) ⊗₁ id {W′}
pad-α⇒ _ = ((refl⟩⊗⟨ (⟺ ⊗.identity)) ⟩∘⟨refl) ○ ⟺ assoc-commute-from

pad-α⇐ : (h : K₁ ⇒ K₂) → α⇐ ∘ h ⊗₁ id {W ⊗₀ W′} ≈ (h ⊗₁ id {W}) ⊗₁ id {W′} ∘ α⇐
pad-α⇐ _ = (refl⟩∘⟨ (refl⟩⊗⟨ (⟺ ⊗.identity))) ○ assoc-commute-to

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

-- `Ω` is upstream's four-middle-interchange: `Ω` is `swapInner′.from` and the
-- right-hand side is `swapInner.from`, both definitionally, so this is exactly
-- `swapInner-coherent`.  Only the same atomic crossing appears on the two
-- sides, which is why no hexagon is involved.
Ω≈swapInner : Ω {P} {Q} {X} {Z} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
Ω≈swapInner = ⟺ swapInner-coherent

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
-- Reassociating a slot's padding
------------------------------------------------------------------------

σ⊗-inv : σ⇒ {P} {Q} ⊗₁ id {A} ∘ σ⇒ {Q} {P} ⊗₁ id ≈ id
σ⊗-inv = merge₁ˡ ○ (commutative ⟩⊗⟨refl) ○ ⊗.identity

private
  -- The pentagon, read as "a padding may be split or merged".
  pent⇒ : α⇒ ∘ (α⇒ {X} {Y} {Z} ⊗₁ id {S}) ≈ id ⊗₁ α⇐ ∘ (α⇒ ∘ α⇒)
  pent⇒ = insertˡ (pad-inv associator.isoˡ) ○ (refl⟩∘⟨ pentagon)

  pent⇐ : α⇒ ∘ (α⇐ {X} {Y} {Z} ⊗₁ id {S} ∘ α⇐) ≈ α⇐ ∘ id ⊗₁ α⇒
  pent⇐ = (refl⟩∘⟨ (insertʳ (pad-inv associator.isoˡ) ○ (pentagon-inv ⟩∘⟨refl)))
        ○ sym-assoc ○ (cancelˡ associator.isoʳ ⟩∘⟨refl)

-- Slot 1 is natural in the factor it leaves alone.
slot₁-pad : (h : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y}
          → slot₁ᵍ {Z = S} k ∘ id ⊗₁ (id ⊗₁ h) ≈ id ⊗₁ (id ⊗₁ h) ∘ slot₁ᵍ {Z = Z} k
slot₁-pad h {k} = begin
  (α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ (id ⊗₁ h)
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇒ ∘ (k ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (id ⊗₁ h)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc-commute-to ○ ((⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl)) ⟩
  α⇒ ∘ (k ⊗₁ id ∘ (id ⊗₁ h ∘ α⇐))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (pad-transport k h)) ⟩
  α⇒ ∘ ((id ⊗₁ h ∘ k ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ (id ⊗₁ h ∘ (k ⊗₁ id ∘ α⇐))
    ≈⟨ pullˡ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ○ assoc ⟩
  id ⊗₁ (id ⊗₁ h) ∘ (α⇒ ∘ (k ⊗₁ id ∘ α⇐))  ∎

-- Slot 2 is natural in its untouched factor, which is slot 1's braided.
slot₂-pad : (h : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y}
          → slot₂ᵍ {Z = S} k ∘ id ⊗₁ (h ⊗₁ id) ≈ id ⊗₁ (h ⊗₁ id) ∘ slot₂ᵍ {Z = Z} k
slot₂-pad h {k} = begin
  slot₂ᵍ k ∘ id ⊗₁ (h ⊗₁ id)
    ≈⟨ slot₂-slot₁ ⟩∘⟨refl ⟩
  (id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒)) ∘ id ⊗₁ (h ⊗₁ id)
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ (id ⊗₁ σ⇒ ∘ id ⊗₁ (h ⊗₁ id)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (h , id)) ○ split₂ʳ) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ (id ⊗₁ (id ⊗₁ h) ∘ id ⊗₁ σ⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (slot₁-pad h) ⟩
  id ⊗₁ σ⇒ ∘ ((id ⊗₁ (id ⊗₁ h) ∘ slot₁ᵍ k) ∘ id ⊗₁ σ⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ σ⇒ ∘ (id ⊗₁ (id ⊗₁ h) ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒))
    ≈⟨ pullˡ (merge₂ʳ ○ (refl⟩⊗⟨ braiding.⇒.commute (id , h)) ○ split₂ʳ) ○ assoc ⟩
  id ⊗₁ (h ⊗₁ id) ∘ (id ⊗₁ σ⇒ ∘ (slot₁ᵍ k ∘ id ⊗₁ σ⇒))
    ≈˘⟨ refl⟩∘⟨ slot₂-slot₁ ⟩
  id ⊗₁ (h ⊗₁ id) ∘ slot₂ᵍ k  ∎

-- A step that ignores the state slots into either interface slot as itself.
slot₁-str : (h : X ⇒ Y) → slot₁ᵍ {Z = Z} (id {P} ⊗₁ h) ≈ id ⊗₁ (h ⊗₁ id)
slot₁-str h = pullˡ assoc-commute-from ○ cancelʳ associator.isoʳ

slot₂-str : (h : X ⇒ Y) → slot₂ᵍ {Z = Z} (id {P} ⊗₁ h) ≈ id ⊗₁ (id ⊗₁ h)
slot₂-str h = slot₂-slot₁ ○ (refl⟩∘⟨ slot₁-str h ⟩∘⟨refl)
            ○ (refl⟩∘⟨ merge₂ʳ) ○ merge₂ʳ ○ refl⟩⊗⟨ (⟺ (pad-braid _ h))

-- A letterwise pair of interface actions is one action per slot.
pair-slots : (h : A ⇒ B) (j : X ⇒ Y)
           → id {P} ⊗₁ (h ⊗₁ j) ≈ slot₁ᵍ (id ⊗₁ h) ∘ slot₂ᵍ (id ⊗₁ j)
pair-slots h j = (refl⟩⊗⟨ serialize₁₂) ○ split₂ʳ ○ ⟺ (slot₁-str h ⟩∘⟨ slot₂-str j)

slot₁-id : ∀ {X Z} → slot₁ {P} {X} {X} {Z} id ≈ id
slot₁-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoʳ

slot₂-id : ∀ {X Z} → slot₂ {P} {X} {X} {Z} id ≈ id
slot₂-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ untuck-tuck

-- A state map conjugating the steps passes through both interface slots…
slot₁-sim : {u : P ⇒ R} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
          → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
          → u ⊗₁ id {Y ⊗₀ Z} ∘ slot₁ k ≈ slot₁ k′ ∘ u ⊗₁ id
slot₁-sim {u = u} {k} {k′} e = begin
  u ⊗₁ id ∘ (α⇒ ∘ (k ⊗₁ id ∘ α⇐))            ≈⟨ pullˡ (pad-α⇒ u) ⟩
  (α⇒ ∘ (u ⊗₁ id) ⊗₁ id) ∘ (k ⊗₁ id ∘ α⇐)    ≈⟨ center merge₁ˡ ⟩
  α⇒ ∘ ((u ⊗₁ id ∘ k) ⊗₁ id ∘ α⇐)            ≈⟨ refl⟩∘⟨ (e ⟩⊗⟨refl ○ split₁ˡ) ⟩∘⟨refl ⟩
  α⇒ ∘ ((k′ ⊗₁ id ∘ (u ⊗₁ id) ⊗₁ id) ∘ α⇐)   ≈⟨ refl⟩∘⟨ pullʳ (⟺ (pad-α⇐ u)) ⟩
  α⇒ ∘ (k′ ⊗₁ id ∘ (α⇐ ∘ u ⊗₁ id))           ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇒ ∘ (k′ ⊗₁ id ∘ α⇐)) ∘ u ⊗₁ id           ∎

-- …the second one being the first conjugated by an interface braiding.
slot₂-sim : {u : P ⇒ R} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
          → u ⊗₁ id ∘ k ≈ k′ ∘ u ⊗₁ id
          → u ⊗₁ id {Z ⊗₀ Y} ∘ slot₂ k ≈ slot₂ k′ ∘ u ⊗₁ id
slot₂-sim {u = u} {k} {k′} e = begin
  u ⊗₁ id ∘ slot₂ k                            ≈⟨ refl⟩∘⟨ slot₂-slot₁ ⟩
  u ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ (slot₁ k ∘ id ⊗₁ σ⇒))  ≈⟨ pullˡ (⟺ (pad-transport u σ⇒)) ⟩
  (id ⊗₁ σ⇒ ∘ u ⊗₁ id) ∘ (slot₁ k ∘ id ⊗₁ σ⇒)  ≈⟨ center (slot₁-sim e) ⟩
  id ⊗₁ σ⇒ ∘ ((slot₁ k′ ∘ u ⊗₁ id) ∘ id ⊗₁ σ⇒) ≈⟨ refl⟩∘⟨ pullʳ (⟺ (pad-transport u σ⇒)) ⟩
  id ⊗₁ σ⇒ ∘ (slot₁ k′ ∘ (id ⊗₁ σ⇒ ∘ u ⊗₁ id)) ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (id ⊗₁ σ⇒ ∘ (slot₁ k′ ∘ id ⊗₁ σ⇒)) ∘ u ⊗₁ id ≈˘⟨ slot₂-slot₁ ⟩∘⟨refl ⟩
  slot₂ k′ ∘ u ⊗₁ id                           ∎

------------------------------------------------------------------------
-- The frame
------------------------------------------------------------------------

-- `k` acting on slot 1, with the rest of the interface reshuffled on both
-- sides.  Every goal the word split raises is an equality of two of these.
frame : (P ⊗₀ X ⇒ R ⊗₀ Y) → (A ⇒ X ⊗₀ Z) → (Y ⊗₀ Z ⇒ B) → P ⊗₀ A ⇒ R ⊗₀ B
frame k i o = id ⊗₁ o ∘ (slot₁ᵍ k ∘ id ⊗₁ i)

frame-cong : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i i′ : A ⇒ X ⊗₀ Z} {o o′ : Y ⊗₀ Z ⇒ B}
           → i ≈ i′ → o ≈ o′ → frame k i o ≈ frame k i′ o′
frame-cong ei eo = (refl⟩⊗⟨ eo) ⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ei))

frame-∘ʳ : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ Z ⇒ B} {j : C ⇒ A}
         → frame k i o ∘ id ⊗₁ j ≈ frame k (i ∘ j) o
frame-∘ʳ = assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ merge₂ʳ)

frame-∘ˡ : {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ Z ⇒ B} {j : B ⇒ C}
         → id ⊗₁ j ∘ frame k i o ≈ frame k i (j ∘ o)
frame-∘ˡ = pullˡ merge₂ʳ

-- Sliding the untouched factor from one side of the frame to the other.
frame-pad : (s : Z ⇒ S) {k : P ⊗₀ X ⇒ R ⊗₀ Y} {i : A ⇒ X ⊗₀ Z} {o : Y ⊗₀ S ⇒ B}
          → frame k (id ⊗₁ s ∘ i) o ≈ frame k i (o ∘ id ⊗₁ s)
frame-pad s = (refl⟩∘⟨ refl⟩∘⟨ split₂ʳ) ○ (refl⟩∘⟨ pullˡ (slot₁-pad s))
            ○ (refl⟩∘⟨ assoc) ○ pullˡ merge₂ʳ

------------------------------------------------------------------------
-- Two nested slots, as frames
------------------------------------------------------------------------

slot₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y} → slot₁ᵍ {Z = Z} k ≈ frame k id id
slot₁-frame = ⟺ (elimˡ ⊗.identity ○ elimʳ ⊗.identity)

slot₁₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₁ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ≈ frame k α⇒ α⇐
slot₁₁-frame {k = k} = begin
  α⇒ ∘ ((α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ⊗₁ id ∘ α⇐)
    ≈⟨ refl⟩∘⟨ (split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)) ⟩∘⟨refl ⟩
  α⇒ ∘ ((α⇒ ⊗₁ id ∘ ((k ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id)) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc)) ⟩
  α⇒ ∘ (α⇒ ⊗₁ id ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐)))
    ≈⟨ pullˡ pent⇒ ⟩
  (id ⊗₁ α⇐ ∘ (α⇒ ∘ α⇒)) ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐))
    ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (α⇒ ∘ ((k ⊗₁ id) ⊗₁ id ∘ (α⇐ ⊗₁ id ∘ α⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ (pad-α⇒ k)) ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ ((k ⊗₁ id ∘ α⇒) ∘ (α⇐ ⊗₁ id ∘ α⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (k ⊗₁ id ∘ (α⇒ ∘ (α⇐ ⊗₁ id ∘ α⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pent⇐ ⟩
  id ⊗₁ α⇐ ∘ (α⇒ ∘ (k ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ α⇒)))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc) ○ (refl⟩∘⟨ sym-assoc) ⟩
  id ⊗₁ α⇐ ∘ ((α⇒ ∘ (k ⊗₁ id ∘ α⇐)) ∘ id ⊗₁ α⇒)  ∎

slot₂₁-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ≈ frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐)
slot₂₁-frame = slot₂-slot₁ ○ (refl⟩∘⟨ slot₁₁-frame ⟩∘⟨refl)
             ○ (refl⟩∘⟨ frame-∘ʳ) ○ frame-∘ˡ

slot₁₂-frame : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
             → slot₁ᵍ {Z = Z} (slot₂ᵍ {Z = S} k)
             ≈ frame k (α⇒ ∘ σ⇒ ⊗₁ id) (σ⇒ ⊗₁ id ∘ α⇐)
slot₁₂-frame = slot₁ᵍ-cong slot₂-slot₁ ○ (slot₁ᵍ-∘ ○ (refl⟩∘⟨ slot₁ᵍ-∘))
             ○ (slot₁-str σ⇒ ⟩∘⟨ (slot₁₁-frame ⟩∘⟨ slot₁-str σ⇒))
             ○ (refl⟩∘⟨ frame-∘ʳ) ○ frame-∘ˡ

------------------------------------------------------------------------
-- The generator-free residue: one hexagon each way
------------------------------------------------------------------------

-- Rotating a factor out of a pair, and back in.
rot-in : ∀ {X S Z : Obj} → α⇒ {X} {Z} {S} ∘ (σ⇒ {S} {X ⊗₀ Z} ∘ α⇒ {S} {X} {Z})
       ≈ id ⊗₁ σ⇒ ∘ (α⇒ {X} {S} {Z} ∘ σ⇒ {S} {X} ⊗₁ id {Z})
rot-in = (refl⟩∘⟨ (σ-splitˡ ⟩∘⟨refl)) ○ (refl⟩∘⟨ cancelʳ associator.isoˡ)
       ○ cancelˡ associator.isoʳ

rot-out : ∀ {Y S Z : Obj} → σ⇒ {Y ⊗₀ Z} {S} ∘ α⇐ {Y} {Z} {S}
        ≈ (α⇒ {S} {Y} {Z} ∘ (σ⇒ {Y} {S} ⊗₁ id {Z} ∘ α⇐ {Y} {S} {Z}))
          ∘ id ⊗₁ σ⇒ {Z} {S}
rot-out = (σ-splitʳ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ cancelʳ associator.isoʳ) ○ sym-assoc

private
  -- The rotation absorbs the braiding it was built from.
  swap-in : ∀ {X S Z : Obj} → (α⇒ {X} {Z} {S} ∘ σ⇒ {S} {X ⊗₀ Z}) ∘ swapˡ {X} {S} {Z}
          ≈ id ⊗₁ σ⇒ {S} {Z}
  swap-in = assoc ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (rot-in ⟩∘⟨refl)
          ○ assoc ○ (refl⟩∘⟨ (cancelInner σ⊗-inv ○ associator.isoʳ)) ○ identityʳ

------------------------------------------------------------------------
-- The two arms the word split needs
------------------------------------------------------------------------

-- Merging the paddings of two nested slots…
slot-α : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
       → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ∘ id ⊗₁ α⇒
       ≈ id ⊗₁ α⇒ ∘ slot₁ᵍ {Z = Z} (slot₂ᵍ {Z = S} k)
slot-α {X = X} {Y = Y} {S = S} {Z = Z} {k = k} = begin
  slot₂ᵍ (slot₁ᵍ k) ∘ id ⊗₁ α⇒
    ≈⟨ slot₂₁-frame ⟩∘⟨refl ⟩
  frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐) ∘ id ⊗₁ α⇒
    ≈⟨ frame-∘ʳ ⟩
  frame k ((α⇒ ∘ σ⇒) ∘ α⇒) (σ⇒ ∘ α⇐)
    ≈⟨ frame-cong (assoc ○ rot-in {X} {S} {Z}) (rot-out {Y} {S} {Z}) ⟩
  frame k (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id)) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-pad (σ⇒ {S} {Z}) ⟩
  frame k (α⇒ ∘ σ⇒ ⊗₁ id) ((swapˡ ∘ id ⊗₁ σ⇒) ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-cong refl (cancelʳ (pad-inv (commutative {Z} {S}))) ⟩
  frame k (α⇒ ∘ σ⇒ ⊗₁ id) swapˡ
    ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ α⇒ ∘ frame k (α⇒ ∘ σ⇒ ⊗₁ id) (σ⇒ ⊗₁ id ∘ α⇐)
    ≈˘⟨ refl⟩∘⟨ slot₁₂-frame ⟩
  id ⊗₁ α⇒ ∘ slot₁ᵍ (slot₂ᵍ k)  ∎

-- …and moving one letter of the padding out of the way.
slot-σ : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
       → slot₂ᵍ {Z = S} (slot₁ᵍ {Z = Z} k) ∘ id ⊗₁ swapˡ
       ≈ id ⊗₁ swapˡ ∘ slot₁ᵍ {Z = S ⊗₀ Z} k
slot-σ {X = X} {Y = Y} {S = S} {Z = Z} {k = k} = begin
  slot₂ᵍ (slot₁ᵍ k) ∘ id ⊗₁ swapˡ
    ≈⟨ slot₂₁-frame ⟩∘⟨refl ⟩
  frame k (α⇒ ∘ σ⇒) (σ⇒ ∘ α⇐) ∘ id ⊗₁ swapˡ
    ≈⟨ frame-∘ʳ ⟩
  frame k ((α⇒ ∘ σ⇒) ∘ swapˡ) (σ⇒ ∘ α⇐)
    ≈⟨ frame-cong (swap-in {X} {S} {Z}) (rot-out {Y} {S} {Z}) ⟩
  frame k (id ⊗₁ σ⇒) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈˘⟨ frame-cong identityʳ refl ⟩
  frame k (id ⊗₁ σ⇒ ∘ id) (swapˡ ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-pad (σ⇒ {S} {Z}) ⟩
  frame k id ((swapˡ ∘ id ⊗₁ σ⇒) ∘ id ⊗₁ σ⇒)
    ≈⟨ frame-cong refl (cancelʳ (pad-inv (commutative {Z} {S}))) ⟩
  frame k id swapˡ
    ≈˘⟨ frame-cong refl identityʳ ⟩
  frame k id (swapˡ ∘ id)
    ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ swapˡ ∘ frame k id id
    ≈˘⟨ refl⟩∘⟨ slot₁-frame ⟩
  id ⊗₁ swapˡ ∘ slot₁ᵍ k  ∎

-- Splitting one padding into two.
slot₁-α : {k : P ⊗₀ X ⇒ R ⊗₀ Y}
        → slot₁ᵍ {Z = Z ⊗₀ S} k ∘ id ⊗₁ α⇒
        ≈ id ⊗₁ α⇒ ∘ slot₁ᵍ {Z = S} (slot₁ᵍ {Z = Z} k)
slot₁-α {k = k} = begin
  slot₁ᵍ k ∘ id ⊗₁ α⇒                       ≈⟨ slot₁-frame ⟩∘⟨refl ⟩
  frame k id id ∘ id ⊗₁ α⇒                  ≈⟨ frame-∘ʳ ⟩
  frame k (id ∘ α⇒) id                      ≈⟨ frame-cong identityˡ refl ⟩
  frame k α⇒ id                              ≈˘⟨ frame-cong refl associator.isoʳ ⟩
  frame k α⇒ (α⇒ ∘ α⇐)                       ≈˘⟨ frame-∘ˡ ⟩
  id ⊗₁ α⇒ ∘ frame k α⇒ α⇐                   ≈˘⟨ refl⟩∘⟨ slot₁₁-frame ⟩
  id ⊗₁ α⇒ ∘ slot₁ᵍ (slot₁ᵍ k)  ∎

------------------------------------------------------------------------
-- The state pair's two actions
------------------------------------------------------------------------

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ swp-swp

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

-- `Machine.step (g ∘ᴹ f)`.
compK : (P ⊗₀ B ⇒ P ⊗₀ C) → (Q ⊗₀ A ⇒ Q ⊗₀ B) → (P ⊗₀ Q) ⊗₀ A ⇒ (P ⊗₀ Q) ⊗₀ C
compK g f = onL g ∘ onR f

compK-id : compK (id {P ⊗₀ A}) (id {Q ⊗₀ A}) ≈ id
compK-id = (onL-id ⟩∘⟨ onR-id) ○ identity²

-- `swp` is natural in the interface factor it moves out, too — the mirror of
-- `swp-natural`, obtained from it by involutivity.
swp-natural′ : (g : X ⇒ Y) → swp {P} {Y} {Q} ∘ (id ⊗₁ g) ⊗₁ id ≈ id ⊗₁ g ∘ swp
swp-natural′ g = begin
  swp ∘ (id ⊗₁ g) ⊗₁ id                ≈⟨ refl⟩∘⟨ insertʳ swp-swp ⟩
  swp ∘ (((id ⊗₁ g) ⊗₁ id ∘ swp) ∘ swp) ≈˘⟨ refl⟩∘⟨ swp-natural g ⟩∘⟨refl ⟩
  swp ∘ ((swp ∘ id ⊗₁ g) ∘ swp)        ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ (swp ∘ (id ⊗₁ g ∘ swp))        ≈⟨ cancelˡ swp-swp ⟩
  id ⊗₁ g ∘ swp                        ∎

-- `swp` is natural in all three factors.
swp-nat : (u : P ⇒ R) (v : Q ⇒ Z) (t : X ⇒ Y)
        → (u ⊗₁ t) ⊗₁ v ∘ swp ≈ swp ∘ (u ⊗₁ v) ⊗₁ t
swp-nat u v t = begin
  (u ⊗₁ t) ⊗₁ v ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (u ⊗₁ (t ⊗₁ v) ∘ (id ⊗₁ σ⇒ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm (⟺ (braiding.⇒.commute (v , t)))) ⟩
  α⇐ ∘ ((id ⊗₁ σ⇒ ∘ u ⊗₁ (v ⊗₁ t)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (u ⊗₁ (v ⊗₁ t) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ (u ⊗₁ v) ⊗₁ t))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ (u ⊗₁ v) ⊗₁ t  ∎

-- Both state-side actions carry a square that is natural in the interface…
onL-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onL {Q = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onL k
onL-branch {k = k} {t} {j} {j′} e = begin
  (swp ∘ (t ⊗₁ id ∘ swp)) ∘ id ⊗₁ j        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  swp ∘ (t ⊗₁ id ∘ (swp ∘ id ⊗₁ j))        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swp-natural j ⟩
  swp ∘ (t ⊗₁ id ∘ ((id ⊗₁ j) ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ e ⟩⊗⟨refl ○ split₁ˡ) ⟩
  swp ∘ (((id ⊗₁ j′) ⊗₁ id ∘ k ⊗₁ id) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ○ pullˡ (swp-natural′ j′) ○ assoc ⟩
  id ⊗₁ j′ ∘ (swp ∘ (k ⊗₁ id ∘ swp))       ∎

onR-branch : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {t : Q ⊗₀ X ⇒ Q ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onR {P = P} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onR k
onR-branch {k = k} {t} {j} {j′} e = begin
  (α⇐ ∘ (id ⊗₁ t ∘ α⇒)) ∘ id ⊗₁ j          ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇐ ∘ (id ⊗₁ t ∘ (α⇒ ∘ id ⊗₁ j))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ⟩
  α⇐ ∘ (id ⊗₁ t ∘ (id ⊗₁ (id ⊗₁ j) ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ e ○ split₂ʳ) ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ j′) ∘ id ⊗₁ k) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc
       ○ pullˡ (assoc-commute-to ○ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ○ assoc ⟩
  id ⊗₁ j′ ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))         ∎

-- A state map on each factor of a paired state conjugates the two actions:
-- `slot₁-sim`'s mirror for the state side.
onL-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
        → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id {Y} ∘ onL k ≈ onL k′ ∘ (v ⊗₁ w) ⊗₁ id {X}
onL-sim {v = v} {w} {k} {k′} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (swp ∘ (k ⊗₁ id ∘ swp))
    ≈⟨ pullˡ (swp-nat v id w) ○ assoc ⟩
  swp ∘ ((v ⊗₁ id) ⊗₁ w ∘ (k ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel e id-comm) ⟩
  swp ∘ ((k′ ⊗₁ id ∘ (v ⊗₁ id) ⊗₁ w) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  swp ∘ (k′ ⊗₁ id ∘ ((v ⊗₁ id) ⊗₁ w ∘ swp))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swp-nat v w id ⟩
  swp ∘ (k′ ⊗₁ id ∘ (swp ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (swp ∘ (k′ ⊗₁ id ∘ swp)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

onR-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : Q ⊗₀ X ⇒ Q ⊗₀ Y} {k′ : Z ⊗₀ X ⇒ Z ⊗₀ Y}
        → w ⊗₁ id ∘ k ≈ k′ ∘ w ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id {Y} ∘ onR k ≈ onR k′ ∘ (v ⊗₁ w) ⊗₁ id {X}
onR-sim {v = v} {w} {k} {k′} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (v ⊗₁ (w ⊗₁ id) ∘ (id ⊗₁ k ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm e) ⟩
  α⇐ ∘ ((id ⊗₁ k′ ∘ v ⊗₁ (w ⊗₁ id)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ k′ ∘ (v ⊗₁ (w ⊗₁ id) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ k′ ∘ (α⇒ ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ k′ ∘ α⇒)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

-- The state-side arm of the interchange: braiding the state pair swaps which
-- factor acts.  The braiding crosses `k`'s whole block, so `unbraid` puts the
-- padding on one side and the two residual obligations are the block hexagon
-- (`σ-splitˡ`/`σ-splitʳ`).
σ-onR : {k : Q ⊗₀ A ⇒ Q ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onR {P = P} k ≈ onL {Q = P} k ∘ σ⇒ ⊗₁ id {A}
σ-onR {k = k} = begin
  σ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))              ≈⟨ sym-assoc ⟩
  (σ⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ k ∘ α⇒)              ≈⟨ unbraid k ⟩
  ((σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇒) ∘ (k ⊗₁ id ∘ (σ⇒ ∘ α⇒))
    ≈⟨ out ⟩∘⟨ (refl⟩∘⟨ inn) ⟩
  swp ∘ (k ⊗₁ id ∘ (swp ∘ σ⇒ ⊗₁ id))            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  swp ∘ ((k ⊗₁ id ∘ swp) ∘ σ⇒ ⊗₁ id)            ≈⟨ sym-assoc ⟩
  (swp ∘ (k ⊗₁ id ∘ swp)) ∘ σ⇒ ⊗₁ id            ∎
  where
    out : (σ⇒ {P} {Q} ⊗₁ id {B} ∘ α⇐) ∘ σ⇒ ≈ swp
    out = (refl⟩∘⟨ σ-splitʳ) ○ cancelInner associator.isoˡ
        ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

    inn : σ⇒ {P} {Q ⊗₀ A} ∘ α⇒ ≈ swp ∘ σ⇒ ⊗₁ id
    inn = (σ-splitˡ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ
        ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc

-- …and the mirror arm follows by conjugating with the braiding.
σ-onL : {k : P ⊗₀ A ⇒ P ⊗₀ B}
      → σ⇒ {P} {Q} ⊗₁ id {B} ∘ onL {Q = Q} k ≈ onR {P = Q} k ∘ σ⇒ ⊗₁ id {A}
σ-onL {k = k} = begin
  σ⇒ ⊗₁ id ∘ onL k                        ≈˘⟨ refl⟩∘⟨ cancelʳ σ⊗-inv ⟩
  σ⇒ ⊗₁ id ∘ ((onL k ∘ σ⇒ ⊗₁ id) ∘ σ⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ σ-onR ⟩∘⟨refl ⟩
  σ⇒ ⊗₁ id ∘ ((σ⇒ ⊗₁ id ∘ onR k) ∘ σ⇒ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  σ⇒ ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ (onR k ∘ σ⇒ ⊗₁ id))
    ≈⟨ cancelˡ σ⊗-inv ⟩
  onR k ∘ σ⇒ ⊗₁ id                        ∎

-- The reflection frontend wants the `MonoidalCategory` bundle.
𝕄 : MonoidalCategory o ℓ e
𝕄 = record { U = U ; monoidal = monoidal }

-- One generator `k : P ⊗ X ⇒ P ⊗ Y`, four object atoms besides.
module OneGen (P Q X Y Z : Obj) (k : P ⊗₀ X ⇒ P ⊗₀ Y) where

  -- The left state factor acting on interface slot 1 is an `Ω`-conjugate: the
  -- same crossing `σ⇒ {Q} {X}` sits on both sides, so it is an opaque box and
  -- the Mon arm decides the goal.
  slot₁-onL : slot₁ {Z = Z} (onL {Q = Q} k) ≈ Ω ∘ k ⊗₁ id ∘ Ω
  slot₁-onL = solve-mor 𝕄

  -- Going the other way round, the padding comes out as `Z ⊗ Q` instead of
  -- `Q ⊗ Z` (`repad-σ`), and `onL` crosses `Q` with the whole interface block —
  -- a crossing block the macro cannot split, so `σ-splitˡ`/`σ-splitʳ` split it
  -- by hand first and only then is the goal solver food.
  private
    onL-split : {S₁ S₂ T₁ T₂ : Obj} (h : P ⊗₀ (S₁ ⊗₀ S₂) ⇒ P ⊗₀ (T₁ ⊗₀ T₂))
              → onL {Q = Q} h
              ≈ (α⇐ ∘ (id ⊗₁ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)) ∘ α⇒))
                ∘ h ⊗₁ id
                ∘ (α⇐ ∘ (id ⊗₁ ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ α⇒))
    onL-split _ = (refl⟩∘⟨ refl⟩⊗⟨ σ-splitʳ ⟩∘⟨refl)
                    ⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩⊗⟨ σ-splitˡ ⟩∘⟨refl)

    -- `solve-mor` cannot read this one: after the split the two sides mention
    -- the same crossings, but the macro's object parser stores some of the
    -- compound endpoints as fresh atoms and then sees one box at two arities.
    -- Naming the four crossings as generators sidesteps the parse entirely.
    onL-slot₁ : onL {Q = Q} (slot₁ {Z = Z} k) ≈ (Ω ∘ id ⊗₁ σ⇒) ∘ k ⊗₁ id ∘ (id ⊗₁ σ⇒ ∘ Ω)
    onL-slot₁ = onL-split (slot₁ k) ○
      (let vs = P ∷ Q ∷ X ∷ Y ∷ Z ∷ []
           open MorAtoms 𝕄 vs
           open MorSolve 𝕄 vs
                ( ((V (# 0) ⊗ᵒ V (# 2) , V (# 0) ⊗ᵒ V (# 3)) , k)
                ∷ ((V (# 1) ⊗ᵒ V (# 2) , V (# 2) ⊗ᵒ V (# 1)) , σ⇒)
                ∷ ((V (# 1) ⊗ᵒ V (# 4) , V (# 4) ⊗ᵒ V (# 1)) , σ⇒)
                ∷ ((V (# 3) ⊗ᵒ V (# 1) , V (# 1) ⊗ᵒ V (# 3)) , σ⇒)
                ∷ ((V (# 4) ⊗ᵒ V (# 1) , V (# 1) ⊗ᵒ V (# 4)) , σ⇒) ∷ [] )
           p = V (# 0); q = V (# 1); x = V (# 2); y = V (# 3); z = V (# 4)
           k′ = gen (# 0); σqx = gen (# 1); σqz = gen (# 2)
           σyq = gen (# 3); σzq = gen (# 4)
           -- `swp` at the two atom triples, and the two hexagon splits
           swpᵢ = S.α⇐ S.∘ S.id {p} S.⊗₁ σqx S.∘ S.α⇒
           swpₒ = S.α⇐ S.∘ S.id {p} S.⊗₁ σyq S.∘ S.α⇒
           Ωᵢ = S.α⇒ S.∘ swpᵢ S.⊗₁ S.id {z} S.∘ S.α⇐
           Ωₒ = S.α⇒ S.∘ swpₒ S.⊗₁ S.id {z} S.∘ S.α⇐
           splitˡ = (S.α⇐ S.∘ (S.id {x} S.⊗₁ σqz S.∘ (S.α⇒ S.∘ σqx S.⊗₁ S.id {z})))
                      S.∘ S.α⇐
           splitʳ = S.α⇒ S.∘ (((σyq S.⊗₁ S.id {z} S.∘ S.α⇐) S.∘ S.id {y} S.⊗₁ σzq)
                      S.∘ S.α⇒)
           swpSplitˡ = S.α⇐ S.∘ (S.id {p} S.⊗₁ splitˡ S.∘ S.α⇒)
           swpSplitʳ = S.α⇐ S.∘ (S.id {p} S.⊗₁ splitʳ S.∘ S.α⇒)
           slot₁ᵀ = S.α⇒ S.∘ k′ S.⊗₁ S.id {z} S.∘ S.α⇐
       in solveMor! (swpSplitʳ S.∘ slot₁ᵀ S.⊗₁ S.id {q} S.∘ swpSplitˡ)
                    ((Ωₒ S.∘ S.id {p ⊗ᵒ y} S.⊗₁ σzq)
                     S.∘ k′ S.⊗₁ S.id {z ⊗ᵒ q}
                     S.∘ (S.id {p ⊗ᵒ x} S.⊗₁ σqz S.∘ Ωᵢ)))

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
  Ω≈Ω′ = Ω≈swapInner

-- The right state factor's actions commute with both interface slots.
module OneGenʳ (P Q X Y Z : Obj) (k : Q ⊗₀ X ⇒ Q ⊗₀ Y) where

  slot₁-onR : slot₁ {Z = Z} (onR {P = P} k) ≈ onR (slot₁ k)
  slot₁-onR = solve-mor 𝕄

  slot₂-onR : slot₂ {Z = Z} (onR {P = P} k) ≈ onR (slot₂ k)
  slot₂-onR = solve-mor 𝕄

  private
    -- `tuck`/`untuck` route the interface pair past the state through a single
    -- block crossing; `swapˡ` routes it through two atomic ones, so these two
    -- are hexagon instances (hence `σ-splitˡ`/`σ-splitʳ` first).
    tuck-swapˡ : tuck {P = Q} {Q = Z} {R = X} ≈ σ⇒ ∘ swapˡ
    tuck-swapˡ = ⟺ (begin
      σ⇒ ∘ swapˡ
        ≈⟨ σ-splitˡ ⟩∘⟨refl ⟩
      ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id ∘ α⇐))
        ≈⟨ cancelInner associator.isoˡ ⟩
      (α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ (σ⇒ ⊗₁ id ∘ α⇐)
        ≈⟨ (refl⟩∘⟨ sym-assoc) ⟩∘⟨refl ⟩
      (α⇐ ∘ ((id ⊗₁ σ⇒ ∘ α⇒) ∘ σ⇒ ⊗₁ id)) ∘ (σ⇒ ⊗₁ id ∘ α⇐)
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ σ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id ∘ α⇐)
        ≈⟨ cancelInner σ⊗-inv ⟩
      (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)) ∘ α⇐
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((α⇐ ∘ id ⊗₁ σ⇒) ∘ α⇒) ∘ α⇐
        ≈⟨ cancelʳ associator.isoʳ ⟩
      tuck ∎)

    untuck-swapˡ : untuck {P = Q} {R = Y} {Q = Z} ≈ swapˡ ∘ σ⇒
    untuck-swapˡ = ⟺ (begin
      swapˡ ∘ σ⇒
        ≈⟨ refl⟩∘⟨ σ-splitʳ ⟩
      (α⇒ ∘ (σ⇒ ⊗₁ id ∘ α⇐)) ∘ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒))
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒))
        ≈⟨ cancelInner associator.isoˡ ⟩
      (α⇒ ∘ σ⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (α⇒ ∘ σ⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⇒ ∘ α⇒))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (α⇒ ∘ σ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒)))
        ≈⟨ cancelInner σ⊗-inv ⟩
      α⇒ ∘ (α⇐ ∘ (id ⊗₁ σ⇒ ∘ α⇒))
        ≈⟨ cancelˡ associator.isoʳ ⟩
      untuck ∎)

    Ω≈Ω′ᵢ : Ω {P} {Q} {Z} {X} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
    Ω≈Ω′ᵢ = Ω≈swapInner

    Ω≈Ω′ₒ : Ω {P} {Z} {Q} {Y} ≈ α⇐ ∘ id ⊗₁ swapˡ ∘ α⇒
    Ω≈Ω′ₒ = Ω≈swapInner

  -- Slot 2 acted on by the right state factor is a `swapˡ`-conjugate…
  slot₂-swapˡ : slot₂ {Z = Z} k ≈ swapˡ ∘ id ⊗₁ k ∘ swapˡ
  slot₂-swapˡ = (untuck-swapˡ ⟩∘⟨ (refl⟩∘⟨ tuck-swapˡ)) ○ ⟺ (unbraid k)

  -- …and `onR` turns that into the `Ω`-conjugate: the half of the interchange
  -- the solver declines (`lim-straddle`, the padding `P ⊗ Z` straddling `k`).
  slot₂-onR-Ω : slot₂ {Z = Z} (onR {P = P} k) ≈ Ω ∘ id ⊗₁ k ∘ Ω
  slot₂-onR-Ω = slot₂-onR ○ onR-cong slot₂-swapˡ ○ onRᵍ-⊗
              ○ ((⟺ Ω≈Ω′ₒ) ⟩∘⟨ (refl⟩∘⟨ (⟺ Ω≈Ω′ᵢ)))

------------------------------------------------------------------------
-- The two state factors act on complementary interface slots
------------------------------------------------------------------------

-- What the general `trace-∘` needs: composing machines pairs their states,
-- unrolling them pairs their interfaces, and the two pairings commute because
-- the two actions touch complementary tensor factors.  At `𝒱 = Kleisli M` that
-- interchange IS the monad's commutativity, which is why the elementwise layer
-- needs `Discrete.Commutative` for exactly this lemma and nothing else.

-- Both sides are the `Ω`-conjugate of `g ⊗₁ f`; only the order in which the
-- two disjoint boxes fire differs.
slot-comm : {g : P ⊗₀ B ⇒ P ⊗₀ C} {f : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
          → slot₂ {Z = C} (onR {P = P} f) ∘ slot₁ {Z = A′} (onL {Q = Q} g)
          ≈ slot₁ {Z = B′} (onL {Q = Q} g) ∘ slot₂ {Z = B} (onR {P = P} f)
slot-comm {P = P} {B} {C} {Q} {A′} {B′} {g} {f} = begin
  slot₂ (onR f) ∘ slot₁ (onL g)
    ≈⟨ Gᶠ.slot₂-onR-Ω ⟩∘⟨ Gᵍ.slot₁-onL ⟩
  (Ω ∘ (id ⊗₁ f ∘ Ω)) ∘ (Ω ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ center (cancelʳ Ω-involutive) ⟩
  Ω ∘ (id ⊗₁ f ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁ ○ serialize₁₂) ⟩
  Ω ∘ ((g ⊗₁ id ∘ id ⊗₁ f) ∘ Ω)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  Ω ∘ (g ⊗₁ id ∘ (id ⊗₁ f ∘ Ω))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ Ω-involutive ⟩
  Ω ∘ (g ⊗₁ id ∘ (Ω ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  Ω ∘ ((g ⊗₁ id ∘ Ω) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω)))
    ≈⟨ sym-assoc ⟩
  (Ω ∘ (g ⊗₁ id ∘ Ω)) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))
    ≈˘⟨ Gᵍ′.slot₁-onL ⟩∘⟨ Gᶠ′.slot₂-onR-Ω ⟩
  slot₁ (onL g) ∘ slot₂ (onR f)  ∎
  where
    module Gᵍ  = OneGen  P Q B C A′ g
    module Gᵍ′ = OneGen  P Q B C B′ g
    module Gᶠ  = OneGenʳ P Q A′ B′ C f
    module Gᶠ′ = OneGenʳ P Q A′ B′ B f

-- Slotting a composite step: this is the whole content of `run-∘`.
compK-slot : {g₁ : P ⊗₀ B ⇒ P ⊗₀ C} {f₁ : Q ⊗₀ A ⇒ Q ⊗₀ B}
             {g₂ : P ⊗₀ B′ ⇒ P ⊗₀ C′} {f₂ : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
           → slot₂ {Z = C} (compK g₂ f₂) ∘ slot₁ {Z = A′} (compK g₁ f₁)
           ≈ compK (slot₂ g₂ ∘ slot₁ g₁) (slot₂ f₂ ∘ slot₁ f₁)
compK-slot {P = P} {B} {C} {Q} {A} {B′} {C′} {A′} {g₁} {f₁} {g₂} {f₂} = begin
  slot₂ (onL g₂ ∘ onR f₂) ∘ slot₁ (onL g₁ ∘ onR f₁)
    ≈⟨ slot₂ᵍ-∘ ⟩∘⟨ slot₁ᵍ-∘ ⟩
  (slot₂ (onL g₂) ∘ slot₂ (onR f₂)) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁))
    ≈⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₂ (onR f₂) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  slot₂ (onL g₂) ∘ ((slot₂ (onR f₂) ∘ slot₁ (onL g₁)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ slot-comm ⟩∘⟨refl ⟩
  slot₂ (onL g₂) ∘ ((slot₁ (onL g₁) ∘ slot₂ (onR f₂)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₁ (onL g₁) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁)))
    ≈⟨ sym-assoc ⟩
  (slot₂ (onL g₂) ∘ slot₁ (onL g₁)) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁))
    ≈⟨ (Hᵍ.slot₂-onL-comm ⟩∘⟨ Hᵍ′.slot₁-onL-comm) ⟩∘⟨ (Hᶠ.slot₂-onR ⟩∘⟨ Hᶠ′.slot₁-onR) ⟩
  (onL (slot₂ g₂) ∘ onL (slot₁ g₁)) ∘ (onR (slot₂ f₂) ∘ onR (slot₁ f₁))
    ≈˘⟨ onL-∘ ⟩∘⟨ onRᵍ-∘ ⟩
  onL (slot₂ g₂ ∘ slot₁ g₁) ∘ onR (slot₂ f₂ ∘ slot₁ f₁)  ∎
  where
    module Hᵍ  = OneGen  P Q B′ C′ C g₂
    module Hᵍ′ = OneGen  P Q B  C  B′ g₁
    module Hᶠ  = OneGenʳ P Q A′ B′ B f₂
    module Hᶠ′ = OneGenʳ P Q A  B  A′ f₁

------------------------------------------------------------------------
-- Closing off the state
------------------------------------------------------------------------

-- `Spike.Mealy`'s `eval f n` is `cl (discard (state f)) (point (state f))
-- (run f n)`.
cl : (K₁ ⇒ unit) → (unit ⇒ K₁) → (K₁ ⊗₀ X ⇒ K₁ ⊗₀ Y) → X ⇒ Y
cl d p R = λ⇒ ∘ d ⊗₁ id ∘ R ∘ p ⊗₁ id ∘ λ⇐

-- Discarding / pointing the second factor of a paired state.
dsc : (Q ⇒ unit) → P ⊗₀ Q ⇒ P
dsc d = ρ⇒ ∘ id ⊗₁ d

psc : (unit ⇒ Q) → P ⇒ P ⊗₀ Q
psc p = id ⊗₁ p ∘ ρ⇐

cl-cong : {d : P ⇒ unit} {p : unit ⇒ P} {R R′ : P ⊗₀ A ⇒ P ⊗₀ B}
        → R ≈ R′ → cl d p R ≈ cl d p R′
cl-cong e = refl⟩∘⟨ refl⟩∘⟨ e ⟩∘⟨refl

cl-resp : {d d′ : P ⇒ unit} {p p′ : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B}
        → d ≈ d′ → p ≈ p′ → cl d p R ≈ cl d′ p′ R
cl-resp e₁ e₂ = refl⟩∘⟨ ((e₁ ⟩⊗⟨refl) ⟩∘⟨ (refl⟩∘⟨ ((e₂ ⟩⊗⟨refl) ⟩∘⟨refl)))

-- An action on the interface alone comes out of the closure.
cl-∘ʳ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B} {h : C ⇒ A}
      → cl d p (R ∘ id ⊗₁ h) ≈ cl d p R ∘ h
cl-∘ʳ {d = d} {p} {R} {h} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((R ∘ id ⊗₁ h) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (id ⊗₁ h ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pad-transport p h) ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ ((p ⊗₁ id ∘ id ⊗₁ h) ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ (id ⊗₁ h ∘ λ⇐))))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ (λ⇐ ∘ h))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ ((p ⊗₁ id ∘ λ⇐) ∘ h)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ ((R ∘ (p ⊗₁ id ∘ λ⇐)) ∘ h))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ ((d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))) ∘ h)
    ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))) ∘ h  ∎

-- …and so does an action on the interface alone on the other side.
cl-∘ˡ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B} {h : B ⇒ C}
      → cl d p (id ⊗₁ h ∘ R) ≈ h ∘ cl d p R
cl-∘ˡ {d = d} {p} {R} {h} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((id ⊗₁ h ∘ R) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (id ⊗₁ h ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (pad-transport d h)) ⟩
  λ⇒ ∘ ((id ⊗₁ h ∘ d ⊗₁ id) ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (id ⊗₁ h ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  h ∘ (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))  ∎

-- Slotting into the first interface factor comes out of the closure untouched:
-- this is what turns a word's `A`-subrun back into `eval f`.
cl-slot₁ : {d : P ⇒ unit} {p : unit ⇒ P} {R : P ⊗₀ A ⇒ P ⊗₀ B}
         → cl d p (slot₁ {Z = C} R) ≈ cl d p R ⊗₁ id
cl-slot₁ {d = d} {p} {R} = begin
  λ⇒ ∘ (d ⊗₁ id ∘ ((α⇒ ∘ (R ⊗₁ id ∘ α⇐)) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc)) ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (α⇒ ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐)))))
    ≈⟨ refl⟩∘⟨ pullˡ (pad-α⇒ d) ⟩
  λ⇒ ∘ ((α⇒ ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ pullˡ (pullˡ coherence₁) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (α⇐ ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pad-α⇐ p) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ (((p ⊗₁ id) ⊗₁ id ∘ α⇐) ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ coherence-inv₁)) ⟩
  (λ⇒ ⊗₁ id ∘ (d ⊗₁ id) ⊗₁ id) ∘ (R ⊗₁ id ∘ ((p ⊗₁ id) ⊗₁ id ∘ λ⇐ ⊗₁ id))
    ≈⟨ merge₁ˡ ⟩∘⟨ ((refl⟩∘⟨ merge₁ˡ) ○ merge₁ˡ) ⟩
  (λ⇒ ∘ d ⊗₁ id) ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)) ⊗₁ id
    ≈⟨ merge₁ˡ ○ (assoc ⟩⊗⟨refl) ⟩
  (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))) ⊗₁ id  ∎

-- A state map that conjugates the two runs identifies their closures; `sim` is
-- this at every unrolling.
cl-sim : {d : P ⇒ unit} {p : unit ⇒ P} {d′ : Q ⇒ unit} {p′ : unit ⇒ Q}
         {R : P ⊗₀ A ⇒ P ⊗₀ B} {R′ : Q ⊗₀ A ⇒ Q ⊗₀ B} (u : P ⇒ Q)
       → d′ ∘ u ≈ d → u ∘ p ≈ p′ → u ⊗₁ id ∘ R ≈ R′ ∘ u ⊗₁ id
       → cl d p R ≈ cl d′ p′ R′
cl-sim {d = d} {p} {d′} {p′} {R} {R′} u ed ep e = begin
  λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈˘⟨ refl⟩∘⟨ ed ⟩⊗⟨refl ⟩∘⟨refl ⟩
  λ⇒ ∘ ((d′ ∘ u) ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ○ (refl⟩∘⟨ assoc) ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ e ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ ((R′ ∘ u ⊗₁ id) ∘ (p ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (R′ ∘ (u ⊗₁ id ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ ep ⟩⊗⟨refl) ⟩
  λ⇒ ∘ (d′ ⊗₁ id ∘ (R′ ∘ (p′ ⊗₁ id ∘ λ⇐)))  ∎

-- A factorization of the point and the discard factors out of the closure.
cl-factor : {d : P ⇒ unit} {p : unit ⇒ P} {u : Q ⇒ P} {v : P ⇒ Q}
            {R : Q ⊗₀ A ⇒ Q ⊗₀ B}
          → cl (d ∘ u) (v ∘ p) R ≈ cl d p (u ⊗₁ id ∘ (R ∘ v ⊗₁ id))
cl-factor {d = d} {p} {u} {v} {R} = begin
  λ⇒ ∘ ((d ∘ u) ⊗₁ id ∘ (R ∘ ((v ∘ p) ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ (split₁ˡ ⟩∘⟨ (refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl))) ⟩
  λ⇒ ∘ ((d ⊗₁ id ∘ u ⊗₁ id) ∘ (R ∘ ((v ⊗₁ id ∘ p ⊗₁ id) ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ ((v ⊗₁ id ∘ p ⊗₁ id) ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ (R ∘ (v ⊗₁ id ∘ (p ⊗₁ id ∘ λ⇐)))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ (u ⊗₁ id ∘ ((R ∘ v ⊗₁ id) ∘ (p ⊗₁ id ∘ λ⇐))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (d ⊗₁ id ∘ ((u ⊗₁ id ∘ (R ∘ v ⊗₁ id)) ∘ (p ⊗₁ id ∘ λ⇐)))  ∎

-- `_⊛_`'s discard and point factor as "discard/point the second factor, then
-- the first".
discard-pair : (dp : P ⇒ unit) (dq : Q ⇒ unit) → λ⇒ ∘ dp ⊗₁ dq ≈ dp ∘ dsc dq
discard-pair dp dq = begin
  λ⇒ ∘ dp ⊗₁ dq                ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
  λ⇒ ∘ (dp ⊗₁ id ∘ id ⊗₁ dq)   ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ dp ⊗₁ id) ∘ id ⊗₁ dq   ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (ρ⇒ ∘ dp ⊗₁ id) ∘ id ⊗₁ dq   ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
  (dp ∘ ρ⇒) ∘ id ⊗₁ dq         ≈⟨ assoc ⟩
  dp ∘ (ρ⇒ ∘ id ⊗₁ dq)         ∎

point-pair : (pp : unit ⇒ P) (pq : unit ⇒ Q) → pp ⊗₁ pq ∘ λ⇐ ≈ psc pq ∘ pp
point-pair pp pq = begin
  pp ⊗₁ pq ∘ λ⇐                ≈⟨ serialize₂₁ ⟩∘⟨refl ⟩
  (id ⊗₁ pq ∘ pp ⊗₁ id) ∘ λ⇐   ≈⟨ assoc ⟩
  id ⊗₁ pq ∘ (pp ⊗₁ id ∘ λ⇐)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
  id ⊗₁ pq ∘ (pp ⊗₁ id ∘ ρ⇐)   ≈˘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
  id ⊗₁ pq ∘ (ρ⇐ ∘ pp)         ≈⟨ sym-assoc ⟩
  (id ⊗₁ pq ∘ ρ⇐) ∘ pp         ∎

-- The braiding is trivial on the unit, so it leaves a paired point and a paired
-- discard alone.
σ-unit : σ⇒ {unit} {unit} ≈ id
σ-unit = insertˡ unitorˡ.isoˡ ○ (refl⟩∘⟨ (braiding-coherence ○ ⟺ coherence₃))
       ○ unitorˡ.isoˡ

------------------------------------------------------------------------
-- Closing the second state factor of a composite step
------------------------------------------------------------------------

ρα-λ : ρ⇒ {P} ⊗₁ id {A} ∘ α⇐ ≈ id ⊗₁ λ⇒
ρα-λ = ((⟺ triangle) ⟩∘⟨refl) ○ cancelʳ associator.isoʳ

αρ-λ : α⇒ ∘ ρ⇐ {P} ⊗₁ id {A} ≈ id ⊗₁ λ⇐
αρ-λ = (refl⟩∘⟨ (⟺ triangle-inv)) ○ cancelˡ associator.isoʳ

ρ-swp : ρ⇒ {P} ⊗₁ id {A} ∘ swp ≈ ρ⇒
ρ-swp = pullˡ ρα-λ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ braiding-coherence) ○ coherence₂

dsc-swp : {d : Q ⇒ unit} → dsc {P = P} d ⊗₁ id {A} ∘ swp ≈ ρ⇒ ∘ id ⊗₁ d
dsc-swp {d = d} = begin
  (ρ⇒ ∘ id ⊗₁ d) ⊗₁ id ∘ swp            ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  (ρ⇒ ⊗₁ id ∘ (id ⊗₁ d) ⊗₁ id) ∘ swp    ≈⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ swp)    ≈˘⟨ refl⟩∘⟨ swp-natural d ⟩
  ρ⇒ ⊗₁ id ∘ (swp ∘ id ⊗₁ d)            ≈⟨ pullˡ ρ-swp ⟩
  ρ⇒ ∘ id ⊗₁ d                          ∎

-- `onL` does not see the second state factor, so closing it passes through.
discard-onL : {d : Q ⇒ unit} {R : P ⊗₀ A ⇒ P ⊗₀ B}
            → dsc d ⊗₁ id {B} ∘ onL R ≈ R ∘ dsc d ⊗₁ id {A}
discard-onL {d = d} {R} = begin
  dsc d ⊗₁ id ∘ (swp ∘ (R ⊗₁ id ∘ swp))
    ≈⟨ pullˡ dsc-swp ⟩
  (ρ⇒ ∘ id ⊗₁ d) ∘ (R ⊗₁ id ∘ swp)
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (id ⊗₁ d ∘ (R ⊗₁ id ∘ swp))
    ≈⟨ refl⟩∘⟨ pullˡ (pad-transport R d) ⟩
  ρ⇒ ∘ ((R ⊗₁ id ∘ id ⊗₁ d) ∘ swp)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (R ⊗₁ id ∘ (id ⊗₁ d ∘ swp))
    ≈⟨ pullˡ unitorʳ-commute-from ⟩
  (R ∘ ρ⇒) ∘ (id ⊗₁ d ∘ swp)
    ≈⟨ assoc ⟩
  R ∘ (ρ⇒ ∘ (id ⊗₁ d ∘ swp))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  R ∘ ((ρ⇒ ∘ id ⊗₁ d) ∘ swp)
    ≈˘⟨ refl⟩∘⟨ dsc-swp ⟩∘⟨refl ⟩
  R ∘ ((dsc d ⊗₁ id ∘ swp) ∘ swp)
    ≈⟨ refl⟩∘⟨ cancelʳ swp-swp ⟩
  R ∘ dsc d ⊗₁ id  ∎

-- …and closing it around `onR` is exactly `eval` of the second factor.
discard-onR : {d : Q ⇒ unit} {p : unit ⇒ Q} {R : Q ⊗₀ A ⇒ Q ⊗₀ B}
            → dsc d ⊗₁ id {B} ∘ (onR {P = P} R ∘ psc p ⊗₁ id {A})
            ≈ id {P} ⊗₁ cl d p R
discard-onR {d = d} {p} {R} = begin
  dsc d ⊗₁ id ∘ (onR R ∘ psc p ⊗₁ id)
    ≈⟨ split₁ˡ ⟩∘⟨ (refl⟩∘⟨ split₁ˡ) ⟩
  (ρ⇒ ⊗₁ id ∘ (id ⊗₁ d) ⊗₁ id) ∘ (onR R ∘ ((id ⊗₁ p) ⊗₁ id ∘ ρ⇐ ⊗₁ id))
    ≈⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ (onR R ∘ ((id ⊗₁ p) ⊗₁ id ∘ ρ⇐ ⊗₁ id)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  ρ⇒ ⊗₁ id ∘ ((id ⊗₁ d) ⊗₁ id ∘ ((onR R ∘ (id ⊗₁ p) ⊗₁ id) ∘ ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  ρ⇒ ⊗₁ id ∘ (((id ⊗₁ d) ⊗₁ id ∘ (onR R ∘ (id ⊗₁ p) ⊗₁ id)) ∘ ρ⇐ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ (onRᵍ-⊗id d ⟩∘⟨ (refl⟩∘⟨ onRᵍ-⊗id p)) ⟩∘⟨refl ⟩
  ρ⇒ ⊗₁ id ∘ ((onRᵍ (d ⊗₁ id) ∘ (onRᵍ R ∘ onRᵍ (p ⊗₁ id))) ∘ ρ⇐ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ (onRᵍ-∘ ○ (refl⟩∘⟨ onRᵍ-∘)) ⟩∘⟨refl ⟩
  ρ⇒ ⊗₁ id ∘ (onRᵍ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ⊗₁ id ∘ (α⇐ ∘ ((id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ α⇒) ∘ ρ⇐ ⊗₁ id))
    ≈⟨ pullˡ ρα-λ ⟩
  id ⊗₁ λ⇒ ∘ ((id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ α⇒) ∘ ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  id ⊗₁ λ⇒ ∘ (id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ (α⇒ ∘ ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ αρ-λ ⟩
  id ⊗₁ λ⇒ ∘ (id ⊗₁ (d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ id ⊗₁ λ⇐)
    ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
  id ⊗₁ λ⇒ ∘ id ⊗₁ ((d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ λ⇐)
    ≈⟨ merge₂ʳ ⟩
  id ⊗₁ (λ⇒ ∘ ((d ⊗₁ id ∘ (R ∘ p ⊗₁ id)) ∘ λ⇐))
    ≈⟨ refl⟩⊗⟨ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc))) ⟩
  id ⊗₁ (λ⇒ ∘ (d ⊗₁ id ∘ (R ∘ (p ⊗₁ id ∘ λ⇐))))  ∎

------------------------------------------------------------------------
-- Collapsing a trivial state factor
------------------------------------------------------------------------

IˢIˢ-closed : discard (Iˢ ⊛ Iˢ) ∘ point (Iˢ ⊛ Iˢ) ≈ id
IˢIˢ-closed = (elimʳ ⊗.identity ⟩∘⟨ elimˡ ⊗.identity) ○ unitorˡ.isoʳ

-- A trivial left state factor sees an `onR` action as the action itself…
onR-collapseˡ : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → λ⇒ ⊗₁ id ∘ onR k ≈ k ∘ λ⇒ ⊗₁ id
onR-collapseˡ {k = k} = begin
  λ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))   ≈˘⟨ coherence₁ ⟩∘⟨refl ⟩
  (λ⇒ ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))  ≈⟨ cancelInner associator.isoʳ ⟩
  λ⇒ ∘ (id ⊗₁ k ∘ α⇒)                ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  k ∘ (λ⇒ ∘ α⇒)                      ≈⟨ refl⟩∘⟨ coherence₁ ⟩
  k ∘ λ⇒ ⊗₁ id                       ∎

-- …and a trivial right one an `onL` action, which is `discard-onL` at `id`.
onL-collapseʳ : {k : P ⊗₀ A ⇒ P ⊗₀ B} → ρ⇒ ⊗₁ id ∘ onL k ≈ k ∘ ρ⇒ ⊗₁ id
onL-collapseʳ {P = P} =
    ((⟺ dsc-id) ⟩⊗⟨refl ⟩∘⟨refl) ○ discard-onL ○ (refl⟩∘⟨ dsc-id ⟩⊗⟨refl)
  where
    dsc-id : dsc (id {unit}) ≈ ρ⇒ {P}
    dsc-id = elimʳ ⊗.identity

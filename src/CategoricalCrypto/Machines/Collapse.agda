{-# OPTIONS --safe --without-K --guardedness #-}

-- A G-composite of two machines as ONE traced machine with a readable step.
--
-- `𝒢ₚ` hands `g ∘ f` over as `trace (α ∘ (g ⊗ᵉ f) ∘ γ)`, two structural legs
-- around the interface tensor.  Both legs are pure — every factor of
-- `Categories.GConstructionTrace`'s `α`/`γ` is an associator or a braiding — so
-- `pure-∘ˡ`/`pure-∘ʳ` fold them into the tensor's own step, and what survives is
-- `kᴳ`: a four-way dispatch sending each letter to the factor that owns it and
-- routing that factor's emission out or around the loop.  Any consumer that has
-- to read a `𝒢ₚ`-composite's step off starts here.
--
-- The point calculus the legs are read with is `Machines.Pointwise`.  Everything here stays inside `ℳₚ` and measures 16 s warm.
-- `collapseᵀ` is stated as a trace rather than as `𝒢ₚ`'s `_∘_` on purpose: a
-- consumer's goal names `_∘_` already, so leaving the projection out of the
-- G-construction record to the consumer costs ONE such projection, while a
-- lemma stated with `_∘_` costs the consumer a second one — measured at 269 s
-- against 704 s (`Protocol.Machine.Compose`) and 282 s against 507 s
-- (`UC.Seam.Adequacy.Wiring`).  Opaque machine composition keeps that boundary
-- nominal instead of eta-expanding both composite records.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
import Categories.GConstruction as GC
import Categories.GConstructionTrace as GT

open import Data.Product.Base
open import Data.Sum.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure

import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.Machines.Collapse where


module MT  = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
module TC  = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

module ℳ   = SymmetricMonoidalCategory (ℳₚ 0ℓ)
module W   = GT ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
module 𝒢   = Category (𝒢ₚ 0ℓ)

private
  variable P Q X Y : Set

------------------------------------------------------------------------
-- The two structural legs of a G-composite

αᶠ : (P ⊎ Q) ⊎ (X ⊎ Y) → (X ⊎ Q) ⊎ (P ⊎ Y)
αᶠ (inj₁ (inj₁ p)) = inj₂ (inj₁ p)
αᶠ (inj₁ (inj₂ q)) = inj₁ (inj₂ q)
αᶠ (inj₂ (inj₁ r)) = inj₁ (inj₁ r)
αᶠ (inj₂ (inj₂ s)) = inj₂ (inj₂ s)

γᶠ : (P ⊎ Q) ⊎ (X ⊎ Y) → (Y ⊎ Q) ⊎ (P ⊎ X)
γᶠ (inj₁ (inj₁ p)) = inj₂ (inj₁ p)
γᶠ (inj₁ (inj₂ q)) = inj₁ (inj₂ q)
γᶠ (inj₂ (inj₁ r)) = inj₂ (inj₂ r)
γᶠ (inj₂ (inj₂ s)) = inj₁ (inj₁ s)

α-pure : (P Q R N : Set) → W.α {R} {N} {P} {Q} S.≈ᴹ pureᶠ (αᶠ {P} {Q} {R} {N})
α-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (α⇒ᶠ P Q (R ⊎ N)) (⊗ᶠ (idᶠ P) (α⇐ᶠ Q R N)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q R) (idᶠ N))))
             (α⇐ᶠ P (R ⊎ Q) N))
         (⊗ᶠ (σᶠ P (R ⊎ Q)) (idᶠ N)))
     (α⇒ᶠ (R ⊎ Q) P N)
  S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

γ-pure : (P Q R N : Set) → W.γ {P} {N} {R} {Q} S.≈ᴹ pureᶠ (γᶠ {P} {Q} {R} {N})
γ-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (⊗ᶠ (idᶠ (P ⊎ Q)) (σᶠ R N)) (α⇒ᶠ P Q (N ⊎ R)))
                     (⊗ᶠ (idᶠ P) (α⇐ᶠ Q N R)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q N) (idᶠ R))))
             (α⇐ᶠ P (N ⊎ Q) R))
         (⊗ᶠ (σᶠ P (N ⊎ Q)) (idᶠ R)))
     (α⇒ᶠ (N ⊎ Q) P R)
  S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

------------------------------------------------------------------------
-- The collapsed step

-- Where each factor's emission goes: the shared interface `B` re-enters the
-- trace's loop, the outer interfaces `A` and `C` leave.
module _ {A⁻ B⁺ B⁻ C⁺ : Set} where

  outᶠ : A⁻ ⊎ B⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outᶠ (inj₁ a) = inj₁ (inj₁ a)
  outᶠ (inj₂ b) = inj₂ (inj₂ b)

  outᵍ : B⁻ ⊎ C⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outᵍ (inj₁ b) = inj₂ (inj₁ b)
  outᵍ (inj₂ c) = inj₁ (inj₂ c)

opaque
  composeᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set} →
             MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺) →
             MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) →
             MC.Machine (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
  composeᴳ = GC.composeᴳ ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
         (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) where

  opaque
    unfolding composeᴳ

    compose-raw≈ᴳ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                      (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ))
                    S.≈ᴹ composeᴳ g f
    compose-raw≈ᴳ = ℳ.Equiv.sym (GC.composeᴳ-raw ℳ.U ℳ.monoidal (Tracedₚ 0ℓ))

    compose≈∘ᴳ : composeᴳ g f S.≈ᴹ 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
    compose≈∘ᴳ = S.reflᴹ

    compose-raw≈∘ᴳ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                       (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ))
                     S.≈ᴹ 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
    compose-raw≈∘ᴳ = compose-raw≈ᴳ S.○ᴹ compose≈∘ᴳ

  Sᴳ : MC.State
  Sᴳ = MC.state g MC.⊛ MC.state f

  kᴳ : MC.obj Sᴳ × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺))
     → Dₚ (MC.obj Sᴳ × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)))
  kᴳ ((sg , sf) , inj₁ (inj₁ a)) =
    MC.step f (sf , inj₁ a) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r))
  kᴳ ((sg , sf) , inj₁ (inj₂ c)) =
    MC.step g (sg , inj₂ c) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r))
  kᴳ ((sg , sf) , inj₂ (inj₁ b)) =
    MC.step f (sf , inj₂ b) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r))
  kᴳ ((sg , sf) , inj₂ (inj₂ b)) =
    MC.step g (sg , inj₁ b) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r))

  private
    â : (B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺) → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
    â = αᶠ

    ĉ : (A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺) → (B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)
    ĉ = γᶠ

    tw : MC.obj Sᴳ × ((B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)) → Dₚ (MC.obj Sᴳ × ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺)))
    tw = MC.step (g T.⊗ᵉ f)

    mid : MC.Machine ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)) ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺))
    mid = MC.mk Sᴳ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))

    -- The outer factor is activated, on a query from `C` or on an answer from
    -- the inner one; either way its emission is routed by `outᵍ`.
    onLcase : (sg : MC.St g) (sf : MC.St f) (y : B⁺ ⊎ C⁻)
            → (tw ((sg , sf) , inj₁ y) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step g (sg , y) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r)))
    onLcase sg sf y =
      bindˣ ( tstep-inj₁ (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) y
            ⟨≈⟩ bindˣ (onL-pt (MC.step g) sg sf y)
            ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , sf) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sg′ , inj₁ b) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₁ b)) _
                           ⟨≈⟩ pureᴵ â ((sg′ , sf) , inj₁ (inj₁ b))
            (sg′ , inj₂ c) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₂ c)) _
                           ⟨≈⟩ pureᴵ â ((sg′ , sf) , inj₁ (inj₂ c)))

    onRcase : (sg : MC.St g) (sf : MC.St f) (z : A⁺ ⊎ B⁻)
            → (tw ((sg , sf) , inj₂ z) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step f (sf , z) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r)))
    onRcase sg sf z =
      bindˣ ( tstep-inj₂ (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) z
            ⟨≈⟩ bindˣ (onR-pt (MC.step f) sg sf z)
            ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((sg , proj₁ r) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sf′ , inj₁ a) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₁ a)) _
                           ⟨≈⟩ pureᴵ â ((sg , sf′) , inj₂ (inj₁ a))
            (sf′ , inj₂ b) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₂ b)) _
                           ⟨≈⟩ pureᴵ â ((sg , sf′) , inj₂ (inj₂ b)))

    stepEq : (z : MC.obj Sᴳ × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)))
           → ((V.id V.⊗₁ K.pureᵏ â) V.∘ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))) z ≈ₚ kᴳ z
    stepEq ((sg , sf) , inj₁ (inj₁ a)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₁ (inj₁ a)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₁ a)) tw)
      ⟨≈⟩ onRcase sg sf (inj₁ a)
    stepEq ((sg , sf) , inj₁ (inj₂ c)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₁ (inj₂ c)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₂ c)) tw)
      ⟨≈⟩ onLcase sg sf (inj₂ c)
    stepEq ((sg , sf) , inj₂ (inj₁ b)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₂ (inj₁ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₂ b)) tw)
      ⟨≈⟩ onRcase sg sf (inj₂ b)
    stepEq ((sg , sf) , inj₂ (inj₂ b)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₂ (inj₂ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₁ b)) tw)
      ⟨≈⟩ onLcase sg sf (inj₁ b)

    inner : ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}) S.≈ᴹ mid
    inner = Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (γ-pure A⁺ C⁻ B⁻ B⁺)
       S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ ĉ) (g T.⊗ᵉ f))

  -- The body of `𝒢ₚ`'s composite, both legs absorbed.
  outer : (W.α {A⁻} {B⁺} {B⁻} {C⁺} MC.∘ᴹ
            ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}))
          S.≈ᴹ MC.mk Sᴳ kᴳ
  outer = Cat.∘ᴹ-resp-≈ᴹ (α-pure B⁻ C⁺ A⁻ B⁺) inner
     S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ â) mid)
     S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong stepEq)

  -- `𝒢ₚ`'s composite, up to the record projection (see the header).
  collapseᵀ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                (W.α {A⁻} {B⁺} {B⁻} {C⁺} MC.∘ᴹ
                  ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}))
              S.≈ᴹ MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk Sᴳ kᴳ)
  collapseᵀ = TC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺} outer

------------------------------------------------------------------------
-- A traced machine's step at a point

-- One pass of the loop, then the loop: stated at an arbitrary state and
-- pre-trace step, which is how both a closed composite's tick
-- (`UC.Seam.Plug.Tick`) and `Protocol.Machine.Compose` read `kᴳ`'s trace.
module Loop (A B X : Set) (S : MC.State)
            (k : MC.obj S × (A ⊎ X) → Dₚ (MC.obj S × (B ⊎ X)))
            where

  tracedᴹ : MC.Machine A B
  tracedᴹ = MT.traceᴹ A B X (MC.mk S k)

  body : Body (MC.obj S) X B
  body p = k (proj₁ p , inj₂ (proj₂ p))

  private
    solveᵗ : MC.obj S × (B ⊎ X) → Dₚ (MC.obj S × B)
    solveᵗ = MT.solve S A B X k

    bodyᵗ : Body (MC.obj S) X B
    bodyᵗ = MT.loopBody S A B X k

    -- The junctions the Kleisli tensor spends on a pure relabelling.
    loop-red : (p : MC.obj S × X) → bodyᵗ p ≈ₚ body p
    loop-red (st , x) = bindˣ (>>=ₚ-identityˡ st _)
                  ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₂ x) _)
                  ⟨≈⟩ >>=ₚ-identityˡ (st , inj₂ x) k

    -- The distributor's case split IS the loop's continuation.
    solve-red : (r : MC.obj S × (B ⊎ X)) → solveᵗ r ≈ₚ contᵢ bodyᵗ r
    solve-red (st , inj₁ o) = >>=ₚ-identityˡ (inj₁ (st , o)) _
    solve-red (st , inj₂ x) = >>=ₚ-identityˡ (inj₂ (st , x)) _

  solve-cont : (r : MC.obj S × (B ⊎ X)) → solveᵗ r ≈ₚ contᵢ body r
  solve-cont (st , inj₁ o) = solve-red (st , inj₁ o)
  solve-cont (st , inj₂ x) =
    solve-red (st , inj₂ x) ⟨≈⟩ iterₚ-cong bodyᵗ body loop-red (st , x)

  step-red : (st : MC.obj S) (y : A)
           → MC.step tracedᴹ (st , y) ≈ₚ (k (st , inj₁ y) >>=ₚ contᵢ body)
  step-red st y = bindˣ (bindˣ (>>=ₚ-identityˡ st _)
                    ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₁ y) _)
                    ⟨≈⟩ >>=ₚ-identityˡ (st , inj₁ y) k)
            ⟨≈⟩ bindᶠ solve-cont

  loop-fix : (st : MC.obj S) (x : X)
           → iterₚ body (st , x) ≈ₚ (k (st , inj₂ x) >>=ₚ contᵢ body)
  loop-fix st x = iterₚ-fix body (st , x)

  loop-pass : (st : MC.obj S) (x : X) (st′ : MC.obj S) (o : B ⊎ X)
            → k (st , inj₂ x) ≈ₚ returnₚ (st′ , o)
            → iterₚ body (st , x) ≈ₚ contᵢ body (st′ , o)
  loop-pass st x st′ o eq =
    loop-fix st x ⟨≈⟩ bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (st′ , o) (contᵢ body)

  loop-bot : (st : MC.obj S) (x : X) → k (st , inj₂ x) ≈ₚ botₚ → iterₚ body (st , x) ≈ₚ botₚ
  loop-bot st x eq = loop-fix st x ⟨≈⟩ bindˣ eq ⟨≈⟩ bot-bind-≈ₚ (contᵢ body)

{-# OPTIONS --safe --without-K --guardedness #-}

-- The `Kl(Dₚ)` point-level calculus machine steps are read with: simulations
-- along a function (`simFn`) and back (`fnStep`, at a simulation `step-sim`), and
-- the paired point and the state actions evaluated at a point.


open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure

module CategoricalCrypto.Machines.Pointwise where

open import Categories.Category.Monoidal.Symmetric.Properties.Ext V.symmetric

private
  variable P Q X Y Z : Set

-- A state map applied to the state factor: the shape every `_≲_`'s `θ ⊗₁ id`
-- takes at a point, the state-side mirror of `Machines.Pure.pureᴵ`.
padϕ : (X → Y) → X × Z → Dₚ (Y × Z)
padϕ ϕ p = returnₚ (ϕ (proj₁ p) , proj₂ p)

⊗-pureˡ : (h : X → Y) (p : X × Z) → (K.pureᵏ h V.⊗₁ V.id) p ≈ₚ padϕ h p
⊗-pureˡ h = K.pureᵏ-⊗ h id

------------------------------------------------------------------------
-- Simulations along a function

-- A simulation along a function: a consumer supplies only the two pointwise laws.
simFn : {S T : MC.State} {k : MC.obj S × X → Dₚ (MC.obj S × Y)}
        {k′ : MC.obj T × X → Dₚ (MC.obj T × Y)} (h : MC.obj S → MC.obj T)
      → ((x : V.unit) → (MC.point S x >>=ₚ λ s → returnₚ (h s)) ≈ₚ MC.point T x)
      → ((p : MC.obj S × X) → (k p >>=ₚ padϕ h) ≈ₚ k′ (h (proj₁ p) , proj₂ p))
      → MC.mk S k MS.≲ MC.mk T k′
simFn {k′ = k′} h hp hs = MS.sim (K.pureᵏ h) (KP.structural h) hp λ p →
  bindᶠ (⊗-pureˡ h) ⟨≈⟩ hs p
  ⟨≈⟩ ≈sym (bindˣ (⊗-pureˡ h p) ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p) , proj₂ p) k′)

-- The converse: a step law along a pure state map, read at a point.
fnStep : {k : P × X → Dₚ (P × Y)} {k′ : Q × X → Dₚ (Q × Y)} {θ : P → Dₚ Q} (θp : KP.IsPure θ)
       → V._≈_ (V._∘_ (θ V.⊗₁ V.id) k) (V._∘_ k′ (θ V.⊗₁ V.id))
       → (p : P × X) → (k p >>=ₚ padϕ (KP.fn θp)) ≈ₚ k′ (KP.fn θp (proj₁ p) , proj₂ p)
fnStep {P = P} {k′ = k′} {θ = θ} θp step p =
  bindᶠ (λ q → ≈sym (pad-fn q)) ⟨≈⟩ step p ⟨≈⟩ bindˣ (pad-fn p) ⟨≈⟩ >>=ₚ-identityˡ _ k′
  where
  pad-fn : {Z : Set} (q : P × Z) → (θ V.⊗₁ V.id) q ≈ₚ padϕ (KP.fn θp) q
  pad-fn (s , z) = bindˣ (KP.is-fn θp s) ⟨≈⟩ >>=ₚ-identityˡ (KP.fn θp s) _ ⟨≈⟩ >>=ₚ-identityˡ z _

-- …and what a simulation supplies, read at a point.
module _ {X Y : Set} {f g : MC.Machine X Y} (sim : f MS.≲ g) where

  ϕ : MC.St f → MC.St g
  ϕ = KP.fn (MS.θ-pure sim)

  step-sim : (p : MC.St f × X)
           → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
  step-sim = fnStep (MS.θ-pure sim) (MS.θ-step sim)

  point-sim : mapₚ ϕ (MC.point (MC.state f) ttᵛ) ≈ₚ MC.point (MC.state g) ttᵛ
  point-sim = bindᶠ (λ s → ≈sym (KP.is-fn (MS.θ-pure sim) s)) ⟨≈⟩ MS.θ-point sim ttᵛ

------------------------------------------------------------------------
-- The paired point and the state actions, at a point

point-⊛ : (S T : MC.State) (x : V.unit)
        → MC.point (S MC.⊛ T) x
        ≈ₚ (MC.point S ttᵛ >>=ₚ λ a → MC.point T x >>=ₚ λ b → returnₚ (a , b))
point-⊛ S T x = >>=ₚ-identityˡ (ttᵛ , x) _

β-pt : (p : P) (q : Q) (x : X) → β ((p , q) , x) ≈ₚ returnₚ ((p , x) , q)
β-pt p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ pureᴵ swap (p , q , x))
  ⟨≈⟩ >>=ₚ-identityˡ (p , x , q) _

onL-pt : (k : P × X → Dₚ (P × Y)) (p : P) (q : Q) (x : X)
       → MC.onL k ((p , q) , x)
       ≈ₚ (k (p , x) >>=ₚ λ r → returnₚ ((proj₁ r , q) , proj₂ r))
onL-pt k p q x =
  bindˣ (bindˣ (β-pt p q x) ⟨≈⟩ >>=ₚ-identityˡ ((p , x) , q) _
         ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ q _))
  ⟨≈⟩ >>=ₚ-assoc (k (p , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (p′ , y) → >>=ₚ-identityˡ ((p′ , y) , q) _ ⟨≈⟩ β-pt p′ y q)

onR-pt : (k : Q × X → Dₚ (Q × Y)) (p : P) (q : Q) (x : X)
       → MC.onR k ((p , q) , x)
       ≈ₚ (k (q , x) >>=ₚ λ r → returnₚ ((p , proj₁ r) , proj₂ r))
onR-pt k p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ >>=ₚ-identityˡ p _)
  ⟨≈⟩ >>=ₚ-assoc (k (q , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (q′ , y) → >>=ₚ-identityˡ (p , q′ , y) _)

------------------------------------------------------------------------
-- A traced machine's step at a point

-- One pass of the loop, then the loop: stated at an arbitrary state and
-- pre-trace step, which is how both a closed composite's tick
-- (`UC.Machine.Plug.Tick`) and `Protocol.Machine.Compose` read `kᴳ`'s trace.
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

  loop-pass : (st : MC.obj S) (x : X) (st′ : MC.obj S) (o : B ⊎ X)
            → k (st , inj₂ x) ≈ₚ returnₚ (st′ , o)
            → iterₚ body (st , x) ≈ₚ contᵢ body (st′ , o)
  loop-pass st x st′ o eq =
    iterₚ-fix body (st , x) ⟨≈⟩ bindˣ eq ⟨≈⟩ >>=ₚ-identityˡ (st′ , o) (contᵢ body)

  loop-bot : (st : MC.obj S) (x : X) → k (st , inj₂ x) ≈ₚ botₚ → iterₚ body (st , x) ≈ₚ botₚ
  loop-bot st x eq = iterₚ-fix body (st , x) ⟨≈⟩ bindˣ eq ⟨≈⟩ bot-bind-≈ₚ (contᵢ body)

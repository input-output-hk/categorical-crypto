{-# OPTIONS --safe --without-K --guardedness #-}

-- The G construction's compact-closed unit at an interface, `cupᴵ A : I → A* ⊗ A`
-- (jsv1996's Int construction): a process `f : A → B` with its domain bent
-- round onto the ancilla `A*` is a closed process at `A* ⊗ B` whose runs are
-- `f`'s own, letter for letter.  That is what lets an ancilla context ask a
-- process anything a strategy at its own alphabet can
-- (`UC.RandomSystems.FullAbstraction`).

open import Categories.Category

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (padϕ; point-⊛; simFn)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Cup where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

dualᴵ : Iface → Iface
dualᴵ A = Neg A ⇿ Pos A

cupᴵ : (A : Iface) → Proc unitᴵ (dualᴵ A ⊗ᴵ A)
cupᴵ A = MC.mk MC.Iˢ cupStep
  where
  cupStep : ⊤ᵛ × (⊥ ⊎ (Pos A ⊎ Neg A)) → Dₚ (⊤ᵛ × (⊥ ⊎ (Neg A ⊎ Pos A)))
  cupStep (_ , inj₁ ())
  cupStep (s , inj₂ (inj₁ a)) = returnₚ (s , inj₂ (inj₂ a))
  cupStep (s , inj₂ (inj₂ a)) = returnₚ (s , inj₂ (inj₁ a))

bendᴹ : {A B : Iface} → Proc A B → Proc unitᴵ (dualᴵ A ⊗ᴵ B)
bendᴹ {A} {B} f = MC.mk (MC.state f) bendStep
  where
  bendStep : MC.St f × (⊥ ⊎ (Pos A ⊎ Neg B)) → Dₚ (MC.St f × (⊥ ⊎ (Neg A ⊎ Pos B)))
  bendStep (_ , inj₁ ())
  bendStep (s , inj₂ z) = MC.step f (s , z) >>=ₚ λ r → returnₚ (proj₁ r , inj₂ (proj₂ r))

module _ {A B : Iface} (f : Proc A B) where

  bend-run : (d : Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)) → runᴹ (bendᴹ f) d ≈ₚ runˢ f d
  bend-run d = bindᶠ λ s → from s d
    where
    from : (s : MC.St f) (d : Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
         → runᴹFrom (bendᴹ f) s d ≈ₚ runFromˢ f s d
    from s (out b)    = ≈refl
    from s (coin μ k) = bindᶠ λ b → from s (k b)
    from s (ask z k)  = >>=ₚ-assoc (MC.step f (s , z)) _ _
                    ⟨≈⟩ bindᶠ λ r → >>=ₚ-identityˡ (proj₁ r , inj₂ (proj₂ r)) _ ⟨≈⟩ from (proj₁ r) (k (proj₂ r))

  private
    g : Proc (dualᴵ A ⊗ᴵ A) (dualᴵ A ⊗ᴵ B)
    g = T₁ᴵ (dualᴵ A) f

    S₀ : MC.State
    S₀ = Col.Sᴳ g (cupᴵ A)

  open Col.Loop (⊥ ⊎ (Pos A ⊎ Neg B)) (⊥ ⊎ (Neg A ⊎ Pos B)) ((Pos A ⊎ Neg A) ⊎ (Neg A ⊎ Pos A)) S₀
                (Col.kᴳ g (cupᴵ A))

  private
    -- An answer of `f` on `B` leaves at once; one on `A` goes round the cup and
    -- leaves on the ancilla.
    out-f : (sc : ⊤ᵛ) (r : MC.St f × (Neg A ⊎ Pos B))
          → (contᵢ body ((proj₁ r , sc) , Col.outᵍ (outT (proj₂ r))) >>=ₚ padϕ proj₁)
            ≈ₚ returnₚ (proj₁ r , inj₂ (proj₂ r))
    out-f sc (s , inj₂ b) = >>=ₚ-identityˡ ((s , sc) , inj₂ (inj₂ b)) (padϕ proj₁)
    out-f sc (s , inj₁ a) =
        bindˣ ( loop-pass (s , sc) (inj₁ (inj₂ a)) (s , sc) (inj₂ (inj₂ (inj₁ a)))
                          (>>=ₚ-identityˡ (sc , inj₂ (inj₁ a)) _)
              ⟨≈⟩ loop-pass (s , sc) (inj₂ (inj₁ a)) (s , sc) (inj₁ (inj₂ (inj₁ a)))
                            (>>=ₚ-identityˡ (s , inj₂ (inj₁ a)) _))
      ⟨≈⟩ >>=ₚ-identityˡ ((s , sc) , inj₂ (inj₁ a)) (padϕ proj₁)

    through : (s : MC.St f) (sc : ⊤ᵛ) (z : Pos A ⊎ Neg B)
            → (((mapₚ (map₂ outT) (MC.step f (s , z))
                   >>=ₚ λ r → returnₚ ((proj₁ r , sc) , Col.outᵍ (proj₂ r)))
                  >>=ₚ contᵢ body) >>=ₚ padϕ proj₁)
              ≈ₚ (MC.step f (s , z) >>=ₚ λ r → returnₚ (proj₁ r , inj₂ (proj₂ r)))
    through s sc z =
        >>=ₚ-assoc (mapₚ (map₂ outT) (MC.step f (s , z)) >>=ₚ _) (contᵢ body) (padϕ proj₁)
      ⟨≈⟩ >>=ₚ-assoc (mapₚ (map₂ outT) (MC.step f (s , z))) _ _
      ⟨≈⟩ bind-map (MC.step f (s , z)) (map₂ outT) _
      ⟨≈⟩ bindᶠ λ r → >>=ₚ-identityˡ ((proj₁ r , sc) , Col.outᵍ (outT (proj₂ r))) _ ⟨≈⟩ out-f sc r

    step-law : (p : MC.obj S₀ × (⊥ ⊎ (Pos A ⊎ Neg B)))
             → (MC.step tracedᴹ p >>=ₚ padϕ proj₁) ≈ₚ MC.step (bendᴹ f) (proj₁ (proj₁ p) , proj₂ p)
    step-law ((s , sc) , inj₂ (inj₁ x)) =
        bindˣ ( step-red (s , sc) (inj₂ (inj₁ x))
              ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (s , inj₁ (inj₁ x)) _)
              ⟨≈⟩ >>=ₚ-identityˡ ((s , sc) , inj₂ (inj₁ (inj₁ x))) (contᵢ body)
              ⟨≈⟩ loop-pass (s , sc) (inj₁ (inj₁ x)) (s , sc) (inj₂ (inj₂ (inj₂ x)))
                            (>>=ₚ-identityˡ (sc , inj₂ (inj₂ x)) _)
              ⟨≈⟩ loop-fix (s , sc) (inj₂ (inj₂ x)))
      ⟨≈⟩ through s sc (inj₁ x)
    step-law ((s , sc) , inj₂ (inj₂ b)) =
      bindˣ (step-red (s , sc) (inj₂ (inj₂ b))) ⟨≈⟩ through s sc (inj₂ b)

    point-law : (x : ⊤ᵛ) → (MC.point S₀ x >>=ₚ λ p → returnₚ (proj₁ p)) ≈ₚ MC.point (MC.state f) x
    point-law x =
        bindˣ (point-⊛ (MC.state f) MC.Iˢ x)
      ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state f) tt) _ _
      ⟨≈⟩ bindᶠ (λ s → >>=ₚ-assoc (returnₚ x) _ _ ⟨≈⟩ >>=ₚ-identityˡ x _ ⟨≈⟩ >>=ₚ-identityˡ (s , x) _)
      ⟨≈⟩ >>=ₚ-identityʳ (MC.point (MC.state f) tt)

  cup-≈ : 𝒫._≈_ {unitᴵ} {dualᴵ A ⊗ᴵ B}
            (𝒫._∘_ {unitᴵ} {dualᴵ A ⊗ᴵ A} {dualᴵ A ⊗ᴵ B} (T₁ᴵ (dualᴵ A) f) (cupᴵ A)) (bendᴹ f)
  cup-≈ = S.⟺ᴹ (Col.compose-raw≈∘ᴳ g (cupᴵ A)) S.○ᴹ Col.collapseᵀ g (cupᴵ A)
     S.○ᴹ S.≲⇒≈ᴹ (simFn proj₁ point-law step-law)

  cup-run : (d : Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
          → runᴹ (𝒫._∘_ {unitᴵ} {dualᴵ A ⊗ᴵ A} {dualᴵ A ⊗ᴵ B} (T₁ᴵ (dualᴵ A) f) (cupᴵ A)) d ≈ₚ runˢ f d
  cup-run d = runᴹ-resp-≈ᴹ cup-≈ d ⟨≈⟩ bend-run d

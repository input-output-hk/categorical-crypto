{-# OPTIONS --safe --without-K --guardedness #-}

-- What an embedded strategy costs: `UC.Seam.strategyEnv B d` carries the query
-- bound `d`'s own ask-depth gives it.
--
-- `Certified` is not invariant under the machine equality, and the environment's
-- own state is the bare `EnvSt` — a `susp` records nothing of how much of the
-- tree is left, so no potential can be read off it.  `QB` is the `≈`-closure, so
-- the certificate is exhibited on a REFINED machine whose suspended state
-- carries the remaining ask-depth, and the forgetful state map is the
-- simulation.
--
-- The potential IS that remaining depth: the tick deposits `c`, each query
-- withdraws one, and `asks≤` is exactly the invariant keeping the account
-- solvent.  Coins are free on both sides — they are internal to one `playˢ`
-- pass — so the induction is the one `asks≤` itself recurses on.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (Dₚ-DiscreteMonad; 𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.QueryBound using (Ans; Certified; QB; forget)
open import CategoricalCrypto.UC.Seam

import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Seam.Budget where

private
  module K = KD (Dₚ-DiscreteMonad {0ℓ})
  module MC = Core (𝒱ₚ 0ℓ)
  module P = KDP (Dₚ-DiscreteMonad {0ℓ})
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

  variable X Y : Set

  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ X} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  bindˣ : {d e : Dₚ X} {g : X → Dₚ Y} → d ≈ₚ e → (d >>=ₚ g) ≈ₚ (e >>=ₚ g)
  bindˣ {d = d} {e} {g} p = >>=ₚ-cong d e g g p λ _ → ≈ₚ-refl _

  bindᶠ : {d : Dₚ X} {g l : X → Dₚ Y} → ((x : X) → g x ≈ₚ l x)
        → (d >>=ₚ g) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {g} {l} p = >>=ₚ-cong d d g l (≈ₚ-refl d) p

module _ (B : Iface) (c : ℕ) where

  -- The environment's state refined by the ask-depth still available to it.
  data CSt : Set where
    playᶜ : (e : Strat (Neg B) (Pos B)) → asks≤ c e → CSt
    suspᶜ : (n : ℕ) (k : Pos B → Strat (Neg B) (Pos B))
          → ((r : Pos B) → asks≤ n (k r)) → CSt

  Φᶜ : CSt → ℕ
  Φᶜ (playᶜ _ _)   = 0
  Φᶜ (suspᶜ n _ _) = n

  -- `playˢ` with the refined answer the certificate owes: a query strictly
  -- spends potential, a verdict leaves the account where an exhausted tree does.
  playᴬ : (r : ℕ) (e : Strat (Neg B) (Pos B)) → asks≤ r e
        → Dₚ (Ans Φᶜ (Neg B) Bool r)
  playᴬ _       (out b)    _ = returnₚ (inj₂ ((playᶜ (out b) tt , z≤n) , b))
  playᴬ zero    (ask _ _)  h = ⊥-elim h
  playᴬ (suc n) (ask q k)  h = returnₚ (inj₁ ((suspᶜ n k h , ≤-refl) , q))
  playᴬ r       (coin μ k) h = coinₚ μ >>=ₚ λ b → playᴬ r (k b) (h b)

  stepᶜ : CSt × (Pos B ⊎ ⊤) → Dₚ (CSt × (Neg B ⊎ Bool))
  stepᶜ (playᶜ e h   , inj₂ _) = mapₚ forget (playᴬ c e h)
  stepᶜ (suspᶜ n k h , inj₁ p) = mapₚ forget (playᴬ n (k p) (h p))
  stepᶜ (playᶜ _ _   , inj₁ _) = botₚ
  stepᶜ (suspᶜ _ _ _ , inj₂ _) = botₚ

  stateᶜ : (d : Strat (Neg B) (Pos B)) → asks≤ c d → MC.State
  stateᶜ d h = record
    { obj = CSt ; point = λ _ → returnₚ (playᶜ d h) ; discard = λ _ → returnₚ ttᵛ }

  envᶜ : (d : Strat (Neg B) (Pos B)) → asks≤ c d → Proc B Ωᴵ
  envᶜ d h = MC.mk (stateᶜ d h) stepᶜ

  certᶜ : (d : Strat (Neg B) (Pos B)) (h : asks≤ c d) → Certified c (envᶜ d h)
  certᶜ d h = record
    { Φ      = Φᶜ
    ; pointᵍ = returnₚ (playᶜ d h , z≤n)
    ; coh₀   = >>=ₚ-identityˡ (playᶜ d h , z≤n) (returnₚ ∘′ proj₁)
    ; onLᵍ   = onL ; onRᵍ = onR ; cohL = cohL ; cohR = cohR
    }
    where
    onL : (s : CSt) (p : Pos B) → Dₚ (Ans Φᶜ (Neg B) Bool (Φᶜ s))
    onL (playᶜ _ _)    _ = botₚ
    onL (suspᶜ _ k hk) p = playᴬ _ (k p) (hk p)

    onR : (s : CSt) (t : ⊤) → Dₚ (Ans Φᶜ (Neg B) Bool (Φᶜ s + c))
    onR (playᶜ e he)  _ = playᴬ c e he
    onR (suspᶜ _ _ _) _ = botₚ

    cohL : (s : CSt) (p : Pos B) → mapₚ forget (onL s p) ≈ₚ stepᶜ (s , inj₁ p)
    cohL (playᶜ _ _)   _ = bot-bind-≈ₚ _
    cohL (suspᶜ _ _ _) _ = ≈ₚ-refl _

    cohR : (s : CSt) (t : ⊤) → mapₚ forget (onR s t) ≈ₚ stepᶜ (s , inj₂ t)
    cohR (playᶜ _ _)   _ = ≈ₚ-refl _
    cohR (suspᶜ _ _ _) _ = bot-bind-≈ₚ _

  ------------------------------------------------------------------------
  -- …and the refinement is invisible

  private
    forgetᶜ : CSt → EnvSt B
    forgetᶜ (playᶜ e _)   = play e
    forgetᶜ (suspᶜ _ k _) = susp k

    fgt : CSt × (Neg B ⊎ Bool) → EnvSt B × (Neg B ⊎ Bool)
    fgt q = forgetᶜ (proj₁ q) , proj₂ q

    -- The two `returnₚ` junctions a refined answer costs.
    fuse : {r : ℕ} (x : Ans Φᶜ (Neg B) Bool r)
         → mapₚ fgt (mapₚ forget (returnₚ x)) ≈ₚ returnₚ (fgt (forget x))
    fuse x = bindˣ (>>=ₚ-identityˡ x (returnₚ ∘′ forget))
           ⟨≈⟩ >>=ₚ-identityˡ (forget x) (returnₚ ∘′ fgt)

    playᴬ-erase : (r : ℕ) (e : Strat (Neg B) (Pos B)) (h : asks≤ r e)
                → mapₚ fgt (mapₚ forget (playᴬ r e h)) ≈ₚ playˢ B e
    playᴬ-erase _       (out _)    _ = fuse _
    playᴬ-erase zero    (ask _ _)  h = ⊥-elim h
    playᴬ-erase (suc _) (ask _ _)  _ = fuse _
    playᴬ-erase r       (coin μ k) h =
        bindˣ (>>=ₚ-assoc (coinₚ μ) _ (returnₚ ∘′ forget))
      ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ (returnₚ ∘′ fgt)
      ⟨≈⟩ bindᶠ (λ b → playᴬ-erase r (k b) (h b))

    θᶜ : CSt → Dₚ (EnvSt B)
    θᶜ = K.pureᵏ forgetᶜ

    pad : (q : CSt × (Neg B ⊎ Bool)) → V._⊗₁_ θᶜ V.id q ≈ₚ returnₚ (fgt q)
    pad = K.pureᵏ-⊗ forgetᶜ (λ o → o)

    padᵈ : (p : CSt × (Pos B ⊎ ⊤))
         → V._⊗₁_ θᶜ V.id p ≈ₚ returnₚ (forgetᶜ (proj₁ p) , proj₂ p)
    padᵈ = K.pureᵏ-⊗ forgetᶜ (λ o → o)

    step-erase : (p : CSt × (Pos B ⊎ ⊤))
               → mapₚ fgt (stepᶜ p) ≈ₚ stepˢ B (forgetᶜ (proj₁ p) , proj₂ p)
    step-erase (playᶜ e h   , inj₂ _) = playᴬ-erase c e h
    step-erase (suspᶜ _ k h , inj₁ p) = playᴬ-erase _ (k p) (h p)
    step-erase (playᶜ _ _   , inj₁ _) = bot-bind-≈ₚ _
    step-erase (suspᶜ _ _ _ , inj₂ _) = bot-bind-≈ₚ _

  simᶜ : (d : Strat (Neg B) (Pos B)) (h : asks≤ c d) → envᶜ d h S.≲ strategyEnv B d
  simᶜ d h = S.sim θᶜ (P.structural forgetᶜ)
                   (λ s → >>=ₚ-identityˡ (forgetᶜ s) _)
                   (λ _ → >>=ₚ-identityˡ (playᶜ d h) θᶜ) square
    where
    square : V._≈_ (V._∘_ (V._⊗₁_ θᶜ V.id) stepᶜ) (V._∘_ (stepˢ B) (V._⊗₁_ θᶜ V.id))
    square p = bindᶠ pad ⟨≈⟩ step-erase p
             ⟨≈⟩ ≈ₚ-sym _ _ (>>=ₚ-identityˡ _ (stepˢ B))
             ⟨≈⟩ ≈ₚ-sym _ _ (bindˣ (padᵈ p))

  -- An environment playing a `c`-ask strategy issues at most `c` queries per
  -- activation from above, which is the bound at the hom.
  qb-strategyEnv : (d : Strat (Neg B) (Pos B)) → asks≤ c d → QB c (strategyEnv B d)
  qb-strategyEnv d h = envᶜ d h , certᶜ d h , S.≲⇒≈ᴹ (simᶜ d h)

{-# OPTIONS --safe --without-K --guardedness #-}

-- What an embedded strategy costs: `UC.Seam.strategyEnv B d` carries the query
-- bound `d`'s own ask-depth gives it.
--
-- The environment's own state is the bare `EnvSt` — a `susp` records nothing
-- of how much of the tree is left, so no potential can be read off it.  The
-- certificate is exhibited on a REFINED machine whose suspended state carries
-- the remaining ask-depth, and the forgetful state map is the simulation
-- `UC.QueryBound.QB`'s `≈`-closure asks for.
--
-- The potential IS that remaining depth: the tick deposits `c`, each query
-- withdraws one, and `asks≤` is exactly the invariant keeping the account
-- solvent.  Coins are free on both sides — they are internal to one `playˢ`
-- pass — so the induction is the one `asks≤` itself recurses on.
--
-- `stratTest` is the same strategy embedded as a test, and inherits the bound.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Laws
open import CategoricalCrypto.UC.Seam

module CategoricalCrypto.UC.Seam.Budget where

private
  module 𝒫 = Category 𝒫ᴵ

module _ (B : Iface) (c : ℕ) where

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

  envᶜ : (d : Strat (Neg B) (Pos B)) → asks≤ c d → Proc B Ωᴵ
  envᶜ d h = MC.mk (initˢ CSt (playᶜ d h)) stepᶜ

  certᶜ : (d : Strat (Neg B) (Pos B)) (h : asks≤ c d) → Certified c (envᶜ d h)
  certᶜ d h = record
    { Φ      = Φᶜ
    ; pointᵍ = returnₚ (playᶜ d h , z≤n)
    ; coh₀   = >>=ₚ-identityˡ (playᶜ d h , z≤n) (returnₚ ∘′ proj₁)
    ; onLᵍ   = onL ; onRᵍ = onR
    ; cohL   = λ where (playᶜ _ _)   _ → bot-bind-≈ₚ _
                       (suspᶜ _ _ _) _ → ≈ₚ-refl _
    ; cohR   = λ where (playᶜ _ _)   _ → ≈ₚ-refl _
                       (suspᶜ _ _ _) _ → bot-bind-≈ₚ _
    }
    where
    onL : (s : CSt) (p : Pos B) → Dₚ (Ans Φᶜ (Neg B) Bool (Φᶜ s))
    onL (playᶜ _ _)    _ = botₚ
    onL (suspᶜ _ k hk) p = playᴬ _ (k p) (hk p)

    onR : (s : CSt) (t : ⊤) → Dₚ (Ans Φᶜ (Neg B) Bool (Φᶜ s + c))
    onR (playᶜ e he)  _ = playᴬ c e he
    onR (suspᶜ _ _ _) _ = botₚ

  ------------------------------------------------------------------------
  -- …and the refinement is invisible

  private
    forgetᶜ : CSt → EnvSt B
    forgetᶜ (playᶜ e _)   = play e
    forgetᶜ (suspᶜ _ k _) = susp k

    fuse : {r : ℕ} (x : Ans Φᶜ (Neg B) Bool r)
         → mapₚ (map₁ forgetᶜ) (mapₚ forget (returnₚ x)) ≈ₚ returnₚ (map₁ forgetᶜ (forget x))
    fuse x = bindˣ (>>=ₚ-identityˡ x (returnₚ ∘′ forget))
           ⟨≈⟩ >>=ₚ-identityˡ (forget x) (returnₚ ∘′ map₁ forgetᶜ)

    playᴬ-erase : (r : ℕ) (e : Strat (Neg B) (Pos B)) (h : asks≤ r e)
                → mapₚ (map₁ forgetᶜ) (mapₚ forget (playᴬ r e h)) ≈ₚ playˢ B e
    playᴬ-erase _       (out _)    _ = fuse _
    playᴬ-erase zero    (ask _ _)  h = ⊥-elim h
    playᴬ-erase (suc _) (ask _ _)  _ = fuse _
    playᴬ-erase r       (coin μ k) h =
        bindˣ (>>=ₚ-assoc (coinₚ μ) _ (returnₚ ∘′ forget))
      ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ (returnₚ ∘′ map₁ forgetᶜ)
      ⟨≈⟩ bindᶠ (λ b → playᴬ-erase r (k b) (h b))

    θᶜ : CSt → Dₚ (EnvSt B)
    θᶜ = K.pureᵏ forgetᶜ

    pad : {Z : Set} (q : CSt × Z) → V._⊗₁_ θᶜ V.id q ≈ₚ returnₚ (map₁ forgetᶜ q)
    pad = K.pureᵏ-⊗ forgetᶜ id

    step-erase : (p : CSt × (Pos B ⊎ ⊤))
               → mapₚ (map₁ forgetᶜ) (stepᶜ p) ≈ₚ stepˢ B (forgetᶜ (proj₁ p) , proj₂ p)
    step-erase (playᶜ e h   , inj₂ _) = playᴬ-erase c e h
    step-erase (suspᶜ _ k h , inj₁ p) = playᴬ-erase _ (k p) (h p)
    step-erase (playᶜ _ _   , inj₁ _) = bot-bind-≈ₚ _
    step-erase (suspᶜ _ _ _ , inj₂ _) = bot-bind-≈ₚ _

  simᶜ : (d : Strat (Neg B) (Pos B)) (h : asks≤ c d) → envᶜ d h MS.≲ strategyEnv B d
  simᶜ d h = MS.sim θᶜ (KP.structural forgetᶜ) (λ _ → >>=ₚ-identityˡ (playᶜ d h) θᶜ) λ p →
    bindᶠ pad ⟨≈⟩ step-erase p ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ (stepˢ B)) ⟨≈⟩ ≈sym (bindˣ (pad p))

  qb-strategyEnv : (d : Strat (Neg B) (Pos B)) → asks≤ c d → QB c (strategyEnv B d)
  qb-strategyEnv d h = envᶜ d h , certᶜ d h , MS.≲⇒≈ᴹ (simᶜ d h)

------------------------------------------------------------------------
-- A strategy embedded as a test

-- `strategyEnv` read on the compiler's own domain: the ancilla is
-- trivial, so the empty summand is eliminated.
outᵁ : (B : Iface) → Neg B ⊎ Bool → (Pos unitᴵ ⊎ Neg B) ⊎ Bool
outᵁ B (inj₁ q) = inj₁ (inj₂ q)
outᵁ B (inj₂ v) = inj₂ v

stepᵁ : (B : Iface) → EnvSt B × ((Pos unitᴵ ⊎ Pos B) ⊎ ⊤)
      → Dₚ (EnvSt B × ((Neg unitᴵ ⊎ Neg B) ⊎ Bool))
stepᵁ B (se , inj₁ (inj₁ ()))
stepᵁ B (se , inj₁ (inj₂ p)) = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₁ p))
stepᵁ B (se , inj₂ _)        = mapₚ (λ z → proj₁ z , outᵁ B (proj₂ z)) (stepˢ B (se , inj₂ tt))

stratTest : (B : Iface) → Strat (Neg B) (Pos B) → Proc (unitᴵ ⊗ᴵ B) Ωᴵ
stratTest B d = MC.mk (stateˢ B d) (stepᵁ B)

stratTest-embeds : (B : Iface) (d : Strat (Neg B) (Pos B))
                 → 𝒫._≈_ (stratTest B d) (strategyEnv B d 𝒫.∘ λᴵ⇒)
stratTest-embeds B d =
  MS.⟺ᴹ (∘-wireᴹ [ ⊥-elim , id ] inj₂ (strategyEnv B d) MS.○ᴹ MS.≲⇒≈ᴹ (MS.mk-cong pt))
  where
  pt : (z : _) → _
  pt (se , inj₁ (inj₁ ()))
  pt (se , inj₁ (inj₂ p)) =
    map-eq (stepˢ B (se , inj₁ p)) _ _ λ where (_ , inj₁ _) → refl
                                               (_ , inj₂ _) → refl
  pt (se , inj₂ _) =
    map-eq (stepˢ B (se , inj₂ tt)) _ _ λ where (_ , inj₁ _) → refl
                                                (_ , inj₂ _) → refl

qb-stratTest : (B : Iface) {q : ℕ} (d : Strat (Neg B) (Pos B)) → asks≤ q d
             → QB q (stratTest B d)
qb-stratTest B {q} d a =
  qb-resp-≈ (𝒫.Equiv.sym (stratTest-embeds B d))
    (subst (λ k → QB k (strategyEnv B d 𝒫.∘ λᴵ⇒)) (*-identityʳ q)
      (qb-∘-category (unitᴵ ⊗ᴵ B) B Ωᴵ (strategyEnv B d) λᴵ⇒
        (qb-strategyEnv B q d a) qb-λᴵ⇒))

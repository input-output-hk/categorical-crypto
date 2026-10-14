{-# OPTIONS --safe --without-K #-}

-- Fig. 9 observes Get before that round's quiescence. Saturation consumes
-- strictly decreasing reaction work; blocked reads retain their residuals.
module CategoricalCrypto.IPDL.Native where

open import Class.DecEq
open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.List.Base using ([]; _∷_; _++_; length)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base using (case_of_; _∘_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import CategoricalCrypto.IPDL.Syntax
open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; sample)
open import CategoricalCrypto.SSP.Iface using (Iface)

private variable
  Γ Δ I O : Ctx
  τ : Ty
  X Y : Set

mapCoins : (X → Y) → Coins X → Coins Y
mapCoins f (done x) = done (f x)
mapCoins f (toss μ k) = toss μ λ b → mapCoins f (k b)

bindCoins : Coins X → (X → Coins Y) → Coins Y
bindCoins (done x) f = f x
bindCoins (toss μ k) f = toss μ λ b → bindCoins (k b) f

cellStep : Environment Γ → (c : Cell Γ τ)
         → Maybe (Coins (Σ (Cell Γ τ) (λ d → cost d < cost c)))
cellStep e (assigned v) = nothing
cellStep e (waiting n (ret v)) = just (done (assigned v , s≤s z≤n))
cellStep e (waiting (suc n) (read c k)) = case e c of λ where
  nothing → nothing
  (just v) → just (done (waiting n (k v) , ≤-refl))
cellStep e (waiting (suc n) (coin μ k)) = just (toss μ λ b → done (waiting n (k b) , ≤-refl))

choose : Environment Γ → (s : Cells Γ Δ)
       → Maybe (Coins (Σ (Cells Γ Δ) (λ t → work t < work s)))
choose {Δ = []} e s = nothing
choose {Δ = τ ∷ Δ} e (c , cs) with cellStep e c
... | just κ = just (mapCoins (λ (d , p) → (d , cs) , +-monoˡ-< (work cs) p) κ)
... | nothing with choose e cs
...   | nothing = nothing
...   | just κ = just (mapCoins (λ (ds , p) → (c , ds) , +-monoʳ-< (cost c) p) κ)

module Residual {I O} (N : Net I O) where
  private D = O ++ H N
  private Global = I ++ D

  State : Set
  State = Store I × Cells Global D

  initial : State
  initial = empty I , start (def N)

  env : State → Environment Global
  env (i , cs) = lookup Global (append I D i (values cs))

  Quiet : State → Set
  Quiet s = choose (env s) (proj₂ s) ≡ nothing

  saturate : (n : ℕ) (i : Store I) (cs : Cells Global D) → work cs ≤ n
           → Coins (Σ (Cells Global D) (λ ds → Quiet (i , ds)))
  saturate zero i cs le with choose (env (i , cs)) cs in eq
  ... | nothing = done (cs , eq)
  ... | just κ = bindCoins κ λ (ds , lt) → ⊥-elim (n≮0 (≤-trans lt le))
  saturate (suc n) i cs le with choose (env (i , cs)) cs in eq
  ... | nothing = done (cs , eq)
  ... | just κ = bindCoins κ λ (ds , lt) → saturate n i ds (s≤s⁻¹ (≤-trans lt le))

  quiesce : (s : State) → Coins (Σ State Quiet)
  quiesce (i , cs) = mapCoins (λ (ds , q) → (i , ds) , q) (saturate (work cs) i cs ≤-refl)

Port : Ctx → Ctx → Set
Port I O = Ref I ⊎ (Ref O ⊎ ⊤)

pattern Input i = inj₁ i
pattern Get o = inj₂ (inj₁ o)
pattern Step = inj₂ (inj₂ tt)

Query : (I O : Ctx) → Port I O → Set
Query I O (Input i) = Val (ty I i)
Query I O (Get o) = ⊤
Query I O Step = ⊤

Reply : (I O : Ctx) → Port I O → Set
Reply I O (Input i) = ⊤
Reply I O (Get o) = Maybe (Val (ty O o))
Reply I O Step = ⊤

API : Ctx → Ctx → Iface
API I O = record
  { Ch = Port I O ; Q = Query I O ; R = Reply I O
  ; Ch-dec = DecEq-⊎ ⦃ DecEq-Fin ⦄ ⦃ DecEq-⊎ ⦃ DecEq-Fin ⦄ ⦃ DecEq-⊤ ⦄ ⦄ }

module Interaction {I O} (N : Net I O) where
  open Residual N

  before : State → (c : Port I O) → Query I O c → State × Reply I O c
  before (i , cs) (Input c) v = (assign I i c v , cs) , tt
  before s@(_ , cs) (Get c) _ = s , lookup O (take O (H N) (values cs)) c
  before s Step _ = s , tt

  round : State → (c : Port I O) → Query I O c → Coins (Σ State Quiet × Reply I O c)
  round s c q = mapCoins (λ t → t , proj₂ b) (quiesce (proj₁ b))
    where b = before s c q

  turn : State → (c : Port I O) → Query I O c → Coins (State × Reply I O c)
  turn s c q = mapCoins (λ (t , r) → proj₁ t , r) (round s c q)

data Strategy (I O : Ctx) (X : Set) : Set where
  finish : X → Strategy I O X
  ask : (c : Port I O) → Query I O c → (Reply I O c → Strategy I O X) → Strategy I O X
  random : Dist-ℚ Bool → (Bool → Strategy I O X) → Strategy I O X

module Experiment {I O} (N : Net I O) where
  open Residual N
  open Interaction N

  runWith : (X → Dist-ℚ Y) → Strategy I O X → State → Dist-ℚ Y
  runWith f (finish x) s = f x
  runWith f (ask c q k) s = sample (turn s c q) >>=ᴹ λ (s′ , r) → runWith f (k r) s′
  runWith f (random μ k) s = μ >>=ᴹ λ b → runWith f (k b) s

  run : Strategy I O X → Dist-ℚ X
  run a = runWith return-ℚ a initial

-- The four JSV traced-monoidal laws (vanishing₁, vanishing₂,
-- superposing, yanking) are fully derived from the `IterativeMonad`
-- axiomatisation, as are the trace-naturality laws (trace-∘ˡ-ᵉ,
-- trace-∘ʳ-ᵉ) and the Fubini exchange of nested traces (trace-comm-ᵉ)
-- at the end of this file. Axioms used: iter-fix, iter-cong, iter-nat,
-- iter-strengthen, iter-codiag, iter-codiag-y, iter-conjugate,
-- iter-vanishing-2, iter-vanishing-2-x.
{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Traced symmetric monoidal structure on `SFunᵉ-Category` with the
-- coproduct tensor (⊎, ⊥).
--
-- This file extends `SFunM/Monoidal` (which gives the Monoidal record)
-- with a Symmetric structure (braiding σᵉ + hexagons) and a Traced
-- structure built from an iteration operator on the underlying monad.
--
-- The trace operator
--
--   tr : SFunᵉ (A ⊎ X) (B ⊎ X) → SFunᵉ A B
--
-- feeds the X-side of the output back as the X-side of the next input,
-- iterating until the function emits on the A-side. This requires the
-- monad `M` to support iteration (`IterativeMonad`). See
-- `Class.Monad.Iterative`.

open import categorical-crypto.Prelude hiding (Bifunctor)
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Symmetric as Sym
import Categories.Category.Monoidal.Braided as Br
open import Categories.Category.Monoidal.Traced
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Data.List.Properties using (map-∘; map-id; map-cong)

open import Class.Core
open import Class.Monad.Ext
open import Class.Monad.Iterative

module CategoricalCrypto.SFunM.Traced {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ F-Laws        : FunctorLaws M      ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄
  ⦃ M-Comm        : CommutativeMonad M ⦄
  ⦃ M-Iter        : IterativeMonad M   ⦄
  where

open import CategoricalCrypto.SFunM
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄

open import CategoricalCrypto.SFunM.Monoidal
  ⦃ Monad-M ⦄ ⦃ F-Laws ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ ⦃ M-Comm ⦄

open Sym SFunᵉ-monoidal using (Symmetric; symmetricHelper)
open Br  SFunᵉ-monoidal using (Braided)

private variable A B C D E S X Y : Type

------------------------------------------------------------------------
-- List-level lemmas about how filter₁/filter₂/weave interact with
-- swapping the tag (σ-fn).

filter₁-σ : ∀ {A C} (xs : List (A ⊎ C))
  → filter₁ (map σ-fn xs) ≡ filter₂ xs
filter₁-σ []             = refl
filter₁-σ (inj₁ a ∷ xs)  = filter₁-σ xs
filter₁-σ (inj₂ c ∷ xs)  = cong (c ∷_) (filter₁-σ xs)

filter₂-σ : ∀ {A C} (xs : List (A ⊎ C))
  → filter₂ (map σ-fn xs) ≡ filter₁ xs
filter₂-σ []             = refl
filter₂-σ (inj₁ a ∷ xs)  = cong (a ∷_) (filter₂-σ xs)
filter₂-σ (inj₂ c ∷ xs)  = filter₂-σ xs

weave-σ : ∀ {A B C D} (xs : List (A ⊎ C))
  (bs : List B) (ds : List D)
  → weave (map σ-fn xs) bs ds ≡ map σ-fn (weave xs ds bs)
weave-σ []              _        _        = refl
weave-σ (inj₁ a ∷ xs)   bs       []       = refl
weave-σ (inj₁ a ∷ xs)   bs       (d ∷ ds) = cong (inj₂ d ∷_) (weave-σ xs bs ds)
weave-σ (inj₂ c ∷ xs)   []       ds       = refl
weave-σ (inj₂ c ∷ xs)   (b ∷ bs) ds       = cong (inj₁ b ∷_) (weave-σ xs bs ds)

------------------------------------------------------------------------
-- σ naturality.
--
-- σᵉ ∘ᵉ (f ⊗ᵉ g) ≈ᵉ (g ⊗ᵉ f) ∘ᵉ σᵉ
--
-- Both sides reduce, via trace-⊗ᵉ and pure-reshape-correct, to a
-- canonical form that runs f on the A-positions and g on the C-positions
-- of `xs`, then assembles the output with swapped tags.  Their order of
-- binding f and g differs, and we swap it using `>>=-comm-y`.

private
  σᵉ-natural-LHS : ∀ {A B C D} (f : SFunᵉ A B) (g : SFunᵉ C D)
    (xs : List (A ⊎ C))
    → eval (σᵉ ∘ᵉ (f ⊗ᵉ g)) xs
      ≡ (eval f (filter₁ xs) >>= λ bs →
         eval g (filter₂ xs) >>= λ ds →
           return (map σ-fn (weave xs bs ds)))
  σᵉ-natural-LHS f g xs = begin
    eval (σᵉ ∘ᵉ (f ⊗ᵉ g)) xs
      ≡⟨ sym (trace-∘ {sg = tt} {sf = SFunᵉ.init (f ⊗ᵉ g)}
                       {g = SFunᵉ.fun σᵉ} {f = SFunᵉ.fun (f ⊗ᵉ g)} xs) ⟩
    ((eval (f ⊗ᵉ g) xs >>= λ ys → return (eval σᵉ ys)) >>= λ x → x)
      ≡⟨ >>=-assoc (eval (f ⊗ᵉ g) xs) ⟩
    (eval (f ⊗ᵉ g) xs >>= λ ys → return (eval σᵉ ys) >>= λ x → x)
      ≡⟨ refl⟩>>=⟨ (λ ys → >>=-identityˡ) ⟩
    (eval (f ⊗ᵉ g) xs >>= λ ys → eval σᵉ ys)
      ≡⟨ refl⟩>>=⟨ (λ ys → pure-reshape-correct ys) ⟩
    (eval (f ⊗ᵉ g) xs >>= λ ys → return (map σ-fn ys))
      ≡⟨ trace-⊗ᵉ (SFunᵉ.init f) (SFunᵉ.init g) xs ⟩>>=⟨refl ⟩
    ((eval f (filter₁ xs) >>= λ bs →
        eval g (filter₂ xs) >>= λ ds →
          return (weave xs bs ds))
      >>= λ ys → return (map σ-fn ys))
      ≡⟨ >>=-assoc (eval f (filter₁ xs)) ⟩
    (eval f (filter₁ xs) >>= λ bs →
       (eval g (filter₂ xs) >>= λ ds → return (weave xs bs ds))
         >>= λ ys → return (map σ-fn ys))
      ≡⟨ refl⟩>>=⟨ (λ bs → >>=-assoc (eval g (filter₂ xs))) ⟩
    (eval f (filter₁ xs) >>= λ bs →
       eval g (filter₂ xs) >>= λ ds →
         return (weave xs bs ds) >>= λ ys → return (map σ-fn ys))
      ≡⟨ refl⟩>>=⟨ (λ bs → refl⟩>>=⟨ (λ ds → >>=-identityˡ)) ⟩
    (eval f (filter₁ xs) >>= λ bs →
       eval g (filter₂ xs) >>= λ ds →
         return (map σ-fn (weave xs bs ds)))
    ∎
    where open ≡-Reasoning

  σᵉ-natural-RHS : ∀ {A B C D} (f : SFunᵉ A B) (g : SFunᵉ C D)
    (xs : List (A ⊎ C))
    → eval ((g ⊗ᵉ f) ∘ᵉ σᵉ) xs
      ≡ (eval g (filter₂ xs) >>= λ ds →
         eval f (filter₁ xs) >>= λ bs →
           return (map σ-fn (weave xs bs ds)))
  σᵉ-natural-RHS f g xs = begin
    eval ((g ⊗ᵉ f) ∘ᵉ σᵉ) xs
      ≡⟨ sym (trace-∘ {sg = SFunᵉ.init (g ⊗ᵉ f)} {sf = tt}
                       {g = SFunᵉ.fun (g ⊗ᵉ f)} {f = SFunᵉ.fun σᵉ} xs) ⟩
    ((eval σᵉ xs >>= λ ys → return (eval (g ⊗ᵉ f) ys)) >>= λ x → x)
      ≡⟨ >>=-assoc (eval σᵉ xs) ⟩
    (eval σᵉ xs >>= λ ys → return (eval (g ⊗ᵉ f) ys) >>= λ x → x)
      ≡⟨ refl⟩>>=⟨ (λ ys → >>=-identityˡ) ⟩
    (eval σᵉ xs >>= λ ys → eval (g ⊗ᵉ f) ys)
      ≡⟨ pure-reshape-correct xs ⟩>>=⟨refl ⟩
    (return (map σ-fn xs) >>= λ ys → eval (g ⊗ᵉ f) ys)
      ≡⟨ >>=-identityˡ ⟩
    eval (g ⊗ᵉ f) (map σ-fn xs)
      ≡⟨ trace-⊗ᵉ (SFunᵉ.init g) (SFunᵉ.init f) (map σ-fn xs) ⟩
    (eval g (filter₁ (map σ-fn xs)) >>= λ bs →
       eval f (filter₂ (map σ-fn xs)) >>= λ ds →
         return (weave (map σ-fn xs) bs ds))
      ≡⟨ cong-eval-g ⟩
    (eval g (filter₂ xs) >>= λ bs →
       eval f (filter₁ xs) >>= λ ds →
         return (map σ-fn (weave xs ds bs)))
    ∎
    where
      open ≡-Reasoning
      cong-eval-g :
          (eval g (filter₁ (map σ-fn xs)) >>= λ bs →
             eval f (filter₂ (map σ-fn xs)) >>= λ ds →
               return (weave (map σ-fn xs) bs ds))
        ≡ (eval g (filter₂ xs) >>= λ bs →
             eval f (filter₁ xs) >>= λ ds →
               return (map σ-fn (weave xs ds bs)))
      cong-eval-g
        rewrite filter₁-σ xs
              | filter₂-σ xs
              = refl⟩>>=⟨ (λ bs → refl⟩>>=⟨ (λ ds →
                  cong return (weave-σ xs bs ds)))

σᵉ-natural : ∀ {A B C D} {f : SFunᵉ A B} {g : SFunᵉ C D}
  → (σᵉ ∘ᵉ (f ⊗ᵉ g)) ≈ᵉ ((g ⊗ᵉ f) ∘ᵉ σᵉ)
σᵉ-natural {f = f} {g} xs = begin
  eval (σᵉ ∘ᵉ (f ⊗ᵉ g)) xs
    ≡⟨ σᵉ-natural-LHS f g xs ⟩
  (eval f (filter₁ xs) >>= λ bs →
     eval g (filter₂ xs) >>= λ ds →
       return (map σ-fn (weave xs bs ds)))
    ≡⟨ >>=-comm-y _ ⟩
  (eval g (filter₂ xs) >>= λ ds →
     eval f (filter₁ xs) >>= λ bs →
       return (map σ-fn (weave xs bs ds)))
    ≡⟨ sym (σᵉ-natural-RHS f g xs) ⟩
  eval ((g ⊗ᵉ f) ∘ᵉ σᵉ) xs
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- σ is its own inverse: σᵉ ∘ᵉ σᵉ ≈ᵉ idᵉ.

σᵉ-involutive : ∀ {A B} → (σᵉ {A} {B} ∘ᵉ σᵉ {B} {A}) ≈ᵉ idᵉ
σᵉ-involutive = pure-reshape-∘ᵉ-id λ where
  (inj₁ _) → refl
  (inj₂ _) → refl

------------------------------------------------------------------------
-- The braiding NaturalIsomorphism.

braiding-ᵉ : NaturalIsomorphism ⊗ᵉ-bifunctor (flip-bifunctor ⊗ᵉ-bifunctor)
braiding-ᵉ = record
  { F⇒G = ntHelper (record { η = λ (A , B) → σᵉ {A} {B}
                            ; commute = λ (f , g) → σᵉ-natural {f = f} {g} })
  ; F⇐G = ntHelper (record { η = λ (A , B) → σᵉ {B} {A}
                            ; commute = λ (f , g) → σᵉ-natural {f = g} {f} })
  ; iso = λ _ → record { isoˡ = σᵉ-involutive ; isoʳ = σᵉ-involutive }
  }

------------------------------------------------------------------------
-- Hexagon laws.

------------------------------------------------------------------------
-- Hexagon laws.
--
-- Both sides are compositions of pure-reshapes; we collapse them into
-- a single `pure-reshape` and discharge the resulting function-level
-- equality by case analysis.

hexagon₁-ᵉ : ∀ {X Y Z} →
    ((idᵉ {Y} ⊗ᵉ σᵉ {X} {Z}) ∘ᵉ (α⇒ᵉ {Y} {X} {Z} ∘ᵉ (σᵉ {X} {Y} ⊗ᵉ idᵉ {Z})))
  ≈ᵉ (α⇒ᵉ {Y} {Z} {X} ∘ᵉ (σᵉ {X} {Y ⊎ Z} ∘ᵉ α⇒ᵉ {X} {Y} {Z}))
hexagon₁-ᵉ {X} {Y} {Z} xs = begin
  eval ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ (α⇒ᵉ ∘ᵉ (σᵉ ⊗ᵉ idᵉ))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (⊗ᵉ-resp-≈ᵉ idᵉ≈ᵉpure-id (λ _ → refl)) (λ _ → refl) xs ⟩
  eval ((pure-reshape id ⊗ᵉ σᵉ) ∘ᵉ (α⇒ᵉ ∘ᵉ (σᵉ ⊗ᵉ idᵉ))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (λ _ → refl)
        (∘ᵉ-resp-≈ᵉ (λ _ → refl) (⊗ᵉ-resp-≈ᵉ (λ _ → refl) idᵉ≈ᵉpure-id)) xs ⟩
  eval ((pure-reshape id ⊗ᵉ σᵉ) ∘ᵉ (α⇒ᵉ ∘ᵉ (σᵉ ⊗ᵉ pure-reshape id))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ pure-reshape-⊗ᵉ
        (∘ᵉ-resp-≈ᵉ (λ _ → refl) pure-reshape-⊗ᵉ) xs ⟩
  eval (pure-reshape (⊎-map id σ-fn) ∘ᵉ
         (α⇒ᵉ ∘ᵉ pure-reshape (⊎-map σ-fn id))) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (λ _ → refl) pure-reshape-∘ xs ⟩
  eval (pure-reshape (⊎-map id σ-fn) ∘ᵉ
         pure-reshape (α-fn ∘ ⊎-map σ-fn id)) xs
    ≡⟨ pure-reshape-∘ xs ⟩
  eval (pure-reshape (⊎-map id σ-fn ∘ (α-fn ∘ ⊎-map σ-fn id))) xs
    ≡⟨ pure-reshape-cong hex₁-fn-eq xs ⟩
  eval (pure-reshape (α-fn ∘ σ-fn ∘ α-fn)) xs
    ≡⟨ sym (pure-reshape-∘ xs) ⟩
  eval (pure-reshape α-fn ∘ᵉ pure-reshape (σ-fn ∘ α-fn)) xs
    ≡⟨ ∘ᵉ-resp-≈ᵉ (λ _ → refl) (sym ∘ pure-reshape-∘) xs ⟩
  eval (α⇒ᵉ ∘ᵉ (σᵉ ∘ᵉ α⇒ᵉ)) xs
  ∎
  where
    open ≡-Reasoning
    hex₁-fn-eq : (x : (X ⊎ Y) ⊎ Z)
      → (⊎-map id σ-fn ∘ (α-fn ∘ ⊎-map σ-fn id)) x
        ≡ (α-fn ∘ σ-fn ∘ α-fn) x
    hex₁-fn-eq (inj₁ (inj₁ _)) = refl
    hex₁-fn-eq (inj₁ (inj₂ _)) = refl
    hex₁-fn-eq (inj₂ _)        = refl

------------------------------------------------------------------------
-- Symmetric record (and from it the Braided structure).
--
-- We use `symmetricHelper`, which only requires `hexagon₁`; the second
-- hexagon is derived from `hexagon₁` and `commutative`.

symmetric-ᵉ : Symmetric
symmetric-ᵉ = symmetricHelper record
  { braiding    = braiding-ᵉ
  ; commutative = σᵉ-involutive
  ; hexagon     = hexagon₁-ᵉ
  }

braided-ᵉ : Braided
braided-ᵉ = Symmetric.braided symmetric-ᵉ

------------------------------------------------------------------------
-- Trace operator.
--
-- Given `f : SFunᵉ (A ⊎ X) (B ⊎ X)`, the trace `tr f : SFunᵉ A B`
-- uses `iter` to keep running f on inj₂-feedback until f emits on the
-- inj₁ (A-)side.

-- Continuation used by `tr-step` and `tr.fun`: classify the output
-- of f as "loop" (inj₂ x'), "done" (inj₁ b), and wrap accordingly.
tr-cont : S × (B ⊎ X) → M ((S × X) ⊎ (S × B))
tr-cont (s' , inj₁ b)  = return (inj₂ (s' , b))
tr-cont (s' , inj₂ x') = return (inj₁ (s' , x'))

-- The iteration body used by `tr`: feed back inj₂ x as inj₂-input,
-- run f, route inj₁ b as "done" and inj₂ x' as "keep looping".
tr-step : (f : SFunᵉ (A ⊎ X) (B ⊎ X))
        → SFunᵉ.State f × X → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B))
tr-step f (s , x) = SFunᵉ.fun f (s , inj₂ x) >>= tr-cont

-- Continuation used by `tr.fun`: emit on the A-side immediately,
-- or enter the iteration loop on the X-side.
tr-fun-cont : (S × X → M (S × B)) → S × (B ⊎ X) → M (S × B)
tr-fun-cont iter-bod (s' , inj₁ b) = return (s' , b)
tr-fun-cont iter-bod (s' , inj₂ x) = iter-bod (s' , x)

tr : SFunᵉ (A ⊎ X) (B ⊎ X) → SFunᵉ A B
tr {A} {B} {X} f = record
  { State = f.State
  ; init  = f.init
  ; fun   = λ (s , a) →
              f.fun (s , inj₁ a) >>= tr-fun-cont (iter (tr-step f))
  }
  where
    module f = SFunᵉ f

------------------------------------------------------------------------
-- yanking.
--
-- `tr σ ≈ᵉ id` because feeding inj₁ x through σ produces inj₂ x (one
-- loop), and feeding inj₂ x back through σ produces inj₁ x (terminate).
-- Two iter steps, both definitional, give back the original `x`.

private
  yanking-fun : ∀ {X} (s : ⊤) (x : X)
              → SFunᵉ.fun (tr {X = X} (σᵉ {X} {X})) (s , x) ≡ return (s , x)
  yanking-fun s x = begin
    SFunᵉ.fun (tr σᵉ) (s , x)
      ≡⟨⟩
    (return (s , inj₂ x) >>= tr-fun-cont (iter (tr-step σᵉ)))
      ≡⟨ >>=-identityˡ ⟩
    iter (tr-step σᵉ) (s , x)
      ≡⟨ iter-fix {f = tr-step σᵉ} (s , x) ⟩
    (tr-step σᵉ (s , x) >>= iter-cont iter (tr-step σᵉ))
      ≡⟨⟩
    ((return (s , inj₁ x) >>= tr-cont) >>= iter-cont iter (tr-step σᵉ))
      ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
    (return (inj₂ (s , x)) >>= iter-cont iter (tr-step σᵉ))
      ≡⟨ >>=-identityˡ ⟩
    return (s , x) ∎
    where open ≡-Reasoning

  yanking-trace : ∀ {X} (s : ⊤) (xs : List X)
                → trace (SFunᵉ.fun (tr {X = X} (σᵉ {X} {X}))) s xs
                  ≡ return xs
  yanking-trace s []       = refl
  yanking-trace s (x ∷ xs) = begin
    trace (SFunᵉ.fun (tr σᵉ)) s (x ∷ xs)
      ≡⟨⟩
    (SFunᵉ.fun (tr σᵉ) (s , x) >>= λ (s' , b) →
       trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ yanking-fun s x ⟩>>=⟨refl ⟩
    (return (s , x) >>= λ (s' , b) →
       trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    (trace _ s xs >>= λ bs → return (x ∷ bs))
      ≡⟨ yanking-trace s xs ⟩>>=⟨refl ⟩
    (return xs >>= λ bs → return (x ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    return (x ∷ xs) ∎
    where open ≡-Reasoning

yanking-ᵉ : ∀ {X} → tr {X = X} (σᵉ {X} {X}) ≈ᵉ idᵉ
yanking-ᵉ xs = begin
  eval (tr σᵉ) xs
    ≡⟨ yanking-trace tt xs ⟩
  return xs
    ≡⟨ id-correct xs ⟩
  eval idᵉ xs ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- vanishing₁.
--
-- When X = ⊥, the loop variable is uninhabited. `(f ⊗ᵉ idᵉ).fun` on
-- `inj₁ a` returns `f (s, a) >>= λ (s', b) → return ((s', tt), inj₁ b)`,
-- so the trace's iter is never entered.

private
  vanishing₁-fun : {f : SFunᵉ A B}
    (s : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun (tr {X = ⊥} (f ⊗ᵉ idᵉ)) ((s , tt) , a)
      ≡ (SFunᵉ.fun f (s , a) >>= λ (s' , b) → return ((s' , tt) , b))
  vanishing₁-fun {f = f} s a = begin
    SFunᵉ.fun (tr (f ⊗ᵉ idᵉ)) ((s , tt) , a)
      ≡⟨⟩
    ((SFunᵉ.fun f (s , a) >>= λ (s' , b) → return ((s' , tt) , inj₁ b))
       >>= tr-fun-cont (iter (tr-step (f ⊗ᵉ idᵉ))))
      ≡⟨ >>=-assoc (SFunᵉ.fun f (s , a)) ⟩
    (SFunᵉ.fun f (s , a) >>= λ (s' , b) →
       return ((s' , tt) , inj₁ b) >>= tr-fun-cont (iter (tr-step (f ⊗ᵉ idᵉ))))
      ≡⟨ refl⟩>>=⟨ (λ (s' , b) → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (s , a) >>= λ (s' , b) → return ((s' , tt) , b))
    ∎
    where open ≡-Reasoning

  vanishing₁-trace : {f : SFunᵉ A B}
    (s : SFunᵉ.State f) (xs : List A)
    → trace (SFunᵉ.fun (tr {X = ⊥} (f ⊗ᵉ idᵉ))) (s , tt) xs
      ≡ trace (SFunᵉ.fun f) s xs
  vanishing₁-trace s [] = refl
  vanishing₁-trace {f = f} s (a ∷ xs) = begin
    trace (SFunᵉ.fun (tr (f ⊗ᵉ idᵉ))) (s , tt) (a ∷ xs)
      ≡⟨⟩
    (SFunᵉ.fun (tr (f ⊗ᵉ idᵉ)) ((s , tt) , a) >>= λ (s' , b) →
       trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ vanishing₁-fun {f = f} s a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (s , a) >>= λ (s' , b) → return ((s' , tt) , b))
       >>= λ (s'' , b') → trace _ s'' xs >>= λ bs → return (b' ∷ bs))
      ≡⟨ >>=-assoc (SFunᵉ.fun f (s , a)) ⟩
    (SFunᵉ.fun f (s , a) >>= λ (s' , b) →
       return ((s' , tt) , b) >>= λ (s'' , b') →
         trace _ s'' xs >>= λ bs → return (b' ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , b) → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (s , a) >>= λ (s' , b) →
       trace (SFunᵉ.fun (tr (f ⊗ᵉ idᵉ))) (s' , tt) xs >>= λ bs →
         return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (s' , b) → vanishing₁-trace {f = f} s' xs ⟩>>=⟨refl) ⟩
    (SFunᵉ.fun f (s , a) >>= λ (s' , b) →
       trace (SFunᵉ.fun f) s' xs >>= λ bs → return (b ∷ bs))
    ∎
    where open ≡-Reasoning

vanishing₁-ᵉ : {f : SFunᵉ A B} → tr {X = ⊥} (f ⊗ᵉ idᵉ) ≈ᵉ f
vanishing₁-ᵉ {f = f} xs = vanishing₁-trace {f = f} (SFunᵉ.init f) xs


------------------------------------------------------------------------
-- superposing.
--
-- For `f : SFunᵉ (A ⊎ X) (B ⊎ X)` and trace over X:
--   tr (α⇐ ∘ (id_Y ⊗ f) ∘ α⇒) ≈ᵉ id_Y ⊗ tr f
--
-- Intuition: on `inj₁ y` the inner morphism `α⇐ ∘ (id⊗f) ∘ α⇒` just
-- rebrackets and returns `inj₁(inj₁ y)` (f is never invoked), so tr's
-- continuation emits directly. On `inj₂ a` the inner morphism runs f
-- and routes inj₁/inj₂ outputs identically to how tr(f) would; the
-- X-loop coincides via `iter-conjugate`.

private
  -- ⊗ᵉ on (inj₁ y) with id on the left: just returns the input,
  -- threading f's state unchanged.
  id⊗f-on-Y :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (y : Y)
    → SFunᵉ.fun (idᵉ {Y} ⊗ᵉ f) ((tt , sf) , inj₁ y)
      ≡ return ((tt , sf) , inj₁ y)
  id⊗f-on-Y sf y = >>=-identityˡ

  -- ((id ⊗ f) ∘ α⇒) on inj₁(inj₁ y): also pure passthrough.
  id⊗f-∘-α⇒-on-Y :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (y : Y)
    → SFunᵉ.fun ((idᵉ {Y} ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})
                (((tt , sf) , tt) , inj₁ (inj₁ y))
      ≡ return (((tt , sf) , tt) , inj₁ y)
  id⊗f-∘-α⇒-on-Y {f = f} sf y = begin
    SFunᵉ.fun ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ) (((tt , sf) , tt) , inj₁ (inj₁ y))
      ≡⟨ >>=-identityˡ ⟩
    (SFunᵉ.fun (idᵉ ⊗ᵉ f) ((tt , sf) , inj₁ y) >>= λ (sIF , b) →
       return ((sIF , tt) , b))
      ≡⟨ id⊗f-on-Y {f = f} sf y ⟩>>=⟨refl ⟩
    (return ((tt , sf) , inj₁ y) >>= λ (sIF , b) →
       return ((sIF , tt) , b))
      ≡⟨ >>=-identityˡ ⟩
    return (((tt , sf) , tt) , inj₁ y)
    ∎
    where open ≡-Reasoning

  -- (α⇐ ∘ (id⊗f) ∘ α⇒) on inj₁(inj₁ y): wraps back to inj₁(inj₁ y).
  inner-Y :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (y : Y)
    → SFunᵉ.fun (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))
                ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
      ≡ return ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
  inner-Y {f = f} sf y = begin
    SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))
              ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
      ≡⟨ id⊗f-∘-α⇒-on-Y {f = f} sf y ⟩>>=⟨refl ⟩
    (return (((tt , sf) , tt) , inj₁ y) >>= λ (sM' , b) →
      return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
      return ((sα⇐' , sM') , c))
      ≡⟨ >>=-identityˡ ⟩
    (return (tt , inj₁ (inj₁ y)) >>= λ (sα⇐' , c) →
      return ((sα⇐' , ((tt , sf) , tt)) , c))
      ≡⟨ >>=-identityˡ ⟩
    return ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
    ∎
    where open ≡-Reasoning

  -- tr's fun on Y-input passes through (no loop), preserving state.
  LHS-Y-step :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (y : Y)
    → SFunᵉ.fun (tr {X = X} (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})))
                ((tt , ((tt , sf) , tt)) , inj₁ y)
      ≡ return ((tt , ((tt , sf) , tt)) , inj₁ y)
  LHS-Y-step {f = f} sf y = begin
    SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))
              ((tt , ((tt , sf) , tt)) , inj₁ y)
      ≡⟨⟩
    (SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))
              ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
        >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))))
      ≡⟨ inner-Y {f = f} sf y ⟩>>=⟨refl ⟩
    (return ((tt , ((tt , sf) , tt)) , inj₁ (inj₁ y))
       >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))))
      ≡⟨ >>=-identityˡ ⟩
    return ((tt , ((tt , sf) , tt)) , inj₁ y)
    ∎
    where open ≡-Reasoning

  -- (id ⊗ tr f)'s fun on Y-input: same passthrough behavior.
  RHS-Y-step :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (y : Y)
    → SFunᵉ.fun (idᵉ {Y} ⊗ᵉ tr {X = X} f) ((tt , sf) , inj₁ y)
      ≡ return ((tt , sf) , inj₁ y)
  RHS-Y-step sf y = >>=-identityˡ

  -- (id ⊗ f).fun on inj₂(inj₁ a): inj₂ branch of ⊗ᵉ' runs f.
  id⊗f-on-A :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun (idᵉ {Y} ⊗ᵉ f) ((tt , sf) , inj₂ (inj₁ a))
      ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
          return ((tt , sf') , inj₂ byx))
  id⊗f-on-A sf a = refl

  -- (id ⊗ f).fun on inj₂(inj₂ x): inj₂ branch of ⊗ᵉ' runs f on inj₂ x.
  id⊗f-on-X :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (x : X)
    → SFunᵉ.fun (idᵉ {Y} ⊗ᵉ f) ((tt , sf) , inj₂ (inj₂ x))
      ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
          return ((tt , sf') , inj₂ byx))
  id⊗f-on-X sf x = refl

  -- ((id ⊗ f) ∘ α⇒) on inj₁(inj₂ a) reduces to f.fun + state rebracket.
  id⊗f-∘-α⇒-on-A :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun ((idᵉ {Y} ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})
                (((tt , sf) , tt) , inj₁ (inj₂ a))
      ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
          return (((tt , sf') , tt) , inj₂ byx))
  id⊗f-∘-α⇒-on-A {f = f} sf a = begin
    SFunᵉ.fun ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ) (((tt , sf) , tt) , inj₁ (inj₂ a))
      ≡⟨ >>=-identityˡ ⟩
    (SFunᵉ.fun (idᵉ ⊗ᵉ f) ((tt , sf) , inj₂ (inj₁ a)) >>= λ (sIF , b) →
       return ((sIF , tt) , b))
      ≡⟨ id⊗f-on-A {f = f} sf a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        return ((tt , sf') , inj₂ byx))
        >>= λ (sIF , b) → return ((sIF , tt) , b))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        return ((tt , sf') , inj₂ byx) >>= λ (sIF , b) →
          return ((sIF , tt) , b))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        return (((tt , sf') , tt) , inj₂ byx))
    ∎
    where open ≡-Reasoning

  -- Same shape for the loop step: inner morphism on inj₂ x.
  id⊗f-∘-α⇒-on-X :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (x : X)
    → SFunᵉ.fun ((idᵉ {Y} ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})
                (((tt , sf) , tt) , inj₂ x)
      ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
          return (((tt , sf') , tt) , inj₂ byx))
  id⊗f-∘-α⇒-on-X {f = f} sf x = begin
    SFunᵉ.fun ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ) (((tt , sf) , tt) , inj₂ x)
      ≡⟨ >>=-identityˡ ⟩
    (SFunᵉ.fun (idᵉ ⊗ᵉ f) ((tt , sf) , inj₂ (inj₂ x)) >>= λ (sIF , b) →
       return ((sIF , tt) , b))
      ≡⟨ id⊗f-on-X {f = f} sf x ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
        return ((tt , sf') , inj₂ byx))
        >>= λ (sIF , b) → return ((sIF , tt) , b))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
        return ((tt , sf') , inj₂ byx) >>= λ (sIF , b) →
          return ((sIF , tt) , b))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
        return (((tt , sf') , tt) , inj₂ byx))
    ∎
    where open ≡-Reasoning

  -- α⇐ collapse: α-fn-inv (inj₂ byx) returns inj₁(inj₂ b) for inj₁ b
  -- and inj₂ x for inj₂ x.

  -- Full inner morphism on inj₁(inj₂ a).
  inner-A :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))
                ((tt , ((tt , sf) , tt)) , inj₁ (inj₂ a))
      ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
          return ((tt , ((tt , sf') , tt)) , α-fn-inv (inj₂ byx)))
  inner-A {f = f} sf a = begin
    SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))
              ((tt , ((tt , sf) , tt)) , inj₁ (inj₂ a))
      ≡⟨ id⊗f-∘-α⇒-on-A {f = f} sf a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        return (((tt , sf') , tt) , inj₂ byx))
       >>= λ (sM , b) →
       return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
       return ((sα⇐' , sM) , c))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       return (((tt , sf') , tt) , inj₂ byx) >>= λ (sM , b) →
       return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
       return ((sα⇐' , sM) , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       return (tt , α-fn-inv (inj₂ byx)) >>= λ (sα⇐' , c) →
       return ((sα⇐' , ((tt , sf') , tt)) , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       return ((tt , ((tt , sf') , tt)) , α-fn-inv (inj₂ byx)))
    ∎
    where open ≡-Reasoning

  -- Full inner morphism on inj₂ x — used for tr-step inside iter.
  inner-X :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (x : X)
    → SFunᵉ.fun (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))
                ((tt , ((tt , sf) , tt)) , inj₂ x)
      ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
          return ((tt , ((tt , sf') , tt)) , α-fn-inv (inj₂ byx)))
  inner-X {f = f} sf x = begin
    SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))
              ((tt , ((tt , sf) , tt)) , inj₂ x)
      ≡⟨ id⊗f-∘-α⇒-on-X {f = f} sf x ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
        return (((tt , sf') , tt) , inj₂ byx))
       >>= λ (sM , b) →
       return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
       return ((sα⇐' , sM) , c))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       return (((tt , sf') , tt) , inj₂ byx) >>= λ (sM , b) →
       return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
       return ((sα⇐' , sM) , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       return (tt , α-fn-inv (inj₂ byx)) >>= λ (sα⇐' , c) →
       return ((sα⇐' , ((tt , sf') , tt)) , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       return ((tt , ((tt , sf') , tt)) , α-fn-inv (inj₂ byx)))
    ∎
    where open ≡-Reasoning

  -- Premise of iter-conjugate: tr-step of LHS-morph at padded state
  -- is tr-step of f, with output mapped through `iter-conj-step φ ψ`,
  -- where φ pads state and ψ wraps in inj₂.
  φ-pad : ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
        → SFunᵉ.State f → SFunᵉ.State (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))
  φ-pad {Y = Y} {A = A} {f = f} sf = tt , ((tt , sf) , tt)

  ψ-inj₂ : ∀ {Y′ B′ : Type} → B′ → Y′ ⊎ B′
  ψ-inj₂ b = inj₂ b

  tr-step-premise :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (x : X)
    → tr-step (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})) (φ-pad {Y = Y} {A = A} {f = f} sf , x)
      ≡ (tr-step f (sf , x)
          >>= iter-conj-step {A = B} {B = Y ⊎ B} (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂)
  tr-step-premise {Y = Y} {A = A} {f = f} sf x = begin
    tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)) (φ-pad {Y = Y} {A = A} {f = f} sf , x)
      ≡⟨⟩
    (SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)) (φ-pad {Y = Y} {A = A} {f = f} sf , inj₂ x) >>= tr-cont)
      ≡⟨ inner-X {f = f} sf x ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
        return (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx)))
       >>= tr-cont)
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       return (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx)) >>= tr-cont)
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       tr-cont (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx)))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , byx) → lemma sf' byx) ⟩
    (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , byx) →
       tr-cont (sf' , byx) >>= iter-conj-step (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂)
      ≡˘⟨ >>=-assoc _ ⟩
    ((SFunᵉ.fun f (sf , inj₂ x) >>= tr-cont)
       >>= iter-conj-step (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂)
      ≡⟨⟩
    (tr-step f (sf , x) >>= iter-conj-step (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂)
    ∎
    where
      open ≡-Reasoning
      -- Per-output case analysis: route α-fn-inv ∘ inj₂ through tr-cont
      -- and show it equals tr-cont composed with iter-conj-step.
      lemma : (sf' : SFunᵉ.State f) (byx : _)
        → tr-cont (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv {Y} (inj₂ byx))
          ≡ (tr-cont (sf' , byx) >>= iter-conj-step (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂)
      lemma sf' (inj₁ b) = sym >>=-identityˡ
      lemma sf' (inj₂ x') = sym >>=-identityˡ

  -- iter on LHS-morph's tr-step at padded state equals iter on f's
  -- tr-step, post-composed with state-padding and inj₂-wrapping.
  iter-equiv :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (x : X)
    → iter (tr-step (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))) (φ-pad {Y = Y} {A = A} {f = f} sf , x)
      ≡ (iter (tr-step f) (sf , x) >>= λ (sf' , b) →
          return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
  iter-equiv {Y = Y} {A = A} {f = f} sf x =
    iter-conjugate
      (φ-pad {Y = Y} {A = A} {f = f}) ψ-inj₂
      (tr-step f)
      (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))
      (λ s₁ x' → tr-step-premise {Y = Y} {A = A} {f = f} s₁ x')
      sf x

  -- tr's fun on inj₂ a for LHS: f's first call + route through tr-fun-cont.
  LHS-A-step :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun (tr {X = X} (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X})))
                (φ-pad {Y = Y} {A = A} {f = f} sf , inj₂ a)
      ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
          [ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
          , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                     return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
          ]′ byx)
  LHS-A-step {Y = Y} {A = A} {f = f} sf a = begin
    SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))) (φ-pad {Y = Y} {A = A} {f = f} sf , inj₂ a)
      ≡⟨⟩
    (SFunᵉ.fun (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)) (φ-pad {Y = Y} {A = A} {f = f} sf , inj₁ (inj₂ a))
       >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))))
      ≡⟨ inner-A {f = f} sf a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        return (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx)))
       >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       return (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx))
         >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))))
                   (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ byx)))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , byx) → case-branch sf' byx) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       [ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
       , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                  return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
       ]′ byx)
    ∎
    where
      open ≡-Reasoning
      -- Per-output case: route α-fn-inv ∘ inj₂ through tr-fun-cont,
      -- and use iter-equiv for the loop case.
      case-branch : (sf' : SFunᵉ.State f) (byx : _)
        → tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))))
                      (φ-pad {Y = Y} {A = A} {f = f} sf' , α-fn-inv {Y} (inj₂ byx))
          ≡ [ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
            , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                       return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
            ]′ byx
      case-branch sf' (inj₁ b)  = refl
      case-branch sf' (inj₂ x') = iter-equiv {f = f} sf' x'

  -- (id ⊗ tr f).fun on inj₂ a, reduced to the same f.fun + iter form.
  RHS-A-step :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (a : A)
    → SFunᵉ.fun (idᵉ {Y} ⊗ᵉ tr {X = X} f) ((tt , sf) , inj₂ a)
      ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
          [ (λ b → return ((tt , sf') , inj₂ b))
          , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                     return ((tt , sf'') , inj₂ b))
          ]′ byx)
  RHS-A-step {f = f} sf a = begin
    SFunᵉ.fun (idᵉ ⊗ᵉ tr f) ((tt , sf) , inj₂ a)
      ≡⟨⟩
    (SFunᵉ.fun (tr f) (sf , a) >>= λ (sf' , b) →
       return ((tt , sf') , inj₂ b))
      ≡⟨⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= tr-fun-cont (iter (tr-step f)))
       >>= λ (sf' , b) → return ((tt , sf') , inj₂ b))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       tr-fun-cont (iter (tr-step f)) (sf' , byx) >>= λ (sf'' , b) →
         return ((tt , sf'') , inj₂ b))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , byx) → case-branch sf' byx) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       [ (λ b → return ((tt , sf') , inj₂ b))
       , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                  return ((tt , sf'') , inj₂ b))
       ]′ byx)
    ∎
    where
      open ≡-Reasoning
      case-branch : (sf' : SFunᵉ.State f) (byx : _)
        → (tr-fun-cont (iter (tr-step f)) (sf' , byx) >>= λ (sf'' , b) →
            return ((tt , sf'') , inj₂ b))
          ≡ [ (λ b → return ((tt , sf') , inj₂ b))
            , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                       return ((tt , sf'') , inj₂ b))
            ]′ byx
      case-branch sf' (inj₁ b)  = >>=-identityˡ
      case-branch sf' (inj₂ x') = refl

  -- The trace-level inj₂ case: combine LHS-A-step, RHS-A-step,
  -- and the IH on the tail.
  -- The trace-level claim, parameterised over the (matching) states.
  superposing-trace :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
    (sf : SFunᵉ.State f) (xs : List (Y ⊎ A))
    → trace (SFunᵉ.fun (tr {X = X} (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))))
            (tt , ((tt , sf) , tt)) xs
      ≡ trace (SFunᵉ.fun (idᵉ {Y} ⊗ᵉ tr {X = X} f)) (tt , sf) xs
  superposing-trace sf [] = refl
  superposing-trace {f = f} sf (inj₁ y ∷ xs) = begin
    trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))))
          (tt , ((tt , sf) , tt)) (inj₁ y ∷ xs)
      ≡⟨⟩
    (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))
               ((tt , ((tt , sf) , tt)) , inj₁ y)
        >>= λ (s' , b) →
           trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ LHS-Y-step {f = f} sf y ⟩>>=⟨refl ⟩
    (return ((tt , ((tt , sf) , tt)) , inj₁ y) >>= λ (s' , b) →
        trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ >>=-identityˡ ⟩
    (trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))))
           (tt , ((tt , sf) , tt)) xs
       >>= λ bs → return (inj₁ y ∷ bs))
      ≡⟨ superposing-trace {f = f} sf xs ⟩>>=⟨refl ⟩
    (trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) (tt , sf) xs
       >>= λ bs → return (inj₁ y ∷ bs))
      ≡˘⟨ >>=-identityˡ ⟩
    (return ((tt , sf) , inj₁ y) >>= λ (s' , b) →
        trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡˘⟨ RHS-Y-step {f = f} sf y ⟩>>=⟨refl ⟩
    (SFunᵉ.fun (idᵉ ⊗ᵉ tr f) ((tt , sf) , inj₁ y) >>= λ (s' , b) →
        trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨⟩
    trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) (tt , sf) (inj₁ y ∷ xs)
    ∎
    where open ≡-Reasoning
  superposing-trace {Y = Y} {A = A} {f = f} sf (inj₂ a ∷ xs) = begin
    trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))))
          (φ-pad {Y = Y} {A = A} {f = f} sf) (inj₂ a ∷ xs)
      ≡⟨⟩
    (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ))) (φ-pad {Y = Y} {A = A} {f = f} sf , inj₂ a)
       >>= λ (s' , b) → trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ LHS-A-step {f = f} sf a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        [ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
        , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                   return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
        ]′ byx)
       >>= λ (s' , b) → trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       [ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
       , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                  return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
       ]′ byx
         >>= λ (s' , b) → trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , byx) → tail-eq sf' byx) ⟩
    (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
       [ (λ b → return ((tt , sf') , inj₂ b))
       , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                  return ((tt , sf'') , inj₂ b))
       ]′ byx
         >>= λ (s' , b) → trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
                            >>= λ bs → return (b ∷ bs))
      ≡˘⟨ >>=-assoc _ ⟩
    ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byx) →
        [ (λ b → return ((tt , sf') , inj₂ b))
        , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                   return ((tt , sf'') , inj₂ b))
        ]′ byx)
       >>= λ (s' , b) → trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
                          >>= λ bs → return (b ∷ bs))
      ≡˘⟨ RHS-A-step {f = f} sf a ⟩>>=⟨refl ⟩
    (SFunᵉ.fun (idᵉ ⊗ᵉ tr f) ((tt , sf) , inj₂ a) >>= λ (s' , b) →
       trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨⟩
    trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) (tt , sf) (inj₂ a ∷ xs)
    ∎
    where
      open ≡-Reasoning
      -- After f's first call, the case-branch's result feeds into the
      -- tail trace. For each case, the LHS-state (φ-pad {Y = Y} {A = A} {f = f} sf') and the
      -- RHS-state ((tt, sf')) differ; the tail trace bridges this via
      -- the IH `superposing-trace`.
      tail-eq : (sf' : SFunᵉ.State f) (byx : _)
        → ([ (λ b → return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b))
           , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                      return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
           ]′ byx
             >>= λ (s' , b) →
               trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) s' xs
                 >>= λ bs → return (b ∷ bs))
          ≡ ([ (λ b → return ((tt , sf') , inj₂ b))
             , (λ x → iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
                        return ((tt , sf'') , inj₂ b))
             ]′ byx
               >>= λ (s' , b) →
                 trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
                   >>= λ bs → return (b ∷ bs))
      tail-eq sf' (inj₁ b) = begin
        (return (φ-pad {Y = Y} {A = A} {f = f} sf' , inj₂ b)
           >>= λ (s' , b') →
             trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) s' xs
               >>= λ bs → return (b' ∷ bs))
          ≡⟨ >>=-identityˡ ⟩
        (trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) (φ-pad {Y = Y} {A = A} {f = f} sf') xs
           >>= λ bs → return (inj₂ b ∷ bs))
          ≡⟨ superposing-trace {f = f} sf' xs ⟩>>=⟨refl ⟩
        (trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) (tt , sf') xs
           >>= λ bs → return (inj₂ b ∷ bs))
          ≡˘⟨ >>=-identityˡ ⟩
        (return ((tt , sf') , inj₂ b)
           >>= λ (s' , b') →
             trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
               >>= λ bs → return (b' ∷ bs))
        ∎
      tail-eq sf' (inj₂ x) = begin
        ((iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
             return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b))
           >>= λ (s' , b') →
             trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) s' xs
               >>= λ bs → return (b' ∷ bs))
          ≡⟨ >>=-assoc _ ⟩
        (iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
           return (φ-pad {Y = Y} {A = A} {f = f} sf'' , inj₂ b) >>= λ (s' , b') →
             trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) s' xs
               >>= λ bs → return (b' ∷ bs))
          ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
        (iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
           trace (SFunᵉ.fun (tr (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ)))) (φ-pad {Y = Y} {A = A} {f = f} sf'') xs
             >>= λ bs → return (inj₂ b ∷ bs))
          ≡⟨ refl⟩>>=⟨ (λ (sf'' , b) →
               superposing-trace {f = f} sf'' xs ⟩>>=⟨refl) ⟩
        (iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
           trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) (tt , sf'') xs
             >>= λ bs → return (inj₂ b ∷ bs))
          ≡˘⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
        (iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
           return ((tt , sf'') , inj₂ b) >>= λ (s' , b') →
             trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
               >>= λ bs → return (b' ∷ bs))
          ≡˘⟨ >>=-assoc _ ⟩
        ((iter (tr-step f) (sf' , x) >>= λ (sf'' , b) →
             return ((tt , sf'') , inj₂ b))
           >>= λ (s' , b') →
             trace (SFunᵉ.fun (idᵉ ⊗ᵉ tr f)) s' xs
               >>= λ bs → return (b' ∷ bs))
        ∎

superposing-ᵉ : ∀ {X Y A B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
  → tr {X = X} (α⇐ᵉ {Y} {B} {X} ∘ᵉ ((idᵉ ⊗ᵉ f) ∘ᵉ α⇒ᵉ {Y} {A} {X}))
    ≈ᵉ (idᵉ {Y} ⊗ᵉ tr {X = X} f)
superposing-ᵉ {f = f} = superposing-trace {f = f} (SFunᵉ.init f)

------------------------------------------------------------------------
-- vanishing₂.
--
-- Nested traces over Y (inner) and X (outer) collapse into a single
-- trace over X ⊎ Y. This is JSV's vanishing₂ axiom.
--
-- Proof strategy: derive two iter bodies fx-f, fy-f from f such that
-- combine fx-f fy-f ≡ tr-step f. Then by the (full) iter-codiag axiom
-- in `Class.Monad.Iterative`, iter (tr-step f) on inj₁ x corresponds
-- to a nested iter — outer X-iter with an inner Y-iter (iter fy-f)
-- that may switch back to X. This nested form matches the LHS's
-- tr_X(tr_Y(α⇐ ∘ f ∘ α⇒)) via iter-conjugate (state padding by α⇐,
-- α⇒ which carry only ⊤-state).

private
  -- State-padding map: from f's state to LHS-morph's state. The
  -- intermediate ⊤'s come from the trivial states of α⇐ and α⇒.
  φ₂ : ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
     → SFunᵉ.State f
     → SFunᵉ.State (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ {A} {X} {Y}))
  φ₂ sf = tt , (sf , tt)

  -- (f ∘ᵉ α⇒ᵉ) reduces to f applied to α-fn z.
  f-∘-α⇒-2 :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (z : (A ⊎ X) ⊎ Y)
    → SFunᵉ.fun (f ∘ᵉ α⇒ᵉ {A} {X} {Y}) ((sf , tt) , z)
      ≡ (SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
          return ((sf' , tt) , byxy))
  f-∘-α⇒-2 sf z = >>=-identityˡ

  -- The inner morphism's behaviour on each input case: it just runs
  -- f on the α-rebracketed input and then α-rebrackets the output.
  inner₂ :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (z : (A ⊎ X) ⊎ Y)
    → SFunᵉ.fun (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , z)
      ≡ (SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
  inner₂ {X = X} {Y = Y} {A = A} {f = f} sf z = begin
    SFunᵉ.fun (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)) ((tt , (sf , tt)) , z)
      ≡⟨ f-∘-α⇒-2 {f = f} sf z ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
        return ((sf' , tt) , byxy))
       >>= λ (s' , b) →
         return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
         return ((sα⇐' , s') , c))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
       return ((sf' , tt) , byxy) >>= λ (s' , b) →
         return (tt , α-fn-inv b) >>= λ (sα⇐' , c) →
         return ((sα⇐' , s') , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
       return (tt , α-fn-inv byxy) >>= λ (sα⇐' , c) →
       return ((sα⇐' , (sf' , tt)) , c))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , α-fn z) >>= λ (sf' , byxy) →
       return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
    ∎
    where open ≡-Reasoning

  -- Named routing bodies: factored out so equational reasoning can
  -- compare them definitionally rather than relying on alpha/eta of
  -- inline `λ where` lambdas.
  fx-route : ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
           → SFunᵉ.State f × (B ⊎ (X ⊎ Y))
           → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y)))
  fx-route (sf' , inj₁ b)         = return (inj₂ (sf' , inj₁ b))
  fx-route (sf' , inj₂ (inj₁ x')) = return (inj₁ (sf' , x'))
  fx-route (sf' , inj₂ (inj₂ y))  = return (inj₂ (sf' , inj₂ y))

  fy-route : ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
           → SFunᵉ.State f × (B ⊎ (X ⊎ Y))
           → M ((SFunᵉ.State f × Y) ⊎ (SFunᵉ.State f × (B ⊎ X)))
  fy-route (sf' , inj₁ b)         = return (inj₂ (sf' , inj₁ b))
  fy-route (sf' , inj₂ (inj₁ x))  = return (inj₂ (sf' , inj₂ x))
  fy-route (sf' , inj₂ (inj₂ y')) = return (inj₁ (sf' , y'))

  -- X-iter body derived from f: handles input inj₂(inj₁ x) (the X
  -- branch of f's input X⊎Y). f's output is routed via fx-route.
  fx-f : ∀ {X Y A B} (f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y)))
       → (SFunᵉ.State f × X)
       → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y)))
  fx-f f (sf , x) = SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= fx-route {f = f}

  -- Y-iter body derived from f: handles input inj₂(inj₂ y). f's output
  -- can either emit B (final), loop in Y, or switch to outer X-iter —
  -- the cross-branch case enabled by the strengthened iter-codiag.
  fy-f : ∀ {X Y A B} (f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y)))
       → (SFunᵉ.State f × Y)
       → M ((SFunᵉ.State f × Y) ⊎ (SFunᵉ.State f × (B ⊎ X)))
  fy-f f (sf , y) = SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= fy-route {f = f}

  -- The Bekič combine of fx-f and fy-f equals f's tr-step. Bridge
  -- lemma — connects f's tr-step (which acts directly on X⊎Y) to the
  -- case-split combine form so the strengthened iter-codiag can be
  -- applied.
  tr-step-f-as-combine :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (z : X ⊎ Y)
    → tr-step f (sf , z) ≡ combine (fx-f f) (fy-f f) (sf , z)
  tr-step-f-as-combine {f = f} sf (inj₁ x) =
    trans (refl⟩>>=⟨ (λ where
      (sf' , inj₁ b)          → sym >>=-identityˡ
      (sf' , inj₂ (inj₁ x'))  → sym >>=-identityˡ
      (sf' , inj₂ (inj₂ y))   → sym >>=-identityˡ))
      (sym (>>=-assoc _))
  tr-step-f-as-combine {f = f} sf (inj₂ y) =
    trans (refl⟩>>=⟨ (λ where
      (sf' , inj₁ b)          → sym >>=-identityˡ
      (sf' , inj₂ (inj₁ x))   → sym >>=-identityˡ
      (sf' , inj₂ (inj₂ y'))  → sym >>=-identityˡ))
      (sym (>>=-assoc _))

  -- The inner Y-iter body of LHS = tr_X(tr_Y(α⇐ ∘ f ∘ α⇒)) is
  -- `tr-step (α⇐ ∘ f ∘ α⇒)`. We show it equals fy-f's body (post-
  -- composed through `iter-conj-step φ₂ id` to handle state-padding).
  -- This is the premise of iter-conjugate, which then gives the
  -- iter-equivalence between LHS's inner Y-iter and iter (fy-f f).
  tr-step-LHS-morph-y :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (y : Y)
    → tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , y)
      ≡ (fy-f f (sf , y) >>=
          iter-conj-step {A = B ⊎ X} {B = B ⊎ X}
                         (φ₂ {X = X} {Y = Y} {A = A} {f = f})
                         (λ b → b))
  tr-step-LHS-morph-y {X = X} {Y = Y} {A = A} {B = B} {f = f} sf y = begin
    tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , y)
      ≡⟨⟩
    (SFunᵉ.fun (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , inj₂ y) >>= tr-cont)
      ≡⟨ inner₂ {X = X} {Y = Y} {A = A} {f = f} sf (inj₂ y) ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= λ (sf' , byxy) →
        return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
       >>= tr-cont)
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= λ (sf' , byxy) →
       return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy) >>= tr-cont)
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= λ (sf' , byxy) →
       tr-cont (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , byxy) → pointwise sf' byxy) ⟩
    (SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= λ (sf' , byxy) →
       fy-route {f = f} (sf' , byxy) >>=
       iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
      ≡˘⟨ >>=-assoc _ ⟩
    ((SFunᵉ.fun f (sf , inj₂ (inj₂ y)) >>= fy-route {f = f})
       >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
      ≡⟨⟩
    (fy-f f (sf , y) >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
    ∎
    where
      open ≡-Reasoning
      -- Pointwise: for each f-output byxy, tr-cont (after α-fn-inv)
      -- equals fy-route's routing then iter-conj-step's state-padding.
      pointwise : (sf' : SFunᵉ.State f) (byxy : B ⊎ (X ⊎ Y))
        → tr-cont (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
          ≡ (fy-route {f = f} (sf' , byxy) >>=
              iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
      pointwise sf' (inj₁ b)         = sym >>=-identityˡ
      pointwise sf' (inj₂ (inj₁ x))  = sym >>=-identityˡ
      pointwise sf' (inj₂ (inj₂ y')) = sym >>=-identityˡ

  -- iter on the inner Y-iter body (LHS) equals iter on fy-f (RHS-ish)
  -- post-composed with state-padding. This is iter-conjugate applied
  -- to tr-step-LHS-morph-y.
  iter-equiv-2-y :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (y : Y)
    → iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , y)
      ≡ (iter (fy-f f) (sf , y) >>= λ (sf' , a) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , a))
  iter-equiv-2-y {X = X} {Y = Y} {A = A} {f = f} sf y =
    iter-conjugate
      (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)
      (fy-f f)
      (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))
      (λ s₁ y' → tr-step-LHS-morph-y {X = X} {Y = Y} {A = A} {f = f} s₁ y')
      sf y

  -- ----------------------------------------------------------------
  -- Outer X-iter: relating tr-step M (the outer X-iter body of LHS)
  -- to iter-codiag's outer body using fx-f and (inner) iter (fy-f).
  -- ----------------------------------------------------------------

  -- Named outer-routing for outer-body-2: extracted so equational
  -- reasoning can match it definitionally.
  inner-iter-route :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    → SFunᵉ.State f × (B ⊎ X)
    → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B))
  inner-iter-route (sf'' , inj₁ b)  = return (inj₂ (sf'' , b))
  inner-iter-route (sf'' , inj₂ x') = return (inj₁ (sf'' , x'))

  outer-route :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    → (SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y))
    → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B))
  outer-route (inj₁ (sf' , x'))     = return (inj₁ (sf' , x'))
  outer-route (inj₂ (sf' , inj₁ b)) = return (inj₂ (sf' , b))
  outer-route {f = f} (inj₂ (sf' , inj₂ y)) =
    iter (fy-f f) (sf' , y) >>= inner-iter-route {f = f}

  -- iter-codiag's outer body: drives fx-f and enters inner iter (fy-f)
  -- when fx-f signals fall-through (inj₂ y). The inner iter's result
  -- routes back: A → outer done, X → outer loop.
  outer-body-2 :
    ∀ {X Y A B} (f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y)))
    → (SFunᵉ.State f × X)
    → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B))
  outer-body-2 f (sf , x) = fx-f f (sf , x) >>= outer-route {f = f}

  -- tr-step M (the outer X-iter body of LHS) equals outer-body-2
  -- modulo state-padding via φ₂. Uses inner₂ + iter-equiv-2-y for
  -- the inj₂(inj₂ y) case.
  tr-step-M-x :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (x : X)
    → tr-step (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))
              (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , x)
      ≡ (outer-body-2 f (sf , x) >>=
          iter-conj-step {A = B} {B = B}
                         (φ₂ {X = X} {Y = Y} {A = A} {f = f})
                         (λ b → b))
  tr-step-M-x {X = X} {Y = Y} {A = A} {B = B} {f = f} sf x = begin
      tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , x)
        ≡⟨⟩
      ((SFunᵉ.fun (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))
           (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , inj₁ (inj₂ x))
           >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
         >>= tr-cont)
        ≡⟨ inner₂ {X = X} {Y = Y} {A = A} {f = f} sf (inj₁ (inj₂ x))
             ⟩>>=⟨refl ⟩>>=⟨refl ⟩
      (((SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
           return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
          >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
         >>= tr-cont)
        ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
            >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
         >>= tr-cont)
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
        (return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
           >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
          >>= tr-cont)
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ ⟩>>=⟨refl) ⟩
      (SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
        tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                    (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
          >>= tr-cont)
        ≡⟨ _⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ refl (λ where (sf' , byxy) → pointwise sf' byxy) ⟩
      (SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
        (fx-route {f = f} (sf' , byxy) >>= outer-route {f = f})
          >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
        ≡˘⟨ >>=-assoc _ ⟩
      ((SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= λ (sf' , byxy) →
          fx-route {f = f} (sf' , byxy) >>= outer-route {f = f})
         >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
        ≡˘⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      (((SFunᵉ.fun f (sf , inj₂ (inj₁ x)) >>= fx-route {f = f})
          >>= outer-route {f = f})
         >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
        ≡⟨⟩
      (outer-body-2 f (sf , x)
         >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
    ∎
    where
      open ≡-Reasoning
      -- Pointwise: for each f-output byxy, the LHS routing equals the
      -- RHS routing. Per-case proofs differ for inj₂(inj₂ y) where both
      -- sides invoke iter (fy-f f) — handled via iter-equiv-2-y.
      pointwise-yy : (sf' : SFunᵉ.State f) (y : Y)
        → (_>>=_ ⦃ Monad-M ⦄
              (tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                           (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ (inj₂ y))))
              tr-cont)
          ≡ (_>>=_ ⦃ Monad-M ⦄
              (_>>=_ ⦃ Monad-M ⦄
                  (fx-route {f = f} (sf' , inj₂ (inj₂ y)))
                  (outer-route {f = f}))
              (iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)))
      pointwise-yy sf' y = begin
        (iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))) (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , y) >>= tr-cont)
          ≡⟨ iter-equiv-2-y {X = X} {f = f} sf' y ⟩>>=⟨refl ⟩
        ((iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (fy-f f) (sf' , y) >>=
            λ (sf'' , a) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , a)) >>= tr-cont)
          ≡⟨ >>=-assoc _ ⟩
        (iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (fy-f f) (sf' , y) >>= λ (sf'' , a) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , a) >>= tr-cont)
          ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
        (iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (fy-f f) (sf' , y) >>= λ (sf'' , a) →
          tr-cont (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , a))
          ≡⟨ refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄
                (λ where (sf'' , inj₁ b) → pw-b sf'' b
                         (sf'' , inj₂ x') → pw-x sf'' x') ⟩
        (iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (fy-f f) (sf' , y) >>= λ p →
          inner-iter-route {f = f} p
            >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
          ≡˘⟨ >>=-assoc _ ⟩
        ((iter ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Iter ⦄ (fy-f f) (sf' , y) >>= inner-iter-route {f = f})
           >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
          ≡˘⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
        ((return (inj₂ (sf' , inj₂ y)) >>= outer-route {f = f})
           >>= iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b))
        ∎
        where
          open ≡-Reasoning
          pw-b : (sf'' : SFunᵉ.State f) (b : B)
            → tr-cont (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , inj₁ b)
              ≡ (_>>=_ ⦃ Monad-M ⦄
                    (inner-iter-route {f = f} (sf'' , inj₁ b))
                    (iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)))
          pw-b sf'' b = sym >>=-identityˡ
          pw-x : (sf'' : SFunᵉ.State f) (x' : X)
            → tr-cont (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , inj₂ x')
              ≡ (_>>=_ ⦃ Monad-M ⦄
                    (inner-iter-route {f = f} (sf'' , inj₂ x'))
                    (iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)))
          pw-x sf'' x' = sym >>=-identityˡ

      pointwise : (sf' : SFunᵉ.State f) (byxy : B ⊎ (X ⊎ Y))
        → (_>>=_ ⦃ Monad-M ⦄
              (tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                           (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
              tr-cont)
          ≡ (_>>=_ ⦃ Monad-M ⦄
              (_>>=_ ⦃ Monad-M ⦄
                  (fx-route {f = f} (sf' , byxy))
                  (outer-route {f = f}))
              (iter-conj-step (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)))
      pointwise sf' (inj₁ b) =
        trans >>=-identityˡ
          (sym (trans (>>=-assoc _)
                      (trans >>=-identityˡ >>=-identityˡ)))
      pointwise sf' (inj₂ (inj₁ x')) =
        trans >>=-identityˡ
          (sym (trans (>>=-assoc _)
                      (trans >>=-identityˡ >>=-identityˡ)))
      pointwise sf' (inj₂ (inj₂ y))  = pointwise-yy sf' y

  -- iter on the outer X-iter body (LHS) equals iter on outer-body-2
  -- post-composed with state-padding.
  iter-equiv-2-x :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (x : X)
    → iter (tr-step (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
           (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , x)
      ≡ (iter (outer-body-2 f) (sf , x) >>= λ (sf' , b) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
  iter-equiv-2-x {X = X} {Y = Y} {A = A} {f = f} sf x =
    iter-conjugate
      (φ₂ {X = X} {Y = Y} {A = A} {f = f}) (λ b → b)
      (outer-body-2 f)
      (tr-step (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
      (λ s₁ x' → tr-step-M-x {X = X} {Y = Y} {A = A} {f = f} s₁ x')
      sf x

  -- iter-codiag applied: iter (combine fx-f fy-f) starting at (sf, inj₁ x)
  -- equals iter (outer-body-2) (sf, x). Direct invocation of the
  -- strengthened iter-codiag axiom. The actual application would be
  -- `iter-codiag (fx-f f) (fy-f f) sf x`, but iter-codiag's RHS uses
  -- an inline pattern-lambda that's alpha-equivalent to outer-body-2.
  -- Bridged via `iter-cong` with pointwise reflexivity of the lambdas.
  iter-codiag-applied :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (x : X)
    → iter (combine (fx-f f) (fy-f f)) (sf , inj₁ x)
      ≡ iter (outer-body-2 f) (sf , x)
  iter-codiag-applied {X = X} {Y = Y} {A = A} {B = B} {f = f} sf x =
    trans (iter-codiag (fx-f f) (fy-f f) sf x)
          (iter-cong body-eq (sf , x))
    where
      body-eq : ∀ p → _ ≡ outer-body-2 f p
      body-eq (s' , x') =
        refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄
          (λ where
            (inj₁ (s'' , x'')) → refl
            (inj₂ (s'' , inj₁ a)) → refl
            (inj₂ (s'' , inj₂ y)) →
              refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄
                (λ where
                  (s''' , inj₁ a)   → refl
                  (s''' , inj₂ x'') → refl))

  -- Combine everything: iter on the outer X-iter body of LHS equals
  -- iter on tr-step f starting at (sf, inj₁ x), post-composed with
  -- state-padding. This is the iter equivalence that drives the
  -- trace-level proof of vanishing₂-ᵉ.
  iter-equiv-final :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (x : X)
    → iter (tr-step (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
           (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , x)
      ≡ (iter (tr-step f) (sf , inj₁ x) >>= λ (sf' , b) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
  iter-equiv-final {X = X} {Y = Y} {A = A} {f = f} sf x = begin
    iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
         (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , x)
      ≡⟨ iter-equiv-2-x {X = X} {Y = Y} {A = A} {f = f} sf x ⟩
    (iter (outer-body-2 f) (sf , x) >>= λ (sf' , b) →
       return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
      ≡˘⟨ iter-codiag-applied {X = X} {Y = Y} {A = A} {f = f} sf x ⟩>>=⟨refl ⟩
    (iter (combine (fx-f f) (fy-f f)) (sf , inj₁ x) >>= λ (sf' , b) →
       return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
      ≡˘⟨ iter-cong (λ z → tr-step-f-as-combine {f = f} (proj₁ z) (proj₂ z))
                    (sf , inj₁ x) ⟩>>=⟨refl ⟩
    (iter (tr-step f) (sf , inj₁ x) >>= λ (sf' , b) →
       return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
    ∎
    where open ≡-Reasoning

-- ------------------------------------------------------------------
-- vanishing₂-ᵉ: trace-level induction using iter-equiv-final.
--
-- For each input `a : A`, the LHS (nested trace of `α⇐ ∘ f ∘ α⇒`)
-- agrees with the RHS (flat trace of `f` over `X ⊎ Y`) on the next
-- output and the residual state — modulo state-padding via φ₂. The
-- function-level lemma `vanishing₂-fun` captures this; the trace-level
-- induction lifts it to lists.
-- ------------------------------------------------------------------

private
  module Vanishing₂ where
    -- The Y-case sub-lemma: starting the nested LHS iters at an
    -- f-output `inj₂ (inj₂ y)`, after one Y-iter the X-iter
    -- continues exactly as the flat RHS iter starting at `inj₂ y`.
    -- Discharged using the `iter-vanishing-2` axiom (Bloom-Esik /
    -- Hasegawa vanishing for nested iter).
    iter-equiv-final-y :
      ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
      (sf : SFunᵉ.State f) (y : Y)
      → (_>>=_ ⦃ Monad-M ⦄
            (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))
                  (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , y))
            (tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))))
        ≡ (_>>=_ ⦃ Monad-M ⦄
            (iter (tr-step f) (sf , inj₂ y))
            (λ (sf' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b)))
    iter-equiv-final-y {X = X} {Y = Y} {A = A} {B = B} {f = f} sf y = begin
        (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))
              (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , y)
            >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ iter-equiv-2-y {X = X} {f = f} sf y ⟩>>=⟨refl ⟩
        ((iter (fy-f f) (sf , y)
            >>= λ (sf' , a) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , a))
           >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ >>=-assoc _ ⟩
        (iter (fy-f f) (sf , y) >>= λ (sf' , a) →
          return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , a)
            >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
        (iter (fy-f f) (sf , y) >>= λ (sf' , a) →
          tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
                      (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , a))
          ≡⟨ refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄
                (λ where (sf' , inj₁ b) → pw-b sf' b
                         (sf' , inj₂ x) → pw-x sf' x) ⟩
        (iter (fy-f f) (sf , y) >>= λ p → padded-cont p)
          ≡⟨ refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄ pad-extract ⟩
        (iter (fy-f f) (sf , y) >>= λ p →
          vanishing-2-dispatch iter (fx-f f) (fy-f f) p
            >>= λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b))
          ≡˘⟨ >>=-assoc _ ⟩
        ((iter (fy-f f) (sf , y) >>= vanishing-2-dispatch iter (fx-f f) (fy-f f))
           >>= λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b))
          ≡⟨ iter-vanishing-2 (fx-f f) (fy-f f) sf y ⟩>>=⟨refl ⟩
        (iter (combine (fx-f f) (fy-f f)) (sf , inj₂ y)
           >>= λ (sf' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
          ≡˘⟨ iter-cong (λ z → tr-step-f-as-combine {f = f} (proj₁ z) (proj₂ z))
                        (sf , inj₂ y) ⟩>>=⟨refl ⟩
        (iter (tr-step f) (sf , inj₂ y)
           >>= λ (sf' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
        ∎
      where
        open ≡-Reasoning
        -- The state-padded version of `vanishing-2-dispatch iter (fx-f f) (fy-f f)`.
        padded-cont : SFunᵉ.State f × (B ⊎ X)
                    → M (SFunᵉ.State (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ {A} {X} {Y})) × B)
        padded-cont (sf' , inj₁ b) = return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b)
        padded-cont (sf' , inj₂ x) =
          iter (tr-step f) (sf' , inj₁ x) >>= λ (sf'' , b) →
            return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b)
        -- B case: tr-fun-cont on padded state with inj₁ b just returns.
        pw-b : (sf' : SFunᵉ.State f) (b : B)
          → tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
                        (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , inj₁ b)
            ≡ padded-cont (sf' , inj₁ b)
        pw-b sf' b = refl
        -- X case: tr-fun-cont expands to inner X-iter; rewrite via
        -- iter-equiv-final.
        pw-x : (sf' : SFunᵉ.State f) (x : X)
          → tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
                        (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , inj₂ x)
            ≡ padded-cont (sf' , inj₂ x)
        pw-x sf' x = iter-equiv-final {X = X} {Y = Y} {A = A} {f = f} sf' x
        -- Pad-extraction pointwise: `padded-cont p` equals
        -- `vanishing-2-dispatch iter (fx-f f) (fy-f f) p >>= state-pad`.
        pad-extract : (p : SFunᵉ.State f × (B ⊎ X))
          → padded-cont p
            ≡ (_>>=_ ⦃ Monad-M ⦄
                  (vanishing-2-dispatch iter (fx-f f) (fy-f f) p)
                  (λ (sf'' , b) →
                    return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b)))
        pad-extract (sf' , inj₁ b) = sym >>=-identityˡ
        pad-extract (sf' , inj₂ x) =
          iter-cong (λ z → tr-step-f-as-combine {f = f} (proj₁ z) (proj₂ z))
                    (sf' , inj₁ x) ⟩>>=⟨refl

    -- The function-level lemma: one step of LHS factors through one
    -- step of RHS via state-padding. Case analysis on f's output
    -- byxy : B ⊎ (X ⊎ Y), discharged by `>>=-identityˡ` (B case),
    -- `iter-equiv-final` (X case), `iter-equiv-final-y` (Y case).
    vanishing₂-fun :
      ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
      (sf : SFunᵉ.State f) (a : A)
      → SFunᵉ.fun (tr {X = X} (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                  (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , a)
        ≡ (_>>=_ ⦃ Monad-M ⦄
            (SFunᵉ.fun (tr {X = X ⊎ Y} f) (sf , a))
            (λ (sf' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b)))
    vanishing₂-fun {X = X} {Y = Y} {A = A} {B = B} {f = f} sf a = begin
        ((SFunᵉ.fun (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))
            (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , inj₁ (inj₁ a))
            >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
           >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ inner₂ {X = X} {Y = Y} {A = A} {f = f} sf (inj₁ (inj₁ a))
               ⟩>>=⟨refl ⟩>>=⟨refl ⟩
        (((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byxy) →
              return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy))
            >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
           >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
        ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byxy) →
            return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
              >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
           >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ >>=-assoc _ ⟩
        (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byxy) →
          (return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
             >>= tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
            >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ ⟩>>=⟨refl) ⟩
        (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byxy) →
          tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                      (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv byxy)
            >>= tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))))
          ≡⟨ refl⟩>>=⟨_ ⦃ Monad-M ⦄ ⦃ M-Laws ⦄ ⦃ M-Extensional ⦄
                (λ where (sf' , inj₁ b)         → pw-b  sf' b
                         (sf' , inj₂ (inj₁ x')) → pw-x  sf' x'
                         (sf' , inj₂ (inj₂ y))  → pw-y  sf' y) ⟩
        (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , byxy) →
          tr-fun-cont (iter (tr-step f)) (sf' , byxy)
            >>= λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b))
          ≡˘⟨ >>=-assoc _ ⟩
        ((SFunᵉ.fun f (sf , inj₁ a) >>= tr-fun-cont (iter (tr-step f)))
           >>= λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b))
        ∎
      where
        open ≡-Reasoning
        -- Pointwise inner: case-analysis on f's output byxy.
        pw-b : (sf' : SFunᵉ.State f) (b : B)
          → (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                             (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₁ b)))
                (tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))))
            ≡ (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step f)) (sf' , inj₁ b))
                (λ (sf'' , b') → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b')))
        pw-b sf' b = trans >>=-identityˡ (sym >>=-identityˡ)
        pw-x : (sf' : SFunᵉ.State f) (x' : X)
          → (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                             (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ (inj₁ x'))))
                (tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))))
            ≡ (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step f)) (sf' , inj₂ (inj₁ x')))
                (λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b)))
        pw-x sf' x' = trans >>=-identityˡ
                            (iter-equiv-final {X = X} {Y = Y} {A = A} {f = f} sf' x')
        pw-y : (sf' : SFunᵉ.State f) (y : Y)
          → (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
                             (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , α-fn-inv (inj₂ (inj₂ y))))
                (tr-fun-cont (iter (tr-step (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))))
            ≡ (_>>=_ ⦃ Monad-M ⦄
                (tr-fun-cont (iter (tr-step f)) (sf' , inj₂ (inj₂ y)))
                (λ (sf'' , b) → return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf'' , b)))
        pw-y sf' y = iter-equiv-final-y {X = X} {Y = Y} {A = A} {f = f} sf' y

  vanishing₂-trace :
    ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
    (sf : SFunᵉ.State f) (xs : List A)
    → trace (SFunᵉ.fun (tr {X = X} (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
            (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf) xs
      ≡ trace (SFunᵉ.fun (tr {X = X ⊎ Y} f)) sf xs
  vanishing₂-trace sf [] = refl
  vanishing₂-trace {X = X} {Y = Y} {A = A} {f = f} sf (a ∷ xs) = begin
    trace (SFunᵉ.fun (tr (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
          (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf) (a ∷ xs)
      ≡⟨⟩
    (SFunᵉ.fun (tr (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))))
               (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf , a)
       >>= λ (s' , b) → trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ Vanishing₂.vanishing₂-fun {f = f} sf a ⟩>>=⟨refl ⟩
    ((SFunᵉ.fun (tr f) (sf , a) >>= λ (sf' , b) →
        return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b))
       >>= λ (s' , b) → trace _ s' xs >>= λ bs → return (b ∷ bs))
      ≡⟨ >>=-assoc _ ⟩
    (SFunᵉ.fun (tr f) (sf , a) >>= λ (sf' , b) →
      (return (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf' , b)
         >>= λ (s' , b') → trace _ s' xs >>= λ bs → return (b' ∷ bs)))
      ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
    (SFunᵉ.fun (tr f) (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun (tr (tr (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ)))))
            (φ₂ {X = X} {Y = Y} {A = A} {f = f} sf') xs
        >>= λ bs → return (b ∷ bs))
      ≡⟨ refl⟩>>=⟨ (λ (sf' , b) →
            vanishing₂-trace {f = f} sf' xs ⟩>>=⟨refl) ⟩
    (SFunᵉ.fun (tr f) (sf , a) >>= λ (sf' , b) →
      trace (SFunᵉ.fun (tr f)) sf' xs >>= λ bs → return (b ∷ bs))
      ≡⟨⟩
    trace (SFunᵉ.fun (tr f)) sf (a ∷ xs)
    ∎
    where open ≡-Reasoning

vanishing₂-ᵉ : ∀ {X Y A B} {f : SFunᵉ (A ⊎ (X ⊎ Y)) (B ⊎ (X ⊎ Y))}
  → tr {X = X} (tr {X = Y} (α⇐ᵉ ∘ᵉ (f ∘ᵉ α⇒ᵉ))) ≈ᵉ tr {X = X ⊎ Y} f
vanishing₂-ᵉ {f = f} xs = vanishing₂-trace {f = f} (SFunᵉ.init f) xs

SFunᵉ-traced : Traced SFunᵉ-monoidal
SFunᵉ-traced = record
  { symmetric   = symmetric-ᵉ
  ; trace       = tr
  ; vanishing₁  = vanishing₁-ᵉ
  ; vanishing₂  = vanishing₂-ᵉ
  ; superposing = superposing-ᵉ
  ; yanking     = yanking-ᵉ
  }

------------------------------------------------------------------------
-- Trace naturality (right): tr f ∘ᵉ h ≈ᵉ tr (f ∘ᵉ (h ⊗ᵉ idᵉ)).
--
-- The pre-composed `h` runs once per external input, before the loop;
-- inside the loop the (h ⊗ᵉ idᵉ)-layer is the identity, so the loops
-- coincide via `iter-conjugate` (state padded by h's final state).

private
  module _ {A' A B X : Type} (f : SFunᵉ (A ⊎ X) (B ⊎ X)) (h : SFunᵉ A' A) where

    -- State padding: LHS state (Sf × Sh) to RHS state (Sf × (Sh × ⊤)).
    ∘ʳ-st : SFunᵉ.State f × SFunᵉ.State h → SFunᵉ.State (f ∘ᵉ (h ⊗ᵉ idᵉ))
    ∘ʳ-st (sf , sh) = sf , (sh , tt)

    -- The composed body on a loop input: the (h ⊗ᵉ idᵉ)-layer is pure.
    ∘ʳ-body-loop : ∀ sf sh (x : X)
      → SFunᵉ.fun (f ∘ᵉ (h ⊗ᵉ idᵉ)) ((sf , (sh , tt)) , inj₂ x)
        ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
            return ((sf' , (sh , tt)) , w))
    ∘ʳ-body-loop sf sh x = begin
      (SFunᵉ.fun (h ⊗ᵉ idᵉ) ((sh , tt) , inj₂ x) >>= λ (sht' , w₀) →
        SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sht') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      (return ((sh , tt) , inj₂ x) >>= λ (sht' , w₀) →
        SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sht') , u))
        ≡⟨ >>=-identityˡ ⟩
      (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , u) →
        return ((sf' , (sh , tt)) , u)) ∎
      where open ≡-Reasoning

    -- The composed body on the entry input: h runs, then f.
    ∘ʳ-body-entry : ∀ sf sh (a' : A')
      → SFunᵉ.fun (f ∘ᵉ (h ⊗ᵉ idᵉ)) ((sf , (sh , tt)) , inj₁ a')
        ≡ (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              return ((sf' , (sh' , tt)) , w))
    ∘ʳ-body-entry sf sh a' = begin
      ((SFunᵉ.fun h (sh , a') >>= λ (sh' , a) → return ((sh' , tt) , inj₁ a))
        >>= λ (sht' , w₀) →
          SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sht') , u))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
        return ((sh' , tt) , inj₁ a) >>= λ (sht' , w₀) →
          SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sht') , u))
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
        SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , u) →
          return ((sf' , (sh' , tt)) , u)) ∎
      where open ≡-Reasoning

    -- Premise of iter-conjugate: the composed body's tr-step at padded
    -- state is f's tr-step, with output routed through iter-conj-step.
    ∘ʳ-premise : ∀ sh sf (x : X)
      → tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)) ((sf , (sh , tt)) , x)
        ≡ (tr-step f (sf , x) >>=
            iter-conj-step (λ sf' → ∘ʳ-st (sf' , sh)) (λ b → b))
    ∘ʳ-premise sh sf x = begin
      (SFunᵉ.fun (f ∘ᵉ (h ⊗ᵉ idᵉ)) ((sf , (sh , tt)) , inj₂ x) >>= tr-cont)
        ≡⟨ ∘ʳ-body-loop sf sh x ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
         return ((sf' , (sh , tt)) , w)) >>= tr-cont)
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
        return ((sf' , (sh , tt)) , w) >>= tr-cont)
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
        tr-cont ((sf' , (sh , tt)) , w))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → pointwise sf' w) ⟩
      (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
        tr-cont (sf' , w) >>=
          iter-conj-step (λ sf'' → ∘ʳ-st (sf'' , sh)) (λ b → b))
        ≡˘⟨ >>=-assoc _ ⟩
      ((SFunᵉ.fun f (sf , inj₂ x) >>= tr-cont)
        >>= iter-conj-step (λ sf'' → ∘ʳ-st (sf'' , sh)) (λ b → b)) ∎
      where
        open ≡-Reasoning
        pointwise : ∀ sf' (w : B ⊎ X)
          → tr-cont ((sf' , (sh , tt)) , w)
            ≡ (tr-cont (sf' , w) >>=
                iter-conj-step (λ sf'' → ∘ʳ-st (sf'' , sh)) (λ b → b))
        pointwise sf' (inj₁ b)  = sym >>=-identityˡ
        pointwise sf' (inj₂ x') = sym >>=-identityˡ

    -- The loops coincide modulo state padding.
    ∘ʳ-iter-equiv : ∀ sh sf (x : X)
      → iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))) ((sf , (sh , tt)) , x)
        ≡ (iter (tr-step f) (sf , x) >>= λ (sf' , b) →
            return (∘ʳ-st (sf' , sh) , b))
    ∘ʳ-iter-equiv sh sf x =
      iter-conjugate
        (λ sf' → ∘ʳ-st (sf' , sh)) (λ b → b)
        (tr-step f)
        (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)))
        (λ s₁ x' → ∘ʳ-premise sh s₁ x')
        sf x

    -- The fun-level simulation hypothesis.
    ∘ʳ-hyp : ∀ s (a' : A')
      → (SFunᵉ.fun (tr {X = X} f ∘ᵉ h) (s , a') >>= λ (s' , b) →
          return (∘ʳ-st s' , b))
        ≡ SFunᵉ.fun (tr {X = X} (f ∘ᵉ (h ⊗ᵉ idᵉ))) (∘ʳ-st s , a')
    ∘ʳ-hyp (sf , sh) a' = trans lhs-chain (sym rhs-chain)
      where
        open ≡-Reasoning

        branch : ∀ sh' sf' (w : B ⊎ X)
          → (tr-fun-cont (iter (tr-step f)) (sf' , w) >>= λ (sf'' , b) →
              return ((sf'' , (sh' , tt)) , b))
            ≡ tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))))
                          ((sf' , (sh' , tt)) , w)
        branch sh' sf' (inj₁ b) = >>=-identityˡ
        branch sh' sf' (inj₂ x) = sym (∘ʳ-iter-equiv sh' sf' x)

        lhs-chain :
          (SFunᵉ.fun (tr {X = X} f ∘ᵉ h) ((sf , sh) , a') >>= λ (s' , b) →
            return (∘ʳ-st s' , b))
          ≡ (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
              SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
                tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))))
                            ((sf' , (sh' , tt)) , w))
        lhs-chain = begin
          ((SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
             SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
               return ((sf' , sh') , b))
            >>= λ (s' , b) → return (∘ʳ-st s' , b))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            (SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
              return ((sf' , sh') , b))
              >>= λ (s' , b) → return (∘ʳ-st s' , b))
            ≡⟨ refl⟩>>=⟨ (λ (sh' , a) → >>=-assoc _) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
              return ((sf' , sh') , b) >>= λ (s' , b') → return (∘ʳ-st s' , b'))
            ≡⟨ refl⟩>>=⟨ (λ (sh' , a) → refl⟩>>=⟨ (λ (sf' , b) → >>=-identityˡ)) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
              return ((sf' , (sh' , tt)) , b))
            ≡⟨ refl⟩>>=⟨ (λ (sh' , a) → >>=-assoc _) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              tr-fun-cont (iter (tr-step f)) (sf' , w) >>= λ (sf'' , b) →
                return ((sf'' , (sh' , tt)) , b))
            ≡⟨ refl⟩>>=⟨ (λ (sh' , a) → refl⟩>>=⟨ (λ (sf' , w) → branch sh' sf' w)) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))))
                          ((sf' , (sh' , tt)) , w)) ∎

        rhs-chain :
          SFunᵉ.fun (tr {X = X} (f ∘ᵉ (h ⊗ᵉ idᵉ))) ((sf , (sh , tt)) , a')
          ≡ (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
              SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
                tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))))
                            ((sf' , (sh' , tt)) , w))
        rhs-chain = begin
          (SFunᵉ.fun (f ∘ᵉ (h ⊗ᵉ idᵉ)) ((sf , (sh , tt)) , inj₁ a')
            >>= tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)))))
            ≡⟨ ∘ʳ-body-entry sf sh a' ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
             SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
               return ((sf' , (sh' , tt)) , w))
            >>= tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)))))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              return ((sf' , (sh' , tt)) , w))
              >>= tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)))))
            ≡⟨ refl⟩>>=⟨ (λ (sh' , a) → >>=-assoc _) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              return ((sf' , (sh' , tt)) , w)
                >>= tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ)))))
            ≡⟨ refl⟩>>=⟨ (λ _ → refl⟩>>=⟨ (λ _ → >>=-identityˡ)) ⟩
          (SFunᵉ.fun h (sh , a') >>= λ (sh' , a) →
            SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
              tr-fun-cont (iter (tr-step (f ∘ᵉ (h ⊗ᵉ idᵉ))))
                          ((sf' , (sh' , tt)) , w)) ∎

trace-∘ʳ-ᵉ : ∀ {X A A' B} {f : SFunᵉ (A ⊎ X) (B ⊎ X)} {h : SFunᵉ A' A}
           → (tr {X = X} f ∘ᵉ h) ≈ᵉ tr {X = X} (f ∘ᵉ (h ⊗ᵉ idᵉ))
trace-∘ʳ-ᵉ {f = f} {h} xs =
  trace-sim (∘ʳ-st f h) (∘ʳ-hyp f h)
            (SFunᵉ.init f , SFunᵉ.init h) xs

------------------------------------------------------------------------
-- Trace naturality (left): g ∘ᵉ tr f ≈ᵉ tr ((g ⊗ᵉ idᵉ) ∘ᵉ f).
--
-- Here `g` runs once per external input — *after* the loop on the LHS,
-- but *inside* the final loop iteration on the RHS. The bridge works
-- in three stages over an intermediate loop on state (Sg × Sf):
--   (iii) pad f's loop with a constant g-state   (iter-conjugate)
--   (ii)  move g's exit-effect into the loop body (iter-nat)
--   (i)   repackage the state to the RHS's shape  (iter-conjugate)

private
  module _ {A B B' X : Type} (g : SFunᵉ B B') (f : SFunᵉ (A ⊎ X) (B ⊎ X)) where

    -- State repackaging: LHS state (Sg × Sf) to RHS state ((Sg × ⊤) × Sf).
    ∘ˡ-st : SFunᵉ.State g × SFunᵉ.State f → SFunᵉ.State ((g ⊗ᵉ idᵉ) ∘ᵉ f)
    ∘ˡ-st (sg , sf) = (sg , tt) , sf

    -- Intermediate loop bodies on the carrier (Sg × Sf) × X.
    ∘ˡ-pure-route : (sg : SFunᵉ.State g)
      → (SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B)
      → M (((SFunᵉ.State g × SFunᵉ.State f) × X) ⊎
            ((SFunᵉ.State g × SFunᵉ.State f) × B))
    ∘ˡ-pure-route sg (inj₁ (sf' , x')) = return (inj₁ ((sg , sf') , x'))
    ∘ˡ-pure-route sg (inj₂ (sf' , b))  = return (inj₂ ((sg , sf') , b))

    ∘ˡ-pure-step : ((SFunᵉ.State g × SFunᵉ.State f) × X)
      → M ((((SFunᵉ.State g × SFunᵉ.State f) × X)) ⊎
            ((SFunᵉ.State g × SFunᵉ.State f) × B))
    ∘ˡ-pure-step ((sg , sf) , x) = tr-step f (sf , x) >>= ∘ˡ-pure-route sg

    ∘ˡ-mid-route : (sg : SFunᵉ.State g)
      → (SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B)
      → M (((SFunᵉ.State g × SFunᵉ.State f) × X) ⊎
            ((SFunᵉ.State g × SFunᵉ.State f) × B'))
    ∘ˡ-mid-route sg (inj₁ (sf' , x')) = return (inj₁ ((sg , sf') , x'))
    ∘ˡ-mid-route sg (inj₂ (sf' , b))  =
      SFunᵉ.fun g (sg , b) >>= λ (sg' , b') → return (inj₂ ((sg' , sf') , b'))

    ∘ˡ-mid-step : ((SFunᵉ.State g × SFunᵉ.State f) × X)
      → M (((SFunᵉ.State g × SFunᵉ.State f) × X) ⊎
            ((SFunᵉ.State g × SFunᵉ.State f) × B'))
    ∘ˡ-mid-step ((sg , sf) , x) = tr-step f (sf , x) >>= ∘ˡ-mid-route sg

    -- The exit-effect, as iter-nat's post-processing.
    ∘ˡ-exit : ((SFunᵉ.State g × SFunᵉ.State f) × B)
      → M ((SFunᵉ.State g × SFunᵉ.State f) × B')
    ∘ˡ-exit ((sg , sf') , b) =
      SFunᵉ.fun g (sg , b) >>= λ (sg' , b') → return ((sg' , sf') , b')

    -- (iii) Padding f's loop with a constant g-state.
    ∘ˡ-stage₃ : ∀ sg sf (x : X)
      → iter ∘ˡ-pure-step ((sg , sf) , x)
        ≡ (iter (tr-step f) (sf , x) >>= λ (sf' , b) → return ((sg , sf') , b))
    ∘ˡ-stage₃ sg sf x =
      iter-conjugate
        (λ sf' → (sg , sf')) (λ b → b)
        (tr-step f) ∘ˡ-pure-step
        (λ s₁ x' → refl⟩>>=⟨ (λ where
          (inj₁ (sf' , x'')) → refl
          (inj₂ (sf' , b))   → refl))
        sf x

    -- (ii) Moving g's exit-effect into the loop body.
    ∘ˡ-stage₂ : ∀ sg sf (x : X)
      → iter ∘ˡ-mid-step ((sg , sf) , x)
        ≡ (iter ∘ˡ-pure-step ((sg , sf) , x) >>= ∘ˡ-exit)
    ∘ˡ-stage₂ sg sf x =
      trans
        (iter-cong
          (λ ((sg₀ , sf₀) , x₀) →
            trans (refl⟩>>=⟨ (λ where
              (inj₁ (sf' , x')) → sym >>=-identityˡ
              (inj₂ (sf' , b))  →
                sym (trans >>=-identityˡ
                      (trans (>>=-assoc _)
                             (refl⟩>>=⟨ (λ _ → >>=-identityˡ))))))
              (sym (>>=-assoc _)))
          ((sg , sf) , x))
        (sym (iter-nat ∘ˡ-pure-step ∘ˡ-exit ((sg , sf) , x)))

    -- (i) Premise: the RHS body's tr-step at repackaged state is the
    -- intermediate body routed through iter-conj-step.
    ∘ˡ-premise : ∀ sg sf (x : X)
      → tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f) (((sg , tt) , sf) , x)
        ≡ (∘ˡ-mid-step ((sg , sf) , x) >>= iter-conj-step ∘ˡ-st (λ b → b))
    ∘ˡ-premise sg sf x = trans lhs-chain (sym rhs-chain)
      where
        open ≡-Reasoning

        common : SFunᵉ.State f → B ⊎ X
               → M ((((SFunᵉ.State g × ⊤) × SFunᵉ.State f) × X) ⊎
                     (((SFunᵉ.State g × ⊤) × SFunᵉ.State f) × B'))
        common sf' (inj₁ b)  = SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
                                 return (inj₂ (((sg' , tt) , sf') , b₁))
        common sf' (inj₂ x') = return (inj₁ (((sg , tt) , sf') , x'))

        lhs-branch : ∀ sf' (w : B ⊎ X)
          → ((SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
               return ((sgt' , sf') , u)) >>= tr-cont)
            ≡ common sf' w
        lhs-branch sf' (inj₁ b) = begin
          (((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) → return ((sg' , tt) , inj₁ b₁))
            >>= λ (sgt' , u) → return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return ((sg' , tt) , inj₁ b₁) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ (refl⟩>>=⟨ (λ _ → >>=-identityˡ)) ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (((sg' , tt) , sf') , inj₁ b₁)) >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (((sg' , tt) , sf') , inj₁ b₁) >>= tr-cont)
            ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (inj₂ (((sg' , tt) , sf') , b₁))) ∎
        lhs-branch sf' (inj₂ x') = begin
          (((return (tt , x') >>= λ (st' , d) → return ((sg , st') , inj₂ d))
            >>= λ (sgt' , u) → return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
          ((return ((sg , tt) , inj₂ x') >>= λ (sgt' , u) →
            return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
          (return (((sg , tt) , sf') , inj₂ x') >>= tr-cont)
            ≡⟨ >>=-identityˡ ⟩
          return (inj₁ (((sg , tt) , sf') , x')) ∎

        rhs-branch : ∀ sf' (w : B ⊎ X)
          → ((tr-cont (sf' , w) >>= ∘ˡ-mid-route sg)
              >>= iter-conj-step ∘ˡ-st (λ b → b))
            ≡ common sf' w
        rhs-branch sf' (inj₁ b) = begin
          ((tr-cont (sf' , inj₁ b) >>= ∘ˡ-mid-route sg)
            >>= iter-conj-step ∘ˡ-st (λ b₀ → b₀))
            ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun g (sg , b) >>= λ (sg' , b') → return (inj₂ ((sg' , sf') , b')))
            >>= iter-conj-step ∘ˡ-st (λ b₀ → b₀))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
            return (inj₂ ((sg' , sf') , b')) >>= iter-conj-step ∘ˡ-st (λ b₀ → b₀))
            ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
            return (inj₂ (((sg' , tt) , sf') , b'))) ∎
        rhs-branch sf' (inj₂ x') = begin
          ((tr-cont (sf' , inj₂ x') >>= ∘ˡ-mid-route sg)
            >>= iter-conj-step ∘ˡ-st (λ b₀ → b₀))
            ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
          (return (inj₁ ((sg , sf') , x')) >>= iter-conj-step ∘ˡ-st (λ b₀ → b₀))
            ≡⟨ >>=-identityˡ ⟩
          return (inj₁ (((sg , tt) , sf') , x')) ∎

        lhs-chain :
          tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f) (((sg , tt) , sf) , x)
          ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) → common sf' w)
        lhs-chain = begin
          ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
            SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
            (SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u)) >>= tr-cont)
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → lhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) → common sf' w) ∎

        rhs-chain :
          (∘ˡ-mid-step ((sg , sf) , x) >>= iter-conj-step ∘ˡ-st (λ b → b))
          ≡ (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) → common sf' w)
        rhs-chain = begin
          (((SFunᵉ.fun f (sf , inj₂ x) >>= tr-cont) >>= ∘ˡ-mid-route sg)
            >>= iter-conj-step ∘ˡ-st (λ b → b))
            ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
             tr-cont (sf' , w) >>= ∘ˡ-mid-route sg)
            >>= iter-conj-step ∘ˡ-st (λ b → b))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) →
            (tr-cont (sf' , w) >>= ∘ˡ-mid-route sg)
              >>= iter-conj-step ∘ˡ-st (λ b → b))
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → rhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₂ x) >>= λ (sf' , w) → common sf' w) ∎

    -- (i) applied.
    ∘ˡ-stage₁ : ∀ sg sf (x : X)
      → iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (((sg , tt) , sf) , x)
        ≡ (iter ∘ˡ-mid-step ((sg , sf) , x) >>= λ (s' , b') →
            return (∘ˡ-st s' , b'))
    ∘ˡ-stage₁ sg sf x =
      iter-conjugate
        ∘ˡ-st (λ b → b)
        ∘ˡ-mid-step
        (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))
        (λ (sg₀ , sf₀) x' → ∘ˡ-premise sg₀ sf₀ x')
        (sg , sf) x

    -- The combined bridge: the RHS loop equals f's loop followed by g.
    ∘ˡ-bridge : ∀ sg sf (x : X)
      → iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (((sg , tt) , sf) , x)
        ≡ (iter (tr-step f) (sf , x) >>= λ (sf' , b) →
            SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
              return (((sg' , tt) , sf') , b'))
    ∘ˡ-bridge sg sf x = begin
      iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (((sg , tt) , sf) , x)
        ≡⟨ ∘ˡ-stage₁ sg sf x ⟩
      (iter ∘ˡ-mid-step ((sg , sf) , x) >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ ∘ˡ-stage₂ sg sf x ⟩>>=⟨refl ⟩
      ((iter ∘ˡ-pure-step ((sg , sf) , x) >>= ∘ˡ-exit)
        >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ (∘ˡ-stage₃ sg sf x ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
      (((iter (tr-step f) (sf , x) >>= λ (sf' , b) → return ((sg , sf') , b))
         >>= ∘ˡ-exit)
        >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      ((iter (tr-step f) (sf , x) >>= λ (sf' , b) →
         return ((sg , sf') , b) >>= ∘ˡ-exit)
        >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ (refl⟩>>=⟨ (λ _ → >>=-identityˡ)) ⟩>>=⟨refl ⟩
      ((iter (tr-step f) (sf , x) >>= λ (sf' , b) → ∘ˡ-exit ((sg , sf') , b))
        >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ >>=-assoc _ ⟩
      (iter (tr-step f) (sf , x) >>= λ (sf' , b) →
        ∘ˡ-exit ((sg , sf') , b) >>= λ (s' , b') → return (∘ˡ-st s' , b'))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , b) →
             trans (>>=-assoc _) (refl⟩>>=⟨ (λ _ → >>=-identityˡ))) ⟩
      (iter (tr-step f) (sf , x) >>= λ (sf' , b) →
        SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
          return (((sg' , tt) , sf') , b')) ∎
      where open ≡-Reasoning

    -- The fun-level simulation hypothesis.
    ∘ˡ-hyp : ∀ s (a : A)
      → (SFunᵉ.fun (g ∘ᵉ tr {X = X} f) (s , a) >>= λ (s' , b) →
          return (∘ˡ-st s' , b))
        ≡ SFunᵉ.fun (tr {X = X} ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (∘ˡ-st s , a)
    ∘ˡ-hyp (sg , sf) a = trans lhs-chain (sym rhs-chain)
      where
        open ≡-Reasoning

        common : SFunᵉ.State f → B ⊎ X
               → M (((SFunᵉ.State g × ⊤) × SFunᵉ.State f) × B')
        common sf' (inj₁ b) = SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
                                return (((sg' , tt) , sf') , b')
        common sf' (inj₂ x) = iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))
                                   (((sg , tt) , sf') , x)

        lhs-branch : ∀ sf' (w : B ⊎ X)
          → (tr-fun-cont (iter (tr-step f)) (sf' , w) >>= λ (sf'' , b) →
              SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
                return (((sg' , tt) , sf'') , b'))
            ≡ common sf' w
        lhs-branch sf' (inj₁ b) = >>=-identityˡ
        lhs-branch sf' (inj₂ x) = sym (∘ˡ-bridge sg sf' x)

        lhs-chain :
          (SFunᵉ.fun (g ∘ᵉ tr {X = X} f) ((sg , sf) , a) >>= λ (s' , b) →
            return (∘ˡ-st s' , b))
          ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) → common sf' w)
        lhs-chain = begin
          ((SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
             SFunᵉ.fun g (sg , b) >>= λ (sg' , b') → return ((sg' , sf') , b'))
            >>= λ (s' , b) → return (∘ˡ-st s' , b))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
            (SFunᵉ.fun g (sg , b) >>= λ (sg' , b') → return ((sg' , sf') , b'))
              >>= λ (s' , b₁) → return (∘ˡ-st s' , b₁))
            ≡⟨ refl⟩>>=⟨ (λ (sf' , b) →
                 trans (>>=-assoc _) (refl⟩>>=⟨ (λ _ → >>=-identityˡ))) ⟩
          (SFunᵉ.fun (tr {X = X} f) (sf , a) >>= λ (sf' , b) →
            SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
              return (((sg' , tt) , sf') , b'))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
            tr-fun-cont (iter (tr-step f)) (sf' , w) >>= λ (sf'' , b) →
              SFunᵉ.fun g (sg , b) >>= λ (sg' , b') →
                return (((sg' , tt) , sf'') , b'))
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → lhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) → common sf' w) ∎

        rhs-branch : ∀ sf' (w : B ⊎ X)
          → ((SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
               return ((sgt' , sf') , u))
              >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡ common sf' w
        rhs-branch sf' (inj₁ b) = begin
          (((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) → return ((sg' , tt) , inj₁ b₁))
            >>= λ (sgt' , u) → return ((sgt' , sf') , u))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return ((sg' , tt) , inj₁ b₁) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ (refl⟩>>=⟨ (λ _ → >>=-identityˡ)) ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (((sg' , tt) , sf') , inj₁ b₁))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (((sg' , tt) , sf') , inj₁ b₁)
              >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
          (SFunᵉ.fun g (sg , b) >>= λ (sg' , b₁) →
            return (((sg' , tt) , sf') , b₁)) ∎
        rhs-branch sf' (inj₂ x) = begin
          (((return (tt , x) >>= λ (st' , d) → return ((sg , st') , inj₂ d))
            >>= λ (sgt' , u) → return ((sgt' , sf') , u))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
          ((return ((sg , tt) , inj₂ x) >>= λ (sgt' , u) →
            return ((sgt' , sf') , u))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
          (return (((sg , tt) , sf') , inj₂ x)
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ >>=-identityˡ ⟩
          iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (((sg , tt) , sf') , x) ∎

        rhs-chain :
          SFunᵉ.fun (tr {X = X} ((g ⊗ᵉ idᵉ) ∘ᵉ f)) (((sg , tt) , sf) , a)
          ≡ (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) → common sf' w)
        rhs-chain = begin
          ((SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
            SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u))
            >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) →
            (SFunᵉ.fun (g ⊗ᵉ idᵉ) ((sg , tt) , w) >>= λ (sgt' , u) →
              return ((sgt' , sf') , u))
              >>= tr-fun-cont (iter (tr-step ((g ⊗ᵉ idᵉ) ∘ᵉ f))))
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → rhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₁ a) >>= λ (sf' , w) → common sf' w) ∎

trace-∘ˡ-ᵉ : ∀ {X A B B' : Type} {g : SFunᵉ B B'} {f : SFunᵉ (A ⊎ X) (B ⊎ X)}
           → (g ∘ᵉ tr {X = X} f) ≈ᵉ tr {X = X} ((g ⊗ᵉ idᵉ) ∘ᵉ f)
trace-∘ˡ-ᵉ {g = g} {f} xs =
  trace-sim (∘ˡ-st g f) (∘ˡ-hyp g f)
            (SFunᵉ.init g , SFunᵉ.init f) xs

------------------------------------------------------------------------
-- Trace exchange (Fubini):
--   tr_X (tr_Y f) ≈ᵉ tr_Y (tr_X (β ∘ᵉ (f ∘ᵉ β)))
-- where β = α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ) swaps the last two factors.
--
-- Strategy: both nestings reduce to a single flat iter over the
-- combined loop X ⊎ Y (body `combine comm-fx (tr-step f)`), via
-- iter-codiag / iter-codiag-y for the loops entered on the outer
-- channel and iter-vanishing-2 / iter-vanishing-2-x for the loops
-- entered on the inner channel. The β-layers of the RHS are pure and
-- only contribute constant state padding (`iter-conjugate`).

private
  module _ {A B X Y : Type} (f : SFunᵉ ((A ⊎ X) ⊎ Y) ((B ⊎ X) ⊎ Y)) where

    private
      βᵉ : ∀ {P Q R : Type} → SFunᵉ ((P ⊎ Q) ⊎ R) ((P ⊎ R) ⊎ Q)
      βᵉ = α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ)

      g₀ : SFunᵉ ((A ⊎ Y) ⊎ X) ((B ⊎ Y) ⊎ X)
      g₀ = βᵉ ∘ᵉ (f ∘ᵉ βᵉ)

    -- Value-level behaviour of β.
    β-route : {P Q R : Type} → (P ⊎ Q) ⊎ R → (P ⊎ R) ⊎ Q
    β-route (inj₁ (inj₁ p)) = inj₁ (inj₁ p)
    β-route (inj₁ (inj₂ q)) = inj₂ q
    β-route (inj₂ r)        = inj₁ (inj₂ r)

    β-char : ∀ {P Q R : Type} s (z : (P ⊎ Q) ⊎ R)
           → SFunᵉ.fun (βᵉ {P} {Q} {R}) (s , z) ≡ return (s , β-route z)
    β-char (s⇐ , ((sid , sσ) , s⇒)) (inj₁ (inj₁ p)) = begin
      ((return (tt , inj₁ p) >>= λ (s⇒' , w₀) →
         SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , w₀) >>= λ (sidσ' , u) →
           return ((sidσ' , s⇒') , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , inj₁ p) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
      ((return ((tt , sσ) , inj₁ p) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      (return (((tt , sσ) , tt) , inj₁ p)
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩
      (SFunᵉ.fun α⇐ᵉ (s⇐ , inj₁ p) >>= λ (s⇐' , u) →
        return ((s⇐' , ((tt , sσ) , tt)) , u))
        ≡⟨ >>=-identityˡ ⟩
      return ((tt , ((tt , sσ) , tt)) , inj₁ (inj₁ p)) ∎
      where open ≡-Reasoning
    β-char (s⇐ , ((sid , sσ) , s⇒)) (inj₁ (inj₂ q)) = begin
      ((return (tt , inj₂ (inj₁ q)) >>= λ (s⇒' , w₀) →
         SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , w₀) >>= λ (sidσ' , u) →
           return ((sidσ' , s⇒') , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , inj₂ (inj₁ q)) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
      ((return ((sid , tt) , inj₂ (inj₂ q)) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      (return (((sid , tt) , tt) , inj₂ (inj₂ q))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩
      (SFunᵉ.fun α⇐ᵉ (s⇐ , inj₂ (inj₂ q)) >>= λ (s⇐' , u) →
        return ((s⇐' , ((sid , tt) , tt)) , u))
        ≡⟨ >>=-identityˡ ⟩
      return ((tt , ((sid , tt) , tt)) , inj₂ q) ∎
      where open ≡-Reasoning
    β-char (s⇐ , ((sid , sσ) , s⇒)) (inj₂ r) = begin
      ((return (tt , inj₂ (inj₂ r)) >>= λ (s⇒' , w₀) →
         SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , w₀) >>= λ (sidσ' , u) →
           return ((sidσ' , s⇒') , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun (idᵉ ⊗ᵉ σᵉ) ((sid , sσ) , inj₂ (inj₂ r)) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ (>>=-identityˡ ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
      ((return ((sid , tt) , inj₂ (inj₁ r)) >>= λ (sidσ' , u) →
         return ((sidσ' , tt) , u))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
      (return (((sid , tt) , tt) , inj₂ (inj₁ r))
        >>= λ (sR' , w₁) → SFunᵉ.fun α⇐ᵉ (s⇐ , w₁) >>= λ (s⇐' , u) →
          return ((s⇐' , sR') , u))
        ≡⟨ >>=-identityˡ ⟩
      (SFunᵉ.fun α⇐ᵉ (s⇐ , inj₂ (inj₁ r)) >>= λ (s⇐' , u) →
        return ((s⇐' , ((sid , tt) , tt)) , u))
        ≡⟨ >>=-identityˡ ⟩
      return ((tt , ((sid , tt) , tt)) , inj₁ (inj₂ r)) ∎
      where open ≡-Reasoning

    -- g₀'s pointwise behaviour: f conjugated by the (pure) β's.
    g₀-char : ∀ sβ₁ sf sβ₂ (z : (A ⊎ Y) ⊎ X)
      → SFunᵉ.fun g₀ ((sβ₁ , (sf , sβ₂)) , z)
        ≡ (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
            return ((sβ₁ , (sf' , sβ₂)) , β-route w))
    g₀-char sβ₁ sf sβ₂ z = begin
      (SFunᵉ.fun (f ∘ᵉ βᵉ) ((sf , sβ₂) , z) >>= λ (sR' , w₁) →
        SFunᵉ.fun βᵉ (sβ₁ , w₁) >>= λ (sβ₁' , u) → return ((sβ₁' , sR') , u))
        ≡⟨ inner ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
         return ((sf' , sβ₂) , w))
        >>= λ (sR' , w₁) →
          SFunᵉ.fun βᵉ (sβ₁ , w₁) >>= λ (sβ₁' , u) → return ((sβ₁' , sR') , u))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
        return ((sf' , sβ₂) , w) >>= λ (sR' , w₁) →
          SFunᵉ.fun βᵉ (sβ₁ , w₁) >>= λ (sβ₁' , u) → return ((sβ₁' , sR') , u))
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
        SFunᵉ.fun βᵉ (sβ₁ , w) >>= λ (sβ₁' , u) →
          return ((sβ₁' , (sf' , sβ₂)) , u))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → β-char sβ₁ w ⟩>>=⟨refl) ⟩
      (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
        return (sβ₁ , β-route w) >>= λ (sβ₁' , u) →
          return ((sβ₁' , (sf' , sβ₂)) , u))
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
        return ((sβ₁ , (sf' , sβ₂)) , β-route w)) ∎
      where
        open ≡-Reasoning
        inner : SFunᵉ.fun (f ∘ᵉ βᵉ) ((sf , sβ₂) , z)
              ≡ (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , w) →
                  return ((sf' , sβ₂) , w))
        inner = begin
          (SFunᵉ.fun βᵉ (sβ₂ , z) >>= λ (sβ₂' , w₀) →
            SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sβ₂') , u))
            ≡⟨ β-char sβ₂ z ⟩>>=⟨refl ⟩
          (return (sβ₂ , β-route z) >>= λ (sβ₂' , w₀) →
            SFunᵉ.fun f (sf , w₀) >>= λ (sf' , u) → return ((sf' , sβ₂') , u))
            ≡⟨ >>=-identityˡ ⟩
          (SFunᵉ.fun f (sf , β-route z) >>= λ (sf' , u) →
            return ((sf' , sβ₂) , u)) ∎

    -- The X-channel loop body derived from f (the Y-channel one is
    -- literally `tr-step f`).
    comm-fx-route : SFunᵉ.State f × ((B ⊎ X) ⊎ Y)
                  → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y)))
    comm-fx-route (sf' , inj₁ (inj₁ b))  = return (inj₂ (sf' , inj₁ b))
    comm-fx-route (sf' , inj₁ (inj₂ x')) = return (inj₁ (sf' , x'))
    comm-fx-route (sf' , inj₂ y)         = return (inj₂ (sf' , inj₂ y))

    comm-fx : (SFunᵉ.State f × X)
            → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y)))
    comm-fx (sf , x) = SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= comm-fx-route

    -- The common flat-loop entry continuation.
    comm-entry : SFunᵉ.State f × ((B ⊎ X) ⊎ Y) → M (SFunᵉ.State f × B)
    comm-entry (sf' , inj₁ (inj₁ b)) = return (sf' , b)
    comm-entry (sf' , inj₁ (inj₂ x)) =
      iter (combine comm-fx (tr-step f)) (sf' , inj₁ x)
    comm-entry (sf' , inj₂ y)        =
      iter (combine comm-fx (tr-step f)) (sf' , inj₂ y)

    -- State padding for the RHS (the β-layers carry only ⊤'s).
    comm-pad : SFunᵉ.State f → SFunᵉ.State g₀
    comm-pad sf = (tt , ((tt , tt) , tt)) , (sf , (tt , ((tt , tt) , tt)))

    comm-padloop : SFunᵉ.State f × (B ⊎ Y) → M (SFunᵉ.State g₀ × (B ⊎ Y))
    comm-padloop (sf , w) = return (comm-pad sf , w)

    comm-padexit : SFunᵉ.State f × B → M (SFunᵉ.State g₀ × B)
    comm-padexit (sf , b) = return (comm-pad sf , b)

    -- ────────────────────────────────────────────────────────────────
    -- LHS: tr_X (tr_Y f).

    comm-outer-route : (SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × (B ⊎ Y))
                     → M ((SFunᵉ.State f × X) ⊎ (SFunᵉ.State f × B))
    comm-outer-route (inj₁ p)              = return (inj₁ p)
    comm-outer-route (inj₂ (sf' , inj₁ b)) = return (inj₂ (sf' , b))
    comm-outer-route (inj₂ (sf' , inj₂ y)) =
      iter (tr-step f) (sf' , y) >>= tr-cont

    L-outer-char : ∀ p
      → tr-step (tr {X = Y} f) p ≡ (comm-fx p >>= comm-outer-route)
    L-outer-char (sf , x) = begin
      ((SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= tr-fun-cont (iter (tr-step f)))
        >>= tr-cont)
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
        tr-fun-cont (iter (tr-step f)) (sf' , w) >>= tr-cont)
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → branch sf' w) ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
        comm-fx-route (sf' , w) >>= comm-outer-route)
        ≡˘⟨ >>=-assoc _ ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= comm-fx-route)
        >>= comm-outer-route) ∎
      where
        open ≡-Reasoning
        branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
          → (tr-fun-cont (iter (tr-step f)) (sf' , w) >>= tr-cont)
            ≡ (comm-fx-route (sf' , w) >>= comm-outer-route)
        branch sf' (inj₁ (inj₁ b))  = trans >>=-identityˡ (sym >>=-identityˡ)
        branch sf' (inj₁ (inj₂ x')) = trans >>=-identityˡ (sym >>=-identityˡ)
        branch sf' (inj₂ y)         = sym >>=-identityˡ

    L-outer-as-codiag : ∀ sf (x : X)
      → iter (tr-step (tr {X = Y} f)) (sf , x)
        ≡ iter (combine comm-fx (tr-step f)) (sf , inj₁ x)
    L-outer-as-codiag sf x =
      trans
        (iter-cong
          (λ p → trans (L-outer-char p)
            (refl⟩>>=⟨ (λ where
              (inj₁ q)               → refl
              (inj₂ (sf' , inj₁ b))  → refl
              (inj₂ (sf' , inj₂ y))  →
                refl⟩>>=⟨ (λ where
                  (sf'' , inj₁ b)  → refl
                  (sf'' , inj₂ x') → refl))))
          (sf , x))
        (sym (iter-codiag comm-fx (tr-step f) sf x))

    L-fun-char : ∀ sf (a : A)
      → SFunᵉ.fun (tr {X = X} (tr {X = Y} f)) (sf , a)
        ≡ (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= comm-entry)
    L-fun-char sf a = begin
      ((SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= tr-fun-cont (iter (tr-step f)))
        >>= tr-fun-cont (iter (tr-step (tr {X = Y} f))))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
        tr-fun-cont (iter (tr-step f)) (sf' , w)
          >>= tr-fun-cont (iter (tr-step (tr {X = Y} f))))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → branch sf' w) ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= comm-entry) ∎
      where
        open ≡-Reasoning
        branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
          → (tr-fun-cont (iter (tr-step f)) (sf' , w)
              >>= tr-fun-cont (iter (tr-step (tr {X = Y} f))))
            ≡ comm-entry (sf' , w)
        branch sf' (inj₁ (inj₁ b)) = >>=-identityˡ
        branch sf' (inj₁ (inj₂ x)) =
          trans >>=-identityˡ (L-outer-as-codiag sf' x)
        branch sf' (inj₂ y) =
          trans
            (refl⟩>>=⟨ (λ where
              (sf'' , inj₁ b) → refl
              (sf'' , inj₂ x) → L-outer-as-codiag sf'' x))
            (iter-vanishing-2 comm-fx (tr-step f) sf' y)

    -- ────────────────────────────────────────────────────────────────
    -- RHS: tr_Y (tr_X g₀).

    R-inner-premise : ∀ sf (x : X)
      → tr-step g₀ (comm-pad sf , x)
        ≡ (comm-fx (sf , x) >>= iter-conj-step comm-pad (λ b → b))
    R-inner-premise sf x = begin
      (SFunᵉ.fun g₀ (comm-pad sf , inj₂ x) >>= tr-cont)
        ≡⟨ g₀-char _ sf _ (inj₂ x) ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
         return (comm-pad sf' , β-route w)) >>= tr-cont)
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
        return (comm-pad sf' , β-route w) >>= tr-cont)
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
        tr-cont (comm-pad sf' , β-route w))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → branch sf' w) ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= λ (sf' , w) →
        comm-fx-route (sf' , w) >>= iter-conj-step comm-pad (λ b → b))
        ≡˘⟨ >>=-assoc _ ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₂ x)) >>= comm-fx-route)
        >>= iter-conj-step comm-pad (λ b → b)) ∎
      where
        open ≡-Reasoning
        branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
          → tr-cont (comm-pad sf' , β-route w)
            ≡ (comm-fx-route (sf' , w) >>= iter-conj-step comm-pad (λ b → b))
        branch sf' (inj₁ (inj₁ b))  = sym >>=-identityˡ
        branch sf' (inj₁ (inj₂ x')) = sym >>=-identityˡ
        branch sf' (inj₂ y)         = sym >>=-identityˡ

    R-inner-equiv : ∀ sf (x : X)
      → iter (tr-step g₀) (comm-pad sf , x)
        ≡ (iter comm-fx (sf , x) >>= comm-padloop)
    R-inner-equiv sf x =
      iter-conjugate
        comm-pad (λ b → b)
        comm-fx (tr-step g₀)
        (λ s₁ x' → R-inner-premise s₁ x')
        sf x

    R-outer-route : (SFunᵉ.State f × Y) ⊎ (SFunᵉ.State f × (B ⊎ X))
                  → M ((SFunᵉ.State f × Y) ⊎ (SFunᵉ.State f × B))
    R-outer-route (inj₁ q)              = return (inj₁ q)
    R-outer-route (inj₂ (sf' , inj₁ b)) = return (inj₂ (sf' , b))
    R-outer-route (inj₂ (sf' , inj₂ x)) =
      iter comm-fx (sf' , x) >>= tr-cont

    R-outer-body : (SFunᵉ.State f × Y)
                 → M ((SFunᵉ.State f × Y) ⊎ (SFunᵉ.State f × B))
    R-outer-body (sf , y) = tr-step f (sf , y) >>= R-outer-route

    R-outer-premise : ∀ sf (y : Y)
      → tr-step (tr {X = X} g₀) (comm-pad sf , y)
        ≡ (R-outer-body (sf , y) >>= iter-conj-step comm-pad (λ b → b))
    R-outer-premise sf y = trans lhs-chain (sym rhs-chain)
      where
        open ≡-Reasoning

        common : SFunᵉ.State f → (B ⊎ X) ⊎ Y
               → M ((SFunᵉ.State g₀ × Y) ⊎ (SFunᵉ.State g₀ × B))
        common sf' (inj₁ (inj₁ b)) = return (inj₂ (comm-pad sf' , b))
        common sf' (inj₁ (inj₂ x)) =
          iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
            tr-cont (sf'' , w₀) >>= iter-conj-step comm-pad (λ b → b)
        common sf' (inj₂ y')       = return (inj₁ (comm-pad sf' , y'))

        lhs-branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
          → (tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w)
              >>= tr-cont)
            ≡ common sf' w
        lhs-branch sf' (inj₁ (inj₁ b)) = >>=-identityˡ
        lhs-branch sf' (inj₂ y')       = >>=-identityˡ
        lhs-branch sf' (inj₁ (inj₂ x)) = begin
          (iter (tr-step g₀) (comm-pad sf' , x) >>= tr-cont)
            ≡⟨ R-inner-equiv sf' x ⟩>>=⟨refl ⟩
          ((iter comm-fx (sf' , x) >>= comm-padloop) >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩
          (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
            comm-padloop (sf'' , w₀) >>= tr-cont)
            ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
          (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
            tr-cont (comm-pad sf'' , w₀))
            ≡⟨ refl⟩>>=⟨ (λ where
                 (sf'' , inj₁ b)  → sym >>=-identityˡ
                 (sf'' , inj₂ y') → sym >>=-identityˡ) ⟩
          (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
            tr-cont (sf'' , w₀) >>= iter-conj-step comm-pad (λ b → b)) ∎

        lhs-chain :
          tr-step (tr {X = X} g₀) (comm-pad sf , y)
          ≡ (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) → common sf' w)
        lhs-chain = begin
          ((SFunᵉ.fun g₀ (comm-pad sf , inj₁ (inj₂ y))
             >>= tr-fun-cont (iter (tr-step g₀)))
            >>= tr-cont)
            ≡⟨ (g₀-char _ sf _ (inj₁ (inj₂ y)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
          (((SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
              return (comm-pad sf' , β-route w))
             >>= tr-fun-cont (iter (tr-step g₀)))
            >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
             return (comm-pad sf' , β-route w)
               >>= tr-fun-cont (iter (tr-step g₀)))
            >>= tr-cont)
            ≡⟨ ((refl⟩>>=⟨ (λ _ → >>=-identityˡ))) ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
             tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w))
            >>= tr-cont)
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
            tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w)
              >>= tr-cont)
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → lhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) → common sf' w) ∎

        rhs-branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
          → ((tr-cont (sf' , w) >>= R-outer-route)
              >>= iter-conj-step comm-pad (λ b → b))
            ≡ common sf' w
        rhs-branch sf' (inj₁ (inj₁ b)) =
          trans (>>=-identityˡ ⟩>>=⟨refl) >>=-identityˡ
        rhs-branch sf' (inj₂ y') =
          trans (>>=-identityˡ ⟩>>=⟨refl) >>=-identityˡ
        rhs-branch sf' (inj₁ (inj₂ x)) = begin
          ((tr-cont (sf' , inj₁ (inj₂ x)) >>= R-outer-route)
            >>= iter-conj-step comm-pad (λ b → b))
            ≡⟨ >>=-identityˡ ⟩>>=⟨refl ⟩
          (R-outer-route (inj₂ (sf' , inj₂ x))
            >>= iter-conj-step comm-pad (λ b → b))
            ≡⟨ >>=-assoc _ ⟩
          (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
            tr-cont (sf'' , w₀) >>= iter-conj-step comm-pad (λ b → b)) ∎

        rhs-chain :
          (R-outer-body (sf , y) >>= iter-conj-step comm-pad (λ b → b))
          ≡ (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) → common sf' w)
        rhs-chain = begin
          (((SFunᵉ.fun f (sf , inj₂ y) >>= tr-cont) >>= R-outer-route)
            >>= iter-conj-step comm-pad (λ b → b))
            ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
          ((SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
             tr-cont (sf' , w) >>= R-outer-route)
            >>= iter-conj-step comm-pad (λ b → b))
            ≡⟨ >>=-assoc _ ⟩
          (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) →
            (tr-cont (sf' , w) >>= R-outer-route)
              >>= iter-conj-step comm-pad (λ b → b))
            ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → rhs-branch sf' w) ⟩
          (SFunᵉ.fun f (sf , inj₂ y) >>= λ (sf' , w) → common sf' w) ∎

    R-outer-equiv : ∀ sf (y : Y)
      → iter (tr-step (tr {X = X} g₀)) (comm-pad sf , y)
        ≡ (iter R-outer-body (sf , y) >>= comm-padexit)
    R-outer-equiv sf y =
      iter-conjugate
        comm-pad (λ b → b)
        R-outer-body (tr-step (tr {X = X} g₀))
        (λ s₁ y' → R-outer-premise s₁ y')
        sf y

    R-outer-as-codiag : ∀ sf (y : Y)
      → iter R-outer-body (sf , y)
        ≡ iter (combine comm-fx (tr-step f)) (sf , inj₂ y)
    R-outer-as-codiag sf y =
      trans
        (iter-cong
          (λ p → refl⟩>>=⟨ (λ where
            (inj₁ q)               → refl
            (inj₂ (sf' , inj₁ b))  → refl
            (inj₂ (sf' , inj₂ x))  →
              refl⟩>>=⟨ (λ where
                (sf'' , inj₁ b)  → refl
                (sf'' , inj₂ y') → refl)))
          (sf , y))
        (sym (iter-codiag-y comm-fx (tr-step f) sf y))

    R-outer-full : ∀ sf (y : Y)
      → iter (tr-step (tr {X = X} g₀)) (comm-pad sf , y)
        ≡ (iter (combine comm-fx (tr-step f)) (sf , inj₂ y) >>= comm-padexit)
    R-outer-full sf y =
      trans (R-outer-equiv sf y) (R-outer-as-codiag sf y ⟩>>=⟨refl)

    R-entry-branch : ∀ sf' (w : (B ⊎ X) ⊎ Y)
      → (tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w)
          >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡ (comm-entry (sf' , w) >>= comm-padexit)
    R-entry-branch sf' (inj₁ (inj₁ b)) =
      trans >>=-identityˡ (sym >>=-identityˡ)
    R-entry-branch sf' (inj₂ y) =
      trans >>=-identityˡ (R-outer-full sf' y)
    R-entry-branch sf' (inj₁ (inj₂ x)) = begin
      (iter (tr-step g₀) (comm-pad sf' , x)
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ R-inner-equiv sf' x ⟩>>=⟨refl ⟩
      ((iter comm-fx (sf' , x) >>= comm-padloop)
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ >>=-assoc _ ⟩
      (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
        comm-padloop (sf'' , w₀)
          >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ refl⟩>>=⟨ (λ _ → >>=-identityˡ) ⟩
      (iter comm-fx (sf' , x) >>= λ (sf'' , w₀) →
        tr-fun-cont (iter (tr-step (tr {X = X} g₀))) (comm-pad sf'' , w₀))
        ≡⟨ refl⟩>>=⟨ (λ where
             (sf'' , inj₁ b) → sym >>=-identityˡ
             (sf'' , inj₂ y) → R-outer-full sf'' y) ⟩
      (iter comm-fx (sf' , x) >>= λ q →
        vanishing-2-dispatch-x iter comm-fx (tr-step f) q >>= comm-padexit)
        ≡˘⟨ >>=-assoc _ ⟩
      ((iter comm-fx (sf' , x)
         >>= vanishing-2-dispatch-x iter comm-fx (tr-step f))
        >>= comm-padexit)
        ≡⟨ iter-vanishing-2-x comm-fx (tr-step f) sf' x ⟩>>=⟨refl ⟩
      (iter (combine comm-fx (tr-step f)) (sf' , inj₁ x) >>= comm-padexit) ∎
      where open ≡-Reasoning

    R-fun-char : ∀ sf (a : A)
      → SFunᵉ.fun (tr {X = Y} (tr {X = X} g₀)) (comm-pad sf , a)
        ≡ (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
            comm-entry (sf' , w) >>= comm-padexit)
    R-fun-char sf a = begin
      ((SFunᵉ.fun g₀ (comm-pad sf , inj₁ (inj₁ a))
         >>= tr-fun-cont (iter (tr-step g₀)))
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ (g₀-char _ sf _ (inj₁ (inj₁ a)) ⟩>>=⟨refl) ⟩>>=⟨refl ⟩
      (((SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
          return (comm-pad sf' , β-route w))
         >>= tr-fun-cont (iter (tr-step g₀)))
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ >>=-assoc _ ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
         return (comm-pad sf' , β-route w)
           >>= tr-fun-cont (iter (tr-step g₀)))
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ (refl⟩>>=⟨ (λ _ → >>=-identityˡ)) ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
         tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w))
        >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
        tr-fun-cont (iter (tr-step g₀)) (comm-pad sf' , β-route w)
          >>= tr-fun-cont (iter (tr-step (tr {X = X} g₀))))
        ≡⟨ refl⟩>>=⟨ (λ (sf' , w) → R-entry-branch sf' w) ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
        comm-entry (sf' , w) >>= comm-padexit) ∎
      where open ≡-Reasoning

    comm-hyp : ∀ sf (a : A)
      → (SFunᵉ.fun (tr {X = X} (tr {X = Y} f)) (sf , a) >>= λ (s' , b) →
          return (comm-pad s' , b))
        ≡ SFunᵉ.fun (tr {X = Y} (tr {X = X} g₀)) (comm-pad sf , a)
    comm-hyp sf a = begin
      (SFunᵉ.fun (tr {X = X} (tr {X = Y} f)) (sf , a) >>= λ (s' , b) →
        return (comm-pad s' , b))
        ≡⟨ L-fun-char sf a ⟩>>=⟨refl ⟩
      ((SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= comm-entry) >>= λ (s' , b) →
        return (comm-pad s' , b))
        ≡⟨ >>=-assoc _ ⟩
      (SFunᵉ.fun f (sf , inj₁ (inj₁ a)) >>= λ (sf' , w) →
        comm-entry (sf' , w) >>= λ (s' , b) → return (comm-pad s' , b))
        ≡˘⟨ R-fun-char sf a ⟩
      SFunᵉ.fun (tr {X = Y} (tr {X = X} g₀)) (comm-pad sf , a) ∎
      where open ≡-Reasoning

trace-comm-ᵉ : ∀ {X Y A B : Type}
  {f : SFunᵉ ((A ⊎ X) ⊎ Y) ((B ⊎ X) ⊎ Y)}
  → tr {X = X} (tr {X = Y} f)
    ≈ᵉ tr {X = Y} (tr {X = X}
        ((α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ)) ∘ᵉ
          (f ∘ᵉ (α⇐ᵉ ∘ᵉ ((idᵉ ⊗ᵉ σᵉ) ∘ᵉ α⇒ᵉ)))))
trace-comm-ᵉ {f = f} xs =
  trace-sim (comm-pad f) (comm-hyp f) (SFunᵉ.init f) xs

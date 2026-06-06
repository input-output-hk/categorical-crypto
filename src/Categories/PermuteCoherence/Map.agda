{-# OPTIONS --safe --with-K #-}

module Categories.PermuteCoherence.Map where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Level using (Level)

private
  variable
    a c : Level
    A : Set a
    C : Set c

-- J-lemmas about subst₂ on FinBij
subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
subst₂-FinBij-id refl = refl

cons-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (subst₂ FinBij a b π) ≡ subst₂ FinBij (cong suc a) (cong suc b) (cons-fb π)
cons-fb-subst₂ refl refl π = refl

swap-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (cons-fb (subst₂ FinBij a b π))
    ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) b)
        (cons-fb (cons-fb π))
swap-fb-subst₂ refl refl π = refl

-- Bridge: subst₂ along `cong f`-rewritten proofs equals subst₂ along the
-- recombined proof (needed since `length-map h (x∷xs)` reduces to
-- `cong suc (length-map h xs)`, but our recursion produces
-- `cong suc (sym (length-map h xs)) = subst₂` shape).
subst₂-FinBij-irr : ∀ {n m n' m'} (a a' : n ≡ n') (b b' : m ≡ m') (π : FinBij n m)
  → a ≡ a' → b ≡ b' → subst₂ FinBij a b π ≡ subst₂ FinBij a' b' π
subst₂-FinBij-irr a a' b b' π refl refl = refl

sym-cong-suc : ∀ {n m} (e : n ≡ m) → sym (cong suc e) ≡ cong suc (sym e)
sym-cong-suc refl = refl

sym-cong-ss : ∀ {n m} (e : n ≡ m)
  → sym (cong suc (cong suc e)) ≡ cong (λ z → suc (suc z)) (sym e)
sym-cong-ss refl = refl

∘-fb-subst₂ : ∀ {n m k n' m' k'} (a : n ≡ n') (b : m ≡ m') (cc : k ≡ k')
  (g : FinBij m k) (f : FinBij n m)
  → subst₂ FinBij b cc g ∘-fb subst₂ FinBij a b f
    ≡ subst₂ FinBij a cc (g ∘-fb f)
∘-fb-subst₂ refl refl refl g f = refl

-- swap-fb commutes trivially: swap-fb at size suc(suc n) under subst
swap-gen-subst₂ : ∀ {n n'} (a : n ≡ n')
  → swap-fb n' ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) a) (swap-fb n)
swap-gen-subst₂ refl = refl

eval-map⁺ : (h : A → C) {xs ys : List A} (p : xs ↭ ys)
  → eval-↭ (PermProp.map⁺ h p)
    ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
  trans (cong cons-fb (eval-map⁺ h p))
  (trans (cons-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p))
         (subst₂-FinBij-irr
            (cong suc (sym (length-map h xs))) (sym (length-map h (x ∷ xs)))
            (cong suc (sym (length-map h ys))) (sym (length-map h (x ∷ ys)))
            (cons-fb (eval-↭ p))
            (sym (sym-cong-suc (length-map h xs)))
            (sym (sym-cong-suc (length-map h ys)))))
eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
  trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
  (trans goal
         (subst₂-FinBij-irr
            (ss aa) (sym (length-map h (x ∷ x' ∷ xs)))
            (ss bb) (sym (length-map h (y ∷ y' ∷ ys)))
            (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
            (sym (sym-cong-ss (length-map h xs)))
            (sym (sym-cong-ss (length-map h ys)))))
  where
    aa = sym (length-map h xs)
    bb = sym (length-map h ys)
    ss : ∀ {n m} → n ≡ m → suc (suc n) ≡ suc (suc m)
    ss = cong (λ z → suc (suc z))
    goal : swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb (subst₂ FinBij aa bb (eval-↭ p)))
         ≡ subst₂ FinBij (ss aa) (ss bb)
             (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
    goal =
      trans (cong (swap-fb (length (map h ys)) ∘-fb_) (swap-fb-subst₂ aa bb (eval-↭ p)))
      (trans (cong (_∘-fb subst₂ FinBij (ss aa) (ss bb) (cons-fb (cons-fb (eval-↭ p))))
                   (swap-gen-subst₂ bb))
             (∘-fb-subst₂ (ss aa) (ss bb) (ss bb) (swap-fb (length ys)) (cons-fb (cons-fb (eval-↭ p)))))
eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
  trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
        (∘-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (sym (length-map h zs)) (eval-↭ q) (eval-↭ p))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

------------------------------------------------------------------------
-- More generic eval lemmas.

-- eval of a reflexive permutation is id-fb, modulo the length cast.
eval-↭-reflexive : {xs ys : List A} (eq : xs ≡ ys)
  → eval-↭ (Perm.↭-reflexive eq)
    ≡ subst (λ n → FinBij (length xs) n) (cong length eq) id-fb
eval-↭-reflexive refl = refl

-- eval commutes with subst on the codomain list.
eval-subst-cod : {xs : List A} {C D : List A} (eq : C ≡ D) (p : xs ↭ C)
  → eval-↭ (subst (λ z → xs ↭ z) eq p)
    ≡ subst (λ n → FinBij (length xs) n) (cong length eq) (eval-↭ p)
eval-subst-cod refl p = refl

-- ≈-fb is preserved by transporting both bijections along the SAME
-- length equalities (subst₂ on FinBij).
subst₂-FinBij-≈ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') {π ρ : FinBij n m}
  → π ≈-fb ρ → subst₂ FinBij a b π ≈-fb subst₂ FinBij a b ρ
subst₂-FinBij-≈ refl refl eq = eq

-- ≈-fb is preserved by transporting along subst on the codomain.
subst-FinBij-≈ : ∀ {n m m'} (b : m ≡ m') {π ρ : FinBij n m}
  → π ≈-fb ρ
  → subst (λ k → FinBij n k) b π ≈-fb subst (λ k → FinBij n k) b ρ
subst-FinBij-≈ refl eq = eq

-- eval commutes with subst on the DOMAIN list.
eval-subst-dom : {C D : List A} {ys : List A} (eq : C ≡ D) (p : C ↭ ys)
  → eval-↭ (subst (λ z → z ↭ ys) eq p)
    ≡ subst (λ n → FinBij n (length ys)) (cong length eq) (eval-↭ p)
eval-subst-dom refl p = refl

-- `map⁺` of a reflexive permutation is the reflexive permutation of the
-- mapped equality (definitionally when the equality is `refl`; by J in
-- general).
map⁺-↭-reflexive : (h : A → C) {xs ys : List A} (eq : xs ≡ ys)
  → PermProp.map⁺ h (Perm.↭-reflexive eq) ≡ Perm.↭-reflexive (cong (map h) eq)
map⁺-↭-reflexive h refl = refl

-- `≈-fb` from propositional equality of bijections.
≈-fb-of-≡ : ∀ {n m} {π ρ : FinBij n m} → π ≡ ρ → π ≈-fb ρ
≈-fb-of-≡ refl _ = refl

-- Pointwise congruence and associativity for `_∘-fb_`.
∘-fb-cong : ∀ {n m k} {g g′ : FinBij m k} {f f′ : FinBij n m}
  → g ≈-fb g′ → f ≈-fb f′ → (g ∘-fb f) ≈-fb (g′ ∘-fb f′)
∘-fb-cong {g = g} {g′} {f} {f′} g≈ f≈ i rewrite f≈ i = g≈ (f′ P.⟨$⟩ʳ i)

∘-fb-assoc : ∀ {n m k l} (h : FinBij k l) (g : FinBij m k) (f : FinBij n m)
  → (h ∘-fb g) ∘-fb f ≈-fb h ∘-fb (g ∘-fb f)
∘-fb-assoc h g f i = refl

------------------------------------------------------------------------
-- Identity / inverse laws for `_∘-fb_` (pointwise).

open import Relation.Binary.PropositionalEquality.Core using () renaming (refl to ≡refl)

id-fb-left : ∀ {n m} (f : FinBij n m) → id-fb ∘-fb f ≈-fb f
id-fb-left f i = ≡refl

id-fb-right : ∀ {n m} (f : FinBij n m) → f ∘-fb id-fb ≈-fb f
id-fb-right f i = ≡refl

-- `f` after `inv-fb f` is the identity:  f ∘-fb inv-fb f ≈ id.
∘-fb-inv-right : ∀ {n m} (f : FinBij n m) → f ∘-fb inv-fb f ≈-fb id-fb
∘-fb-inv-right f i = P.inverseʳ f

-- Cancellation:  f ∘-fb (inv-fb f ∘-fb z) ≈ z.
∘-fb-cancel-left : ∀ {n m k} (f : FinBij m k) (z : FinBij n k)
  → f ∘-fb (inv-fb f ∘-fb z) ≈-fb z
∘-fb-cancel-left f z i = P.inverseʳ f

------------------------------------------------------------------------
-- Codomain-cast (`subst` on the FinBij codomain) algebra.

open import Categories.PermuteCoherence.FinBij using (inv-fb)

-- `inv-fb` is pointwise congruent.  From `f ⟨$⟩ʳ ≡ g ⟨$⟩ʳ` pointwise:
--   f ⟨$⟩ˡ i = g ⟨$⟩ˡ (g ⟨$⟩ʳ (f ⟨$⟩ˡ i))
--           = g ⟨$⟩ˡ (f ⟨$⟩ʳ (f ⟨$⟩ˡ i))   (by eq)
--           = g ⟨$⟩ˡ i.
inv-fb-cong : ∀ {n m} {f g : FinBij n m} → f ≈-fb g → inv-fb f ≈-fb inv-fb g
inv-fb-cong {f = f} {g} eq i =
  trans (sym (P.inverseˡ g))
        (cong (g P.⟨$⟩ˡ_) (trans (sym (eq (f P.⟨$⟩ˡ i))) (P.inverseʳ f)))

-- Post-composing a codomain cast-identity transports the codomain.
cast-id-∘ : ∀ {n m m'} (e : m ≡ m') (f : FinBij n m)
  → subst (λ k → FinBij m k) e id-fb ∘-fb f ≡ subst (λ k → FinBij n k) e f
cast-id-∘ refl f = ≈refl
  where open import Relation.Binary.PropositionalEquality.Core using () renaming (refl to ≈refl)

-- The inverse of a codomain cast-identity is the reversed cast-identity.
inv-fb-cast-id : ∀ {m m'} (e : m ≡ m')
  → inv-fb (subst (λ k → FinBij m k) e id-fb) ≡ subst (λ k → FinBij m' k) (sym e) id-fb
inv-fb-cast-id refl = ≈refl
  where open import Relation.Binary.PropositionalEquality.Core using () renaming (refl to ≈refl)

-- Compose two codomain substs.
subst-cod-comp : ∀ {n m₁ m₂ m₃} (e₁ : m₁ ≡ m₂) (e₂ : m₂ ≡ m₃) (f : FinBij n m₁)
  → subst (λ k → FinBij n k) e₂ (subst (λ k → FinBij n k) e₁ f)
    ≡ subst (λ k → FinBij n k) (trans e₁ e₂) f
subst-cod-comp refl refl f = ≈refl
  where open import Relation.Binary.PropositionalEquality.Core using () renaming (refl to ≈refl)

-- Codomain-subst proof-irrelevance (UIP via --with-K).
subst-cod-irr : ∀ {n m m'} (e e' : m ≡ m') (f : FinBij n m)
  → e ≡ e' → subst (λ k → FinBij n k) e f ≡ subst (λ k → FinBij n k) e' f
subst-cod-irr e e' f refl = ≈refl
  where open import Relation.Binary.PropositionalEquality.Core using () renaming (refl to ≈refl)

-- Transport `≈-fb` along propositional equalities of both arguments.
≈-fb-resp-≡ : ∀ {n m} {π π' ρ ρ' : FinBij n m}
  → π ≡ π' → ρ ≡ ρ' → π ≈-fb ρ → π' ≈-fb ρ'
≈-fb-resp-≡ refl refl eq = eq

{-# OPTIONS --safe --without-K #-}

-- A ciphertext under a key no recipe can name is inert (`comonlundhcortier2008`
-- Example 3.8 p. 13; the proof of Lemma 17 p. 26).  Evaluate recipes on the bare
-- key name `k` instead: substituting the ciphertext for `k` commutes with `nf`
-- (`nf-[≔]`) and is injective, since it leaves no `name k` outside a copy of the
-- ciphertext.  So equality tests see the ciphertext as `k` (`inert`), whatever
-- its plaintext (`cipher-≈ₛ`), and decryption under `k` opens nothing but the
-- ciphertext itself (`dec-opens`).

module CategoricalCrypto.Symbolic.Term.PairEnc.Cipher where

open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product
open import Data.Unit
open import Function.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Construct.Composition using (_⇔-∘_)
open import Function.Construct.Symmetry using (⇔-sym)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc

open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀

open Terms Σ₀
open EqTheory E₀

private variable
  ss           : List ⊤
  m m′ t u x y : Msg
  n r          : Name
  own          : Name → Set

cipher : Msg → Name → Name → Msg
cipher m k r = enc⟨ m , name k , name r ⟩

infixl 7 _[_≔_] _[_≔_]*
_[_≔_]  : Msg → Name → Msg → Msg
_[_≔_]* : All Tm ss → Name → Msg → All Tm ss
name n [ k ≔ c ] with n ≟ₙ k
... | yes _ = c
... | no _  = name n
app f ts [ k ≔ c ] = app f (ts [ k ≔ c ]*)
[]       [ k ≔ c ]* = []
(t ∷ ts) [ k ≔ c ]* = t [ k ≔ c ] ∷ ts [ k ≔ c ]*

private
  key : Msg → Msg
  key enc⟨ _ , k , _ ⟩ = k
  key dec⟨ _ , k ⟩     = k
  key t                = t

  dec′-≢ : t ≢ u → dec′ enc⟨ x , u , y ⟩ t ≡ dec⟨ enc⟨ x , u , y ⟩ , t ⟩
  dec′-≢ {t = t} {u = u} t≢u with t ≟ᵗ u
  ... | yes t≡u = ⊥-elim (t≢u t≡u)
  ... | no _    = refl

module _ {k : Name} where

  [≔]-here : name k [ k ≔ u ] ≡ u
  [≔]-here with k ≟ₙ k
  ... | yes _   = refl
  ... | no k≢k = ⊥-elim (k≢k refl)

  [≔]-∉  : ∀ t → k ∉ names t → t [ k ≔ u ] ≡ t
  [≔]-∉* : (ts : All Tm ss) → k ∉ names* ts → ts [ k ≔ u ]* ≡ ts
  [≔]-∉ (name n) k∉ with n ≟ₙ k
  ... | yes refl = ⊥-elim (k∉ (here refl))
  ... | no _     = refl
  [≔]-∉ (app f ts) k∉ = cong (app f) ([≔]-∉* ts k∉)
  [≔]-∉* []       _  = refl
  [≔]-∉* (t ∷ ts) k∉ = cong₂ _∷_ ([≔]-∉ t (k∉ ∘ ∈-++⁺ˡ)) ([≔]-∉* ts (k∉ ∘ ∈-++⁺ʳ (names t)))

  ⟨⟩-[≔]  : (∀ {n} → own n → n ≢ k) → (ζ : Recipe (tt ∷ []) own tt) → ζ ⟨ u ∷ [] ⟩ ≡ ζ ⟨ name k ∷ [] ⟩ [ k ≔ u ]
  ⟨⟩-[≔]* : (∀ {n} → own n → n ≢ k) → (ζs : All (Recipe (tt ∷ []) own) ss)
          → ζs ⟨ u ∷ [] ⟩* ≡ ζs ⟨ name k ∷ [] ⟩* [ k ≔ u ]*
  ⟨⟩-[≔] _ (var (here refl)) = sym [≔]-here
  ⟨⟩-[≔] o (mine n p) with n ≟ₙ k
  ... | yes n≡k = ⊥-elim (o p n≡k)
  ... | no _    = refl
  ⟨⟩-[≔] o (app f ζs) = cong (app f) (⟨⟩-[≔]* o ζs)
  ⟨⟩-[≔]* o []       = refl
  ⟨⟩-[≔]* o (ζ ∷ ζs) = cong₂ _∷_ (⟨⟩-[≔] o ζ) (⟨⟩-[≔]* o ζs)

  private
    [≔]-≢ : ∀ t → t [ k ≔ cipher m k r ] ≢ name k
    [≔]-≢ (name n) with n ≟ₙ k
    ... | yes _   = λ ()
    ... | no n≢k = λ { refl → n≢k refl }
    [≔]-≢ (app _ _) = λ ()

    [≔]-key : ∀ t → t [ k ≔ cipher m k r ] ≡ enc⟨ x , name k , y ⟩ → t ≡ name k
    [≔]-key (name n) with n ≟ₙ k
    ... | yes refl = λ _ → refl
    ... | no _     = λ ()
    [≔]-key enc⟨ _ , u , _ ⟩ e = ⊥-elim ([≔]-≢ u (cong key e))
    [≔]-key ⟪ _ , _ ⟫       ()
    [≔]-key (π₁ _)          ()
    [≔]-key (π₂ _)          ()
    [≔]-key dec⟨ _ , _ ⟩    ()
    [≔]-key (app (cst _) _) ()

    -- a left inverse of `_[ k ≔ cipher m k r ]`, which is therefore injective
    hide  : Msg → Msg → Msg
    hide* : Msg → All Tm ss → All Tm ss
    hide c (name n)     = name n
    hide c t@(app f ts) with t ≟ᵗ c
    ... | yes _ = name k
    ... | no _  = app f (hide* c ts)
    hide* c []       = []
    hide* c (t ∷ ts) = hide c t ∷ hide* c ts

    hide-[≔]  : ∀ t → hide (cipher m k r) (t [ k ≔ cipher m k r ]) ≡ t
    hide-[≔]* : (ts : All Tm ss) → hide* (cipher m k r) (ts [ k ≔ cipher m k r ]*) ≡ ts
    hide-[≔] {m = m} {r = r} (name n) with n ≟ₙ k
    ... | no _ = refl
    ... | yes refl with cipher m k r ≟ᵗ cipher m k r
    ...   | yes _  = refl
    ...   | no c≢c = ⊥-elim (c≢c refl)
    hide-[≔] {m = m} {r = r} (app f ts) with app f (ts [ k ≔ cipher m k r ]*) ≟ᵗ cipher m k r
    ... | yes e = case [≔]-key (app f ts) e of λ ()
    ... | no _  = cong (app f) (hide-[≔]* ts)
    hide-[≔]* []       = refl
    hide-[≔]* (t ∷ ts) = cong₂ _∷_ (hide-[≔] t) (hide-[≔]* ts)

  [≔]-injective : t [ k ≔ cipher m k r ] ≡ u [ k ≔ cipher m k r ] → t ≡ u
  [≔]-injective e = trans (sym (hide-[≔] _)) (trans (cong (hide _) e) (hide-[≔] _))

  private
    π₁′-[≔] : ∀ t → π₁′ (t [ k ≔ cipher m k r ]) ≡ π₁′ t [ k ≔ cipher m k r ]
    π₁′-[≔] (name n) with n ≟ₙ k
    ... | yes _ = refl
    ... | no _  = refl
    π₁′-[≔] ⟪ _ , _ ⟫       = refl
    π₁′-[≔] (app fst _)     = refl
    π₁′-[≔] (app snd _)     = refl
    π₁′-[≔] (app enc _)     = refl
    π₁′-[≔] (app dec _)     = refl
    π₁′-[≔] (app (cst _) _) = refl

    π₂′-[≔] : ∀ t → π₂′ (t [ k ≔ cipher m k r ]) ≡ π₂′ t [ k ≔ cipher m k r ]
    π₂′-[≔] (name n) with n ≟ₙ k
    ... | yes _ = refl
    ... | no _  = refl
    π₂′-[≔] ⟪ _ , _ ⟫       = refl
    π₂′-[≔] (app fst _)     = refl
    π₂′-[≔] (app snd _)     = refl
    π₂′-[≔] (app enc _)     = refl
    π₂′-[≔] (app dec _)     = refl
    π₂′-[≔] (app (cst _) _) = refl

    dec′-[≔] : ∀ t u → dec′ (t [ k ≔ cipher m k r ]) (u [ k ≔ cipher m k r ]) ≡ dec′ t u [ k ≔ cipher m k r ]
    dec′-[≔] (name n) u with n ≟ₙ k
    ... | yes _ = dec′-≢ ([≔]-≢ u)
    ... | no _  = refl
    dec′-[≔] {m = m} {r = r} enc⟨ _ , v , _ ⟩ u with u ≟ᵗ v | u [ k ≔ cipher m k r ] ≟ᵗ v [ k ≔ cipher m k r ]
    ... | yes refl | yes _ = refl
    ... | yes refl | no ¬e = ⊥-elim (¬e refl)
    ... | no u≢v   | yes e = ⊥-elim (u≢v ([≔]-injective e))
    ... | no _     | no _  = refl
    dec′-[≔] ⟪ _ , _ ⟫       _ = refl
    dec′-[≔] (π₁ _)          _ = refl
    dec′-[≔] (π₂ _)          _ = refl
    dec′-[≔] dec⟨ _ , _ ⟩    _ = refl
    dec′-[≔] (app (cst _) _) _ = refl

  app↓-[≔] : ∀ f (us : All Tm (arity f)) → app↓ f (us [ k ≔ cipher m k r ]*) ≡ app↓ f us [ k ≔ cipher m k r ]
  app↓-[≔] pair    _            = refl
  app↓-[≔] fst     (u ∷ [])     = π₁′-[≔] u
  app↓-[≔] snd     (u ∷ [])     = π₂′-[≔] u
  app↓-[≔] enc     _            = refl
  app↓-[≔] dec     (u ∷ v ∷ []) = dec′-[≔] u v
  app↓-[≔] (cst _) _            = refl

  nf-[≔]  : ∀ t → nf (t [ k ≔ cipher m k r ]) ≡ nf t [ k ≔ cipher (nf m) k r ]
  nf*-[≔] : (ts : All Tm ss) → nf* (ts [ k ≔ cipher m k r ]*) ≡ nf* ts [ k ≔ cipher (nf m) k r ]*
  nf-[≔] (name n) with n ≟ₙ k
  ... | yes _ = refl
  ... | no _  = refl
  nf-[≔] (app f ts) = trans (cong (app↓ f) (nf*-[≔] ts)) (app↓-[≔] f (nf* ts))
  nf*-[≔] []       = refl
  nf*-[≔] (t ∷ ts) = cong₂ _∷_ (nf-[≔] t) (nf*-[≔] ts)

  nf-⟨⟩ : (∀ {n} → own n → n ≢ k) → (ζ : Recipe (tt ∷ []) own tt)
        → nf (ζ ⟨ cipher m k r ∷ [] ⟩) ≡ nf (ζ ⟨ name k ∷ [] ⟩) [ k ≔ cipher (nf m) k r ]
  nf-⟨⟩ o ζ = trans (cong nf (⟨⟩-[≔] o ζ)) (nf-[≔] (ζ ⟨ name k ∷ [] ⟩))

  inert : (∀ {n} → own n → n ≢ k) → (ζ ζ′ : Recipe (tt ∷ []) own tt)
        → (ζ ⟨ cipher m k r ∷ [] ⟩ ≈E ζ′ ⟨ cipher m k r ∷ [] ⟩) ⇔ (ζ ⟨ name k ∷ [] ⟩ ≈E ζ′ ⟨ name k ∷ [] ⟩)
  inert o ζ ζ′ = mk⇔
    (λ e → [≔]-injective (trans (sym (nf-⟨⟩ o ζ)) (trans e (nf-⟨⟩ o ζ′))))
    (λ e → trans (nf-⟨⟩ o ζ) (trans (cong (_[ k ≔ cipher _ k _ ]) e) (sym (nf-⟨⟩ o ζ′))))

  private
    foreign-≢ : ∀ m → n ∉ names* (cipher m k r ∷ []) → n ≢ k
    foreign-≢ m n∉ n≡k = n∉ (∈-++⁺ˡ (∈-++⁺ʳ (names m) (here n≡k)))

  cipher-≈ₛ : k ∉ names m → k ∉ names m′ → (cipher m k r ∷ []) ≈ₛ (cipher m′ k r ∷ [])
  cipher-≈ₛ {m = m} _ _ ζ ζ′ = ⇔-sym (inert (foreign-≢ m ∘ proj₁) ζ ζ′) ⇔-∘ inert (foreign-≢ m ∘ proj₁) ζ ζ′

  private
    opens : m [ k ≔ cipher m k r ] ≡ m → ∀ u → t ≡ u [ k ≔ cipher m k r ]
          → app↓ dec (t ∷ name k ∷ []) ≡ m → t ≡ cipher m k r
    opens {m = m} {r = r} {t = t} fixed u h e with app↓ dec (t ∷ name k ∷ []) | app↓-view dec (t ∷ name k ∷ [])
    ... | _ | contract dec-enc = trans h (trans (cong (_[ k ≔ cipher m k r ]) ([≔]-key u (sym h))) [≔]-here)
    ... | _ | stuck _          =
      ⊥-elim ([≔]-≢ (name k) (cong key (trans (cong (_[ k ≔ cipher m k r ]) e) (trans fixed (sym e)))))

  dec-opens : k ∉ names m → {own : Name → Set} → (∀ {n} → own n → n ≢ k)
            → (ζ : Recipe (tt ∷ []) own tt)
            → (dec⟨ ζ ⟨ cipher m k r ∷ [] ⟩ , name k ⟩ ≈E m) ⇔ (ζ ⟨ cipher m k r ∷ [] ⟩ ≈E cipher m k r)
  dec-opens {m = m} k∉m o ζ = mk⇔
    (opens (trans (sym (nf-[≔] {m = m} m)) (cong nf ([≔]-∉ m k∉m))) (nf (ζ ⟨ name k ∷ [] ⟩)) (nf-⟨⟩ o ζ))
    (λ e → trans (cong (flip dec′ (name k)) e) (⟶-nf {t = dec⟨ cipher m k _ , name k ⟩} (root dec-enc)))

{-# OPTIONS --safe --without-K #-}

-- The free functor read with one datum per generator occurrence: `⟦ f ⟧[ ι ]`
-- interprets each `var` of `f` at its own decoration `ι o`, and `Occ f` is the
-- set of those occurrences.  A coherence equation permutes occurrences but never
-- adds or drops one, so `⟦⟧[]-resp-≈` returns that permutation with the
-- equation.  The symbolic setup decorates occurrences with name supplies
-- (docs/uc-setup-symbolic.md §3.5).

open import Categories.FreeMonoidal
open import Level

module Categories.FreeMonoidal.Decorated
  {ℓ′ o ℓ e d} (dat : FreeMonoidalData {ℓ′}) (let open FreeMonoidalData dat)
  (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) (let module C = ⟦_⟧ᵥ.Cat ⟦v⟧)
  (⟦_⟧ᵖ₀ : X → C.Obj) (let open FreeObjInterp v X ⟦v⟧ ⟦_⟧ᵖ₀)
  (D : Set d) (⟦_⟧ᵈ : ∀ {x y} → mor x y → D → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀) where

open import Data.Empty
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum.Algebra
open import Data.Sum.Base
open import Data.Unit
open import Function.Base using (_∘′_)
open import Function.Bundles
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation

open FreeMonoidal dat

private variable A B : ObjTerm

Occ : HomTerm A B → Set
Occ (var _)  = ⊤
Occ (g ∘ f)  = Occ g ⊎ Occ f
Occ (f ⊗₁ g) = Occ f ⊎ Occ g
Occ _        = ⊥

⟦_⟧[_] : (f : HomTerm A B) → (Occ f → D) → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
⟦ var p ⟧[ ι ]  = ⟦ p ⟧ᵈ (ι tt)
⟦ id ⟧[ _ ]     = C.id
⟦ g ∘ f ⟧[ ι ]  = ⟦ g ⟧[ ι ∘′ inj₁ ] C.∘ ⟦ f ⟧[ ι ∘′ inj₂ ]
⟦ f ⊗₁ g ⟧[ ι ] = ⟦ f ⟧[ ι ∘′ inj₁ ] C.⊗₁ ⟦ g ⟧[ ι ∘′ inj₂ ]
⟦ λ⇒ ⟧[ _ ]     = C.λ⇒
⟦ λ⇐ ⟧[ _ ]     = C.λ⇐
⟦ ρ⇒ ⟧[ _ ]     = C.ρ⇒
⟦ ρ⇐ ⟧[ _ ]     = C.ρ⇐
⟦ α⇒ ⟧[ _ ]     = C.α⇒
⟦ α⇐ ⟧[ _ ]     = C.α⇐
⟦ σ ⟧[ _ ]      = C.σ

⟦⟧[]-cong : (f : HomTerm A B) {ι ι′ : Occ f → D} → (∀ x → ι x ≡ ι′ x) → ⟦ f ⟧[ ι ] ≡ ⟦ f ⟧[ ι′ ]
⟦⟧[]-cong (var p)  h = cong ⟦ p ⟧ᵈ (h tt)
⟦⟧[]-cong id       _ = refl
⟦⟧[]-cong (g ∘ f)  h = cong₂ C._∘_ (⟦⟧[]-cong g λ x → h (inj₁ x)) (⟦⟧[]-cong f λ x → h (inj₂ x))
⟦⟧[]-cong (f ⊗₁ g) h = cong₂ C._⊗₁_ (⟦⟧[]-cong f λ x → h (inj₁ x)) (⟦⟧[]-cong g λ x → h (inj₂ x))
⟦⟧[]-cong λ⇒       _ = refl
⟦⟧[]-cong λ⇐       _ = refl
⟦⟧[]-cong ρ⇒       _ = refl
⟦⟧[]-cong ρ⇐       _ = refl
⟦⟧[]-cong α⇒       _ = refl
⟦⟧[]-cong α⇐       _ = refl
⟦⟧[]-cong σ        _ = refl

private
  variable P Q R S : Set

  empty : ¬ P → ¬ Q → P ↔ Q
  empty ¬P ¬Q = mk↔ₛ′ (⊥-elim ∘′ ¬P) (⊥-elim ∘′ ¬Q) (λ q → ⊥-elim (¬Q q)) (λ p → ⊥-elim (¬P p))

  ⊥⊎ : (⊥ ⊎ P) ↔ P
  ⊥⊎ = mk↔ₛ′ [ ⊥-elim , (λ x → x) ]′ inj₂ (λ _ → refl) [ (λ ()) , (λ _ → refl) ]

  ⊎⊥ : (P ⊎ ⊥) ↔ P
  ⊎⊥ = mk↔ₛ′ [ (λ x → x) , ⊥-elim ]′ inj₁ (λ _ → refl) [ (λ _ → refl) , (λ ()) ]

  -- the occurrences of `(g ∘ f) ⊗₁ (g′ ∘ f′)` against `g ⊗₁ g′ ∘ f ⊗₁ f′`
  middle : ((P ⊎ Q) ⊎ (R ⊎ S)) ↔ ((P ⊎ R) ⊎ (Q ⊎ S))
  middle = mk↔ₛ′ swap₂ swap₂ inv inv
    where
    swap₂ : ∀ {P Q R S : Set} → (P ⊎ Q) ⊎ (R ⊎ S) → (P ⊎ R) ⊎ (Q ⊎ S)
    swap₂ (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
    swap₂ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
    swap₂ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
    swap₂ (inj₂ (inj₂ x)) = inj₂ (inj₂ x)
    inv : ∀ {P Q R S : Set} (x : (P ⊎ Q) ⊎ (R ⊎ S)) → swap₂ (swap₂ x) ≡ x
    inv (inj₁ (inj₁ _)) = refl
    inv (inj₁ (inj₂ _)) = refl
    inv (inj₂ (inj₁ _)) = refl
    inv (inj₂ (inj₂ _)) = refl

  -- `λ⇒ ∘ id ⊗₁ f` and `f ∘ λ⇒`
  unitˡ : (⊥ ⊎ (⊥ ⊎ P)) ↔ (P ⊎ ⊥)
  unitˡ = mk↔ₛ′ [ ⊥-elim , [ ⊥-elim , inj₁ ]′ ]′ [ inj₂ ∘′ inj₂ , ⊥-elim ]′
                [ (λ _ → refl) , (λ ()) ] [ (λ ()) , [ (λ ()) , (λ _ → refl) ] ]

  -- `ρ⇒ ∘ f ⊗₁ id` and `f ∘ ρ⇒`
  unitʳ : (⊥ ⊎ (P ⊎ ⊥)) ↔ (P ⊎ ⊥)
  unitʳ = mk↔ₛ′ [ ⊥-elim , [ inj₁ , ⊥-elim ]′ ]′ [ inj₂ ∘′ inj₁ , ⊥-elim ]′
                [ (λ _ → refl) , (λ ()) ] [ (λ ()) , [ (λ _ → refl) , (λ ()) ] ]

  -- `α⇒ ∘ (f ⊗₁ g) ⊗₁ h` and `f ⊗₁ g ⊗₁ h ∘ α⇒`
  shift : (⊥ ⊎ ((P ⊎ Q) ⊎ R)) ↔ ((P ⊎ (Q ⊎ R)) ⊎ ⊥)
  shift = mk↔ₛ′ [ ⊥-elim , inj₁ ∘′ assocʳ ]′ [ inj₂ ∘′ assocˡ , ⊥-elim ]′
                [ [ (λ _ → refl) , [ (λ _ → refl) , (λ _ → refl) ] ] , (λ ()) ]
                [ (λ ()) , [ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ] ]

  -- `σ ∘ (f ⊗₁ g)` and `(g ⊗₁ f) ∘ σ`
  braid : (⊥ ⊎ (P ⊎ Q)) ↔ ((Q ⊎ P) ⊎ ⊥)
  braid = mk↔ₛ′ [ ⊥-elim , inj₁ ∘′ swap ]′ [ inj₂ ∘′ swap , ⊥-elim ]′
                [ [ (λ _ → refl) , (λ _ → refl) ] , (λ ()) ]
                [ (λ ()) , [ (λ _ → refl) , (λ _ → refl) ] ]

  ¬² : ¬ (⊥ ⊎ ⊥)
  ¬² = [ (λ ()) , (λ ()) ]

open Inverse

⟦⟧[]-resp-≈ : {f g : HomTerm A B} → f ≈Term g
            → Σ[ π ∈ Occ f ↔ Occ g ] (∀ ι → ⟦ f ⟧[ ι ∘′ to π ] C.≈ ⟦ g ⟧[ ι ])
⟦⟧[]-resp-≈ idˡ              = ⊥⊎ , λ _ → C.identityˡ
⟦⟧[]-resp-≈ idʳ              = ⊎⊥ , λ _ → C.identityʳ
⟦⟧[]-resp-≈ assoc            = ⊎-assoc 0ℓ _ _ _ , λ _ → C.assoc
⟦⟧[]-resp-≈ (∘-resp-≈ p q) with ⟦⟧[]-resp-≈ p | ⟦⟧[]-resp-≈ q
... | π₁ , e₁ | π₂ , e₂ = ⊎-cong π₁ π₂ , λ ι → C.∘-resp-≈ (e₁ (ι ∘′ inj₁)) (e₂ (ι ∘′ inj₂))
⟦⟧[]-resp-≈ ≈-Term-refl      = ↔-refl , λ _ → C.Equiv.refl
⟦⟧[]-resp-≈ (≈-Term-sym {f = f} p) with ⟦⟧[]-resp-≈ p
... | π , e = ↔-sym π , λ ι →
  C.Equiv.sym (C.Equiv.trans (C.Equiv.reflexive (⟦⟧[]-cong f λ x → sym (cong ι (strictlyInverseʳ π x))))
                             (e (ι ∘′ from π)))
⟦⟧[]-resp-≈ (≈-Term-trans p q) with ⟦⟧[]-resp-≈ p | ⟦⟧[]-resp-≈ q
... | π₁ , e₁ | π₂ , e₂ = ↔-trans π₁ π₂ , λ ι → C.Equiv.trans (e₁ (ι ∘′ to π₂)) (e₂ ι)
⟦⟧[]-resp-≈ id⊗id≈id         = empty ¬² (λ ()) , λ _ → C.⊗.identity
⟦⟧[]-resp-≈ (⊗-resp-≈ p q) with ⟦⟧[]-resp-≈ p | ⟦⟧[]-resp-≈ q
... | π₁ , e₁ | π₂ , e₂ = ⊎-cong π₁ π₂ , λ ι → C.⊗.F-resp-≈ (e₁ (ι ∘′ inj₁) , e₂ (ι ∘′ inj₂))
⟦⟧[]-resp-≈ ⊗-∘-dist         = middle , λ _ → C.⊗.homomorphism
⟦⟧[]-resp-≈ λ⇐∘λ⇒≈id         = empty ¬² (λ ()) , λ _ → C.unitorˡ.isoˡ
⟦⟧[]-resp-≈ λ⇒∘λ⇐≈id         = empty ¬² (λ ()) , λ _ → C.unitorˡ.isoʳ
⟦⟧[]-resp-≈ ρ⇐∘ρ⇒≈id         = empty ¬² (λ ()) , λ _ → C.unitorʳ.isoˡ
⟦⟧[]-resp-≈ ρ⇒∘ρ⇐≈id         = empty ¬² (λ ()) , λ _ → C.unitorʳ.isoʳ
⟦⟧[]-resp-≈ α⇐∘α⇒≈id         = empty ¬² (λ ()) , λ _ → C.associator.isoˡ
⟦⟧[]-resp-≈ α⇒∘α⇐≈id         = empty ¬² (λ ()) , λ _ → C.associator.isoʳ
⟦⟧[]-resp-≈ λ⇒∘id⊗f≈f∘λ⇒     = unitˡ , λ _ → C.unitorˡ-commute-from
⟦⟧[]-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒     = unitʳ , λ _ → C.unitorʳ-commute-from
⟦⟧[]-resp-≈ α-comm           = shift , λ _ → C.assoc-commute-from
⟦⟧[]-resp-≈ triangle         = empty [ ¬² , (λ ()) ] ¬² , λ _ → C.triangle
⟦⟧[]-resp-≈ pentagon         = empty [ ¬² , [ (λ ()) , ¬² ] ] ¬² , λ _ → C.pentagon
⟦⟧[]-resp-≈ σ∘σ≈id           = empty ¬² (λ ()) , λ _ → C.commutative
⟦⟧[]-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ  = braid , λ _ → C.braiding.⇒.commute _
⟦⟧[]-resp-≈ hexagon          = empty [ ¬² , [ (λ ()) , ¬² ] ] [ (λ ()) , ¬² ] , λ _ → C.hexagon₁

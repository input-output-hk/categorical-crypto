{-# OPTIONS --safe --without-K #-}

-- Relabellings of choice sites and their SSP wires
-- (`docs/uc-setup-nondeterministic.md` §3.1).  A relabelling `ρ : S⃗ ⇝ T⃗`
-- routes each real site of `S⃗` to at most one ideal site of `T⃗`, injectively,
-- with a map of picks: a partial injection with fibre maps.  Relabellings form
-- `Alph`, and `_++ʳ_` sets two side by side.  `⌈ ρ ⌉ʳ` serves the real sites
-- by calling the ideal ones, ideal to real as a simulator runs: a pick on a
-- routed site is forwarded as `⌜ m ⌝` forwards a query, any other is answered
-- as `ack` answers (`⌈⌉ʳ-factor`), and no pick is ever originated.
-- `⌈−⌉ʳ : Alphᵒᵖ → Prot` is a functor.  SSP's wires never use injectivity; PM's
-- need it to route each request back statelessly.

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor.Core using (Functor)

open import Data.List.Base using (List; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective; map-∘)
open import Data.Maybe.Relation.Binary.Pointwise as Pointwise using (Pointwise; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Unit.Base
open import Function.Base using (case_of_; const; id; _∘_)
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category using (Prot)

module CategoricalCrypto.ND.Relabel where

private variable
  K P S X Y : Set
  F : K → Set
  S⃗ S⃗′ T⃗ T⃗′ U⃗ V⃗ : List Set

target : Maybe (Σ K F) → Maybe K
target = Maybe.map proj₁

private
  map-just⁻¹ : {f : X → Y} (m : Maybe X) {y : Y}
             → Maybe.map f m ≡ just y → Σ[ x ∈ X ] m ≡ just x × f x ≡ y
  map-just⁻¹ (just x) refl = x , refl , refl

------------------------------------------------------------------------
-- Relabellings
------------------------------------------------------------------------

infix 4 _⇝_

record _⇝_ (S⃗ T⃗ : List Set) : Set where
  field route     : (i : Ch Cᴵ⟦ S⃗ ⟧) → Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (Q Cᴵ⟦ S⃗ ⟧ i → Q Cᴵ⟦ T⃗ ⟧ k))
        injective : ∀ {i j k} → target (route i) ≡ just k → target (route j) ≡ just k → i ≡ j
open _⇝_ public

-- Follow a routed pick through a relabelling.
infixl 5 _▷_
_▷_ : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (P → Q Cᴵ⟦ T⃗ ⟧ k)) → T⃗ ⇝ U⃗ → Maybe (Σ[ l ∈ Ch Cᴵ⟦ U⃗ ⟧ ] (P → Q Cᴵ⟦ U⃗ ⟧ l))
nothing      ▷ ρ = nothing
just (k , r) ▷ ρ = Maybe.map (map₂ (_∘ r)) (route ρ k)

▷-inv : (x : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (P → Q Cᴵ⟦ T⃗ ⟧ k))) (ρ : T⃗ ⇝ U⃗) {l : Ch Cᴵ⟦ U⃗ ⟧}
      → target (x ▷ ρ) ≡ just l → Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] target x ≡ just k × target (route ρ k) ≡ just l
▷-inv nothing        ρ ()
▷-inv (just (k , r)) ρ e = k , refl , trans (map-∘ (route ρ k)) e

idʳ : S⃗ ⇝ S⃗
idʳ = record
  { route     = λ i → just (i , id)
  ; injective = λ e e′ → trans (just-injective e) (sym (just-injective e′)) }

infixr 9 _∘ʳ_
_∘ʳ_ : T⃗ ⇝ U⃗ → S⃗ ⇝ T⃗ → S⃗ ⇝ U⃗
ρ′ ∘ʳ ρ = record
  { route     = λ i → route ρ i ▷ ρ′
  ; injective = λ {i} {j} e e′ →
      let (k , eᵢ , eₖ) = ▷-inv (route ρ i) ρ′ e ; (k′ , eⱼ , eₖ′) = ▷-inv (route ρ j) ρ′ e′
      in injective ρ eᵢ (trans eⱼ (cong just (injective ρ′ eₖ′ eₖ))) }

infix 4 _≐_ _≈ʳ_

-- The same target, and pick maps equal pointwise.
data _≐_ {K P : Set} {F : K → Set} : Σ K (λ k → P → F k) → Σ K (λ k → P → F k) → Set where
  fibre : ∀ {k r r′} → (∀ p → r p ≡ r′ p) → (k , r) ≐ (k , r′)

≐-refl : {x : Σ K (λ k → P → F k)} → x ≐ x
≐-refl = fibre λ _ → refl

≐-sym : {x y : Σ K (λ k → P → F k)} → x ≐ y → y ≐ x
≐-sym (fibre e) = fibre λ p → sym (e p)

≐-trans : {x y z : Σ K (λ k → P → F k)} → x ≐ y → y ≐ z → x ≐ z
≐-trans (fibre e) (fibre e′) = fibre λ p → trans (e p) (e′ p)

record _≈ʳ_ (ρ ρ′ : S⃗ ⇝ T⃗) : Set where
  constructor mk≈ʳ
  field pointwise : ∀ i → Pointwise _≐_ (route ρ i) (route ρ′ i)
open _≈ʳ_ public

∘ʳ-identityˡ : (ρ : S⃗ ⇝ T⃗) → idʳ ∘ʳ ρ ≈ʳ ρ
∘ʳ-identityˡ {T⃗ = T⃗} ρ = mk≈ʳ go
  where
  go : ∀ i → Pointwise _≐_ (route ρ i ▷ idʳ {T⃗}) (route ρ i)
  go i with route ρ i
  ... | nothing = nothing
  ... | just _  = just ≐-refl

∘ʳ-identityʳ : (ρ : S⃗ ⇝ T⃗) → ρ ∘ʳ idʳ ≈ʳ ρ
∘ʳ-identityʳ ρ = mk≈ʳ go
  where
  go : ∀ i → Pointwise _≐_ (route (ρ ∘ʳ idʳ) i) (route ρ i)
  go i with route ρ i
  ... | nothing = nothing
  ... | just _  = just ≐-refl

∘ʳ-assoc : (ρ : S⃗ ⇝ T⃗) (ρ′ : T⃗ ⇝ U⃗) (ρ″ : U⃗ ⇝ V⃗) → (ρ″ ∘ʳ ρ′) ∘ʳ ρ ≈ʳ ρ″ ∘ʳ ρ′ ∘ʳ ρ
∘ʳ-assoc ρ ρ′ ρ″ = mk≈ʳ go
  where
  go : ∀ i → Pointwise _≐_ (route ((ρ″ ∘ʳ ρ′) ∘ʳ ρ) i) (route (ρ″ ∘ʳ ρ′ ∘ʳ ρ) i)
  go i with route ρ i
  ... | nothing      = nothing
  ... | just (k , _) with route ρ′ k
  ...   | nothing      = nothing
  ...   | just (l , _) with route ρ″ l
  ...     | nothing = nothing
  ...     | just _  = just ≐-refl

∘ʳ-resp-≈ʳ : {ρ₁ ρ₂ : T⃗ ⇝ U⃗} {ρ₁′ ρ₂′ : S⃗ ⇝ T⃗}
           → ρ₁ ≈ʳ ρ₂ → ρ₁′ ≈ʳ ρ₂′ → ρ₁ ∘ʳ ρ₁′ ≈ʳ ρ₂ ∘ʳ ρ₂′
∘ʳ-resp-≈ʳ {T⃗ = T⃗} {ρ₁ = ρ₁} {ρ₂} e e′ = mk≈ʳ λ i → go (pointwise e′ i)
  where
  go : {P : Set} {x y : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (P → Q Cᴵ⟦ T⃗ ⟧ k))}
     → Pointwise _≐_ x y → Pointwise _≐_ (x ▷ ρ₁) (y ▷ ρ₂)
  go nothing = nothing
  go (just (fibre {k} {r} {r′} h)) with route ρ₁ k | route ρ₂ k | pointwise e k
  ... | _ | _ | nothing                         = nothing
  ... | _ | _ | just (fibre {r = s} {s′} h′) = just (fibre λ p → trans (cong s (h p)) (h′ (r′ p)))

Alph : Category (suc 0ℓ) 0ℓ 0ℓ
Alph = categoryHelper record
  { Obj       = List Set
  ; _⇒_       = _⇝_
  ; _≈_       = _≈ʳ_
  ; id        = idʳ
  ; _∘_       = _∘ʳ_
  ; assoc     = λ {f = f} {g} {h} → ∘ʳ-assoc f g h
  ; identityˡ = λ {f = f} → ∘ʳ-identityˡ f
  ; identityʳ = λ {f = f} → ∘ʳ-identityʳ f
  ; equiv     = record
    { refl  = mk≈ʳ λ _ → Pointwise.refl ≐-refl
    ; sym   = λ e → mk≈ʳ λ i → Pointwise.sym ≐-sym (pointwise e i)
    ; trans = λ e e′ → mk≈ʳ λ i → Pointwise.trans ≐-trans (pointwise e i) (pointwise e′ i) }
  ; ∘-resp-≈  = ∘ʳ-resp-≈ʳ
  }

module _ {S⃗ T⃗ S⃗′ T⃗′ : List Set} (ρ : S⃗ ⇝ T⃗) (ρ′ : S⃗′ ⇝ T⃗′) where

  -- A site of the juxtaposition, by the side `split` puts it on.
  route-++ : (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧))
           → Maybe (Σ[ l ∈ Ch Cᴵ⟦ T⃗ ++ T⃗′ ⟧ ] (Q (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧) x → Q Cᴵ⟦ T⃗ ++ T⃗′ ⟧ l))
  route-++ (inj₁ i) =
    Maybe.map (λ (k , r) → ch (join T⃗ T⃗′) (inj₁ k) , qu (join T⃗ T⃗′) {inj₁ k} ∘ r) (route ρ i)
  route-++ (inj₂ j) =
    Maybe.map (λ (k , r) → ch (join T⃗ T⃗′) (inj₂ k) , qu (join T⃗ T⃗′) {inj₂ k} ∘ r) (route ρ′ j)

  private
    τ : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧) → Maybe (Ch (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗′ ⟧))
    τ (inj₁ i) = Maybe.map inj₁ (target (route ρ i))
    τ (inj₂ j) = Maybe.map inj₂ (target (route ρ′ j))

    target-route : (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧))
                 → target (route-++ x) ≡ Maybe.map (ch (join T⃗ T⃗′)) (τ x)
    target-route (inj₁ i) with route ρ i
    ... | nothing = refl
    ... | just _  = refl
    target-route (inj₂ j) with route ρ′ j
    ... | nothing = refl
    ... | just _  = refl

    from : ∀ {c l}
         → target (Maybe.map (map₂ (_∘ qu (split S⃗ S⃗′) {c})) (route-++ (ch (split S⃗ S⃗′) c))) ≡ just l
         → Maybe.map (ch (join T⃗ T⃗′)) (τ (ch (split S⃗ S⃗′) c)) ≡ just l
    from {c} e = trans (sym (target-route (ch (split S⃗ S⃗′) c)))
                       (trans (map-∘ (route-++ (ch (split S⃗ S⃗′) c))) e)

    τ-injective : ∀ {x x′ y} → τ x ≡ just y → τ x′ ≡ just y → x ≡ x′
    τ-injective {inj₁ i} {inj₁ i′} e e′ =
      let (k , eₖ , ek)    = map-just⁻¹ (target (route ρ i)) e
          (k′ , eₖ′ , ek′) = map-just⁻¹ (target (route ρ i′)) e′
      in cong inj₁ (injective ρ eₖ (trans eₖ′ (cong just (inj₁-injective (trans ek′ (sym ek))))))
    τ-injective {inj₂ j} {inj₂ j′} e e′ =
      let (k , eₖ , ek)    = map-just⁻¹ (target (route ρ′ j)) e
          (k′ , eₖ′ , ek′) = map-just⁻¹ (target (route ρ′ j′)) e′
      in cong inj₂ (injective ρ′ eₖ (trans eₖ′ (cong just (inj₂-injective (trans ek′ (sym ek))))))
    τ-injective {inj₁ i} {inj₂ j′} e e′ =
      let (_ , _ , ek)  = map-just⁻¹ (target (route ρ i)) e
          (_ , _ , ek′) = map-just⁻¹ (target (route ρ′ j′)) e′
      in case trans ek (sym ek′) of λ ()
    τ-injective {inj₂ j} {inj₁ i′} e e′ =
      let (_ , _ , ek)  = map-just⁻¹ (target (route ρ′ j)) e
          (_ , _ , ek′) = map-just⁻¹ (target (route ρ i′)) e′
      in case trans ek (sym ek′) of λ ()

  infixr 6 _++ʳ_
  _++ʳ_ : S⃗ ++ S⃗′ ⇝ T⃗ ++ T⃗′
  _++ʳ_ = record
    { route     = λ c → Maybe.map (map₂ (_∘ qu (split S⃗ S⃗′))) (route-++ (ch (split S⃗ S⃗′) c))
    ; injective = λ {c} {c′} e e′ →
        let (y , eτ , ey)    = map-just⁻¹ (τ (ch (split S⃗ S⃗′) c)) (from e)
            (y′ , eτ′ , ey′) = map-just⁻¹ (τ (ch (split S⃗ S⃗′) c′)) (from e′)
            y≡y′ = trans (sym (split-join T⃗ T⃗′ y))
                         (trans (cong (ch (split T⃗ T⃗′)) (trans ey (sym ey′))) (split-join T⃗ T⃗′ y′))
        in trans (sym (join-split S⃗ S⃗′ c))
                 (trans (cong (ch (join S⃗ S⃗′)) (τ-injective eτ (trans eτ′ (cong just (sym y≡y′)))))
                        (join-split S⃗ S⃗′ c′)) }

------------------------------------------------------------------------
-- The SSP wires
------------------------------------------------------------------------

ack : Protocol unitᴵ (Cᴵ S)
ack = record { St = ⊤ ; init = tt ; step = λ _ _ _ → ret (tt , tt) }

-- Forward a pick along its route, or answer it here.
forward : {B : Iface} → Y → Maybe (Σ[ k ∈ Ch B ] (P → Q B k)) → P → Calls B (⊤ × Y)
forward y nothing        p = ret (tt , y)
forward y (just (k , r)) p = call k (r p) λ _ → ret (tt , y)

⌈_⌉ʳ : S⃗ ⇝ T⃗ → Protocol Cᴵ⟦ T⃗ ⟧ Cᴵ⟦ S⃗ ⟧
⌈_⌉ʳ {S⃗} ρ = record { St = ⊤ ; init = tt ; step = λ _ i p → forward (tt⟦ S⃗ ⟧ i) (route ρ i) p }

-- `⌈ ρ ⌉ʳ` as a container wire routing every real site, the unrouted ones to
-- one absorbed site.
relabelᴵ : S⃗ ⇝ T⃗ → Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ ⊤
relabelᴵ {S⃗} {T⃗} ρ = record
  { ch = λ i → maybe′ (inj₁ ∘ proj₁) (inj₂ tt) (route ρ i)
  ; qu = λ {i} → pick (route ρ i)
  ; re = λ {i} _ → tt⟦ S⃗ ⟧ i }
  where
  pick : (x : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (P → Q Cᴵ⟦ T⃗ ⟧ k)))
       → P → Q (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ ⊤) (maybe′ (inj₁ ∘ proj₁) (inj₂ tt) x)
  pick nothing        _ = tt
  pick (just (k , r)) p = r p

⌈⌉ʳ-factor : (ρ : S⃗ ⇝ T⃗) → ⌈ ρ ⌉ʳ ≈ᵖ ⌜ relabelᴵ ρ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ack ∘ᵖ ⌜ ρᴵ ⌝
⌈⌉ʳ-factor {S⃗} {T⃗} ρ = ≲⇒≈ᵖ (≲ᵖ-const go)
  where
  go : ∀ s i p → mapᶜ (map₁ (const ((tt , tt , tt) , tt))) (step ⌈ ρ ⌉ʳ s i p)
                 ≈ᶜ step (⌜ relabelᴵ ρ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ack ∘ᵖ ⌜ ρᴵ ⌝) ((tt , tt , tt) , tt) i p
  go _ i p with route ρ i
  ... | nothing = ret refl
  ... | just _  = call λ _ → ret refl

-- A relabelling routing every site along a container map with a left inverse
-- on sites; its wire is the map's.
wireʳ : (m : Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧) (back : Ch Cᴵ⟦ T⃗ ⟧ → Ch Cᴵ⟦ S⃗ ⟧) → (∀ i → back (ch m i) ≡ i) → S⃗ ⇝ T⃗
wireʳ m back inv = record
  { route     = λ i → just (ch m i , qu m)
  ; injective = λ {i} {j} e e′ →
      trans (sym (inv i)) (trans (cong back (just-injective (trans e (sym e′)))) (inv j)) }

⌈⌉ʳ-wire : (m : Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧) (back : Ch Cᴵ⟦ T⃗ ⟧ → Ch Cᴵ⟦ S⃗ ⟧) (inv : ∀ i → back (ch m i) ≡ i)
         → ⌈ wireʳ {S⃗} {T⃗} m back inv ⌉ʳ ≲ᵖ ⌜ m ⌝
⌈⌉ʳ-wire {S⃗} m _ _ = ≲ᵖ-const λ _ i p → call λ r → ret (cong (tt ,_) (sym (tt⟦⟧-unique S⃗ (re m r))))

⌈⌉ʳ-id : ⌈ idʳ {S⃗} ⌉ʳ ≲ᵖ wireᵖ
⌈⌉ʳ-id {S⃗} = ≲ᵖ-const λ _ i p → call λ r → ret (cong (tt ,_) (sym (tt⟦⟧-unique S⃗ r)))

⌈⌉ʳ-∘ : (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗) → ⌈ ρ′ ∘ʳ ρ ⌉ʳ ≲ᵖ ⌈ ρ ⌉ʳ ∘ᵖ ⌈ ρ′ ⌉ʳ
⌈⌉ʳ-∘ {T⃗} {U⃗} {S⃗} ρ′ ρ = ≲ᵖ-const λ _ i p → go i p (route ρ i)
  where
  go : (i : Ch Cᴵ⟦ S⃗ ⟧) (p : Q Cᴵ⟦ S⃗ ⟧ i)
       (x : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (Q Cᴵ⟦ S⃗ ⟧ i → Q Cᴵ⟦ T⃗ ⟧ k)))
     → mapᶜ (map₁ (const (tt , tt))) (forward (tt⟦ S⃗ ⟧ i) (x ▷ ρ′) p)
       ≈ᶜ graft ⌈ ρ ⌉ʳ ⌈ ρ′ ⌉ʳ (forward (tt⟦ S⃗ ⟧ i) x p) tt
  go i p nothing        = ret refl
  go i p (just (k , r)) with route ρ′ k
  ... | nothing = ret refl
  ... | just _  = call λ _ → ret refl

⌈⌉ʳ-resp : {ρ ρ′ : S⃗ ⇝ T⃗} → ρ ≈ʳ ρ′ → ⌈ ρ ⌉ʳ ≲ᵖ ⌈ ρ′ ⌉ʳ
⌈⌉ʳ-resp {S⃗} {T⃗} e = ≲ᵖ-const λ _ i p → go {B = Cᴵ⟦ T⃗ ⟧} (tt⟦ S⃗ ⟧ i) p (pointwise e i)
  where
  go : {B : Iface} (y : Y) (p : P) {x x′ : Maybe (Σ[ k ∈ Ch B ] (P → Q B k))} → Pointwise _≐_ x x′
     → mapᶜ (map₁ (const tt)) (forward {B = B} y x p) ≈ᶜ forward y x′ p
  go y p nothing                       = ret refl
  go y p (just (fibre h)) rewrite h p = call λ _ → ret refl

⌈−⌉ʳ : Functor (Category.op Alph) Prot
⌈−⌉ʳ = record
  { F₀           = Cᴵ⟦_⟧
  ; F₁           = ⌈_⌉ʳ
  ; identity     = λ {S⃗} → ≲⇒≈ᵖ (⌈⌉ʳ-id {S⃗})
  ; homomorphism = λ {f = f} {g = g} → ≲⇒≈ᵖ (⌈⌉ʳ-∘ f g)
  ; F-resp-≈     = λ e → ≲⇒≈ᵖ (⌈⌉ʳ-resp e)
  }

-- `⌈−⌉ʳ` is monoidal: juxtaposed relabellings are wired side by side, between
-- the regroupings of `Choice`.
module _ {S⃗ T⃗ S⃗′ T⃗′ : List Set} (ρ : S⃗ ⇝ T⃗) (ρ′ : S⃗′ ⇝ T⃗′) where

  ⌈⌉ʳ-++ : ⌈ ρ ++ʳ ρ′ ⌉ʳ ≈ᵖ ⌜ split S⃗ S⃗′ ⌝ ∘ᵖ ⌈ ρ ⌉ʳ ⊗ᵖ ⌈ ρ′ ⌉ʳ ∘ᵖ ⌜ join T⃗ T⃗′ ⌝
  ⌈⌉ʳ-++ = ≲⇒≈ᵖ (≲ᵖ-const λ _ c p →
    go c p (ch (split S⃗ S⃗′) c) (qu (split S⃗ S⃗′) {c}) (re (split S⃗ S⃗′) {c}))
    where
    -- `split`'s routing of `c`, abstracted together with its pick and reply maps.
    go : (c : Ch Cᴵ⟦ S⃗ ++ S⃗′ ⟧) (p : Q Cᴵ⟦ S⃗ ++ S⃗′ ⟧ c) (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧))
         (g : Q Cᴵ⟦ S⃗ ++ S⃗′ ⟧ c → Q (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧) x)
         (h : R (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧) x → R Cᴵ⟦ S⃗ ++ S⃗′ ⟧ c)
       → mapᶜ (map₁ (const ((tt , tt , tt) , tt)))
              (forward (tt⟦ S⃗ ++ S⃗′ ⟧ c) (Maybe.map (map₂ (_∘ g)) (route-++ ρ ρ′ x)) p)
         ≈ᶜ graft (⌜ split S⃗ S⃗′ ⌝ ∘ᵖ ⌈ ρ ⌉ʳ ⊗ᵖ ⌈ ρ′ ⌉ʳ) ⌜ join T⃗ T⃗′ ⌝
              (graft ⌜ split S⃗ S⃗′ ⌝ (⌈ ρ ⌉ʳ ⊗ᵖ ⌈ ρ′ ⌉ʳ) (call x (g p) λ r → ret (tt , h r)) (tt , tt)) tt
    go c p (inj₁ i) g h with route ρ i
    ... | nothing = ret (cong (_ ,_) (sym (tt⟦⟧-unique (S⃗ ++ S⃗′) _)))
    ... | just _  = call λ _ → ret (cong (_ ,_) (sym (tt⟦⟧-unique (S⃗ ++ S⃗′) _)))
    go c p (inj₂ j) g h with route ρ′ j
    ... | nothing = ret (cong (_ ,_) (sym (tt⟦⟧-unique (S⃗ ++ S⃗′) _)))
    ... | just _  = call λ _ → ret (cong (_ ,_) (sym (tt⟦⟧-unique (S⃗ ++ S⃗′) _)))

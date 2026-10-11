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
-- (`ND.PM.Relabel`) route each request back statelessly along `preimage`.

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor.Core using (Functor)

open import Class.DecEq using (DecEq)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective; map-∘; ≡-dec)
open import Data.Maybe.Relation.Binary.Pointwise as Pointwise using (Pointwise; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Unit.Base
open import Function.Base using (case_of_; const; id; _∘_)
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)

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

▷-target : (x : Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (P → Q Cᴵ⟦ T⃗ ⟧ k))) (ρ : T⃗ ⇝ U⃗) {k : Ch Cᴵ⟦ T⃗ ⟧} {l : Ch Cᴵ⟦ U⃗ ⟧}
         → target x ≡ just k → target (route ρ k) ≡ just l → target (x ▷ ρ) ≡ just l
▷-target (just (k , r)) ρ refl e = trans (sym (map-∘ (route ρ k))) e

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

------------------------------------------------------------------------
-- Preimages
------------------------------------------------------------------------

private
  -- The first site passing a decidable test.
  first : (S⃗ : List Set) {R : Ch Cᴵ⟦ S⃗ ⟧ → Set} → (∀ j → Dec (R j)) → Maybe (Ch Cᴵ⟦ S⃗ ⟧)
  first []      _ = nothing
  first (S ∷ S⃗) d with d (inj₁ tt)
  ... | yes _ = just (inj₁ tt)
  ... | no  _ = Maybe.map inj₂ (first S⃗ (d ∘ inj₂))

  first-sound : (S⃗ : List Set) {R : Ch Cᴵ⟦ S⃗ ⟧ → Set} (d : ∀ j → Dec (R j)) {j : Ch Cᴵ⟦ S⃗ ⟧}
              → first S⃗ d ≡ just j → R j
  first-sound []      _ ()
  first-sound (S ∷ S⃗) {R} d e with d (inj₁ tt)
  first-sound (S ∷ S⃗) {R} d refl | yes r = r
  first-sound (S ∷ S⃗) {R} d e    | no _ with first S⃗ (d ∘ inj₂) in e′
  first-sound (S ∷ S⃗) {R} d refl | no _ | just i = first-sound S⃗ (d ∘ inj₂) e′
  first-sound (S ∷ S⃗) {R} d ()   | no _ | nothing

  first-complete : (S⃗ : List Set) {R : Ch Cᴵ⟦ S⃗ ⟧ → Set} (d : ∀ j → Dec (R j)) {j : Ch Cᴵ⟦ S⃗ ⟧}
                 → R j → Σ[ j′ ∈ Ch Cᴵ⟦ S⃗ ⟧ ] first S⃗ d ≡ just j′
  first-complete []      _ {()} _
  first-complete (S ∷ S⃗) d {inj₁ _} r with d (inj₁ tt)
  ... | yes _ = inj₁ tt , refl
  ... | no ¬r = ⊥-elim (¬r r)
  first-complete (S ∷ S⃗) d {inj₂ i} r with d (inj₁ tt)
  ... | yes _ = inj₁ tt , refl
  ... | no _  = let (i′ , e) = first-complete S⃗ (d ∘ inj₂) r in inj₂ i′ , cong (Maybe.map inj₂) e

  found : (ρ : S⃗ ⇝ T⃗) (k : Ch Cᴵ⟦ T⃗ ⟧) (j : Ch Cᴵ⟦ S⃗ ⟧) → Dec (target (route ρ j) ≡ just k)
  found {T⃗ = T⃗} ρ k j = ≡-dec (DecEq._≟_ (Ch-dec Cᴵ⟦ T⃗ ⟧)) (target (route ρ j)) (just k)

-- The real site routed to an ideal one, if any: PM's wires route a request back
-- along it, statelessly, by injectivity (`docs/uc-setup-nondeterministic.md` §3.1).
preimage : S⃗ ⇝ T⃗ → Ch Cᴵ⟦ T⃗ ⟧ → Maybe (Ch Cᴵ⟦ S⃗ ⟧)
preimage {S⃗} ρ k = first S⃗ (found ρ k)

preimage-sound : (ρ : S⃗ ⇝ T⃗) {k : Ch Cᴵ⟦ T⃗ ⟧} {j : Ch Cᴵ⟦ S⃗ ⟧}
               → preimage ρ k ≡ just j → target (route ρ j) ≡ just k
preimage-sound {S⃗} ρ {k} = first-sound S⃗ (found ρ k)

preimage-complete : (ρ : S⃗ ⇝ T⃗) {j : Ch Cᴵ⟦ S⃗ ⟧} {k : Ch Cᴵ⟦ T⃗ ⟧}
                  → target (route ρ j) ≡ just k → preimage ρ k ≡ just j
preimage-complete {S⃗} ρ {k = k} e =
  let (j′ , e′) = first-complete S⃗ (found ρ k) e in trans e′ (cong just (injective ρ (first-sound S⃗ (found ρ k) e′) e))

-- A preimage is the one candidate that is sound and complete.
preimage-≡ : (ρ : S⃗ ⇝ T⃗) {k : Ch Cᴵ⟦ T⃗ ⟧} {m : Maybe (Ch Cᴵ⟦ S⃗ ⟧)}
           → (∀ {j} → m ≡ just j → target (route ρ j) ≡ just k)
           → (∀ {j} → target (route ρ j) ≡ just k → m ≡ just j)
           → preimage ρ k ≡ m
preimage-≡ ρ {m = just j} sound _ = preimage-complete ρ (sound refl)
preimage-≡ ρ {k} {nothing} _ complete with preimage ρ k in e
... | nothing = refl
... | just j  = case complete (preimage-sound ρ e) of λ ()

preimage-id : (k : Ch Cᴵ⟦ S⃗ ⟧) → preimage (idʳ {S⃗}) k ≡ just k
preimage-id {S⃗} k = preimage-complete (idʳ {S⃗}) refl

preimage-∘ : (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗) (l : Ch Cᴵ⟦ U⃗ ⟧)
           → preimage (ρ′ ∘ʳ ρ) l ≡ (preimage ρ′ l Maybe.>>= preimage ρ)
preimage-∘ ρ′ ρ l = preimage-≡ (ρ′ ∘ʳ ρ) sound complete
  where
  sound : ∀ {j} → (preimage ρ′ l Maybe.>>= preimage ρ) ≡ just j → target (route (ρ′ ∘ʳ ρ) j) ≡ just l
  sound {j} e with preimage ρ′ l in e′
  ... | just k  = ▷-target (route ρ j) ρ′ (preimage-sound ρ e) (preimage-sound ρ′ e′)
  ... | nothing = case e of λ ()

  complete : ∀ {j} → target (route (ρ′ ∘ʳ ρ) j) ≡ just l → (preimage ρ′ l Maybe.>>= preimage ρ) ≡ just j
  complete {j} e = let (k , eᵢ , eₖ) = ▷-inv (route ρ j) ρ′ e in
    trans (cong (Maybe._>>= preimage ρ) (preimage-complete ρ′ eₖ)) (preimage-complete ρ eᵢ)

private
  target-≐ : {x y : Maybe (Σ K (λ k → P → F k))} → Pointwise _≐_ x y → target x ≡ target y
  target-≐ nothing          = refl
  target-≐ (just (fibre _)) = refl

preimage-resp : {ρ ρ′ : S⃗ ⇝ T⃗} → ρ ≈ʳ ρ′ → (k : Ch Cᴵ⟦ T⃗ ⟧) → preimage ρ k ≡ preimage ρ′ k
preimage-resp {ρ = ρ} {ρ′} e k = preimage-≡ ρ
  (λ {j} e′ → trans (target-≐ (pointwise e j)) (preimage-sound ρ′ e′))
  (λ {j} t → preimage-complete ρ′ (trans (sym (target-≐ (pointwise e j))) t))

------------------------------------------------------------------------
-- Picks
------------------------------------------------------------------------

-- A pick at a site, flat: what PM's wires carry down.
Pick : List Set → Set
Pick S⃗ = Σ (Ch Cᴵ⟦ S⃗ ⟧) (Q Cᴵ⟦ S⃗ ⟧)

-- A real pick, routed to its ideal site.
routePick : S⃗ ⇝ T⃗ → Pick S⃗ → Maybe (Pick T⃗)
routePick ρ (i , p) = Maybe.map (λ (k , r) → k , r p) (route ρ i)

routePick-∘ : (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗) (x : Pick S⃗) → routePick (ρ′ ∘ʳ ρ) x ≡ (routePick ρ x Maybe.>>= routePick ρ′)
routePick-∘ ρ′ ρ (i , p) with route ρ i
... | nothing      = refl
... | just (k , _) with route ρ′ k
...   | nothing = refl
...   | just _  = refl

routePick-resp : {ρ ρ′ : S⃗ ⇝ T⃗} → ρ ≈ʳ ρ′ → (x : Pick S⃗) → routePick ρ x ≡ routePick ρ′ x
routePick-resp {ρ = ρ} {ρ′} e (i , p) with route ρ i | route ρ′ i | pointwise e i
... | _ | _ | nothing        = refl
... | _ | _ | just (fibre h) = cong (λ q → just (_ , q)) (h p)

private
  Σ-⊎ : {A B : Set} {F : A → Set} {G : B → Set} → Σ (A ⊎ B) [ F , G ]′ → Σ A F ⊎ Σ B G
  Σ-⊎ (inj₁ a , u) = inj₁ (a , u)
  Σ-⊎ (inj₂ b , v) = inj₂ (b , v)

-- A pick of a concatenation, on the side `split` puts its site, and back.
splitPick : (S⃗ T⃗ : List Set) → Pick (S⃗ ++ T⃗) → Pick S⃗ ⊎ Pick T⃗
splitPick S⃗ T⃗ (c , p) = Σ-⊎ (ch (split S⃗ T⃗) c , qu (split S⃗ T⃗) p)

joinPick : (S⃗ T⃗ : List Set) → Pick S⃗ ⊎ Pick T⃗ → Pick (S⃗ ++ T⃗)
joinPick S⃗ T⃗ (inj₁ (i , p)) = ch (join S⃗ T⃗) (inj₁ i) , qu (join S⃗ T⃗) p
joinPick S⃗ T⃗ (inj₂ (j , p)) = ch (join S⃗ T⃗) (inj₂ j) , qu (join S⃗ T⃗) p

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

  private
    σ : Ch (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗′ ⟧) → Maybe (Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧))
    σ = [ Maybe.map inj₁ ∘ preimage ρ , Maybe.map inj₂ ∘ preimage ρ′ ]′

    σ-τ : (x : Ch (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗′ ⟧)) {y : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧)} → σ x ≡ just y → τ y ≡ just x
    σ-τ (inj₁ k) e with preimage ρ k in eₖ
    σ-τ (inj₁ k) refl | just _ = cong (Maybe.map inj₁) (preimage-sound ρ eₖ)
    σ-τ (inj₁ k) ()   | nothing
    σ-τ (inj₂ k) e with preimage ρ′ k in eₖ
    σ-τ (inj₂ k) refl | just _ = cong (Maybe.map inj₂) (preimage-sound ρ′ eₖ)
    σ-τ (inj₂ k) ()   | nothing

    τ-σ : (y : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧)) {x : Ch (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗′ ⟧)} → τ y ≡ just x → σ x ≡ just y
    τ-σ (inj₁ i) e with target (route ρ i) in eₖ
    τ-σ (inj₁ i) refl | just _ = cong (Maybe.map inj₁) (preimage-complete ρ eₖ)
    τ-σ (inj₁ i) ()   | nothing
    τ-σ (inj₂ j) e with target (route ρ′ j) in eₖ
    τ-σ (inj₂ j) refl | just _ = cong (Maybe.map inj₂) (preimage-complete ρ′ eₖ)
    τ-σ (inj₂ j) ()   | nothing

    target-++ : (c : Ch Cᴵ⟦ S⃗ ++ S⃗′ ⟧) → target (route _++ʳ_ c) ≡ Maybe.map (ch (join T⃗ T⃗′)) (τ (ch (split S⃗ S⃗′) c))
    target-++ c = trans (sym (map-∘ (route-++ (ch (split S⃗ S⃗′) c)))) (target-route (ch (split S⃗ S⃗′) c))

  preimage-++ : (l : Ch Cᴵ⟦ T⃗ ++ T⃗′ ⟧)
              → preimage _++ʳ_ l
                ≡ Maybe.map (ch (join S⃗ S⃗′)) ([ Maybe.map inj₁ ∘ preimage ρ , Maybe.map inj₂ ∘ preimage ρ′ ]′ (ch (split T⃗ T⃗′) l))
  preimage-++ l = preimage-≡ _++ʳ_ sound complete
    where
    open ≡-Reasoning

    sound : ∀ {c} → Maybe.map (ch (join S⃗ S⃗′)) (σ (ch (split T⃗ T⃗′) l)) ≡ just c → target (route _++ʳ_ c) ≡ just l
    sound e with map-just⁻¹ (σ (ch (split T⃗ T⃗′) l)) e
    ... | y , eσ , refl = begin
      target (route _++ʳ_ (ch (join S⃗ S⃗′) y))
        ≡⟨ target-++ _ ⟩
      Maybe.map (ch (join T⃗ T⃗′)) (τ (ch (split S⃗ S⃗′) (ch (join S⃗ S⃗′) y)))
        ≡⟨ cong (Maybe.map (ch (join T⃗ T⃗′)) ∘ τ) (split-join S⃗ S⃗′ y) ⟩
      Maybe.map (ch (join T⃗ T⃗′)) (τ y)
        ≡⟨ cong (Maybe.map (ch (join T⃗ T⃗′))) (σ-τ _ eσ) ⟩
      just (ch (join T⃗ T⃗′) (ch (split T⃗ T⃗′) l))
        ≡⟨ cong just (join-split T⃗ T⃗′ l) ⟩
      just l ∎

    complete : ∀ {c} → target (route _++ʳ_ c) ≡ just l → Maybe.map (ch (join S⃗ S⃗′)) (σ (ch (split T⃗ T⃗′) l)) ≡ just c
    complete {c} e with map-just⁻¹ (τ (ch (split S⃗ S⃗′) c)) (trans (sym (target-++ c)) e)
    ... | x , eτ , ex = begin
      Maybe.map (ch (join S⃗ S⃗′)) (σ (ch (split T⃗ T⃗′) l))
        ≡⟨ cong (Maybe.map (ch (join S⃗ S⃗′)) ∘ σ ∘ ch (split T⃗ T⃗′)) (sym ex) ⟩
      Maybe.map (ch (join S⃗ S⃗′)) (σ (ch (split T⃗ T⃗′) (ch (join T⃗ T⃗′) x)))
        ≡⟨ cong (Maybe.map (ch (join S⃗ S⃗′)) ∘ σ) (split-join T⃗ T⃗′ x) ⟩
      Maybe.map (ch (join S⃗ S⃗′)) (σ x)
        ≡⟨ cong (Maybe.map (ch (join S⃗ S⃗′))) (τ-σ _ eτ) ⟩
      just (ch (join S⃗ S⃗′) (ch (split S⃗ S⃗′) c))
        ≡⟨ cong just (join-split S⃗ S⃗′ c) ⟩
      just c ∎

  routePick-++ : (x : Pick (S⃗ ++ S⃗′))
               → routePick _++ʳ_ x
                 ≡ Maybe.map (joinPick T⃗ T⃗′) ([ Maybe.map inj₁ ∘ routePick ρ , Maybe.map inj₂ ∘ routePick ρ′ ]′ (splitPick S⃗ S⃗′ x))
  routePick-++ (c , p) = trans (sym (map-∘ (route-++ (ch (split S⃗ S⃗′) c)))) (go (ch (split S⃗ S⃗′) c) (qu (split S⃗ S⃗′) p))
    where
    -- `split`'s routing of the site, abstracted together with the pick.
    go : (y : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧)) (q : Q (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ S⃗′ ⟧) y)
       → Maybe.map (λ (l , r) → l , r q) (route-++ y)
         ≡ Maybe.map (joinPick T⃗ T⃗′) ([ Maybe.map inj₁ ∘ routePick ρ , Maybe.map inj₂ ∘ routePick ρ′ ]′ (Σ-⊎ (y , q)))
    go (inj₁ i) q with route ρ i
    ... | nothing = refl
    ... | just _  = refl
    go (inj₂ j) q with route ρ′ j
    ... | nothing = refl
    ... | just _  = refl

------------------------------------------------------------------------
-- Relabellings along container maps; the regroupings of a concatenation
------------------------------------------------------------------------

-- A relabelling routing every site along a container map with a left inverse
-- on sites; its SSP wire is the map's (`⌈⌉ʳ-wire`).
wireʳ : (m : Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧) (back : Ch Cᴵ⟦ T⃗ ⟧ → Ch Cᴵ⟦ S⃗ ⟧) → (∀ i → back (ch m i) ≡ i) → S⃗ ⇝ T⃗
wireʳ m back inv = record
  { route     = λ i → just (ch m i , qu m)
  ; injective = λ {i} {j} e e′ →
      trans (sym (inv i)) (trans (cong back (just-injective (trans e (sym e′)))) (inv j)) }

preimage-wireʳ : (m : Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧) (back : Ch Cᴵ⟦ T⃗ ⟧ → Ch Cᴵ⟦ S⃗ ⟧) (inv : ∀ i → back (ch m i) ≡ i)
               → (∀ k → ch m (back k) ≡ k) → (k : Ch Cᴵ⟦ T⃗ ⟧) → preimage (wireʳ {S⃗} {T⃗} m back inv) k ≡ just (back k)
preimage-wireʳ {S⃗} {T⃗} m back inv inv′ k = preimage-complete (wireʳ {S⃗} {T⃗} m back inv) (cong just (inv′ k))

unitʳᴵ : (S⃗ : List Set) → Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ++ [] ⟧
unitʳᴵ S⃗ = join S⃗ [] ∘ᴵ ι₁ {Cᴵ⟦ S⃗ ⟧} {unitᴵ}

unitʳᴵ⁻¹ : (S⃗ : List Set) → Cᴵ⟦ S⃗ ++ [] ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ⟧
unitʳᴵ⁻¹ S⃗ = ρᴵ {Cᴵ⟦ S⃗ ⟧} ∘ᴵ split S⃗ []

assocᴵ : (S⃗ T⃗ U⃗ : List Set) → Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧ ⇒ᴵ Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧
assocᴵ S⃗ T⃗ U⃗ = join (S⃗ ++ T⃗) U⃗ ∘ᴵ (join S⃗ T⃗ ⊗ᴵᴵ idᴵ) ∘ᴵ αᴵ⁻¹ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}
              ∘ᴵ (idᴵ ⊗ᴵᴵ split T⃗ U⃗) ∘ᴵ split S⃗ (T⃗ ++ U⃗)

assocᴵ⁻¹ : (S⃗ T⃗ U⃗ : List Set) → Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧
assocᴵ⁻¹ S⃗ T⃗ U⃗ = join S⃗ (T⃗ ++ U⃗) ∘ᴵ (idᴵ ⊗ᴵᴵ join T⃗ U⃗) ∘ᴵ αᴵ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}
                ∘ᴵ (split S⃗ T⃗ ⊗ᴵᴵ idᴵ) ∘ᴵ split (S⃗ ++ T⃗) U⃗

private
  map-inv : {A B C D : Set} {f : A → B} (g : B → A) {h : C → D} (k : D → C)
          → (∀ a → g (f a) ≡ a) → (∀ c → k (h c) ≡ c) → ∀ x → Sum.map g k (Sum.map f h x) ≡ x
  map-inv g k p q (inj₁ a) = cong inj₁ (p a)
  map-inv g k p q (inj₂ c) = cong inj₂ (q c)

  assocʳˡ : {A B C : Set} (x : A ⊎ B ⊎ C) → Sum.assocʳ (Sum.assocˡ x) ≡ x
  assocʳˡ (inj₁ _)        = refl
  assocʳˡ (inj₂ (inj₁ _)) = refl
  assocʳˡ (inj₂ (inj₂ _)) = refl

  assocˡʳ : {A B C : Set} (x : (A ⊎ B) ⊎ C) → Sum.assocˡ (Sum.assocʳ x) ≡ x
  assocˡʳ (inj₁ (inj₁ _)) = refl
  assocˡʳ (inj₁ (inj₂ _)) = refl
  assocˡʳ (inj₂ _)        = refl

unitʳ-inv : (S⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) → ch (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗) i) ≡ i
unitʳ-inv S⃗ i = cong [ id , ⊥-elim ]′ (split-join S⃗ [] (inj₁ i))

unitʳ⁻¹-inv : (S⃗ : List Set) (c : Ch Cᴵ⟦ S⃗ ++ [] ⟧) → ch (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗) c) ≡ c
unitʳ⁻¹-inv S⃗ c = trans (cong (ch (join S⃗ [])) (unρ (ch (split S⃗ []) c))) (join-split S⃗ [] c)
  where
  unρ : (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ unitᴵ)) → inj₁ ([ id , ⊥-elim ]′ x) ≡ x
  unρ (inj₁ _) = refl
  unρ (inj₂ ())

assoc-inv : (S⃗ T⃗ U⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧) → ch (assocᴵ⁻¹ S⃗ T⃗ U⃗) (ch (assocᴵ S⃗ T⃗ U⃗) i) ≡ i
assoc-inv S⃗ T⃗ U⃗ i =
  trans (cong (λ x → j₄ (Sum.map id j₃ (Sum.assocʳ (Sum.map s₁ id x)))) (split-join (S⃗ ++ T⃗) U⃗ y₂))
 (trans (cong (λ x → j₄ (Sum.map id j₃ (Sum.assocʳ x))) (map-inv s₁ id (split-join S⃗ T⃗) (λ _ → refl) y₃))
 (trans (cong (λ x → j₄ (Sum.map id j₃ x)) (assocʳˡ y₄))
 (trans (cong j₄ (map-inv id j₃ (λ _ → refl) (join-split T⃗ U⃗) (s₄ i))) (join-split S⃗ (T⃗ ++ U⃗) i))))
  where
  s₁ = ch (split S⃗ T⃗)
  s₄ = ch (split S⃗ (T⃗ ++ U⃗))
  j₃ = ch (join T⃗ U⃗)
  j₄ = ch (join S⃗ (T⃗ ++ U⃗))
  y₄ = Sum.map id (ch (split T⃗ U⃗)) (s₄ i)
  y₃ = Sum.assocˡ y₄
  y₂ = Sum.map (ch (join S⃗ T⃗)) id y₃

assoc⁻¹-inv : (S⃗ T⃗ U⃗ : List Set) (c : Ch Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧)
            → ch (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗) c) ≡ c
assoc⁻¹-inv S⃗ T⃗ U⃗ c =
  trans (cong (λ x → j₂ (Sum.map j₁ id (Sum.assocˡ (Sum.map id s₃ x)))) (split-join S⃗ (T⃗ ++ U⃗) z₂))
 (trans (cong (λ x → j₂ (Sum.map j₁ id (Sum.assocˡ x))) (map-inv id s₃ (λ _ → refl) (split-join T⃗ U⃗) z₃))
 (trans (cong (λ x → j₂ (Sum.map j₁ id x)) (assocˡʳ z₄))
 (trans (cong j₂ (map-inv j₁ id (join-split S⃗ T⃗) (λ _ → refl) (s₂ c))) (join-split (S⃗ ++ T⃗) U⃗ c))))
  where
  j₁ = ch (join S⃗ T⃗)
  j₂ = ch (join (S⃗ ++ T⃗) U⃗)
  s₂ = ch (split (S⃗ ++ T⃗) U⃗)
  s₃ = ch (split T⃗ U⃗)
  z₄ = Sum.map (ch (split S⃗ T⃗)) id (s₂ c)
  z₃ = Sum.assocʳ z₄
  z₂ = Sum.map id (ch (join T⃗ U⃗)) z₃

unit⇒ʳ : (S⃗ : List Set) → S⃗ ⇝ S⃗ ++ []
unit⇒ʳ S⃗ = wireʳ (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗)) (unitʳ-inv S⃗)

unit⇐ʳ : (S⃗ : List Set) → S⃗ ++ [] ⇝ S⃗
unit⇐ʳ S⃗ = wireʳ (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗)) (unitʳ⁻¹-inv S⃗)

assoc⇒ʳ : (S⃗ T⃗ U⃗ : List Set) → S⃗ ++ (T⃗ ++ U⃗) ⇝ (S⃗ ++ T⃗) ++ U⃗
assoc⇒ʳ S⃗ T⃗ U⃗ = wireʳ (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗)) (assoc-inv S⃗ T⃗ U⃗)

assoc⇐ʳ : (S⃗ T⃗ U⃗ : List Set) → (S⃗ ++ T⃗) ++ U⃗ ⇝ S⃗ ++ (T⃗ ++ U⃗)
assoc⇐ʳ S⃗ T⃗ U⃗ = wireʳ (assocᴵ⁻¹ S⃗ T⃗ U⃗) (ch (assocᴵ S⃗ T⃗ U⃗)) (assoc⁻¹-inv S⃗ T⃗ U⃗)

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

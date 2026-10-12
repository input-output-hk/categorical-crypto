{-# OPTIONS --safe --without-K --guardedness #-}

-- A run may extend its message relation after accepting an input. Projections
-- therefore act on the world, state and pending letter together, rather than
-- independently on a fixed interface. All projections below are functions.

module CategoricalCrypto.Machines.Sim.RunFollowing
  (World : Set) (initial : World) (_≤ʷ_ : World → World → Set)
  (reflʷ : ∀ {w} → w ≤ʷ w)
  (transʷ : ∀ {w w′ w″} → w ≤ʷ w′ → w′ ≤ʷ w″ → w ≤ʷ w″) where

import Categories.Category.Monoidal.Distributive as MD

open import Data.Bool.Base
open import Data.Product
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Transfer
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base using (distₚ)
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.Machines.Sandwich using (sandwichᴹ)
open import CategoricalCrypto.UC.Machine using (initˢ)

import CategoricalCrypto.Machines.Collapse as Col

open MD.MonoidalDistributive (distₚ 0ℓ) using (_+₁_)

private
  sum-pure : {A B C D : Set} {f : A → B} {g : C → D}
    → V._≈_ (K.pureᵏ f +₁ K.pureᵏ g) (K.pureᵏ (Sum.map f g))
  sum-pure = +₁-pureᵏ V.Equiv.refl V.Equiv.refl

  mapped-point : {A B C D : Set} {f : MC.Machine A B} {g : MC.Machine C D}
    {μ : A → C} {ν : B → D} (s : f RS.≲[ K.pureᵏ μ ∣ K.pureᵏ ν ] g)
    (h : MC.St f → MC.St g) → V._≈_ (RS.leg s) (K.pureᵏ h)
    → mapₚ h (MC.point (MC.state f) ttᵛ) ≈ₚ MC.point (MC.state g) ttᵛ
  mapped-point s h e = bindᶠ (λ x → ≈sym (e x)) ⟨≈⟩ RS.leg-point s ttᵛ

  mapped-step : {A B C D : Set} {f : MC.Machine A B} {g : MC.Machine C D}
    {μ : A → C} {ν : B → D} (s : f RS.≲[ K.pureᵏ μ ∣ K.pureᵏ ν ] g)
    (h : MC.St f → MC.St g) → V._≈_ (RS.leg s) (K.pureᵏ h)
    → ∀ sx → mapₚ (Data.Product.map h ν) (MC.step f sx) ≈ₚ MC.step g (h (proj₁ sx) , μ (proj₂ sx))
  mapped-step {g = g} {μ = μ} {ν} s h e sx =
    bindᶠ (λ sy → ≈sym (pad ν sy))
    ⟨≈⟩ RS.leg-step s sx
    ⟨≈⟩ bindˣ (pad μ sx)
    ⟨≈⟩ >>=ₚ-identityˡ _ _
    where
    pad : {A B : Set} (v : A → B) (sx : _ × A)
      → (RS.leg s V.⊗₁ K.pureᵏ v) sx ≈ₚ returnₚ (h (proj₁ sx) , v (proj₂ sx))
    pad v sx = V.⊗.F-resp-≈ {f = RS.leg s , K.pureᵏ v} {g = K.pureᵏ h , K.pureᵏ v}
      (e , V.Equiv.refl) sx ⟨≈⟩ K.pureᵏ-⊗ h v sx

record Letters : Set₁ where
  field
    Base : Set
    Related : World → Set
    project : (b : Bool) (w : World) → Related w → Base
open Letters public

infixr 5 _⊎ᴸ_
_⊎ᴸ_ : Letters → Letters → Letters
X ⊎ᴸ Y = record
  { Base = Base X ⊎ Base Y
  ; Related = λ w → Related X w ⊎ Related Y w
  ; project = λ b w → Sum.map (project X b w) (project Y b w) }

private variable
  X Y Z L : Letters
  w w′ : World

record Turn (State : World → Set) (Output : World → Set) (origin : World) : Set where
  constructor turn
  field
    world : World
    advances : origin ≤ʷ world
    state : State world
    output : Output world
open Turn public

record Stable (X Y : Letters) (p : Bool → MC.Machine (Base X) (Base Y)) : Set₁ where
  field
    State : World → Set
    project-state : ∀ b w → State w → MC.St (p b)
    point : ∀ w → Dₚ (State w)
    point-law : ∀ b w → mapₚ (project-state b w) (point w) ≈ₚ MC.point (MC.state (p b)) ttᵛ
    act : ∀ w → State w × Related X w → Dₚ (State w × Related Y w)
    act-law : ∀ b w s x → mapₚ (Data.Product.map (project-state b w) (project Y b w)) (act w (s , x))
      ≈ₚ MC.step (p b) (project-state b w s , project X b w x)
    promote : w ≤ʷ w′ → State w → State w′
    promote-law : ∀ b (e : w ≤ʷ w′) s → project-state b w′ (promote e s) ≡ project-state b w s

record Following (X Y : Letters) (p : Bool → MC.Machine (Base X) (Base Y)) : Set₁ where
  field
    State : World → Set
    project-state : ∀ b w → State w → MC.St (p b)
    point : Dₚ (State initial)
    point-law : ∀ b → mapₚ (project-state b initial) point ≈ₚ MC.point (MC.state (p b)) ttᵛ
    act : ∀ w → State w × Related X w → Dₚ (Turn State (Related Y) w)
    act-law : ∀ b w s x → mapₚ (λ t → project-state b (world t) (state t) , project Y b (world t) (output t))
      (act w (s , x)) ≈ₚ MC.step (p b) (project-state b w s , project X b w x)

stable-following : {p : Bool → MC.Machine (Base X) (Base Y)} → Stable X Y p → Following X Y p
stable-following q = record
  { State = Q.State ; project-state = Q.project-state
  ; point = Q.point initial ; point-law = λ b → Q.point-law b initial
  ; act = λ w sx → mapₚ (λ sy → turn w reflʷ (proj₁ sy) (proj₂ sy)) (Q.act w sx)
  ; act-law = λ b w s x → map-map (Q.act w (s , x)) _ _ ⟨≈⟩ Q.act-law b w s x }
  where module Q = Stable q

module _ {p : Bool → MC.Machine (Base X) (Base Y)} (q : Stable X Y p) where
  private module Q = Stable q

  stable-machine : ∀ w → MC.Machine (Related X w) (Related Y w)
  stable-machine w = MC.mk record { obj = Q.State w ; point = λ _ → Q.point w } (Q.act w)

  stable-leg : ∀ b w → stable-machine w RS.≲[ K.pureᵏ (project X b w) ∣ K.pureᵏ (project Y b w) ] p b
  stable-leg b w = simFn[] (Q.project-state b w) (project X b w) (project Y b w)
    (λ _ → Q.point-law b w) λ (s , x) → Q.act-law b w s x

module _ {p : Bool → MC.Machine (Base X) (Base Y)} {r : Bool → MC.Machine (Base Y) (Base Z)}
  (g : Stable Y Z r) (f : Stable X Y p) where
  private
    module F = Stable f
    module G = Stable g
    sim : ∀ b w → (stable-machine g w MC.∘ᴹ stable-machine f w)
      RS.≲[ K.pureᵏ (project X b w) ∣ K.pureᵏ (project Z b w) ] (r b MC.∘ᴹ p b)
    sim b w = RS.∘ᴹ-resp-≲[] (stable-leg g b w) (stable-leg f b w)

  opaque
    unfolding MC._∘ᴹ_ RS.∘ᴹ-resp-≲[]

    stable-compose : Stable X Z (λ b → r b MC.∘ᴹ p b)
    stable-compose = record
      { State = λ w → G.State w × F.State w
      ; project-state = λ b w → Data.Product.map (G.project-state b w) (F.project-state b w)
      ; point = λ w → MC.point (MC.state (stable-machine g w MC.∘ᴹ stable-machine f w)) ttᵛ
      ; point-law = λ b w → mapped-point (sim b w) _ (K.pureᵏ-⊗ _ _)
      ; act = λ w → MC.step (stable-machine g w MC.∘ᴹ stable-machine f w)
      ; act-law = λ b w s x → mapped-step (sim b w) _ (K.pureᵏ-⊗ _ _) (s , x)
      ; promote = λ e → Data.Product.map (G.promote e) (F.promote e)
      ; promote-law = λ b e (sg , sf) → cong₂ _,_ (G.promote-law b e sg) (F.promote-law b e sf) }

module _ {A B C D : Letters} {p : Bool → MC.Machine (Base A) (Base B)} {r : Bool → MC.Machine (Base C) (Base D)}
  (f : Stable A B p) (g : Stable C D r) where
  private
    module F = Stable f
    module G = Stable g
    sim : ∀ b w → (stable-machine f w T.⊗ᵉ stable-machine g w)
      RS.≲[ K.pureᵏ (project (A ⊎ᴸ C) b w) ∣ K.pureᵏ (project (B ⊎ᴸ D) b w) ] (p b T.⊗ᵉ r b)
    sim b w = RS.≲[]-resp-≈ sum-pure sum-pure (RS.⊗ᵉ-resp-≲[] (stable-leg f b w) (stable-leg g b w))

  stable-events : Stable (A ⊎ᴸ C) (B ⊎ᴸ D) (λ b → p b T.⊗ᵉ r b)
  stable-events = record
    { State = λ w → F.State w × G.State w
    ; project-state = λ b w → Data.Product.map (F.project-state b w) (G.project-state b w)
    ; point = λ w → MC.point (MC.state (stable-machine f w T.⊗ᵉ stable-machine g w)) ttᵛ
    ; point-law = λ b w → mapped-point (sim b w) _ (K.pureᵏ-⊗ _ _)
    ; act = λ w → MC.step (stable-machine f w T.⊗ᵉ stable-machine g w)
    ; act-law = λ b w s x → mapped-step (sim b w) _ (K.pureᵏ-⊗ _ _) (s , x)
    ; promote = λ e → Data.Product.map (F.promote e) (G.promote e)
    ; promote-law = λ b e (sf , sg) → cong₂ _,_ (F.promote-law b e sf) (G.promote-law b e sg) }

module _ {p : Bool → MC.Machine (Base X ⊎ Base L) (Base Y ⊎ Base L)}
  (q : Stable (X ⊎ᴸ L) (Y ⊎ᴸ L) p) where
  private
    module Q = Stable q
    sim : ∀ b w → Col.MT.traceᴹ (Related X w) (Related Y w) (Related L w) (stable-machine q w)
      RS.≲[ K.pureᵏ (project X b w) ∣ K.pureᵏ (project Y b w) ]
      Col.MT.traceᴹ (Base X) (Base Y) (Base L) (p b)
    sim b w = RS.trace-resp-≲[] (KP.structural _) (KP.structural _) (KP.structural _)
      (RS.≲[]-resp-≈ (λ z → ≈sym (sum-pure z)) (λ z → ≈sym (sum-pure z)) (stable-leg q b w))

  trace-stable : Stable X Y (λ b → Col.MT.traceᴹ (Base X) (Base Y) (Base L) (p b))
  trace-stable = record
    { State = Q.State ; project-state = Q.project-state
    ; point = Q.point ; point-law = Q.point-law
    ; act = λ w → MC.step (Col.MT.traceᴹ (Related X w) (Related Y w) (Related L w) (stable-machine q w))
    ; act-law = λ b w s x → mapped-step (sim b w) _ (λ _ → ≈refl) (s , x)
    ; promote = Q.promote ; promote-law = Q.promote-law }

pure-stable : (h : Bool → Base X → Base Y) (r : ∀ w → Related X w → Related Y w)
  → (∀ b w x → project Y b w (r w x) ≡ h b (project X b w x))
  → Stable X Y (λ b → pureᶠ (h b))
pure-stable {X = X} h r natural = record
  { State = λ _ → V.unit ; project-state = λ _ _ s → s
  ; point = λ _ → returnₚ ttᵛ ; point-law = λ _ _ → >>=ₚ-identityʳ _
  ; act = λ w (s , x) → returnₚ (s , r w x)
  ; act-law = λ b w s x → >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (cong (s ,_) (natural b w x))
    ⟨≈⟩ ≈sym (pureᴵ (h b) (s , project X b w x))
  ; promote = λ _ s → s ; promote-law = λ _ _ _ → refl }

module _ {A B C D : Letters} {p : Bool → MC.Machine (Base A) (Base B)}
  (i : Bool → Base C → Base A) (o : Bool → Base B → Base D)
  (ri : ∀ w → Related C w → Related A w) (ro : ∀ w → Related B w → Related D w)
  (ei : ∀ b w x → project A b w (ri w x) ≡ i b (project C b w x))
  (eo : ∀ b w y → project D b w (ro w y) ≡ o b (project B b w y)) where

  sandwich-stable : Stable A B p → Stable C D (λ b → sandwichᴹ (p b) (i b) (o b))
  sandwich-stable q = record
    { State = Q.State ; project-state = Q.project-state
    ; point = Q.point ; point-law = Q.point-law
    ; act = λ w sx → mapₚ (λ sy → proj₁ sy , ro w (proj₂ sy)) (Q.act w (proj₁ sx , ri w (proj₂ sx)))
    ; act-law = λ b w s x →
        map-map (Q.act w (s , ri w x)) _ _
        ⟨≈⟩ map-eq (Q.act w (s , ri w x)) _ _
          (λ sy → cong (Q.project-state b w (proj₁ sy) ,_) (eo b w (proj₂ sy)))
        ⟨≈⟩ ≈sym (map-map (Q.act w (s , ri w x)) _ _)
        ⟨≈⟩ map-arg _ (Q.act-law b w s (ri w x))
        ⟨≈⟩ map-arg _ (ret≡-step b w s x)
    ; promote = Q.promote ; promote-law = Q.promote-law }
    where
    module Q = Stable q
    ret≡-step : ∀ b w s x → MC.step (p b) (Q.project-state b w s , project A b w (ri w x))
      ≈ₚ MC.step (p b) (Q.project-state b w s , i b (project C b w x))
    ret≡-step b w s x = ≡⇒≈ₚ (cong (MC.step (p b) ∘ (Q.project-state b w s ,_)) (ei b w x))

  sandwich-following : Following A B p → Following C D (λ b → sandwichᴹ (p b) (i b) (o b))
  sandwich-following q = record
    { State = Q.State ; project-state = Q.project-state
    ; point = Q.point ; point-law = Q.point-law
    ; act = λ w sx → mapₚ (λ t → turn (world t) (advances t) (state t) (ro (world t) (output t)))
        (Q.act w (proj₁ sx , ri w (proj₂ sx)))
    ; act-law = λ b w s x →
        map-map (Q.act w (s , ri w x)) _ _
        ⟨≈⟩ map-eq (Q.act w (s , ri w x)) _ _
          (λ t → cong (Q.project-state b (world t) (state t) ,_) (eo b (world t) (output t)))
        ⟨≈⟩ ≈sym (map-map (Q.act w (s , ri w x)) _ _)
        ⟨≈⟩ map-arg _ (Q.act-law b w s (ri w x))
        ⟨≈⟩ map-arg _ (≡⇒≈ₚ (cong (MC.step (p b) ∘ (Q.project-state b w s ,_)) (ei b w x))) }
    where module Q = Following q

private
  pair-point : {A B : MC.State} {S T : Set} (d : Dₚ S) (e : Dₚ T)
    (h : S → MC.obj A) (k : T → MC.obj B)
    → mapₚ h d ≈ₚ MC.point A ttᵛ → mapₚ k e ≈ₚ MC.point B ttᵛ
    → mapₚ (Data.Product.map h k) (d >>=ₚ λ s → e >>=ₚ λ t → returnₚ (s , t))
      ≈ₚ MC.point (A MC.⊛ B) ttᵛ
  pair-point {A} {B} d e h k hd he =
    map-bind d _ _
    ⟨≈⟩ bindᶠ (λ s → map-bind e _ _ ⟨≈⟩ bindᶠ (λ t → >>=ₚ-identityˡ _ _)
      ⟨≈⟩ ≈sym (bind-map e k (λ t → returnₚ (h s , t))) ⟨≈⟩ bindˣ he)
    ⟨≈⟩ ≈sym (bind-map d h (λ s → MC.point B ttᵛ >>=ₚ λ t → returnₚ (s , t)))
    ⟨≈⟩ bindˣ hd ⟨≈⟩ ≈sym (point-⊛ A B ttᵛ)

  event-left : {A B C D : Set} (f : MC.Machine A B) (g : MC.Machine C D) → ∀ sf sg x
    → MC.step (f T.⊗ᵉ g) ((sf , sg) , inj₁ x)
      ≈ₚ mapₚ (λ sy → (proj₁ sy , sg) , inj₁ (proj₂ sy)) (MC.step f (sf , x))
  event-left f g sf sg x = tstep-inj₁ _ _ (sf , sg) x ⟨≈⟩ bindˣ (onL-pt (MC.step f) sf sg x)
    ⟨≈⟩ bind-map (MC.step f (sf , x)) _ _

  event-right : {A B C D : Set} (f : MC.Machine A B) (g : MC.Machine C D) → ∀ sf sg x
    → MC.step (f T.⊗ᵉ g) ((sf , sg) , inj₂ x)
      ≈ₚ mapₚ (λ sy → (sf , proj₁ sy) , inj₂ (proj₂ sy)) (MC.step g (sg , x))
  event-right f g sf sg x = tstep-inj₂ _ _ (sf , sg) x ⟨≈⟩ bindˣ (onR-pt (MC.step g) sf sg x)
    ⟨≈⟩ bind-map (MC.step g (sg , x)) _ _

module _ {A B C D : Letters} {p : Bool → MC.Machine (Base A) (Base B)} {r : Bool → MC.Machine (Base C) (Base D)}
  (f : Stable A B p) (g : Following C D r) where
  private
    module F = Stable f
    module G = Following g

    State : World → Set
    State w = F.State w × G.State w

    act : ∀ w → State w × Related (A ⊎ᴸ C) w → Dₚ (Turn State (Related (B ⊎ᴸ D)) w)
    act w ((sf , sg) , inj₁ a) = mapₚ (λ sy → turn w reflʷ (proj₁ sy , sg) (inj₁ (proj₂ sy))) (F.act w (sf , a))
    act w ((sf , sg) , inj₂ c) = mapₚ (λ t → turn (world t) (advances t) (F.promote (advances t) sf , state t) (inj₂ (output t)))
      (G.act w (sg , c))

    act-law : ∀ b w sf sg x → mapₚ
      (λ t → (F.project-state b (world t) (proj₁ (state t)) , G.project-state b (world t) (proj₂ (state t)))
               , project (B ⊎ᴸ D) b (world t) (output t)) (act w ((sf , sg) , x))
      ≈ₚ MC.step (p b T.⊗ᵉ r b) ((F.project-state b w sf , G.project-state b w sg) , project (A ⊎ᴸ C) b w x)
    act-law b w sf sg (inj₁ a) =
      map-map (F.act w (sf , a)) _ _
      ⟨≈⟩ ≈sym (map-map (F.act w (sf , a)) _ _)
      ⟨≈⟩ map-arg _ (F.act-law b w sf a)
      ⟨≈⟩ ≈sym (event-left (p b) (r b) (F.project-state b w sf) (G.project-state b w sg) (project A b w a))
    act-law b w sf sg (inj₂ c) =
      map-map (G.act w (sg , c)) _ _
      ⟨≈⟩ map-eq (G.act w (sg , c)) _ _
        (λ t → cong (λ z → (z , G.project-state b (world t) (state t)) , inj₂ (project D b (world t) (output t)))
          (F.promote-law b (advances t) sf))
      ⟨≈⟩ ≈sym (map-map (G.act w (sg , c)) _ _)
      ⟨≈⟩ map-arg _ (G.act-law b w sg c)
      ⟨≈⟩ ≈sym (event-right (p b) (r b) (F.project-state b w sf) (G.project-state b w sg) (project C b w c))

  events-following-right : Following (A ⊎ᴸ C) (B ⊎ᴸ D) (λ b → p b T.⊗ᵉ r b)
  events-following-right = record
    { State = State
    ; project-state = λ b w → Data.Product.map (F.project-state b w) (G.project-state b w)
    ; point = F.point initial >>=ₚ λ sf → G.point >>=ₚ λ sg → returnₚ (sf , sg)
    ; point-law = λ b → pair-point (F.point initial) G.point _ _ (F.point-law b initial) (G.point-law b)
    ; act = act ; act-law = λ b w (sf , sg) x → act-law b w sf sg x }

module _ {A B C D : Letters} {p : Bool → MC.Machine (Base A) (Base B)} {r : Bool → MC.Machine (Base C) (Base D)}
  (f : Following A B p) (g : Stable C D r) where
  private
    module F = Following f
    module G = Stable g

    State : World → Set
    State w = F.State w × G.State w

    act : ∀ w → State w × Related (A ⊎ᴸ C) w → Dₚ (Turn State (Related (B ⊎ᴸ D)) w)
    act w ((sf , sg) , inj₁ a) = mapₚ (λ t → turn (world t) (advances t) (state t , G.promote (advances t) sg) (inj₁ (output t)))
      (F.act w (sf , a))
    act w ((sf , sg) , inj₂ c) = mapₚ (λ sy → turn w reflʷ (sf , proj₁ sy) (inj₂ (proj₂ sy))) (G.act w (sg , c))

    act-law : ∀ b w sf sg x → mapₚ
      (λ t → (F.project-state b (world t) (proj₁ (state t)) , G.project-state b (world t) (proj₂ (state t)))
               , project (B ⊎ᴸ D) b (world t) (output t)) (act w ((sf , sg) , x))
      ≈ₚ MC.step (p b T.⊗ᵉ r b) ((F.project-state b w sf , G.project-state b w sg) , project (A ⊎ᴸ C) b w x)
    act-law b w sf sg (inj₁ a) =
      map-map (F.act w (sf , a)) _ _
      ⟨≈⟩ map-eq (F.act w (sf , a)) _ _
        (λ t → cong (λ z → (F.project-state b (world t) (state t) , z) , inj₁ (project B b (world t) (output t)))
          (G.promote-law b (advances t) sg))
      ⟨≈⟩ ≈sym (map-map (F.act w (sf , a)) _ _)
      ⟨≈⟩ map-arg _ (F.act-law b w sf a)
      ⟨≈⟩ ≈sym (event-left (p b) (r b) (F.project-state b w sf) (G.project-state b w sg) (project A b w a))
    act-law b w sf sg (inj₂ c) =
      map-map (G.act w (sg , c)) _ _
      ⟨≈⟩ ≈sym (map-map (G.act w (sg , c)) _ _)
      ⟨≈⟩ map-arg _ (G.act-law b w sg c)
      ⟨≈⟩ ≈sym (event-right (p b) (r b) (F.project-state b w sf) (G.project-state b w sg) (project C b w c))

  events-following-left : Following (A ⊎ᴸ C) (B ⊎ᴸ D) (λ b → p b T.⊗ᵉ r b)
  events-following-left = record
    { State = State
    ; project-state = λ b w → Data.Product.map (F.project-state b w) (G.project-state b w)
    ; point = F.point >>=ₚ λ sf → G.point initial >>=ₚ λ sg → returnₚ (sf , sg)
    ; point-law = λ b → pair-point F.point (G.point initial) _ _ (F.point-law b) (G.point-law b initial)
    ; act = act ; act-law = λ b w (sf , sg) x → act-law b w sf sg x }

------------------------------------------------------------------------
-- A loop carries the current world beside its pending letter

module _ {X Y L : Letters} {p : Bool → MC.Machine (Base X ⊎ Base L) (Base Y ⊎ Base L)}
  (q : Following (X ⊎ᴸ L) (Y ⊎ᴸ L) p) where
  private
    module Q = Following q

    Loop Exit : World → Set
    Loop origin = Σ[ w ∈ World ] origin ≤ʷ w × Q.State w × Related L w
    Exit origin = Σ[ w ∈ World ] origin ≤ʷ w × Q.State w × Related Y w

    route : ∀ origin {w} → origin ≤ʷ w → Turn Q.State (Related (Y ⊎ᴸ L)) w → Exit origin ⊎ Loop origin
    route origin e (turn w′ e′ s (inj₁ y)) = inj₁ (w′ , transʷ e e′ , s , y)
    route origin e (turn w′ e′ s (inj₂ l)) = inj₂ (w′ , transʷ e e′ , s , l)

    walk : ∀ origin → Body ⊤ (Loop origin) (Exit origin)
    walk origin (_ , w , e , s , l) = mapₚ (λ t → tt , route origin e t) (Q.act w (s , inj₂ l))

    loop-project : ∀ b origin → ⊤ × Loop origin → MC.St (p b) × Base L
    loop-project b origin (_ , w , _ , s , l) = Q.project-state b w s , project L b w l

    exit-project : ∀ b origin → ⊤ × Exit origin → MC.St (p b) × Base Y
    exit-project b origin (_ , w , _ , s , y) = Q.project-state b w s , project Y b w y

    module P (b : Bool) = Col.Loop (Base X) (Base Y) (Base L) (MC.state (p b)) (MC.step (p b))

    route-project : ∀ b origin {w} (e : origin ≤ʷ w) t
      → φ (loop-project b origin) (exit-project b origin) (tt , route origin e t)
        ≡ (Q.project-state b (world t) (state t) , project (Y ⊎ᴸ L) b (world t) (output t))
    route-project b origin e (turn _ _ _ (inj₁ _)) = refl
    route-project b origin e (turn _ _ _ (inj₂ _)) = refl

    walk-law : ∀ b origin sa → P.body b (loop-project b origin sa)
      ≈ₚ mapₚ (φ (loop-project b origin) (exit-project b origin)) (walk origin sa)
    walk-law b origin (_ , w , e , s , l) = ≈sym
      (map-map (Q.act w (s , inj₂ l)) _ _
       ⟨≈⟩ map-eq (Q.act w (s , inj₂ l)) _ _ (route-project b origin e)
       ⟨≈⟩ Q.act-law b w s (inj₂ l))

    resume : ∀ origin → Exit origin ⊎ Loop origin → Dₚ (Exit origin)
    resume origin (inj₁ y) = returnₚ y
    resume origin (inj₂ l) = mapₚ proj₂ (iterₚ (walk origin) (tt , l))

    exit-turn : ∀ origin → Exit origin → Turn Q.State (Related Y) origin
    exit-turn origin (w , e , s , y) = turn w e s y

    resume-law : ∀ b origin {w} (e : origin ≤ʷ w) t
      → mapₚ (λ z → Q.project-state b (proj₁ z) (proj₁ (proj₂ (proj₂ z)))
                  , project Y b (proj₁ z) (proj₂ (proj₂ (proj₂ z)))) (resume origin (route origin e t))
        ≈ₚ contᵢ (P.body b) (Q.project-state b (world t) (state t)
                            , project (Y ⊎ᴸ L) b (world t) (output t))
    resume-law b origin e (turn w′ e′ s (inj₁ y)) = >>=ₚ-identityˡ _ _
    resume-law b origin e (turn w′ e′ s (inj₂ l)) =
      map-map (iterₚ (walk origin) (tt , (w′ , transʷ e e′ , s , l))) _ _
      ⟨≈⟩ ≈sym (iterₚ-transfer (walk origin) (P.body b)
        (loop-project b origin) (exit-project b origin) (walk-law b origin)
        (tt , (w′ , transʷ e e′ , s , l)))

  trace-following : Following X Y (λ b → P.tracedᴹ b)
  trace-following = record
    { State = Q.State ; project-state = Q.project-state
    ; point = Q.point ; point-law = Q.point-law
    ; act = λ w sx → Q.act w (proj₁ sx , inj₁ (proj₂ sx)) >>=ₚ λ t → mapₚ (exit-turn w) (resume w (route w reflʷ t))
    ; act-law = λ b w s x →
        map-bind (Q.act w (s , inj₁ x)) _ _
        ⟨≈⟩ bindᶠ (λ t → map-map (resume w (route w reflʷ t)) _ _ ⟨≈⟩ resume-law b w reflʷ t)
        ⟨≈⟩ ≈sym (bind-map (Q.act w (s , inj₁ x)) _ (contᵢ (P.body b)))
        ⟨≈⟩ bindˣ (Q.act-law b w s (inj₁ x))
        ⟨≈⟩ ≈sym (P.step-red b (Q.project-state b w s) (project X b w x)) }

------------------------------------------------------------------------
-- Identity projections at the boundary give an ordinary relational span

module _ {X Y : Set} (rx ry : World → Set)
  (px : Bool → ∀ w → rx w → X) (py : Bool → ∀ w → ry w → Y)
  {p : Bool → MC.Machine X Y}
  (q : Following (record { Base = X ; Related = rx ; project = px })
                 (record { Base = Y ; Related = ry ; project = py }) p)
  (input : ∀ w → X → rx w) (input-law : ∀ b w x → px b w (input w x) ≡ x)
  (output : ∀ w → ry w → Y) (output-law : ∀ b w y → py b w y ≡ output w y) where
  private
    module Q = Following q

    S⁺ : Set
    S⁺ = Σ World Q.State

    step⁺ : S⁺ × X → Dₚ (S⁺ × Y)
    step⁺ ((w , s) , x) = mapₚ (λ t → (world t , state t) , output (world t) (Turn.output t)) (Q.act w (s , input w x))

    apex⁺ : MC.Machine X Y
    apex⁺ = MC.mk record
      { obj = S⁺ ; point = λ _ → mapₚ (initial ,_) Q.point } step⁺

    leg⁺ : ∀ b → apex⁺ RS.≲[ V.id ∣ V.id ] p b
    leg⁺ b = RS.≲[]-resp-≈ (λ x → ≈sym (pure-idᵏ x)) (λ y → ≈sym (pure-idᵏ y))
      (simFn[] (λ (w , s) → Q.project-state b w s) (λ x → x) (λ y → y)
        (λ _ → map-map Q.point _ _ ⟨≈⟩ Q.point-law b)
        λ where
          ((w , s) , x) →
            map-map (Q.act w (s , input w x)) _ _
            ⟨≈⟩ map-eq (Q.act w (s , input w x)) _ _
              (λ t → cong (Q.project-state b (world t) (state t) ,_) (sym (output-law b (world t) (Turn.output t))))
            ⟨≈⟩ Q.act-law b w s (input w x)
            ⟨≈⟩ ≡⇒≈ₚ (cong (MC.step (p b) ∘ (Q.project-state b w s ,_)) (input-law b w x)))

  following-relsim : RS.RelSim V.id V.id V.id V.id (p true) (p false)
  following-relsim = record { apex = apex⁺ ; left = leg⁺ true ; right = leg⁺ false }

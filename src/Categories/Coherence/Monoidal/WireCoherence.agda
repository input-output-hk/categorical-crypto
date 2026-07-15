{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Wire-coherence theory: ALL ⟦_⟧ᵇ-free coherence of the structural
-- `wires`/`HomTerm` layer — the `castW` object-transport algebra, the
-- +-associators, and the flat-shift / merge-split conjugation lemmas
-- `liftW-merge`/`pad≡liftW` (`WireCoh`), plus the DecEq-dependent UIP/castW-collapse layer,
-- the castW helper kit, and the merge/split right-unitor & pentagon coherence
-- family (`WireCohDec`).
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.WireCoherence where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality.Properties
import Data.List.Properties.Ext as ListExt

open import Categories.Category
import Categories.Category.Monoidal.Properties as MonProps
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Reasoning.Ext as MRExt
open import Categories.FreeMonoidal

module WireCoh (v : Variant) (X : Set)
               (mor : FreeMonoidalHelper.ObjTerm v X → FreeMonoidalHelper.ObjTerm v X → Set)
               where
  open FreeMonoidalHelper v X
  open FreeMonoidalHelper.Mor v X mor
  open Category.HomReasoning FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; split₁ʳ; serialize₁₂)
  open MR FreeMonoidal
  open MRExt FreeMonoidal

  -- the object transport along a propositional equality of wire-lists.
  castW : ∀ {u v : List X} → u ≡ v → HomTerm (wires u) (wires v)
  castW refl = id

  castW-∘ : ∀ {u v w : List X} (e₁ : u ≡ v) (e₂ : v ≡ w) → castW e₂ ∘ castW e₁ ≈Term castW (trans e₁ e₂)
  castW-∘ refl refl = idˡ

  castW-∷ : ∀ {x : X} {u v : List X} (e : u ≡ v) → id ⊗₁ castW e ≈Term castW (cong (x ∷_) e)
  castW-∷ refl = id⊗id≈id

  castW-isoˡ : ∀ {u v : List X} (e : u ≡ v) → castW (sym e) ∘ castW e ≈Term id
  castW-isoˡ refl = idˡ

  castW-isoʳ : ∀ {u v : List X} (e : u ≡ v) → castW e ∘ castW (sym e) ≈Term id
  castW-isoʳ refl = idˡ

  castWˡ-invert : ∀ {A p q} (eq : p ≡ q) (h : HomTerm A (wires q)) (k : HomTerm A (wires p))
               → h ≈Term castW eq ∘ k → castW (sym eq) ∘ h ≈Term k
  castWˡ-invert eq h k e = (refl⟩∘⟨ e) ○ cancelˡ (castW-isoˡ eq)

  castWʳ-invert : ∀ {B p q} (eq : p ≡ q) (h : HomTerm (wires q) B) (k : HomTerm (wires p) B)
               → h ≈Term k ∘ castW (sym eq) → h ∘ castW eq ≈Term k
  castWʳ-invert eq h k e = (e ⟩∘⟨refl) ○ cancelʳ (castW-isoˡ eq)

  --------------------------------------------------------------------------------
  -- The structural associators on wire-lists
  --------------------------------------------------------------------------------
  assocW : (p q s : List X) → HomTerm (wires (p ++ (q ++ s))) (wires ((p ++ q) ++ s))
  assocW p q s = castW (sym (++-assoc p q s))

  assocW⁻ : (p q s : List X) → HomTerm (wires ((p ++ q) ++ s)) (wires (p ++ (q ++ s)))
  assocW⁻ p q s = castW (++-assoc p q s)

  -- `assocW`/`assocW⁻` are mutually inverse (they are `castW` of `sym`-related indices).
  assocW⁻∘assocW : ∀ (p q s : List X) → assocW⁻ p q s ∘ assocW p q s ≈Term id
  assocW⁻∘assocW p q s = castW-isoʳ (++-assoc p q s)

  liftW-assoc : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW x (liftW m W) ≈Term assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
  liftW-assoc x m {u} {v} W = introˡ (assocW⁻∘assocW x m v) ○ pullʳ (⟺ (liftW-assoc' x m W))
    where
    assocW-∷ : ∀ (y : X) (x q s : List X) → assocW (y ∷ x) q s ≈Term id ⊗₁ assocW x q s
    assocW-∷ y x q s = ≡⇒≈Term (cong castW (sym-cong (++-assoc x q s))) ○ ⟺ (castW-∷ (sym (++-assoc x q s)))

    liftW-assoc' : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
                → liftW (x ++ m) W ∘ assocW x m u ≈Term assocW x m v ∘ liftW x (liftW m W)
    liftW-assoc' []       m W = idʳ ○ (⟺ idˡ)
    liftW-assoc' (y ∷ x) m {u} {v} W =
      (refl⟩∘⟨ assocW-∷ y x m u) ○ id⊗-∘ _ _ ○ (refl⟩⊗⟨ liftW-assoc' x m W)
        ○ (⟺ (id⊗-∘ _ _)) ○ (⟺ (assocW-∷ y x m v) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- Flat-shift of a wire morphism as a merge/split conjugation.  `liftW p W`
  -- (the prefix-idle lift, `id {wires p} ⊗₁ W` reflattened) equals the box `W`
  -- conjugated by the flat `merge p`/`split p`; and the flat `pad` is literally
  -- the wire-shift of the right-pad `rpad`.  Both are ⟦_⟧ᵇ-free wire coherence.
  --------------------------------------------------------------------------------

  -- the flat shift equals the merge/split conjugation.
  liftW-merge : ∀ (p : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW p W ≈Term merge p ∘ (id ⊗₁ W) ∘ split p
  liftW-merge []      W = introʳ λ⇒∘λ⇐≈id ○ pullˡ (⟺ λ⇒∘id⊗f≈f∘λ⇒) ○ assoc
  liftW-merge (x ∷ p) {u} {v} W =
    (refl⟩⊗⟨ liftW-merge p W)
      ○ (⟺ (id⊗-∘3 (merge p) (id ⊗₁ W) (split p)))
      ○ reassoc-suc
    where
      -- insert α⇒∘α⇐ = id in the middle and reassociate to expose
      -- merge (suc p) = id⊗₁merge p ∘ α⇒ and split (suc p) = α⇐ ∘ id⊗₁split p.
      reassoc-suc :
          id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
        ≈Term (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p)
      reassoc-suc = begin
        id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
          ≈⟨ refl⟩∘⟨ insertInner α⇒∘α⇐≈id ⟩
        id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ W) ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ split p))
          ≈⟨ refl⟩∘⟨ ((⟺ α-comm) ○ (refl⟩∘⟨ (id⊗id≈id ⟩⊗⟨refl))) ⟩∘⟨refl ⟩
        id ⊗₁ merge p ∘ ((α⇒ ∘ id ⊗₁ W) ∘ (α⇐ ∘ id ⊗₁ split p))
          ≈⟨ center ≈-Term-refl ⟨
        (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p) ∎

  -- `pad` is literally the wire-shift of `rpad` — definitional.
  pad≡liftW : ∀ {a b} (pre suf : List X) (g : HomTerm (wires a) (wires b))
            → pad pre suf g ≈Term liftW pre (rpad suf g)
  pad≡liftW pre suf g = ≈-Term-refl

  --------------------------------------------------------------------------------
  -- The DecEq-dependent layer: `castW` is determined by its
  -- endpoints. On top of that UIP fact this holds the castW helper
  -- kit, the merge/split right-unitor & pentagon coherence family,
  -- and the structural reassociators' collapse to `castW`.
  --------------------------------------------------------------------------------
  module WireCohDec ⦃ _ : DecEq X ⦄ where
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = ListExt.≡-irrelevant _≟_

    castW-irr : ∀ {u v : List X} (e e' : u ≡ v) → castW e ≈Term castW e'
    castW-irr e e' = ≡⇒≈Term (cong castW (≡-irrelevantL e e'))

    -- push a coercion along `cong (x ∷_)` under the prefix `id {Var x} ⊗₁ _`;
    -- the other end is an ARBITRARY object, since the merge/split steps below
    -- need bracketed tensors of wires, not flat ones.
    castW-id⊗ˡ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm R (wires p))
               → castW (cong (x ∷_) e) ∘ (id ⊗₁ h) ≈Term id ⊗₁ (castW e ∘ h)
    castW-id⊗ˡ x e h = (⟺ (castW-∷ e) ⟩∘⟨refl) ○ id⊗-∘ (castW e) h

    --------------------------------------------------------------------------------
    -- The merge/split coherence family: the right-unitor coherence on the flat
    -- merge/split (`merge-ρ`/`split-ρ`, ≈ ρ⇒/ρ⇐) and the pentagon associativity
    -- of merge/split (`merge-assoc`/`split-assoc`).  Pure ⟦_⟧ᵇ-free wire
    -- coherence — the merge/split analogue of the assocW/castW theory above.
    -- They bottom out in the Mac Lane / Kelly unit coherence laws at the *free*
    -- monoidal category over `mor`, whose _≈_/α⇒/ρ⇒/λ⇒/_⊗₁_ coincide
    -- DEFINITIONALLY with _≈Term_/α⇒/ρ⇒/λ⇒/_⊗₁_, so these land as `≈Term`.
    --------------------------------------------------------------------------------
    module K = MonProps.Kelly's Monoidal-FreeMonoidal

    merge-ρ : (a : List X) → castW (++-identityʳ a) ∘ merge a ≈Term ρ⇒
    merge-ρ []      = idˡ ○ K.coherence₃
    merge-ρ (x ∷ a) = begin
      castW (++-identityʳ (x ∷ a)) ∘ (id ⊗₁ merge a ∘ α⇒)
        ≈⟨ ⟺ assoc ⟩
      (castW (cong (x ∷_) (++-identityʳ a)) ∘ (id ⊗₁ merge a)) ∘ α⇒
        ≈⟨ (castW-id⊗ˡ x (++-identityʳ a) (merge a)) ⟩∘⟨refl ⟩
      id ⊗₁ (castW (++-identityʳ a) ∘ merge a) ∘ α⇒
        ≈⟨ (refl⟩⊗⟨ (merge-ρ a)) ⟩∘⟨refl ⟩
      id ⊗₁ ρ⇒ ∘ α⇒
        ≈⟨ K.coherence₂ ⟩
      ρ⇒ ∎

    split-ρ : (a : List X) → split a ∘ castW (sym (++-identityʳ a)) ≈Term ρ⇐
    split-ρ a = inv-resp fi-f ρ⇒∘ρ⇐≈id (merge-ρ a)
      where
        e = ++-identityʳ a
        fi-f : (split a ∘ castW (sym e)) ∘ (castW e ∘ merge a) ≈Term id
        fi-f = cancelInner (castW-isoˡ e) ○ split∘merge a

    merge-assoc : ∀ (p q r : List X)
      → merge p ∘ (id ⊗₁ merge q) ∘ α⇒ ≈Term assocW⁻ p q r ∘ (merge (p ++ q) ∘ (merge p ⊗₁ id))
    merge-assoc []      q r = begin
      λ⇒ ∘ (id ⊗₁ merge q) ∘ α⇒
        ≈⟨ pullˡ λ⇒∘id⊗f≈f∘λ⇒ ⟩
      (merge q ∘ λ⇒) ∘ α⇒
        ≈⟨ pullʳ K.coherence₁ ⟩
      merge q ∘ (λ⇒ ⊗₁ id)
        ≈⟨ ⟺ idˡ ⟩
      assocW⁻ [] q r ∘ (merge q ∘ (λ⇒ ⊗₁ id)) ∎
    merge-assoc (x ∷ p) q r = begin
      (id ⊗₁ merge p ∘ α⇒) ∘ (id ⊗₁ merge q) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (((⟺ id⊗id≈id) ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
      (id ⊗₁ merge p ∘ α⇒) ∘ ((id ⊗₁ id) ⊗₁ merge q) ∘ α⇒
        ≈⟨ center α-comm ⟩
      id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ merge q) ∘ α⇒) ∘ α⇒)
        ≈⟨ ⟺ assoc ⟩
      (id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ merge q) ∘ α⇒)) ∘ α⇒
        ≈⟨ (pullˡ (id⊗-∘ (merge p) (id ⊗₁ merge q))) ⟩∘⟨refl ⟩
      ((id ⊗₁ (merge p ∘ (id ⊗₁ merge q))) ∘ α⇒) ∘ α⇒
        ≈⟨ pent ⟩
      (id ⊗₁ (merge p ∘ (id ⊗₁ merge q)) ∘ id ⊗₁ α⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (id⊗-∘ (merge p ∘ (id ⊗₁ merge q)) α⇒) ⟩∘⟨refl ⟩
      (id ⊗₁ ((merge p ∘ (id ⊗₁ merge q)) ∘ α⇒)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (refl⟩⊗⟨ (assoc ○ (merge-assoc p q r))) ⟩∘⟨refl ⟩
      (id ⊗₁ (assocW⁻ p q r ∘ (merge (p ++ q) ∘ (merge p ⊗₁ id)))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (⟺ (castW-id⊗ˡ x (++-assoc p q r) _)) ⟩∘⟨refl ⟩
      (assocW⁻ (x ∷ p) q r ∘ (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id)))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ assoc ⟩
      assocW⁻ (x ∷ p) q r ∘ ((id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id))
        ≈⟨ refl⟩∘⟨ tailRHS ⟩
      assocW⁻ (x ∷ p) q r ∘ (((id ⊗₁ merge (p ++ q)) ∘ α⇒) ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id)) ∎
      where
        pent : ∀ {B} {X : HomTerm (Var x ⊗₀ (wires p ⊗₀ (wires q ⊗₀ wires r))) B}
             → (X ∘ α⇒) ∘ α⇒ ≈Term (X ∘ id ⊗₁ α⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        pent = pullʳ (⟺ pentagon) ○ ⟺ assoc

        tailRHS : (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
                ≈Term ((id ⊗₁ merge (p ++ q)) ∘ α⇒) ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id)
        tailRHS = begin
          (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
            ≈⟨ (⟺ (id⊗-∘ (merge (p ++ q)) (merge p ⊗₁ id))) ⟩∘⟨refl ⟩
          (id ⊗₁ merge (p ++ q) ∘ id ⊗₁ (merge p ⊗₁ id)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
            ≈⟨ center (⟺ α-comm) ⟩
          id ⊗₁ merge (p ++ q) ∘ ((α⇒ ∘ (id ⊗₁ merge p) ⊗₁ id) ∘ α⇒ ⊗₁ id)
            ≈⟨ refl⟩∘⟨ pullʳ (⟺ split₁ʳ) ⟩
          id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id))
            ≈⟨ ⟺ assoc ⟩
          (id ⊗₁ merge (p ++ q) ∘ α⇒) ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id) ∎

    split-assoc : ∀ (p q r : List X)
      → α⇐ ∘ (id ⊗₁ split q) ∘ split p ≈Term ((split p ⊗₁ id) ∘ split (p ++ q)) ∘ assocW p q r
    split-assoc p q r = inv-resp fi-f g-gi (merge-assoc p q r)
      where
        mL : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires (p ++ (q ++ r)))
        mL = merge p ∘ (id ⊗₁ merge q) ∘ α⇒
        fi : HomTerm (wires (p ++ (q ++ r))) ((wires p ⊗₀ wires q) ⊗₀ wires r)
        fi = α⇐ ∘ (id ⊗₁ split q) ∘ split p
        mR : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires ((p ++ q) ++ r))
        mR = merge (p ++ q) ∘ (merge p ⊗₁ id)
        giU : HomTerm (wires ((p ++ q) ++ r)) ((wires p ⊗₀ wires q) ⊗₀ wires r)
        giU = (split p ⊗₁ id) ∘ split (p ++ q)

        fi-f : fi ∘ mL ≈Term id
        fi-f = begin
          (α⇐ ∘ (id ⊗₁ split q) ∘ split p) ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒)
            ≈⟨ center (cancelʳ (split∘merge p)) ⟩
          α⇐ ∘ ((id ⊗₁ split q) ∘ ((id ⊗₁ merge q) ∘ α⇒))
            ≈⟨ refl⟩∘⟨ cancelˡ (id⊗-cancel (split∘merge q)) ⟩
          α⇐ ∘ α⇒
            ≈⟨ α⇐∘α⇒≈id ⟩
          id ∎

        g-gi : (assocW⁻ p q r ∘ mR) ∘ (giU ∘ assocW p q r) ≈Term id
        g-gi = cancelInner mR-giU ○ assocW⁻∘assocW p q r
          where
            mR-giU : mR ∘ giU ≈Term id
            mR-giU = cancelInner ((⟺ ⊗-∘-dist) ○ ((merge∘split p) ⟩⊗⟨ idˡ) ○ id⊗id≈id) ○ merge∘split (p ++ q)

    liftW-castW : ∀ (p : List X) {u v : List X} (e : u ≡ v) → liftW p (castW e) ≈Term castW (cong (p ++_) e)
    liftW-castW []      e = castW-irr e (cong ([] ++_) e)
    liftW-castW (x ∷ p) e = (refl⟩⊗⟨ liftW-castW p e) ○ castW-∷ (cong (p ++_) e) ○ castW-irr _ _

    --------------------------------------------------------------------------------
    -- The conjugation-by-index-casts relation:  `isConjugate eC eD Y Z` says `Y`
    -- is `Z` retyped on both ends by the wire-list equalities `eC` (codomain) and
    -- `eD` (domain).  Stated as the commutative square with the two `castW`
    -- transports as verticals (`castW (sym eC) ∘ Y ≈ Z ∘ castW eD`).  It packages
    -- the `++`-assoc castW tax that arises when re-cleaning a grouped box-layer
    -- into a flat `pad`.
    --------------------------------------------------------------------------------
    open Definitions FreeMonoidal

    isConjugate : ∀ {p q w t : List X} (eC : t ≡ q) (eD : p ≡ w)
         → HomTerm (wires p) (wires q) → HomTerm (wires w) (wires t) → Set
    isConjugate eC eD Y Z = CommutativeSquare Y (castW eD) (castW (sym eC)) Z

    conj-fromSandwich : ∀ {p q w t} {eC : t ≡ q} {eD : p ≡ w}
                        {Y : HomTerm (wires p) (wires q)} {Z : HomTerm (wires w) (wires t)}
                      → Y ≈Term castW eC ∘ Z ∘ castW eD → isConjugate eC eD Y Z
    conj-fromSandwich {eC = eC} s = (refl⟩∘⟨ s) ○ cancelˡ (castW-isoˡ eC)

    conj-toSandwich : ∀ {p q w t} {eC : t ≡ q} {eD : p ≡ w}
                      {Y : HomTerm (wires p) (wires q)} {Z : HomTerm (wires w) (wires t)}
                    → isConjugate eC eD Y Z → Y ≈Term castW eC ∘ Z ∘ castW eD
    conj-toSandwich {eC = eC} s = introˡ (castW-isoʳ eC) ○ assoc ○ (refl⟩∘⟨ s)

    conj-trans : ∀ {p q w t w' t'}
      {Y : HomTerm (wires p) (wires q)} {Z : HomTerm (wires w) (wires t)} {V : HomTerm (wires w') (wires t')}
      {eC : t ≡ q} {eD : p ≡ w} {fC : t' ≡ t} {fD : w ≡ w'}
      → isConjugate eC eD Y Z → isConjugate fC fD Z V → isConjugate (trans fC eC) (trans eD fD) Y V
    conj-trans {eC = eC} {eD} {fC} {fD} hy hz =
      (⟺ (castW-∘ (sym eC) (sym fC) ○ castW-irr _ _) ⟩∘⟨refl)
        ○ glue hz hy
        ○ (refl⟩∘⟨ castW-∘ eD fD)

    conj-irr : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z : HomTerm (wires w) (wires t)}
               {eC eC' : t ≡ q} {eD eD' : p ≡ w}
             → isConjugate eC eD Y Z → isConjugate eC' eD' Y Z
    conj-irr {eC = eC} {eC'} {eD} {eD'} s =
      (castW-irr (sym eC') (sym eC) ⟩∘⟨refl) ○ s ○ (refl⟩∘⟨ castW-irr eD eD')

    conj-≈ˡ : ∀ {p q w t}
              {Y' Y : HomTerm (wires p) (wires q)}
              {Z : HomTerm (wires w) (wires t)}
              {eC : t ≡ q} {eD : p ≡ w}
            → Y' ≈Term Y → isConjugate eC eD Y Z → isConjugate eC eD Y' Z
    conj-≈ˡ e s = (refl⟩∘⟨ e) ○ s

    conj-mid : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z Z' : HomTerm (wires w) (wires t)}
               {eC : t ≡ q} {eD : p ≡ w}
             → isConjugate eC eD Y Z → Z ≈Term Z' → isConjugate eC eD Y Z'
    conj-mid s e = s ○ (e ⟩∘⟨refl)

    -- the sandwich-cancellation used by both clean slides: cancel the inverse
    -- cast pair `castW (sym eD) ∘ castW eD` against the caller's cast.
    conj-cancel : ∀ {p q w t} {A : ObjTerm}
                  {Y : HomTerm (wires p) (wires q)}
                  {Z : HomTerm (wires w) (wires t)}
                  {eC : t ≡ q} (eD : p ≡ w) (C : HomTerm A (wires p))
                → isConjugate eC eD Y Z
                → Z ∘ (castW eD ∘ C) ≈Term castW (sym eC) ∘ (Y ∘ C)
    conj-cancel eD C s = ⟺ assoc ○ (⟺ s ⟩∘⟨refl) ○ assoc

    -- prefix-lift of a conjugation.
    liftW-conj : ∀ (p : List X) {pp q w t}
                 {Y : HomTerm (wires pp) (wires q)}
                 {Z : HomTerm (wires w) (wires t)}
                 {eC : t ≡ q} {eD : pp ≡ w}
               → isConjugate eC eD Y Z
               → isConjugate (cong (p ++_) eC) (cong (p ++_) eD) (liftW p Y) (liftW p Z)
    liftW-conj p {Y = Y} {Z = Z} {eC = eC} {eD = eD} s = begin
      castW (sym (cong (p ++_) eC)) ∘ liftW p Y
        ≈⟨ ≡⇒≈Term (cong castW (sym-cong eC)) ⟩∘⟨refl ⟩
      castW (cong (p ++_) (sym eC)) ∘ liftW p Y
        ≈⟨ ⟺ (liftW-castW p (sym eC)) ⟩∘⟨refl ⟩
      liftW p (castW (sym eC)) ∘ liftW p Y
        ≈⟨ ⟺ (liftW-∘ p (castW (sym eC)) Y) ⟩
      liftW p (castW (sym eC) ∘ Y)
        ≈⟨ liftW-resp p s ⟩
      liftW p (Z ∘ castW eD)
        ≈⟨ liftW-∘ p Z (castW eD) ⟩
      liftW p Z ∘ liftW p (castW eD)
        ≈⟨ refl⟩∘⟨ liftW-castW p eD ⟩
      liftW p Z ∘ castW (cong (p ++_) eD) ∎

    --------------------------------------------------------------------------------
    -- The pad-fusion bi-action.  `liftW p` (prefix idle wires, structural) and
    -- `rpad s` (suffix idle wires, a merge/split conjugation) form a bi-action of
    -- the list monoid on wire morphisms, with `pad p s ≡ liftW p ∘ rpad s`
    -- DEFINITIONALLY (`pad≡liftW`).  Its fusion is captured by THREE primitive
    -- laws, all `isConjugate`/sandwich equations against `++`-associativity casts:
    -- `liftW-fuse` (prefix∘prefix), `rpad-fuse` (suffix∘suffix), and `rpad-liftW`
    -- (a suffix past a prefix); `rpad-rpad` is `conj-fromSandwich` of `rpad-fuse`.
    -- Every pad-fusion staircase downstream (`liftW-pad`/`rpad-pad` in Reflect,
    -- the re-cleanings in Sigma) is a conjugation CHAIN over these three.
    --------------------------------------------------------------------------------

    -- prefix-lift fusion, as a conjugation (assocW towers collapse to castW).
    liftW-fuse : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → isConjugate (++-assoc x m v) (sym (++-assoc x m u))
                      (liftW x (liftW m W)) (liftW (x ++ m) W)
    liftW-fuse x m {u} {v} W = begin
      castW (sym (++-assoc x m v)) ∘ liftW x (liftW m W)
        ≈⟨ refl⟩∘⟨ liftW-assoc x m W ⟩
      castW (sym (++-assoc x m v)) ∘ (assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u)
        ≈⟨ cancelˡ (castW-isoˡ (++-assoc x m v)) ⟩
      liftW (x ++ m) W ∘ assocW x m u ∎

    -- suffix-pad fusion:  `rpad rt (rpad suf g)` is the wider `rpad (suf ++ rt) g`,
    -- up to +-associativity reindex on its endpoints.  Assembled from the
    -- merge/split `merge-assoc`/`split-assoc` pentagon coherence above.
    rpad-fuse : ∀ {a b} (suf rt : List X) (g : HomTerm (wires a) (wires b))
              → rpad rt (rpad suf g)
                ≈Term (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g)
                        ∘ castW (++-assoc a suf rt)
    rpad-fuse {a} {b} suf rt g = begin
      merge (b ++ suf) ∘ ((merge b ∘ (g ⊗₁ id) ∘ split a) ⊗₁ id) ∘ split (a ++ suf)
        ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ (⟺ idˡ)) ⟩∘⟨refl) ⟩
      merge (b ++ suf) ∘ ((merge b ∘ ((g ⊗₁ id) ∘ split a)) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
        ≈⟨ refl⟩∘⟨ (⊗-∘-dist ⟩∘⟨refl) ⟩
      merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ id) ∘ split (a ++ suf)
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (refl⟩⊗⟨ (⟺ idˡ))) ⟩∘⟨refl) ⟩
      merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⊗-∘-dist) ⟩∘⟨refl) ⟩
      merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
        ≈⟨ regroup5 ⟩
      (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
        ≈⟨ mergeStep ⟩∘⟨ (refl⟩∘⟨ splitStep) ⟩
      (castW (sym (++-assoc b suf rt)) ∘ (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒))
        ∘ ((g ⊗₁ id) ⊗₁ id)
        ∘ ((α⇐ ∘ (id ⊗₁ split suf) ∘ split a) ∘ castW (++-assoc a suf rt))
        ≈⟨ pull-coe ⟩
      (castW (sym (++-assoc b suf rt)) ∘
          ((merge b ∘ (id ⊗₁ merge suf) ∘ α⇒)
            ∘ ((g ⊗₁ id) ⊗₁ id)
            ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)))
        ∘ castW (++-assoc a suf rt)
        ≈⟨ (refl⟩∘⟨ core) ⟩∘⟨refl ⟩
      (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g)
        ∘ castW (++-assoc a suf rt) ∎
      where
        -- mergeStep:  merge(b++suf)∘(merge b⊗id) ≈ castW(sym e_b) ∘ (merge b{suf++rt}∘(id⊗merge suf)∘α⇒)
        mergeStep : merge (b ++ suf) ∘ (merge b ⊗₁ id)
                  ≈Term castW (sym (++-assoc b suf rt)) ∘ (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒)
        mergeStep = ⟺ (castWˡ-invert (++-assoc b suf rt) _ _ (merge-assoc b suf rt))
        -- splitStep:  (split a⊗id)∘split(a++suf) ≈ (α⇐∘(id⊗split suf)∘split a{suf++rt}) ∘ castW(sym(sym e_a))
        splitStep : (split a ⊗₁ id) ∘ split (a ++ suf)
                  ≈Term (α⇐ ∘ (id ⊗₁ split suf) ∘ split a) ∘ castW (++-assoc a suf rt)
        splitStep = ⟺ (castWʳ-invert (++-assoc a suf rt) _ _ (split-assoc a suf rt))
        -- bookkeeping regroup of the 5-fold composite.
        regroup5 : merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
                 ≈Term (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
        regroup5 = center⁻¹ ≈-Term-refl assoc
        -- pull the castW coercions out of the composite to the ends.
        pull-coe :
            (castW (sym (++-assoc b suf rt)) ∘ (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒))
              ∘ ((g ⊗₁ id) ⊗₁ id)
              ∘ ((α⇐ ∘ (id ⊗₁ split suf) ∘ split a) ∘ castW (++-assoc a suf rt))
          ≈Term (castW (sym (++-assoc b suf rt)) ∘
                    ((merge b ∘ (id ⊗₁ merge suf) ∘ α⇒)
                      ∘ ((g ⊗₁ id) ⊗₁ id)
                      ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)))
                ∘ castW (++-assoc a suf rt)
        pull-coe = pull (sym (++-assoc b suf rt)) (++-assoc a suf rt) _ _ _
          where
            pull : ∀ {pb qb pa qa} {C D : ObjTerm}
                     (eb : pb ≡ qb) (ea : pa ≡ qa)
                     (L : HomTerm C (wires pb))
                     (Mid : HomTerm D C)
                     (Rt : HomTerm (wires qa) D)
                 → (castW eb ∘ L) ∘ Mid ∘ (Rt ∘ castW ea)
                   ≈Term (castW eb ∘ (L ∘ Mid ∘ Rt)) ∘ castW ea
            pull refl refl L Mid Rt = (idˡ ⟩∘⟨ (refl⟩∘⟨ idʳ)) ○ ⟺ (idʳ ○ idˡ)
        -- the core box-conjugation collapse (pure bifunctoriality + α + iso).
        core : (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒)
                 ∘ ((g ⊗₁ id) ⊗₁ id)
                 ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)
               ≈Term rpad (suf ++ rt) g
        core = begin
          (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)
            ≈⟨ coreRegroup ⟩
          merge b ∘ ((id ⊗₁ merge suf) ∘ (α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ split suf)) ∘ split a
            ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (midα ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
          merge b ∘ ((id ⊗₁ merge suf) ∘ (g ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ split suf)) ∘ split a
            ≈⟨ refl⟩∘⟨ (midColl ⟩∘⟨refl) ⟩
          merge b ∘ (g ⊗₁ id) ∘ split a ∎
          where
            -- both sides equal the fully right-associated 7-fold composite.
            m1 = merge b
            m2 = id ⊗₁ merge suf
            m3 = α⇒
            m4 = (g ⊗₁ id) ⊗₁ id
            m5 = α⇐
            m6 = id ⊗₁ split suf
            m7 = split a
            rNF = m1 ∘ (m2 ∘ (m3 ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7)))))
            coreRegroup :
                (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)
              ≈Term merge b ∘ ((id ⊗₁ merge suf) ∘ (α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ split suf)) ∘ split a
            coreRegroup = (lhsNF ○ (⟺ rhsNF))
              where
                lhsNF : (m1 ∘ m2 ∘ m3) ∘ (m4 ∘ (m5 ∘ m6 ∘ m7)) ≈Term rNF
                lhsNF = assoc ○ (refl⟩∘⟨ assoc)
                rhsNF : m1 ∘ ((m2 ∘ (m3 ∘ (m4 ∘ m5)) ∘ m6) ∘ m7) ≈Term rNF
                rhsNF = refl⟩∘⟨ pullʳ (assoc ○ pullʳ assoc)
            -- α⇒ ∘ ((g⊗id)⊗id) ∘ α⇐ ≈ g⊗(id⊗id)
            midα : α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐ ≈Term g ⊗₁ (id ⊗₁ id)
            midα = α-conj g (id) (id)
            -- (id⊗merge suf) ∘ (g⊗(id⊗id)) ∘ (id⊗split suf) ≈ g ⊗ id{suf++rt}
            midColl : (id ⊗₁ merge suf) ∘ (g ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ split suf) ≈Term g ⊗₁ id
            midColl = begin
              (id ⊗₁ merge suf) ∘ (g ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ split suf)
                ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ id⊗id≈id) ⟩∘⟨refl) ⟩
              (id ⊗₁ merge suf) ∘ (g ⊗₁ id) ∘ (id ⊗₁ split suf)
                ≈⟨ refl⟩∘⟨ (⟺ serialize₁₂) ⟩
              (id ⊗₁ merge suf) ∘ (g ⊗₁ split suf)
                ≈⟨ ⟺ ⊗-∘-dist ⟩
              (id ∘ g) ⊗₁ (merge suf ∘ split suf)
                ≈⟨ idˡ ⟩⊗⟨ (merge∘split suf) ⟩
              g ⊗₁ id ∎

    -- a suffix-pad past a prefix-lift.  σ-free: only `rpad-id⊗` and the
    -- `castW`/`liftW` kit, so it is part of the structural wire theory here.
    rpad-liftW : ∀ (sq p : List X) {u v} (W : HomTerm (wires u) (wires v))
               → isConjugate (sym (++-assoc p v sq)) (++-assoc p u sq)
                             (rpad sq (liftW p W)) (liftW p (rpad sq W))
    rpad-liftW sq p {u} {v} W = conj-fromSandwich (go sq p W)
      where
      go : ∀ (sq p : List X) {u v} (W : HomTerm (wires u) (wires v))
         → rpad sq (liftW p W)
           ≈Term castW (sym (++-assoc p v sq)) ∘ liftW p (rpad sq W) ∘ castW (++-assoc p u sq)
      go sq [] {u} {v} W = ⟺ (idˡ ○ idʳ)
      go sq (x ∷ p) {u} {v} W = begin
        rpad sq (liftW (x ∷ p) W)
          ≈⟨ rpad-id⊗ sq x (liftW p W) ⟩
        id ⊗₁ rpad sq (liftW p W)
          ≈⟨ refl⟩⊗⟨ go sq p W ⟩
        id ⊗₁ (castW (sym (++-assoc p v sq)) ∘ liftW p (rpad sq W) ∘ castW (++-assoc p u sq))
          ≈⟨ id⊗-∘3 _ _ _ ⟨
        id ⊗₁ castW (sym (++-assoc p v sq))
          ∘ id ⊗₁ liftW p (rpad sq W)
          ∘ id ⊗₁ castW (++-assoc p u sq)
          ≈⟨ castW-∷ (sym (++-assoc p v sq)) ⟩∘⟨ refl⟩∘⟨ castW-∷ (++-assoc p u sq) ⟩
        castW (cong (x ∷_) (sym (++-assoc p v sq)))
          ∘ liftW (x ∷ p) (rpad sq W)
          ∘ castW (cong (x ∷_) (++-assoc p u sq))
          ≈⟨ castW-irr _ _ ⟩∘⟨ refl⟩∘⟨ castW-irr _ _ ⟩
        castW (sym (++-assoc (x ∷ p) v sq))
          ∘ liftW (x ∷ p) (rpad sq W)
          ∘ castW (++-assoc (x ∷ p) u sq) ∎

    -- suffix-pad fusion as an `isConjugate`: `rpad-fuse` (above) is already in
    -- the castW sandwich form; we only reassociate and repackage.
    rpad-rpad : ∀ (s sq : List X) {u v} (W : HomTerm (wires u) (wires v))
              → isConjugate (sym (++-assoc v s sq)) (++-assoc u s sq)
                            (rpad sq (rpad s W)) (rpad (s ++ sq) W)
    rpad-rpad s sq {u} {v} W = conj-fromSandwich (begin
      rpad sq (rpad s W)
        ≈⟨ rpad-fuse s sq W ⟩
      (castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W) ∘ castW (++-assoc u s sq)
        ≈⟨ assoc ⟩
      castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W ∘ castW (++-assoc u s sq) ∎)

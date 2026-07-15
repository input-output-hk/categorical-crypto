{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Wire-coherence theory: ALL ⟦box⟧-free coherence of the structural
-- `wires`/`HomTerm` layer — the `castW` object-transport algebra and the
-- +-associators (`WireCoh`), plus the DecEq-dependent UIP/castW-collapse layer,
-- the castW helper kit, and the merge/split right-unitor & pentagon coherence
-- family (`WireCohDec`).  Speaks only of `wires`/`HomTerm`; no reflection engine.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.WireCoherence where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Data.List.Properties.Ext as ListExt

open import Categories.Category using (Category)
import Categories.Category.Monoidal.Properties as MonProps
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR
open import Categories.FreeMonoidal

module WireCoh (v : Variant) (X : Set)
               (mor : FreeMonoidalHelper.ObjTerm v X → FreeMonoidalHelper.ObjTerm v X → Set)
               where
  open FreeMonoidalHelper v X using (Var; wires; unit; _⊗₀_)
  open FreeMonoidalHelper.Mor v X mor
  -- the full `_≈_`-reasoning syntax (`begin`/`≈⟨_⟩`/`∎`) plus the ∘-step
  -- combinators; opened unrestricted since `≈⟨_⟩` is `syntax` (not a name a
  -- `using` clause can carry).
  open Category.HomReasoning FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; split₁ʳ)
  open MR FreeMonoidal
    using (introˡ; introʳ; pullˡ; pullʳ; center; cancelˡ; cancelʳ; cancelInner)

  -- the object transport: u ≡ v  →  HomTerm (wires u) (wires v).
  castW : ∀ {u v : List X} → u ≡ v → HomTerm (wires u) (wires v)
  castW refl = id

  castW-∘ : ∀ {u v w : List X} (e₁ : u ≡ v) (e₂ : v ≡ w)
          → castW e₂ ∘ castW e₁ ≈Term castW (trans e₁ e₂)
  castW-∘ refl refl = idˡ

  castW-∷ : ∀ {x : X} {u v : List X} (e : u ≡ v)
          → id {Var x} ⊗₁ castW e ≈Term castW (cong (x ∷_) e)
  castW-∷ refl = id⊗id≈id

  castW-sym-r : ∀ {u v : List X} (e : u ≡ v) → castW (sym e) ∘ castW e ≈Term id
  castW-sym-r refl = idˡ

  castW-sym-r-flip : ∀ {u v : List X} (e : u ≡ v) → castW e ∘ castW (sym e) ≈Term id
  castW-sym-r-flip refl = idˡ

  castW-cancelʳ : ∀ {u v w : List X} (e : u ≡ v)
                  {A B : HomTerm (wires v) (wires w)}
                → A ∘ castW e ≈Term B ∘ castW e → A ≈Term B
  castW-cancelʳ refl {A} {B} h = ⟺ idʳ ○ h ○ idʳ

  --------------------------------------------------------------------------------
  -- The structural +-associators on wire-lists.  Defined by recursion on `p`:
  -- at each `∷` both indices grow by one label, so each is an id-reshape
  -- threaded through ⊗₁ (the base case is genuinely id since
  -- [] ++ (q ++ s) = q ++ s = ([] ++ q) ++ s definitionally).
  --------------------------------------------------------------------------------
  assocW : (p q s : List X) → HomTerm (wires (p ++ (q ++ s))) (wires ((p ++ q) ++ s))
  assocW []      q s = id
  assocW (x ∷ p) q s = id ⊗₁ assocW p q s

  assocW⁻ : (p q s : List X) → HomTerm (wires ((p ++ q) ++ s)) (wires (p ++ (q ++ s)))
  assocW⁻ []      q s = id
  assocW⁻ (x ∷ p) q s = id ⊗₁ assocW⁻ p q s

  assocW⁻∘assocW : ∀ (p q s : List X) → assocW⁻ p q s ∘ assocW p q s ≈Term id
  assocW⁻∘assocW []      q s = idˡ
  assocW⁻∘assocW (x ∷ p) q s = id⊗-cancel (assocW⁻∘assocW p q s)

  -- Lifting by (x+m) vs lifting by x then m, bridged by assocW.
  liftW-assoc : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW (x ++ m) W ∘ assocW x m u
                ≈Term assocW x m v ∘ liftW x (liftW m W)
  liftW-assoc []       m W = idʳ ○ (⟺ idˡ)
  liftW-assoc (y ∷ x) m {u} {v} W =
    id⊗-∘ _ _ ○ (refl⟩⊗⟨ liftW-assoc x m W) ○ (⟺ (id⊗-∘ _ _))

  -- rearranged (both directions of conjugation made explicit).
  liftW-assoc' : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → liftW x (liftW m W)
                 ≈Term assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
  liftW-assoc' x m {u} {v} W =
    introˡ (assocW⁻∘assocW x m v) ○ pullʳ (⟺ (liftW-assoc x m W))

  --------------------------------------------------------------------------------
  -- The DecEq-dependent layer: `castW` is determined by its endpoints (UIP on
  -- wire-lists, via Hedberg).  On top of that UIP fact this holds the castW
  -- helper kit, the merge/split right-unitor & pentagon coherence family, and
  -- the structural reassociators' collapse to `castW`.
  --------------------------------------------------------------------------------
  module WireCohDec (_≟X_ : DecidableEquality X) where
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = ListExt.≡-irrelevant _≟X_

    castW-irr : ∀ {u v : List X} (e e' : u ≡ v) → castW e ≈Term castW e'
    castW-irr e e' = ≡⇒≈Term (cong castW (≡-irrelevantL e e'))

    --------------------------------------------------------------------------------
    -- The castW algebra kit: a HomTerm whose codomain (resp. domain) wire list
    -- is retyped along a propositional equality is precisely a `castW`
    -- post-composition `castW e ∘ h` (resp. pre-composition `h ∘ castW (sym e)`).
    -- The other end is an ARBITRARY object (the merge/split steps below need
    -- bracketed tensors of wires, not flat ones).  The lemma kit below records
    -- the algebra of these two `castW` conjugations directly.
    --   castWˡ-irr / castWʳ-irr  : irrelevance (UIP) for the two sides
    --   castW-id⊗ˡ / castW-id⊗ʳ  : push castW through `id ⊗₁ _`
    --   castWˡ-invert / castWʳ-invert : cancel a castW against a proven equation
    --   mid-retype                : cancel a castW pair inserted in the middle
    --------------------------------------------------------------------------------

    -- recast along a propositionally-equal index (UIP on the wire lists).
    castWˡ-irr : ∀ {A p q} (e e' : p ≡ q) (h : HomTerm A (wires p))
               → castW e ∘ h ≈Term castW e' ∘ h
    castWˡ-irr e e' h = castW-irr e e' ⟩∘⟨refl

    castWʳ-irr : ∀ {B p q} (e e' : p ≡ q) (h : HomTerm (wires p) B)
               → h ∘ castW (sym e) ≈Term h ∘ castW (sym e')
    castWʳ-irr e e' h = refl⟩∘⟨ castW-irr (sym e) (sym e')

    -- retype the middle object of a composite (the two transports cancel).
    mid-retype : ∀ {A B p q} (e : p ≡ q) (h : HomTerm (wires p) B) (j : HomTerm A (wires p))
               → h ∘ j ≈Term (h ∘ castW (sym e)) ∘ (castW e ∘ j)
    mid-retype e h j = ⟺ (cancelInner (castW-sym-r e))

    -- push a coercion along `cong (x ∷_)` under the prefix `id {Var x} ⊗₁ _`.
    castW-id⊗ˡ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm R (wires p))
               → castW (cong (x ∷_) e) ∘ (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ (castW e ∘ h)
    castW-id⊗ˡ x e h =
      (⟺ (castW-∷ e) ⟩∘⟨refl) ○ id⊗-∘ (castW e) h

    castW-id⊗ʳ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm (wires p) R)
               → (id {Var x} ⊗₁ h) ∘ castW (sym (cong (x ∷_) e)) ≈Term id {Var x} ⊗₁ (h ∘ castW (sym e))
    castW-id⊗ʳ x e h =
      (refl⟩∘⟨ castW-irr (sym (cong (x ∷_) e)) (cong (x ∷_) (sym e)))
      ○ (refl⟩∘⟨ ⟺ (castW-∷ (sym e))) ○ id⊗-∘ h (castW (sym e))

    -- invert a coercion equation:  h ≈ castW eq ∘ k  ⇒  castW (sym eq) ∘ h ≈ k.
    castWˡ-invert : ∀ {A p q} (eq : p ≡ q) (h : HomTerm A (wires q)) (k : HomTerm A (wires p))
                 → h ≈Term castW eq ∘ k → castW (sym eq) ∘ h ≈Term k
    castWˡ-invert eq h k e =
      (refl⟩∘⟨ e) ○ cancelˡ (castW-sym-r eq)

    castWʳ-invert : ∀ {B p q} (eq : p ≡ q) (h : HomTerm (wires q) B) (k : HomTerm (wires p) B)
                 → h ≈Term k ∘ castW (sym eq) → h ∘ castW (sym (sym eq)) ≈Term k
    castWʳ-invert eq h k e =
      (e ⟩∘⟨refl) ○ cancelʳ (castW-sym-r-flip (sym eq))

    --------------------------------------------------------------------------------
    -- The merge/split coherence family: the right-unitor coherence on the flat
    -- merge/split (`merge-ρ`/`split-ρ`, ≈ ρ⇒/ρ⇐) and the pentagon associativity
    -- of merge/split (`merge-assoc`/`split-assoc`).  Pure ⟦box⟧-free wire
    -- coherence — the merge/split analogue of the assocW/castW theory above.
    -- They bottom out in the Mac Lane / Kelly unit coherence laws at the *free*
    -- monoidal category over `mor`, whose _≈_/α⇒/ρ⇒/λ⇒/_⊗₁_ coincide
    -- DEFINITIONALLY with _≈Term_/α⇒/ρ⇒/λ⇒/_⊗₁_, so these land as `≈Term`.
    --------------------------------------------------------------------------------
    module K = MonProps.Kelly's Monoidal-FreeMonoidal

    λ⇒≈ρ⇒ : λ⇒ {unit} ≈Term ρ⇒ {unit}
    λ⇒≈ρ⇒ = K.coherence₃

    idρ∘α≈ρ : ∀ {A B} → id {A} ⊗₁ ρ⇒ {B} ∘ α⇒ ≈Term ρ⇒
    idρ∘α≈ρ = K.coherence₂

    λ⇒∘α⇒≈λ⇒⊗id : ∀ {A B} → λ⇒ {A ⊗₀ B} ∘ α⇒ {unit} {A} {B} ≈Term λ⇒ ⊗₁ id
    λ⇒∘α⇒≈λ⇒⊗id = K.coherence₁

    -- generic inverse-respects-≈:  if `fi`/`gi` are right/left inverses of
    -- equal morphisms `f ≈ g`, then `fi ≈ gi`.  Lets the `split` (inverse)
    -- coherences be derived from the `merge` ones rather than re-inducted.
    inv-resp : ∀ {A B} {f g : HomTerm A B} {fi gi : HomTerm B A}
             → fi ∘ f ≈Term id → g ∘ gi ≈Term id → f ≈Term g → fi ≈Term gi
    inv-resp {f = f} {g} {fi} {gi} fif ggi f≈g =
      introʳ ggi ○ (refl⟩∘⟨ ((⟺ f≈g) ⟩∘⟨refl)) ○ cancelˡ fif

    -- the right-unitor coherence on the flat merge:  merge a {[]} ≈ ρ⇒ (retyped).
    merge-ρ : (a : List X) → castW (++-identityʳ a) ∘ merge a {[]}
                            ≈Term ρ⇒ {wires a}
    merge-ρ []      = idˡ ○ λ⇒≈ρ⇒
    merge-ρ (x ∷ a) = begin
      castW (++-identityʳ (x ∷ a)) ∘ (id {Var x} ⊗₁ merge a ∘ α⇒)
        ≈⟨ ⟺ assoc ⟩
      (castW (cong (x ∷_) (++-identityʳ a)) ∘ (id {Var x} ⊗₁ merge a)) ∘ α⇒
        ≈⟨ (castW-id⊗ˡ x (++-identityʳ a) (merge a)) ⟩∘⟨refl ⟩
      id {Var x} ⊗₁ (castW (++-identityʳ a) ∘ merge a) ∘ α⇒
        ≈⟨ (refl⟩⊗⟨ (merge-ρ a)) ⟩∘⟨refl ⟩
      id {Var x} ⊗₁ ρ⇒ {wires a} ∘ α⇒
        ≈⟨ idρ∘α≈ρ ⟩
      ρ⇒ ∎

    -- the right-unitor coherence on the flat split:  split a {[]} ≈ ρ⇐ (retyped).
    -- Derived from `merge-ρ` by inversion: `split a {[]} ∘ castW (sym e)` is the
    -- inverse of `castW e ∘ merge a {[]}`, and `ρ⇐` is the inverse of `ρ⇒`.
    split-ρ : (a : List X) → split a {[]} ∘ castW (sym (++-identityʳ a))
                            ≈Term ρ⇐ {wires a}
    split-ρ a = inv-resp fi-f ρ⇒∘ρ⇐≈id (merge-ρ a)
      where
        e = ++-identityʳ a
        fi-f : (split a {[]} ∘ castW (sym e)) ∘ (castW e ∘ merge a {[]}) ≈Term id
        fi-f = cancelInner (castW-sym-r e) ○ split∘merge a

    -- `merge` associativity (built from `coherence₁` and α-naturality):
    --   merge p {q++r} ∘ (id ⊗₁ merge q {r}) ∘ α⇒
    --     ≈ castW (++-assoc p q r) ∘ (merge (p++q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
    merge-assoc : ∀ (p q r : List X)
                → merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒
                  ≈Term castW (++-assoc p q r) ∘ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
    merge-assoc []      q r = begin
      λ⇒ ∘ (id {unit} ⊗₁ merge q {r}) ∘ α⇒
        ≈⟨ pullˡ λ⇒∘id⊗f≈f∘λ⇒ ⟩
      (merge q {r} ∘ λ⇒) ∘ α⇒
        ≈⟨ pullʳ λ⇒∘α⇒≈λ⇒⊗id ⟩
      merge q {r} ∘ (λ⇒ ⊗₁ id)
        ≈⟨ ⟺ idˡ ⟩
      castW (++-assoc [] q r) ∘ (merge q {r} ∘ (λ⇒ ⊗₁ id)) ∎
    merge-assoc (x ∷ p) q r = begin
      -- LHS = merge(x∷p){q++r} ∘ (id{wires(x∷p)} ⊗ merge q) ∘ α⇒
      (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
        ∘ (id {Var x ⊗₀ wires p} ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
        ≈⟨ refl⟩∘⟨ (((⟺ id⊗id≈id) ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
      (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
        ∘ ((id {Var x} ⊗₁ id {wires p}) ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
        ≈⟨ center α-comm ⟩
      id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ merge q) ∘ α⇒) ∘ α⇒)
        ≈⟨ ⟺ assoc ⟩
      (id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ merge q) ∘ α⇒)) ∘ α⇒
        ≈⟨ (pullˡ (id⊗-∘ (merge p {q ++ r}) (id ⊗₁ merge q {r}))) ⟩∘⟨refl ⟩
      ((id ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) )
         ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
        ≈⟨ pent ⟩
      (id {Var x} ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r}) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (id⊗-∘ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) (α⇒ {wires p} {wires q} {wires r})) ⟩∘⟨refl ⟩
      (id {Var x} ⊗₁ ((merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ α⇒ {wires p} {wires q} {wires r})) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (refl⟩⊗⟨ (assoc ○ (merge-assoc p q r))) ⟩∘⟨refl ⟩
      (id ⊗₁ (castW (++-assoc p q r) ∘ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))))
        ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ (⟺ (castW-id⊗ˡ x (++-assoc p q r) _)) ⟩∘⟨refl ⟩
      (castW (cong (x ∷_) (++-assoc p q r)) ∘ (id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id))))
        ∘ (α⇒ ∘ α⇒ ⊗₁ id)
        ≈⟨ assoc ⟩
      castW (cong (x ∷_) (++-assoc p q r)) ∘
        ((id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id))
        ≈⟨ refl⟩∘⟨ tailRHS ⟩
      castW (cong (x ∷_) (++-assoc p q r)) ∘
        (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r}))
        ≈⟨ castWˡ-irr (cong (x ∷_) (++-assoc p q r)) (++-assoc (x ∷ p) q r) _ ⟩
      castW (++-assoc (x ∷ p) q r) ∘
        (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})) ∎
      where
        -- pentagon rebracketing of the two trailing associators:
        --   (X ∘ α⇒) ∘ α⇒  ≈  (X ∘ id⊗α⇒) ∘ (α⇒ ∘ α⇒⊗id)
        -- where X = id ⊗ (…).  Uses `pentagon`.
        pent : ∀ {B} {X : HomTerm (Var x ⊗₀ (wires p ⊗₀ (wires q ⊗₀ wires r))) B}
             → (X ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
               ≈Term (X ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r})
                     ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r} ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
        pent {X = X} = pullʳ (⟺ pentagon) ○ ⟺ assoc
        -- expand the RHS tail (id⊗(merge(p++q) ∘ (merge p ⊗ id))) ∘ (α⇒ ∘ α⇒⊗id)
        -- into the cons-merge form  (id⊗merge(p++q) ∘ α⇒) ∘ ((id⊗merge p ∘ α⇒)⊗id).
        tailRHS : (id {Var x} ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
                    ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r}
                       ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
                ≈Term ((id {Var x} ⊗₁ merge (p ++ q) {r}) ∘ α⇒)
                      ∘ ((id {Var x} ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})
        tailRHS = begin
          (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
            ≈⟨ (⟺ (id⊗-∘ (merge (p ++ q) {r}) (merge p {q} ⊗₁ id))) ⟩∘⟨refl ⟩
          (id ⊗₁ merge (p ++ q) ∘ id ⊗₁ (merge p ⊗₁ id)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
            ≈⟨ center (⟺ α-comm) ⟩
          id ⊗₁ merge (p ++ q) ∘ ((α⇒ ∘ (id ⊗₁ merge p) ⊗₁ id) ∘ α⇒ ⊗₁ id)
            ≈⟨ refl⟩∘⟨ pullʳ (⟺ split₁ʳ) ⟩
          id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id))
            ≈⟨ ⟺ assoc ⟩
          (id ⊗₁ merge (p ++ q) ∘ α⇒) ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id) ∎

    -- `split` associativity (dual of `merge-assoc`, by inverting it):
    --   α⇐ ∘ (id ⊗₁ split q {r}) ∘ split p {q++r}
    --     ≈ castW (++-assoc p q r) ∘ ((split p {q} ⊗₁ id) ∘ split (p++q) {r})
    -- proven uniformly (no induction) by inverting `merge-assoc`: both
    -- split-assoc-LHS and merge-assoc-LHS are mutually-inverse isos, as are
    -- the two RHSs, so the equation transports across inversion.
    split-assoc : ∀ (p q r : List X)
                → α⇐ ∘ (id {wires p} ⊗₁ split q {r}) ∘ split p {q ++ r}
                  ≈Term ((split p {q} ⊗₁ id {wires r}) ∘ split (p ++ q) {r}) ∘ castW (sym (++-assoc p q r))
    split-assoc p q r = inv-resp fi-f g-gi (merge-assoc p q r)
      where
        e = ++-assoc p q r
        mL : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires (p ++ (q ++ r)))
        mL = merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒
        fi : HomTerm (wires (p ++ (q ++ r))) ((wires p ⊗₀ wires q) ⊗₀ wires r)
        fi = α⇐ ∘ (id {wires p} ⊗₁ split q {r}) ∘ split p {q ++ r}
        mR : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires ((p ++ q) ++ r))
        mR = merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})
        giU : HomTerm (wires ((p ++ q) ++ r)) ((wires p ⊗₀ wires q) ⊗₀ wires r)
        giU = (split p {q} ⊗₁ id {wires r}) ∘ split (p ++ q) {r}
        -- fi ∘ mL ≈ id  (mutual inverses, cancelling split∘merge and α⇐∘α⇒).
        fi-f : fi ∘ mL ≈Term id
        fi-f = begin
          (α⇐ ∘ (id ⊗₁ split q) ∘ split p) ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒)
            ≈⟨ center (cancelʳ (split∘merge p)) ⟩
          α⇐ ∘ ((id ⊗₁ split q) ∘ ((id ⊗₁ merge q) ∘ α⇒))
            ≈⟨ refl⟩∘⟨ cancelˡ (id⊗-cancel (split∘merge q)) ⟩
          α⇐ ∘ α⇒
            ≈⟨ α⇐∘α⇒≈id ⟩
          id ∎
        -- (castW e ∘ mR) ∘ (giU ∘ castW (sym e)) ≈ id  via mR ∘ giU ≈ id and coercion cancel.
        g-gi : (castW e ∘ mR) ∘ (giU ∘ castW (sym e)) ≈Term id
        g-gi = coe-cancel e mR giU mR-giU
          where
            coe-cancel : ∀ {p' q'} (eq : p' ≡ q')
                           (M : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires p'))
                           (N : HomTerm (wires p') ((wires p ⊗₀ wires q) ⊗₀ wires r))
                       → M ∘ N ≈Term id → (castW eq ∘ M) ∘ (N ∘ castW (sym eq)) ≈Term id
            coe-cancel refl M N eq = idˡ ⟩∘⟨ idʳ ○ eq
            mR-giU : mR ∘ giU ≈Term id
            mR-giU =
              cancelInner ((⟺ ⊗-∘-dist) ○ ((merge∘split p) ⟩⊗⟨ idˡ) ○ id⊗id≈id)
                ○ merge∘split (p ++ q)

    liftW-castW : ∀ (p : List X) {u v : List X} (e : u ≡ v)
                → liftW p (castW e) ≈Term castW (cong (p ++_) e)
    liftW-castW []      e = castW-irr e (cong ([] ++_) e)
    liftW-castW (x ∷ p) e =
      (refl⟩⊗⟨ liftW-castW p e) ○ castW-∷ (cong (p ++_) e) ○ castW-irr _ _

    -- the structural +-associator IS the `++`-assoc transport (both α-free).
    assocW-castW : ∀ (p q s : List X)
                 → assocW p q s ≈Term castW (sym (++-assoc p q s))
    assocW-castW []      q s = ≈-Term-refl
    assocW-castW (x ∷ p) q s =
      (refl⟩⊗⟨ assocW-castW p q s) ○ castW-∷ (sym (++-assoc p q s)) ○ castW-irr _ _

    assocW⁻-castW : ∀ (p q s : List X)
                  → assocW⁻ p q s ≈Term castW (++-assoc p q s)
    assocW⁻-castW []      q s = ≈-Term-refl
    assocW⁻-castW (x ∷ p) q s =
      (refl⟩⊗⟨ assocW⁻-castW p q s) ○ castW-∷ (++-assoc p q s) ○ castW-irr _ _

    -- the frame reassociators are two-level assocW/liftW towers; both directions
    -- collapse to a single `castW`.
    assocTower≈castW : ∀ (pre c mid t : List X)
                     → assocW pre (c ++ mid) t ∘ liftW pre (assocW c mid t)
                       ≈Term castW (sym (trans (++-assoc pre (c ++ mid) t)
                                               (cong (pre ++_) (++-assoc c mid t))))
    assocTower≈castW pre c mid t =
      (assocW-castW pre (c ++ mid) t
         ⟩∘⟨ (liftW-resp pre (assocW-castW c mid t)
                ○ liftW-castW pre (sym (++-assoc c mid t))))
      ○ castW-∘ _ _ ○ castW-irr _ _

    assocTower⁻≈castW : ∀ (pre c mid t : List X)
                      → liftW pre (assocW⁻ c mid t) ∘ assocW⁻ pre (c ++ mid) t
                        ≈Term castW (trans (++-assoc pre (c ++ mid) t)
                                           (cong (pre ++_) (++-assoc c mid t)))
    assocTower⁻≈castW pre c mid t =
      ((liftW-resp pre (assocW⁻-castW c mid t) ○ liftW-castW pre (++-assoc c mid t))
         ⟩∘⟨ assocW⁻-castW pre (c ++ mid) t)
      ○ castW-∘ _ _

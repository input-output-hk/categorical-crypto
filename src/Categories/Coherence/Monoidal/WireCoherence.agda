{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Wire-coherence theory: the box-free coherence of the structural
-- `wires`/`HomTerm` layer — the `castW` object-transport algebra and
-- the ++-associators, plus the DecEq-dependent merge/split unitor &
-- pentagon coherence.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.WireCoherence where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties

open import Categories.Category
import Categories.Category.Monoidal.Properties as MonProps
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Reasoning.Ext as MRExt
open import Categories.FreeMonoidal

module WireCoh (X : Set)
               (mor : FreeMonoidalHelper.ObjTerm Mon X → FreeMonoidalHelper.ObjTerm Mon X → Set)
               where
  open FreeMonoidalHelper Mon X
  open FreeMonoidalHelper.Mor Mon X mor
  open Category.HomReasoning FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; split₁ʳ)
  open MR FreeMonoidal
  open MRExt FreeMonoidal

  -- the object transport along a propositional equality of wire-lists.
  castW : ∀ {u v : List X} → u ≡ v → HomTerm (wires u) (wires v)
  castW refl = id

  castW-∷ : ∀ {x : X} {u v : List X} (e : u ≡ v) → id ⊗₁ castW e ≈Term castW (cong (x ∷_) e)
  castW-∷ refl = id⊗id≈id

  castW-isoˡ : ∀ {u v : List X} (e : u ≡ v) → castW (sym e) ∘ castW e ≈Term id
  castW-isoˡ refl = idˡ

  castW-isoʳ : ∀ {u v : List X} (e : u ≡ v) → castW e ∘ castW (sym e) ≈Term id
  castW-isoʳ refl = idˡ
  --------------------------------------------------------------------------------
  -- The structural associators on wire-lists
  --------------------------------------------------------------------------------
  assocW : (p q s : List X) → HomTerm (wires (p ++ (q ++ s))) (wires ((p ++ q) ++ s))
  assocW p q s = castW (sym (++-assoc p q s))

  assocW⁻ : (p q s : List X) → HomTerm (wires ((p ++ q) ++ s)) (wires (p ++ (q ++ s)))
  assocW⁻ p q s = castW (++-assoc p q s)

  assocW⁻∘assocW : ∀ (p q s : List X) → assocW⁻ p q s ∘ assocW p q s ≈Term id
  assocW⁻∘assocW p q s = castW-isoʳ (++-assoc p q s)

  --------------------------------------------------------------------------------
  -- The DecEq-dependent layer: the `castW` helper kit and the merge/split
  -- right-unitor & pentagon coherence family.
  --------------------------------------------------------------------------------
  module WireCohDec ⦃ _ : DecEq X ⦄ where
    -- the far end is an arbitrary object, since the merge/split steps below
    -- need bracketed tensors of wires, not flat ones.
    castW-id⊗ˡ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm R (wires p))
               → castW (cong (x ∷_) e) ∘ (id ⊗₁ h) ≈Term id ⊗₁ (castW e ∘ h)
    castW-id⊗ˡ x e h = (⟺ (castW-∷ e) ⟩∘⟨refl) ○ id⊗-∘ (castW e) h

    --------------------------------------------------------------------------------
    -- The merge/split coherence family: the right-unitor coherence
    -- (`merge-ρ`/`split-ρ`) and the pentagon associativity
    -- (`merge-assoc`/`split-assoc`).  They bottom out in the Mac Lane / Kelly
    -- unit coherence laws at the free monoidal category over `mor`, whose `_≈_`
    -- coincides definitionally with `_≈Term_`.
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

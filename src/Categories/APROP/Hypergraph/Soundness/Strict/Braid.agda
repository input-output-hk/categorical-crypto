{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict Yang-Baxter braid `strict-braid` — the KEYSTONE residual of the
-- strictified soundness pipeline (`PermDischarge.Discharge.StrictBraid`).
--
-- The statement is GENERATOR-FREE, so it holds in every `FreeStrictSMC.Build`
-- instance.  We prove it generically, over an arbitrary generator family `mor`,
-- by transporting the proven non-strict `SigmaBlockHexagon.σ-block-hexagon`
-- (over the EMPTY free symmetric monoidal category `d₀`, whose generators are
-- `⊥`) through a self-contained strictification functor `st` into the strict
-- SMC `Build X _≟X_ mor`.  The functor mirrors `Strict.Boundary.st` but its
-- generator case is absurd (`λ ()`), so `st` and `st-resp-≈` are mor-agnostic.
--
-- Because the σ-block frames are SINGLETONS, the two associators in each
-- `st (σ-block …)` are `coe refl` and collapse, leaving exactly the strict swap
-- blocks `σˢ [x] [y] ⊗ˢ idˢ {tail}`.
--
-- `PermDischarge.Discharge` opens `Build X _≟X_ (λ _ _ → V)`, so it instantiates
-- `Generic.strict-braid` at `mor := (λ _ _ → V)`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Braid
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Categories.FreeMonoidal
  using (FreeMonoidalData; Variant; _≤_; v≤v)
open Variant
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; flatten-unflatten)
open import Categories.FreeStrictSMC using (module Build)

--------------------------------------------------------------------------------
-- The empty free symmetric monoidal category over `X`: same objects as `sig`'s
-- (so `flatten` applies), no generators.

private
  d₀ : FreeMonoidalData
  d₀ = record { v = Symm ; X = X ; mor = λ _ _ → ⊥ }

  instance
    symm≤d₀ : Symm ≤ FreeMonoidalData.v d₀
    symm≤d₀ = v≤v

import Categories.FreeMonoidal as FM
open FM.FreeMonoidal d₀ using
  ( ObjTerm; HomTerm; _≈Term_
  ; id; _∘_; _⊗₁_; λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐; σ
  ; unit; _⊗₀_; Var
  ; idˡ; idʳ; assoc; ∘-resp-≈; ≈-Term-refl; ≈-Term-sym; ≈-Term-trans
  ; id⊗id≈id; ⊗-resp-≈; ⊗-∘-dist; λ⇐∘λ⇒≈id; λ⇒∘λ⇐≈id; ρ⇐∘ρ⇒≈id; ρ⇒∘ρ⇐≈id
  ; α⇐∘α⇒≈id; α⇒∘α⇐≈id; λ⇒∘id⊗f≈f∘λ⇒; ρ⇒∘f⊗id≈f∘ρ⇒; α-comm; triangle; pentagon
  ; σ∘σ≈id; σ∘[f⊗g]≈[g⊗f]∘σ; hexagon )
  renaming (var to Agen)

import Categories.FreeSMC.SigmaBlockHexagon
  d₀ as SBH
open SBH using (σ-block; σ-block-hexagon)

--------------------------------------------------------------------------------
-- The generic part, over an arbitrary generator family.

module Generic (mor : List X → List X → Set) where

  open Build X _≟X_ mor

  ------------------------------------------------------------------------
  -- The cast kit (mirrors `Strict.Boundary`; all derived from `Build`).

  coe : ∀ {xs ys : List X} → xs ≡ ys → HomS xs ys
  coe p = castˢ refl p idˢ

  coe-id≈ : ∀ {xs} (p : xs ≡ xs) → coe p ≈ˢ idˢ
  coe-id≈ p = cast-id refl p

  coe-uip : ∀ {xs ys} (p q : xs ≡ ys) → coe p ≈ˢ coe q
  coe-uip p q = ≡⇒≈ˢ (cast-irrel refl refl p q idˢ)

  coe-trans : ∀ {xs ys zs} (p : xs ≡ ys) (q : ys ≡ zs)
            → coe q ∘ˢ coe p ≈ˢ coe (trans p q)
  coe-trans refl q = idʳ

  coe-cancel : ∀ {xs ys} (p : xs ≡ ys) → coe (sym p) ∘ˢ coe p ≈ˢ idˢ
  coe-cancel refl = idˡ

  coe-cancelʳ : ∀ {xs ys} (p : xs ≡ ys) → coe p ∘ˢ coe (sym p) ≈ˢ idˢ
  coe-cancelʳ refl = idˡ

  cast⇒comm
    : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys')
        {t : HomS xs ys} {u : HomS xs' ys'}
    → castˢ p q t ≈ˢ u → coe q ∘ˢ t ≈ˢ u ∘ˢ coe p
  cast⇒comm refl refl e = ≈-trans idˡ (≈-trans e (≈-sym idʳ))

  coe-conj
    : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
    → castˢ p q t ≈ˢ coe q ∘ˢ t ∘ˢ coe (sym p)
  coe-conj refl refl t = ≈-sym (≈-trans idˡ idʳ)

  coe-frameˡ : ∀ {xs ys} (p : xs ≡ ys) (ls : List X)
             → coe p ⊗ˢ idˢ {ls} ≈ˢ coe (cong (_++ ls) p)
  coe-frameˡ p ls =
    ≈-trans (≡⇒≈ˢ (cast-⊗ˡ refl p idˢ))
            (cast-resp refl (cong (_++ ls) p) ⊗-id)

  coe-frameʳ : ∀ {xs ys} (ls : List X) (p : xs ≡ ys)
             → idˢ {ls} ⊗ˢ coe p ≈ˢ coe (cong (ls ++_) p)
  coe-frameʳ ls p =
    ≈-trans (≈-sym (cast-⊗-frame idˢ refl p idˢ refl (cong (ls ++_) p)))
            (cast-resp refl (cong (ls ++_) p) ⊗-id)

  private
    elim²
      : ∀ {as bs cs} {f : HomS as bs} {f' : HomS bs as} {h : HomS cs as}
      → f' ∘ˢ f ≈ˢ idˢ → f' ∘ˢ (f ∘ˢ h) ≈ˢ h
    elim² e = ≈-trans (≈-sym assocˢ) (≈-trans (∘-resp e ≈-refl) idˡ)

    inv-uniqueˢ
      : ∀ {as bs} {u : HomS as bs} {v w : HomS bs as}
      → v ∘ˢ u ≈ˢ idˢ → u ∘ˢ w ≈ˢ idˢ → v ≈ˢ w
    inv-uniqueˢ e₁ e₂ =
      ≈-trans (≈-sym idʳ)
      (≈-trans (∘-resp ≈-refl (≈-sym e₂))
      (≈-trans (≈-sym assocˢ)
      (≈-trans (∘-resp e₁ ≈-refl) idˡ)))

  ------------------------------------------------------------------------
  -- The strictification functor `st : HomTerm A B → HomS (flatten A) (flatten B)`.

  st : ∀ {A B} → HomTerm A B → HomS (flatten A) (flatten B)
  st (Agen ())
  st id               = idˢ
  st (g ∘ f)          = st g ∘ˢ st f
  st (f ⊗₁ g)         = st f ⊗ˢ st g
  st λ⇒               = idˢ
  st λ⇐               = idˢ
  st (ρ⇒ {A})         = coe (++-identityʳ (flatten A))
  st (ρ⇐ {A})         = coe (sym (++-identityʳ (flatten A)))
  st (α⇒ {A} {B} {C}) = coe (++-assoc (flatten A) (flatten B) (flatten C))
  st (α⇐ {A} {B} {C}) = coe (sym (++-assoc (flatten A) (flatten B) (flatten C)))
  st (σ {A} {B})      = σˢ (flatten A) (flatten B)

  st-resp-≈ : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → st f ≈ˢ st g
  st-resp-≈ idˡ                      = idˡ
  st-resp-≈ idʳ                      = idʳ
  st-resp-≈ assoc                    = assocˢ
  st-resp-≈ (∘-resp-≈ e₁ e₂)         = ∘-resp (st-resp-≈ e₁) (st-resp-≈ e₂)
  st-resp-≈ ≈-Term-refl              = ≈-refl
  st-resp-≈ (≈-Term-sym e)           = ≈-sym (st-resp-≈ e)
  st-resp-≈ (≈-Term-trans e₁ e₂)     = ≈-trans (st-resp-≈ e₁) (st-resp-≈ e₂)
  st-resp-≈ id⊗id≈id                 = ⊗-id
  st-resp-≈ (⊗-resp-≈ e₁ e₂)         = ⊗-resp (st-resp-≈ e₁) (st-resp-≈ e₂)
  st-resp-≈ ⊗-∘-dist                 = ≈-sym interchangeˢ
  st-resp-≈ λ⇐∘λ⇒≈id                 = idˡ
  st-resp-≈ λ⇒∘λ⇐≈id                 = idˡ
  st-resp-≈ (ρ⇐∘ρ⇒≈id {A})           = coe-cancel (++-identityʳ (flatten A))
  st-resp-≈ (ρ⇒∘ρ⇐≈id {A})           = coe-cancelʳ (++-identityʳ (flatten A))
  st-resp-≈ (α⇐∘α⇒≈id {A} {B} {C})   =
    coe-cancel (++-assoc (flatten A) (flatten B) (flatten C))
  st-resp-≈ (α⇒∘α⇐≈id {A} {B} {C})   =
    coe-cancelʳ (++-assoc (flatten A) (flatten B) (flatten C))
  st-resp-≈ (λ⇒∘id⊗f≈f∘λ⇒ {f = f})   =
    ≈-trans idˡ (≈-trans (⊗-unitˡˢ (st f)) (≈-sym idʳ))
  st-resp-≈ (ρ⇒∘f⊗id≈f∘ρ⇒ {f = f})   =
    cast⇒comm (++-identityʳ _) (++-identityʳ _) (⊗-unitʳˢ (st f))
  st-resp-≈ (α-comm {f = f} {g = g} {h = h}) = α-comm-case f g h
    where
      α-comm-case
        : ∀ {A B C D E F'} (f : HomTerm A B) (g : HomTerm C D) (h : HomTerm E F')
        → coe (++-assoc (flatten B) (flatten D) (flatten F'))
            ∘ˢ ((st f ⊗ˢ st g) ⊗ˢ st h)
          ≈ˢ (st f ⊗ˢ (st g ⊗ˢ st h))
            ∘ˢ coe (++-assoc (flatten A) (flatten C) (flatten E))
      α-comm-case {A} {B} {C} {D} {E} {F'} f g h =
        cast⇒comm (++-assoc (flatten A) (flatten C) (flatten E))
                  (++-assoc (flatten B) (flatten D) (flatten F'))
                  (⊗-assocˢ (st f) (st g) (st h))
  st-resp-≈ (triangle {A} {B})       =
    ≈-trans (∘-resp ⊗-id ≈-refl)
    (≈-trans idˡ
    (≈-trans (coe-uip (++-assoc a [] b) (cong (_++ b) (++-identityʳ a)))
      (≈-sym (coe-frameˡ (++-identityʳ a) b))))
    where a = flatten A ; b = flatten B
  st-resp-≈ (pentagon {A} {B} {C} {D}) =
    ≈-trans (∘-resp (coe-frameʳ a P₁) (∘-resp ≈-refl (coe-frameˡ P₃ d)))
    (≈-trans (∘-resp ≈-refl (coe-trans (cong (_++ d) P₃) P₂))
    (≈-trans (coe-trans (trans (cong (_++ d) P₃) P₂) (cong (a ++_) P₁))
    (≈-trans (coe-uip _ (trans P₅ P₄))
      (≈-sym (coe-trans P₅ P₄)))))
    where
      a = flatten A ; b = flatten B ; c = flatten C ; d = flatten D
      P₁ = ++-assoc b c d
      P₂ = ++-assoc a (b ++ c) d
      P₃ = ++-assoc a b c
      P₄ = ++-assoc a b (c ++ d)
      P₅ = ++-assoc (a ++ b) c d
  st-resp-≈ σ∘σ≈id                   = σ-σˢ
  st-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ          = σ-natˢ
  st-resp-≈ (hexagon {A} {B} {C})    = ≈-sym reduce
    where
      a = flatten A ; b = flatten B ; c = flatten C
      P = ++-assoc a b c
      Q = ++-assoc b c a
      R = ++-assoc b a c

      X₁ = σˢ a b ⊗ˢ idˢ {c}
      X₂ = idˢ {b} ⊗ˢ σˢ a c
      W₁ = σˢ b a ⊗ˢ idˢ {c}
      W₂ = idˢ {b} ⊗ˢ σˢ c a

      L : HomS ((a ++ b) ++ c) (b ++ c ++ a)
      L = X₂ ∘ˢ coe R ∘ˢ X₁

      step-σʳ : W₂ ∘ˢ X₂ ≈ˢ idˢ
      step-σʳ = ≈-trans interchangeˢ (≈-trans (⊗-resp idˡ σ-σˢ) ⊗-id)

      step-σˡ : W₁ ∘ˢ X₁ ≈ˢ idˢ
      step-σˡ = ≈-trans interchangeˢ (≈-trans (⊗-resp σ-σˢ idˡ) ⊗-id)

      u-form
        : σˢ (b ++ c) a
          ≈ˢ coe P ∘ˢ (W₁ ∘ˢ ((coe (sym R) ∘ˢ W₂) ∘ˢ coe Q))
      u-form =
        ≈-trans (σ-hexˢ b c a)
        (≈-trans (coe-conj (sym Q) P (W₁ ∘ˢ castˢ refl (sym R) W₂))
        (∘-resp ≈-refl
          (≈-trans assocˢ
            (∘-resp ≈-refl
              (∘-resp (≈-trans (coe-conj refl (sym R) W₂) (∘-resp ≈-refl idʳ))
                      (coe-uip (sym (sym Q)) Q))))))

      M-nest : L ∘ˢ coe (sym P) ≈ˢ X₂ ∘ˢ (coe R ∘ˢ (X₁ ∘ˢ coe (sym P)))
      M-nest = ≈-trans assocˢ (∘-resp ≈-refl assocˢ)

      cancel
        : σˢ (b ++ c) a ∘ˢ (coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))) ≈ˢ idˢ
      cancel =
        ≈-trans (∘-resp u-form ≈-refl)
        (≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl assocˢ)
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                   (∘-resp ≈-refl (elim² (coe-cancelʳ Q)))))
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                   (∘-resp ≈-refl (∘-resp ≈-refl M-nest))))
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                   (∘-resp ≈-refl (elim² step-σʳ))))
        (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (elim² (coe-cancel R))))
        (≈-trans (∘-resp ≈-refl (elim² step-σˡ))
          (coe-cancelʳ P))))))))))

      H : σˢ a (b ++ c) ≈ˢ coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))
      H = inv-uniqueˢ σ-σˢ cancel

      reduce : coe Q ∘ˢ σˢ a (b ++ c) ∘ˢ coe P ≈ˢ L
      reduce =
        ≈-trans (∘-resp ≈-refl (∘-resp H ≈-refl))
        (≈-trans (∘-resp ≈-refl assocˢ)
        (≈-trans (elim² (coe-cancelʳ Q))
        (≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl (coe-cancel P)) idʳ))))

  ----------------------------------------------------------------------
  -- `st` of a σ-block over single-strand A,B and arbitrary tail C reduces to
  -- a strict swap block: both associators are `coe refl` (singleton frames).

  private
    st-σ-block
      : ∀ (a b : X) (Cob : ObjTerm)
      → st (σ-block {Var a} {Var b} {Cob})
        ≈ˢ σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {flatten Cob}
    st-σ-block a b Cob =
      ≈-trans (∘-resp (coe-id≈ (++-assoc (b ∷ []) (a ∷ []) (flatten Cob))) ≈-refl)
      (≈-trans idˡ
      (≈-trans (∘-resp ≈-refl
                 (coe-id≈ (sym (++-assoc (a ∷ []) (b ∷ []) (flatten Cob)))))
        idʳ))

  ----------------------------------------------------------------------
  -- The braid statement as a predicate on the tail list.

  BraidAt : (a b c : X) → List X → Set
  BraidAt a b c L =
    ((σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {a ∷ L})
        ∘ˢ (idˢ {b ∷ []} ⊗ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {L})))
          ∘ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {c ∷ L})
    ≈ˢ
    ((idˢ {c ∷ []} ⊗ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {L}))
        ∘ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {b ∷ L}))
          ∘ˢ (idˢ {a ∷ []} ⊗ˢ (σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {L}))

  private
    -- `st` of the σ-block-hexagon LHS / RHS, in right-associated form.
    st-hex-lhs
      : ∀ (a b c : X) (C : ObjTerm)
      → st ((id {Var c} ⊗₁ σ-block {Var a} {Var b} {C})
              ∘ σ-block {Var a} {Var c} {Var b ⊗₀ C}
              ∘ (id {Var a} ⊗₁ σ-block {Var b} {Var c} {C}))
        ≈ˢ (idˢ {c ∷ []} ⊗ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {flatten C}))
            ∘ˢ ((σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {b ∷ flatten C})
              ∘ˢ (idˢ {a ∷ []}
                    ⊗ˢ (σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {flatten C})))
    st-hex-lhs a b c C =
      ∘-resp
        (⊗-resp ≈-refl (st-σ-block a b C))
        (∘-resp (st-σ-block a c (Var b ⊗₀ C))
                (⊗-resp ≈-refl (st-σ-block b c C)))

    st-hex-rhs
      : ∀ (a b c : X) (C : ObjTerm)
      → st (σ-block {Var b} {Var c} {Var a ⊗₀ C}
              ∘ (id {Var b} ⊗₁ σ-block {Var a} {Var c} {C})
              ∘ σ-block {Var a} {Var b} {Var c ⊗₀ C})
        ≈ˢ (σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {a ∷ flatten C})
            ∘ˢ ((idˢ {b ∷ []}
                  ⊗ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {flatten C}))
              ∘ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {c ∷ flatten C}))
    st-hex-rhs a b c C =
      ∘-resp
        (st-σ-block b c (Var a ⊗₀ C))
        (∘-resp (⊗-resp ≈-refl (st-σ-block a c C))
                (st-σ-block a b (Var c ⊗₀ C)))

  ----------------------------------------------------------------------
  -- The strict Yang-Baxter braid, in EVERY tail `L`: realise `L` as
  -- `flatten (Var-list)` — here we simply use the `ObjTerm` whose flattening
  -- is `L`, namely an arbitrary `C` with `flatten C ≡ L`.  Choosing `C`'s
  -- flattening to be `L` exactly: see `strict-braid` below, which feeds the
  -- canonical `unflatten L` and transports along `flatten (unflatten L) ≡ L`.
  braid-flat : ∀ (a b c : X) (C : ObjTerm) → BraidAt a b c (flatten C)
  braid-flat a b c C =
    ≈-trans assocˢ
    (≈-trans (≈-sym (st-hex-rhs a b c C))
    (≈-trans (≈-sym (st-resp-≈ (σ-block-hexagon
                       {Var a} {Var b} {Var c} {C})))
    (≈-trans (st-hex-lhs a b c C)
      (≈-sym assocˢ))))

  -- The keystone: the strict Yang-Baxter braid for every right tail `L`,
  -- obtained from `braid-flat (unflatten L)` and `flatten (unflatten L) ≡ L`.
  -- This is exactly `PermDischarge.Discharge.StrictBraid` once `mor := (λ _ _ → V)`.
  strict-braid : ∀ (a b c : X) (L : List X) → BraidAt a b c L
  strict-braid a b c L =
    subst (BraidAt a b c) (flatten-unflatten L) (braid-flat a b c (unflatten L))

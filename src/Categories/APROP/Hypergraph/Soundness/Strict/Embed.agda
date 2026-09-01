{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The BOUNDARY of the strictified pipeline: `emb : HomS → HomTerm` (the
-- embedding of the presented strict SMC back into the non-strict free SMC)
-- and `emb-resp-≈ˢ` — the one-time Mac-Lane payment per strict axiom that
-- replaces the per-site M-tax of the non-strict pipeline.  Generators are
-- arbitrary HomTerms (`morL`); other generator families enter via
-- `FreeStrictSMC.Map` along their interpretation into HomTerms.
--
-- Structure: the substantial cases (`⊗-assocˢ` — the laxator associativity,
-- `⊗-unitʳˢ`, `σ-hexˢ`, `σ-unitˢ`) are proved first as standalone lemmas;
-- `EmbRespFull.emb-resp-≈ˢ` at the end closes all sixteen, the cheap ones
-- inline.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Embed
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-++-≅
        ; subst-id-dom; subst-id-cod
        ; cast-dc; cod-cancel; dom-cancel )
open import Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal sig
  using (c-iso-assoc-to; c-iso-assoc-from)

open import Categories.FreeStrictSMC using (module Build)

open import Data.List.Properties using (++-assoc; ++-identityʳ)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal
  using ( pullˡ; pullʳ; cancelˡ; cancelʳ; cancelInner )
open import Categories.Category.Monoidal.Reasoning Monoidal-FreeMonoidal
  using ( merge₁ʳ; merge₂ʳ; split₁ˡ; split₁ʳ )

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

-- shorthands for the laxator
private
  U : List X → ObjTerm
  U = unflatten

  T : ∀ a b → HomTerm (U a ⊗₀ U b) (U (a ++ b))
  T a b = _≅_.to (unflatten-++-≅ a b)

  F : ∀ a b → HomTerm (U (a ++ b)) (U a ⊗₀ U b)
  F a b = _≅_.from (unflatten-++-≅ a b)

--------------------------------------------------------------------------------
-- The strict side: generators = arbitrary HomTerms between unflattens.

morL : List X → List X → Set
morL as bs = HomTerm (U as) (U bs)

open Build X _≟X_ morL public

--------------------------------------------------------------------------------
-- The embedding.

emb : ∀ {xs ys} → HomS xs ys → HomTerm (U xs) (U ys)
emb idˢ                              = id
emb (g ∘ˢ f)                         = emb g ∘ emb f
emb (_⊗ˢ_ {xs} {ys} {us} {vs} f g)   = T ys vs ∘ (emb f ⊗₁ emb g) ∘ F xs us
emb (genˢ t)                         = t
emb (σˢ xs ys)                       = T ys xs ∘ σ ∘ F xs ys

-- the de-casting step, used at every `castˢ` case below.  At `refl`/`refl`
-- `castˢ` vanishes and the two conjugating `subst-id-*` are `id`, so the
-- whole statement is the unit pair read backwards.
emb-cast-conj
  : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
  → emb (castˢ p q t) ≈Term subst-id-cod q ∘ emb t ∘ subst-id-dom p
emb-cast-conj refl refl t = ≈-Term-sym (≈-Term-trans idˡ idʳ)


--------------------------------------------------------------------------------
-- THE CRUX: the `⊗-assocˢ` case — the laxator-associativity payment,
-- made ONCE here instead of per positional site.

private
  -- α-conjugation of a ⊗-pair (the Mac-Lane move, once)
  α-conjE
    : ∀ {A B C A' B' C'} (m : HomTerm A A') (n : HomTerm B B') (k : HomTerm C C')
    → (m ⊗₁ n) ⊗₁ k
      ≈Term α⇐ ∘ (m ⊗₁ (n ⊗₁ k)) ∘ α⇒
  α-conjE m n k = ⟺ (cancelˡ α⇐∘α⇒≈id) ○ (refl⟩∘⟨ α-comm)

⊗-assoc-case
  : ∀ {xs ys us vs ps qs}
      (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
  → emb (castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h))
    ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
⊗-assoc-case {xs} {ys} {us} {vs} {ps} {qs} f g h =
  emb-cast-conj (++-assoc xs us ps) (++-assoc ys vs qs) _ ○ main
  where
    A₁ = ++-assoc xs us ps
    A₂ = ++-assoc ys vs qs
    ef = emb f ; eg = emb g ; eh = emb h
    Sd₁ = subst-id-dom A₁ ; Sc₁ = subst-id-cod A₁
    Sd₂ = subst-id-dom A₂ ; Sc₂ = subst-id-cod A₂
    N   = ef ⊗₁ (eg ⊗₁ eh)

    -- E ≈ Sd₂ ∘ emb (f ⊗ (g ⊗ h)) ∘ Sc₁
    core : emb ((f ⊗ˢ g) ⊗ˢ h) ≈Term Sd₂ ∘ emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁
    core =
      -- phase 1: split the G-side laxator legs out of the left ⊗-factor
      (refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ split₁ʳ) ⟩∘⟨refl))
      -- phase 2: α-conjugate the ⊗-pair (the Mac Lane move, once)
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ (α-conjE ef eg eh ⟩∘⟨refl)) ⟩∘⟨refl))
      -- phase 3: flatten to a right-nested spine, then re-bracket the three
      -- cod-side legs into one factor
      ○ (refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ ≈-Term-sym FM.assoc
      ○ ≈-Term-sym FM.assoc
      ○ (FM.assoc ⟩∘⟨refl)
      -- phase 4: the two laxator-associativity payments (cod side, then dom)
      ○ (c-iso-assoc-to ys vs qs ⟩∘⟨refl)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (c-iso-assoc-from xs us ps))
      -- phase 5: re-nest, then fuse the two ⊗-frames onto `N`
      ○ FM.assoc
      ○ (refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
      ○ (refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (≈-Term-trans idʳ idˡ) FM.assoc ⟩∘⟨refl))
      -- phase 6: re-bracket into `emb (f ⊗ˢ (g ⊗ˢ h))`'s own shape
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ ≈-Term-sym FM.assoc)

    main : Sc₂ ∘ emb ((f ⊗ˢ g) ⊗ˢ h) ∘ Sd₁ ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
    main =
      (refl⟩∘⟨ (core ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (cod-cancel A₁)))
      ○ cancelˡ (cod-cancel A₂)

--------------------------------------------------------------------------------
-- The `⊗-unitʳˢ` case — the right-unit payment.
--
-- The `ρ⇒ ∘ F a []` collapse is NOT re-derived here: it IS the boundary
-- layer's list coherence `BridgeCoherence.ρ⇒-coh-list`, whose statement
-- `subst-id-cod (++-identityʳ a) ≈Term ρ⇒ ∘ from (unflatten-++-≅ a [])`
-- is this one read through `Unflatten.cast-dc` (`subst-id-dom (sym p)` IS
-- `subst-id-cod p`).  `TR` is then its inverse composite.

import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig as BC

private
  -- ρ⇒ ∘ F a []  collapses to a pure cast
  FR : ∀ a → ρ⇒ ∘ F a [] ≈Term subst-id-dom (sym (++-identityʳ a))
  FR a = ⟺ (BC.ρ⇒-coh-list a) ○ ⟺ (cast-dc (++-identityʳ a))

  -- its inverse composite, by uniqueness of inverses
  TR : ∀ a → T a [] ∘ ρ⇐ ≈Term subst-id-cod (sym (++-identityʳ a))
  TR a =
    ⟺ (cancelˡ (cod-cancel (sym (++-identityʳ a))))
    ○ (refl⟩∘⟨ (⟺ (FR a) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ collapse)
    ○ idʳ
    where
      collapse : (ρ⇒ ∘ F a []) ∘ (T a [] ∘ ρ⇐) ≈Term id
      collapse =
        cancelInner (_≅_.isoʳ (unflatten-++-≅ a [])) ○ ρ⇒∘ρ⇐≈id

⊗-unitʳ-case
  : ∀ {xs ys} (f : HomS xs ys)
  → emb (castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}))
    ≈Term emb f
⊗-unitʳ-case {xs} {ys} f =
  emb-cast-conj (++-identityʳ xs) (++-identityʳ ys) _ ○ main
  where
    ef = emb f
    Sd = subst-id-dom (++-identityʳ xs)
    Sc = subst-id-cod (++-identityʳ ys)

    -- ef ⊗ id_unit ≈ ρ⇐ ∘ ef ∘ ρ⇒
    padE : ef ⊗₁ id {unit} ≈Term ρ⇐ ∘ ef ∘ ρ⇒
    padE = ⟺ (cancelˡ ρ⇐∘ρ⇒≈id) ○ (refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒)

    -- the de-cast'd embedding collapses
    main : Sc ∘ emb (f ⊗ˢ idˢ {[]}) ∘ Sd ≈Term ef
    main =
      -- pad `ef` with the ρ-pair, slide the laxator legs onto it (`TR`/`FR`),
      -- then the two transported-identity pairs cancel.
      (refl⟩∘⟨ ((refl⟩∘⟨ (padE ⟩∘⟨refl)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ (≈-Term-sym FM.assoc ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((TR ys ⟩∘⟨ (refl⟩∘⟨ FR xs)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (dom-cancel (++-identityʳ xs))))
      ○ cancelˡ (cod-cancel (++-identityʳ ys))

--------------------------------------------------------------------------------
-- The `σ-hexˢ` case — the block-braiding payment.  Strategy: reduce BOTH
-- sides to the common normal form
--   N = Sc A₂ ∘ T (zs++xs) ys ∘ ((T zs xs ∘ σ) ⊗ id)
--         ∘ α⇐ ∘ (id ⊗ (σ ∘ F ys zs)) ∘ F xs (ys++zs) ∘ Sc A₁ .

private
  -- fold two right-framed / left-framed tensor factors under a tail W
  fold⊗ʳ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (D ⊗₀ A)}
    → (id {D} ⊗₁ p) ∘ ((id {D} ⊗₁ q) ∘ W) ≈Term (id {D} ⊗₁ (p ∘ q)) ∘ W
  fold⊗ʳ = pullˡ merge₂ʳ

  fold⊗ˡ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (A ⊗₀ D)}
    → (p ⊗₁ id {D}) ∘ ((q ⊗₁ id {D}) ∘ W) ≈Term ((p ∘ q) ⊗₁ id {D}) ∘ W
  fold⊗ˡ = pullˡ merge₁ʳ

  -- σ at a fused block, split through the laxator
  σ-split
    : ∀ xs ys zs
    → σ {U (xs ++ ys)} {U zs}
      ≈Term (id ⊗₁ T xs ys) ∘ σ {U xs ⊗₀ U ys} {U zs} ∘ (F xs ys ⊗₁ id)
  σ-split xs ys zs =
    ⟺ (pullˡ (⟺ σ∘[f⊗g]≈[g⊗f]∘σ)
        ○ cancelʳ (⊗-cancel (_≅_.isoˡ (unflatten-++-≅ xs ys)) idˡ))

  -- L1: the cod-side laxator chain, c-iso-assoc-to re-oriented
  L1 : ∀ xs ys zs
     → T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys)
       ≈Term subst-id-cod (++-assoc zs xs ys)
             ∘ T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id) ∘ α⇐
  L1 xs ys zs =
    ⟺ ( (refl⟩∘⟨ c-iso-assoc-to zs xs ys)
      ○ cancelˡ (cod-cancel (++-assoc zs xs ys)) )

  -- L2: the dom-side laxator chain, c-iso-assoc-from re-oriented
  L2 : ∀ xs ys zs
     → (F xs ys ⊗₁ id {U zs}) ∘ F (xs ++ ys) zs
       ≈Term α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
             ∘ subst-id-cod (++-assoc xs ys zs)
  L2 xs ys zs =
    ⟺ ( (refl⟩∘⟨ ⟺ (c-iso-assoc-from xs ys zs))
      ○ cancelˡ α⇐∘α⇒≈id )

  -- J: the junction between the two σ-frames on the RHS
  J : ∀ xs ys zs
    → F (xs ++ zs) ys ∘ subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys)
      ≈Term (T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys)
  J xs ys zs =
    ⟺ ( ⟺ FM.assoc
      ○ (star ⟩∘⟨refl)
      ○ pullʳ (pullʳ (cancelʳ (id⊗-cancel (_≅_.isoˡ (unflatten-++-≅ zs ys))))) )
    where
      star : (T xs zs ⊗₁ id {U ys}) ∘ α⇐
             ≈Term F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
                   ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)
      star =
        ⟺ (cancelˡ (_≅_.isoʳ (unflatten-++-≅ (xs ++ zs) ys)))
        ○ (refl⟩∘⟨ c-iso-assoc-to xs zs ys)

private
  -- α⇒ ∘ (α⇐ ∘ W) ≈ W
  tidyL : ∀ xs zs → (T zs xs ∘ σ ∘ F xs zs) ∘ T xs zs ≈Term T zs xs ∘ σ
  tidyL xs zs = pullʳ (cancelʳ (_≅_.isoʳ (unflatten-++-≅ xs zs)))

  tidyR : ∀ ys zs → F zs ys ∘ (T zs ys ∘ σ ∘ F ys zs) ≈Term σ ∘ F ys zs
  tidyR ys zs = cancelˡ (_≅_.isoʳ (unflatten-++-≅ zs ys))

  lhs→N
    : ∀ xs ys zs
    → emb (σˢ (xs ++ ys) zs)
      ≈Term subst-id-cod (++-assoc zs xs ys)
            ∘ T (zs ++ xs) ys ∘ ((T zs xs ∘ σ) ⊗₁ id)
            ∘ α⇐ ∘ (id ⊗₁ (σ ∘ F ys zs)) ∘ F xs (ys ++ zs)
            ∘ subst-id-cod (++-assoc xs ys zs)
  lhs→N xs ys zs =
    -- phase 1: split σ off the fused block, then expand it by the hexagon
    (refl⟩∘⟨ (σ-split xs ys zs ⟩∘⟨refl))
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ (σ-A⊗B-expand ⟩∘⟨refl)) ⟩∘⟨refl))
    -- phase 2: reassociate onto the dom-side laxator run, then L2
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ L2 xs ys zs)
    -- phase 3: regroup onto the cod-side laxator run, then L1
    ○ ≈-Term-sym FM.assoc
    ○ (L1 xs ys zs ⟩∘⟨refl)
    -- phase 4: expose the inner α⇐/α⇒ pair and cancel it
    ○ ((refl⟩∘⟨ ≈-Term-sym FM.assoc) ⟩∘⟨refl)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ cancel-mid-iso α⇐∘α⇒≈id
    -- phase 5: fold the left frame into (T zs xs ∘ σ) ⊗ id
    ○ (refl⟩∘⟨ FM.assoc) ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    -- phase 6: cancel the outer α-pair and fold the right frame
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ α⇒∘α⇐≈id)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ)

private
  rhs→N
    : ∀ xs ys zs
    → emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
             ((σˢ xs zs ⊗ˢ idˢ {ys})
               ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                    (idˢ {xs} ⊗ˢ σˢ ys zs)))
      ≈Term subst-id-cod (++-assoc zs xs ys)
            ∘ T (zs ++ xs) ys ∘ ((T zs xs ∘ σ) ⊗₁ id)
            ∘ α⇐ ∘ (id ⊗₁ (σ ∘ F ys zs)) ∘ F xs (ys ++ zs)
            ∘ subst-id-cod (++-assoc xs ys zs)
  rhs→N xs ys zs =
    -- phase 1: de-cast the outer cast into a conjugation by transported ids
    emb-cast-conj (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _
    -- phase 2: de-cast the inner factor (`stepC`), then merge the dom-side cast
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ stepC) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ (refl⟩∘⟨ cast-dc (++-assoc xs ys zs)))
    -- phase 3: reassociate the two σ-frames into one right-nested spine
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    -- phase 4: regroup the junction between the frames and discharge it by J
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym FM.assoc))
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (J xs ys zs ⟩∘⟨refl))
    -- phase 5: fold the left frame and tidy it to (T zs xs ∘ σ) ⊗ id
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (tidyL xs zs) ≈-Term-refl ⟩∘⟨refl))
    -- phase 6: fold the right frame and tidy it to id ⊗ (σ ∘ F ys zs)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         (⊗-resp-≈ ≈-Term-refl (tidyR ys zs) ⟩∘⟨refl))
    where
      stepC
        : emb (castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs))
          ≈Term subst-id-cod (sym (++-assoc xs zs ys))
                ∘ (T xs (zs ++ ys)
                    ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
      stepC = emb-cast-conj refl (sym (++-assoc xs zs ys)) _ ○ (refl⟩∘⟨ idʳ)

σ-hex-case
  : ∀ xs ys zs
  → emb (σˢ (xs ++ ys) zs)
    ≈Term emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                 ((σˢ xs zs ⊗ˢ idˢ {ys})
                   ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                        (idˢ {xs} ⊗ˢ σˢ ys zs)))
σ-hex-case xs ys zs = ≈-Term-trans (lhs→N xs ys zs) (≈-Term-sym (rhs→N xs ys zs))

--------------------------------------------------------------------------------
-- The `σ-unitˢ` case — unit braiding collapses to the right-unit cast.
-- `F [] xs = λ⇐` and `T [] xs = λ⇒` are DEFINITIONAL
-- (`unflatten-++-≅ [] = ≅.sym unitorˡ`), so the case is
-- `braiding-coherence-inv` + the `TR` induction from the `⊗-unitʳˢ` case.

open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal using (Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence-inv)

σ-unit-case : ∀ xs → emb (σˢ [] xs) ≈Term emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs}))
σ-unit-case xs = begin
  T xs [] ∘ σ ∘ λ⇐
    ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
  T xs [] ∘ ρ⇐
    ≈⟨ TR xs ⟩
  subst-id-cod (sym (++-identityʳ xs))
    ≈⟨ emb-cast-conj refl (sym (++-identityʳ xs)) _ ○ (refl⟩∘⟨ idˡ) ○ idʳ ⟨
  emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})) ∎

--------------------------------------------------------------------------------
-- `emb` respects `_≈ˢ_` — all sixteen cases closed: the cheap ones inline, the
-- four substantial ones by the standalone lemmas above.

module EmbRespFull where

  emb-resp-≈ˢ : ∀ {xs ys} {f g : HomS xs ys} → f ≈ˢ g → emb f ≈Term emb g
  emb-resp-≈ˢ ≈-refl           = ≈-Term-refl
  emb-resp-≈ˢ (≈-sym e)        = ≈-Term-sym (emb-resp-≈ˢ e)
  emb-resp-≈ˢ (≈-trans e e')   = ≈-Term-trans (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (∘-resp e e')    = ∘-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (⊗-resp e e')    = refl⟩∘⟨ (⊗-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e') ⟩∘⟨refl)
  emb-resp-≈ˢ idˡ              = idˡ
  emb-resp-≈ˢ idʳ              = idʳ
  emb-resp-≈ˢ assocˢ           = FM.assoc
  -- to ∘ (id ⊗ id) ∘ from  ≈  id
  emb-resp-≈ˢ (⊗-id {xs} {us}) =
    (refl⟩∘⟨ (id⊗id≈id ⟩∘⟨refl)) ○ (refl⟩∘⟨ idˡ)
    ○ _≅_.isoˡ (unflatten-++-≅ xs us)
  -- (T∘(a⊗b)∘F) ∘ (T∘(c⊗d)∘F)  ≈  T∘((a∘c)⊗(b∘d))∘F
  emb-resp-≈ˢ (interchangeˢ {xs} {ys} {zs} {us} {vs} {ws} {a} {b} {c} {d}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys vs))
    ○ (refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
  emb-resp-≈ˢ (⊗-assocˢ f g h) = ⊗-assoc-case f g h
  emb-resp-≈ˢ (⊗-unitʳˢ f)     = ⊗-unitʳ-case f
  -- (T∘σ∘F) ∘ (T∘(f⊗g)∘F)  ≈  (T∘(g⊗f)∘F) ∘ (T∘σ∘F)
  emb-resp-≈ˢ (σ-natˢ {xs} {ys} {us} {vs} {f} {g}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys vs))
    ○ (refl⟩∘⟨ (σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl))
    ○ ≈-Term-sym (cancel-mid-iso {M₂ = σ} (_≅_.isoʳ (unflatten-++-≅ us xs)))
  -- (T∘σ∘F) ∘ (T∘σ∘F)  ≈  id
  emb-resp-≈ˢ (σ-σˢ {xs} {ys}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys xs))
    ○ (refl⟩∘⟨ (σ∘σ≈id ⟩∘⟨refl))
    ○ (refl⟩∘⟨ idˡ)
    ○ _≅_.isoˡ (unflatten-++-≅ xs ys)
  emb-resp-≈ˢ (σ-hexˢ xs ys zs) = σ-hex-case xs ys zs
  emb-resp-≈ˢ (σ-unitˢ xs)      = σ-unit-case xs

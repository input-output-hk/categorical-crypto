{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → DiagU  with soundness, for the untyped free
-- monoidal diagram normal form of `Categories.Coherence.Monoidal.Diagram`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _), _⊗₁_,
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.
--
-- The combinator soundness lemmas are stated cast-free in `⟦_⟧`-form
-- (`∘ᵈ-sound`, `shiftL-sound`/`shiftR-sound`, `tensorD-sound`), and
-- `reflect-sound : ⟦ reflect t ⟧ ≈Term embed t` chains them.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Reflect where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize

module ReflectI {v : Variant} {X : Set} (E : WireEngine v {X})
                (_≟X_ : DecidableEquality X) where

  open WireEngine E
  open UntypedI E
  open FreeMonoidalHelper v X using (ObjTerm; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)
  open ≈R

  open MR FreeMonoidal
  open MonR Monoidal-FreeMonoidal
    using (_⟩⊗⟨_; serialize₂₁)

  open WireCohDec _≟X_ public using (merge-ρ; merge-assoc)
  open WireCohDec _≟X_        using (castW-irr)

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed terms
  --------------------------------------------------------------------------------
  infixr 9 _∘ʷ_
  infixr 10 _⊗ʷ_
  data WTerm : List X → List X → Set where
    boxʷ : ∀ {a b} → Mor a b → WTerm a b
    idʷ  : ∀ {n} → WTerm n n
    _∘ʷ_ : ∀ {n m k} → WTerm m k → WTerm n m → WTerm n k
    _⊗ʷ_ : ∀ {nl ml nr mr} → WTerm nl ml → WTerm nr mr → WTerm (nl ++ nr) (ml ++ mr)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦box⟧ g
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  embed (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) =
    merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr}

  private
    --------------------------------------------------------------------------------
    -- Combinator 1:  sequential composition / append of diagrams.
    --
    -- Recursion on the first-applied diagram d₁ : DiagU n m.  We cons each of
    -- its layers, then attach d₂ : DiagU m k at the empty tail.  The output
    -- index `k` is carried structurally, so the `[]_` clause returns `d₂` at
    -- the right type definitionally.
    --------------------------------------------------------------------------------
    infixr 9 _∘ᵈ_
    _∘ᵈ_ : ∀ {n m k} → DiagU n m → DiagU m k → DiagU n k
    ([]_ _)               ∘ᵈ d₂ = d₂
    (pre ▸ suf ∷ f ⟨ d ⟩) ∘ᵈ d₂ = pre ▸ suf ∷ f ⟨ d ∘ᵈ d₂ ⟩

    -- the pad-fusion bi-action laws and their conjugation combinators, opened
    -- privately here (rather than via the module-level public `WireCohDec` open)
    -- since they are only used by the private soundness proofs below.  The two
    -- pad staircases (`liftW-pad`/`rpad-pad`) are conjugation chains over these.
    open WireCohDec _≟X_
      using (split-ρ; conj-toSandwich; conj-trans; conj-irr;
             liftW-conj; liftW-fuse; rpad-liftW; rpad-rpad)

    ∘ᵈ-sound : ∀ {n m k} (d₁ : DiagU n m) (d₂ : DiagU m k)
             → ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
    ∘ᵈ-sound ([]_ _) d₂ = ⟺ idʳ
    ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = (∘ᵈ-sound d d₂ ⟩∘⟨refl) ○ assoc

    --------------------------------------------------------------------------------
    -- Combinator 2:  horizontal tensor of diagrams.
    --
    -- We build the tensor as  (left factor padded with `l` idle suffix wires)
    --                  ∘ᵈ    (right factor padded with `n` idle prefix wires),
    -- mirroring  Ef ⊗₁ Eg = (Ef ⊗₁ id) ∘ (id ⊗₁ Eg).  Each padding is a
    -- per-layer offset shift on the diagram.
    --------------------------------------------------------------------------------

    -- Prefix-shift: prepend `lt` idle wires to every layer (offset pre ↦ lt++pre).
    -- Definitionally  ⟦ shiftL lt d ⟧  is  liftW lt ⟦ d ⟧  up to the associativity
    -- reindexing absorbed by `substDiagU`; the output index is threaded as `lt ++ m`.
    shiftL : ∀ {n m} (lt : List X) → DiagU n m → DiagU (lt ++ n) (lt ++ m)
    shiftL lt ([]_ n) = []_ (lt ++ n)
    shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
      substDiagU (++-assoc lt pre (a ++ suf))
        ((lt ++ pre) ▸ suf ∷ f ⟨ substDiagU (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

    reassoc++ : ∀ (p a s r : List X) → (p ++ (a ++ s)) ++ r ≡ p ++ (a ++ (s ++ r))
    reassoc++ p a s r = trans (++-assoc p (a ++ s) r) (cong (p ++_) (++-assoc a s r))

    -- Suffix-shift: append `rt` idle wires (suffix suf ↦ suf++rt).
    shiftR : ∀ {n m} (rt : List X) → DiagU n m → DiagU (n ++ rt) (m ++ rt)
    shiftR rt ([]_ n) = []_ (n ++ rt)
    shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
      substDiagU (sym (reassoc++ pre a suf rt))
        (pre ▸ (suf ++ rt) ∷ f ⟨ substDiagU (reassoc++ pre b suf rt) (shiftR rt d) ⟩)

    --------------------------------------------------------------------------------
    -- Horizontal tensor of diagrams (the `_⊗₁_` combinator).
    --
    --   tensorD dl dr  places `dl`'s layers in the left wire-block (suffix-padded
    --   by the right input wires `nr` via `shiftR`) and `dr`'s layers in the
    --   right block (prefix-padded by the left OUTPUT wires `ml` via `shiftL`),
    --   composed sequentially.  The middle interface `ml ++ nr` matches
    --   DEFINITIONALLY, so no transport wrapper is needed.  Result lives over
    --   `nl ++ nr` with output `ml ++ mr`.
    --------------------------------------------------------------------------------
    tensorD : ∀ {nl ml nr mr} → DiagU nl ml → DiagU nr mr → DiagU (nl ++ nr) (ml ++ mr)
    tensorD {nl} {ml} {nr} {mr} dl dr = shiftR nr dl ∘ᵈ shiftL ml dr

    --------------------------------------------------------------------------------
    -- Reflection of the wire fragment into DiagU (M1).
    --
    --   id     →  empty diagram      [] _
    --   g ∘ f  →  reflect f ∘ᵈ reflect g   (f applied first)
    --   box g  →  single-box layer (see `boxD` below)
    --
    -- The single box `g : Mor a b` is placed with empty offsets; its layer has
    -- domain index  [] ++ (a ++ [])  =  a ++ []  and codomain  b ++ []  (note the
    -- trailing []s), so the leaf carries `++-identityʳ` reindices on BOTH
    -- endpoints.  The remaining right-unitor coherence is discharged by `boxSound`.
    --------------------------------------------------------------------------------

    -- single-box diagram; the trailing `[]` suffixes force the `++-identityʳ`
    -- reindices discharged by `boxSound`.
    boxD : ∀ {a b} → Mor a b → DiagU (a ++ []) (b ++ [])
    boxD {a} {b} g = [] ▸ [] ∷ g ⟨ []_ (b ++ []) ⟩

  --------------------------------------------------------------------------------
  -- reflect on the full wire fragment (id / ∘ / box / ⊗).  Both endpoints are
  -- carried as diagram indices, so the ∘ case feeds `reflect g : DiagU m k`
  -- into `reflect f : DiagU n m` with the shared index `m` matching
  -- definitionally — no `out`, no transport.  The box leaf transports both of
  -- its `++ []` endpoints (`substDiagU` on the input, `substDiagUᵒ` on the
  -- output).
  --------------------------------------------------------------------------------
  reflect : ∀ {n m} → WTerm n m → DiagU n m
  reflect idʷ              = []_ _
  reflect (g ∘ʷ f)         = reflect f ∘ᵈ reflect g
  reflect (boxʷ {a} {b} g) =
    substDiagU (++-identityʳ a) (substDiagUᵒ (++-identityʳ b) (boxD g))
  reflect (s ⊗ʷ t)         = tensorD (reflect s) (reflect t)

  private
    --------------------------------------------------------------------------------
    -- Box-leaf soundness (`boxSound`):  ⟦ boxD g ⟧, transported across the
    -- structural  a ++ [] ≡ a  and  b ++ [] ≡ b  reindices, equals ⟦box⟧ g.
    --
    --   ⟦ boxD g ⟧ = id ∘ (merge b {[]} ∘ (⟦box⟧ g ⊗₁ id) ∘ split a {[]})
    -- the empty-suffix merge/split reduce to ρ⇒ / ρ⇐ (by `merge-ρ` / `split-ρ`),
    -- and the conjugation  ρ⇒ ∘ (⟦box⟧ g ⊗₁ id) ∘ ρ⇐  collapses to ⟦box⟧ g by
    -- right-unitor naturality `ρ⇒∘f⊗id≈f∘ρ⇒` and `ρ⇒∘ρ⇐≈id`.
    --------------------------------------------------------------------------------

    boxSound : ∀ {a b} (g : Mor a b)
      → (castW (++-identityʳ b) ∘ ⟦ boxD g ⟧) ∘ castW (sym (++-identityʳ a)) ≈Term ⟦box⟧ g
    boxSound {a} {b} g = begin
      (castW (++-identityʳ b) ∘ ⟦ boxD g ⟧) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (refl⟩∘⟨ idˡ) ⟩∘⟨refl ⟩
      (castW (++-identityʳ b) ∘ merge b {[]} ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
      ((castW (++-identityʳ b) ∘ merge b {[]}) ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ assoc ⟩
      (castW (++-identityʳ b) ∘ merge b {[]}) ∘ (rest ∘ castW (sym (++-identityʳ a)))
        ≈⟨ (merge-ρ b) ⟩∘⟨ assoc ⟩
      ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ (split a {[]} ∘ castW (sym (++-identityʳ a))))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (split-ρ a)) ⟩
      ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ ρ⇐)
        ≈⟨ pullˡ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
      (⟦box⟧ g ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ cancelʳ ρ⇒∘ρ⇐≈id ⟩
      ⟦box⟧ g ∎
      where
        rest : HomTerm (wires (a ++ [])) (wires b ⊗₀ wires [])
        rest = (⟦box⟧ g ⊗₁ id {wires []}) ∘ split a {[]}

    --------------------------------------------------------------------------------
    -- Soundness of the offset shifts `shiftL` / `shiftR`.
    --
    --   The shifts are the diagram-level flat-shift operators, cast-free on
    --   their endpoints:
    --     shiftL-sound : ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
    --     shiftR-sound : ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
    --   where `rpad` is the suffix flat-shift; the per-layer `substDiagU`
    --   wrappers are peeled by `substDiagU-conj`.
    --------------------------------------------------------------------------------

    -- `liftW lt (pad pre suf g)` is the wider `pad (lt ++ pre) suf g`, up to the
    -- +-associativity reindex on its endpoints.  This is exactly the sandwich
    -- form of the prefix∘prefix law `liftW-fuse lt pre (rpad suf g)` (both pads
    -- ARE the `liftW … (rpad …)`s definitionally), rebracketed to the shiftL shape.
    liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
              → liftW lt (pad pre suf g)
                ≈Term (castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g)
                        ∘ castW (sym (++-assoc lt pre (a ++ suf)))
    liftW-pad lt pre suf g = conj-toSandwich (liftW-fuse lt pre (rpad suf g)) ○ ⟺ assoc

    -- The output index is now `lt ++ m` structurally, so the statement is
    -- cast-free; the two `substDiagU` wrappers are peeled by `substDiagU-conj`.
    shiftL-sound : ∀ {n m} (lt : List X) (d : DiagU n m)
                 → ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
    shiftL-sound lt ([]_ _) = ⟺ (liftW-id lt)
    shiftL-sound lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiagU E1 LAYER ⟧
        ≈⟨ substDiagU-conj E1 LAYER ⟩
      (⟦ subst2 ⟧ ∘ pf) ∘ castW (sym E1)
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((liftW lt ⟦ d ⟧ ∘ castW Eb) ∘ pf) ∘ castW (sym E1)
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      liftW lt ⟦ d ⟧ ∘ ((castW Eb ∘ pf) ∘ castW (sym E1))
        ≈⟨ refl⟩∘⟨ ⟺ (liftW-pad lt pre suf g) ⟩
      liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
        ≈⟨ ⟺ (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
      liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦box⟧ f
        Eb = ++-assoc lt pre (b ++ suf)
        E1 = ++-assoc lt pre (a ++ suf)
        E2 = sym Eb
        d' = shiftL lt d
        subst2 = substDiagU E2 d'
        pf = pad (lt ++ pre) suf g
        LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiagU` to `liftW lt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term liftW lt ⟦ d ⟧ ∘ castW Eb
        subst2≈ = substDiagU-conj E2 d' ○ (shiftL-sound lt d ⟩∘⟨ castW-irr (sym E2) Eb)

  --------------------------------------------------------------------------------
  -- The suffix flat-shift `rpad` / `pad` relation and its soundness for `shiftR`.
  -- The suffix-fusion primitives (`rpad-fuse`/`rpad-liftW`/`rpad-rpad`) live in
  -- `WireCoh.WireCohDec`, re-exported into scope above; `rpad-pad` below is a
  -- conjugation chain over them, mirroring `liftW-pad`.
  --------------------------------------------------------------------------------

  private
    -- rpad / pad relation (suffix analogue of `liftW-pad`): a conjugation chain
    -- over the bi-action laws, all at `R = rpad suf g`.  `rpad-liftW rt pre R`
    -- slides the outer `rpad rt` past the `pad pre suf g = liftW pre R` prefix;
    -- `liftW-conj pre (rpad-rpad suf rt g)` fuses the two suffix pads underneath;
    -- `conj-irr` bridges the composite cast indices to the `reassoc++` forms.
    rpad-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
               → rpad rt (pad pre suf g)
                 ≈Term (castW (sym (reassoc++ pre b suf rt)) ∘ pad pre (suf ++ rt) g)
                         ∘ castW (reassoc++ pre a suf rt)
    rpad-pad pre suf rt g =
      conj-toSandwich
        (conj-irr (conj-trans (rpad-liftW rt pre R) (liftW-conj pre (rpad-rpad suf rt g))))
        ○ ⟺ assoc
      where R = rpad suf g

    shiftR-sound : ∀ {n m} (rt : List X) (d : DiagU n m)
                 → ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
    shiftR-sound rt ([]_ _) = ⟺ (rpad-id rt)
    shiftR-sound rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiagU (sym E1) LAYER ⟧
        ≈⟨ substDiagU-conj (sym E1) LAYER ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW (sym (sym E1))
        ≈⟨ refl⟩∘⟨ castW-irr (sym (sym E1)) E1 ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW E1
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((rpad rt ⟦ d ⟧ ∘ castW (sym E2)) ∘ padR) ∘ castW E1
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      rpad rt ⟦ d ⟧ ∘ ((castW (sym E2) ∘ padR) ∘ castW E1)
        ≈⟨ refl⟩∘⟨ ⟺ (rpad-pad pre suf rt g) ⟩
      rpad rt ⟦ d ⟧ ∘ rpad rt (pad pre suf g)
        ≈⟨ ⟺ (rpad-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
      rpad rt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦box⟧ f
        E1 = reassoc++ pre a suf rt
        E2 = reassoc++ pre b suf rt
        d' = shiftR rt d
        subst2 = substDiagU E2 d'
        padR = pad pre (suf ++ rt) g
        LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiagU` to `rpad rt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term rpad rt ⟦ d ⟧ ∘ castW (sym E2)
        subst2≈ = substDiagU-conj E2 d' ○ (shiftR-sound rt d ⟩∘⟨refl)

    -- tensorD soundness: pure bifunctoriality (no σ), via the wire-grouping
    -- bridge between `wires nl ⊗₀ wires nr` and `wires (nl ++ nr)`.  With both
    -- endpoints indexed the middle interface `ml ++ nr` matches definitionally,
    -- so the statement is cast-free.
    tensorD-sound : ∀ {nl ml nr mr} (dl : DiagU nl ml) (dr : DiagU nr mr)
                  → ⟦ tensorD dl dr ⟧
                    ≈Term merge ml {mr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
    tensorD-sound {nl} {ml} {nr} {mr} dl dr = begin
      ⟦ shiftR nr dl ∘ᵈ shiftL ml dr ⟧
        ≈⟨ ∘ᵈ-sound (shiftR nr dl) (shiftL ml dr) ⟩
      ⟦ shiftL ml dr ⟧ ∘ ⟦ shiftR nr dl ⟧
        ≈⟨ shiftL-sound ml dr ⟩∘⟨ shiftR-sound nr dl ⟩
      liftW ml ⟦ dr ⟧ ∘ rpad nr ⟦ dl ⟧
        ≈⟨ liftW-merge ml ⟦ dr ⟧ ⟩∘⟨refl ⟩
      (merge ml {mr} ∘ (id {wires ml} ⊗₁ ⟦ dr ⟧) ∘ split ml {nr})
        ∘ (merge ml {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
        ≈⟨ collapse ⟩
      merge ml {mr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr} ∎
      where
        -- the central bifunctoriality collapse.
        collapse :
            (merge ml {mr} ∘ (id {wires ml} ⊗₁ ⟦ dr ⟧) ∘ split ml {nr})
              ∘ (merge ml {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
          ≈Term merge ml {mr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
        collapse = begin
          (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml) ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
            ≈⟨ center (cancelʳ (split∘merge ml)) ⟩
          merge ml ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))
            ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁) ⟩
          merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎

  --------------------------------------------------------------------------------
  -- THE REFLECTION SOUNDNESS THEOREM.
  --
  --   ⟦ reflect t ⟧  ≈Term  embed t
  --
  -- i.e. the reflected diagram equals the original wire-fragment morphism.
  -- Both endpoints are diagram indices, so the statement is cast-free; the box
  -- leaf's two `++ []` transports are peeled by `substDiagU-conj` / `⟦substDiagUᵒ⟧`.
  --------------------------------------------------------------------------------
  reflect-sound : ∀ {n m} (t : WTerm n m) → ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound idʷ = ≈-Term-refl
  reflect-sound (_∘ʷ_ {n} {m} {k} g f) =
    ∘ᵈ-sound (reflect f) (reflect g)
      ○ (reflect-sound g ⟩∘⟨ reflect-sound f)
  reflect-sound (boxʷ {a} {b} g) =
    substDiagU-conj eA leaf1
      ○ (⟺ (⟦substDiagUᵒ⟧ eB (boxD g)) ⟩∘⟨refl)
      ○ boxSound g
    where
      eA = ++-identityʳ a
      eB = ++-identityʳ b
      leaf1 = substDiagUᵒ eB (boxD g)
  reflect-sound (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) =
    tensorD-sound (reflect s) (reflect t)
      ○ (refl⟩∘⟨ ((reflect-sound s ⟩⊗⟨ reflect-sound t) ⟩∘⟨refl))

--------------------------------------------------------------------------------
-- Compatibility wrapper: `ReflectI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`).
--------------------------------------------------------------------------------
module Reflect (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
               (Mor : List X → List X → Set) where

  open Untyped v {X} Mor
  open ReflectI (record { Mor = Mor ; ⟦box⟧ = ⟦box⟧ }) _≟X_ public

--------------------------------------------------------------------------------
-- `DecideCore`: the shared wire-level DECISION ASSEMBLY.
--
-- Both front-ends' `decide?W`/`decideσ?` are byte-identical given a normalizer
-- `norm : ∀ {n m} (d : DiagU n m) → Σ[ d' ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)`: reflect both
-- sides to `DiagU`, normalize each, decide normal-form equality, and chain the
-- reflect-soundness witnesses through the bridge.  The interface stays SEMANTIC
-- (the syntactic `_≈D_` trace is discharged by `≈D-sound` inside each
-- front-end's `norm`).  `norm` is passed as an ordinary FUNCTION
-- argument so the per-variant oracle (interchange / σσ-cancel / slides) stays in
-- each front-end's scope while the assembly lives here once.
--------------------------------------------------------------------------------
module DecideCore
  {v : Variant} {X : Set} (E : WireEngine v {X})
  (_≟X_ : DecidableEquality X)
  where

  open WireEngine E
  open UntypedI E
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)
  open ≈R
  open ReflectI E _≟X_
  open NormalizeI E _≟X_
  open SortD
  open MR FreeMonoidal

  private
    module SCmp = SolverCompareI E _≟X_

  -- the caller supplies decidable equality on the Σ-packaged generators (used
  -- only to build `_≟DiagU_`) and a normalizer.
  module Decide
    (_≟Mor_ : DecidableEquality SCmp.Gen)
    (norm : ∀ {n m} (d : DiagU n m) → Σ[ d' ∈ DiagU n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧))
    where

    open SCmp.Decide _≟Mor_

    -- reflect both sides, normalize each, decide normal-form equality; on a hit
    -- the two normal forms are equal (`≈NF⇒≡`), so the reflect-soundness and
    -- the normalizer's `≈Term` witnesses chain directly (no output casts).
    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW {n} {m} f g with norm (reflect f) | norm (reflect g)
    ... | (df' , sndf) | (dg' , sndg) = case df' ≟DiagU dg' of λ where
        (no  _)  → nothing
        (yes eq) → just (chain (≈NF⇒≡ eq))
      where
        chain : df' ≡ dg' → embed f ≈Term embed g
        chain refl = ⟺ (reflect-sound f) ○ sndf ○ ⟺ sndg ○ reflect-sound g

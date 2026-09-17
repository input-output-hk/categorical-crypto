{-# OPTIONS --safe #-}

-- Machine isomorphism: equality of machines up to a stepRel-preserving
-- bijection of states.  This module proves that it is an equivalence and a
-- congruence for the machine builders, and the associativity bisimulation;
-- the identity laws and the `Category` record are in `Machine.Category`.

module CategoricalCrypto.Machine.Iso where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Relation.Binary using (IsEquivalence)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

private variable A B C D E : Channel

infix 4 _≅ᴹ_

record _≅ᴹ_ (M M' : Machine A B) : Type where
  constructor MkIso
  open Machine M  renaming (State to S;  stepRel to R)
  open Machine M' renaming (State to S'; stepRel to R')
  field
    to        : S → S'
    from      : S' → S
    from∘to   : ∀ s → from (to s) ≡ s
    to∘from   : ∀ s' → to (from s') ≡ s'
    step-to   : ∀ {s₁ i o s₂} → R s₁ i o s₂ → R' (to s₁) i o (to s₂)
    step-from : ∀ {s₁' i o s₂'} → R' s₁' i o s₂' → R (from s₁') i o (from s₂')

open _≅ᴹ_

≅ᴹ-refl : {M : Machine A B} → M ≅ᴹ M
≅ᴹ-refl = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) (λ p → p) (λ p → p)

≅ᴹ-sym : {M M' : Machine A B} → M ≅ᴹ M' → M' ≅ᴹ M
≅ᴹ-sym φ = MkIso (from φ) (to φ) (to∘from φ) (from∘to φ) (step-from φ) (step-to φ)

≅ᴹ-trans : {M₁ M₂ M₃ : Machine A B} → M₁ ≅ᴹ M₂ → M₂ ≅ᴹ M₃ → M₁ ≅ᴹ M₃
≅ᴹ-trans φ ψ = MkIso
  (λ s → to ψ (to φ s))
  (λ s → from φ (from ψ s))
  (λ s → trans (cong (from φ) (from∘to ψ (to φ s))) (from∘to φ s))
  (λ s → trans (cong (to ψ) (to∘from φ (from ψ s))) (to∘from ψ s))
  (λ p → step-to ψ (step-to φ p))
  (λ p → step-from φ (step-from ψ p))

≅ᴹ-isEquivalence : IsEquivalence (_≅ᴹ_ {A} {B})
≅ᴹ-isEquivalence = record { refl = ≅ᴹ-refl ; sym = ≅ᴹ-sym ; trans = ≅ᴹ-trans }

------------------------------------------------------------------------
-- Congruence: machine composition respects isomorphism.
--
-- An iso of components lifts through the tensor (`CompRel`), the
-- channel reshapes (`modifyStepRel` — definitionally transparent), and
-- the trace (`TraceRel`, by structural recursion). The messages are
-- untouched; only the states map.

private
  ×-map : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
        → (A → C) → (B → D) → A × B → C × D
  ×-map f g (a , b) = f a , g b

  -- Lift a step correspondence through `TraceRel`.
  TraceRel-map :
    ∀ {A B C} (M N : Machine (A ⊗₀ C) (B ⊗₀ C))
      (φ : Machine.State M → Machine.State N)
    → (∀ {s i mo s'} → Machine.stepRel M s i mo s'
                     → Machine.stepRel N (φ s) i mo (φ s'))
    → ∀ {s i mo s'} → TraceRel M s i mo s'
                    → TraceRel N (φ s) i mo (φ s')
  TraceRel-map M N φ h Trace[ p ]      = Trace[ h p ]
  TraceRel-map M N φ h (p Trace∷ₒ tr₀) = h p Trace∷ₒ TraceRel-map M N φ h tr₀
  TraceRel-map M N φ h (p Trace∷ᵢ tr₀) = h p Trace∷ᵢ TraceRel-map M N φ h tr₀

  -- Lift component isos through the tensor's `CompRel`.
  CompRel-map :
    ∀ {A B C D} {M₁ M₁' : Machine A B} {M₂ M₂' : Machine C D}
      (φ₁ : M₁ ≅ᴹ M₁') (φ₂ : M₂ ≅ᴹ M₂')
    → ∀ {s i mo s'} → Tensor.CompRel M₁ M₂ s i mo s'
    → Tensor.CompRel M₁' M₂'
        (×-map (to φ₁) (to φ₂) s) i mo
        (×-map (to φ₁) (to φ₂) s')
  CompRel-map φ₁ φ₂ (Tensor.Step₁ p) = Tensor.Step₁ (step-to φ₁ p)
  CompRel-map φ₁ φ₂ (Tensor.Step₂ p) = Tensor.Step₂ (step-to φ₂ p)

∘-resp-≅ᴹ : {M₁ M₁' : Machine B C} {M₂ M₂' : Machine A B}
          → M₁ ≅ᴹ M₁' → M₂ ≅ᴹ M₂'
          → (M₁ ∘ M₂) ≅ᴹ (M₁' ∘ M₂')
∘-resp-≅ᴹ {M₁ = M₁} {M₁'} {M₂} {M₂'} φ₁ φ₂ = MkIso
  (×-map (to φ₂) (to φ₁))
  (×-map (from φ₂) (from φ₁))
  (λ (s₂ , s₁) → cong₂ _,_ (from∘to φ₂ s₂) (from∘to φ₁ s₁))
  (λ (s₂ , s₁) → cong₂ _,_ (to∘from φ₂ s₂) (to∘from φ₁ s₁))
  (TraceRel-map _ _ _ (CompRel-map φ₂ φ₁))
  (TraceRel-map _ _ _ (CompRel-map (≅ᴹ-sym φ₂) (≅ᴹ-sym φ₁)))



private
  -- Tiny injectivity / conflict helpers (stated over transparent types;
  -- applied to opaque-typed equations via conversion inside the
  -- unfolding blocks).
  inj₁-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
           → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl

  inj₂-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
           → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-inj refl = refl

  inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ ()

  just-inj : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  just≢nothing : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
               → just x ≡ nothing → W
  just≢nothing ()

  nothing≢just : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
               → nothing ≡ just x → W
  nothing≢just ()

private
  -- General-index inversion views: splitting on `TraceRel`/`CompRel`
  -- with fully general indices always succeeds; the resulting
  -- propositional equations are then discharged by conversion inside
  -- `opaque unfolding` blocks (the case-split unifier itself does not
  -- see the unfolding).
  trace-view :
    ∀ {A B C} {M : Machine (A ⊗₀ C) (B ⊗₀ C)} {s i w s'}
    → TraceRel M s i w s'
    → (Machine.stepRel M s i w s')
    ⊎ (∃ λ s₁ → ∃ λ outC →
         Machine.stepRel M s i (just ((L⊗ ϵ) ⊗R ↑ₒ outC)) s₁
         × TraceRel M s₁ ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ᵢ outC) w s')
    ⊎ (∃ λ s₁ → ∃ λ inC →
         Machine.stepRel M s i (just ((L⊗ (L⊗ ϵ ᵗ¹) ᵗ¹) ↑ₒ inC)) s₁
         × TraceRel M s₁ (((L⊗ ϵ) ⊗R) ↑ᵢ inC) w s')
  trace-view Trace[ p ]      = inj₁ p
  trace-view (p Trace∷ₒ tr₀) = inj₂ (inj₁ (_ , _ , p , tr₀))
  trace-view (p Trace∷ᵢ tr₀) = inj₂ (inj₂ (_ , _ , p , tr₀))

  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp'
    → (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

------------------------------------------------------------------------
-- Environment equivalence: two machines are `_≅ℰ_`-related when they
-- are bisimilar (`_≅ᴹ_`) under every environment. This is the
-- semantic equality of the machine category, coarser than propositional
-- equality of `map-ℰ`, which distinguishes state representations, but
-- still sound for all UC notions defined by quantifying over environments.

_≅ℰ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
_≅ℰ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≅ᴹ map-ℰ M' E

≅ℰ-refl : {M : Machine A B} → M ≅ℰ M
≅ℰ-refl E = ≅ᴹ-refl

≅ℰ-sym : {M M' : Machine A B} → M ≅ℰ M' → M' ≅ℰ M
≅ℰ-sym p E = ≅ᴹ-sym (p E)

≅ℰ-trans : {M₁ M₂ M₃ : Machine A B} → M₁ ≅ℰ M₂ → M₂ ≅ℰ M₃ → M₁ ≅ℰ M₃
≅ℰ-trans p q E = ≅ᴹ-trans (p E) (q E)

≅ℰ-isEquivalence : IsEquivalence (_≅ℰ_ {A} {B})
≅ℰ-isEquivalence = record { refl = ≅ℰ-refl ; sym = ≅ℰ-sym ; trans = ≅ℰ-trans }

-- Machine isomorphism is finer than environment equivalence.
≅ᴹ⇒≅ℰ : {M M' : Machine A B} → M ≅ᴹ M' → M ≅ℰ M'
≅ᴹ⇒≅ℰ φ E = ∘-resp-≅ᴹ ≅ᴹ-refl φ

------------------------------------------------------------------------
-- Associativity: (h ∘ g) ∘ f ≅ᴹ h ∘ (g ∘ f), via a common flattened
-- normal form. Both bracketings are isomorphic to the TriTrace machine
-- below, which interleaves the three component machines explicitly
-- (B-messages bounce between f and g, C-messages between g and h).

open import Tactic.Defaults

-- Generic three-machine interleaving ("TriTrace"): the common
-- flattened normal form of both bracketings.
module TriStep
  {Sf Sg Sh : Type}
  {IA OA IB OB IC OC ID OD : Type}
  (Rf : Sf → IA ⊎ OB → Maybe (OA ⊎ IB) → Sf → Type)
  (Rg : Sg → IB ⊎ OC → Maybe (OB ⊎ IC) → Sg → Type)
  (Rh : Sh → IC ⊎ OD → Maybe (OC ⊎ ID) → Sh → Type)
  where

  TriState : Type
  TriState = Sf × Sg × Sh

  ExtOut : Type
  ExtOut = Maybe (OA ⊎ ID)

  data TriF : TriState → IA ⊎ OB → ExtOut → TriState → Type
  data TriG : TriState → IB ⊎ OC → ExtOut → TriState → Type
  data TriH : TriState → IC ⊎ OD → ExtOut → TriState → Type

  data TriF where
    F-out  : ∀ {sf sg sh sf' i oa} → Rf sf i (just (inj₁ oa)) sf'
           → TriF (sf , sg , sh) i (just (inj₁ oa)) (sf' , sg , sh)
    F-stop : ∀ {sf sg sh sf' i} → Rf sf i nothing sf'
           → TriF (sf , sg , sh) i nothing (sf' , sg , sh)
    F-pass : ∀ {sf sg sh sf' st' i ib mo} → Rf sf i (just (inj₂ ib)) sf'
           → TriG (sf' , sg , sh) (inj₁ ib) mo st'
           → TriF (sf , sg , sh) i mo st'

  data TriG where
    G-stop  : ∀ {sf sg sh sg' i} → Rg sg i nothing sg'
            → TriG (sf , sg , sh) i nothing (sf , sg' , sh)
    G-passF : ∀ {sf sg sh sg' st' i ob mo} → Rg sg i (just (inj₁ ob)) sg'
            → TriF (sf , sg' , sh) (inj₂ ob) mo st'
            → TriG (sf , sg , sh) i mo st'
    G-passH : ∀ {sf sg sh sg' st' i ic mo} → Rg sg i (just (inj₂ ic)) sg'
            → TriH (sf , sg' , sh) (inj₁ ic) mo st'
            → TriG (sf , sg , sh) i mo st'

  data TriH where
    H-out   : ∀ {sf sg sh sh' i d} → Rh sh i (just (inj₂ d)) sh'
            → TriH (sf , sg , sh) i (just (inj₂ d)) (sf , sg , sh')
    H-stop  : ∀ {sf sg sh sh' i} → Rh sh i nothing sh'
            → TriH (sf , sg , sh) i nothing (sf , sg , sh')
    H-passG : ∀ {sf sg sh sh' st' i oc mo} → Rh sh i (just (inj₁ oc)) sh'
            → TriG (sf , sg , sh') (inj₂ oc) mo st'
            → TriH (sf , sg , sh) i mo st'

  -- dispatchers: external channel, and the two inner-machine entries
  TriExt : TriState → IA ⊎ OD → ExtOut → TriState → Type
  TriExt st (inj₁ a)  mo st' = TriF st (inj₁ a)  mo st'
  TriExt st (inj₂ od) mo st' = TriH st (inj₂ od) mo st'

  TriBD : TriState → IB ⊎ OD → ExtOut → TriState → Type
  TriBD st (inj₁ ib) mo st' = TriG st (inj₁ ib) mo st'
  TriBD st (inj₂ od) mo st' = TriH st (inj₂ od) mo st'

  TriAC : TriState → IA ⊎ OC → ExtOut → TriState → Type
  TriAC st (inj₁ a)  mo st' = TriF st (inj₁ a)  mo st'
  TriAC st (inj₂ oc) mo st' = TriG st (inj₂ oc) mo st'

  -- continuation/exit types for the two inner-composite inversions
  ContL : Sf → Sg × Sh → Maybe (OB ⊎ ID) → ExtOut → TriState → Type
  ContL sf s₂ nothing          mo st' = (mo ≡ nothing) × (st' ≡ (sf , s₂))
  ContL sf s₂ (just (inj₂ d))  mo st' = (mo ≡ just (inj₂ d)) × (st' ≡ (sf , s₂))
  ContL sf s₂ (just (inj₁ ob)) mo st' = TriF (sf , s₂) (inj₂ ob) mo st'

  ContR : Sf × Sg → Sh → Maybe (OA ⊎ IC) → ExtOut → TriState → Type
  ContR s₁ sh nothing          mo st' = (mo ≡ nothing) × (st' ≡ (proj₁ s₁ , proj₂ s₁ , sh))
  ContR s₁ sh (just (inj₁ oa)) mo st' = (mo ≡ just (inj₁ oa)) × (st' ≡ (proj₁ s₁ , proj₂ s₁ , sh))
  ContR s₁ sh (just (inj₂ ic)) mo st' = TriH (proj₁ s₁ , proj₂ s₁ , sh) (inj₁ ic) mo st'

  -- termination-shape validation: same mutual call graph as the
  -- embedding directions (emb*) of the assoc proof
  sizeF : ∀ {st i mo st'} → TriF st i mo st' → ℕ
  sizeG : ∀ {st i mo st'} → TriG st i mo st' → ℕ
  sizeH : ∀ {st i mo st'} → TriH st i mo st' → ℕ
  sizeF (F-out _)      = 0
  sizeF (F-stop _)     = 0
  sizeF (F-pass _ k)   = suc (sizeG k)
  sizeG (G-stop _)     = 0
  sizeG (G-passF _ k)  = suc (sizeF k)
  sizeG (G-passH _ k)  = suc (sizeH k)
  sizeH (H-out _)      = 0
  sizeH (H-stop _)     = 0
  sizeH (H-passG _ k)  = suc (sizeG k)

module ∘-assoc-implementation
  {A B C D : Channel} (f : Machine A B) (g : Machine B C) (h : Machine C D) where

  private
    Sf = Machine.State f
    Sg = Machine.State g
    Sh = Machine.State h

    -- bridged step relations: transparent statements of the components'
    -- step relations over the *unfolded* message sums
    Rf♭ : Sf → Channel.inType A ⊎ Channel.outType B
        → Maybe (Channel.outType A ⊎ Channel.inType B) → Sf → Type
    Rf♭ s i mo s' = Machine.stepRel f s (construct-⊗ {m = In} i)
                      ((λ o → construct-⊗ {m = Out} o) <$> mo) s'

    Rg♭ : Sg → Channel.inType B ⊎ Channel.outType C
        → Maybe (Channel.outType B ⊎ Channel.inType C) → Sg → Type
    Rg♭ s i mo s' = Machine.stepRel g s (construct-⊗ {m = In} i)
                      ((λ o → construct-⊗ {m = Out} o) <$> mo) s'

    Rh♭ : Sh → Channel.inType C ⊎ Channel.outType D
        → Maybe (Channel.outType C ⊎ Channel.inType D) → Sh → Type
    Rh♭ s i mo s' = Machine.stepRel h s (construct-⊗ {m = In} i)
                      ((λ o → construct-⊗ {m = Out} o) <$> mo) s'

    module T = TriStep Rf♭ Rg♭ Rh♭

    cmpL : Machine A D
    cmpL = _∘_ {B = B} (_∘_ {B = C} h g) f

    cmpR : Machine A D
    cmpR = _∘_ {B = C} h (_∘_ {B = B} g f)

    -- the two inner composites' tensor cores (fresh ⇒-solver: probe
    -- fact 4 says these are definitionally the baked-in ones)
    itensL : Machine (B ⊗₀ C) (D ⊗₀ C)
    itensL = modifyStepRel ⇒-solver (g ⊗₁ h)

    itensR : Machine (A ⊗₀ B) (C ⊗₀ B)
    itensR = modifyStepRel ⇒-solver (f ⊗₁ g)

  -- state layout checks (must be transparent refl)
  _ : Machine.State cmpL ≡ T.TriState
  _ = refl

  _ : Machine.State cmpR ≡ ((Sf × Sg) × Sh)
  _ = refl

  reasc : (Sf × Sg) × Sh → T.TriState
  reasc ((sf , sg) , sh) = sf , sg , sh

  reasc⁻ : T.TriState → (Sf × Sg) × Sh
  reasc⁻ (sf , sg , sh) = (sf , sg) , sh

  _ : ∀ (s : (Sf × Sg) × Sh) → reasc⁻ (reasc s) ≡ s
  _ = λ _ → refl

  _ : ∀ (s : T.TriState) → reasc (reasc⁻ s) ≡ s
  _ = λ _ → refl

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine

    -- the flattened machine's step relation
    TriRel : MachineType A D T.TriState
    TriRel st i mo st' = T.TriExt st i mo st'

  -- the flattened machine itself (transparent: TriRel's stated type
  -- is exact)
  TriM : Machine A D
  TriM = MkMachine TriRel

  -- statements of the six work-package lemmas, elaborated as types
  -- (validates that all signatures are statable at top level)
  InvInnerL-Stmt : Type
  InvInnerL-Stmt = ∀ {sf sg sh sg' sh' mo st'}
      (i₂ : Channel.inType B ⊎ Channel.outType D)
      (m₂ : Maybe (Channel.outType B ⊎ Channel.inType D))
    → Machine.stepRel (_∘_ {B = C} h g) (sg , sh)
        (construct-⊗ {m = In} i₂) ((λ o → construct-⊗ {m = Out} o) <$> m₂) (sg' , sh')
    → T.ContL sf (sg' , sh') m₂ mo st'
    → T.TriBD (sf , sg , sh) i₂ mo st'

  InvInnerR-Stmt : Type
  InvInnerR-Stmt = ∀ {sf sg sf' sg' sh mo st'}
      (i₁ : Channel.inType A ⊎ Channel.outType C)
      (m₁ : Maybe (Channel.outType A ⊎ Channel.inType C))
    → Machine.stepRel (_∘_ {B = B} g f) (sf , sg)
        (construct-⊗ {m = In} i₁) ((λ o → construct-⊗ {m = Out} o) <$> m₁) (sf' , sg')
    → T.ContR (sf' , sg') sh m₁ mo st'
    → T.TriAC (sf , sg , sh) i₁ mo st'

  L-fwd-Stmt : Type
  L-fwd-Stmt = ∀ {sp sp' i mo}
    → Machine.stepRel cmpL sp i mo sp' → TriRel sp i mo sp'

  L-bwd-Stmt : Type
  L-bwd-Stmt = ∀ {sp sp' i mo}
    → TriRel sp i mo sp' → Machine.stepRel cmpL sp i mo sp'

  R-fwd-Stmt : Type
  R-fwd-Stmt = ∀ {sp sp' i mo}
    → Machine.stepRel cmpR sp i mo sp' → TriRel (reasc sp) i mo (reasc sp')

  R-bwd-Stmt : Type
  R-bwd-Stmt = ∀ {sp sp' i mo}
    → TriRel (reasc sp) i mo (reasc sp') → Machine.stepRel cmpR sp i mo sp'

  -- final assembly, given the four cores (validates state maps,
  -- refl roundtrips, MkIso wiring, ≅ᴹ-trans composition)
  assemble : L-fwd-Stmt → L-bwd-Stmt → R-fwd-Stmt → R-bwd-Stmt
           → cmpL ≅ᴹ cmpR
  assemble lf lb rf rb = ≅ᴹ-trans isoL (≅ᴹ-sym isoR)
    where
    isoL : cmpL ≅ᴹ TriM
    isoL = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) lf lb
    isoR : cmpR ≅ᴹ TriM
    isoR = MkIso reasc reasc⁻ (λ _ → refl) (λ _ → refl) rf rb

  ------------------------------------------------------------------
  -- L-bwd: every TriTrace chain embeds into the LEFT bracketing
  -- (h ∘ g) ∘ f. The mutual embeddings embF/embG/embH follow the
  -- structure of the TriF/TriG/TriH chain; the parts of a chain that
  -- live inside the inner (h ∘ g) composite are collected in `GResL`
  -- (terminal without output, terminal with external D output, or an
  -- exit towards f on the middle B together with an outer
  -- continuation).

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine TriRel

    L-bwd : L-bwd-Stmt
    L-bwd {sp} {sp'} {i} {mo} t = go i mo t
      where
      -- the outer tensor core of cmpL (definitionally the baked-in one)
      tens : Machine (A ⊗₀ B) (D ⊗₀ B)
      tens = modifyStepRel ⇒-solver (f ⊗₁ (_∘_ {B = C} h g))

      -- external output map at the outer trace level
      extO : Maybe (Channel.outType A ⊎ Channel.inType D)
           → Maybe ((Channel.outType A ⊎ Channel.outType B)
                    ⊎ (Channel.inType D ⊎ Channel.inType B))
      extO nothing          = nothing
      extO (just (inj₁ oa)) = just (inj₁ (inj₁ oa))
      extO (just (inj₂ d))  = just (inj₂ (inj₁ d))

      -- entry maps: component-level inputs to trace-level indices
      entF : Channel.inType A ⊎ Channel.outType B
           → (Channel.inType A ⊎ Channel.inType B)
             ⊎ (Channel.outType D ⊎ Channel.outType B)
      entF (inj₁ a)  = inj₁ (inj₁ a)
      entF (inj₂ ob) = inj₂ (inj₂ ob)

      entG : Channel.inType B ⊎ Channel.outType C
           → (Channel.inType B ⊎ Channel.inType C)
             ⊎ (Channel.outType D ⊎ Channel.outType C)
      entG (inj₁ ib) = inj₁ (inj₁ ib)
      entG (inj₂ oc) = inj₂ (inj₂ oc)

      entH : Channel.inType C ⊎ Channel.outType D
           → (Channel.inType B ⊎ Channel.inType C)
             ⊎ (Channel.outType D ⊎ Channel.outType C)
      entH (inj₁ ic) = inj₁ (inj₂ ic)
      entH (inj₂ od) = inj₂ (inj₁ od)

      -- result package for the sides that live inside the inner (h ∘ g)
      -- chain
      GResL : Sf → (s₂ : Sg × Sh)
            → ((Channel.inType B ⊎ Channel.inType C)
               ⊎ (Channel.outType D ⊎ Channel.outType C))
            → Maybe (Channel.outType A ⊎ Channel.inType D)
            → T.TriState → Type
      GResL sf s₂ x mo₀ st' =
          (∃ λ s₂' → (mo₀ ≡ nothing) × (st' ≡ (sf , s₂'))
                   × TraceRel itensL s₂ x nothing s₂')
        ⊎ (∃ λ s₂' → ∃ λ d → (mo₀ ≡ just (inj₂ d)) × (st' ≡ (sf , s₂'))
                   × TraceRel itensL s₂ x (just (inj₂ (inj₁ d))) s₂')
        ⊎ (∃ λ s₂' → ∃ λ ob → TraceRel itensL s₂ x (just (inj₁ (inj₁ ob))) s₂'
                   × TraceRel tens (sf , s₂') (inj₂ (inj₂ ob)) (extO mo₀) st')

      embF : ∀ {sf s₂ st' mo₀} (iF : Channel.inType A ⊎ Channel.outType B)
           → T.TriF (sf , s₂) iF mo₀ st'
           → TraceRel tens (sf , s₂) (entF iF) (extO mo₀) st'
      embG : ∀ {sf sg sh st' mo₀} (iG : Channel.inType B ⊎ Channel.outType C)
           → T.TriG (sf , sg , sh) iG mo₀ st'
           → GResL sf (sg , sh) (entG iG) mo₀ st'
      embH : ∀ {sf sg sh st' mo₀} (iH : Channel.inType C ⊎ Channel.outType D)
           → T.TriH (sf , sg , sh) iH mo₀ st'
           → GResL sf (sg , sh) (entH iH) mo₀ st'

      embF (inj₁ a)  (T.F-out p)  = Trace[ Tensor.Step₁ p ]
      embF (inj₂ ob) (T.F-out p)  = Trace[ Tensor.Step₁ p ]
      embF (inj₁ a)  (T.F-stop p) = Trace[ Tensor.Step₁ p ]
      embF (inj₂ ob) (T.F-stop p) = Trace[ Tensor.Step₁ p ]
      embF (inj₁ a) (T.F-pass {ib = ib} p k) with embG (inj₁ ib) k
      embF (inj₁ a) (T.F-pass {ib = ib} p k)
        | inj₁ (s₂' , refl , refl , itr) =
        Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ {m' = nothing} itr ]
      embF (inj₁ a) (T.F-pass {ib = ib} p k)
        | inj₂ (inj₁ (s₂' , d , refl , refl , itr)) =
        Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ itr ]
      embF (inj₁ a) (T.F-pass {ib = ib} p k)
        | inj₂ (inj₂ (s₂' , ob' , itr , cont)) =
        Tensor.Step₁ p Trace∷ᵢ (Tensor.Step₂ itr Trace∷ₒ cont)
      embF (inj₂ ob) (T.F-pass {ib = ib} p k) with embG (inj₁ ib) k
      embF (inj₂ ob) (T.F-pass {ib = ib} p k)
        | inj₁ (s₂' , refl , refl , itr) =
        Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ {m' = nothing} itr ]
      embF (inj₂ ob) (T.F-pass {ib = ib} p k)
        | inj₂ (inj₁ (s₂' , d , refl , refl , itr)) =
        Tensor.Step₁ p Trace∷ᵢ Trace[ Tensor.Step₂ itr ]
      embF (inj₂ ob) (T.F-pass {ib = ib} p k)
        | inj₂ (inj₂ (s₂' , ob' , itr , cont)) =
        Tensor.Step₁ p Trace∷ᵢ (Tensor.Step₂ itr Trace∷ₒ cont)

      embG (inj₁ ib) (T.G-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₁ q ])
      embG (inj₂ oc) (T.G-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₁ q ])
      embG (inj₁ ib) (T.G-passF {ob = ob} q k) =
        inj₂ (inj₂ (_ , ob , Trace[ Tensor.Step₁ q ] , embF (inj₂ ob) k))
      embG (inj₂ oc) (T.G-passF {ob = ob} q k) =
        inj₂ (inj₂ (_ , ob , Trace[ Tensor.Step₁ q ] , embF (inj₂ ob) k))
      embG (inj₁ ib) (T.G-passH {ic = ic} q k) with embH (inj₁ ic) k
      embG (inj₁ ib) (T.G-passH {ic = ic} q k)
        | inj₁ (s₂' , e₁ , e₂ , itr) =
        inj₁ (s₂' , e₁ , e₂ , (Tensor.Step₁ q Trace∷ᵢ itr))
      embG (inj₁ ib) (T.G-passH {ic = ic} q k)
        | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        inj₂ (inj₁ (s₂' , d , e₁ , e₂ , (Tensor.Step₁ q Trace∷ᵢ itr)))
      embG (inj₁ ib) (T.G-passH {ic = ic} q k)
        | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        inj₂ (inj₂ (s₂' , ob , (Tensor.Step₁ q Trace∷ᵢ itr) , cont))
      embG (inj₂ oc) (T.G-passH {ic = ic} q k) with embH (inj₁ ic) k
      embG (inj₂ oc) (T.G-passH {ic = ic} q k)
        | inj₁ (s₂' , e₁ , e₂ , itr) =
        inj₁ (s₂' , e₁ , e₂ , (Tensor.Step₁ q Trace∷ᵢ itr))
      embG (inj₂ oc) (T.G-passH {ic = ic} q k)
        | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        inj₂ (inj₁ (s₂' , d , e₁ , e₂ , (Tensor.Step₁ q Trace∷ᵢ itr)))
      embG (inj₂ oc) (T.G-passH {ic = ic} q k)
        | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        inj₂ (inj₂ (s₂' , ob , (Tensor.Step₁ q Trace∷ᵢ itr) , cont))

      embH (inj₁ ic) (T.H-out q) =
        inj₂ (inj₁ (_ , _ , refl , refl , Trace[ Tensor.Step₂ q ]))
      embH (inj₂ od) (T.H-out q) =
        inj₂ (inj₁ (_ , _ , refl , refl , Trace[ Tensor.Step₂ q ]))
      embH (inj₁ ic) (T.H-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₂ q ])
      embH (inj₂ od) (T.H-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₂ q ])
      embH (inj₁ ic) (T.H-passG {oc = oc} q k) with embG (inj₂ oc) k
      embH (inj₁ ic) (T.H-passG {oc = oc} q k)
        | inj₁ (s₂' , e₁ , e₂ , itr) =
        inj₁ (s₂' , e₁ , e₂ , (Tensor.Step₂ q Trace∷ₒ itr))
      embH (inj₁ ic) (T.H-passG {oc = oc} q k)
        | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        inj₂ (inj₁ (s₂' , d , e₁ , e₂ , (Tensor.Step₂ q Trace∷ₒ itr)))
      embH (inj₁ ic) (T.H-passG {oc = oc} q k)
        | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        inj₂ (inj₂ (s₂' , ob , (Tensor.Step₂ q Trace∷ₒ itr) , cont))
      embH (inj₂ od) (T.H-passG {oc = oc} q k) with embG (inj₂ oc) k
      embH (inj₂ od) (T.H-passG {oc = oc} q k)
        | inj₁ (s₂' , e₁ , e₂ , itr) =
        inj₁ (s₂' , e₁ , e₂ , (Tensor.Step₂ q Trace∷ₒ itr))
      embH (inj₂ od) (T.H-passG {oc = oc} q k)
        | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        inj₂ (inj₁ (s₂' , d , e₁ , e₂ , (Tensor.Step₂ q Trace∷ₒ itr)))
      embH (inj₂ od) (T.H-passG {oc = oc} q k)
        | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        inj₂ (inj₂ (s₂' , ob , (Tensor.Step₂ q Trace∷ₒ itr) , cont))

      -- top-level dispatcher over the external (input, output) shapes:
      -- the A-side entry is a TriF chain embedded directly; the D-side
      -- entry is a TriH chain, whose inner part becomes the single
      -- leading Step₂ node of the outer trace.
      go : (i₀ : Channel.inType A ⊎ Channel.outType D)
           (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
         → T.TriExt sp i₀ mo₀ sp'
         → Machine.stepRel cmpL sp i₀ mo₀ sp'
      go (inj₁ a) (just (inj₁ oa)) t₀ = embF (inj₁ a) t₀
      go (inj₁ a) (just (inj₂ d))  t₀ = embF (inj₁ a) t₀
      go (inj₁ a) nothing          t₀ = embF (inj₁ a) t₀
      go (inj₂ od) (just (inj₁ oa)) t₀ with embH (inj₂ od) t₀
      go (inj₂ od) (just (inj₁ oa)) t₀ | inj₁ (s₂' , e₁ , e₂ , itr) =
        just≢nothing e₁
      go (inj₂ od) (just (inj₁ oa)) t₀ | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        inj₁≢inj₂ (just-inj e₁)
      go (inj₂ od) (just (inj₁ oa)) t₀ | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        Tensor.Step₂ itr Trace∷ₒ cont
      go (inj₂ od) (just (inj₂ d)) t₀ with embH (inj₂ od) t₀
      go (inj₂ od) (just (inj₂ d)) t₀ | inj₁ (s₂' , e₁ , e₂ , itr) =
        just≢nothing e₁
      go (inj₂ od) (just (inj₂ d)) t₀ | inj₂ (inj₁ (s₂' , d' , e₁ , e₂ , itr)) =
        subst₂ (λ v st → TraceRel tens sp (inj₂ (inj₁ od)) (just (inj₂ (inj₁ v))) st)
               (sym (inj₂-inj (just-inj e₁))) (sym e₂)
               Trace[ Tensor.Step₂ itr ]
      go (inj₂ od) (just (inj₂ d)) t₀ | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        Tensor.Step₂ itr Trace∷ₒ cont
      go (inj₂ od) nothing t₀ with embH (inj₂ od) t₀
      go (inj₂ od) nothing t₀ | inj₁ (s₂' , e₁ , e₂ , itr) =
        subst (λ st → TraceRel tens sp (inj₂ (inj₁ od)) nothing st) (sym e₂)
              Trace[ Tensor.Step₂ {m' = nothing} itr ]
      go (inj₂ od) nothing t₀ | inj₂ (inj₁ (s₂' , d , e₁ , e₂ , itr)) =
        nothing≢just e₁
      go (inj₂ od) nothing t₀ | inj₂ (inj₂ (s₂' , ob , itr , cont)) =
        Tensor.Step₂ itr Trace∷ₒ cont

  ------------------------------------------------------------------------
  -- R-bwd: embedding TriTrace chains into the RIGHT bracketing
  -- h ∘ (g ∘ f). The roles flip relative to the left bracketing:
  -- h-steps are bare outer Step₂ nodes, while f- and g-steps live
  -- inside inner (g ∘ f)-chains (TraceRel itensR, middle B) hung on
  -- outer Step₁ nodes. C-bounces are outer trace links, B-bounces
  -- inner ones.

  private
    -- the right bracketing's outer tensor core (fresh ⇒-solver:
    -- definitionally the one baked into cmpR)
    tensR : Machine (A ⊗₀ C) (D ⊗₀ C)
    tensR = modifyStepRel ⇒-solver ((_∘_ {B = B} g f) ⊗₁ h)

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine TriRel

    R-bwd : R-bwd-Stmt
    R-bwd {sp = (sf , sg) , sh} {sp' = (sf' , sg') , sh'} {i} {mo} t =
      go i mo t
      where
      -- index maps: external outputs and h-steps into the outer trace,
      -- f- and g-steps into the inner (g ∘ f) trace
      ⟪_⟫E : Maybe (Channel.outType A ⊎ Channel.inType D)
           → Maybe ((Channel.outType A ⊎ Channel.outType C)
                  ⊎ (Channel.inType D ⊎ Channel.inType C))
      ⟪ nothing ⟫E        = nothing
      ⟪ just (inj₁ oa) ⟫E = just (inj₁ (inj₁ oa))
      ⟪ just (inj₂ d)  ⟫E = just (inj₂ (inj₁ d))

      ⟪_⟫H : Channel.inType C ⊎ Channel.outType D
           → (Channel.inType A ⊎ Channel.inType C)
           ⊎ (Channel.outType D ⊎ Channel.outType C)
      ⟪ inj₁ ic ⟫H = inj₁ (inj₂ ic)
      ⟪ inj₂ od ⟫H = inj₂ (inj₁ od)

      ⟪_⟫F : Channel.inType A ⊎ Channel.outType B
           → (Channel.inType A ⊎ Channel.inType B)
           ⊎ (Channel.outType C ⊎ Channel.outType B)
      ⟪ inj₁ a  ⟫F = inj₁ (inj₁ a)
      ⟪ inj₂ ob ⟫F = inj₂ (inj₂ ob)

      ⟪_⟫G : Channel.inType B ⊎ Channel.outType C
           → (Channel.inType A ⊎ Channel.inType B)
           ⊎ (Channel.outType C ⊎ Channel.outType B)
      ⟪ inj₁ ib ⟫G = inj₁ (inj₂ ib)
      ⟪ inj₂ oc ⟫G = inj₂ (inj₁ oc)

      -- result package for the f/g sides: the inner (g ∘ f)-chain
      -- either terminates (silently, or with an external A-output)
      -- leaving the h-state untouched, or exits towards h with a
      -- middle-C message plus the corresponding outer continuation
      GResR : Sh → Sf × Sg
            → (Channel.inType A ⊎ Channel.inType B)
            ⊎ (Channel.outType C ⊎ Channel.outType B)
            → Maybe (Channel.outType A ⊎ Channel.inType D)
            → T.TriState → Type
      GResR sh₀ s₁ x mo₀ st' =
          (∃ λ s₁' → (mo₀ ≡ nothing)
                   × (st' ≡ (proj₁ s₁' , proj₂ s₁' , sh₀))
                   × TraceRel itensR s₁ x nothing s₁')
        ⊎ (∃ λ s₁' → ∃ λ oa
                   → (mo₀ ≡ just (inj₁ oa))
                   × (st' ≡ (proj₁ s₁' , proj₂ s₁' , sh₀))
                   × TraceRel itensR s₁ x (just (inj₁ (inj₁ oa))) s₁')
        ⊎ (∃ λ s₁' → ∃ λ ic
                   → TraceRel itensR s₁ x (just (inj₂ (inj₁ ic))) s₁'
                   × TraceRel tensR (s₁' , sh₀) (inj₁ (inj₂ ic)) ⟪ mo₀ ⟫E (reasc⁻ st'))

      embF : ∀ {sf sg sh₀ mo₀ st'} (i₀ : Channel.inType A ⊎ Channel.outType B)
           → T.TriF (sf , sg , sh₀) i₀ mo₀ st'
           → GResR sh₀ (sf , sg) ⟪ i₀ ⟫F mo₀ st'
      embG : ∀ {sf sg sh₀ mo₀ st'} (i₀ : Channel.inType B ⊎ Channel.outType C)
           → T.TriG (sf , sg , sh₀) i₀ mo₀ st'
           → GResR sh₀ (sf , sg) ⟪ i₀ ⟫G mo₀ st'
      embH : ∀ {sf sg sh₀ mo₀ st'} (i₀ : Channel.inType C ⊎ Channel.outType D)
           → T.TriH (sf , sg , sh₀) i₀ mo₀ st'
           → TraceRel tensR ((sf , sg) , sh₀) ⟪ i₀ ⟫H ⟪ mo₀ ⟫E (reasc⁻ st')

      -- f-steps: bare inner Step₁ nodes; an emitted middle-B message
      -- heads an inner ∷ᵢ link towards g
      embF (inj₁ a)  (T.F-out q)  =
        inj₂ (inj₁ (_ , _ , refl , refl , Trace[ Tensor.Step₁ q ]))
      embF (inj₂ ob) (T.F-out q)  =
        inj₂ (inj₁ (_ , _ , refl , refl , Trace[ Tensor.Step₁ q ]))
      embF (inj₁ a)  (T.F-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₁ q ])
      embF (inj₂ ob) (T.F-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₁ q ])
      embF (inj₁ a)  (T.F-pass {ib = ib} q k) with embG (inj₁ ib) k
      ... | inj₁ (s₁' , moeq , steq , itr) =
            inj₁ (s₁' , moeq , steq , (Tensor.Step₁ q Trace∷ᵢ itr))
      ... | inj₂ (inj₁ (s₁' , oa , moeq , steq , itr)) =
            inj₂ (inj₁ (s₁' , oa , moeq , steq , (Tensor.Step₁ q Trace∷ᵢ itr)))
      ... | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
            inj₂ (inj₂ (s₁' , ic , (Tensor.Step₁ q Trace∷ᵢ itr) , cont))
      embF (inj₂ ob) (T.F-pass {ib = ib} q k) with embG (inj₁ ib) k
      ... | inj₁ (s₁' , moeq , steq , itr) =
            inj₁ (s₁' , moeq , steq , (Tensor.Step₁ q Trace∷ᵢ itr))
      ... | inj₂ (inj₁ (s₁' , oa , moeq , steq , itr)) =
            inj₂ (inj₁ (s₁' , oa , moeq , steq , (Tensor.Step₁ q Trace∷ᵢ itr)))
      ... | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
            inj₂ (inj₂ (s₁' , ic , (Tensor.Step₁ q Trace∷ᵢ itr) , cont))

      -- g-steps: bare inner Step₂ nodes; towards f heads an inner ∷ₒ
      -- link, towards h exits the inner chain on the middle C channel
      embG (inj₁ ib) (T.G-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₂ q ])
      embG (inj₂ oc) (T.G-stop q) =
        inj₁ (_ , refl , refl , Trace[ Tensor.Step₂ q ])
      embG (inj₁ ib) (T.G-passF {ob = ob} q k) with embF (inj₂ ob) k
      ... | inj₁ (s₁' , moeq , steq , itr) =
            inj₁ (s₁' , moeq , steq , (Tensor.Step₂ q Trace∷ₒ itr))
      ... | inj₂ (inj₁ (s₁' , oa , moeq , steq , itr)) =
            inj₂ (inj₁ (s₁' , oa , moeq , steq , (Tensor.Step₂ q Trace∷ₒ itr)))
      ... | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
            inj₂ (inj₂ (s₁' , ic , (Tensor.Step₂ q Trace∷ₒ itr) , cont))
      embG (inj₂ oc) (T.G-passF {ob = ob} q k) with embF (inj₂ ob) k
      ... | inj₁ (s₁' , moeq , steq , itr) =
            inj₁ (s₁' , moeq , steq , (Tensor.Step₂ q Trace∷ₒ itr))
      ... | inj₂ (inj₁ (s₁' , oa , moeq , steq , itr)) =
            inj₂ (inj₁ (s₁' , oa , moeq , steq , (Tensor.Step₂ q Trace∷ₒ itr)))
      ... | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
            inj₂ (inj₂ (s₁' , ic , (Tensor.Step₂ q Trace∷ₒ itr) , cont))
      embG (inj₁ ib) (T.G-passH {ic = ic} q k) =
        inj₂ (inj₂ (_ , ic , Trace[ Tensor.Step₂ q ] , embH (inj₁ ic) k))
      embG (inj₂ oc) (T.G-passH {ic = ic} q k) =
        inj₂ (inj₂ (_ , ic , Trace[ Tensor.Step₂ q ] , embH (inj₁ ic) k))

      -- h-steps: bare outer Step₂ nodes; an emitted middle-C message
      -- heads an outer ∷ₒ link whose tail is the (g ∘ f)-chain from
      -- embG, hung on an outer Step₁ node
      embH (inj₁ ic) (T.H-out q)  = Trace[ Tensor.Step₂ q ]
      embH (inj₂ od) (T.H-out q)  = Trace[ Tensor.Step₂ q ]
      embH (inj₁ ic) (T.H-stop q) = Trace[ Tensor.Step₂ q ]
      embH (inj₂ od) (T.H-stop q) = Trace[ Tensor.Step₂ q ]
      embH (inj₁ ic) (T.H-passG {oc = oc} q k) with embG (inj₂ oc) k
      ... | inj₁ (s₁' , refl , refl , itr) =
            Tensor.Step₂ q Trace∷ₒ
            Trace[ Tensor.Step₁ {m = inj₂ oc} {m' = nothing} itr ]
      ... | inj₂ (inj₁ (s₁' , oa , refl , refl , itr)) =
            Tensor.Step₂ q Trace∷ₒ
            Trace[ Tensor.Step₁ {m = inj₂ oc} {m' = just (inj₁ oa)} itr ]
      ... | inj₂ (inj₂ (s₁' , ic' , itr , cont)) =
            Tensor.Step₂ q Trace∷ₒ
            (Tensor.Step₁ {m = inj₂ oc} {m' = just (inj₂ ic')} itr Trace∷ᵢ cont)
      embH (inj₂ od) (T.H-passG {oc = oc} q k) with embG (inj₂ oc) k
      ... | inj₁ (s₁' , refl , refl , itr) =
            Tensor.Step₂ q Trace∷ₒ
            Trace[ Tensor.Step₁ {m = inj₂ oc} {m' = nothing} itr ]
      ... | inj₂ (inj₁ (s₁' , oa , refl , refl , itr)) =
            Tensor.Step₂ q Trace∷ₒ
            Trace[ Tensor.Step₁ {m = inj₂ oc} {m' = just (inj₁ oa)} itr ]
      ... | inj₂ (inj₂ (s₁' , ic' , itr , cont)) =
            Tensor.Step₂ q Trace∷ₒ
            (Tensor.Step₁ {m = inj₂ oc} {m' = just (inj₂ ic')} itr Trace∷ᵢ cont)

      -- top dispatcher over the external input/output shapes
      go : ∀ {sf₀ sg₀ sh₀ st'}
           (i₀ : Channel.inType A ⊎ Channel.outType D)
           (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
         → T.TriExt (sf₀ , sg₀ , sh₀) i₀ mo₀ st'
         → Machine.stepRel cmpR ((sf₀ , sg₀) , sh₀) i₀ mo₀ (reasc⁻ st')
      go (inj₁ a) mo₀ t₀ with embF (inj₁ a) t₀
      go (inj₁ a) mo₀ t₀ | inj₁ (s₁' , refl , refl , itr) =
        Trace[ Tensor.Step₁ {m = inj₁ a} {m' = nothing} itr ]
      go (inj₁ a) mo₀ t₀ | inj₂ (inj₁ (s₁' , oa , refl , refl , itr)) =
        Trace[ Tensor.Step₁ {m = inj₁ a} {m' = just (inj₁ oa)} itr ]
      go (inj₁ a) nothing t₀ | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
        Tensor.Step₁ {m = inj₁ a} {m' = just (inj₂ ic)} itr Trace∷ᵢ cont
      go (inj₁ a) (just (inj₁ oa)) t₀ | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
        Tensor.Step₁ {m = inj₁ a} {m' = just (inj₂ ic)} itr Trace∷ᵢ cont
      go (inj₁ a) (just (inj₂ d)) t₀ | inj₂ (inj₂ (s₁' , ic , itr , cont)) =
        Tensor.Step₁ {m = inj₁ a} {m' = just (inj₂ ic)} itr Trace∷ᵢ cont
      go (inj₂ od) nothing          t₀ = embH (inj₂ od) t₀
      go (inj₂ od) (just (inj₁ oa)) t₀ = embH (inj₂ od) t₀
      go (inj₂ od) (just (inj₂ d))  t₀ = embH (inj₂ od) t₀

  ------------------------------------------------------------------------
  -- inv-innerL: inverting the inner (h ∘ g) composite of the LEFT
  -- bracketing. A bridged step of (h ∘ g) is a TraceRel chain over
  -- itensL; the mutual workers goG/goH walk that chain, rebuilding the
  -- TriG/TriH spine and closing with the outer continuation κ (a
  -- T.ContL value) when the chain terminates.

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine TriRel

    inv-innerL : InvInnerL-Stmt
    inv-innerL {sf} {sg} {sh} {sg'} {sh'} {mo} {st'} i₂ m₂ d κ = go i₂ m₂ d κ
      where
      -- entry maps: component-level inputs to itensL trace-level indices
      entG : Channel.inType B ⊎ Channel.outType C
           → (Channel.inType B ⊎ Channel.inType C)
             ⊎ (Channel.outType D ⊎ Channel.outType C)
      entG (inj₁ ib) = inj₁ (inj₁ ib)
      entG (inj₂ oc) = inj₂ (inj₂ oc)

      entH : Channel.inType C ⊎ Channel.outType D
           → (Channel.inType B ⊎ Channel.inType C)
             ⊎ (Channel.outType D ⊎ Channel.outType C)
      entH (inj₁ ic) = inj₁ (inj₂ ic)
      entH (inj₂ od) = inj₂ (inj₁ od)

      -- external output map of the inner composite at its trace level
      extO₂ : Maybe (Channel.outType B ⊎ Channel.inType D)
            → Maybe ((Channel.outType B ⊎ Channel.outType C)
                     ⊎ (Channel.inType D ⊎ Channel.inType C))
      extO₂ nothing          = nothing
      extO₂ (just (inj₁ ob)) = just (inj₁ (inj₁ ob))
      extO₂ (just (inj₂ dd)) = just (inj₂ (inj₁ dd))

      goG : ∀ {s₂ s₂' x y} {sf₀ : Sf} {mo₀ : T.ExtOut} {st₀ : T.TriState}
          → TraceRel itensL s₂ x y s₂'
          → (ig : Channel.inType B ⊎ Channel.outType C)
            (m₀ : Maybe (Channel.outType B ⊎ Channel.inType D))
          → x ≡ entG ig → y ≡ extO₂ m₀
          → T.ContL sf₀ s₂' m₀ mo₀ st₀
          → T.TriG (sf₀ , proj₁ s₂ , proj₂ s₂) ig mo₀ st₀
      goH : ∀ {s₂ s₂' x y} {sf₀ : Sf} {mo₀ : T.ExtOut} {st₀ : T.TriState}
          → TraceRel itensL s₂ x y s₂'
          → (ih : Channel.inType C ⊎ Channel.outType D)
            (m₀ : Maybe (Channel.outType B ⊎ Channel.inType D))
          → x ≡ entH ih → y ≡ extO₂ m₀
          → T.ContL sf₀ s₂' m₀ mo₀ st₀
          → T.TriH (sf₀ , proj₁ s₂ , proj₂ s₂) ih mo₀ st₀

      -- goG, terminal node: the head step must be g's (h-steps are
      -- refuted by the entry index); the output shape decides between
      -- G-passF (middle-B exit towards f) and G-stop.
      goG {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₁ ib) (just (inj₁ ob)) refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passF q κ₀
      goG Trace[ p ] (inj₁ ib) (just (inj₂ dd)) refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goG {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₁ ib) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.G-stop q
      goG {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₂ oc) (just (inj₁ ob)) refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passF q κ₀
      goG Trace[ p ] (inj₂ oc) (just (inj₂ dd)) refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goG {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₂ oc) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.G-stop q

      -- goG, ∷ₒ-headed chain: impossible after a g-entry (the bounced
      -- middle-C output belongs to h, the entry pins the step to g).
      goG (p Trace∷ₒ tr₀) (inj₁ ib) m₀ refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goG (p Trace∷ₒ tr₀) (inj₂ oc) m₀ refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq

      -- goG, ∷ᵢ-headed chain: g emits middle-C ic towards h; recurse.
      goG {s₂ = sg₀ , sh₀} (_Trace∷ᵢ_ {s' = sgm , shm} {inC = ic} p tr₀) (inj₁ ib) m₀ refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passH q (goH tr₀ (inj₁ ic) m₀ refl refl κ₀)
      goG {s₂ = sg₀ , sh₀} (_Trace∷ᵢ_ {s' = sgm , shm} {inC = ic} p tr₀) (inj₂ oc) m₀ refl refl κ₀
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passH q (goH tr₀ (inj₁ ic) m₀ refl refl κ₀)

      -- goH, terminal node: the head step must be h's; the output
      -- shape decides between H-out and H-stop (a middle exit towards
      -- g heads a ∷ₒ link instead).
      goH {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₁ ic) (just (inj₂ dd)) refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-out q
      goH Trace[ p ] (inj₁ ic) (just (inj₁ ob)) refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goH {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₁ ic) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.H-stop q
      goH {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₂ od) (just (inj₂ dd)) refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-out q
      goH Trace[ p ] (inj₂ od) (just (inj₁ ob)) refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goH {s₂ = sg₀ , sh₀} {s₂' = sg₁ , sh₁} Trace[ p ] (inj₂ od) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.H-stop q

      -- goH, ∷ₒ-headed chain: h emits middle-C oc back towards g;
      -- recurse.
      goH {s₂ = sg₀ , sh₀} (_Trace∷ₒ_ {s' = sgm , shm} {outC = oc} p tr₀) (inj₁ ic) m₀ refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-passG q (goG tr₀ (inj₂ oc) m₀ refl refl κ₀)
      goH {s₂ = sg₀ , sh₀} (_Trace∷ₒ_ {s' = sgm , shm} {outC = oc} p tr₀) (inj₂ od) m₀ refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-passG q (goG tr₀ (inj₂ oc) m₀ refl refl κ₀)

      -- goH, ∷ᵢ-headed chain: impossible after an h-entry.
      goH (p Trace∷ᵢ tr₀) (inj₁ ic) m₀ refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goH (p Trace∷ᵢ tr₀) (inj₂ od) m₀ refl refl κ₀
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq

      -- top dispatcher: case the external shapes so the bridged step
      -- converts to a TraceRel itensL value at concrete indices
      go : (i₀ : Channel.inType B ⊎ Channel.outType D)
           (m₀ : Maybe (Channel.outType B ⊎ Channel.inType D))
         → Machine.stepRel (_∘_ {B = C} h g) (sg , sh)
             (construct-⊗ {A = B} {B = D ᵀ} {m = In} i₀)
             ((λ o → construct-⊗ {A = B} {B = D ᵀ} {m = Out} o) <$> m₀) (sg' , sh')
         → T.ContL sf (sg' , sh') m₀ mo st'
         → T.TriBD (sf , sg , sh) i₀ mo st'
      go (inj₁ ib) nothing          p₀ κ₀ = goG p₀ (inj₁ ib) nothing refl refl κ₀
      go (inj₁ ib) (just (inj₁ ob)) p₀ κ₀ = goG p₀ (inj₁ ib) (just (inj₁ ob)) refl refl κ₀
      go (inj₁ ib) (just (inj₂ dd)) p₀ κ₀ = goG p₀ (inj₁ ib) (just (inj₂ dd)) refl refl κ₀
      go (inj₂ od) nothing          p₀ κ₀ = goH p₀ (inj₂ od) nothing refl refl κ₀
      go (inj₂ od) (just (inj₁ ob)) p₀ κ₀ = goH p₀ (inj₂ od) (just (inj₁ ob)) refl refl κ₀
      go (inj₂ od) (just (inj₂ dd)) p₀ κ₀ = goH p₀ (inj₂ od) (just (inj₂ dd)) refl refl κ₀

  ------------------------------------------------------------------------
  -- L-fwd: every step of the LEFT bracketing (h ∘ g) ∘ f flattens into
  -- a TriTrace chain. The outer trace over `tens` is walked by the
  -- mutual workers goF (f-entries) / goI (inner-composite entries);
  -- each inner (h ∘ g) step hanging off a Step₂ node is inverted by
  -- inv-innerL, with the remaining outer chain packaged as the T.ContL
  -- continuation.

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine TriRel

    L-fwd : L-fwd-Stmt
    L-fwd {sp} {sp'} {i} {mo} d = go i mo d
      where
      -- the outer tensor core of cmpL (definitionally the baked-in one)
      tens : Machine (A ⊗₀ B) (D ⊗₀ B)
      tens = modifyStepRel ⇒-solver (f ⊗₁ (_∘_ {B = C} h g))

      -- external output map at the outer trace level
      extO : Maybe (Channel.outType A ⊎ Channel.inType D)
           → Maybe ((Channel.outType A ⊎ Channel.outType B)
                    ⊎ (Channel.inType D ⊎ Channel.inType B))
      extO nothing          = nothing
      extO (just (inj₁ oa)) = just (inj₁ (inj₁ oa))
      extO (just (inj₂ dd)) = just (inj₂ (inj₁ dd))

      -- entry maps: component-level inputs to outer trace-level indices
      entF : Channel.inType A ⊎ Channel.outType B
           → (Channel.inType A ⊎ Channel.inType B)
             ⊎ (Channel.outType D ⊎ Channel.outType B)
      entF (inj₁ a)  = inj₁ (inj₁ a)
      entF (inj₂ ob) = inj₂ (inj₂ ob)

      entI : Channel.inType B ⊎ Channel.outType D
           → (Channel.inType A ⊎ Channel.inType B)
             ⊎ (Channel.outType D ⊎ Channel.outType B)
      entI (inj₁ ib) = inj₁ (inj₂ ib)
      entI (inj₂ od) = inj₂ (inj₁ od)

      goF : ∀ {sp₀ sp₀' x y} → TraceRel tens sp₀ x y sp₀'
          → (iF : Channel.inType A ⊎ Channel.outType B)
            (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
          → x ≡ entF iF → y ≡ extO mo₀
          → T.TriF sp₀ iF mo₀ sp₀'
      goI : ∀ {sp₀ sp₀' x y} → TraceRel tens sp₀ x y sp₀'
          → (iB : Channel.inType B ⊎ Channel.outType D)
            (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
          → x ≡ entI iB → y ≡ extO mo₀
          → T.TriBD sp₀ iB mo₀ sp₀'

      -- goF, terminal node: the head step must be f's; the output
      -- shape decides between F-out and F-stop.
      goF {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₁ a) (just (inj₁ oa)) refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-out q
      goF Trace[ p ] (inj₁ a) (just (inj₂ dd)) refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goF {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₁ a) nothing refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.F-stop q
      goF {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₂ ob) (just (inj₁ oa)) refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-out q
      goF Trace[ p ] (inj₂ ob) (just (inj₂ dd)) refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goF {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₂ ob) nothing refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.F-stop q

      -- goF, ∷ₒ-headed chain: impossible after an f-entry (the bounced
      -- middle-B output belongs to the inner composite).
      goF (p Trace∷ₒ tr₀) (inj₁ a) mo₀ refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goF (p Trace∷ₒ tr₀) (inj₂ ob) mo₀ refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq

      -- goF, ∷ᵢ-headed chain: f emits middle-B ib towards the inner
      -- composite; recurse.
      goF {sp₀ = sf₀ , s₂₀} (_Trace∷ᵢ_ {s' = sfm , s₂m} {inC = ib} p tr₀) (inj₁ a) mo₀ refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-pass q (goI tr₀ (inj₁ ib) mo₀ refl refl)
      goF {sp₀ = sf₀ , s₂₀} (_Trace∷ᵢ_ {s' = sfm , s₂m} {inC = ib} p tr₀) (inj₂ ob) mo₀ refl refl
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-pass q (goI tr₀ (inj₁ ib) mo₀ refl refl)

      -- goI, terminal node: the head step must be the inner
      -- composite's; invert it with inv-innerL, closing with the
      -- terminal continuation (an equation pair).
      goI {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₁ ib) nothing refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | steq
      ... | refl | refl = inv-innerL (inj₁ ib) nothing q₂ (refl , refl)
      goI {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₁ ib) (just (inj₂ dd)) refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = inv-innerL (inj₁ ib) (just (inj₂ dd)) q₂ (refl , refl)
      goI Trace[ p ] (inj₁ ib) (just (inj₁ oa)) refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goI {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₂ od) nothing refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | steq
      ... | refl | refl = inv-innerL (inj₂ od) nothing q₂ (refl , refl)
      goI {sp₀ = sf₀ , s₂₀} {sp₀' = sf₁ , s₂₁} Trace[ p ] (inj₂ od) (just (inj₂ dd)) refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = inv-innerL (inj₂ od) (just (inj₂ dd)) q₂ (refl , refl)
      goI Trace[ p ] (inj₂ od) (just (inj₁ oa)) refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq

      -- goI, ∷ₒ-headed chain: the inner composite emits middle-B ob
      -- towards f; the outer tail (an f-entry chain) becomes the
      -- T.ContL continuation of inv-innerL.
      goI {sp₀ = sf₀ , s₂₀} (_Trace∷ₒ_ {s' = sfm , s₂m} {outC = ob} p tr₀) (inj₁ ib) mo₀ refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl =
            inv-innerL (inj₁ ib) (just (inj₁ ob)) q₂ (goF tr₀ (inj₂ ob) mo₀ refl refl)
      goI {sp₀ = sf₀ , s₂₀} (_Trace∷ₒ_ {s' = sfm , s₂m} {outC = ob} p tr₀) (inj₂ od) mo₀ refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q₂)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl =
            inv-innerL (inj₂ od) (just (inj₁ ob)) q₂ (goF tr₀ (inj₂ ob) mo₀ refl refl)

      -- goI, ∷ᵢ-headed chain: impossible after an inner-composite
      -- entry (the bounced middle-B input belongs to f's output side).
      goI (p Trace∷ᵢ tr₀) (inj₁ ib) mo₀ refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      goI (p Trace∷ᵢ tr₀) (inj₂ od) mo₀ refl refl
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq

      -- top dispatcher over the external (input, output) shapes
      go : (i₀ : Channel.inType A ⊎ Channel.outType D)
           (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
         → Machine.stepRel cmpL sp i₀ mo₀ sp'
         → T.TriExt sp i₀ mo₀ sp'
      go (inj₁ a)  nothing          d₀ = goF d₀ (inj₁ a) nothing refl refl
      go (inj₁ a)  (just (inj₁ oa)) d₀ = goF d₀ (inj₁ a) (just (inj₁ oa)) refl refl
      go (inj₁ a)  (just (inj₂ dd)) d₀ = goF d₀ (inj₁ a) (just (inj₂ dd)) refl refl
      go (inj₂ od) nothing          d₀ = goI d₀ (inj₂ od) nothing refl refl
      go (inj₂ od) (just (inj₁ oa)) d₀ = goI d₀ (inj₂ od) (just (inj₁ oa)) refl refl
      go (inj₂ od) (just (inj₂ dd)) d₀ = goI d₀ (inj₂ od) (just (inj₂ dd)) refl refl

  ------------------------------------------------------------------------
  -- inv-innerR: inverting the inner (g ∘ f) composite of the RIGHT
  -- bracketing. A bridged composite step at the A/C interface is a
  -- TraceRel itensR chain of f-steps (Step₁) and g-steps (Step₂)
  -- bouncing on the middle B. The mutual workers goF'/goG' walk the
  -- chain at fully general trace indices (with separate propositional
  -- index equations, dissolved by conversion inside the unfolding) and
  -- rebuild the TriF/TriG spine, finishing in the supplied ContR
  -- continuation.

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-intro ⊗-fusion ⊗-combine TriRel

    inv-innerR : InvInnerR-Stmt
    inv-innerR {sf} {sg} {sf'} {sg'} {sh} {mo} {st'} i₁ m₁ d κ =
      dispatch i₁ m₁ d κ
      where
      -- entry maps: component-level inputs to inner-trace indices
      entF : Channel.inType A ⊎ Channel.outType B
           → (Channel.inType A ⊎ Channel.inType B)
             ⊎ (Channel.outType C ⊎ Channel.outType B)
      entF (inj₁ a)  = inj₁ (inj₁ a)
      entF (inj₂ ob) = inj₂ (inj₂ ob)

      entG : Channel.inType B ⊎ Channel.outType C
           → (Channel.inType A ⊎ Channel.inType B)
             ⊎ (Channel.outType C ⊎ Channel.outType B)
      entG (inj₁ ib) = inj₁ (inj₂ ib)
      entG (inj₂ oc) = inj₂ (inj₁ oc)

      -- external output map, one level down
      extO₁ : Maybe (Channel.outType A ⊎ Channel.inType C)
            → Maybe ((Channel.outType A ⊎ Channel.outType B)
                   ⊎ (Channel.inType C ⊎ Channel.inType B))
      extO₁ nothing          = nothing
      extO₁ (just (inj₁ oa)) = just (inj₁ (inj₁ oa))
      extO₁ (just (inj₂ ic)) = just (inj₂ (inj₁ ic))

      goF' : ∀ {s₁ s₁' x y} → TraceRel itensR s₁ x y s₁'
           → (iF : Channel.inType A ⊎ Channel.outType B)
             (m₂ : Maybe (Channel.outType A ⊎ Channel.inType C))
             {sh₀ : Sh} {mo₀ : T.ExtOut} {st₀ : T.TriState}
           → x ≡ entF iF → y ≡ extO₁ m₂
           → T.ContR s₁' sh₀ m₂ mo₀ st₀
           → T.TriF (proj₁ s₁ , proj₂ s₁ , sh₀) iF mo₀ st₀
      goG' : ∀ {s₁ s₁' x y} → TraceRel itensR s₁ x y s₁'
           → (iG : Channel.inType B ⊎ Channel.outType C)
             (m₂ : Maybe (Channel.outType A ⊎ Channel.inType C))
             {sh₀ : Sh} {mo₀ : T.ExtOut} {st₀ : T.TriState}
           → x ≡ entG iG → y ≡ extO₁ m₂
           → T.ContR s₁' sh₀ m₂ mo₀ st₀
           → T.TriG (proj₁ s₁ , proj₂ s₁ , sh₀) iG mo₀ st₀

      -- f stepped last: terminal external A-output, silence, or a
      -- C-side output (impossible for f, refuted via the y-equation)
      goF' Trace[ p ] (inj₁ a) (just (inj₁ oa)) refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-out q
      goF' Trace[ p ] (inj₂ ob) (just (inj₁ oa)) refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.F-out q
      goF' Trace[ p ] (inj₁ a) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.F-stop q
      goF' Trace[ p ] (inj₂ ob) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = T.F-stop q
      goF' Trace[ p ] (inj₁ a) (just (inj₂ ic)) refl refl κ
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq))
      goF' Trace[ p ] (inj₂ ob) (just (inj₂ ic)) refl refl κ
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq))

      -- f emitted the middle B: recurse into the g-side of the chain
      goF' (_Trace∷ᵢ_ {inC = ib} p tr₀) (inj₁ a) m₂ refl yeq κ
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.F-pass q (goG' tr₀ (inj₁ ib) m₂ refl yeq κ)
      goF' (_Trace∷ᵢ_ {inC = ib} p tr₀) (inj₂ ob) m₂ refl yeq κ
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.F-pass q (goG' tr₀ (inj₁ ib) m₂ refl yeq κ)

      -- a ∷ₒ-headed chain cannot start at an f-entry
      goF' (p Trace∷ₒ tr₀) (inj₁ a) m₂ refl yeq κ with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (_ , just w , _ , yeq₁ , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq₁))
      goF' (p Trace∷ₒ tr₀) (inj₂ ob) m₂ refl yeq κ with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (_ , just w , _ , yeq₁ , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq₁))

      -- g stepped last: the C-side exit hands over to the supplied
      -- TriH continuation; silence terminates; an A-output is
      -- impossible for g
      goG' Trace[ p ] (inj₁ ib) (just (inj₂ ic)) refl refl κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passH q κ
      goG' Trace[ p ] (inj₂ oc) (just (inj₂ ic)) refl refl κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.G-passH q κ
      goG' Trace[ p ] (inj₁ ib) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.G-stop q
      goG' Trace[ p ] (inj₂ oc) nothing refl refl (refl , refl)
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.G-stop q
      goG' Trace[ p ] (inj₁ ib) (just (inj₁ oa)) refl refl κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      goG' Trace[ p ] (inj₂ oc) (just (inj₁ oa)) refl refl κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

      -- g bounced the middle B back towards f: recurse
      goG' (_Trace∷ₒ_ {outC = ob} p tr₀) (inj₁ ib) m₂ refl yeq κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.G-passF q (goF' tr₀ (inj₂ ob) m₂ refl yeq κ)
      goG' (_Trace∷ₒ_ {outC = ob} p tr₀) (inj₂ oc) m₂ refl yeq κ
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.G-passF q (goF' tr₀ (inj₂ ob) m₂ refl yeq κ)

      -- a ∷ᵢ-headed chain cannot start at a g-entry
      goG' (p Trace∷ᵢ tr₀) (inj₁ ib) m₂ refl yeq κ with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (_ , just w , _ , yeq₁ , _ , _) = inj₁≢inj₂ (just-inj yeq₁)
      goG' (p Trace∷ᵢ tr₀) (inj₂ oc) m₂ refl yeq κ with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (_ , just w , _ , yeq₁ , _ , _) = inj₁≢inj₂ (just-inj yeq₁)

      -- top dispatcher over the explicit composite input/output shapes
      dispatch : (i₁' : Channel.inType A ⊎ Channel.outType C)
                 (m₁' : Maybe (Channel.outType A ⊎ Channel.inType C))
               → Machine.stepRel (_∘_ {B = B} g f) (sf , sg)
                   (construct-⊗ {A = A} {B = C ᵀ} {m = In} i₁')
                   ((λ o → construct-⊗ {A = A} {B = C ᵀ} {m = Out} o) <$> m₁')
                   (sf' , sg')
               → T.ContR (sf' , sg') sh m₁' mo st'
               → T.TriAC (sf , sg , sh) i₁' mo st'
      dispatch (inj₁ a)  (just (inj₁ oa)) d' κ' =
        goF' d' (inj₁ a) (just (inj₁ oa)) refl refl κ'
      dispatch (inj₁ a)  (just (inj₂ ic)) d' κ' =
        goF' d' (inj₁ a) (just (inj₂ ic)) refl refl κ'
      dispatch (inj₁ a)  nothing          d' κ' =
        goF' d' (inj₁ a) nothing refl refl κ'
      dispatch (inj₂ oc) (just (inj₁ oa)) d' κ' =
        goG' d' (inj₂ oc) (just (inj₁ oa)) refl refl κ'
      dispatch (inj₂ oc) (just (inj₂ ic)) d' κ' =
        goG' d' (inj₂ oc) (just (inj₂ ic)) refl refl κ'
      dispatch (inj₂ oc) nothing          d' κ' =
        goG' d' (inj₂ oc) nothing refl refl κ'

    ------------------------------------------------------------------
    -- R-fwd: every step of the RIGHT bracketing h ∘ (g ∘ f) flattens
    -- into a TriTrace chain. h-steps are outer Step₂ nodes (walked by
    -- goH); (g ∘ f)-steps are outer Step₁ nodes whose payload is
    -- inverted by inv-innerR, with goH supplying the middle-C
    -- continuation (goI).

    R-fwd : R-fwd-Stmt
    R-fwd {sp = (sf , sg) , sh} {sp' = (sf' , sg') , sh'} {i} {mo} d =
      go i mo d
      where
      -- index maps at the outer (middle C) trace level
      extO : Maybe (Channel.outType A ⊎ Channel.inType D)
           → Maybe ((Channel.outType A ⊎ Channel.outType C)
                  ⊎ (Channel.inType D ⊎ Channel.inType C))
      extO nothing          = nothing
      extO (just (inj₁ oa)) = just (inj₁ (inj₁ oa))
      extO (just (inj₂ d₀)) = just (inj₂ (inj₁ d₀))

      entH : Channel.inType C ⊎ Channel.outType D
           → (Channel.inType A ⊎ Channel.inType C)
           ⊎ (Channel.outType D ⊎ Channel.outType C)
      entH (inj₁ ic) = inj₁ (inj₂ ic)
      entH (inj₂ od) = inj₂ (inj₁ od)

      entI : Channel.inType A ⊎ Channel.outType C
           → (Channel.inType A ⊎ Channel.inType C)
           ⊎ (Channel.outType D ⊎ Channel.outType C)
      entI (inj₁ a)  = inj₁ (inj₁ a)
      entI (inj₂ oc) = inj₂ (inj₂ oc)

      goH : ∀ {sq sq' x y} → TraceRel tensR sq x y sq'
          → (iH : Channel.inType C ⊎ Channel.outType D)
            (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
          → x ≡ entH iH → y ≡ extO mo₀
          → T.TriH (proj₁ (proj₁ sq) , proj₂ (proj₁ sq) , proj₂ sq) iH mo₀
                   (proj₁ (proj₁ sq') , proj₂ (proj₁ sq') , proj₂ sq')
      goI : ∀ {sq sq' x y} → TraceRel tensR sq x y sq'
          → (i₂ : Channel.inType A ⊎ Channel.outType C)
            (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
          → x ≡ entI i₂ → y ≡ extO mo₀
          → T.TriAC (proj₁ (proj₁ sq) , proj₂ (proj₁ sq) , proj₂ sq) i₂ mo₀
                    (proj₁ (proj₁ sq') , proj₂ (proj₁ sq') , proj₂ sq')

      -- h stepped last: external D-output or silence; an A-side output
      -- is impossible for h, and a Step₁ head is refuted via x
      goH Trace[ p ] (inj₁ ic) (just (inj₂ d₀)) refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-out q
      goH Trace[ p ] (inj₂ od) (just (inj₂ d₀)) refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq) | steq
      ... | refl | refl | refl = T.H-out q
      goH Trace[ p ] (inj₁ ic) nothing refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.H-stop q
      goH Trace[ p ] (inj₂ od) nothing refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₂ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₂-inj xeq | steq
      ... | refl | refl = T.H-stop q
      goH Trace[ p ] (inj₁ ic) (just (inj₁ oa)) refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
      goH Trace[ p ] (inj₂ od) (just (inj₁ oa)) refl refl with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₂ (_ , just w , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

      -- h emitted the middle C towards (g ∘ f): outer ∷ₒ link, the
      -- tail enters at the inner composite's C-entry
      goH (_Trace∷ₒ_ {outC = oc} p tr₀) (inj₁ ic) mo₀ refl yeq
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.H-passG q (goI tr₀ (inj₂ oc) mo₀ refl yeq)
      goH (_Trace∷ₒ_ {outC = oc} p tr₀) (inj₂ od) mo₀ refl yeq
        with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        T.H-passG q (goI tr₀ (inj₂ oc) mo₀ refl yeq)

      -- a ∷ᵢ-headed chain cannot start at an h-entry
      goH (p Trace∷ᵢ tr₀) (inj₁ ic) mo₀ refl yeq with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (_ , just w , _ , yeq₁ , _ , _) = inj₁≢inj₂ (just-inj yeq₁)
      goH (p Trace∷ᵢ tr₀) (inj₂ od) mo₀ refl yeq with comp-view p
      ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
      ... | inj₂ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₂ (_ , just w , _ , yeq₁ , _ , _) = inj₁≢inj₂ (just-inj yeq₁)

      -- (g ∘ f) stepped last: terminal external A-output or silence,
      -- inverted by inv-innerR with the terminal ContR pair; a D-side
      -- output is impossible for the inner composite
      goI Trace[ p ] (inj₁ a) (just (inj₁ oa)) refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl =
        inv-innerR (inj₁ a) (just (inj₁ oa)) q (refl , refl)
      goI Trace[ p ] (inj₂ oc) (just (inj₁ oa)) refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq) | steq
      ... | refl | refl | refl =
        inv-innerR (inj₂ oc) (just (inj₁ oa)) q (refl , refl)
      goI Trace[ p ] (inj₁ a) nothing refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = inv-innerR (inj₁ a) nothing q (refl , refl)
      goI Trace[ p ] (inj₂ oc) nothing refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) = nothing≢just yeq
      ... | inj₁ (mᵢ , nothing , xeq , _ , steq , q)
        with inj₁-inj xeq | steq
      ... | refl | refl = inv-innerR (inj₂ oc) nothing q (refl , refl)
      goI Trace[ p ] (inj₁ a) (just (inj₂ d₀)) refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq))
      goI Trace[ p ] (inj₂ oc) (just (inj₂ d₀)) refl refl with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
      ... | inj₁ (_ , just w , _ , yeq , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq))

      -- (g ∘ f) emitted the middle C towards h: invert the inner step
      -- with the TriH continuation built from the tail
      goI (_Trace∷ᵢ_ {inC = ic} p tr₀) (inj₁ a) mo₀ refl yeq
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        inv-innerR (inj₁ a) (just (inj₂ ic)) q (goH tr₀ (inj₁ ic) mo₀ refl yeq)
      goI (_Trace∷ᵢ_ {inC = ic} p tr₀) (inj₂ oc) mo₀ refl yeq
        with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (mᵢ , just w , xeq , yeq₁ , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq₁) | steq
      ... | refl | refl | refl =
        inv-innerR (inj₂ oc) (just (inj₂ ic)) q (goH tr₀ (inj₁ ic) mo₀ refl yeq)

      -- a ∷ₒ-headed chain cannot start at a (g ∘ f)-entry
      goI (p Trace∷ₒ tr₀) (inj₁ a) mo₀ refl yeq with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (_ , just w , _ , yeq₁ , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq₁))
      goI (p Trace∷ₒ tr₀) (inj₂ oc) mo₀ refl yeq with comp-view p
      ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
      ... | inj₁ (_ , nothing , _ , yeq₁ , _ , _) = just≢nothing yeq₁
      ... | inj₁ (_ , just w , _ , yeq₁ , _ , _) =
        inj₁≢inj₂ (sym (just-inj yeq₁))

      -- top dispatcher over the external input/output shapes
      go : (i₀ : Channel.inType A ⊎ Channel.outType D)
           (mo₀ : Maybe (Channel.outType A ⊎ Channel.inType D))
         → Machine.stepRel cmpR ((sf , sg) , sh) i₀ mo₀ ((sf' , sg') , sh')
         → TriRel (sf , sg , sh) i₀ mo₀ (sf' , sg' , sh')
      go (inj₁ a)  (just (inj₁ oa)) t = goI t (inj₁ a) (just (inj₁ oa)) refl refl
      go (inj₁ a)  (just (inj₂ d₀)) t = goI t (inj₁ a) (just (inj₂ d₀)) refl refl
      go (inj₁ a)  nothing          t = goI t (inj₁ a) nothing refl refl
      go (inj₂ od) (just (inj₁ oa)) t = goH t (inj₂ od) (just (inj₁ oa)) refl refl
      go (inj₂ od) (just (inj₂ d₀)) t = goH t (inj₂ od) (just (inj₂ d₀)) refl refl
      go (inj₂ od) nothing          t = goH t (inj₂ od) nothing refl refl

  -- The four cores assembled: both bracketings are isomorphic to the
  -- flattened TriTrace machine.
  ∘-assoc : cmpL ≅ᴹ cmpR
  ∘-assoc = assemble L-fwd L-bwd R-fwd R-bwd

-- The third bisimulation: ((h ∘ g) ∘ f) ≅ᴹ (h ∘ (g ∘ f)).
∘-assoc-≅ᴹ : ∀ {A B C D} {f : Machine A B} {g : Machine B C} {h : Machine C D}
           → (_∘_ {B = B} (_∘_ {B = C} h g) f) ≅ᴹ (_∘_ {B = C} h (_∘_ {B = B} g f))
∘-assoc-≅ᴹ {f = f} {g = g} {h = h} = ∘-assoc-implementation.∘-assoc f g h

------------------------------------------------------------------------
-- Congruences for the remaining machine builders.  `_⊗ʳ_`/`_⊗ˡ_`,
-- `_∘ᴷ_`, `_⊗ᴷ_` and `⨂ᴷ` are all built from `_⊗₁_`, `_∘_` and `id`,
-- so each is a corollary of the tensor congruence.

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

-- The tensor congruence.
⊗₁-resp-≅ᴹ : ∀ {A B C D} {M M' : Machine A B} {N N' : Machine C D}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ⊗₁ N) ≅ᴹ (M' ⊗₁ N')
⊗₁-resp-≅ᴹ φ ψ = MkIso
  (×-map (to φ) (to ψ))
  (×-map (from φ) (from ψ))
  (λ (s₁ , s₂) → cong₂ _,_ (from∘to φ s₁) (from∘to ψ s₂))
  (λ (s₁ , s₂) → cong₂ _,_ (to∘from φ s₁) (to∘from ψ s₂))
  (CompRel-map φ ψ)
  (CompRel-map (≅ᴹ-sym φ) (≅ᴹ-sym ψ))

-- The derived congruences.  `_⊗ʳ_`/`_⊗ˡ_`, `_∘ᴷ_`, `_⊗ᴷ_` and `⨂ᴷ` are all
-- built from `_⊗₁_`, `_∘_` and `id`, so each is a direct corollary.

⊗ʳ-resp-≅ᴹ : ∀ {A B} {M M' : Machine A B} (C : Channel)
           → M ≅ᴹ M' → (M ⊗ʳ C) ≅ᴹ (M' ⊗ʳ C)
⊗ʳ-resp-≅ᴹ _ φ = ⊗₁-resp-≅ᴹ φ ≅ᴹ-refl

∘ᴷ-resp-≅ᴹ : ∀ {A B C E₁ E₂} {M M' : Machine B (C ⊗₀ E₂)} {N N' : Machine A (B ⊗₀ E₁)}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ∘ᴷ N) ≅ᴹ (M' ∘ᴷ N')
∘ᴷ-resp-≅ᴹ {E₁ = E₁} φ ψ =
  ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ (⊗ʳ-resp-≅ᴹ E₁ φ) ψ)

⊗ᴷ-resp-≅ᴹ : ∀ {A₁ B₁ E₁ A₂ B₂ E₂}
             {M M' : Machine A₁ (B₁ ⊗₀ E₁)} {N N' : Machine A₂ (B₂ ⊗₀ E₂)}
           → M ≅ᴹ M' → N ≅ᴹ N' → (M ⊗ᴷ N) ≅ᴹ (M' ⊗ᴷ N')
⊗ᴷ-resp-≅ᴹ φ ψ = ∘-resp-≅ᴹ ≅ᴹ-refl (⊗₁-resp-≅ᴹ φ ψ)

⨂ᴷ-resp-≅ᴹ : ∀ {n} {A B E : Fin n → Channel}
             {f g : (k : Fin n) → Machine (A k) (B k ⊗₀ E k)}
           → (∀ k → f k ≅ᴹ g k) → ⨂ᴷ f ≅ᴹ ⨂ᴷ g
⨂ᴷ-resp-≅ᴹ {zero}  φ = ≅ᴹ-refl
⨂ᴷ-resp-≅ᴹ {suc n} φ = ⊗ᴷ-resp-≅ᴹ (φ fzero) (⨂ᴷ-resp-≅ᴹ (λ k → φ (fsuc k)))

-- Two associativities at once.
module _ where
  assoc²γδ-≅ᴹ : ∀ {A B C D E} {f : Machine A B} {g : Machine B C}
                  {h : Machine C D} {i : Machine D E}
              → ((i ∘ h) ∘ (g ∘ f)) ≅ᴹ (i ∘ ((h ∘ g) ∘ f))
  assoc²γδ-≅ᴹ {f = f} {g} {h} {i} =
    ≅ᴹ-trans (∘-assoc-≅ᴹ {f = g ∘ f} {g = h} {h = i})
             (∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym (∘-assoc-≅ᴹ {f = f} {g = g} {h = h})))

-- ----------------------------------------------------------------------------
-- `_≡ᴹ_` (heterogeneous machine equality, `Machine.Core`) carries the
-- channel-level bookkeeping that `_≅ᴹ_`, being homogeneous, cannot express.
-- Two facts relating it to `_≅ᴹ_`, plus the `∘ᴷ` congruence for it.
-- ----------------------------------------------------------------------------

module _ where
  open import Relation.Binary.HeterogeneousEquality using () renaming (refl to H-refl)

  ≡ᴹ→≅ᴹ : ∀ {A B} {M N : Machine A B} → M ≡ᴹ N → M ≅ᴹ N
  ≡ᴹ→≅ᴹ record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl } = ≅ᴹ-refl

  -- NB: the channel equalities are explicit arguments.  Matching them off the
  -- `_≡ᴹ_` fields instead would require inverting `_⊗₀_` — that is exactly the
  -- `⊗-injectiveˡ/ʳ` the old record postulated, and it is unprovable (the
  -- inconsistency lived in asserting it alongside the unit laws).  Every call
  -- site has the component equalities to hand anyway.
  ∘ᴷ-cong-≡ᴹ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ E₁₁ E₁₂ E₂₁ E₂₂}
              → B₁ ≡ B₂ → C₁ ≡ C₂ → E₂₁ ≡ E₂₂ → E₁₁ ≡ E₁₂
              → {M : Machine B₁ (C₁ ⊗₀ E₂₁)} {M' : Machine B₂ (C₂ ⊗₀ E₂₂)}
                {N : Machine A₁ (B₁ ⊗₀ E₁₁)} {N' : Machine A₂ (B₂ ⊗₀ E₁₂)}
              → M ≡ᴹ M' → N ≡ᴹ N' → (M ∘ᴷ N) ≡ᴹ (M' ∘ᴷ N')
  ∘ᴷ-cong-≡ᴹ refl refl refl refl
             record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl }
             record { A≡C = refl ; B≡D = refl ; M₁≡M₂ = H-refl } = ≡ᴹ-refl

-- ----------------------------------------------------------------------------
-- Transport of a run along an isomorphism: only the states move (`to φ`),
-- every input/output is kept.
-- ----------------------------------------------------------------------------

Trace-map : ∀ {A B} {P Q : Machine A B} (φ : P ≅ᴹ Q) {s s'}
          → Trace P s s' → Trace Q (to φ s) (to φ s')
Trace-map φ []                    = []
Trace-map φ (tr ∷ʳ⟨ i , o , st ⟩) = Trace-map φ tr ∷ʳ⟨ i , o , step-to φ st ⟩

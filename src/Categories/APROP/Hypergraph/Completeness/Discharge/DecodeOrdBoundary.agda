-- Discharge of the `decodeOrd-boundary-resp-≈` residual postulated in
-- `DecodeRelRespIsoWired.agda`.
--
-- ## What this module proves (GIVEN K)
--
-- The residual `decodeOrd-boundary-resp-≈` relates the two natural-order
-- decodings of `⟪f⟫` and `⟪g⟫` (transported to the user-facing `flatten`
-- boundary) given the wiring's iso-boundary hypothesis.  Its ONLY genuine
-- mathematical content is:
--
--   (K₁) Two `Valid ⟪f⟫ (range)` witnesses — `vrange f` (from totality)
--        and `vH` (threaded from the wiring) — are two `↭`-derivations of
--        the SAME endpoints `finalStack (range) ↭ cod ⟪f⟫`.  Their final
--        `permute-via-vlab` factors therefore agree up to `≈Term` by the
--        Kelly faithfulness residual `FaithfulnessResidual.permute-resp-≅↭`.
--        The `≅↭` (equal-evaluated-bijection) hypothesis it needs is
--        discharged FOR FREE by rigidity (`eval-rigid`, inlined below)
--        because the vertex-level codomain `cod ⟪f⟫` is `Unique`
--        (`⟪_⟫-cod-unique`).
--
--   (K₂) Pure `subst₂`-transport algebra for the boundary equalities,
--        which needs UIP on `ObjTerm` (the composite boundary paths agree).
--
-- Both K-inputs are taken as EXPLICIT module parameters:
--
--   * `K  : FaithfulnessResidual` — the TRUE Kelly residual that gates the
--     final-permute throughout this development (a record value, defined in
--     the `--without-K` module `PermuteCoherence.Faithfulness`).
--   * `objUIP` — uniqueness-of-identity-proofs on `ObjTerm` (a K-consequence
--     taken as a hypothesis so the module stays `--without-K`-importable).
--
-- Hence the headline lemma `decodeOrd-boundary-resp-≈` is proved **given K**,
-- with NO new postulate.  This mirrors `Discharge/Sub/StackEvalCoherence.agda`:
-- two `↭`-derivations into the same `Unique` codomain evaluate to the same
-- FinBij via `eval-rigid`, then K closes the gap; the boundary `subst₂` is
-- pure transport algebra.
--
-- ## --without-K
--
-- This module is `--without-K`.  Co-infectivity forbids importing the
-- `--with-K` modules `PermuteCoherence.{Rigid,Map}`, so the (intrinsically
-- K-free, J-only) helpers `eval-rigid`, `eval-map⁺`, `subst₂-FinBij-≈` are
-- re-derived inline here.  The one genuinely K-dependent fact (UIP on
-- `ObjTerm`) is an explicit parameter, alongside the Kelly residual.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeOrdBoundary
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig using (process-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)

-- The Kelly faithfulness residual K (`permute-resp-≅↭`), exposed as a
-- record in the `--without-K` module `PermuteCoherence.Faithfulness`,
-- parameterised over the APROP `FreeMonoidalData`.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

-- K-free FinBij/eval infrastructure (`--cubical-compatible` modules).
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; _∘-fb_; cons-fb; swap-fb)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open import Data.List using (List; []; _∷_; map; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᵘ; _∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

------------------------------------------------------------------------
-- §0. K-FREE helper infrastructure (inlined, J-only copies of the
--     intrinsically K-free lemmas that happen to live in `--with-K`
--     modules `PermuteCoherence.{Rigid,Map}`).
------------------------------------------------------------------------

private
  ----------------------------------------------------------------------
  -- 0a. Rigidity of `eval-↭` on `Unique` codomains (copy of
  --     `PermuteCoherence.Rigid.eval-rigid`; structural, no K).
  ----------------------------------------------------------------------

  All-lookup : ∀ {a p} {A : Set a} {Q : A → Set p} {xs : List A}
             → All Q xs → (i : Fin (length xs)) → Q (lookup xs i)
  All-lookup (q ∷ _)  zero    = q
  All-lookup (_ ∷ qs) (suc i) = All-lookup qs i

  lookup-injective-unique
    : ∀ {a} {A : Set a} {xs : List A}
    → Unique xs → (i j : Fin (length xs))
    → lookup xs i ≡ lookup xs j
    → i ≡ j
  lookup-injective-unique (_  ∷ᵘ _ ) zero    zero    _  = refl
  lookup-injective-unique (x≢ ∷ᵘ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
  lookup-injective-unique (x≢ ∷ᵘ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
  lookup-injective-unique (_  ∷ᵘ uq) (suc i) (suc j) eq =
    cong suc (lookup-injective-unique uq i j eq)

  lookup-sound
    : ∀ {a} {A : Set a} {xs ys : List A} (p : xs ↭ ys) (i : Fin (length xs))
    → lookup ys (eval-↭ p P.⟨$⟩ʳ i) ≡ lookup xs i
  lookup-sound Perm.refl         i             = refl
  lookup-sound (Perm.prep x p)   0F            = refl
  lookup-sound (Perm.prep x p)   (suc i)       = lookup-sound p i
  lookup-sound (Perm.swap x y p) 0F            = refl
  lookup-sound (Perm.swap x y p) (suc 0F)      = refl
  lookup-sound (Perm.swap x y p) (suc (suc i)) = lookup-sound p i
  lookup-sound (Perm.trans p q)  i             =
    trans (lookup-sound q (eval-↭ p P.⟨$⟩ʳ i)) (lookup-sound p i)

  eval-rigid
    : ∀ {a} {A : Set a} {xs ys : List A} → Unique ys
    → (p q : xs ↭ ys)
    → eval-↭ p ≈-fb eval-↭ q
  eval-rigid uniq p q i =
    lookup-injective-unique uniq _ _
      (trans (lookup-sound p i) (sym (lookup-sound q i)))

  ----------------------------------------------------------------------
  -- 0b. `eval-map⁺` and its `subst₂`-on-FinBij algebra (copies of the
  --     `PermuteCoherence.Map` lemmas; all J-only, no K).
  ----------------------------------------------------------------------

  -- All cast lemmas below are matched on the `length`-proofs at `refl`, so
  -- NO higher-order unification on `suc`/`λ z → suc (suc z)` is required
  -- (which `--without-K` would otherwise block).

  subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
  subst₂-FinBij-id refl = refl

  -- cons cast: prepend identity commutes with the (sym) length cast.
  cons-cast
    : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
    → cons-fb (subst₂ FinBij (sym ex) (sym ey) π)
      ≡ subst₂ FinBij (sym (cong suc ex)) (sym (cong suc ey)) (cons-fb π)
  cons-cast refl refl π = refl

  -- swap cast: a leading `swap-fb` block commutes with the (sym) length cast.
  swap-cast
    : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
    → swap-fb m' ∘-fb cons-fb (cons-fb (subst₂ FinBij (sym ex) (sym ey) π))
      ≡ subst₂ FinBij (sym (cong suc (cong suc ex)))
                      (sym (cong suc (cong suc ey)))
                      (swap-fb m ∘-fb cons-fb (cons-fb π))
  swap-cast refl refl π = refl

  -- composition cast: `∘-fb` distributes over the (sym) length casts.
  comp-cast
    : ∀ {n n' m m' k k'}
        (ex : n' ≡ n) (ey : m' ≡ m) (ez : k' ≡ k)
        (g : FinBij m k) (f : FinBij n m)
    → subst₂ FinBij (sym ey) (sym ez) g ∘-fb subst₂ FinBij (sym ex) (sym ey) f
      ≡ subst₂ FinBij (sym ex) (sym ez) (g ∘-fb f)
  comp-cast refl refl refl g f = refl

  -- `eval-↭ (map⁺ h p)` is `eval-↭ p` transported along the length casts.
  eval-map⁺ : ∀ {A C : Set}
    (h : A → C) {xs ys : List A} (p : xs ↭ ys)
    → eval-↭ (PermProp.map⁺ h p)
      ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
  eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
  eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
    -- eval (map⁺ (prep x p)) = cons-fb (eval (map⁺ p))
    --   = cons-fb (subst₂ (sym (lm xs)) (sym (lm ys)) (eval p))   [IH]
    --   = subst₂ (sym (cong suc (lm xs))) (sym (cong suc (lm ys))) (cons-fb (eval p))
    -- and length-map h (x ∷ xs) = cong suc (length-map h xs) definitionally.
    trans (cong cons-fb (eval-map⁺ h p))
          (cons-cast (length-map h xs) (length-map h ys) (eval-↭ p))
  eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
    trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
          (swap-cast (length-map h xs) (length-map h ys) (eval-↭ p))
  eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
    trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
          (comp-cast (length-map h xs) (length-map h ys) (length-map h zs)
                     (eval-↭ q) (eval-↭ p))

  subst₂-FinBij-≈ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') {π ρ : FinBij n m}
    → π ≈-fb ρ → subst₂ FinBij a b π ≈-fb subst₂ FinBij a b ρ
  subst₂-FinBij-≈ refl refl eq = eq

------------------------------------------------------------------------
-- §1. The lemma, GIVEN K (the Kelly residual + ObjTerm-UIP).
------------------------------------------------------------------------

module _ (K : FaithfulnessResidual)
         (objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q) where
  open FaithfulnessResidual K

  ----------------------------------------------------------------------
  -- (K₁) The two validity witnesses agree on their final permute, up to
  -- ≈Term.
  --
  -- `permute-via-vlab vlab v = permute (PermProp.map⁺ vlab v)`
  -- definitionally (Completeness.Permute = FreeSMC.Steps).  The two
  -- derivations `map⁺ vlab v` and `map⁺ vlab w` evaluate to the same
  -- FinBij:
  --   * `eval-map⁺` rewrites each to `subst₂ FinBij _ _ (eval-↭ v)`,
  --   * the inner `eval-↭ v ≈-fb eval-↭ w` holds by `eval-rigid` since
  --     `cod ⟪f⟫` is `Unique` (`⟪_⟫-cod-unique f`),
  --   * `subst₂-FinBij-≈` transports the equality through the (identical)
  --     length casts.
  -- This is exactly the `≅↭` hypothesis of `FaithfulnessResidual`, so K
  -- (`permute-resp-≅↭`) closes it.
  ----------------------------------------------------------------------

  private
    permute-≅↭
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → eval-↭ (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) v)
        ≈-fb eval-↭ (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) w)
    permute-≅↭ {A} {B} f v w =
      subst (λ z → z ≈-fb eval-↭ (PermProp.map⁺ vlab w))
            (sym (eval-map⁺ vlab v))
        (subst (λ z → subst₂ FinBij (sym (length-map vlab stk))
                                    (sym (length-map vlab cod)) (eval-↭ v)
                      ≈-fb z)
               (sym (eval-map⁺ vlab w))
          (subst₂-FinBij-≈ (sym (length-map vlab stk)) (sym (length-map vlab cod))
            (eval-rigid (⟪ f ⟫-cod-unique) v w)))
      where
        vlab = Hypergraph.vlab ⟪ f ⟫
        stk  = proj₁ (process-edges ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))
                       (Hypergraph.dom ⟪ f ⟫))
        cod  = Hypergraph.cod ⟪ f ⟫

    permute-via-vlab-coh
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → permute-via-vlab (Hypergraph.vlab ⟪ f ⟫) v
        ≈Term permute-via-vlab (Hypergraph.vlab ⟪ f ⟫) w
    permute-via-vlab-coh f v w =
      permute-resp-≅↭
        (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) v)
        (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫) w)
        (permute-≅↭ f v w)

    -- The two natural-order decodings of `⟪f⟫` differ ONLY in the
    -- final-permute factor, so they agree up to ≈Term.
    decodeOrd-witness-coh
      : ∀ {A B} (f : HomTerm A B)
          (v w : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
      → IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) v
        ≈Term IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) w
    decodeOrd-witness-coh f v w =
      ∘-resp-≈ (permute-via-vlab-coh f v w) ≈-Term-refl

    ------------------------------------------------------------------
    -- (K₂) Pure subst₂-transport algebra for the boundary.

    subst₂-HomTerm-fuse
      : ∀ {a₁ a₂ a₃ : ObjTerm} {b₁ b₂ b₃ : ObjTerm}
          (pa : a₁ ≡ a₂) (pa' : a₂ ≡ a₃)
          (pb : b₁ ≡ b₂) (pb' : b₂ ≡ b₃)
          (t : HomTerm a₁ b₁)
      → subst₂ HomTerm pa' pb' (subst₂ HomTerm pa pb t)
        ≡ subst₂ HomTerm (trans pa pa') (trans pb pb') t
    subst₂-HomTerm-fuse refl refl refl refl t = refl

    subst₂-HomTerm-irr
      : ∀ {a₁ a₂ : ObjTerm} {b₁ b₂ : ObjTerm}
          (pa pa' : a₁ ≡ a₂) (pb pb' : b₁ ≡ b₂)
          (t : HomTerm a₁ b₁)
      → pa ≡ pa' → pb ≡ pb'
      → subst₂ HomTerm pa pb t ≡ subst₂ HomTerm pa' pb' t
    subst₂-HomTerm-irr pa pa' pb pb' t refl refl = refl

    subst₂-resp-≈
      : ∀ {a₁ a₂ : ObjTerm} {b₁ b₂ : ObjTerm}
          (pa : a₁ ≡ a₂) (pb : b₁ ≡ b₂) {s t : HomTerm a₁ b₁}
      → s ≈Term t → subst₂ HomTerm pa pb s ≈Term subst₂ HomTerm pa pb t
    subst₂-resp-≈ refl refl eq = eq

    ≈-of-≡ : ∀ {a b : ObjTerm} {s t : HomTerm a b} → s ≡ t → s ≈Term t
    ≈-of-≡ refl = ≈-Term-refl

  --------------------------------------------------------------------
  -- The headline lemma — matches the EXACT type of the
  -- `decodeOrd-boundary-resp-≈` postulate in `DecodeRelRespIsoWired.agda`
  -- (with K threaded as the enclosing module argument).
  --------------------------------------------------------------------

  decodeOrd-boundary-resp-≈
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (vf : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
        (vg : IW.PerHG.Valid ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)))
        (vH : IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)))
    → ( subst₂ HomTerm (cong unflatten (IW.domL-iso iso)) (cong unflatten (IW.codL-iso iso))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg)
        ≈Term
        IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vH )
    → ( subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
          (IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vf)
        ≈Term
        subst₂ HomTerm (cong unflatten (⟪⟫-domL g)) (cong unflatten (⟪⟫-codL g))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg) )
  decodeOrd-boundary-resp-≈ {A} {B} f g iso vf vg vH wiring≈ =
    -- LHS ≈ subst₂(df,cf)(dOrd ⟪f⟫ vH)                       [K₁, step1]
    --     ≈ subst₂(df,cf)(subst₂(di,ci)(dOrd ⟪g⟫))          [wiring≈, step2]
    --     ≡ subst₂(dg,cg)(dOrd ⟪g⟫)                         [K₂, step3]
    ≈-Term-trans step1 (≈-Term-trans step2 (≈-of-≡ step3))
    where
      df  = cong unflatten (⟪⟫-domL f)
      cf  = cong unflatten (⟪⟫-codL f)
      dg  = cong unflatten (⟪⟫-domL g)
      cg  = cong unflatten (⟪⟫-codL g)
      di  = cong unflatten (IW.domL-iso iso)
      ci  = cong unflatten (IW.codL-iso iso)

      dOrd-f-vr = IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vf
      dOrd-f-vH = IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) vH
      dOrd-g    = IW.PerHG.decodeOrd ⟪ g ⟫ (dep-irrefl-⟪⟫ g) (range (Hypergraph.nE ⟪ g ⟫)) vg

      step1
        : subst₂ HomTerm df cf dOrd-f-vr ≈Term subst₂ HomTerm df cf dOrd-f-vH
      step1 = subst₂-resp-≈ df cf (decodeOrd-witness-coh f vf vH)

      step2
        : subst₂ HomTerm df cf dOrd-f-vH
          ≈Term subst₂ HomTerm df cf (subst₂ HomTerm di ci dOrd-g)
      step2 = subst₂-resp-≈ df cf (≈-Term-sym wiring≈)

      dom-uip : trans di df ≡ dg
      dom-uip = objUIP (trans di df) dg

      cod-uip : trans ci cf ≡ cg
      cod-uip = objUIP (trans ci cf) cg

      step3
        : subst₂ HomTerm df cf (subst₂ HomTerm di ci dOrd-g)
          ≡ subst₂ HomTerm dg cg dOrd-g
      step3 =
        trans (subst₂-HomTerm-fuse di df ci cf dOrd-g)
              (subst₂-HomTerm-irr (trans di df) dg (trans ci cf) cg dOrd-g
                                  dom-uip cod-uip)

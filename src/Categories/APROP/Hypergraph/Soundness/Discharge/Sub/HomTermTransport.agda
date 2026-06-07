{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Shared `subst₂`/transport algebra for the box-shape decode residuals.
--
-- LEAF module: imports NONE of the `Decode{Compose,Tensor,AgenSigma}
-- {Shape,Pruned}` box-shape modules.  Collects the `subst₂`-cancellation /
-- commutation / distributivity lemmas, the `permute`-relabel-freeness
-- lemma `pvv-relabel`, and the extraction pair `decode-attempt-extract` /
-- `Linear⇒cod-Unique`, shared across all box-shape consumers.
--
-- `subst₂-resp-≈Term` here is the GENERAL (arbitrary-`ObjTerm`-endpoint)
-- variant, distinct from the `cong unflatten`-specialised one in
-- `DecodeRoundtripSafe`.  `objUIP` and `Kf : FaithfulnessResidual` are
-- EXPLICIT per-lemma arguments (not module parameters), matching the
-- consumers' call sites.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-all-edges; decode-attempt; extract-exact)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (decode; decode-attempt-Linear)
import Categories.APROP.Hypergraph.Soundness.Linearity sig as Lin
-- `≡⇒≈Term` lives in `Categories.FreeMonoidal`; consumers reach it via
-- their own `open APROP sig`.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.Hypergraph.ExtractPrefixEvalPhi
  using (eval-map⁺; cast-irrel; subst₂-FinBij-∘; ≈-fb-of-≡)

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-∘; map-cong; length-map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

-- `just ≢ nothing` (shared across the box-shape consumers).
just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

-- Transporting `id` along a diagonal boundary proof is `id` (refl).
subst₂-HomTerm-id : ∀ {A B} (p : A ≡ B) → subst₂ HomTerm p p id ≡ id
subst₂-HomTerm-id refl = refl

-- SKIP closer: under `objUIP`, transporting `id` along ANY two boundary
-- paths with equal endpoints is `≈Term id`.
subst₂-id-≈
  : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
    {A B : ObjTerm} (p q : A ≡ B) → subst₂ HomTerm p q id ≈Term id
subst₂-id-≈ objUIP p q =
  ≡⇒≈Term (trans (cong (λ z → subst₂ HomTerm z q id) (objUIP p q))
                 (subst₂-HomTerm-id q))

-- `subst₂ FlatGen` over `trans p (sym p')` cancels back to the inner
-- `subst₂ FlatGen p q`.
subst₂-FlatGen-cancel
  : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os')
      {is'' os'' : List X} (p' : is'' ≡ is') (q' : os'' ≡ os')
      (z : FlatGen is os)
  → subst₂ FlatGen (trans p (sym p')) (trans q (sym q')) z
    ≡ subst₂ FlatGen (sym p') (sym q') (subst₂ FlatGen p q z)
subst₂-FlatGen-cancel refl refl refl refl z = refl

subst₂-FlatGen-cancel′
  : ∀ {is is' os os' : List X} (p : is ≡ is') (q : os ≡ os') (z : FlatGen is os)
  → subst₂ FlatGen (sym p) (sym q) (subst₂ FlatGen p q z) ≡ z
subst₂-FlatGen-cancel′ refl refl z = refl

-- `subst₂ HomTerm` only depends on the ENDPOINTS: under `objUIP` any two
-- boundary proofs with equal endpoints give the same transported term.
subst₂-HomTerm-irrel
  : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
    {A A' B B' : ObjTerm} (p p' : A ≡ A') (q q' : B ≡ B') (t : HomTerm A B)
  → subst₂ HomTerm p q t ≈Term subst₂ HomTerm p' q' t
subst₂-HomTerm-irrel objUIP p p' q q' t =
  ≡⇒≈Term (cong₂ (λ x y → subst₂ HomTerm x y t) (objUIP p p') (objUIP q q'))

subst₂-HomTerm-∘
  : ∀ {A A' A'' B B' B''}
      (p₁ : A ≡ A') (p₂ : A' ≡ A'') (q₁ : B ≡ B') (q₂ : B' ≡ B'') (t : HomTerm A B)
  → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ t)
    ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) t
subst₂-HomTerm-∘ refl refl refl refl t = refl

-- `subst₂ HomTerm` respects `≈Term` (GENERAL endpoints — see header).
subst₂-resp-≈Term
  : ∀ {A A' B B'} (p : A ≡ A') (q : B ≡ B') {u v : HomTerm A B}
  → u ≈Term v → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
subst₂-resp-≈Term refl refl u≈v = u≈v

subst₂-HomTerm-∘-dist
  : ∀ {A A' B B' C C'}
      (p : A ≡ A') (q : B ≡ B') (r : C ≡ C')
      (f : HomTerm B C) (h : HomTerm A B)
  → subst₂ HomTerm p r (f ∘ h)
    ≡ subst₂ HomTerm q r f ∘ subst₂ HomTerm p q h
subst₂-HomTerm-∘-dist refl refl refl f h = refl

-- `subst₂ HomTerm` of `a ⊗₁ b` over `⊗₀`-shaped endpoints distributes
-- over the two factors.
subst₂-⊗₁-dist
  : ∀ {A A' B B' C C' D D' : ObjTerm}
      (p₁ : A ≡ A') (q₁ : B ≡ B') (p₂ : C ≡ C') (q₂ : D ≡ D')
      (a : HomTerm A B) (b : HomTerm C D)
  → subst₂ HomTerm (cong₂ _⊗₀_ p₁ p₂) (cong₂ _⊗₀_ q₁ q₂) (a ⊗₁ b)
    ≡ subst₂ HomTerm p₁ q₁ a ⊗₁ subst₂ HomTerm p₂ q₂ b
subst₂-⊗₁-dist refl refl refl refl a b = refl

-- Whiskering by `_⊗₁ id {Z}` is functorial in the left factor: it carries
-- composition to composition.  Shared by the block/fire-mid interchange
-- consumers (`HomTerm`-generic; makes no use of `sig`).
⊗id-∘ : ∀ {A B D} {Z : ObjTerm} (h : HomTerm B D) (k : HomTerm A B)
      → (h ∘ k) ⊗₁ id {Z} ≈Term (h ⊗₁ id {Z}) ∘ (k ⊗₁ id {Z})
⊗id-∘ h k =
  ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

-- Three-factor form, built from `⊗id-∘`.
⊗id-∘∘ : ∀ {A B C D} {Z : ObjTerm}
           (h : HomTerm C D) (k : HomTerm B C) (l : HomTerm A B)
       → (h ∘ k ∘ l) ⊗₁ id {Z}
         ≈Term (h ⊗₁ id {Z}) ∘ (k ⊗₁ id {Z}) ∘ (l ⊗₁ id {Z})
⊗id-∘∘ h k l =
  ≈-Term-trans (⊗id-∘ h (k ∘ l)) (∘-resp-≈ ≈-Term-refl (⊗id-∘ k l))

------------------------------------------------------------------------
-- ## Box-shape `subst₂`/`pvl` transport algebra (shared across the
--    box-shape consumers).

-- `subst₂ HomTerm` distributes over `∘` (`cong unflatten`-framed endpoints).
subst₂-∘-distrib
  : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
      (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
      (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
      (h : HomTerm (unflatten As₁) (unflatten Bs₁))
  → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ h)
    ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
      ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) h
subst₂-∘-distrib refl refl refl _ _ = refl

-- `subst₂` on a `permute-via-vlab`, with block-frames of the form
-- `cong (map vlab) a`, pushes onto the underlying `↭`.
pvl-subst₂
  : ∀ {n} (vlab : Fin n → X) {xs xs' ys ys' : List (Fin n)}
      (a : xs ≡ xs') (b : ys ≡ ys') (r : xs Perm.↭ ys)
  → subst₂ HomTerm (cong unflatten (cong (map vlab) a))
                   (cong unflatten (cong (map vlab) b))
                   (permute-via-vlab vlab r)
    ≡ permute-via-vlab vlab (subst₂ Perm._↭_ a b r)
pvl-subst₂ vlab refl refl r = refl

-- `permute-via-vlab vlab ↭-refl ≈Term id` (definitional).
pvl-refl
  : ∀ {n} (vlab : Fin n → X) (xs : List (Fin n))
  → permute-via-vlab vlab (Perm.↭-refl {x = xs}) ≈Term id
pvl-refl vlab xs = ≈-Term-refl

-- A `subst₂` whose cod equation factors as `trans q r` splits into outer
-- `r` of inner `q`.
subst₂-cod-trans
  : ∀ {as as' bs bs' bs'' : List X}
      (p : as ≡ as') (q : bs ≡ bs') (r : bs' ≡ bs'')
      (x : HomTerm (unflatten as) (unflatten bs))
  → subst₂ HomTerm (cong unflatten p) (cong unflatten (trans q r)) x
    ≡ subst₂ HomTerm refl (cong unflatten r)
             (subst₂ HomTerm (cong unflatten p) (cong unflatten q) x)
subst₂-cod-trans refl refl refl x = refl

-- Symmetric: dom equation factoring as `trans q r`.
subst₂-dom-trans
  : ∀ {as as' as'' bs bs' : List X}
      (q : as ≡ as') (r : as' ≡ as'') (p : bs ≡ bs')
      (x : HomTerm (unflatten as) (unflatten bs))
  → subst₂ HomTerm (cong unflatten (trans q r)) (cong unflatten p) x
    ≡ subst₂ HomTerm (cong unflatten r) refl
             (subst₂ HomTerm (cong unflatten q) (cong unflatten p) x)
subst₂-dom-trans refl refl refl x = refl

-- `subst₂ HomTerm` over `cong unflatten` pushes inside `permute`.
permute-subst₂
  : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
      (r : xs Perm.↭ ys)
  → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
    ≡ permute (subst₂ Perm._↭_ p q r)
permute-subst₂ refl refl r = refl

-- `map⁺` commutes with a `subst₂`-transport of a permutation.
map⁺-subst₂
  : ∀ {a b} {A : Set a} {B : Set b} (h : A → B)
      {xs xs' ys ys' : List A} (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
  → PermProp.map⁺ h (subst₂ Perm._↭_ p q r)
    ≡ subst₂ Perm._↭_ (cong (map h) p) (cong (map h) q) (PermProp.map⁺ h r)
map⁺-subst₂ h refl refl r = refl

-- `eval-↭` of a `subst₂`-transported permutation is `subst₂ FinBij`
-- along the lengths.
eval-subst₂-↭
  : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
      (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
  → eval-↭ (subst₂ Perm._↭_ p q r)
    ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
eval-subst₂-↭ refl refl r = refl

------------------------------------------------------------------------
-- ## Permute relabel-freeness: for an injective label-preserving
--    embedding `φ : Fin nH → Fin nJ` with `vJ ∘ φ ≗ vH`, the `vJ`-permute
--    of the `φ`-relabel `map⁺ φ p` is the `vH`-permute of `p`, modulo the
--    boundary transport.  The `≈-fb` coincidence is PURE length-cast
--    bookkeeping (`eval-map⁺` reduces both sides to `eval-↭ p`, ignoring
--    labels); `permute-resp-≅↭` (K) turns it into `≈Term`.
vlab-φ-lemma
  : ∀ {nH nJ : ℕ} (φ : Fin nH → Fin nJ) (vJ : Fin nJ → X) (vH : Fin nH → X)
      (veq : ∀ i → vJ (φ i) ≡ vH i) (s : List (Fin nH))
  → map vJ (map φ s) ≡ map vH s
vlab-φ-lemma φ vJ vH veq s = trans (sym (map-∘ s)) (map-cong veq s)

pvv-relabel
  : (Kf : FaithfulnessResidual)
    {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
    (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
    {xs ys : List (Fin nH)} (p : xs Perm.↭ ys)
  → subst₂ HomTerm
      (cong unflatten (vlab-φ-lemma φ vJ vH veq xs))
      (cong unflatten (vlab-φ-lemma φ vJ vH veq ys))
      (permute-via-vlab vJ (PermProp.map⁺ φ p))
    ≈Term permute-via-vlab vH p
pvv-relabel Kf φ vJ vH veq {xs} {ys} p =
  ≈-Term-trans
    (≡⇒≈Term
      (permute-subst₂ (vlab-φ-lemma φ vJ vH veq xs)
                      (vlab-φ-lemma φ vJ vH veq ys)
                      (PermProp.map⁺ vJ (PermProp.map⁺ φ p))))
    (FaithfulnessResidual.permute-resp-≅↭ Kf
      (subst₂ Perm._↭_ (vlab-φ-lemma φ vJ vH veq xs)
                        (vlab-φ-lemma φ vJ vH veq ys)
                        (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
      (PermProp.map⁺ vH p)
      coincide)
  where
    px = vlab-φ-lemma φ vJ vH veq xs
    py = vlab-φ-lemma φ vJ vH veq ys

    coincide
      : eval-↭ (subst₂ Perm._↭_ px py (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
      ≈-fb eval-↭ (PermProp.map⁺ vH p)
    coincide =
      ≈-fb-of-≡
        (trans (eval-subst₂-↭ px py (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
        (trans (cong (subst₂ FinBij (cong length px) (cong length py))
                     (trans (eval-map⁺ vJ (PermProp.map⁺ φ p))
                            (cong (subst₂ FinBij
                                     (sym (length-map vJ (map φ xs)))
                                     (sym (length-map vJ (map φ ys))))
                                  (eval-map⁺ φ p))))
        (trans (cong (subst₂ FinBij (cong length px) (cong length py))
                     (subst₂-FinBij-∘
                        (sym (length-map φ xs)) (sym (length-map vJ (map φ xs)))
                        (sym (length-map φ ys)) (sym (length-map vJ (map φ ys)))
                        (eval-↭ p)))
        (trans (subst₂-FinBij-∘
                  (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                  (cong length px)
                  (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                  (cong length py)
                  (eval-↭ p))
        (trans (cast-irrel
                  (trans (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                         (cong length px))
                  (sym (length-map vH xs))
                  (trans (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                         (cong length py))
                  (sym (length-map vH ys))
                  (eval-↭ p))
               (sym (eval-map⁺ vH p)))))))

--------------------------------------------------------------------------------
-- ## `Linear H ⇒ Unique (cod H)` (sig-level).
--
-- `count v cod ≤ count v consumedList = count v producedList ≤ 1`, by
-- `count-++`-monotonicity, the balance half, and the bound half.

open import Data.Nat.Base using () renaming (_≤_ to _≤ⁿ_)
import Data.Nat.Properties as Nat
open import Data.List using (concat; tabulate)

Linear⇒cod-Unique : (H : Hypergraph FlatGen) → Lin.Linear H → Unique (Hypergraph.cod H)
Linear⇒cod-Unique H (bal , bnd) = SU.count≤1⇒Unique cod-bnd
  where
    module H = Hypergraph H
    cod-bnd : ∀ v → Lin.count v H.cod ≤ⁿ 1
    cod-bnd v =
      Nat.≤-trans
        (Nat.≤-trans
          (Nat.m≤m+n (Lin.count v H.cod) (Lin.count v (concat (tabulate H.ein))))
          (Nat.≤-reflexive (sym (Lin.count-++ v H.cod (concat (tabulate H.ein))))))
        (Nat.≤-trans (Nat.≤-reflexive (sym (bal v))) (bnd v))

--------------------------------------------------------------------------------
-- ## Algorithm extraction (sig-level).  From a successful `decode-attempt
-- H`, expose the returned term as `permute-via-vlab vlab perm ∘
-- process-term` for the SAME `process-term` and the `perm : s_final ↭ cod`
-- that `extract-exact` computed.  `Valid`-free.

decode-attempt-extract
  : (H : Hypergraph FlatGen)
    (t : HomTerm (unflatten (domL H)) (unflatten (codL H)))
  → decode-attempt H ≡ just t
  → Σ[ perm ∈ proj₁ (process-all-edges H (Hypergraph.dom H)) Perm.↭ Hypergraph.cod H ]
      t ≡ permute-via-vlab (Hypergraph.vlab H) perm
            ∘ proj₂ (process-all-edges H (Hypergraph.dom H))
decode-attempt-extract H t eq
    with process-all-edges H (Hypergraph.dom H)
... | s_final , process-term
    with extract-exact (Hypergraph.cod H) s_final
...    | just perm with eq
...       | refl = perm , refl
decode-attempt-extract H t eq
    | s_final , process-term | nothing with eq
... | ()

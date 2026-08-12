{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

--------------------------------------------------------------------------------
-- MERKLE–DAMGÅRD as a secure realization of a random oracle.
--
-- Reusing `Examples.RandomOracle` (generalised to `RandomOracle p inN outN`),
-- we show that `MerkleDamgard` realises  `RandomOracle p (k * n) n`  from
-- `RandomOracle p (2 * n) n`  (the compression oracle: 2n-bit input, n-bit
-- output).  Both functionalities are `RandomOracle.Functionality` *lifted into*
-- `PMachine` by `liftFun`, which mirrors the G-construction `F : 𝒞 → 𝒢(𝒞)`
-- (`CategoricalCrypto.Machine.Core`'s `Machine I C`: a functionality is a machine
-- with empty subroutine domain).
--
-- MD is a `PMachine` that interacts with the compression machine **once per
-- block**, threading the chaining value (the machine-level `foldl`).
--
-- The security claim is the *output-only* statement "`MD ⊚ Comp.M` is a random
-- oracle", phrased the standard cryptographic way: against ANY adaptive
-- distinguisher `d` issuing `≤ n` queries, the distinguishing advantage is `≤ bound n`
-- (concrete security — the bound is a function of the query count, since more queries
-- genuinely help).  `≈ℰ`, the advantage and the distinguisher are all *defined* via a
-- reactive interaction model (`Dgr`/`run`/`adv`); the bridge is the Fundamental Lemma
-- of Game-Playing (`FLGP`), adaptive-robust by construction.  Assembly:
--
--   adv ⟦General.M⟧ ⟦MD⊚Comp.M⟧ d
--     = ∣ Pr₁(runWith C.idealK s₀ d) − Pr₁(runWith C.realK s₀ d) ∣
--                                   (semantics laws + ideal-marginal + ghost-erase)
--     ≤ Pr[the coupling's bad flag fires]     (coupled FLGP, adaptive-robust)
--     ≤ bound n.                              (adaptive birthday)
--
-- The game-playing AND ideal-side layers are PROVEN here:
--   • `Coupling.FLGP` — the Fundamental Lemma of Game-Playing in COUPLED form (one
--     kernel emits the shared state and BOTH answers; the ideal projection copies
--     the real answer while the POST-state is good).  It holds for ANY coupled
--     kernel, with no side conditions, by induction on the distinguisher.
--   • `ideal-marginal` — ★ the coupling's ideal view IS the variable-length RO,
--     EXACTLY (the ε lives only in FLGP/bad-bound).  The coupling raises an
--     explicit flag whenever the MD answer fails to be a fresh uniform (final-call
--     lookup hit for a new message / inconsistent replay), which makes the proof a
--     direct bisimulation over the distinguisher with NO combinatorial invariants:
--     repeats are answered consistently by the flag's own check (`pointRep`), and
--     at an unflagged final call the fresh sample detaches as ONE uniform draw
--     (`detach`).  All chain-forest combinatorics moves into `bad-bound`.
--   • `ghost-erase` — flag + ghost table are invisible to the real world, whose
--     kernel marginalises back to plain MD chaining (`walkR`).
-- The only probabilistic assumption these rest on is expectation MONOTONICITY
-- (`E-mono`), assumed because the `Dist-ℚ` library tracks mass = 1 but not
-- non-negativity of weights; linearity, boundedness of `Pr₁`, and the expectation
-- triangle inequality are derived from it.
--
-- The `bad-bound` side is reduced to a NON-adaptive per-step certificate:
--   • `badProb-super` (PROVEN) — the supermartingale bound: an invariant `Inv`
--     preserved on support plus a potential `φ` that dominates 1 on bad states
--     and never increases in expectation per query bounds the bad-probability of
--     ANY adaptive distinguisher by the initial potential.  This carries the
--     whole adaptivity argument; `bad-bound` is PROVEN from `md-cert`,
--     which is itself ASSEMBLED (not assumed) below.
--
-- The certificate's PROBABILISTIC side is PROVEN (design: docs/md-cert-design.md):
-- the potential φ = collision count + triangle budget is an EXACT martingale
-- along the walk (`walk-φ`: an interior miss creates `pool` expected collision
-- pairs — the PROVEN `E-collisions` — and spends exactly that from the budget;
-- final calls and hits are free), giving `φ-step`, `φ-nn`, `φ-init` with no
-- invariant and no support reasoning.
--
-- ★★ THE ENTIRE CRYPTOGRAPHIC CONTENT IS PROVEN. ★★  There is NO crypto-specific
-- assumption left.  The chain-forest invariant `MDInv` and its preservation are proven
-- on every branch: flagged (`flagged-step`), unflagged REPEAT (`mdInv-good-repeat` via
-- `walk-replay`), and unflagged NEW — UniqueKeys/Rooted/RecChains (`walk-supp` +
-- `rec-extend`), OwnedLast (`walk-owned` via the final-key tracker `walk-fk`), and the
-- birthday DESCENT `walk-hit-collC` (`1 ≤ collC` when a fresh message's final call hits:
-- co-determinism from `collC ≡ 0` via a δ-sum counting lemma, `unique-run` on the shared
-- prefix, `toBlocks`-injectivity ⇒ the message was already recorded, ⊥).  Together with
-- `MDInv₀`, `flag⇒coll`, the collision-count-monotonicity backbone, `md-cert`,
-- `badProb-super`, FLGP, `ideal-marginal`, and `ghost-erase` — all proven — the theorem
-- `indistinguishable` rests solely on the framework + standard-math assumptions of
-- the module parameter `MDAssumptions` (documented field by field where it is
-- declared, in `MerkleDamgard.Base`): the 𝒢-construction primitives, the trace over
-- the shared interface and its two laws, `≈ᵉ⇒run`, and expectation monotonicity on
-- the support.  `⟦General⟧-sem`, `⟦MD⟧-sem`, the per-machine computation fact
-- `∘ᵍ-MD` and global monotonicity `E-mono` are all DERIVED from them — no
-- machine-specific assumption remains, and this module is `--safe`.
--
-- Warm single-module typecheck: ~535 s (measured 2026-08-12, `+RTS -M10G -H2G`;
-- was ~510 s before the `MDAssumptions` parametrization).
--------------------------------------------------------------------------------

open import CategoricalCrypto.Examples.MerkleDamgard.Base

module CategoricalCrypto.Examples.MerkleDamgard (mdAssumptions : MDAssumptions) where

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_; Stable)
open import Data.Nat using (_+_; _*_; _≤_; _<_; _∸_; NonZero; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (_<?_)
import Data.Nat.Properties as ℕP
open import Data.Fin using (Fin; zero)
open import Data.Vec using (Vec; []; _∷_; cast; toList) renaming (_++_ to _++ᵛ_; take to takeᵛ; drop to dropᵛ; replicate to replicateᵛ)
import Data.Vec as DV
open import Data.List using (_++_; foldl; length)
import Data.List as L
open import Data.List.Properties using (∷-injective; length-++)
import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; nonNegative)
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_; _≟_ to _≟ℚ_)
open import Data.Rational.Properties using
  ( ≤-trans; ≤-refl; ≤-reflexive; ≤-total; neg-antimono-≤; +-monoʳ-≤; +-monoˡ-≤
  ; +-mono-≤; *-identityˡ; *-zeroˡ; *-zeroʳ; *-distribʳ-+
  ; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg
  ; +-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; neg-distrib-+
  ; 0≤∣p∣; 0≤p⇒∣p∣≡p; ∣-p∣≡∣p∣; ≤-antisym; 1≢0 )
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as ListAll
open import Data.List.Run
open import Data.Vec.Properties.Ext using (take-drop-inj)
open import CategoricalCrypto.Channel.Core using (Channel; _⇿_; I; _⊗₀_)
open import CategoricalCrypto.SFunM
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2; bool→ℚ; fromℕ; δ; P-uniform-Vec)
open import CategoricalCrypto.Examples.RandomOracle
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as RS

open MDAssumptions mdAssumptions

-- Closed semantics: a machine with no subroutine (input channel `I = ⊥ ⇿ ⊥`) has a
-- plain kernel `outType C → inType C` — the empty `⊥` interface is dropped.
⟦_⟧cl : ∀ {C : Channel} → PMachine I C → SFun⊥ (Channel.outType C) (Channel.inType C)
⟦ m ⟧cl = strip⊥ ⟦ m ⟧

-- Setoid reasoning for `_≈Mℚ_` (its relation mentions only `entries`, so an
-- inferred intermediate distribution would leave `mass-1` a stray meta; the
-- reasoning chains below always name their intermediates, so stay meta-free).
private
  Mℚ-setoid : (A : Type) → Setoid _ _
  Mℚ-setoid A = record { Carrier = Dist-ℚ A ; _≈_ = _≈Mℚ_ ; isEquivalence = ≈Mℚ-isEquivalence }

  module Mℚ {A : Type} = Setoid (Mℚ-setoid A)

--------------------------------------------------------------------------------
-- Bridging lemmas: the `SFun⊥` run relates to the total `Dist-ℚ` run by the
-- `Dmap just` embedding, and `strip⊥`/`embed⊥` commute up to `_≈ᵉ_`.
--------------------------------------------------------------------------------

-- Reflexive-subject / reflexive-continuation bind congruences with the reflexive
-- side PINNED explicitly.  Inside a setoid-reasoning chain the "to" endpoint is a
-- metavariable while the proof is checked, so a bare `(λ P → refl)` under an
-- inferred `{μ}`/`{f}` makes Agda try to solve the distribution meta by inverting
-- `_+ℚ_` — a catastrophic heap blow-up.  Pinning the reflexive side avoids it.
>>=⊥-congˡ : {A B : Type} (μ : Dist⊥ A) (f g : A → Dist⊥ B)
           → (∀ a → f a ≈Mℚ g a) → (μ >>=⊥ f) ≈Mℚ (μ >>=⊥ g)
>>=⊥-congˡ μ f g pt = >>=⊥-cong {μ = μ} {μ} {f} {g} (λ P → refl) pt

>>=⊥-congʳ : {A B : Type} (f : A → Dist⊥ B) (μ ν : Dist⊥ A)
           → μ ≈Mℚ ν → (μ >>=⊥ f) ≈Mℚ (ν >>=⊥ f)
>>=⊥-congʳ f μ ν μ≈ν = >>=⊥-cong {μ = μ} {ν} {f} {f} μ≈ν (λ a → Mℚ.refl {x = f a})

>>=ᴹ-congˡ : {A B : Type} (μ : Dist-ℚ A) (f g : A → Dist-ℚ B)
           → (∀ a → f a ≈Mℚ g a) → (μ >>=ᴹ f) ≈Mℚ (μ >>=ᴹ g)
>>=ᴹ-congˡ μ f g pt = >>=ᴹ-cong {μ = μ} {μ} {f} {g} (λ P → refl) pt

run⊥-embed-gen : {Q R St : Type} (resp : St → Q → Dist-ℚ (St × R)) (s : St) (d : Dgr Q R)
               → runWith⊥ (λ s q → Dmap just (resp s q)) s d ≈Mℚ Dmap just (runWith resp s d)
run⊥-embed-gen resp s (out b) = begin
  return⊥ b                                  ≈˘⟨ >>=ᴹ-identityˡ b (return-ℚ ∘ just) ⟩
  Dmap just (return-ℚ b)                      ∎
  where open RS (Mℚ-setoid _)
run⊥-embed-gen resp s (ask q k) = begin
  (Dmap just (resp s q) >>=⊥ K⊥)
    ≈⟨ >>=⊥-embed (resp s q) K⊥ ⟩
  (resp s q >>=ᴹ K⊥)
    ≈⟨ >>=ᴹ-cong {μ = resp s q} {resp s q} {K⊥} {λ sr → Dmap just (G sr)}
         (λ P → refl) (λ sr → run⊥-embed-gen resp (proj₁ sr) (k (proj₂ sr))) ⟩
  (resp s q >>=ᴹ (λ sr → Dmap just (G sr)))
    ≈˘⟨ >>=ᴹ-assoc (resp s q) G (return-ℚ ∘ just) ⟩
  Dmap just (resp s q >>=ᴹ G)
    ∎
  where
    G  = λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))
    K⊥ = λ sr → runWith⊥ (λ s q → Dmap just (resp s q)) (proj₁ sr) (k (proj₂ sr))
    open RS (Mℚ-setoid _)

run⊥-embed : {Q R : Type} (h : SFunᵉ {M = Dist-ℚ} Q R) (d : Dgr Q R)
           → run⊥ (embed⊥ h) d ≈Mℚ Dmap just (run h d)
run⊥-embed h d = run⊥-embed-gen (λ s q → SFunᵉ.fun h (s , q)) (SFunᵉ.init h) d

-- `trace` congruence at `Dist⊥`: pointwise-equal kernels give equal traces.
trace-cong⊥ : {A B St : Type} {f g : St × A → Dist⊥ (St × B)}
            → (∀ sa → f sa ≈Mℚ g sa)
            → (s : St) (xs : List A)
            → trace {M = Dist⊥} f s xs ≈Mℚ trace {M = Dist⊥} g s xs
trace-cong⊥ f≈g s []       = λ P → refl
trace-cong⊥ {f = f} {g} f≈g s (a ∷ as) =
  >>=⊥-cong {μ = f (s , a)} {g (s , a)}
    {λ sb → trace {M = Dist⊥} f (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))}
    {λ sb → trace {M = Dist⊥} g (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))}
    (f≈g (s , a))
    (λ sb → >>=⊥-congʳ (λ bs → return⊥ (proj₂ sb ∷ bs))
              (trace {M = Dist⊥} f (proj₁ sb) as) (trace {M = Dist⊥} g (proj₁ sb) as)
              (trace-cong⊥ f≈g (proj₁ sb) as))

-- `embed⊥` of a stripped total functionality equals the `strip⊥` of its embedding.
strip-embed-swap : {A B : Type} (h : SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B))
                 → (_≈ᵉ_ {M = Dist⊥}) (strip⊥ (embed⊥ h)) (embed⊥ (stripᵉ h))
strip-embed-swap h = trace-cong⊥ kern (SFunᵉ.init h)
  where
    kern : ∀ sa → SFunᵉ.fun (strip⊥ (embed⊥ h)) sa ≈Mℚ SFunᵉ.fun (embed⊥ (stripᵉ h)) sa
    kern sa = begin
      SFunᵉ.fun (strip⊥ (embed⊥ h)) sa
        ≈⟨ >>=⊥-embed (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
                      (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))) ⟩
      (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)) >>=ᴹ (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))))
        ≈˘⟨ >>=ᴹ-congˡ (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
              (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr)))
              (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ (return-ℚ ∘ just))
              (λ sr → >>=ᴹ-identityˡ (proj₁ sr , unbot (proj₂ sr)) (return-ℚ ∘ just)) ⟩
      (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)) >>=ᴹ
        (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ (return-ℚ ∘ just)))
        ≈˘⟨ >>=ᴹ-assoc (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
              (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr))) (return-ℚ ∘ just) ⟩
      SFunᵉ.fun (embed⊥ (stripᵉ h)) sa
        ∎
      where open RS (Mℚ-setoid _)

-- Trace commutes with a per-step input relabelling.
trace-mapin : {A A' B St : Type} (g : A → A') (k : St × A' → Dist⊥ (St × B))
              (s : St) (xs : List A)
            → trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) s xs
              ≈Mℚ trace {M = Dist⊥} k s (L.map g xs)
trace-mapin g k s []       = λ P → refl
trace-mapin g k s (a ∷ as) =
  >>=⊥-congˡ (k (s , g a))
    (λ sb → trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs)))
    (λ sb → trace {M = Dist⊥} k (proj₁ sb) (L.map g as) >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs)))
    (λ sb → >>=⊥-congʳ (λ bs → return⊥ (proj₂ sb ∷ bs))
              (trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) (proj₁ sb) as)
              (trace {M = Dist⊥} k (proj₁ sb) (L.map g as))
              (trace-mapin g k (proj₁ sb) as))

-- Trace commutes with a per-step output relabelling (pushed to the end).
trace-mapout : {A B B' St : Type} (φ : B → B') (k : St × A → Dist⊥ (St × B))
               (s : St) (xs : List A)
             → trace {M = Dist⊥} (λ sa → k sa >>=⊥ (λ sr → return⊥ (proj₁ sr , φ (proj₂ sr)))) s xs
               ≈Mℚ (trace {M = Dist⊥} k s xs >>=⊥ (λ ys → return⊥ (L.map φ ys)))
trace-mapout φ k s [] = begin
  return⊥ []                    ≈˘⟨ >>=⊥-identityˡ [] post ⟩
  (return⊥ [] >>=⊥ post)        ∎
  where post = λ ys → return⊥ (L.map φ ys)
        open RS (Mℚ-setoid _)
trace-mapout φ k s (a ∷ as) = begin
  ((K >>=⊥ wret) >>=⊥ ContMO)
    ≈⟨ >>=⊥-assoc K wret ContMO ⟩
  (K >>=⊥ (λ sr → wret sr >>=⊥ ContMO))
    ≈⟨ >>=⊥-congˡ K (λ sr → wret sr >>=⊥ ContMO) (λ sr → ContMO (proj₁ sr , φ (proj₂ sr)))
         (λ sr → >>=⊥-identityˡ (proj₁ sr , φ (proj₂ sr)) ContMO) ⟩
  (K >>=⊥ (λ sr → ContMO (proj₁ sr , φ (proj₂ sr))))
    ≈⟨ >>=⊥-congˡ K (λ sr → ContMO (proj₁ sr , φ (proj₂ sr)))
         (λ sr → (Tk (proj₁ sr) >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
         (λ sr → >>=⊥-congʳ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))
                   (Tm (proj₁ sr)) (Tk (proj₁ sr) >>=⊥ post)
                   (trace-mapout φ k (proj₁ sr) as)) ⟩
  (K >>=⊥ (λ sr → (trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
    ≈⟨ >>=⊥-congˡ K
         (λ sr → (Tk (proj₁ sr) >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
         (λ sr → >>=⊥-assoc (Tk (proj₁ sr)) post (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))) ⟩
  (K >>=⊥ (λ sr → trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))))
    ≈⟨ >>=⊥-congˡ K
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys)))
         (λ sr → >>=⊥-congˡ (Tk (proj₁ sr))
                   (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
                   (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys))
                   (λ ys → >>=⊥-identityˡ (L.map φ ys) (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))) ⟩
  (K >>=⊥ (λ sr → trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys))))
    ≈˘⟨ >>=⊥-congˡ K
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post))
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (φ (proj₂ sb) ∷ L.map φ ys)))
          (λ sb → >>=⊥-congˡ (Tk (proj₁ sb))
                    (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post)
                    (λ ys → return⊥ (φ (proj₂ sb) ∷ L.map φ ys))
                    (λ ys → >>=⊥-identityˡ (proj₂ sb ∷ ys) post)) ⟩
  (K >>=⊥ (λ sb → trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post)))
    ≈˘⟨ >>=⊥-congˡ K
          (λ sb → Gk sb >>=⊥ post)
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post))
          (λ sb → >>=⊥-assoc (Tk (proj₁ sb)) (λ bs → return⊥ (proj₂ sb ∷ bs)) post) ⟩
  (K >>=⊥ (λ sb → (trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))) >>=⊥ post))
    ≈˘⟨ >>=⊥-assoc K Gk post ⟩
  ((K >>=⊥ Gk) >>=⊥ post)
    ∎
  where
    post   = λ ys → return⊥ (L.map φ ys)
    K      = k (s , a)
    wret   = λ sr → return⊥ (proj₁ sr , φ (proj₂ sr))
    Tm     = λ st → trace {M = Dist⊥} (λ sa → k sa >>=⊥ (λ sr → return⊥ (proj₁ sr , φ (proj₂ sr)))) st as
    Tk     = λ st → trace {M = Dist⊥} k st as
    ContMO = λ sb → Tm (proj₁ sb) >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
    Gk     = λ sb → trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
    open RS (Mℚ-setoid _)

-- `strip⊥` unfolds to running on `inj₂`-wrapped inputs and `unbot`-ing outputs.
strip-eval : {A B : Type} (f : SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B)) (s : SFunᵉ.State f) (xs : List A)
           → trace {M = Dist⊥} (SFunᵉ.fun (strip⊥ f)) s xs
             ≈Mℚ (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
strip-eval f s xs = begin
  trace {M = Dist⊥} (SFunᵉ.fun (strip⊥ f)) s xs
    ≈⟨ trace-mapout unbot (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs ⟩
  (trace {M = Dist⊥} (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈⟨ >>=⊥-congʳ (λ ys → return⊥ (L.map unbot ys))
         (trace {M = Dist⊥} (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs)
         (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs))
         (trace-mapin inj₂ (SFunᵉ.fun f) s xs) ⟩
  (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ∎
  where open RS (Mℚ-setoid _)

-- `strip⊥` respects `_≈ᵉ_`.
strip⊥-cong : {A B : Type} {f g : SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B)}
            → (_≈ᵉ_ {M = Dist⊥}) f g → (_≈ᵉ_ {M = Dist⊥}) (strip⊥ f) (strip⊥ g)
strip⊥-cong {f = f} {g} f≈g xs = begin
  eval (strip⊥ f) xs
    ≈⟨ strip-eval f (SFunᵉ.init f) xs ⟩
  (eval f (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈⟨ >>=⊥-congʳ (λ ys → return⊥ (L.map unbot ys))
         (eval f (L.map inj₂ xs)) (eval g (L.map inj₂ xs))
         (f≈g (L.map inj₂ xs)) ⟩
  (eval g (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈˘⟨ strip-eval g (SFunᵉ.init g) xs ⟩
  eval (strip⊥ g) xs
    ∎
  where open RS (Mℚ-setoid _)

--------------------------------------------------------------------------------
-- Expectation facts.  Only MONOTONICITY is assumed (`MDAssumptions.E-mono-on`);
-- linearity / boundedness / the expectation triangle inequality are then derived
-- in terms of it.
--------------------------------------------------------------------------------

private
  all-univ : ∀ {A : Type} {P : A → Type} → (∀ x → P x)
           → (xs : List A) → ListAll.All P xs
  all-univ pt []       = ListAll.[]
  all-univ pt (x ∷ xs) = pt x ListAll.∷ all-univ pt xs

-- global expectation monotonicity, DERIVED from the support-level fact
E-mono : ∀ {A : Type} (μ : Dist-ℚ A) (f g : A → ℚ)
       → (∀ a → f a ≤ℚ g a) → E μ f ≤ℚ E μ g
E-mono μ f g pt =
  E-mono-on μ f g (all-univ (λ e → pt (proj₂ e)) (NE.toList (entries μ)))

private
  -- ℚ cancellation facts (the ring solver is semiring-only, so prove these by hand).
  +-−-cancel : ∀ X d → (X +ℚ d) -ℚ d ≡ X
  +-−-cancel X d = trans (+-assoc X d (-ℚ d))
                         (trans (cong (X +ℚ_) (+-inverseʳ d)) (+-identityʳ X))

  −-+-cancel : ∀ X d → (X -ℚ d) +ℚ d ≡ X
  −-+-cancel X d = trans (+-assoc X (-ℚ d) d)
                         (trans (cong (X +ℚ_) (+-inverseˡ d)) (+-identityʳ X))

  neg-neg : ∀ y → -ℚ (-ℚ y) ≡ y
  neg-neg y = trans (sym (+-identityʳ (-ℚ (-ℚ y))))
              (trans (cong ((-ℚ (-ℚ y)) +ℚ_) (sym (+-inverseˡ y)))
              (trans (sym (+-assoc (-ℚ (-ℚ y)) (-ℚ y) y))
              (trans (cong (_+ℚ y) (+-inverseˡ (-ℚ y))) (+-identityˡ y))))

  neg-sub : ∀ x y → y -ℚ x ≡ -ℚ (x -ℚ y)
  neg-sub x y = sym (trans (neg-distrib-+ x (-ℚ y))
                           (trans (cong ((-ℚ x) +ℚ_) (neg-neg y)) (+-comm (-ℚ x) y)))

  -- additivity and constants
  E-add : ∀ {A : Type} (μ : Dist-ℚ A) (f g : A → ℚ)
        → E μ (λ a → f a +ℚ g a) ≡ E μ f +ℚ E μ g
  E-add μ = lookupᴰℚ-+ (entries μ)

  E-const : ∀ {A : Type} (μ : Dist-ℚ A) (c : ℚ) → E μ (λ _ → c) ≡ c
  E-const μ c = trans (mass-as-const (entries μ) c)
                      (trans (cong (_*ℚ c) (mass-1 μ)) (*-identityˡ c))

  -- E of a difference is the difference of E's
  E-sub : ∀ {A : Type} (μ : Dist-ℚ A) (a b : A → ℚ)
        → E μ (λ x → a x -ℚ b x) ≡ E μ a -ℚ E μ b
  E-sub μ a b = trans (sym (+-−-cancel (E μ (λ x → a x -ℚ b x)) (E μ b)))
                      (cong (_-ℚ E μ b) eq)
    where eq : E μ (λ x → a x -ℚ b x) +ℚ E μ b ≡ E μ a
          eq = trans (sym (E-add μ (λ x → a x -ℚ b x) b))
                     (lookupᴰℚ-cong-P (entries μ) (λ x → −-+-cancel (a x) (b x)))

  -- `E` and `Pr₁` commute with bind, and `Pr₁` is a genuine probability in [0,1]
  E-bind : ∀ {A B : Type} (μ : Dist-ℚ A) (h : A → Dist-ℚ B) (P : B → ℚ)
         → E (μ >>=ᴹ h) P ≡ E μ (λ a → E (h a) P)
  E-bind μ h P = lookupᴰℚ-bind (entries μ) (λ a → entries (h a)) P

  Pr₁-bind : ∀ {A : Type} (μ : Dist-ℚ A) (k : A → Dist-ℚ Bool)
           → Pr₁ (μ >>=ᴹ k) ≡ E μ (λ a → Pr₁ (k a))
  Pr₁-bind μ k = lookupᴰℚ-bind (entries μ) (λ a → entries (k a)) bool→ℚ

  0≤1ℚ : 0ℚ ≤ℚ 1ℚ
  0≤1ℚ = 0≤∣p∣ 1ℚ

  Pr₁≤1 : ∀ (μ : Dist-ℚ Bool) → Pr₁ μ ≤ℚ 1ℚ
  Pr₁≤1 μ = ≤-trans (E-mono μ bool→ℚ (λ _ → 1ℚ) b≤1) (≤-reflexive (E-const μ 1ℚ))
    where b≤1 : ∀ b → bool→ℚ b ≤ℚ 1ℚ
          b≤1 true  = ≤-refl
          b≤1 false = 0≤1ℚ

  Pr₁≥0 : ∀ (μ : Dist-ℚ Bool) → 0ℚ ≤ℚ Pr₁ μ
  Pr₁≥0 μ = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ)))
                    (E-mono μ (λ _ → 0ℚ) bool→ℚ 0≤b)
    where 0≤b : ∀ b → 0ℚ ≤ℚ bool→ℚ b
          0≤b true  = 0≤1ℚ
          0≤b false = ≤-refl

  -- ∣x∣ ≤ c  from  x ≤ c  and  -x ≤ c
  ∣∣≤ : ∀ {x c : ℚ} → x ≤ℚ c → (-ℚ x) ≤ℚ c → ∣ x ∣ℚ ≤ℚ c
  ∣∣≤ {x} {c} x≤c -x≤c with ≤-total 0ℚ x
  ... | inj₁ 0≤x = subst (_≤ℚ c) (sym (0≤p⇒∣p∣≡p 0≤x)) x≤c
  ... | inj₂ x≤0 = subst (_≤ℚ c) (sym ∣x∣≡-x) -x≤c
    where ∣x∣≡-x : ∣ x ∣ℚ ≡ -ℚ x
          ∣x∣≡-x = trans (sym (∣-p∣≡∣p∣ x)) (0≤p⇒∣p∣≡p (neg-antimono-≤ x≤0))

  -- p ≤ ∣p∣
  p≤∣p∣ : ∀ p → p ≤ℚ ∣ p ∣ℚ
  p≤∣p∣ p with ≤-total 0ℚ p
  ... | inj₁ 0≤p = ≤-reflexive (sym (0≤p⇒∣p∣≡p 0≤p))
  ... | inj₂ p≤0 = ≤-trans p≤0 (0≤∣p∣ p)

  -- expectation triangle inequality:  ∣E a − E b∣ ≤ E ∣a − b∣
  E-abs-diff : ∀ {A : Type} (μ : Dist-ℚ A) (a b : A → ℚ)
             → ∣ E μ a -ℚ E μ b ∣ℚ ≤ℚ E μ (λ x → ∣ a x -ℚ b x ∣ℚ)
  E-abs-diff μ a b = ∣∣≤ upper lower
    where
      H = λ x → ∣ a x -ℚ b x ∣ℚ
      upper : (E μ a -ℚ E μ b) ≤ℚ E μ H
      upper = subst (_≤ℚ E μ H) (E-sub μ a b)
                    (E-mono μ (λ x → a x -ℚ b x) H (λ x → p≤∣p∣ (a x -ℚ b x)))
      lower : (-ℚ (E μ a -ℚ E μ b)) ≤ℚ E μ H
      lower = subst (_≤ℚ E μ H) negEq
                    (E-mono μ (λ x → b x -ℚ a x) H bnd)
        where
          negEq : E μ (λ x → b x -ℚ a x) ≡ -ℚ (E μ a -ℚ E μ b)
          negEq = trans (E-sub μ b a) (neg-sub (E μ a) (E μ b))
          bnd : ∀ x → (b x -ℚ a x) ≤ℚ H x
          bnd x = subst ((b x -ℚ a x) ≤ℚ_) absEq (p≤∣p∣ (b x -ℚ a x))
            where absEq : ∣ b x -ℚ a x ∣ℚ ≡ H x
                  absEq = trans (cong ∣_∣ℚ (neg-sub (a x) (b x))) (∣-p∣≡∣p∣ (a x -ℚ b x))

  -- small ℚ / probability facts for the FLGP induction
  0≤bool : ∀ b → 0ℚ ≤ℚ bool→ℚ b
  0≤bool true  = 0≤1ℚ
  0≤bool false = ≤-refl

  neg≤0 : ∀ {y} → 0ℚ ≤ℚ y → (-ℚ y) ≤ℚ 0ℚ
  neg≤0 0≤y = neg-antimono-≤ 0≤y

  x-y≤x : ∀ x {y} → 0ℚ ≤ℚ y → (x -ℚ y) ≤ℚ x
  x-y≤x x 0≤y = ≤-trans (+-monoʳ-≤ x (neg≤0 0≤y)) (≤-reflexive (+-identityʳ x))

  ∣diff∣≤1 : ∀ {a b} → 0ℚ ≤ℚ a → a ≤ℚ 1ℚ → 0ℚ ≤ℚ b → b ≤ℚ 1ℚ → ∣ a -ℚ b ∣ℚ ≤ℚ 1ℚ
  ∣diff∣≤1 {a} {b} 0≤a a≤1 0≤b b≤1 =
    ∣∣≤ (≤-trans (x-y≤x a 0≤b) a≤1)
        (subst (_≤ℚ 1ℚ) (neg-sub a b) (≤-trans (x-y≤x b 0≤a) b≤1))

  ∣Pr-Pr∣≤1 : ∀ (μ ν : Dist-ℚ Bool) → ∣ Pr₁ μ -ℚ Pr₁ ν ∣ℚ ≤ℚ 1ℚ
  ∣Pr-Pr∣≤1 μ ν = ∣diff∣≤1 (Pr₁≥0 μ) (Pr₁≤1 μ) (Pr₁≥0 ν) (Pr₁≤1 ν)

-- any distinguisher issuing ≤ n queries has advantage ≤ ε n
_≈ℰ[_]_ : ∀ {C : Channel} → PMachine I C → (ℕ → ℚ) → PMachine I C → Type
f ≈ℰ[ ε ] g = ∀ n d → asks≤ n d → adv ⟦ f ⟧cl ⟦ g ⟧cl d ≤ℚ ε n

-- Case combinator (the prelude hides `if_then_else_`).
cond : {A : Type} → Bool → A → A → A
cond true  x _ = x
cond false _ y = y

cond-diag : {A : Type} (b : Bool) (x : A) → cond b x x ≡ x
cond-diag true  x = refl
cond-diag false x = refl

-- At a state where `bad` already holds, the bad-probability is 1.
badProb-bad : {Q R St : Type} (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
            → ∀ s (d : Dgr Q R) → bad s ≡ true → badProb resp bad s d ≡ 1ℚ
badProb-bad resp bad s (out _)   eq rewrite eq = refl
badProb-bad resp bad s (ask q k) eq rewrite eq = refl

--------------------------------------------------------------------------------
-- THE SUPERMARTINGALE BOUND for `badProb`, PROVEN.  A potential `φ` (indexed by
-- the remaining query budget) together with a support-preserved invariant `Inv`
-- such that φ ≥ 1 on bad states and φ never increases in expectation per query
-- bounds the bad-probability of ANY adaptive ≤ m-query distinguisher by the
-- initial potential.  This is the adaptive-robust core of any birthday bound:
-- what remains for a concrete system is a NON-adaptive, per-step certificate.
--------------------------------------------------------------------------------

-- `Inv` holds at every state the kernel can actually reach in one step.
Preserved : {Q R St : Type} → (St → Type) → (St → Q → Dist-ℚ (St × R)) → Type
Preserved Inv resp = ∀ s q → Inv s → OnSupport (λ sr → Inv (proj₁ sr)) (resp s q)

badProb-super :
  {Q R St : Type} (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
  (Inv : St → Type) (φ : ℕ → St → ℚ)
  → Preserved Inv resp
  → (∀ m s → Inv s → 0ℚ ≤ℚ φ m s)
  → (∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s)
  → (∀ m s q → Inv s → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s)
  → ∀ m d s → asks≤ m d → Inv s → badProb resp bad s d ≤ℚ φ m s
badProb-super resp bad Inv φ pres nn lb step m (out b) s le inv with bad s in eqb
... | true  = lb m s inv eqb
... | false = nn m s inv
badProb-super resp bad Inv φ pres nn lb step zero (ask q kd) s () inv
badProb-super resp bad Inv φ pres nn lb step (suc m) (ask q kd) s le inv
  with bad s in eqb
... | true  = lb (suc m) s inv eqb
... | false = ≤-trans
    (E-mono-on (resp s q)
      (λ sr → badProb resp bad (proj₁ sr) (kd (proj₂ sr)))
      (λ sr → φ m (proj₁ sr))
      (ListAll.map
        (λ {e} inv' → badProb-super resp bad Inv φ pres nn lb step m
                        (kd (proj₂ (proj₂ e))) (proj₁ (proj₂ e))
                        (le (proj₂ (proj₂ e))) inv')
        (pres s q inv)))
    (step m s q inv)

-- A birthday-style certificate for a kernel: everything `badProb-super` needs,
-- with the initial potential dominated by the claimed bound.
record SuperCert {Q R St : Type} (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
                 (s₀ : St) (ε : ℕ → ℚ) : Type₁ where
  field
    Inv    : St → Type
    φ      : ℕ → St → ℚ
    inv₀   : Inv s₀
    pres   : Preserved Inv resp
    φ-nn   : ∀ m s → Inv s → 0ℚ ≤ℚ φ m s
    φ-bad  : ∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s
    φ-step : ∀ m s q → Inv s → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
    φ-init : ∀ m → φ m s₀ ≤ℚ ε m

badProb-bounded :
  {Q R St : Type} {resp : St → Q → Dist-ℚ (St × R)} {bad : St → Bool}
  {s₀ : St} {ε : ℕ → ℚ}
  → SuperCert resp bad s₀ ε
  → ∀ m d → asks≤ m d → badProb resp bad s₀ d ≤ℚ ε m
badProb-bounded {resp = resp} {bad} {s₀} c m d le = ≤-trans
  (badProb-super resp bad (SuperCert.Inv c) (SuperCert.φ c) (SuperCert.pres c)
    (SuperCert.φ-nn c) (SuperCert.φ-bad c) (SuperCert.φ-step c)
    m d s₀ le (SuperCert.inv₀ c))
  (SuperCert.φ-init c m)

--------------------------------------------------------------------------------
-- THE BRIDGE — Fundamental Lemma of Game-Playing, COUPLED form, PROVEN.
--
-- A coupling is a single kernel producing the shared state evolution together
-- with BOTH answers, real and ideal.  The two worlds are its projections, where
-- the ideal projection is DEFINED to copy the real answer as long as the
-- POST-state is good — so "identical until bad" holds by construction and the
-- lemma needs NO side conditions: for ANY coupled kernel, the two worlds differ
-- by at most the probability that `bad` fires during the interaction.
--------------------------------------------------------------------------------

module Coupling {Q R St : Type} (bad : St → Bool)
                (respB : St → Q → Dist-ℚ (St × (R × R))) where

  fR fI : St × (R × R) → St × R
  fR t = proj₁ t , proj₁ (proj₂ t)
  fI t = proj₁ t , cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))

  realK idealK : St → Q → Dist-ℚ (St × R)
  realK  s q = Dmap fR (respB s q)
  idealK s q = Dmap fI (respB s q)

  FLGP : ∀ s₀ d → ∣ Pr₁ (runWith idealK s₀ d) -ℚ Pr₁ (runWith realK s₀ d) ∣ℚ
                ≤ℚ badProb realK bad s₀ d
  FLGP s (out b) = subst (_≤ℚ bool→ℚ (bad s)) (sym lhs≡0) (0≤bool (bad s))
    where lhs≡0 : ∣ Pr₁ (return-ℚ b) -ℚ Pr₁ (return-ℚ b) ∣ℚ ≡ 0ℚ
          lhs≡0 = trans (cong ∣_∣ℚ (+-inverseʳ (Pr₁ (return-ℚ b))))
                        (0≤p⇒∣p∣≡p ≤-refl)
  FLGP s (ask q k) with bad s in eqbad
  ... | true  = ∣Pr-Pr∣≤1 (runWith idealK s (ask q k)) (runWith realK s (ask q k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqI eqR))
     (≤-trans (E-abs-diff (respB s q) AI AR)
     (≤-trans (E-mono (respB s q) (λ t → ∣ AI t -ℚ AR t ∣ℚ) BB pointwise)
              (≤-reflexive (sym eqB))))
    where
      KI KR : St × R → Dist-ℚ Bool
      KI sr = runWith idealK (proj₁ sr) (k (proj₂ sr))
      KR sr = runWith realK  (proj₁ sr) (k (proj₂ sr))

      AI AR BB : St × (R × R) → ℚ
      AI t = Pr₁ (KI (fI t))
      AR t = Pr₁ (KR (fR t))
      BB t = badProb realK bad (proj₁ t) (k (proj₁ (proj₂ t)))

      eqI : Pr₁ (runWith idealK s (ask q k)) ≡ E (respB s q) AI
      eqI = trans (Pr₁-bind (idealK s q) KI)
                  (lookupᴰℚ-Dmap fI (respB s q) (λ sr → Pr₁ (KI sr)))

      eqR : Pr₁ (runWith realK s (ask q k)) ≡ E (respB s q) AR
      eqR = trans (Pr₁-bind (realK s q) KR)
                  (lookupᴰℚ-Dmap fR (respB s q) (λ sr → Pr₁ (KR sr)))

      eqB : E (realK s q) (λ sr → badProb realK bad (proj₁ sr) (k (proj₂ sr)))
          ≡ E (respB s q) BB
      eqB = lookupᴰℚ-Dmap fR (respB s q)
              (λ sr → badProb realK bad (proj₁ sr) (k (proj₂ sr)))

      pointwise : ∀ t → ∣ AI t -ℚ AR t ∣ℚ ≤ℚ BB t
      pointwise t with bad (proj₁ t) in eqt
      ... | false = FLGP (proj₁ t) (k (proj₁ (proj₂ t)))
      ... | true  =
        subst (λ z → ∣ Pr₁ (KI (proj₁ t , proj₂ (proj₂ t))) -ℚ AR t ∣ℚ ≤ℚ z)
              (sym (badProb-bad realK bad (proj₁ t) (k (proj₁ (proj₂ t))) eqt))
              (∣Pr-Pr∣≤1 (KI (proj₁ t , proj₂ (proj₂ t))) (KR (fR t)))

--------------------------------------------------------------------------------
-- 2. THE EXAMPLE
--
--   p = parties   n = hash / block / chaining size   k = number of blocks
--   Ideal:  RandomOracle p (k * n) n   Resource: RandomOracle p (2 * n) n
--------------------------------------------------------------------------------

-- `k ≥ 1` is REQUIRED: for `k = 0` every message hashes deterministically to
-- `IV` while `bound ≡ 0`, so `indistinguishable` (via `bad-bound`) would be false.
module MD (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

  -- ignore parties for now: a single party.
  p : ℕ
  p = 1

  CV  : Type
  CV  = Vec Bool n            -- chaining value / hash
  Blk : Type
  Blk = Vec Bool n            -- one message block

  module Comp where
    -- 4-input compression oracle (Theorem 3.1): tagging each call with the message
    -- length and block index — the prefix-free encoding — makes `f` an independent
    -- random oracle per (length, index):  (chaining , block , ⟨length⟩ , ⟨index⟩) ↦ n bits.
    open RandomOracle p (CV × Blk × ℕ × ℕ) n public
    Interface = Output ⇿ Input

    M : PMachine I Interface
    M = liftFun (asResource Functionality)

  module General where
    open RandomOracle p (Vec Bool (k * n)) n public
    Interface = Output ⇿ Input

    M : PMachine I Interface
    M = liftFun (asResource Functionality)

  -- A compression query packs the chaining value, the block, the message length
  -- (always `k` here) and the block index — the index-tagged prefix-free encoding.
  pack : CV → Blk → ℕ → CV × Blk × ℕ × ℕ
  pack h b idx = (h , b , k , idx)

  chunk : ∀ j → Vec Bool (j * n) → Vec (Vec Bool n) j
  chunk zero    v = []
  chunk (suc j) v = takeᵛ n v ∷ chunk j (dropᵛ n v)

  toBlocks : Vec Bool (k * n) → List Blk          -- a (k·n)-bit message as k blocks
  toBlocks v = toList (chunk k v)

  -- Merkle-Damgard
  -- FIXME: we just want to fail on invalid input, not give garbage output
  private
    MDState : Type
    MDState = Maybe (Fin p × ℕ × List Blk)   -- idle, or (party, next block index, remaining blocks)

    -- new query: fire the first compression query at index 1, i.e. (IV , b₁ , k , 1).
    -- Split out so it pattern-matches the block list as an honest argument — that
    -- keeps `mdStep (sr , inj₂ (i , M)) = mdStepᵇ i (toBlocks M)` DEFINITIONAL, so
    -- proofs can case on `toBlocks M` via a supplied equation rather than fighting a
    -- `with`-abstracted scrutinee inside `mdStep`.
    mdStepᵇ : Fin p → List Blk → MDState × (Comp.Input ⊎ General.Output)
    mdStepᵇ i []       = (nothing            , inj₂ (i , IV))
    mdStepᵇ i (b ∷ bs) = (just (i , 2 , bs)  , inj₁ (i , pack IV b 1))

    mdStep : MDState × (Comp.Output ⊎ General.Input)
           → MDState × (Comp.Input  ⊎ General.Output)
    mdStep (_ , inj₂ (i , M)) = mdStepᵇ i (toBlocks M)
    -- callback with chaining value `h`: done, or fire the next block at its index
    mdStep (just (i , idx , [])       , inj₁ (_ , h)) = (nothing                 , inj₂ (i , h))
    mdStep (just (i , idx , (b ∷ bs)) , inj₁ (_ , h)) = (just (i , suc idx , bs) , inj₁ (i , pack h b idx))
    mdStep (nothing                   , inj₁ (i , h)) = (nothing                 , inj₂ (i , h))

    mdArrow : SFunᵉ {M = Dist-ℚ} (Comp.Output ⊎ General.Input) (Comp.Input ⊎ General.Output)
    mdArrow = record { State = MDState ; init = nothing ; fun = return-ℚ ∘ mdStep }

  MD : PMachine Comp.Interface General.Interface
  MD = liftFun mdArrow

  ------------------------------------------------------------------------
  -- Security via the reactive model + Fundamental Lemma of Game-Playing.
  -- `MD ⊚ Comp.M` (compression hidden) is a variable-length random oracle:
  -- advantage `bound n` against any adaptive n-query distinguisher.  No simulator.

  i₀ : Fin p
  i₀ = zero

  -- MD chaining the compression oracle over one message's blocks, threading the
  -- compression table; returns the final chaining value (the hash).
  mdRun : Comp.Table → CV → List Blk → ℕ → Dist-ℚ (Comp.Table × CV)
  mdRun s h []       idx = return-ℚ (s , h)
  mdRun s h (b ∷ bs) idx =
    Comp.step (s , i₀ , pack h b idx) >>=ᴹ λ o → mdRun (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)

  -- REAL per-query response = the reactive kernel of `MD ⊚ Comp.M`: run MD's
  -- chaining over the message, echo the querying party with the resulting hash.
  respR : Comp.Table → General.Input → Dist-ℚ (Comp.Table × General.Output)
  respR s (i , M) = mdRun s IV (toBlocks M) 1 >>=ᴹ λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh))

  -- `respR` as a stateful functionality — the underlying morphism the composite
  -- `MD ⊚ Comp.M` should compute to (compression table = internal state).
  respRM : SFunᵉ {M = Dist-ℚ} General.Input General.Output
  respRM = record { State = Comp.Table ; init = [] ; fun = λ sq → respR (proj₁ sq) (proj₂ sq) }


  ------------------------------------------------------------------------
  -- Phase B-now: DERIVE `∘ᵍ-MD` from the generic trace-unfolding law
  -- `∘ᵍ-unfold`.  Reading `embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality)`
  -- as the ⊎-trace of the MD/compression wiring, `∘ᵍ-unfold` replaces it (once fuel
  -- is saturated) by the `GComp` token machine `machineAt Nfuel`, and we then compute
  -- that machine's observable behaviour to `respR` by a bounded loop-replay.

  -- `Fin p` is a singleton here (`p = 1`), so the party a query carries is `i₀`.
  fin1 : (i : Fin p) → i ≡ i₀
  fin1 zero = refl

  private
    -- `≈ᵉ`-transitivity and `≡`-to-`≈ᵉ`, unfolded per-`xs` to `≈Mℚ` (avoids needing
    -- the `IsEquivalence` module of `_≈ᵉ_` in scope).
    ≈ᵉ-trans⊥ : {A B : Type} {f g h : SFun⊥ A B}
              → (_≈ᵉ_ {M = Dist⊥}) f g → (_≈ᵉ_ {M = Dist⊥}) g h → (_≈ᵉ_ {M = Dist⊥}) f h
    ≈ᵉ-trans⊥ {f = f} {g} {h} f≈g g≈h xs =
      Mℚ.trans {i = eval f xs} {j = eval g xs} {k = eval h xs} (f≈g xs) (g≈h xs)

    ≡→≈ᵉ⊥ : {A B : Type} {f g : SFun⊥ A B} → f ≡ g → (_≈ᵉ_ {M = Dist⊥}) f g
    ≡→≈ᵉ⊥ {f = f} {g} eq xs = Mℚ.reflexive (cong (λ m → eval m xs) eq)

    -- `Dmap just` of a point mass collapses to `return⊥`.
    dmap-ret : {A : Type} (x : A) → Dmap just (return-ℚ x) ≈Mℚ return⊥ x
    dmap-ret x = >>=ᴹ-identityˡ x (return-ℚ ∘ just)

    Dmapⱼ-cong : {A : Type} (μ ν : Dist-ℚ A) → μ ≈Mℚ ν → Dmap just μ ≈Mℚ Dmap just ν
    Dmapⱼ-cong μ ν e =
      >>=ᴹ-cong {μ = μ} {ν} {return-ℚ ∘ just} {return-ℚ ∘ just} e (λ a → Mℚ.refl {x = return-ℚ (just a)})

    >>=ᴹ-congʳ : {A B : Type} (K : A → Dist-ℚ B) (μ ν : Dist-ℚ A)
               → μ ≈Mℚ ν → (μ >>=ᴹ K) ≈Mℚ (ν >>=ᴹ K)
    >>=ᴹ-congʳ K μ ν e = >>=ᴹ-cong {μ = μ} {ν} {K} {K} e (λ a → Mℚ.refl {x = K a})

  -- Number of body-steps the token loop takes over a block list: each block costs
  -- one f-bounce (compression answer) + one g-bounce (relay advance/exit).
  double : ℕ → ℕ
  double zero    = zero
  double (suc j) = suc (suc (double j))

  stepsFor : List Blk → ℕ
  stepsFor []       = 0
  stepsFor (_ ∷ bs) = suc (suc (stepsFor bs))

  stepsFor-len : ∀ (L : List Blk) → stepsFor L ≡ double (length L)
  stepsFor-len []       = refl
  stepsFor-len (_ ∷ bs) = cong (λ z → suc (suc z)) (stepsFor-len bs)

  len-tlᴮ : ∀ {A : Type} {j} (v : Vec A j) → length (toList v) ≡ j
  len-tlᴮ []      = refl
  len-tlᴮ (_ ∷ v) = cong suc (len-tlᴮ v)

  blk-len : ∀ (M : Vec Bool (k * n)) → length (toBlocks M) ≡ k
  blk-len M = len-tlᴮ (chunk k M)

  -- A single global fuel that saturates every activation (all messages are `k` blocks).
  Nfuel : ℕ
  Nfuel = double k

  blkBound : ∀ (M : Vec Bool (k * n)) → stepsFor (toBlocks M) ≡ Nfuel
  blkBound M = trans (stepsFor-len (toBlocks M)) (cong double (blk-len M))

  -- MD chaining threading an ARBITRARY compression kernel `h`, carrying the party
  -- `i` that the relay actually forwards (`mdRun` hardcodes `i₀`).
  mdRunH : (h : SFunᵉ {M = Dist-ℚ} Comp.Input Comp.Output)
         → SFunᵉ.State h → Fin p → CV → List Blk → ℕ → Dist-ℚ (SFunᵉ.State h × CV)
  mdRunH h st i cv []       idx = return-ℚ (st , cv)
  mdRunH h st i cv (b ∷ bs) idx =
    SFunᵉ.fun h (st , (i , pack cv b idx)) >>=ᴹ λ o → mdRunH h (proj₁ o) i (proj₂ (proj₂ o)) bs (suc idx)

  -- Party irrelevance: `mdRunH Comp.Functionality` (party from the query) agrees with
  -- `mdRun` (party `i₀`), since `p = 1` forces `i ≡ i₀`.
  mdRunH-mdRun : ∀ (s : Comp.Table) (i : Fin p) (cv : CV) (bs : List Blk) (idx : ℕ)
               → mdRunH Comp.Functionality s i cv bs idx ≈Mℚ mdRun s cv bs idx
  mdRunH-mdRun s i cv []       idx = λ P → refl
  mdRunH-mdRun s i cv (b ∷ bs) idx = Mℚ.trans
    {i = mdRunH Comp.Functionality s i cv (b ∷ bs) idx}
    {j = mdRunH Comp.Functionality s i₀ cv (b ∷ bs) idx}
    {k = mdRun s cv (b ∷ bs) idx}
    (Mℚ.reflexive (cong (λ j → mdRunH Comp.Functionality s j cv (b ∷ bs) idx) (fin1 i)))
    (>>=ᴹ-congˡ (Comp.step (s , i₀ , pack cv b idx))
      (λ o → mdRunH Comp.Functionality (proj₁ o) i₀ (proj₂ (proj₂ o)) bs (suc idx))
      (λ o → mdRun (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx))
      (λ o → mdRunH-mdRun (proj₁ o) i₀ (proj₂ (proj₂ o)) bs (suc idx)))

  -- `respR` with an arbitrary compression kernel `h`.
  respRHM : (h : SFunᵉ {M = Dist-ℚ} Comp.Input Comp.Output) → SFunᵉ {M = Dist-ℚ} General.Input General.Output
  respRHM h = record
    { State = SFunᵉ.State h
    ; init  = SFunᵉ.init h
    ; fun   = λ sq → mdRunH h (proj₁ sq) (proj₁ (proj₂ sq)) IV (toBlocks (proj₂ (proj₂ sq))) 1
                       >>=ᴹ λ sh → return-ℚ (proj₁ sh , (proj₁ (proj₂ sq) , proj₂ sh)) }

  respRHM-CF≈respRM : (_≈ᵉ_ {M = Dist⊥}) (embed⊥ (respRHM Comp.Functionality)) (embed⊥ respRM)
  respRHM-CF≈respRM = trace-cong⊥ kern []
    where
      kern : ∀ sa → SFunᵉ.fun (embed⊥ (respRHM Comp.Functionality)) sa ≈Mℚ SFunᵉ.fun (embed⊥ respRM) sa
      kern (s , (i , M)) = Dmapⱼ-cong
        (mdRunH Comp.Functionality s i IV (toBlocks M) 1 >>=ᴹ (λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh))))
        (mdRun s IV (toBlocks M) 1 >>=ᴹ (λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh))))
        (>>=ᴹ-congʳ (λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh)))
          (mdRunH Comp.Functionality s i IV (toBlocks M) 1)
          (mdRun s IV (toBlocks M) 1)
          (mdRunH-mdRun s i IV (toBlocks M) 1))

  -- The generic loop-replay, parameterised over the (opaque) compression resource.
  module Replay (hraw : SFunᵉ {M = Dist-ℚ} (⊥ ⊎ Comp.Input) (⊥ ⊎ Comp.Output)) where

    private module hr = SFunᵉ hraw

    open GComp (embed⊥ mdArrow) (embed⊥ hraw)

    H : SFunᵉ {M = Dist-ℚ} Comp.Input Comp.Output
    H = stripᵉ hraw

    -- `stepF` on an `SFunᵉ (⊥ ⊎ _) (⊥ ⊎ _)` output (always `inj₂`): continue into g.
    stepF-lemma : ∀ (sg : MDState) (sf' : hr.State) (o : ⊥ ⊎ Comp.Output)
                → stepF sg (sf' , o) ≡ inj₂ ((sg , sf') , inj₁ (unbot o))
    stepF-lemma sg sf' (inj₂ co) = refl

    -- One f-bounce: enter g's partner `f = embed⊥ hraw`, then continue with the answer.
    f-bounce : ∀ (sg : MDState) (t : hr.State) (q : Comp.Input) {R : Type} (K : Res → Dist⊥ R)
             → (body ((sg , t) , inj₂ q) >>=⊥ K)
               ≈Mℚ (hr.fun (t , inj₂ q) >>=ᴹ λ sr → K (inj₂ ((sg , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
    f-bounce sg t q K = begin
      (body ((sg , t) , inj₂ q) >>=⊥ K)
        ≈⟨ >>=⊥-assoc (Dmap just (hr.fun (t , inj₂ q))) (return⊥ ∘ stepF sg) K ⟩
      (Dmap just (hr.fun (t , inj₂ q)) >>=⊥ λ x → return⊥ (stepF sg x) >>=⊥ K)
        ≈⟨ >>=⊥-embed (hr.fun (t , inj₂ q)) (λ x → return⊥ (stepF sg x) >>=⊥ K) ⟩
      (hr.fun (t , inj₂ q) >>=ᴹ λ x → return⊥ (stepF sg x) >>=⊥ K)
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ q))
             (λ x → return⊥ (stepF sg x) >>=⊥ K)
             (λ x → K (stepF sg x))
             (λ x → >>=⊥-identityˡ (stepF sg x) K) ⟩
      (hr.fun (t , inj₂ q) >>=ᴹ λ x → K (stepF sg x))
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ q))
             (λ x → K (stepF sg x))
             (λ sr → K (inj₂ ((sg , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
             (λ x → Mℚ.reflexive (cong K (stepF-lemma sg (proj₁ x) (proj₂ x)))) ⟩
      (hr.fun (t , inj₂ q) >>=ᴹ λ sr → K (inj₂ ((sg , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
      ∎
      where open RS (Mℚ-setoid _)

    -- One g-bounce: `g = embed⊥ mdArrow` is deterministic, so it just applies `mdStep`.
    g-bounce : ∀ (sr : MDState) (t : hr.State) (co : Comp.Output) {R : Type} (K : Res → Dist⊥ R)
             → (body ((sr , t) , inj₁ co) >>=⊥ K) ≈Mℚ K (stepG t (mdStep (sr , inj₁ co)))
    g-bounce sr t co K = begin
      (body ((sr , t) , inj₁ co) >>=⊥ K)
        ≈⟨ >>=⊥-assoc (Dmap just (return-ℚ (mdStep (sr , inj₁ co)))) (return⊥ ∘ stepG t) K ⟩
      (Dmap just (return-ℚ (mdStep (sr , inj₁ co))) >>=⊥ λ x → return⊥ (stepG t x) >>=⊥ K)
        ≈⟨ >>=⊥-congʳ (λ x → return⊥ (stepG t x) >>=⊥ K)
             (Dmap just (return-ℚ (mdStep (sr , inj₁ co))))
             (return⊥ (mdStep (sr , inj₁ co)))
             (dmap-ret (mdStep (sr , inj₁ co))) ⟩
      (return⊥ (mdStep (sr , inj₁ co)) >>=⊥ λ x → return⊥ (stepG t x) >>=⊥ K)
        ≈⟨ >>=⊥-identityˡ (mdStep (sr , inj₁ co)) (λ x → return⊥ (stepG t x) >>=⊥ K) ⟩
      (return⊥ (stepG t (mdStep (sr , inj₁ co))) >>=⊥ K)
        ≈⟨ >>=⊥-identityˡ (stepG t (mdStep (sr , inj₁ co))) K ⟩
      K (stepG t (mdStep (sr , inj₁ co)))
      ∎
      where open RS (Mℚ-setoid _)

    -- The embedded MD-composite value.
    mdEmbed : hr.State → Fin p → CV → List Blk → ℕ → Dist⊥ (S × (⊥ ⊎ General.Output))
    mdEmbed t i cv bs idx =
      Dmap just (mdRunH H t i cv bs idx >>=ᴹ λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh)))

    mdRunH-cons : ∀ (t : hr.State) i cv b bs idx
                → mdRunH H t i cv (b ∷ bs) idx
                  ≈Mℚ (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ
                         λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
    mdRunH-cons t i cv b bs idx = begin
      mdRunH H t i cv (b ∷ bs) idx
        ≈⟨ >>=ᴹ-assoc (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)))
             (λ o → mdRunH H (proj₁ o) i (proj₂ (proj₂ o)) bs (suc idx)) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         (return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ λ o → mdRunH H (proj₁ o) i (proj₂ (proj₂ o)) bs (suc idx)))
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ λ o → mdRunH H (proj₁ o) i (proj₂ (proj₂ o)) bs (suc idx))
             (λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
             (λ sr → >>=ᴹ-identityˡ (proj₁ sr , unbot (proj₂ sr))
                       (λ o → mdRunH H (proj₁ o) i (proj₂ (proj₂ o)) bs (suc idx))) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
      ∎
      where open RS (Mℚ-setoid _)

    mdEmbed-nil : ∀ (t : hr.State) i cv idx → mdEmbed t i cv [] idx ≈Mℚ return⊥ ((nothing , t) , inj₂ (i , cv))
    mdEmbed-nil t i cv idx = begin
      Dmap just (return-ℚ (t , cv) >>=ᴹ λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh)))
        ≈⟨ Dmapⱼ-cong
             (return-ℚ (t , cv) >>=ᴹ (λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh))))
             (return-ℚ ((nothing , t) , inj₂ (i , cv)))
             (>>=ᴹ-identityˡ (t , cv) (λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh)))) ⟩
      Dmap just (return-ℚ ((nothing , t) , inj₂ (i , cv)))
        ≈⟨ dmap-ret ((nothing , t) , inj₂ (i , cv)) ⟩
      return⊥ ((nothing , t) , inj₂ (i , cv))
      ∎
      where open RS (Mℚ-setoid _)

    mdEmbed-cons : ∀ (t : hr.State) i cv b bs idx
                 → mdEmbed t i cv (b ∷ bs) idx
                   ≈Mℚ (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ
                          λ sr → mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
    mdEmbed-cons t i cv b bs idx = begin
      Dmap just (mdRunH H t i cv (b ∷ bs) idx >>=ᴹ Kexit)
        ≈⟨ Dmapⱼ-cong
             (mdRunH H t i cv (b ∷ bs) idx >>=ᴹ Kexit)
             ((hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx)) >>=ᴹ Kexit)
             (>>=ᴹ-congʳ Kexit
               (mdRunH H t i cv (b ∷ bs) idx)
               (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
               (mdRunH-cons t i cv b bs idx)) ⟩
      Dmap just ((hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx)) >>=ᴹ Kexit)
        ≈⟨ Dmapⱼ-cong
             ((hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx)) >>=ᴹ Kexit)
             (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → (mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx) >>=ᴹ Kexit))
             (>>=ᴹ-assoc (hr.fun (t , inj₂ (i , pack cv b idx)))
               (λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
               Kexit) ⟩
      Dmap just (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → (mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx) >>=ᴹ Kexit))
        ≈⟨ >>=ᴹ-assoc (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → mdRunH H (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx) >>=ᴹ Kexit)
             (return-ℚ ∘ just) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) bs (suc idx))
      ∎
      where Kexit = λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh))
            open RS (Mℚ-setoid _)

    -- The core induction: from an f-token (answer for block `b`, remaining `bs`,
    -- chaining `cv`, index `idx`, relay `just (i , suc idx , bs)`) with `≥ stepsFor`
    -- fuel, the token loop replays `mdRunH H … (b ∷ bs) idx` and exits.
    loop-replay : ∀ (b : Blk) (bs : List Blk) (t : hr.State) (i : Fin p) (cv : CV) (idx fuel : ℕ)
                → stepsFor (b ∷ bs) ≤ fuel
                → iterFuel fuel body ((just (i , suc idx , bs) , t) , inj₂ (i , pack cv b idx))
                  ≈Mℚ mdEmbed t i cv (b ∷ bs) idx
    loop-replay b [] t i cv idx (suc (suc m)) (s≤s (s≤s h')) = begin
      iterFuel (suc (suc m)) body ((just (i , suc idx , []) , t) , inj₂ (i , pack cv b idx))
        ≈⟨ f-bounce (just (i , suc idx , [])) t (i , pack cv b idx) (iterGo (suc m) body) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         iterGo (suc m) body (inj₂ ((just (i , suc idx , []) , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → iterGo (suc m) body (inj₂ ((just (i , suc idx , []) , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
             (λ sr → return⊥ ((nothing , proj₁ sr) , inj₂ (i , proj₂ (unbot (proj₂ sr)))))
             (λ sr → g-bounce (just (i , suc idx , [])) (proj₁ sr) (unbot (proj₂ sr)) (iterGo m body)) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         return⊥ ((nothing , proj₁ sr) , inj₂ (i , proj₂ (unbot (proj₂ sr)))))
        ≈˘⟨ Mℚ.trans {i = mdEmbed t i cv (b ∷ []) idx}
              {j = hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) [] (suc idx)}
              {k = hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr → return⊥ ((nothing , proj₁ sr) , inj₂ (i , proj₂ (unbot (proj₂ sr))))}
              (mdEmbed-cons t i cv b [] idx)
              (>>=ᴹ-congˡ (hr.fun (t , inj₂ (i , pack cv b idx)))
                (λ sr → mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) [] (suc idx))
                (λ sr → return⊥ ((nothing , proj₁ sr) , inj₂ (i , proj₂ (unbot (proj₂ sr)))))
                (λ sr → mdEmbed-nil (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) (suc idx))) ⟩
      mdEmbed t i cv (b ∷ []) idx
      ∎
      where open RS (Mℚ-setoid _)
    loop-replay b (b' ∷ bs') t i cv idx (suc (suc m)) (s≤s (s≤s h')) = begin
      iterFuel (suc (suc m)) body ((just (i , suc idx , b' ∷ bs') , t) , inj₂ (i , pack cv b idx))
        ≈⟨ f-bounce (just (i , suc idx , b' ∷ bs')) t (i , pack cv b idx) (iterGo (suc m) body) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         iterGo (suc m) body (inj₂ ((just (i , suc idx , b' ∷ bs') , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → iterGo (suc m) body (inj₂ ((just (i , suc idx , b' ∷ bs') , proj₁ sr) , inj₁ (unbot (proj₂ sr)))))
             (λ sr → iterFuel m body ((just (i , suc (suc idx) , bs') , proj₁ sr) , inj₂ (i , pack (proj₂ (unbot (proj₂ sr))) b' (suc idx))))
             (λ sr → g-bounce (just (i , suc idx , b' ∷ bs')) (proj₁ sr) (unbot (proj₂ sr)) (iterGo m body)) ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         iterFuel m body ((just (i , suc (suc idx) , bs') , proj₁ sr) , inj₂ (i , pack (proj₂ (unbot (proj₂ sr))) b' (suc idx))))
        ≈⟨ >>=ᴹ-congˡ (hr.fun (t , inj₂ (i , pack cv b idx)))
             (λ sr → iterFuel m body ((just (i , suc (suc idx) , bs') , proj₁ sr) , inj₂ (i , pack (proj₂ (unbot (proj₂ sr))) b' (suc idx))))
             (λ sr → mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) (b' ∷ bs') (suc idx))
             (λ sr → loop-replay b' bs' (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) (suc idx) m h') ⟩
      (hr.fun (t , inj₂ (i , pack cv b idx)) >>=ᴹ λ sr →
         mdEmbed (proj₁ sr) i (proj₂ (unbot (proj₂ sr))) (b' ∷ bs') (suc idx))
        ≈˘⟨ mdEmbed-cons t i cv b (b' ∷ bs') idx ⟩
      mdEmbed t i cv (b ∷ b' ∷ bs') idx
      ∎
      where open RS (Mℚ-setoid _)

    -- Entering on the general query: `mdStep` fires block 1, then the loop runs.
    enter-red : ∀ (t : hr.State) (i : Fin p) (M : Vec Bool (k * n)) (sr : MDState) (fuel : ℕ)
              → kernelAt fuel ((sr , t) , inj₂ (i , M)) ≈Mℚ goRes fuel (stepG t (mdStepᵇ i (toBlocks M)))
    enter-red t i M sr fuel = begin
      kernelAt fuel ((sr , t) , inj₂ (i , M))
        ≈⟨ >>=⊥-congʳ (goRes fuel)
             (Dmap just (return-ℚ (mdStepᵇ i (toBlocks M))) >>=⊥ (return⊥ ∘ stepG t))
             (return⊥ (stepG t (mdStepᵇ i (toBlocks M))))
             enterμ ⟩
      (return⊥ (stepG t (mdStepᵇ i (toBlocks M))) >>=⊥ goRes fuel)
        ≈⟨ >>=⊥-identityˡ (stepG t (mdStepᵇ i (toBlocks M))) (goRes fuel) ⟩
      goRes fuel (stepG t (mdStepᵇ i (toBlocks M)))
      ∎
      where
        open RS (Mℚ-setoid _)
        -- explicit `Mℚ.trans` (over `Dist⊥ Res`) so it does not share the main
        -- chain's reasoning metavariable (which is over `Dist⊥ (S × …)`).
        enterμ : (Dmap just (return-ℚ (mdStepᵇ i (toBlocks M))) >>=⊥ (return⊥ ∘ stepG t))
                 ≈Mℚ return⊥ (stepG t (mdStepᵇ i (toBlocks M)))
        enterμ = Mℚ.trans
          {i = Dmap just (return-ℚ (mdStepᵇ i (toBlocks M))) >>=⊥ (return⊥ ∘ stepG t)}
          {j = return⊥ (mdStepᵇ i (toBlocks M)) >>=⊥ (return⊥ ∘ stepG t)}
          {k = return⊥ (stepG t (mdStepᵇ i (toBlocks M)))}
          (>>=⊥-congʳ (return⊥ ∘ stepG t)
            (Dmap just (return-ℚ (mdStepᵇ i (toBlocks M))))
            (return⊥ (mdStepᵇ i (toBlocks M)))
            (dmap-ret (mdStepᵇ i (toBlocks M))))
          (>>=⊥-identityˡ (mdStepᵇ i (toBlocks M)) (return⊥ ∘ stepG t))

    -- Non-emptiness view of a message's block list (`k` is `NonZero`).  Isolated so
    -- that the `with toBlocks M` abstraction never touches a goal mentioning
    -- `kernelAt` (whose normal form contains `toBlocks M` — abstracting it there
    -- would break convertibility with chain nodes still mentioning `M`).
    blkView : ∀ (M : Vec Bool (k * n)) → Σ Blk λ b → Σ (List Blk) λ bs → toBlocks M ≡ b ∷ bs
    blkView M with toBlocks M in eq
    ... | []     = ⊥-elim (≢-nonZero⁻¹ k (trans (sym (blk-len M)) (cong length eq)))
    ... | b ∷ bs = b , bs , refl

    -- Per-query: the token machine computes `mdEmbed` (the embedded `respR`).
    query-kernel : ∀ (t : hr.State) (i : Fin p) (M : Vec Bool (k * n)) (sr : MDState) (fuel : ℕ)
                 → stepsFor (toBlocks M) ≤ fuel
                 → kernelAt fuel ((sr , t) , inj₂ (i , M)) ≈Mℚ mdEmbed t i IV (toBlocks M) 1
    query-kernel t i M sr fuel bd = main (blkView M)
      where
      main : (Σ Blk λ b → Σ (List Blk) λ bs → toBlocks M ≡ b ∷ bs)
           → kernelAt fuel ((sr , t) , inj₂ (i , M)) ≈Mℚ mdEmbed t i IV (toBlocks M) 1
      main (b , bs , eq) = begin
        kernelAt fuel ((sr , t) , inj₂ (i , M))
          ≈⟨ enter-red t i M sr fuel ⟩
        goRes fuel (stepG t (mdStepᵇ i (toBlocks M)))
          ≡⟨ cong (λ L → goRes fuel (stepG t (mdStepᵇ i L))) eq ⟩
        iterFuel fuel body ((just (i , suc 1 , bs) , t) , inj₂ (i , pack IV b 1))
          ≈⟨ loop-replay b bs t i IV 1 fuel (subst (λ L → stepsFor L ≤ fuel) eq bd) ⟩
        mdEmbed t i IV (b ∷ bs) 1
          ≡⟨ cong (λ L → mdEmbed t i IV L 1) (sym eq) ⟩
        mdEmbed t i IV (toBlocks M) 1
        ∎
        where open RS (Mℚ-setoid _)

    stableN : Stable Nfuel
    stableN m (sr , t) (inj₁ ()) _
    stableN m (sr , t) (inj₂ (i , M)) N≤m = Mℚ.trans
      {i = kernelAt m ((sr , t) , inj₂ (i , M))}
      {j = mdEmbed t i IV (toBlocks M) 1}
      {k = kernelAt Nfuel ((sr , t) , inj₂ (i , M))}
      (query-kernel t i M sr m (ℕP.≤-trans (ℕP.≤-reflexive (blkBound M)) N≤m))
      (Mℚ.sym {x = kernelAt Nfuel ((sr , t) , inj₂ (i , M))} {y = mdEmbed t i IV (toBlocks M) 1}
        (query-kernel t i M sr Nfuel (ℕP.≤-reflexive (blkBound M))))

    Km' = SFunᵉ.fun (strip⊥ (machineAt Nfuel))
    Kr' = SFunᵉ.fun (embed⊥ (respRHM H))

    machine-trace : ∀ (t : hr.State) (xs : List General.Input)
                  → trace {M = Dist⊥} Km' (nothing , t) xs ≈Mℚ trace {M = Dist⊥} Kr' t xs
    machine-trace t []              = λ P → refl
    machine-trace t ((i , M) ∷ qs) = begin
      trace {M = Dist⊥} Km' (nothing , t) ((i , M) ∷ qs)
        ≈⟨ >>=⊥-congʳ ContM (Km' ((nothing , t) , (i , M))) (μ >>=ᴹ Km-exit) Km'≈ ⟩
      ((μ >>=ᴹ Km-exit) >>=⊥ ContM)
        ≈⟨ >>=ᴹ-assoc μ Km-exit (kmaybe ContM) ⟩
      (μ >>=ᴹ λ sh → Km-exit sh >>=ᴹ kmaybe ContM)
        ≈⟨ >>=ᴹ-congˡ μ
             (λ sh → Km-exit sh >>=ᴹ kmaybe ContM)
             (λ sh → trace {M = Dist⊥} Km' (nothing , proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
             (λ sh → >>=⊥-identityˡ ((nothing , proj₁ sh) , (i , proj₂ sh)) ContM) ⟩
      (μ >>=ᴹ λ sh → trace {M = Dist⊥} Km' (nothing , proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
        ≈⟨ >>=ᴹ-congˡ μ
             (λ sh → trace {M = Dist⊥} Km' (nothing , proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
             (λ sh → trace {M = Dist⊥} Kr' (proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
             (λ sh → >>=⊥-congʳ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs))
                       (trace {M = Dist⊥} Km' (nothing , proj₁ sh) qs)
                       (trace {M = Dist⊥} Kr' (proj₁ sh) qs)
                       (machine-trace (proj₁ sh) qs)) ⟩
      (μ >>=ᴹ λ sh → trace {M = Dist⊥} Kr' (proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
        ≈˘⟨ >>=ᴹ-congˡ μ
              (λ sh → Kwrapr sh >>=ᴹ ContR)
              (λ sh → trace {M = Dist⊥} Kr' (proj₁ sh) qs >>=⊥ (λ bs → return⊥ ((i , proj₂ sh) ∷ bs)))
              (λ sh → >>=ᴹ-identityˡ (proj₁ sh , (i , proj₂ sh)) ContR) ⟩
      (μ >>=ᴹ λ sh → Kwrapr sh >>=ᴹ ContR)
        ≈˘⟨ >>=ᴹ-assoc μ Kwrapr ContR ⟩
      ((μ >>=ᴹ Kwrapr) >>=ᴹ ContR)
        ≈˘⟨ >>=⊥-embed (μ >>=ᴹ Kwrapr) ContR ⟩
      trace {M = Dist⊥} Kr' t ((i , M) ∷ qs)
      ∎
      where
        open RS (Mℚ-setoid _)
        μ      = mdRunH H t i IV (toBlocks M) 1
        Kwrap  = λ sh → return-ℚ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh))
        Kunbot = λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))
        Km-exit = λ sh → return⊥ ((nothing , proj₁ sh) , (i , proj₂ sh))
        Kwrapr = λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh))
        ContM  = λ sb → trace {M = Dist⊥} Km' (proj₁ sb) qs >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
        ContR  = λ sb → trace {M = Dist⊥} Kr' (proj₁ sb) qs >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
        -- explicit `Mℚ.trans` (over `Dist⊥ (S × General.Output)`) so it does not share
        -- the main chain's reasoning metavariable (over `Dist⊥ (List General.Output)`).
        Km'≈ : Km' ((nothing , t) , (i , M)) ≈Mℚ (μ >>=ᴹ Km-exit)
        Km'≈ = Mℚ.trans
          {i = kernelAt Nfuel ((nothing , t) , inj₂ (i , M)) >>=⊥ Kunbot}
          {j = Dmap just (μ >>=ᴹ Kwrap) >>=⊥ Kunbot}
          {k = μ >>=ᴹ Km-exit}
          (>>=⊥-congʳ Kunbot
            (kernelAt Nfuel ((nothing , t) , inj₂ (i , M)))
            (Dmap just (μ >>=ᴹ Kwrap))
            (query-kernel t i M nothing Nfuel (ℕP.≤-reflexive (blkBound M))))
          (Mℚ.trans
            {i = Dmap just (μ >>=ᴹ Kwrap) >>=⊥ Kunbot}
            {j = (μ >>=ᴹ Kwrap) >>=ᴹ Kunbot}
            {k = μ >>=ᴹ Km-exit}
            (>>=⊥-embed (μ >>=ᴹ Kwrap) Kunbot)
            (Mℚ.trans
              {i = (μ >>=ᴹ Kwrap) >>=ᴹ Kunbot}
              {j = μ >>=ᴹ (λ sh → Kwrap sh >>=ᴹ Kunbot)}
              {k = μ >>=ᴹ Km-exit}
              (>>=ᴹ-assoc μ Kwrap Kunbot)
              (>>=ᴹ-congˡ μ
                (λ sh → Kwrap sh >>=ᴹ Kunbot)
                Km-exit
                (λ sh → >>=ᴹ-identityˡ ((nothing , proj₁ sh) , inj₂ (i , proj₂ sh)) Kunbot))))

    machine-eval : (_≈ᵉ_ {M = Dist⊥}) (strip⊥ (machineAt Nfuel)) (embed⊥ (respRHM H))
    machine-eval xs = machine-trace hr.init xs

  -- ∘ᵍ-MD: now a DERIVED THEOREM (was a per-machine assumption).  The composite's
  -- underlying morphism is the trace `embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality)`;
  -- `∘ᵍ-unfold` (fuel-saturated at `Nfuel`, `RC.stableN`) rewrites it to the token machine
  -- `machineAt Nfuel`, `RC.machine-eval` computes that to the embedded `respRHM`, and the
  -- `asResource-sem` retraction + party-irrelevance bridge land it on `respR`.
  ∘ᵍ-MD : (_≈ᵉ_ {M = Dist⊥})
            (strip⊥ (embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality)))
            (embed⊥ respRM)
  ∘ᵍ-MD =
    ≈ᵉ-trans⊥ (strip⊥-cong (∘ᵍ-unfold (embed⊥ mdArrow) (embed⊥ (asResource Comp.Functionality)) Nfuel RC.stableN))
    (≈ᵉ-trans⊥ RC.machine-eval
    (≈ᵉ-trans⊥ (≡→≈ᵉ⊥ (cong (λ h → embed⊥ (respRHM h)) (asResource-sem Comp.Functionality)))
               respRHM-CF≈respRM))
    where module RC = Replay (asResource Comp.Functionality)

  -- The *structural* chaining collision: a coincidence among {IV} ∪ {interior
  -- chaining values} (interior = outputs of NON-final calls, idx < len).  A
  -- collision among FINAL hashes is harmless — those values are never extended,
  -- and the ideal RO has exactly such coincidences.  NOT used by the coupling
  -- below (which raises an explicit flag instead); kept because the eventual
  -- `bad-bound` proof goes  Pr[flag] ≤ Pr[structural collision] ≤ birthday.
  interior : Comp.Table → Comp.Table
  interior []                                   = []
  interior (e@((_ , _ , len , idx) , _) ∷ es) with idx <? len
  ... | yes _ = e ∷ interior es
  ... | no  _ = interior es

  ivEntry : (CV × Blk × ℕ × ℕ) × CV
  ivEntry = ((IV , IV , 0 , 0) , IV)

  -- the collision POOL: {IV} ∪ interior outputs, as an entry list
  poolL : Comp.Table → Comp.Table
  poolL sc = ivEntry ∷ interior sc

  pool : Comp.Table → ℕ
  pool sc = length (poolL sc)

  -- number of colliding pairs in the pool
  collC : Comp.Table → ℚ
  collC sc = Comp.state-collisions (poolL sc)

  bad : Comp.Table → Bool
  bad s = not ⌊ collC s ≟ℚ 0ℚ ⌋

  -- The birthday bound `triangle (q·k) · 2⁻ⁿ` for q queries of k blocks each — the
  -- value proven by `RandomOracle.RO-collision` (same `triangle`, same `inv-pow-2`).
  -- (NB the exponent is the module's hash length n, NOT the query count — an earlier
  -- version shadowed `n` here.)
  bound : ℕ → ℚ
  bound q = Comp.triangle (q * k) *ℚ inv-pow-2 n

  ------------------------------------------------------------------------
  -- The coupling.  Shared state = an explicit bad FLAG, the compression table,
  -- and a GHOST copy of the ideal (general) table.  ONE kernel (`respB`)
  -- produces the state evolution and BOTH answers; the two worlds are its
  -- projections `C.realK` / `C.idealK`:
  --
  --   real answer  = the MD chaining value (always);
  --   ideal answer = for a repeated message the ghost-recorded value; for a new
  --                  message the chaining value itself while unflagged (then it
  --                  is recorded), an independent uniform once flagged.
  --
  -- The flag is raised by the kernel's own freshness checks, EXACTLY when the
  -- MD answer fails to be a fresh uniform:
  --   (i)  the final compression call of a NEW message was a lookup HIT — only
  --        possible after a chaining collision (two chains reached the same
  --        (value, block, position) triple);
  --   (ii) a REPEATED message replayed to a value different from the recorded
  --        one — impossible without an earlier collision (replay through a
  --        grow-only table is deterministic), but checked anyway so that
  --        consistency of the ideal view holds by fiat.
  -- With the checks inside the kernel, `ideal-marginal` (the ideal view IS the
  -- variable-length RO) is PROVEN below by a direct bisimulation with NO
  -- combinatorial invariants; ALL the chain-forest combinatorics lives in
  -- `bad-bound` (flag ⊆ structural collision ⊆ birthday).

  CState : Type
  CState = Comp.Table × General.Table

  FState : Type
  FState = Bool × CState

  -- one compression call, reporting whether it was a lookup hit
  callC' : Comp.Table → CV → Blk → ℕ → Maybe CV → Dist-ℚ (Comp.Table × (CV × Bool))
  callC' s h b idx (just hm) = return-ℚ (s , hm , true)
  callC' s h b idx nothing   =
    Comp.uniform-Out >>=ᴹ λ hm → return-ℚ ((pack h b idx , hm) ∷ s , hm , false)

  callC : Comp.Table → CV → Blk → ℕ → Dist-ℚ (Comp.Table × (CV × Bool))
  callC s h b idx = callC' s h b idx (Comp.lookup-bs s (pack h b idx))

  -- the chain walk; the reported Bool says whether the FINAL call was a hit
  walk : Comp.Table → CV → List Blk → ℕ → Dist-ℚ (Comp.Table × (CV × Bool))
  walk s h []               idx = return-ℚ (s , h , true)   -- no call ⇒ NOT fresh
  walk s h (b ∷ [])         idx = callC s h b idx
  walk s h (b ∷ bs@(_ ∷ _)) idx =
    callC s h b idx >>=ᴹ λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs (suc idx)

  -- answer/record for a NEW message: flagged → an independent uniform;
  -- unflagged → the (necessarily fresh) chaining value itself
  newAns : Fin p → Vec Bool (k * n) → General.Table
         → Bool → Comp.Table → CV
         → Dist-ℚ (FState × (General.Output × General.Output))
  newAns i M sg true  sc' hR = Comp.uniform-Out >>=ᴹ λ u →
    return-ℚ ((true , sc' , (M , u) ∷ sg) , ((i , hR) , (i , u)))
  newAns i M sg false sc' hR =
    return-ℚ ((false , sc' , (M , hR) ∷ sg) , ((i , hR) , (i , hR)))

  respB' : Fin p → Vec Bool (k * n) → FState → Maybe CV
         → Dist-ℚ (FState × (General.Output × General.Output))
  respB' i M (f , sc , sg) (just h) =          -- repeat: check replay consistency
    walk sc IV (toBlocks M) 1 >>=ᴹ λ w →
    return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f , proj₁ w , sg)
             , ((i , proj₁ (proj₂ w)) , (i , h)))
  respB' i M (f , sc , sg) nothing =           -- new: check final-call freshness
    walk sc IV (toBlocks M) 1 >>=ᴹ λ w →
    newAns i M sg (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))

  respB : FState → General.Input → Dist-ℚ (FState × (General.Output × General.Output))
  respB s (i , M) = respB' i M s (General.lookup-bs (proj₂ (proj₂ s)) M)

  module C = Coupling {St = FState} proj₁ respB

  -- the ideal machine's reactive kernel, LITERALLY the functionality's step
  respG : General.Table → General.Input → Dist-ℚ (General.Table × General.Output)
  respG sg q = General.step (sg , q)

  private
    -- one call's (table , value) marginal agrees with `Comp.step`
    callC-marg : ∀ sc h b idx (P : Comp.Table × CV → ℚ)
               → E (callC sc h b idx) (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w)))
               ≡ E (Comp.step (sc , i₀ , pack h b idx)) (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o)))
    callC-marg sc h b idx P with Comp.lookup-bs sc (pack h b idx)
    ... | just hm = trans (lookupᴰℚ-return (sc , hm , true)
                            (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
                          (sym (lookupᴰℚ-return (sc , i₀ , hm)
                            (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o)))))
    ... | nothing =
      trans (E-bind Comp.uniform-Out
              (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false))
              (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
     (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out)
              (λ hm → lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , hm , false)
                        (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w)))))
     (sym (trans (E-bind Comp.uniform-Out
                   (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , i₀ , hm))
                   (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o))))
                 (lookupᴰℚ-cong-P (entries Comp.uniform-Out)
                   (λ hm → lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , i₀ , hm)
                             (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o))))))))

    -- the walk's (table , final value) marginal is exactly `mdRun`
    walkR : ∀ sc h bs idx (P : Comp.Table × CV → ℚ)
          → E (walk sc h bs idx) (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w)))
          ≡ E (mdRun sc h bs idx) P
    walkR sc h [] idx P =
      trans (lookupᴰℚ-return (sc , h , true) (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
            (sym (lookupᴰℚ-return (sc , h) P))
    walkR sc h (b ∷ []) idx P =
      trans (callC-marg sc h b idx P)
     (trans (lookupᴰℚ-cong-P (entries (Comp.step (sc , i₀ , pack h b idx)))
              (λ (o : Comp.Table × Comp.Output) → sym (lookupᴰℚ-return (proj₁ o , proj₂ (proj₂ o)) P)))
            (sym (E-bind (Comp.step (sc , i₀ , pack h b idx))
                   (λ (o : Comp.Table × Comp.Output) → mdRun (proj₁ o) (proj₂ (proj₂ o)) [] (suc idx)) P)))
    walkR sc h (b ∷ b' ∷ bs) idx P =
      trans (E-bind (callC sc h b idx)
              (λ (w : Comp.Table × (CV × Bool)) → walk (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx))
              (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
     (trans (lookupᴰℚ-cong-P (entries (callC sc h b idx))
              (λ (w : Comp.Table × (CV × Bool)) → walkR (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx) P))
     (trans (callC-marg sc h b idx
              (λ (sh : Comp.Table × CV) → E (mdRun (proj₁ sh) (proj₂ sh) (b' ∷ bs) (suc idx)) P))
            (sym (E-bind (Comp.step (sc , i₀ , pack h b idx))
                   (λ (o : Comp.Table × Comp.Output) → mdRun (proj₁ o) (proj₂ (proj₂ o)) (b' ∷ bs) (suc idx)) P))))

  -- The flag and the ghost table are invisible to the real world: erasing them
  -- gives back the plain MD kernel `respR`.  PROVEN — the flagged branch's extra
  -- uniform sampling is marginalised away by `E-const` (mass 1).
  ghost-erase : ∀ f sc sg d
              → Pr₁ (runWith C.realK (f , sc , sg) d) ≡ Pr₁ (runWith respR sc d)
  ghost-erase f sc sg (out b) = refl
  ghost-erase f sc sg (ask (i , M) k) with General.lookup-bs sg M
  ... | just h =
      trans (Pr₁-bind (Dmap C.fR (respB' i M (f , sc , sg) (just h))) KRc)
     (trans (lookupᴰℚ-Dmap C.fR (respB' i M (f , sc , sg) (just h)) (λ sr → Pr₁ (KRc sr)))
     (trans (E-bind μW
              (λ (w : Comp.Table × (CV × Bool)) → return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f , proj₁ w , sg)
                              , ((i , proj₁ (proj₂ w)) , (i , h))))
              (λ t → Pr₁ (KRc (C.fR t))))
     (trans (lookupᴰℚ-cong-P (entries μW)
              (λ (w : Comp.Table × (CV × Bool)) → lookupᴰℚ-return
                       (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f , proj₁ w , sg)
                       , ((i , proj₁ (proj₂ w)) , (i , h)))
                       (λ t → Pr₁ (KRc (C.fR t)))))
     (trans (lookupᴰℚ-cong-P (entries μW)
              (λ (w : Comp.Table × (CV × Bool)) → ghost-erase ((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f) (proj₁ w) sg
                       (k (i , proj₁ (proj₂ w)))))
     (trans (walkR sc IV (toBlocks M) 1
              (λ (sh : Comp.Table × CV) → Pr₁ (runWith respR (proj₁ sh) (k (i , proj₂ sh)))))
     (trans (sym (lookupᴰℚ-cong-P (entries μM)
              (λ (sh : Comp.Table × CV) → lookupᴰℚ-return (proj₁ sh , (i , proj₂ sh)) (λ sr → Pr₁ (KR' sr)))))
            (sym (trans (Pr₁-bind (respR sc (i , M)) KR')
                        (E-bind μM (λ (sh : Comp.Table × CV) → return-ℚ (proj₁ sh , (i , proj₂ sh)))
                          (λ sr → Pr₁ (KR' sr)))))))))))
    where
      KRc = λ (sr : FState × General.Output) → runWith C.realK (proj₁ sr) (k (proj₂ sr))
      KR' = λ (sr : Comp.Table × General.Output) → runWith respR (proj₁ sr) (k (proj₂ sr))
      μW  = walk sc IV (toBlocks M) 1
      μM  = mdRun sc IV (toBlocks M) 1
  ... | nothing =
      trans (Pr₁-bind (Dmap C.fR (respB' i M (f , sc , sg) nothing)) KRc)
     (trans (lookupᴰℚ-Dmap C.fR (respB' i M (f , sc , sg) nothing) (λ sr → Pr₁ (KRc sr)))
     (trans (E-bind μW
              (λ (w : Comp.Table × (CV × Bool)) → newAns i M sg (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w)))
              (λ t → Pr₁ (KRc (C.fR t))))
     (trans (lookupᴰℚ-cong-P (entries μW)
              (λ (w : Comp.Table × (CV × Bool)) → newAnsE (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))))
     (trans (walkR sc IV (toBlocks M) 1
              (λ (sh : Comp.Table × CV) → Pr₁ (runWith respR (proj₁ sh) (k (i , proj₂ sh)))))
     (trans (sym (lookupᴰℚ-cong-P (entries μM)
              (λ (sh : Comp.Table × CV) → lookupᴰℚ-return (proj₁ sh , (i , proj₂ sh)) (λ sr → Pr₁ (KR' sr)))))
            (sym (trans (Pr₁-bind (respR sc (i , M)) KR')
                        (E-bind μM (λ (sh : Comp.Table × CV) → return-ℚ (proj₁ sh , (i , proj₂ sh)))
                          (λ sr → Pr₁ (KR' sr))))))))))
    where
      KRc = λ (sr : FState × General.Output) → runWith C.realK (proj₁ sr) (k (proj₂ sr))
      KR' = λ (sr : Comp.Table × General.Output) → runWith respR (proj₁ sr) (k (proj₂ sr))
      μW  = walk sc IV (toBlocks M) 1
      μM  = mdRun sc IV (toBlocks M) 1
      -- the real marginal of `newAns` ignores flag and ghost
      newAnsE : ∀ bb sc' hRv
              → E (newAns i M sg bb sc' hRv) (λ t → Pr₁ (KRc (C.fR t)))
              ≡ Pr₁ (runWith respR sc' (k (i , hRv)))
      newAnsE true sc' hRv =
        trans (E-bind Comp.uniform-Out
                (λ u → return-ℚ ((true , sc' , (M , u) ∷ sg) , ((i , hRv) , (i , u))))
                (λ t → Pr₁ (KRc (C.fR t))))
       (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ u →
                trans (lookupᴰℚ-return ((true , sc' , (M , u) ∷ sg) , ((i , hRv) , (i , u)))
                        (λ t → Pr₁ (KRc (C.fR t))))
                      (ghost-erase true sc' ((M , u) ∷ sg) (k (i , hRv)))))
              (E-const Comp.uniform-Out (Pr₁ (runWith respR sc' (k (i , hRv))))))
      newAnsE false sc' hRv =
        trans (lookupᴰℚ-return ((false , sc' , (M , hRv) ∷ sg) , ((i , hRv) , (i , hRv)))
                (λ t → Pr₁ (KRc (C.fR t))))
              (ghost-erase false sc' ((M , hRv) ∷ sg) (k (i , hRv)))

  private
    -- ★ FRESHNESS DETACHMENT: walking the chain and testing `G` on the final
    -- value — with the uniform average produced instead whenever the final call
    -- HIT or the flag was already up — IS the uniform average.  At a fresh final
    -- call the sampled value detaches as one uniform draw; every earlier step
    -- either recurses (hit) or averages out (miss, `E-const`).
    -- the detachment integrand
    dInt : (CV → ℚ) → Bool → Comp.Table × (CV × Bool) → ℚ
    dInt G f w = cond (proj₂ (proj₂ w) ∨ f) (E Comp.uniform-Out G) (G (proj₁ (proj₂ w)))

    -- casing on the flag once and for all: averaging `G` under `cond f` is the average
    condE : ∀ (G : CV → ℚ) f
          → E Comp.uniform-Out (λ hm → cond f (E Comp.uniform-Out G) (G hm))
          ≡ E Comp.uniform-Out G
    condE G true  = E-const Comp.uniform-Out (E Comp.uniform-Out G)
    condE G false = refl

    -- forward declarations (detach ↔ detachC are mutually recursive; passing the
    -- lookup result as an ARGUMENT keeps the recursion structurally decreasing)
    detach : ∀ (G : CV → ℚ) f sc h bs idx
           → E (walk sc h bs idx) (dInt G f) ≡ E Comp.uniform-Out G
    detachL : ∀ (G : CV → ℚ) f sc h b idx (m : Maybe CV)
            → E (callC' sc h b idx m) (dInt G f) ≡ E Comp.uniform-Out G
    detachC : ∀ (G : CV → ℚ) f sc h b bs' idx (m : Maybe CV)
            → E (callC' sc h b idx m >>=ᴹ
                  (λ (w : Comp.Table × (CV × Bool)) →
                     walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)))
                (dInt G f)
            ≡ E Comp.uniform-Out G

    detach G f sc h [] idx = lookupᴰℚ-return (sc , h , true) (dInt G f)
    detach G f sc h (b ∷ []) idx =
      detachL G f sc h b idx (Comp.lookup-bs sc (pack h b idx))
    detach G f sc h (b ∷ b' ∷ bs) idx =
      detachC G f sc h b (b' ∷ bs) idx (Comp.lookup-bs sc (pack h b idx))

    -- the LAST call: a hit is (flagged ⇒) the constant average; a miss detaches
    -- the fresh uniform sample as THE uniform draw.
    detachL G f sc h b idx (just hm) = lookupᴰℚ-return (sc , hm , true) (dInt G f)
    detachL G f sc h b idx nothing =
      trans (E-bind Comp.uniform-Out
              (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false)) (dInt G f))
     (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out)
              (λ hm → lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , hm , false) (dInt G f)))
            (condE G f))

    -- an INTERIOR call: recurse on a hit, average out the fresh sample on a miss.
    detachC G f sc h b bs' idx (just hm) =
      trans (E-bind (return-ℚ (sc , hm , true))
              (λ (w : Comp.Table × (CV × Bool)) →
                 walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (dInt G f))
     (trans (lookupᴰℚ-return (sc , hm , true)
              (λ (w : Comp.Table × (CV × Bool)) →
                 E (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (dInt G f)))
            (detach G f sc hm bs' (suc idx)))
    detachC G f sc h b bs' idx nothing =
      trans (E-bind (Comp.uniform-Out >>=ᴹ
                      (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false)))
              (λ (w : Comp.Table × (CV × Bool)) →
                 walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (dInt G f))
     (trans (E-bind Comp.uniform-Out
              (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false))
              (λ (w : Comp.Table × (CV × Bool)) →
                 E (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (dInt G f)))
     (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out)
              (λ hm → lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , hm , false)
                        (λ (w : Comp.Table × (CV × Bool)) →
                           E (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (dInt G f))))
     (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out)
              (λ hm → detach G f ((pack h b idx , hm) ∷ sc) hm bs' (suc idx)))
            (E-const Comp.uniform-Out (E Comp.uniform-Out G)))))

    -- ★ THE KEY LEMMA, generalized: from ANY flag/compression state whose ghost
    -- table agrees with the RO's table, the ideal view IS the RO.  A bisimulation
    -- over the distinguisher; the flag checks make every case pointwise.
    ideal-marginal-gen : ∀ d f sc sgG
      → Pr₁ (runWith respG sgG d) ≡ Pr₁ (runWith C.idealK (f , sc , sgG) d)
    ideal-marginal-gen (out b) f sc sgG = refl
    ideal-marginal-gen (ask (i , M) k) f sc sgG with General.lookup-bs sgG M
    ... | just h =
        trans (Pr₁-bind (return-ℚ (sgG , i , h)) KG)
       (trans (lookupᴰℚ-return (sgG , i , h) (λ o → Pr₁ (KG o)))
       (trans (sym (E-const μW (Pr₁ (runWith respG sgG (k (i , h))))))
       (trans (sym (lookupᴰℚ-cong-P (entries μW) pointRep))
       (trans (sym (lookupᴰℚ-cong-P (entries μW)
                     (λ (w : Comp.Table × (CV × Bool)) → lookupᴰℚ-return (tupR w) (λ t → Pr₁ (KIc (C.fI t))))))
       (trans (sym (E-bind μW (λ (w : Comp.Table × (CV × Bool)) → return-ℚ (tupR w)) (λ t → Pr₁ (KIc (C.fI t)))))
       (trans (sym (lookupᴰℚ-Dmap C.fI (respB' i M (f , sc , sgG) (just h))
                     (λ sr → Pr₁ (KIc sr))))
              (sym (Pr₁-bind (Dmap C.fI (respB' i M (f , sc , sgG) (just h))) KIc))))))))
      where
        KG  = λ (o : General.Table × General.Output) → runWith respG (proj₁ o) (k (proj₂ o))
        KIc = λ (sr : FState × General.Output) → runWith C.idealK (proj₁ sr) (k (proj₂ sr))
        μW  = walk sc IV (toBlocks M) 1
        tupR : Comp.Table × (CV × Bool) → FState × (General.Output × General.Output)
        tupR w = (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f , proj₁ w , sgG)
                 , ((i , proj₁ (proj₂ w)) , (i , h)))
        -- pointwise: the repeated answer is the recorded one in EVERY branch —
        -- unflagged because the consistency check passed, flagged by fiat.
        pointRep : ∀ w → Pr₁ (KIc (C.fI (tupR w))) ≡ Pr₁ (runWith respG sgG (k (i , h)))
        pointRep w with proj₁ (proj₂ w) ≟ h
        ... | yes q =
          trans (cong (λ v → Pr₁ (runWith C.idealK (f , proj₁ w , sgG)
                                    (k (cond f (i , h) (i , v))))) q)
         (trans (cong (λ z → Pr₁ (runWith C.idealK (f , proj₁ w , sgG) (k z)))
                  (cond-diag f (i , h)))
                (sym (ideal-marginal-gen (k (i , h)) f (proj₁ w) sgG)))
        ... | no ¬q = sym (ideal-marginal-gen (k (i , h)) true (proj₁ w) sgG)
    ... | nothing =
        trans (Pr₁-bind (General.uniform-Out >>=ᴹ retG) KG)
       (trans (E-bind General.uniform-Out retG (λ o → Pr₁ (KG o)))
       (trans (lookupᴰℚ-cong-P (entries General.uniform-Out)
                (λ (u : CV) → lookupᴰℚ-return ((M , u) ∷ sgG , i , u) (λ o → Pr₁ (KG o))))
       (trans (sym (detach G₀ f sc IV (toBlocks M) 1))
       (trans (sym (lookupᴰℚ-cong-P (entries μW) pointNew))
       (trans (sym (E-bind μW
                     (λ (w : Comp.Table × (CV × Bool)) → newAns i M sgG (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w)))
                     (λ t → Pr₁ (KIc (C.fI t)))))
       (trans (sym (lookupᴰℚ-Dmap C.fI (respB' i M (f , sc , sgG) nothing)
                     (λ sr → Pr₁ (KIc sr))))
              (sym (Pr₁-bind (Dmap C.fI (respB' i M (f , sc , sgG) nothing)) KIc))))))))
      where
        KG   = λ (o : General.Table × General.Output) → runWith respG (proj₁ o) (k (proj₂ o))
        KIc  = λ (sr : FState × General.Output) → runWith C.idealK (proj₁ sr) (k (proj₂ sr))
        μW   = walk sc IV (toBlocks M) 1
        retG = λ (u : CV) → return-ℚ ((M , u) ∷ sgG , i , u)
        G₀ : CV → ℚ
        G₀ u = Pr₁ (runWith respG ((M , u) ∷ sgG) (k (i , u)))
        -- pointwise value of a NEW answer: uniform average when flagged,
        -- `G₀` of the (fresh) chaining value when not.
        newAnsVal : ∀ bb sc' hRv
          → E (newAns i M sgG bb sc' hRv) (λ t → Pr₁ (KIc (C.fI t)))
          ≡ cond bb (E Comp.uniform-Out G₀) (G₀ hRv)
        newAnsVal true sc' hRv =
          trans (E-bind Comp.uniform-Out
                  (λ u → return-ℚ ((true , sc' , (M , u) ∷ sgG) , ((i , hRv) , (i , u))))
                  (λ t → Pr₁ (KIc (C.fI t))))
                (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ u →
                   trans (lookupᴰℚ-return
                           ((true , sc' , (M , u) ∷ sgG) , ((i , hRv) , (i , u)))
                           (λ t → Pr₁ (KIc (C.fI t))))
                         (sym (ideal-marginal-gen (k (i , u)) true sc' ((M , u) ∷ sgG)))))
        newAnsVal false sc' hRv =
          trans (lookupᴰℚ-return
                  ((false , sc' , (M , hRv) ∷ sgG) , ((i , hRv) , (i , hRv)))
                  (λ t → Pr₁ (KIc (C.fI t))))
                (sym (ideal-marginal-gen (k (i , hRv)) false sc' ((M , hRv) ∷ sgG)))
        pointNew : ∀ w
          → E (newAns i M sgG (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w)))
              (λ t → Pr₁ (KIc (C.fI t)))
          ≡ cond (proj₂ (proj₂ w) ∨ f) (E Comp.uniform-Out G₀) (G₀ (proj₁ (proj₂ w)))
        pointNew w = newAnsVal (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))

  -- ★ THE KEY LEMMA, PROVEN: the coupling's ideal view IS the variable-length
  -- random oracle — EXACTLY, not up to ε (the ε lives only in FLGP/bad-bound).
  ideal-marginal : ∀ d
    → Pr₁ (runWith respG [] d) ≡ Pr₁ (runWith C.idealK (false , [] , []) d)
  ideal-marginal d = ideal-marginal-gen d false [] []

  -- ⟦General⟧-sem: DERIVED from `liftFun-sem` + `asResource-sem` + the embed/strip
  -- commutation (`strip-embed-swap`), then bridged to the total `Dist-ℚ` run.
  -- `run General.Functionality d` is definitionally `runWith respG [] d`.
  ⟦General⟧-sem : ∀ d → Pr₁⊥ (run⊥ ⟦ General.M ⟧cl d) ≡ Pr₁ (runWith respG [] d)
  ⟦General⟧-sem d =
    trans (Pr₁⊥-cong (run⊥ ⟦ General.M ⟧cl d) (Dmap just (run General.Functionality d))
            (Mℚ.trans {i = run⊥ ⟦ General.M ⟧cl d}
                      {j = run⊥ (embed⊥ General.Functionality) d}
                      {k = Dmap just (run General.Functionality d)}
               (≈ᵉ⇒run {f = ⟦ General.M ⟧cl} {embed⊥ General.Functionality} sem≈ d)
               (run⊥-embed General.Functionality d)))
          (Pr₁⊥-just (run General.Functionality d))
    where
      sem≈ : (_≈ᵉ_ {M = Dist⊥}) ⟦ General.M ⟧cl (embed⊥ General.Functionality)
      sem≈ = subst₂ (_≈ᵉ_ {M = Dist⊥})
               (sym (cong strip⊥ (liftFun-sem (asResource General.Functionality))))
               (cong embed⊥ (asResource-sem General.Functionality))
               (strip-embed-swap (asResource General.Functionality))

  -- ⟦MD⟧-sem: now a DERIVED THEOREM — `MD ⊚ Comp.M` is a composition, handled by
  -- functoriality `⟦⟧-∘`, the `liftFun-sem` retractions (transported under
  -- `strip⊥`/`_∘ᵍ_`), and the per-machine computation fact `∘ᵍ-MD`.
  -- `run respRM d` is definitionally `runWith respR [] d`.
  ⟦MD⟧-sem : ∀ d → Pr₁⊥ (run⊥ ⟦ MD ⊚ Comp.M ⟧cl d) ≡ Pr₁ (runWith respR [] d)
  ⟦MD⟧-sem d =
    trans (Pr₁⊥-cong (run⊥ ⟦ MD ⊚ Comp.M ⟧cl d) (Dmap just (run respRM d))
            (Mℚ.trans {i = run⊥ ⟦ MD ⊚ Comp.M ⟧cl d}
                      {j = run⊥ (embed⊥ respRM) d}
                      {k = Dmap just (run respRM d)}
               (≈ᵉ⇒run {f = ⟦ MD ⊚ Comp.M ⟧cl} {embed⊥ respRM} sem≈ d)
               (run⊥-embed respRM d)))
          (Pr₁⊥-just (run respRM d))
    where
      step≈ : (_≈ᵉ_ {M = Dist⊥})
                (strip⊥ ⟦ MD ⊚ Comp.M ⟧)
                (strip⊥ (embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality)))
      step≈ = subst (λ z → (_≈ᵉ_ {M = Dist⊥}) (strip⊥ ⟦ MD ⊚ Comp.M ⟧) (strip⊥ z))
                (cong₂ _∘ᵍ_ (liftFun-sem mdArrow) (liftFun-sem (asResource Comp.Functionality)))
                (strip⊥-cong (⟦⟧-∘ MD Comp.M))
      sem≈ : (_≈ᵉ_ {M = Dist⊥}) ⟦ MD ⊚ Comp.M ⟧cl (embed⊥ respRM)
      sem≈ xs = Mℚ.trans
                  {i = eval ⟦ MD ⊚ Comp.M ⟧cl xs}
                  {j = eval (strip⊥ (embed⊥ mdArrow ∘ᵍ embed⊥ (asResource Comp.Functionality))) xs}
                  {k = eval (embed⊥ respRM) xs}
                  (step≈ xs) (∘ᵍ-MD xs)

  ------------------------------------------------------------------------
  -- THE BIRTHDAY POTENTIAL (design: docs/md-cert-design.md), PROVEN.
  -- φ = collision count + triangle budget for the remaining interior samples.
  -- φ is an EXACT martingale along the walk: an interior miss creates
  -- `pool` expected collision pairs (the PROVEN `E-collisions`) and spends
  -- exactly `pool` from the budget; final calls and hits are free.

  -- sum of `j` consecutive naturals starting at `t` (a triangle slice)
  sumR : ℕ → ℕ → ℚ
  sumR t zero    = 0ℚ
  sumR t (suc j) = fromℕ t +ℚ sumR (suc t) j

  Γ : ℕ → ℕ → ℚ
  Γ t j = sumR t j *ℚ inv-pow-2 n

  φsc : ℕ → Comp.Table → ℚ
  φsc m sc = collC sc +ℚ Γ (pool sc) (m * (k ∸ 1))

  φMD : ℕ → FState → ℚ
  φMD m s = φsc m (proj₁ (proj₂ s))

  private
    -- ℚ order basics
    0≤fromℕ : ∀ j → 0ℚ ≤ℚ fromℕ j
    0≤fromℕ zero    = ≤-refl
    0≤fromℕ (suc j) = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                              (+-mono-≤ 0≤1ℚ (0≤fromℕ j))

    -- literal-free: `inv-pow-2 n` is the uniform point-mass (P-uniform-Vec),
    -- and expectations of non-negative indicators are non-negative.
    0≤ε : 0ℚ ≤ℚ inv-pow-2 n
    0≤ε = subst (0ℚ ≤ℚ_) (P-uniform-Vec n h₀)
            (≤-trans (≤-reflexive (sym (E-const Comp.uniform-Out 0ℚ)))
                     (E-mono Comp.uniform-Out (λ _ → 0ℚ) (δ h₀)
                             (λ x → 0≤bool ⌊ x ≟ h₀ ⌋)))
      where h₀ = replicateᵛ n false

    x≤x+c : ∀ x {c} → 0ℚ ≤ℚ c → x ≤ℚ x +ℚ c
    x≤x+c x 0≤c = ≤-trans (≤-reflexive (sym (+-identityʳ x))) (+-monoʳ-≤ x 0≤c)

    x≤c+x : ∀ x {c} → 0ℚ ≤ℚ c → x ≤ℚ c +ℚ x
    x≤c+x x 0≤c = ≤-trans (≤-reflexive (sym (+-identityˡ x))) (+-monoˡ-≤ x 0≤c)

    0≤sumR : ∀ t j → 0ℚ ≤ℚ sumR t j
    0≤sumR t zero    = ≤-refl
    0≤sumR t (suc j) = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                               (+-mono-≤ (0≤fromℕ t) (0≤sumR (suc t) j))

    0≤Γ : ∀ t j → 0ℚ ≤ℚ Γ t j
    0≤Γ t j = ≤-trans (≤-reflexive (sym (*-zeroˡ (inv-pow-2 n))))
                      (*-monoʳ-≤-nonNeg _ ⦃ nonNegative 0≤ε ⦄ (0≤sumR t j))

    sumR-≤-suc : ∀ t j → sumR t j ≤ℚ sumR t (suc j)
    sumR-≤-suc t zero    = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                   (+-mono-≤ (0≤fromℕ t) ≤-refl)
    sumR-≤-suc t (suc j) = +-monoʳ-≤ (fromℕ t) (sumR-≤-suc (suc t) j)

    sumR-mono : ∀ t {j j'} → j ≤ j' → sumR t j ≤ℚ sumR t j'
    sumR-mono t le = go t _ _ (ℕP.≤⇒≤′ le)
      where go : ∀ t j j' → j ≤′ j' → sumR t j ≤ℚ sumR t j'
            go t j .j ≤′-refl        = ≤-refl
            go t j _ (≤′-step {j'} pf) = ≤-trans (go t j j' pf) (sumR-≤-suc t j')

    Γ-≤-suc : ∀ t j → Γ t j ≤ℚ Γ t (suc j)
    Γ-≤-suc t j = *-monoʳ-≤-nonNeg _ ⦃ nonNegative 0≤ε ⦄ (sumR-≤-suc t j)

    Γ-step : ∀ t j → fromℕ t *ℚ inv-pow-2 n +ℚ Γ (suc t) j ≡ Γ t (suc j)
    Γ-step t j = sym (*-distribʳ-+ (inv-pow-2 n) (fromℕ t) (sumR (suc t) j))

    -- triangle facts
    tri-mono : ∀ {a b} → a ≤ b → Comp.triangle a ≤ℚ Comp.triangle b
    tri-mono le = go _ _ (ℕP.≤⇒≤′ le)
      where go : ∀ a b → a ≤′ b → Comp.triangle a ≤ℚ Comp.triangle b
            go a .a ≤′-refl        = ≤-refl
            go a _ (≤′-step {b} pf) = ≤-trans (go a b pf) (x≤c+x _ (0≤fromℕ b))

    sumR-tri : ∀ t j → Comp.triangle t +ℚ sumR t j ≡ Comp.triangle (t + j)
    sumR-tri t zero    = trans (+-identityʳ _) (cong Comp.triangle (sym (ℕP.+-identityʳ t)))
    sumR-tri t (suc j) =
      trans (sym (+-assoc (Comp.triangle t) (fromℕ t) (sumR (suc t) j)))
     (trans (cong (_+ℚ sumR (suc t) j) (+-comm (Comp.triangle t) (fromℕ t)))
     (trans (sumR-tri (suc t) j) (cong Comp.triangle (sym (ℕP.+-suc t j)))))

    -- counting facts
    cm-nn : ∀ s h → 0ℚ ≤ℚ Comp.count-matches s h
    cm-nn []            h = ≤-refl
    cm-nn ((_ , v) ∷ s) h = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                    (+-mono-≤ (0≤bool ⌊ h ≟ v ⌋) (cm-nn s h))

    sc-nn : ∀ s → 0ℚ ≤ℚ Comp.state-collisions s
    sc-nn []            = ≤-refl
    sc-nn ((_ , v) ∷ s) = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                  (+-mono-≤ (cm-nn s v) (sc-nn s))

    δ-sym : ∀ (x y : CV) → δ x y ≡ δ y x
    δ-sym x y with y ≟ x | x ≟ y
    ... | yes _ | yes _ = refl
    ... | yes p | no ¬q = ⊥-elim (¬q (sym p))
    ... | no ¬p | yes q = ⊥-elim (¬p (sym q))
    ... | no _  | no _  = refl

    +-inter : ∀ a b c d → (a +ℚ b) +ℚ (c +ℚ d) ≡ (a +ℚ c) +ℚ (b +ℚ d)
    +-inter a b c d =
      trans (+-assoc a b (c +ℚ d))
     (trans (cong (a +ℚ_) (sym (+-assoc b c d)))
     (trans (cong (λ z → a +ℚ (z +ℚ d)) (+-comm b c))
     (trans (cong (a +ℚ_) (+-assoc c b d))
            (sym (+-assoc a c (b +ℚ d))))))

    +-lswap : ∀ a b c → a +ℚ (b +ℚ c) ≡ b +ℚ (a +ℚ c)
    +-lswap a b c = trans (sym (+-assoc a b c))
                   (trans (cong (_+ℚ c) (+-comm a b)) (+-assoc b a c))

    -- table-shape facts
    interior-cons< : ∀ hh bb ii vv sc → ii < k
      → interior (((hh , bb , k , ii) , vv) ∷ sc) ≡ ((hh , bb , k , ii) , vv) ∷ interior sc
    interior-cons< hh bb ii vv sc lt with ii <? k
    ... | yes _  = refl
    ... | no ¬lt = ⊥-elim (¬lt lt)

    interior-consᶠ : ∀ hh bb ii vv sc → ¬ (ii < k)
      → interior (((hh , bb , k , ii) , vv) ∷ sc) ≡ interior sc
    interior-consᶠ hh bb ii vv sc ¬lt with ii <? k
    ... | yes lt = ⊥-elim (¬lt lt)
    ... | no _   = refl

    collC-cons< : ∀ hh bb ii vv sc → ii < k
      → collC (((hh , bb , k , ii) , vv) ∷ sc)
      ≡ Comp.count-matches (poolL sc) vv +ℚ collC sc
    collC-cons< hh bb ii vv sc lt =
      trans (cong (λ z → Comp.state-collisions (ivEntry ∷ z))
              (interior-cons< hh bb ii vv sc lt))
     (trans (cong (_+ℚ (Comp.count-matches (interior sc) vv
                        +ℚ Comp.state-collisions (interior sc)))
              (cong (_+ℚ Comp.count-matches (interior sc) IV) (δ-sym vv IV)))
            (+-inter (δ IV vv) (Comp.count-matches (interior sc) IV)
                     (Comp.count-matches (interior sc) vv)
                     (Comp.state-collisions (interior sc))))

    collC-consᶠ : ∀ hh bb ii vv sc → ¬ (ii < k)
      → collC (((hh , bb , k , ii) , vv) ∷ sc) ≡ collC sc
    collC-consᶠ hh bb ii vv sc ¬lt =
      cong (λ z → Comp.state-collisions (ivEntry ∷ z)) (interior-consᶠ hh bb ii vv sc ¬lt)

    pool-cons< : ∀ hh bb ii vv sc → ii < k
      → pool (((hh , bb , k , ii) , vv) ∷ sc) ≡ suc (pool sc)
    pool-cons< hh bb ii vv sc lt =
      cong (λ z → length (ivEntry ∷ z)) (interior-cons< hh bb ii vv sc lt)

    pool-consᶠ : ∀ hh bb ii vv sc → ¬ (ii < k)
      → pool (((hh , bb , k , ii) , vv) ∷ sc) ≡ pool sc
    pool-consᶠ hh bb ii vv sc ¬lt =
      cong (λ z → length (ivEntry ∷ z)) (interior-consᶠ hh bb ii vv sc ¬lt)

    len-toList : ∀ {A : Type} {j} (v : Vec A j) → length (toList v) ≡ j
    len-toList []      = refl
    len-toList (_ ∷ v) = cong suc (len-toList v)

    suc∸1 : ∀ j → .⦃ _ : NonZero j ⦄ → suc (j ∸ 1) ≡ j
    suc∸1 zero    = ⊥-elim (≢-nonZero⁻¹ zero refl)
    suc∸1 (suc j) = refl

    -- ★ THE WALK MARTINGALE (design §1) — forward-declared, detach-style
    walk-φ : ∀ m sc h bs idx → idx + length bs ≡ suc k
           → E (walk sc h bs idx) (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w))
           ≤ℚ collC sc +ℚ Γ (pool sc) ((length bs ∸ 1) + m * (k ∸ 1))
    walk-φL : ∀ m sc h b idx (mv : Maybe CV) → ¬ (idx < k)
            → E (callC' sc h b idx mv) (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)) ≤ℚ φsc m sc
    walk-φC : ∀ m sc h b bs' idx (mv : Maybe CV) → idx < k
            → suc idx + length bs' ≡ suc k
            → E (callC' sc h b idx mv >>=ᴹ
                  (λ (w : Comp.Table × (CV × Bool)) →
                     walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)))
                (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w))
            ≤ℚ collC sc +ℚ Γ (pool sc) (length bs' + m * (k ∸ 1))

    walk-φ m sc h [] idx pr =
      ≤-reflexive (lookupᴰℚ-return (sc , h , true) (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
    walk-φ m sc h (b ∷ []) idx pr =
      walk-φL m sc h b idx (Comp.lookup-bs sc (pack h b idx)) (ℕP.<-irrefl idx≡k)
      where
        idx≡k : idx ≡ k
        idx≡k = ℕP.suc-injective
          (trans (cong suc (sym (ℕP.+-identityʳ idx)))
                 (trans (sym (ℕP.+-suc idx zero)) pr))
    walk-φ m sc h (b ∷ b' ∷ bs) idx pr =
      walk-φC m sc h b (b' ∷ bs) idx (Comp.lookup-bs sc (pack h b idx)) lt (cong suc eq)
      where
        eq : idx + suc (length bs) ≡ k
        eq = ℕP.suc-injective (trans (sym (ℕP.+-suc idx (suc (length bs)))) pr)
        lt : idx < k
        lt = ℕP.≤-trans (ℕP.m<m+n idx ℕP.0<1+n) (ℕP.≤-reflexive eq)

    walk-φL m sc h b idx (just hm) _ =
      ≤-reflexive (lookupᴰℚ-return (sc , hm , true) (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
    walk-φL m sc h b idx nothing ¬lt = ≤-reflexive
      (trans (E-bind Comp.uniform-Out
               (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false))
               (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
      (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ hm →
                trans (lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , hm , false)
                        (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
                      (cong₂ (λ x y → x +ℚ Γ y (m * (k ∸ 1)))
                        (collC-consᶠ h b idx hm sc ¬lt)
                        (pool-consᶠ h b idx hm sc ¬lt))))
             (E-const Comp.uniform-Out (φsc m sc))))

    walk-φC m sc h b [] idx mv lt pr =
      ⊥-elim (ℕP.<-irrefl
        (trans (sym (ℕP.+-identityʳ idx)) (ℕP.suc-injective pr)) lt)
    walk-φC m sc h b (b'' ∷ bs'') idx (just hm) lt pr =
      ≤-trans (≤-reflexive
        (trans (E-bind (return-ℚ (sc , hm , true))
                 (λ (w : Comp.Table × (CV × Bool)) →
                    walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                 (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
               (lookupᴰℚ-return (sc , hm , true)
                 (λ (w : Comp.Table × (CV × Bool)) →
                    E (walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                      (λ (w' : Comp.Table × (CV × Bool)) → φsc m (proj₁ w'))))))
      (≤-trans (walk-φ m sc hm (b'' ∷ bs'') (suc idx) pr)
               (+-monoʳ-≤ (collC sc) (Γ-≤-suc (pool sc) (length bs'' + m * (k ∸ 1)))))
    walk-φC m sc h b (b'' ∷ bs'') idx nothing lt pr =
      ≤-trans (≤-reflexive
        (trans (E-bind (Comp.uniform-Out >>=ᴹ
                         (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false)))
                 (λ (w : Comp.Table × (CV × Bool)) →
                    walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                 (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
        (trans (E-bind Comp.uniform-Out
                 (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false))
                 (λ (w : Comp.Table × (CV × Bool)) →
                    E (walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                      (λ (w' : Comp.Table × (CV × Bool)) → φsc m (proj₁ w'))))
               (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ hm →
                  lookupᴰℚ-return ((pack h b idx , hm) ∷ sc , hm , false)
                    (λ (w : Comp.Table × (CV × Bool)) →
                       E (walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                         (λ (w' : Comp.Table × (CV × Bool)) → φsc m (proj₁ w'))))))))
      (≤-trans (E-mono Comp.uniform-Out
                 (λ hm → E (walk ((pack h b idx , hm) ∷ sc) hm (b'' ∷ bs'') (suc idx))
                           (λ (w' : Comp.Table × (CV × Bool)) → φsc m (proj₁ w')))
                 (λ hm → collC ((pack h b idx , hm) ∷ sc)
                         +ℚ Γ (pool ((pack h b idx , hm) ∷ sc))
                              ((length (b'' ∷ bs'') ∸ 1) + m * (k ∸ 1)))
                 (λ hm → walk-φ m ((pack h b idx , hm) ∷ sc) hm (b'' ∷ bs'') (suc idx) pr))
       (≤-reflexive
         (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ hm →
                   trans (cong₂ (λ x y → x +ℚ Γ y ((length bs'') + m * (k ∸ 1)))
                           (collC-cons< h b idx hm sc lt)
                           (pool-cons< h b idx hm sc lt))
                         (+-assoc (Comp.count-matches (poolL sc) hm) (collC sc)
                                  (Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))))
         (trans (E-add Comp.uniform-Out
                  (λ hm → Comp.count-matches (poolL sc) hm)
                  (λ _ → collC sc +ℚ Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))
         (trans (cong₂ _+ℚ_
                  (Comp.E-collisions (poolL sc))
                  (E-const Comp.uniform-Out
                    (collC sc +ℚ Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1)))))
         (trans (+-lswap (fromℕ (pool sc) *ℚ inv-pow-2 n) (collC sc)
                         (Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))
                (cong (collC sc +ℚ_)
                  (Γ-step (pool sc) ((length bs'') + m * (k ∸ 1))))))))))

  private
    -- the newAns marginal is φ-constant (ghost/flag/answers don't enter φ)
    newAns-φ : ∀ m i M sg bb sc' hR
             → E (newAns i M sg bb sc' hR) (λ t → φMD m (proj₁ (C.fR t)))
             ≡ φsc m sc'
    newAns-φ m i M sg true sc' hR =
      trans (E-bind Comp.uniform-Out
              (λ u → return-ℚ ((true , sc' , (M , u) ∷ sg) , ((i , hR) , (i , u))))
              (λ t → φMD m (proj₁ (C.fR t))))
     (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ u →
               lookupᴰℚ-return ((true , sc' , (M , u) ∷ sg) , ((i , hR) , (i , u)))
                 (λ t → φMD m (proj₁ (C.fR t)))))
            (E-const Comp.uniform-Out (φsc m sc')))
    newAns-φ m i M sg false sc' hR =
      lookupᴰℚ-return ((false , sc' , (M , hR) ∷ sg) , ((i , hR) , (i , hR)))
        (λ t → φMD m (proj₁ (C.fR t)))

    -- ★ the per-query supermartingale inequality
    φ-step : ∀ m s q → E (C.realK s q) (λ sr → φMD m (proj₁ sr)) ≤ℚ φMD (suc m) s
    φ-step m s (i , M) = aux (General.lookup-bs (proj₂ (proj₂ s)) M)
      where
        pr : 1 + length (toBlocks M) ≡ suc k
        pr = cong suc (len-toList (chunk k M))
        tail-eq : (length (toBlocks M) ∸ 1) + m * (k ∸ 1) ≡ suc m * (k ∸ 1)
        tail-eq = cong (λ z → (z ∸ 1) + m * (k ∸ 1)) (len-toList (chunk k M))
        aux : (mv : Maybe CV)
            → E (Dmap C.fR (respB' i M s mv)) (λ sr → φMD m (proj₁ sr))
            ≤ℚ φMD (suc m) s
        aux (just h) =
          ≤-trans (≤-reflexive
            (trans (lookupᴰℚ-Dmap C.fR (respB' i M s (just h)) (λ sr → φMD m (proj₁ sr)))
            (trans (E-bind (walk (proj₁ (proj₂ s)) IV (toBlocks M) 1)
                     (λ w → return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ proj₁ s
                                       , proj₁ w , proj₂ (proj₂ s))
                                     , ((i , proj₁ (proj₂ w)) , (i , h))))
                     (λ t → φMD m (proj₁ (C.fR t))))
                   (lookupᴰℚ-cong-P (entries (walk (proj₁ (proj₂ s)) IV (toBlocks M) 1))
                     (λ w → lookupᴰℚ-return
                              (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ proj₁ s
                                , proj₁ w , proj₂ (proj₂ s))
                              , ((i , proj₁ (proj₂ w)) , (i , h)))
                              (λ t → φMD m (proj₁ (C.fR t))))))))
          (≤-trans (walk-φ m (proj₁ (proj₂ s)) IV (toBlocks M) 1 pr)
                   (≤-reflexive (cong (λ z → collC (proj₁ (proj₂ s))
                                             +ℚ Γ (pool (proj₁ (proj₂ s))) z) tail-eq)))
        aux nothing =
          ≤-trans (≤-reflexive
            (trans (lookupᴰℚ-Dmap C.fR (respB' i M s nothing) (λ sr → φMD m (proj₁ sr)))
            (trans (E-bind (walk (proj₁ (proj₂ s)) IV (toBlocks M) 1)
                     (λ (w : Comp.Table × (CV × Bool)) →
                        newAns i M (proj₂ (proj₂ s)) (proj₂ (proj₂ w) ∨ proj₁ s)
                          (proj₁ w) (proj₁ (proj₂ w)))
                     (λ t → φMD m (proj₁ (C.fR t))))
                   (lookupᴰℚ-cong-P (entries (walk (proj₁ (proj₂ s)) IV (toBlocks M) 1))
                     (λ w → newAns-φ m i M (proj₂ (proj₂ s))
                              (proj₂ (proj₂ w) ∨ proj₁ s) (proj₁ w) (proj₁ (proj₂ w)))))))
          (≤-trans (walk-φ m (proj₁ (proj₂ s)) IV (toBlocks M) 1 pr)
                   (≤-reflexive (cong (λ z → collC (proj₁ (proj₂ s))
                                             +ℚ Γ (pool (proj₁ (proj₂ s))) z) tail-eq)))

    φ-nn : ∀ m s → 0ℚ ≤ℚ φMD m s
    φ-nn m s = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                       (+-mono-≤ (sc-nn (poolL (proj₁ (proj₂ s))))
                                 (0≤Γ (pool (proj₁ (proj₂ s))) (m * (k ∸ 1))))

    φ-init : ∀ m → φMD m (false , [] , []) ≤ℚ bound m
    φ-init zero = ≤-reflexive
      (trans φ₀ (trans (*-zeroˡ (inv-pow-2 n))
                       (sym (*-zeroˡ (inv-pow-2 n)))))
      where
        φ₀ : φMD zero (false , [] , []) ≡ sumR 1 0 *ℚ inv-pow-2 n
        φ₀ = trans (cong (_+ℚ Γ 1 0) (+-identityʳ 0ℚ)) (+-identityˡ (Γ 1 0))
    φ-init (suc m) =
      ≤-trans (≤-reflexive
        (trans (cong (_+ℚ Γ 1 (suc m * (k ∸ 1))) (+-identityʳ 0ℚ))
               (+-identityˡ (Γ 1 (suc m * (k ∸ 1))))))
      (*-monoʳ-≤-nonNeg _ ⦃ nonNegative 0≤ε ⦄
        (≤-trans (≤-reflexive sumR1)
                 (tri-mono arith)))
      where
        N = suc m * (k ∸ 1)
        sumR1 : sumR 1 N ≡ Comp.triangle (suc N)
        sumR1 = trans (sym (+-identityˡ (sumR 1 N)))
               (trans (cong (_+ℚ sumR 1 N) (sym (+-identityʳ 0ℚ)))
                      (sumR-tri 1 N))
        arith : suc N ≤ suc m * k
        arith = ℕP.+-mono-≤ (ℕP.≤-reflexive (suc∸1 k))
                            (ℕP.*-monoʳ-≤ m (ℕP.m∸n≤m k 1))

  ------------------------------------------------------------------------
  -- ★ THE CHAIN-FOREST INVARIANT, defined CONCRETELY (design §2).  The table is
  -- a labelled transition system on chaining values (`stepT`); a recorded
  -- message denotes a run from IV (`Chain`) — the shape `unique-run` consumes.

  -- the table as a labelled partial transition function on values
  stepT : Comp.Table → CV → Blk × ℕ → Maybe CV
  stepT sc v (b , j) = Comp.lookup-bs sc (v , b , k , j)

  -- position-tagged labels of a block list, starting at position j
  labels : List Blk → ℕ → List (Blk × ℕ)
  labels []       j = []
  labels (b ∷ bs) j = (b , j) ∷ labels bs (suc j)

  -- "M's chain is embedded in sc, ending at value h"
  Chain : Comp.Table → Vec Bool (k * n) → CV → Type
  Chain sc M h = runPath (stepT sc) IV (labels (toBlocks M) 1) ≡ just h

  -- a value occurs among the stored outputs of a table fragment
  HasVal : Comp.Table → CV → Type
  HasVal t v = ListAny.Any (λ e → proj₂ e ≡ v) t

  -- keys are pairwise distinct (inserts only happen on misses)
  UniqueKeys : Comp.Table → Type
  UniqueKeys sc = AllPairs _≢_ (L.map proj₁ sc)

  -- every key's chaining component is rooted in the pool ({IV} ∪ interior outputs)
  Rooted : Comp.Table → Type
  Rooted sc = ListAll.All (λ e → HasVal (poolL sc) (proj₁ (proj₁ e))) sc

  -- every FINAL key present in the table is the last call of a recorded chain
  OwnedLast : Comp.Table → General.Table → Type
  OwnedLast sc sg = ∀ v b w → stepT sc v (b , k) ≡ just w
    → Σ (Vec Bool (k * n)) λ M' → Σ CV λ h' →
        General.lookup-bs sg M' ≡ just h'
      × Σ (List Blk) λ pre →
          toBlocks M' ≡ pre ++ (b ∷ [])
        × runPath (stepT sc) IV (labels pre 1) ≡ just v

  -- recorded messages have embedded chains ending at the recorded value
  RecChains : Comp.Table → General.Table → Type
  RecChains sc sg = ∀ M h → General.lookup-bs sg M ≡ just h → Chain sc M h

  -- The structural parts are needed only WHILE UNFLAGGED (to justify the descent
  -- at the flag-raise); once flagged, only `1 ≤ collC` must persist.  So they are
  -- gated on `¬flag`, which makes the FLAGGED branch of preservation pure
  -- collision-count monotonicity.
  MDInv : FState → Type
  MDInv s =
      (proj₁ s ≡ true → 1ℚ ≤ℚ collC (proj₁ (proj₂ s)))
    × (proj₁ s ≡ false →
         UniqueKeys (proj₁ (proj₂ s))
       × Rooted (proj₁ (proj₂ s))
       × RecChains (proj₁ (proj₂ s)) (proj₂ (proj₂ s))
       × OwnedLast (proj₁ (proj₂ s)) (proj₂ (proj₂ s)))

  MDInv₀ : MDInv (false , [] , [])
  MDInv₀ = (λ ()) , (λ _ → [] , ListAll.[] , (λ M h ()) , (λ v b w ()))

  ------------------------------------------------------------------------
  -- Preservation backbone (PROVEN): collision count is monotone along the walk,
  -- via the `OnSupport` kit.  The support of `uniform` is seeded by `os-⊤`
  -- (`OnSupport (λ _ → ⊤)`), i.e. we discharge the continuation at EVERY value.
  private
    ∨-true : ∀ x → x ∨ true ≡ true
    ∨-true true  = refl
    ∨-true false = refl

    os-⊤ : ∀ {A : Type} (μ : Dist-ℚ A) → OnSupport (λ _ → ⊤) μ
    os-⊤ μ = all-univ (λ _ → tt) (NE.toList (entries μ))

    -- collC is monotone under prepending a (length-k-tagged) compression entry.
    -- (Inlined so the single `with ii <? k` reduces `collC` directly — delegating to
    -- `collC-cons<` would create a mismatched second `with`-neutral.)
    collC-mono1 : ∀ hh bb ii vv sc → collC sc ≤ℚ collC (((hh , bb , k , ii) , vv) ∷ sc)
    collC-mono1 hh bb ii vv sc with ii <? k
    ... | yes lt = +-mono-≤ (x≤c+x (Comp.count-matches (interior sc) IV) (0≤bool ⌊ IV ≟ vv ⌋))
                            (x≤c+x (Comp.state-collisions (interior sc)) (cm-nn (interior sc) vv))
    ... | no ¬lt = ≤-refl

    callC-collC-mono : ∀ c sc h b idx → c ≤ℚ collC sc
                     → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (callC sc h b idx)
    callC-collC-mono c sc h b idx c≤ = aux (Comp.lookup-bs sc (pack h b idx))
      where aux : ∀ mv → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (callC' sc h b idx mv)
            aux (just hm) = OnSupport-return c≤
            aux nothing   = OnSupport-bind Comp.uniform-Out
              (λ hm → return-ℚ ((pack h b idx , hm) ∷ sc , hm , false))
              (os-⊤ Comp.uniform-Out)
              (λ hm _ → OnSupport-return (≤-trans c≤ (collC-mono1 h b idx hm sc)))

    walk-collC-mono : ∀ c sc h bs idx → c ≤ℚ collC sc
                    → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (walk sc h bs idx)
    walk-collC-mono c sc h []            idx c≤ = OnSupport-return c≤
    walk-collC-mono c sc h (b ∷ [])      idx c≤ = callC-collC-mono c sc h b idx c≤
    walk-collC-mono c sc h (b ∷ b' ∷ bs) idx c≤ =
      OnSupport-bind (callC sc h b idx)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx))
        (callC-collC-mono c sc h b idx c≤)
        (λ w c≤w → walk-collC-mono c (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx) c≤w)

    -- a flagged state is `MDInv` as soon as `1 ≤ collC` (structural parts vacuous)
    MDInv-flagged : ∀ x sc' sg' → 1ℚ ≤ℚ collC sc' → MDInv (x ∨ true , sc' , sg')
    MDInv-flagged x sc' sg' h =
      subst (λ b → MDInv (b , sc' , sg')) (sym (∨-true x)) ((λ _ → h) , (λ ()))

    newAns-flagged : ∀ x i' M' sg' sc' hR → 1ℚ ≤ℚ collC sc'
                   → OnSupport (λ t → MDInv (proj₁ t)) (newAns i' M' sg' (x ∨ true) sc' hR)
    newAns-flagged x i' M' sg' sc' hR h rewrite ∨-true x =
      OnSupport-bind Comp.uniform-Out
        (λ u → return-ℚ ((true , sc' , (M' , u) ∷ sg') , ((i' , hR) , (i' , u))))
        (os-⊤ Comp.uniform-Out)
        (λ u _ → OnSupport-return ((λ _ → h) , (λ ())))

    -- ★ THE FLAGGED BRANCH of preservation, PROVEN: from `1 ≤ collC sc`, every
    -- reachable state stays flagged with `1 ≤ collC` (walk grows the table).
    flagged-step : ∀ sc sg i M → 1ℚ ≤ℚ collC sc
                 → OnSupport (λ t → MDInv (proj₁ t)) (respB (true , sc , sg) (i , M))
    flagged-step sc sg i M 1≤ = aux (General.lookup-bs sg M)
      where
        aux : ∀ mv → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (true , sc , sg) mv)
        aux (just h) = OnSupport-bind (walk sc IV (toBlocks M) 1)
          (λ w → return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ true , proj₁ w , sg)
                          , ((i , proj₁ (proj₂ w)) , (i , h))))
          (walk-collC-mono 1ℚ sc IV (toBlocks M) 1 1≤)
          (λ w 1≤w →
             OnSupport-return (MDInv-flagged (not ⌊ proj₁ (proj₂ w) ≟ h ⌋) (proj₁ w) sg 1≤w))
        aux nothing = OnSupport-bind (walk sc IV (toBlocks M) 1)
          (λ w → newAns i M sg (proj₂ (proj₂ w) ∨ true) (proj₁ w) (proj₁ (proj₂ w)))
          (walk-collC-mono 1ℚ sc IV (toBlocks M) 1 1≤)
          (λ w 1≤w → newAns-flagged (proj₂ (proj₂ w)) i M sg (proj₁ w) (proj₁ (proj₂ w)) 1≤w)

  record MDInvData : Type₁ where
    field
      Inv       : FState → Type
      inv₀      : Inv (false , [] , [])
      pres      : Preserved Inv C.realK
      flag⇒coll : ∀ s → Inv s → proj₁ s ≡ true → 1ℚ ≤ℚ collC (proj₁ (proj₂ s))

  private
    ∨-false : ∀ x → x ∨ false ≡ x
    ∨-false true  = refl
    ∨-false false = refl

    ⌊≟⌋-refl : ∀ (x : CV) → ⌊ x ≟ x ⌋ ≡ true
    ⌊≟⌋-refl x with x ≟ x
    ... | yes _ = refl
    ... | no ¬p = ⊥-elim (¬p refl)

    just-inj : ∀ {x y : CV} → just x ≡ just y → x ≡ y
    just-inj refl = refl

    nothing≢just : ∀ {A : Type} {x : A} → nothing ≡ just x → ⊥
    nothing≢just ()

    -- Replaying an EMBEDDED chain: with every lookup a hit, the walk is a
    -- deterministic all-hits run — the table is unchanged and it reaches the
    -- recorded value (support level; `>>=` scales weights but not points).  The
    -- block-list recursion is delegated through `walk-replayL/C` (which take the
    -- lookup result as an argument) to keep it structurally terminating.
    walk-replay  : ∀ sc bs v j hf → runPath (stepT sc) v (labels bs j) ≡ just hf
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf) (walk sc v bs j)
    walk-replayL : ∀ sc b v j hf → runPath (stepT sc) v ((b , j) ∷ []) ≡ just hf
                 → (mv : Maybe CV) → Comp.lookup-bs sc (pack v b j) ≡ mv
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf) (callC' sc v b j mv)
    walk-replayC : ∀ sc b bs' v j hf → runPath (stepT sc) v (labels (b ∷ bs') j) ≡ just hf
                 → (mv : Maybe CV) → Comp.lookup-bs sc (pack v b j) ≡ mv
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf)
                     (callC' sc v b j mv >>=ᴹ (λ u → walk (proj₁ u) (proj₁ (proj₂ u)) bs' (suc j)))

    walk-replay sc []             v j hf rp = OnSupport-return (refl , just-inj rp)
    walk-replay sc (b ∷ [])       v j hf rp = walk-replayL sc b v j hf rp (Comp.lookup-bs sc (pack v b j)) refl
    walk-replay sc (b ∷ b'' ∷ bs) v j hf rp = walk-replayC sc b (b'' ∷ bs) v j hf rp (Comp.lookup-bs sc (pack v b j)) refl

    walk-replayL sc b v j hf rp (just w) eqmv =
      OnSupport-return (refl , just-inj (trans (sym (runPath-step (stepT sc) v (b , j) w [] eqmv)) rp))
    walk-replayL sc b v j hf rp nothing eqmv =
      ⊥-elim (nothing≢just (trans (sym (runPath-nothing (stepT sc) v (b , j) [] eqmv)) rp))

    walk-replayC sc b bs' v j hf rp (just w) eqmv =
      OnSupport-bind (return-ℚ (sc , w , true))
        (λ u → walk (proj₁ u) (proj₁ (proj₂ u)) bs' (suc j))
        (OnSupport-return {P = λ u → u ≡ (sc , w , true)} refl)
        (λ u u≡ → subst
           (λ u' → OnSupport (λ w' → proj₁ w' ≡ sc × proj₁ (proj₂ w') ≡ hf)
                     (walk (proj₁ u') (proj₁ (proj₂ u')) bs' (suc j)))
           (sym u≡)
           (walk-replay sc bs' w (suc j) hf
             (trans (sym (runPath-step (stepT sc) v (b , j) w (labels bs' (suc j)) eqmv)) rp)))
    walk-replayC sc b bs' v j hf rp nothing eqmv =
      ⊥-elim (nothing≢just
        (trans (sym (runPath-nothing (stepT sc) v (b , j) (labels bs' (suc j)) eqmv)) rp))

    -- REPEAT branch, PROVEN: a recorded message replays deterministically (its
    -- chain is embedded, `RecChains`), so the table is unchanged and the value is
    -- the recorded one — the consistency check `not ⌊ h ≟ h ⌋` is `false`, the flag
    -- stays down, and the structural invariant carries over verbatim.
    mdInv-good-repeat : ∀ sc sg i M h
      → UniqueKeys sc × Rooted sc × RecChains sc sg × OwnedLast sc sg
      → General.lookup-bs sg M ≡ just h
      → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (false , sc , sg) (just h))
    mdInv-good-repeat sc sg i M h str@(uk , rt , rc , ol) eq =
      OnSupport-bind (walk sc IV (toBlocks M) 1)
        (λ w → return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ false , proj₁ w , sg)
                        , ((i , proj₁ (proj₂ w)) , (i , h))))
        (walk-replay sc (toBlocks M) IV 1 h (rc M h eq))
        cont
      where
        cont : ∀ w → (proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ h)
             → OnSupport (λ t → MDInv (proj₁ t))
                 (return-ℚ (((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ false , proj₁ w , sg)
                           , ((i , proj₁ (proj₂ w)) , (i , h))))
        cont w (sc≡ , v≡) = OnSupport-return
          (subst (λ fl → MDInv (fl , proj₁ w , sg)) (sym flag≡false)
            (subst (λ tb → MDInv (false , tb , sg)) (sym sc≡) ((λ ()) , (λ _ → str))))
          where
            flag≡false : (not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ false ≡ false
            flag≡false = trans (∨-false _)
                               (trans (cong (λ z → not ⌊ z ≟ h ⌋) v≡) (cong not (⌊≟⌋-refl h)))

  -- ═══ new-message branch (group E): fresh-insert / lookup-extension machinery ═══
  private
    just≢nothing : ∀ {A : Type} {x : A} → just x ≡ nothing → ⊥
    just≢nothing ()

    -- "sc' extends sc": every present lookup is preserved (⟹ successful runs preserved)
    _⊒_ : Comp.Table → Comp.Table → Type
    sc' ⊒ sc = ∀ key x → Comp.lookup-bs sc key ≡ just x → Comp.lookup-bs sc' key ≡ just x

    ⊒-refl : ∀ sc → sc ⊒ sc
    ⊒-refl sc key x e = e

    ⊒-trans : ∀ a b c → a ⊒ b → b ⊒ c → a ⊒ c
    ⊒-trans a b c ab bc key x e = ab key x (bc key x e)

    lookup-cons-≢ : ∀ (k₀ : CV × Blk × ℕ × ℕ) v₀ sc key
                  → key ≢ k₀ → Comp.lookup-bs ((k₀ , v₀) ∷ sc) key ≡ Comp.lookup-bs sc key
    lookup-cons-≢ k₀ v₀ sc key ne with key ≟ k₀
    ... | yes p = ⊥-elim (ne p)
    ... | no  _ = refl

    present≢fresh : ∀ sc (k₀ : CV × Blk × ℕ × ℕ) key x
                  → Comp.lookup-bs sc key ≡ just x → Comp.lookup-bs sc k₀ ≡ nothing → key ≢ k₀
    present≢fresh sc k₀ key x pres absent refl = nothing≢just (trans (sym absent) pres)

    ⊒-cons-fresh : ∀ (k₀ : CV × Blk × ℕ × ℕ) v₀ sc
                 → Comp.lookup-bs sc k₀ ≡ nothing → ((k₀ , v₀) ∷ sc) ⊒ sc
    ⊒-cons-fresh k₀ v₀ sc absent key x pres =
      trans (lookup-cons-≢ k₀ v₀ sc key (present≢fresh sc k₀ key x pres absent)) pres

    -- successful runs are preserved under extension
    runPath-⊒ : ∀ sc' sc → sc' ⊒ sc → ∀ r ls t
              → runPath (stepT sc) r ls ≡ just t → runPath (stepT sc') r ls ≡ just t
    runPath-⊒ sc' sc ext r [] t e = e
    runPath-⊒ sc' sc ext r ((b , j) ∷ ls) t e =
      let (w , hd , tl) = runPath-cons-inv (stepT sc) r (b , j) ls t e
      in trans (runPath-step (stepT sc') r (b , j) w ls (ext (pack r b j) w hd))
               (runPath-⊒ sc' sc ext w ls t tl)

    -- a fresh (absent) key differs from every present key
    lookup-nothing⇒All≢ : ∀ sc (k₀ : CV × Blk × ℕ × ℕ) → Comp.lookup-bs sc k₀ ≡ nothing
                        → ListAll.All (λ key → k₀ ≢ key) (L.map proj₁ sc)
    lookup-nothing⇒All≢ []             k₀ absent = ListAll.[]
    lookup-nothing⇒All≢ ((k , v) ∷ sc) k₀ absent with k₀ ≟ k | absent
    ... | yes _ | ab = ⊥-elim (just≢nothing ab)
    ... | no ¬p | ab = ¬p ListAll.∷ lookup-nothing⇒All≢ sc k₀ ab

    UniqueKeys-cons-fresh : ∀ (k₀ : CV × Blk × ℕ × ℕ) v₀ sc
                          → Comp.lookup-bs sc k₀ ≡ nothing → UniqueKeys sc → UniqueKeys ((k₀ , v₀) ∷ sc)
    UniqueKeys-cons-fresh k₀ v₀ sc absent uk = lookup-nothing⇒All≢ sc k₀ absent ∷ uk

    -- ═══ new-message branch (group E cont.): Rooted maintenance under inserts ═══

    -- insert one element after the head of an Any-witness list
    Any-insert : ∀ {A : Type} {P : A → Type} {x z : A} {ys}
               → ListAny.Any P (x ∷ ys) → ListAny.Any P (x ∷ z ∷ ys)
    Any-insert (ListAny.here p)  = ListAny.here p
    Any-insert (ListAny.there a) = ListAny.there (ListAny.there a)

    -- prepending any entry only grows the pool: pool membership is preserved
    HasVal-cons-any : ∀ (e : (CV × Blk × ℕ × ℕ) × CV) sc x
                    → HasVal (poolL sc) x → HasVal (poolL (e ∷ sc)) x
    HasVal-cons-any ((hh , bb , len , idx) , vv) sc x hv with idx <? len
    ... | yes _ = Any-insert hv
    ... | no  _ = hv

    -- the value of a freshly inserted INTERIOR entry is in the new pool
    new-val-HasVal : ∀ v b idx vv sc → idx < k → HasVal (poolL ((pack v b idx , vv) ∷ sc)) vv
    new-val-HasVal v b idx vv sc lt with idx <? k
    ... | yes _   = ListAny.there (ListAny.here refl)
    ... | no  ¬lt = ⊥-elim (¬lt lt)

    -- an INTERIOR key's stored value is rooted in the pool
    lookup-interior-HasVal : ∀ sc v b idx v'' → idx < k
                           → Comp.lookup-bs sc (pack v b idx) ≡ just v'' → HasVal (poolL sc) v''
    lookup-interior-HasVal ((key , val) ∷ sc) v b idx v'' lt hit with (pack v b idx) ≟ key | hit
    ... | yes p | h = subst (λ K → HasVal (poolL ((K , val) ∷ sc)) v'') p
                        (subst (HasVal (poolL ((pack v b idx , val) ∷ sc))) (just-inj h)
                          (new-val-HasVal v b idx val sc lt))
    ... | no ¬p | h = HasVal-cons-any (key , val) sc v'' (lookup-interior-HasVal sc v b idx v'' lt h)

    lookup-cons-here : ∀ (key : CV × Blk × ℕ × ℕ) val sc → Comp.lookup-bs ((key , val) ∷ sc) key ≡ just val
    lookup-cons-here key val sc with key ≟ key
    ... | yes _  = refl
    ... | no ¬p = ⊥-elim (¬p refl)

    -- prepending a fresh entry preserves Rooted (its chaining is already rooted)
    Rooted-cons-fresh : ∀ (e : (CV × Blk × ℕ × ℕ) × CV) sc
                      → HasVal (poolL sc) (proj₁ (proj₁ e)) → Rooted sc → Rooted (e ∷ sc)
    Rooted-cons-fresh e sc eroot rt =
      HasVal-cons-any e sc (proj₁ (proj₁ e)) eroot
        ListAll.∷ ListAll.map (λ {ent} hv → HasVal-cons-any e sc (proj₁ (proj₁ ent)) hv) rt

    -- ═══ new-message branch (group F): the walk-support lemma ═══

    OnSupport-mono : ∀ {A : Type} {P Q : A → Type} (μ : Dist-ℚ A)
                   → (∀ a → P a → Q a) → OnSupport P μ → OnSupport Q μ
    OnSupport-mono μ f os = ListAll.map (λ {e} pe → f (proj₂ e) pe) os

    OnSupport-bind-return : ∀ {A B : Type} {Q : B → Type} (a : A) (WK : A → Dist-ℚ B)
                          → OnSupport Q (WK a) → OnSupport Q (return-ℚ a >>=ᴹ WK)
    OnSupport-bind-return {Q = Q} a WK os =
      OnSupport-bind (return-ℚ a) WK (OnSupport-return {P = λ x → x ≡ a} refl)
        (λ x x≡ → subst (λ x0 → OnSupport Q (WK x0)) (sym x≡) os)

    -- the walk-support bundle (structural facts on a support element)
    CBnd : Comp.Table → CV → Blk → ℕ → Comp.Table × (CV × Bool) → Type
    CBnd sc v b idx w = (proj₁ w ⊒ sc) × UniqueKeys (proj₁ w) × Rooted (proj₁ w)
                      × HasVal (poolL (proj₁ w)) (proj₁ (proj₂ w))
                      × (stepT (proj₁ w) v (b , idx) ≡ just (proj₁ (proj₂ w)))

    Bnd : Comp.Table → CV → List Blk → ℕ → Comp.Table × (CV × Bool) → Type
    Bnd sc v bs idx w = (proj₁ w ⊒ sc) × UniqueKeys (proj₁ w) × Rooted (proj₁ w)
                      × (runPath (stepT (proj₁ w)) v (labels bs idx) ≡ just (proj₁ (proj₂ w)))

    -- single call: structural facts on its support (INTERIOR variant, idx < k)
    callC-supp : ∀ sc v b idx → idx < k → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → OnSupport (CBnd sc v b idx) (callC sc v b idx)
    callC-supp sc v b idx lt uk rt vroot with Comp.lookup-bs sc (pack v b idx) in eq
    ... | just hm = OnSupport-return (⊒-refl sc , uk , rt , lookup-interior-HasVal sc v b idx hm lt eq , eq)
    ... | nothing = OnSupport-bind Comp.uniform-Out
                      (λ hm → return-ℚ ((pack v b idx , hm) ∷ sc , hm , false))
                      (os-⊤ Comp.uniform-Out)
                      (λ hm _ → OnSupport-return
                        ( ⊒-cons-fresh (pack v b idx) hm sc eq
                        , UniqueKeys-cons-fresh (pack v b idx) hm sc eq uk
                        , Rooted-cons-fresh (pack v b idx , hm) sc vroot rt
                        , new-val-HasVal v b idx hm sc lt
                        , lookup-cons-here (pack v b idx) hm sc ))

    walk-supp  : ∀ sc v bs idx → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → idx + length bs ≡ suc k → OnSupport (Bnd sc v bs idx) (walk sc v bs idx)
    walk-suppL : ∀ sc v b idx (mv : Maybe CV) → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → Comp.lookup-bs sc (pack v b idx) ≡ mv
               → OnSupport (Bnd sc v (b ∷ []) idx) (callC' sc v b idx mv)
    walk-suppC : ∀ sc v b bs' idx (mv : Maybe CV) → idx < k → suc idx + length bs' ≡ suc k
               → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → Comp.lookup-bs sc (pack v b idx) ≡ mv
               → OnSupport (Bnd sc v (b ∷ bs') idx)
                   (callC' sc v b idx mv >>=ᴹ (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)))

    walk-supp sc v []            idx uk rt vroot pr = OnSupport-return (⊒-refl sc , uk , rt , refl)
    walk-supp sc v (b ∷ [])      idx uk rt vroot pr =
      walk-suppL sc v b idx (Comp.lookup-bs sc (pack v b idx)) uk rt vroot refl
    walk-supp sc v (b ∷ b' ∷ bs) idx uk rt vroot pr =
      walk-suppC sc v b (b' ∷ bs) idx (Comp.lookup-bs sc (pack v b idx)) lt pr' uk rt vroot refl
      where
        eq0 : idx + suc (length bs) ≡ k
        eq0 = ℕP.suc-injective (trans (sym (ℕP.+-suc idx (suc (length bs)))) pr)
        lt : idx < k
        lt = ℕP.≤-trans (ℕP.m<m+n idx ℕP.0<1+n) (ℕP.≤-reflexive eq0)
        pr' : suc idx + length (b' ∷ bs) ≡ suc k
        pr' = cong suc eq0

    -- FINAL call (single block): no recursion
    walk-suppL sc v b idx (just hm) uk rt vroot eq =
      OnSupport-return (⊒-refl sc , uk , rt , runPath-step (stepT sc) v (b , idx) hm [] eq)
    walk-suppL sc v b idx nothing uk rt vroot eq =
      OnSupport-bind Comp.uniform-Out
        (λ hm → return-ℚ ((pack v b idx , hm) ∷ sc , hm , false))
        (os-⊤ Comp.uniform-Out)
        (λ hm _ → OnSupport-return
          ( ⊒-cons-fresh (pack v b idx) hm sc eq
          , UniqueKeys-cons-fresh (pack v b idx) hm sc eq uk
          , Rooted-cons-fresh (pack v b idx , hm) sc vroot rt
          , runPath-step (stepT ((pack v b idx , hm) ∷ sc)) v (b , idx) hm [] (lookup-cons-here (pack v b idx) hm sc) ))

    -- INTERIOR call then recurse (mirrors walk-φC)
    walk-suppC sc v b bs' idx (just hm) lt pr uk rt vroot eq =
      OnSupport-bind-return (sc , hm , true)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        (OnSupport-mono (walk sc hm bs' (suc idx)) maphit
          (walk-supp sc hm bs' (suc idx) uk rt (lookup-interior-HasVal sc v b idx hm lt eq) pr))
      where
        maphit : ∀ w2 → Bnd sc hm bs' (suc idx) w2 → Bnd sc v (b ∷ bs') idx w2
        maphit w2 (ext2 , uk2 , rt2 , seg2) =
          ext2 , uk2 , rt2
          , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) hm
                    (labels bs' (suc idx)) (ext2 (pack v b idx) hm eq)) seg2
    walk-suppC sc v b bs' idx nothing lt pr uk rt vroot eq =
      OnSupport-bind (callC' sc v b idx nothing)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        seed
        (λ w cb → OnSupport-mono (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
                    (mapc w cb)
                    (walk-supp (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)
                       (proj₁ (proj₂ cb)) (proj₁ (proj₂ (proj₂ cb))) (proj₁ (proj₂ (proj₂ (proj₂ cb)))) pr))
      where
        seed : OnSupport (CBnd sc v b idx) (callC' sc v b idx nothing)
        seed = OnSupport-bind Comp.uniform-Out
                 (λ hm → return-ℚ ((pack v b idx , hm) ∷ sc , hm , false))
                 (os-⊤ Comp.uniform-Out)
                 (λ hm _ → OnSupport-return
                   ( ⊒-cons-fresh (pack v b idx) hm sc eq
                   , UniqueKeys-cons-fresh (pack v b idx) hm sc eq uk
                   , Rooted-cons-fresh (pack v b idx , hm) sc vroot rt
                   , new-val-HasVal v b idx hm sc lt
                   , lookup-cons-here (pack v b idx) hm sc ))
        mapc : ∀ w → CBnd sc v b idx w → ∀ w2 → Bnd (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) w2
             → Bnd sc v (b ∷ bs') idx w2
        mapc w (ext , uk' , rt' , hvroot , stepeq) w2 (ext2 , uk2 , rt2 , seg2) =
          ⊒-trans (proj₁ w2) (proj₁ w) sc ext2 ext , uk2 , rt2
          , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) (proj₁ (proj₂ w))
                    (labels bs' (suc idx)) (ext2 (pack v b idx) (proj₁ (proj₂ w)) stepeq)) seg2

  private
    -- length of a message in blocks is exactly k
    toList-len : ∀ {A : Type} {m} (xs : Vec A m) → length (toList xs) ≡ m
    toList-len []       = refl
    toList-len (x ∷ xs) = cong suc (toList-len xs)

    -- extending a table by fresh inserts + recording (M , v') preserves RecChains
    rec-extend : ∀ sc sg sc' M v' → sc' ⊒ sc → Chain sc' M v'
               → RecChains sc sg → RecChains sc' ((M , v') ∷ sg)
    rec-extend sc sg sc' M v' ext chain rc M₀ h₀ lk with M₀ ≟ M | lk
    ... | yes p | l = subst (λ hh → Chain sc' M₀ hh) (just-inj l)
                        (subst (λ MM → Chain sc' MM v') (sym p) chain)
    ... | no ¬p | l = runPath-⊒ sc' sc ext IV (labels (toBlocks M₀) 1) h₀ (rc M₀ h₀ l)

  -- ═══ new-message branch (group F cont.): the final-key tracker ═══
  private
    -- an interior key (idx < k) is never a final key (idx = k)
    final≢interior : ∀ v' b' v b idx → idx < k → (v' , b' , k , k) ≢ pack v b idx
    final≢interior v' b' v b idx lt p =
      ℕP.<-irrefl refl (subst (idx <_) (cong (λ z → proj₂ (proj₂ (proj₂ z))) p) lt)

    -- "the key (v',b',k) is the last block of this walk, reaching v'"
    FinalCallOf : CV → List Blk → ℕ → Comp.Table → CV → Blk → Type
    FinalCallOf v bs idx sc' v' b' =
      Σ (List Blk) λ pre → (bs ≡ pre ++ (b' ∷ [])) × (runPath (stepT sc') v (labels pre idx) ≡ just v')

    -- output bundle: extension + every FINAL key of sc' is either old (in sc) or
    -- this walk's own last call
    FKout : Comp.Table → CV → List Blk → ℕ → Comp.Table × (CV × Bool) → Type
    FKout sc v bs idx w = (proj₁ w ⊒ sc)
      × (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u'
           → (stepT sc v' (b' , k) ≡ just u')
           ⊎ (FinalCallOf v bs idx (proj₁ w) v' b' × (proj₂ (proj₂ w) ≡ false)))

    walk-fk  : ∀ sc v bs idx → idx + length bs ≡ suc k
             → OnSupport (FKout sc v bs idx) (walk sc v bs idx)
    walk-fkL : ∀ sc v b idx (mv : Maybe CV) → Comp.lookup-bs sc (pack v b idx) ≡ mv
             → OnSupport (FKout sc v (b ∷ []) idx) (callC' sc v b idx mv)
    walk-fkC : ∀ sc v b bs' idx (mv : Maybe CV) → idx < k → suc idx + length bs' ≡ suc k
             → Comp.lookup-bs sc (pack v b idx) ≡ mv
             → OnSupport (FKout sc v (b ∷ bs') idx)
                 (callC' sc v b idx mv >>=ᴹ (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)))

    walk-fk sc v []            idx pr = OnSupport-return (⊒-refl sc , λ v' b' u' e → inj₁ e)
    walk-fk sc v (b ∷ [])      idx pr =
      walk-fkL sc v b idx (Comp.lookup-bs sc (pack v b idx)) refl
    walk-fk sc v (b ∷ b' ∷ bs) idx pr =
      walk-fkC sc v b (b' ∷ bs) idx (Comp.lookup-bs sc (pack v b idx)) lt pr' refl
      where
        eq0 : idx + suc (length bs) ≡ k
        eq0 = ℕP.suc-injective (trans (sym (ℕP.+-suc idx (suc (length bs)))) pr)
        lt : idx < k
        lt = ℕP.≤-trans (ℕP.m<m+n idx ℕP.0<1+n) (ℕP.≤-reflexive eq0)
        pr' : suc idx + length (b' ∷ bs) ≡ suc k
        pr' = cong suc eq0

    -- FINAL call (single block, no recursion)
    walk-fkL sc v b idx (just hm) eq = OnSupport-return (⊒-refl sc , λ v' b' u' e → inj₁ e)
    walk-fkL sc v b idx nothing eq =
      OnSupport-bind Comp.uniform-Out
        (λ hm → return-ℚ ((pack v b idx , hm) ∷ sc , hm , false))
        (os-⊤ Comp.uniform-Out)
        (λ hm _ → OnSupport-return (⊒-cons-fresh (pack v b idx) hm sc eq , dich hm))
      where
        dich : ∀ hm → ∀ v' b' u' → stepT ((pack v b idx , hm) ∷ sc) v' (b' , k) ≡ just u'
             → (stepT sc v' (b' , k) ≡ just u')
             ⊎ (FinalCallOf v (b ∷ []) idx ((pack v b idx , hm) ∷ sc) v' b' × (false ≡ false))
        dich hm v' b' u' e with (v' , b' , k , k) ≟ pack v b idx | e
        ... | yes p | e' = inj₂ (([] , cong (_∷ []) (sym (cong (λ z → proj₁ (proj₂ z)) p))
                                 , cong just (sym (cong proj₁ p))) , refl)
        ... | no ¬p | e' = inj₁ e'

    -- INTERIOR call then recurse (mirrors walk-suppC)
    walk-fkC sc v b bs' idx (just hm) lt pr eq =
      OnSupport-bind-return (sc , hm , true)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        (OnSupport-mono (walk sc hm bs' (suc idx)) maphit (walk-fk sc hm bs' (suc idx) pr))
      where
        maphit : ∀ w2 → FKout sc hm bs' (suc idx) w2 → FKout sc v (b ∷ bs') idx w2
        maphit w2 (ext2 , dich2) = ext2 , dd
          where
            dd : ∀ v' b' u' → stepT (proj₁ w2) v' (b' , k) ≡ just u'
               → (stepT sc v' (b' , k) ≡ just u')
               ⊎ (FinalCallOf v (b ∷ bs') idx (proj₁ w2) v' b' × (proj₂ (proj₂ w2) ≡ false))
            dd v' b' u' e with dich2 v' b' u' e
            ... | inj₁ x = inj₁ x
            ... | inj₂ ((pre' , beq , req) , bf) = inj₂ (((b ∷ pre') , cong (b ∷_) beq
                  , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) hm (labels pre' (suc idx))
                            (ext2 (pack v b idx) hm eq)) req) , bf)
    walk-fkC sc v b bs' idx nothing lt pr eq =
      OnSupport-bind (callC' sc v b idx nothing)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        seed
        (λ w cb → OnSupport-mono (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
                    (mapc w cb) (walk-fk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) pr))
      where
        seed : OnSupport (λ w → (proj₁ w ⊒ sc)
                  × (stepT (proj₁ w) v (b , idx) ≡ just (proj₁ (proj₂ w)))
                  × (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u' → stepT sc v' (b' , k) ≡ just u'))
                 (callC' sc v b idx nothing)
        seed = OnSupport-bind Comp.uniform-Out
                 (λ hm → return-ℚ ((pack v b idx , hm) ∷ sc , hm , false))
                 (os-⊤ Comp.uniform-Out)
                 (λ hm _ → OnSupport-return
                   ( ⊒-cons-fresh (pack v b idx) hm sc eq
                   , lookup-cons-here (pack v b idx) hm sc
                   , (λ v' b' u' x → trans (sym (lookup-cons-≢ (pack v b idx) hm sc (v' , b' , k , k)
                                              (final≢interior v' b' v b idx lt))) x) ))
        mapc : ∀ w → ((proj₁ w ⊒ sc) × (stepT (proj₁ w) v (b , idx) ≡ just (proj₁ (proj₂ w)))
                       × (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u' → stepT sc v' (b' , k) ≡ just u'))
             → ∀ w2 → FKout (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) w2 → FKout sc v (b ∷ bs') idx w2
        mapc w (exth , steph , finalrev) w2 (ext2 , dich2) =
          ⊒-trans (proj₁ w2) (proj₁ w) sc ext2 exth , dd
          where
            dd : ∀ v' b' u' → stepT (proj₁ w2) v' (b' , k) ≡ just u'
               → (stepT sc v' (b' , k) ≡ just u')
               ⊎ (FinalCallOf v (b ∷ bs') idx (proj₁ w2) v' b' × (proj₂ (proj₂ w2) ≡ false))
            dd v' b' u' e with dich2 v' b' u' e
            ... | inj₁ x = inj₁ (finalrev v' b' u' x)
            ... | inj₂ ((pre' , beq , req) , bf) = inj₂ (((b ∷ pre') , cong (b ∷_) beq
                  , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) (proj₁ (proj₂ w)) (labels pre' (suc idx))
                            (ext2 (pack v b idx) (proj₁ (proj₂ w)) steph)) req) , bf)

  private
    -- conjunction of two support facts over the SAME distribution
    OnSupport-∧ : ∀ {A : Type} {P Q : A → Type} (μ : Dist-ℚ A)
                → OnSupport P μ → OnSupport Q μ → OnSupport (λ a → P a × Q a) μ
    OnSupport-∧ {A} {P} {Q} μ pp qq = go pp qq
      where go : ∀ {xs : List (ℚ × A)}
               → ListAll.All (λ e → P (proj₂ e)) xs → ListAll.All (λ e → Q (proj₂ e)) xs
               → ListAll.All (λ e → P (proj₂ e) × Q (proj₂ e)) xs
            go ListAll.[]       ListAll.[]       = ListAll.[]
            go (p ListAll.∷ ps) (q ListAll.∷ qs) = (p , q) ListAll.∷ go ps qs

    -- ghost-table lookup lemmas (mirror the Comp-table ones)
    G-lookup-cons-≢ : ∀ (M₀ : Vec Bool (k * n)) v₀ sg key → key ≢ M₀
                    → General.lookup-bs ((M₀ , v₀) ∷ sg) key ≡ General.lookup-bs sg key
    G-lookup-cons-≢ M₀ v₀ sg key ne with key ≟ M₀
    ... | yes p = ⊥-elim (ne p)
    ... | no  _ = refl

    G-lookup-cons-here : ∀ (M₀ : Vec Bool (k * n)) v₀ sg → General.lookup-bs ((M₀ , v₀) ∷ sg) M₀ ≡ just v₀
    G-lookup-cons-here M₀ v₀ sg with M₀ ≟ M₀
    ... | yes _  = refl
    ... | no ¬p = ⊥-elim (¬p refl)

  -- ═══ descent (S2): collC ≡ 0 ⇒ interior co-determinism ═══
  private
    pos-sum-≡0 : ∀ a b → 0ℚ ≤ℚ a → 0ℚ ≤ℚ b → a +ℚ b ≡ 0ℚ → (a ≡ 0ℚ) × (b ≡ 0ℚ)
    pos-sum-≡0 a b 0≤a 0≤b s0 =
        ≤-antisym (≤-trans (x≤x+c a 0≤b) (≤-reflexive s0)) 0≤a
      , ≤-antisym (≤-trans (x≤c+x b 0≤a) (≤-reflexive s0)) 0≤b

    -- count-matches ≡ 0 ⇒ no entry has value h
    cm0-all : ∀ L h → Comp.count-matches L h ≡ 0ℚ → ListAll.All (λ e → h ≢ proj₂ e) L
    cm0-all []             h _   = ListAll.[]
    cm0-all ((key , v) ∷ xs) h eq0 with h ≟ v | eq0
    ... | yes _ | eq0' = ⊥-elim (1≢0 (≤-antisym (≤-trans (x≤x+c 1ℚ (cm-nn xs h)) (≤-reflexive eq0')) 0≤1ℚ))
    ... | no ¬p | eq0' = ¬p ListAll.∷ cm0-all xs h (trans (sym (+-identityˡ (Comp.count-matches xs h))) eq0')

    -- state-collisions ≡ 0 ⇒ all stored values pairwise distinct
    sc0-ap : ∀ L → Comp.state-collisions L ≡ 0ℚ → AllPairs (λ e e' → proj₂ e ≢ proj₂ e') L
    sc0-ap []             _   = []
    sc0-ap ((key , h) ∷ ps) eq0 =
      let s = pos-sum-≡0 (Comp.count-matches ps h) (Comp.state-collisions ps) (cm-nn ps h) (sc-nn ps) eq0
      in cm0-all ps h (proj₁ s) ∷ sc0-ap ps (proj₂ s)

    -- a successful lookup exhibits the found entry as a member
    lookup⇒mem : ∀ sc key w → Comp.lookup-bs sc key ≡ just w → ListAny.Any (_≡ (key , w)) sc
    lookup⇒mem ((k' , v') ∷ xs) key w e with key ≟ k' | e
    ... | yes p | e' = ListAny.here (cong₂ _,_ (sym p) (just-inj e'))
    ... | no ¬p | e' = ListAny.there (lookup⇒mem xs key w e')

    -- an interior member (idx < k) survives the `interior` filter
    ∈interior : ∀ sc v b j w → j < k → ListAny.Any (_≡ ((v , b , k , j) , w)) sc
              → ListAny.Any (_≡ ((v , b , k , j) , w)) (interior sc)
    ∈interior (_ ∷ es) v b j w lt (ListAny.here refl) with j <? k
    ... | yes _   = ListAny.here refl
    ... | no ¬lt = ⊥-elim (¬lt lt)
    ∈interior (((cv' , b' , len' , idx') , val') ∷ es) v b j w lt (ListAny.there a) with idx' <? len'
    ... | yes _ = ListAny.there (∈interior es v b j w lt a)
    ... | no  _ = ∈interior es v b j w lt a

    interior-mem : ∀ sc v b j w → j < k → ListAny.Any (_≡ ((v , b , k , j) , w)) sc
                 → ListAny.Any (_≡ ((v , b , k , j) , w)) (poolL sc)
    interior-mem sc v b j w lt mem = ListAny.there (∈interior sc v b j w lt mem)

    -- two members of an AllPairs-list are equal or R-related
    lookupAll : ∀ {A : Type} {R : A → Type} {y xs} → ListAll.All R xs → ListAny.Any (_≡ y) xs → R y
    lookupAll {R = R} (px ListAll.∷ _)  (ListAny.here e) = subst R e px
    lookupAll         (_  ListAll.∷ ps) (ListAny.there a) = lookupAll ps a

    allpairs-mem : ∀ {A : Type} {R : A → A → Type} {xs} → AllPairs R xs
                 → ∀ {x y} → ListAny.Any (_≡ x) xs → ListAny.Any (_≡ y) xs → (x ≡ y) ⊎ (R x y ⊎ R y x)
    allpairs-mem (_  ∷ _)   (ListAny.here refl) (ListAny.here refl) = inj₁ refl
    allpairs-mem (px ∷ _)   (ListAny.here refl) (ListAny.there qy)  = inj₂ (inj₁ (lookupAll px qy))
    allpairs-mem (px ∷ _)   (ListAny.there qx)  (ListAny.here refl) = inj₂ (inj₂ (lookupAll px qx))
    allpairs-mem (_  ∷ aps) (ListAny.there qx)  (ListAny.there qy)  = allpairs-mem aps qx qy

    -- interior co-determinism: two interior keys looking up to the same value are equal
    codet : ∀ sc' → collC sc' ≡ 0ℚ → ∀ v₁ b₁ j₁ v₂ b₂ j₂ w → j₁ < k → j₂ < k
          → Comp.lookup-bs sc' (v₁ , b₁ , k , j₁) ≡ just w
          → Comp.lookup-bs sc' (v₂ , b₂ , k , j₂) ≡ just w
          → (v₁ , b₁ , k , j₁) ≡ (v₂ , b₂ , k , j₂)
    codet sc' c0 v₁ b₁ j₁ v₂ b₂ j₂ w lt₁ lt₂ e₁ e₂ =
      go (allpairs-mem (sc0-ap (poolL sc') c0)
           (interior-mem sc' v₁ b₁ j₁ w lt₁ (lookup⇒mem sc' (v₁ , b₁ , k , j₁) w e₁))
           (interior-mem sc' v₂ b₂ j₂ w lt₂ (lookup⇒mem sc' (v₂ , b₂ , k , j₂) w e₂)))
      where
        go : (((v₁ , b₁ , k , j₁) , w) ≡ ((v₂ , b₂ , k , j₂) , w))
           ⊎ ((w ≢ w) ⊎ (w ≢ w)) → (v₁ , b₁ , k , j₁) ≡ (v₂ , b₂ , k , j₂)
        go (inj₁ eq)        = cong proj₁ eq
        go (inj₂ (inj₁ r)) = ⊥-elim (r refl)
        go (inj₂ (inj₂ r)) = ⊥-elim (r refl)

  -- ═══ descent (S1/S4): integrality + structural list/vector lemmas ═══
  private
    -- integrality: a δ-sum is 0 or ≥ 1
    cm-01 : ∀ L h → (Comp.count-matches L h ≡ 0ℚ) ⊎ (1ℚ ≤ℚ Comp.count-matches L h)
    cm-01 []             h = inj₁ refl
    cm-01 ((_ , v) ∷ xs) h with h ≟ v | cm-01 xs h
    ... | yes _ | _         = inj₂ (x≤x+c 1ℚ (cm-nn xs h))
    ... | no  _ | inj₂ c≥1 = inj₂ (subst (1ℚ ≤ℚ_) (sym (+-identityˡ _)) c≥1)
    ... | no  _ | inj₁ c0  = inj₁ (trans (+-identityˡ _) c0)

    collC-01 : ∀ L → (Comp.state-collisions L ≡ 0ℚ) ⊎ (1ℚ ≤ℚ Comp.state-collisions L)
    collC-01 []             = inj₁ refl
    collC-01 ((_ , h) ∷ ps) with cm-01 ps h | collC-01 ps
    ... | inj₂ cm≥1 | _         = inj₂ (≤-trans cm≥1 (x≤x+c _ (sc-nn ps)))
    ... | inj₁ _    | inj₂ sc≥1 = inj₂ (≤-trans sc≥1 (x≤c+x _ (cm-nn ps h)))
    ... | inj₁ cm0  | inj₁ sc0  = inj₁ (trans (cong₂ _+ℚ_ cm0 sc0) (+-identityˡ 0ℚ))

    -- snoc decomposition of a nonempty block list
    snoc-view : ∀ (xs : List Blk) → 0 < length xs
              → Σ (List Blk) λ ys → Σ Blk λ y → xs ≡ ys ++ (y ∷ [])
    snoc-view (x ∷ [])        _ = [] , x , refl
    snoc-view (x ∷ x' ∷ xs')  _ =
      let s = snoc-view (x' ∷ xs') ℕP.0<1+n
      in x ∷ proj₁ s , proj₁ (proj₂ s) , cong (x ∷_) (proj₂ (proj₂ s))

    -- labels of a snoc: last label carries position (j + length bs)
    labels-++ : ∀ bs b j → labels (bs ++ (b ∷ [])) j ≡ labels bs j ++ ((b , j + length bs) ∷ [])
    labels-++ []       b j = cong (λ z → (b , z) ∷ []) (sym (ℕP.+-identityʳ j))
    labels-++ (x ∷ bs) b j = cong ((x , j) ∷_)
      (trans (labels-++ bs b (suc j))
             (cong (λ z → labels bs (suc j) ++ ((b , z) ∷ [])) (sym (ℕP.+-suc j (length bs)))))

    -- labels is injective at a fixed start position
    labels-inj : ∀ bs bs' j → labels bs j ≡ labels bs' j → bs ≡ bs'
    labels-inj []       []         j _  = refl
    labels-inj []       (b' ∷ bs') j ()
    labels-inj (b ∷ bs) []         j ()
    labels-inj (b ∷ bs) (b' ∷ bs') j eq =
      cong₂ _∷_ (cong proj₁ (proj₁ (∷-injective eq))) (labels-inj bs bs' (suc j) (proj₂ (∷-injective eq)))

    -- interior-restricted step; all-interior runs agree with the full step
    stepT<k : Comp.Table → CV → Blk × ℕ → Maybe CV
    stepT<k sc v (b , j) with j <? k
    ... | yes _ = Comp.lookup-bs sc (v , b , k , j)
    ... | no  _ = nothing

    runPath-≡<k : ∀ sc r bs j → j + length bs ≤ k
                → runPath (stepT<k sc) r (labels bs j) ≡ runPath (stepT sc) r (labels bs j)
    runPath-≡<k sc r []       j le = refl
    runPath-≡<k sc r (b ∷ bs) j le with j <? k
    ... | no ¬lt = ⊥-elim (¬lt (ℕP.<-≤-trans (ℕP.m<m+n j ℕP.0<1+n) le))
    ... | yes _ with Comp.lookup-bs sc (r , b , k , j)
    ...   | nothing = refl
    ...   | just w  = runPath-≡<k sc w bs (suc j) (subst (_≤ k) (ℕP.+-suc j (length bs)) le)

    -- chunk is injective (via take/drop reconstruction)
    chunk-inj : ∀ j (M M' : Vec Bool (j * n)) → chunk j M ≡ chunk j M' → M ≡ M'
    chunk-inj zero    []  []  _  = refl
    chunk-inj (suc j) M   M'  eq =
      take-drop-inj n M M' (cong DV.head eq) (chunk-inj j (dropᵛ n M) (dropᵛ n M') (cong DV.tail eq))

    toList-inj : ∀ {A : Type} {m} (xs ys : Vec A m) → toList xs ≡ toList ys → xs ≡ ys
    toList-inj []       []       _  = refl
    toList-inj (x ∷ xs) (y ∷ ys) eq =
      cong₂ _∷_ (proj₁ (∷-injective eq)) (toList-inj xs ys (proj₂ (∷-injective eq)))

    toBlocks-inj : ∀ (M M' : Vec Bool (k * n)) → toBlocks M ≡ toBlocks M' → M ≡ M'
    toBlocks-inj M M' eq = chunk-inj k M M' (toList-inj (chunk k M) (chunk k M') eq)

  private
    labels-length : ∀ bs j → length (labels bs j) ≡ length bs
    labels-length []       j = refl
    labels-length (b ∷ bs) j = cong suc (labels-length bs (suc j))

    -- length of a snoc-decomposed message's prefix is k − 1 (so 1 + it ≡ k)
    snoc-len : ∀ (M0 : Vec Bool (k * n)) pre b → toBlocks M0 ≡ pre ++ (b ∷ []) → 1 + length pre ≡ k
    snoc-len M0 pre b dec =
      trans (sym (ℕP.+-comm (length pre) 1))
      (trans (sym (length-++ pre {b ∷ []}))
      (trans (sym (cong length dec)) (toList-len (chunk k M0))))

    -- inversion of the interior-restricted step
    stepT<k-inv : ∀ sc v b j w → stepT<k sc v (b , j) ≡ just w
                → (j < k) × (Comp.lookup-bs sc (v , b , k , j) ≡ just w)
    stepT<k-inv sc v b j w e with j <? k | e
    ... | yes lt | e' = lt , e'
    ... | no  _  | ()

    -- co-determinism of the interior step from collC ≡ 0
    codet<k : ∀ sc' → collC sc' ≡ 0ℚ
            → ∀ {a l a' l' w} → stepT<k sc' a l ≡ just w → stepT<k sc' a' l' ≡ just w → (a , l) ≡ (a' , l')
    codet<k sc' c0 {a} {b1 , j1} {a'} {b1' , j1'} {w} e1 e2 =
      let i1 = stepT<k-inv sc' a  b1  j1  w e1
          i2 = stepT<k-inv sc' a' b1' j1' w e2
          keq = codet sc' c0 a b1 j1 a' b1' j1' w (proj₁ i1) (proj₁ i2) (proj₂ i1) (proj₂ i2)
      in cong₂ _,_ (cong (λ z → proj₁ z) keq)
                   (cong₂ _,_ (cong (λ z → proj₁ (proj₂ z)) keq) (cong (λ z → proj₂ (proj₂ (proj₂ z))) keq))

  -- ═══ HIT residual, PROVEN: the birthday descent ═══
  -- A NEW message whose final call hits an existing entry re-meets a recorded
  -- chain M' ≠ M.  If collC ≡ 0 the interior transition system is co-deterministic,
  -- so the two equal-length prefix runs to the shared pre-final value coincide
  -- (`unique-run`); with the shared last block, `toBlocks M ≡ toBlocks M'`, hence
  -- (`toBlocks`-injective) M ≡ M' — contradicting M ∉ sg.  So 1 ≤ collC.
  walk-hit-collC : ∀ sc sg M (w : Comp.Table × (CV × Bool))
                 → General.lookup-bs sg M ≡ nothing
                 → (proj₁ w ⊒ sc) → UniqueKeys (proj₁ w) → Rooted (proj₁ w)
                 → (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u' → stepT sc v' (b' , k) ≡ just u')
                 → RecChains sc sg → OwnedLast sc sg
                 → runPath (stepT (proj₁ w)) IV (labels (toBlocks M) 1) ≡ just (proj₁ (proj₂ w))
                 → 1ℚ ≤ℚ collC (proj₁ w)
  walk-hit-collC sc sg M w eq ext uk' rt' allold rc ol seg = go (collC-01 (poolL (proj₁ w)))
    where
      go : (Comp.state-collisions (poolL (proj₁ w)) ≡ 0ℚ) ⊎ (1ℚ ≤ℚ Comp.state-collisions (poolL (proj₁ w)))
         → 1ℚ ≤ℚ collC (proj₁ w)
      go (inj₂ ge1) = ge1
      go (inj₁ c0)  = ⊥-elim (nothing≢just (trans (sym eq) M-recorded))
        where
          0<len : 0 < length (toBlocks M)
          0<len = subst (0 <_) (sym (toList-len (chunk k M))) (ℕP.n≢0⇒n>0 (≢-nonZero⁻¹ k))
          sv     = snoc-view (toBlocks M) 0<len
          preM   = proj₁ sv
          bk     = proj₁ (proj₂ sv)
          decomp : toBlocks M ≡ preM ++ (bk ∷ [])
          decomp = proj₂ (proj₂ sv)
          posk   : 1 + length preM ≡ k
          posk   = snoc-len M preM bk decomp
          seg2   : runPath (stepT (proj₁ w)) IV (labels preM 1 ++ ((bk , 1 + length preM) ∷ [])) ≡ just (proj₁ (proj₂ w))
          seg2   = subst (λ z → runPath (stepT (proj₁ w)) IV z ≡ just (proj₁ (proj₂ w))) (labels-++ preM bk 1)
                     (subst (λ z → runPath (stepT (proj₁ w)) IV (labels z 1) ≡ just (proj₁ (proj₂ w))) decomp seg)
          sinv   = runPath-snoc-inv (stepT (proj₁ w)) IV (labels preM 1) (bk , 1 + length preM) (proj₁ (proj₂ w)) seg2
          vprev  = proj₁ sinv
          runM   : runPath (stepT (proj₁ w)) IV (labels preM 1) ≡ just vprev
          runM   = proj₁ (proj₂ sinv)
          finalk : stepT (proj₁ w) vprev (bk , k) ≡ just (proj₁ (proj₂ w))
          finalk = subst (λ z → stepT (proj₁ w) vprev (bk , z) ≡ just (proj₁ (proj₂ w))) posk (proj₂ (proj₂ sinv))
          own    = ol vprev bk (proj₁ (proj₂ w)) (allold vprev bk (proj₁ (proj₂ w)) finalk)
          M'     = proj₁ own
          h'     = proj₁ (proj₂ own)
          lk'    : General.lookup-bs sg M' ≡ just h'
          lk'    = proj₁ (proj₂ (proj₂ own))
          pre'   = proj₁ (proj₂ (proj₂ (proj₂ own)))
          blkeq' : toBlocks M' ≡ pre' ++ (bk ∷ [])
          blkeq' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ own))))
          run'   : runPath (stepT sc) IV (labels pre' 1) ≡ just vprev
          run'   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ own))))
          posk'  : 1 + length pre' ≡ k
          posk'  = snoc-len M' pre' bk blkeq'
          runMk  : runPath (stepT<k (proj₁ w)) IV (labels preM 1) ≡ just vprev
          runMk  = trans (runPath-≡<k (proj₁ w) IV preM 1 (ℕP.≤-reflexive posk)) runM
          runM'k : runPath (stepT<k (proj₁ w)) IV (labels pre' 1) ≡ just vprev
          runM'k = trans (runPath-≡<k (proj₁ w) IV pre' 1 (ℕP.≤-reflexive posk'))
                         (runPath-⊒ (proj₁ w) sc ext IV (labels pre' 1) vprev run')
          lengtheq : length (labels preM 1) ≡ length (labels pre' 1)
          lengtheq = trans (labels-length preM 1)
                       (trans (ℕP.suc-injective (trans posk (sym posk'))) (sym (labels-length pre' 1)))
          preM≡pre' : preM ≡ pre'
          preM≡pre' = labels-inj preM pre' 1
                        (unique-run (stepT<k (proj₁ w)) (codet<k (proj₁ w) c0)
                          (labels preM 1) (labels pre' 1) lengtheq runMk runM'k)
          M-recorded : General.lookup-bs sg M ≡ just h'
          M-recorded = subst (λ M0 → General.lookup-bs sg M0 ≡ just h')
                         (sym (toBlocks-inj M M' (trans decomp (trans (cong (_++ (bk ∷ [])) preM≡pre') (sym blkeq')))))
                         lk'

  -- MISS residual, PROVEN: a final key present in sc' is either OLD (owned by an
  -- existing recording, upgraded) or M's OWN last call (owned by the new recording).
  walk-owned : ∀ sc sg M (w : Comp.Table × (CV × Bool))
             → General.lookup-bs sg M ≡ nothing
             → (proj₁ w ⊒ sc)
             → (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u'
                  → (stepT sc v' (b' , k) ≡ just u') ⊎ FinalCallOf IV (toBlocks M) 1 (proj₁ w) v' b')
             → RecChains sc sg → OwnedLast sc sg
             → OwnedLast (proj₁ w) ((M , proj₁ (proj₂ w)) ∷ sg)
  walk-owned sc sg M w eq ext dich rc ol v' b w'' e with dich v' b w'' e
  ... | inj₂ (pre , blkeq , run') =
        M , proj₁ (proj₂ w) , G-lookup-cons-here M (proj₁ (proj₂ w)) sg , pre , blkeq , run'
  ... | inj₁ old with ol v' b w'' old
  ...   | (M' , h' , lk' , pre , blkeq , run') =
          M' , h'
          , trans (G-lookup-cons-≢ M (proj₁ (proj₂ w)) sg M' M'≢M) lk'
          , pre , blkeq , runPath-⊒ (proj₁ w) sc ext IV (labels pre 1) v' run'
        where
          M'≢M : M' ≢ M
          M'≢M p = nothing≢just (trans (sym eq)
                     (subst (λ z → General.lookup-bs sg z ≡ just h') p lk'))

  -- NEW-message preservation, ASSEMBLED: UniqueKeys/Rooted/RecChains PROVEN via
  -- `walk-supp`; OwnedLast (miss) and the birthday descent (hit) are the residuals.
  mdInv-good-new : ∀ sc sg i M
    → UniqueKeys sc × Rooted sc × RecChains sc sg × OwnedLast sc sg
    → General.lookup-bs sg M ≡ nothing
    → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (false , sc , sg) nothing)
  mdInv-good-new sc sg i M (uk , rt , rc , ol) eq =
    OnSupport-bind (walk sc IV (toBlocks M) 1)
      (λ w → newAns i M sg (proj₂ (proj₂ w) ∨ false) (proj₁ w) (proj₁ (proj₂ w)))
      (OnSupport-∧ (walk sc IV (toBlocks M) 1)
        (walk-supp sc IV (toBlocks M) 1 uk rt (ListAny.here refl) (cong suc (toList-len (chunk k M))))
        (walk-fk sc IV (toBlocks M) 1 (cong suc (toList-len (chunk k M)))))
      cont
    where
      cont : ∀ w → Bnd sc IV (toBlocks M) 1 w × FKout sc IV (toBlocks M) 1 w
           → OnSupport (λ t → MDInv (proj₁ t))
               (newAns i M sg (proj₂ (proj₂ w) ∨ false) (proj₁ w) (proj₁ (proj₂ w)))
      cont w ((ext , uk' , rt' , seg) , (_ , dich)) with proj₂ (proj₂ w)
      ... | true  = OnSupport-bind Comp.uniform-Out
                      (λ u → return-ℚ ((true , proj₁ w , (M , u) ∷ sg) , ((i , proj₁ (proj₂ w)) , (i , u))))
                      (os-⊤ Comp.uniform-Out)
                      (λ u _ → OnSupport-return
                         ( (λ _ → walk-hit-collC sc sg M w eq ext uk' rt' dich-old rc ol seg)
                         , (λ ()) ))
        where
          dich-old : ∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u' → stepT sc v' (b' , k) ≡ just u'
          dich-old v' b' u' e with dich v' b' u' e
          ... | inj₁ old = old
          ... | inj₂ (_ , ())
      ... | false = OnSupport-return
                      ( (λ ())
                      , (λ _ → uk' , rt'
                             , rec-extend sc sg (proj₁ w) M (proj₁ (proj₂ w)) ext seg rc
                             , walk-owned sc sg M w eq ext dich-owned rc ol) )
        where
          dich-owned : ∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u'
                     → (stepT sc v' (b' , k) ≡ just u') ⊎ FinalCallOf IV (toBlocks M) 1 (proj₁ w) v' b'
          dich-owned v' b' u' e with dich v' b' u' e
          ... | inj₁ old = inj₁ old
          ... | inj₂ (fc , _) = inj₂ fc

  -- unflagged preservation, ASSEMBLED: repeat branch PROVEN, new branch residual.
  mdInv-pres-good : ∀ sc sg i M
    → UniqueKeys sc × Rooted sc × RecChains sc sg × OwnedLast sc sg
    → OnSupport (λ t → MDInv (proj₁ t)) (C.realK (false , sc , sg) (i , M))
  mdInv-pres-good sc sg i M st =
    OnSupport-Dmap C.fR (respB (false , sc , sg) (i , M)) inner
    where
      inner : OnSupport (λ t → MDInv (proj₁ t))
                (respB' i M (false , sc , sg) (General.lookup-bs sg M))
      inner with General.lookup-bs sg M in eq
      ... | just h  = mdInv-good-repeat sc sg i M h st eq
      ... | nothing = mdInv-good-new sc sg i M st eq

  -- one-query preservation, ASSEMBLED: flagged branch PROVEN, unflagged residual.
  mdInv-pres : Preserved MDInv C.realK
  mdInv-pres (f , sc , sg) (i , M) inv with f
  ... | true  = OnSupport-Dmap C.fR (respB (true , sc , sg) (i , M))
                  (flagged-step sc sg i M (proj₁ inv refl))
  ... | false = mdInv-pres-good sc sg i M (proj₂ inv refl)

  mdInv : MDInvData
  mdInv = record
    { Inv = MDInv ; inv₀ = MDInv₀ ; pres = mdInv-pres
    ; flag⇒coll = λ s inv eq → proj₁ inv eq }

  -- the certificate, ASSEMBLED (all probabilistic fields PROVEN)
  md-cert : SuperCert C.realK proj₁ (false , [] , []) bound
  md-cert = record
    { Inv    = MDInvData.Inv mdInv
    ; φ      = φMD
    ; inv₀   = MDInvData.inv₀ mdInv
    ; pres   = MDInvData.pres mdInv
    ; φ-nn   = λ m s _ → φ-nn m s
    ; φ-bad  = λ m s inv eq → ≤-trans (MDInvData.flag⇒coll mdInv s inv eq)
                                      (x≤x+c (collC (proj₁ (proj₂ s)))
                                             (0≤Γ (pool (proj₁ (proj₂ s))) (m * (k ∸ 1))))
    ; φ-step = λ m s q _ → φ-step m s q
    ; φ-init = φ-init
    }

  -- the ADAPTIVE birthday bound, PROVEN from the certificate
  bad-bound : ∀ n d → asks≤ n d
            → badProb C.realK proj₁ (false , [] , []) d ≤ℚ bound n
  bad-bound n d le = badProb-bounded md-cert n d le

  -- advantage of any adaptive n-query distinguisher ≤ bound n
  indistinguishable : General.M ≈ℰ[ bound ] (MD ⊚ Comp.M)
  indistinguishable n d le =
    subst (_≤ℚ bound n) (sym (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) xEq yEq))
          (≤-trans (C.FLGP (false , [] , []) d) (bad-bound n d le))
    where
      -- (a single `subst` instead of a 4-fold `rewrite`: each `rewrite` step
      -- re-normalizes the whole goal, which costs minutes here)
      xEq : Pr₁⊥ (run⊥ ⟦ General.M ⟧cl d) ≡ Pr₁ (runWith C.idealK (false , [] , []) d)
      xEq = trans (⟦General⟧-sem d) (ideal-marginal d)
      yEq : Pr₁⊥ (run⊥ ⟦ MD ⊚ Comp.M ⟧cl d) ≡ Pr₁ (runWith C.realK (false , [] , []) d)
      yEq = trans (⟦MD⟧-sem d) (sym (ghost-erase false [] [] d))

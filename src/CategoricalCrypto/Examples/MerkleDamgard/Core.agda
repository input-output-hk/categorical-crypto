{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

--------------------------------------------------------------------------------
-- MERKLE–DAMGÅRD: the cryptographic content, machine-free.
--
-- Everything the security proof rests on that never mentions a machine: the
-- real and ideal reactive kernels (`respR`, `respG`), the coupling, the Fundamental Lemma of Game-Playing application,
-- the birthday certificate `md-cert` and the adaptive bound `bad-bound`.  The
-- protocols, the composite `md ∘ᵖ comp` and the theorem `indistinguishable`
-- are `Examples.MerkleDamgard`; the split is what keeps a change to the
-- protocol layer from re-elaborating the crypto.
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
-- These use no probabilistic assumption: expectation monotonicity, linearity,
-- boundedness of `Pr₁` and the expectation triangle inequality are all theorems
-- of the `Dist-ℚ` layer.
--
-- The `bad-bound` side is reduced to a NON-adaptive per-step certificate:
--   • `badProb-super` (PROVEN) — the supermartingale bound: an invariant `Inv`
--     preserved on support plus a potential `φ` that dominates 1 on bad states
--     and never increases in expectation per query bounds the bad-probability of
--     ANY adaptive distinguisher by the initial potential.  This carries the
--     whole adaptivity argument; `bad-bound` is PROVEN from `md-cert`,
--     which is itself ASSEMBLED (not assumed) below.
--
-- The certificate's PROBABILISTIC side is PROVEN:
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
-- `badProb-super`, FLGP, `ideal-marginal` and `ghost-erase` — all proven — this
-- module carries no assumption at all and is `--safe`.
--
-- Warm single-module typecheck: ~34 s (measured 2026-09-10, `+RTS -M8G -H1G`).
--------------------------------------------------------------------------------

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_; Stable)
open import Data.Nat using (_+_; _*_; _≤_; _<_; _∸_; NonZero; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (_<?_)
import Data.Nat.Properties as ℕP
open import Data.Fin using (Fin; zero)
open import Data.Vec using (Vec; []; _∷_; toList) renaming (take to takeᵛ; drop to dropᵛ; replicate to replicateᵛ)
import Data.Vec as DV
open import Data.List using (_++_; length)
import Data.List as L
open import Data.List.Properties using (∷-injective; length-++)
open import Data.Maybe.Ext using (just≢nothing; nothing≢just)
import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; nonNegative)
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_; _≟_ to _≟ℚ_)
open import Data.Rational.Properties using
  ( ≤-trans; ≤-refl; ≤-reflexive; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤
  ; *-zeroˡ; *-monoʳ-≤-nonNeg
  ; +-assoc; +-comm; +-identityˡ; +-identityʳ; ≤-antisym; 1≢0 )
open import Data.Rational.Properties.Ext
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as ListAll
open import Data.List.Run
open import Data.Vec.Properties using (length-toList)
open import Data.Vec.Properties.Ext using (take-drop-inj)
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform using
  (0≤fromℕ; inv-pow-2; fromℕ; fromℕ-+; δ; P-uniform-Vec)
import ProbabilisticLogic.Distribution.Uniform.Birthday as Birthday

module CategoricalCrypto.Examples.MerkleDamgard.Core where

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
    -- 4-input compression oracle (Theorem 3.1 — the citation is for the
    -- construction; what is formalized here is the weaker single-oracle
    -- statement, `f` hidden and no simulator, see `Examples.MerkleDamgard`):
    -- tagging each call with the message length and block index — the
    -- prefix-free encoding — makes `f` an independent random oracle per
    -- (length, index):  (chaining , block , ⟨length⟩ , ⟨index⟩) ↦ n bits.
    open RandomOracle p (CV × Blk × ℕ × ℕ) n public

  module General where
    open RandomOracle p (Vec Bool (k * n)) n public

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
  MDState : Type
  MDState = Maybe (Fin p × ℕ × List Blk)   -- idle, or (party, next block index, remaining blocks)

  ------------------------------------------------------------------------
  -- Security via the reactive model + Fundamental Lemma of Game-Playing.
  -- `MD ⊚ Comp.M` with the compression hidden is INDISTINGUISHABLE from a
  -- variable-length random oracle: advantage `bound n` against any adaptive
  -- n-query distinguisher.  No simulator, so this is not indifferentiability.

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
  -- a coin moves neither state, so both sides average the same branches
  ghost-erase f sc sg (coin μ k) =
    trans (Pr₁-bind μ (λ b → runWith C.realK (f , sc , sg) (k b)))
   (trans (lookupᴰℚ-cong-P (entries μ) (λ b → ghost-erase f sc sg (k b)))
          (sym (Pr₁-bind μ (λ b → runWith respR sc (k b)))))

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
    ideal-marginal-gen (coin μ k) f sc sgG =
      trans (Pr₁-bind μ (λ b → runWith respG sgG (k b)))
     (trans (lookupᴰℚ-cong-P (entries μ) (λ b → ideal-marginal-gen (k b) f sc sgG))
            (sym (Pr₁-bind μ (λ b → runWith C.idealK (f , sc , sgG) (k b)))))

  -- ★ THE KEY LEMMA, PROVEN: the coupling's ideal view IS the variable-length
  -- random oracle — EXACTLY, not up to ε (the ε lives only in FLGP/bad-bound).
  ideal-marginal : ∀ d
    → Pr₁ (runWith respG [] d) ≡ Pr₁ (runWith C.idealK (false , [] , []) d)
  ideal-marginal d = ideal-marginal-gen d false [] []

  ------------------------------------------------------------------------
  -- THE BIRTHDAY POTENTIAL, PROVEN.
  -- φ = collision count + triangle budget for the remaining interior samples.
  -- φ is an EXACT martingale along the walk: an interior miss creates
  -- `pool` expected collision pairs (the PROVEN `E-collisions`) and spends
  -- exactly `pool` from the budget; final calls and hits are free.

  open Birthday n

  -- the triangle slice `Γ` sums, as a rational
  sumR : ℕ → ℕ → ℚ
  sumR t j = fromℕ (sumN t j)

  φsc : ℕ → Comp.Table → ℚ
  φsc m sc = collC sc +ℚ Γ (pool sc) (m * (k ∸ 1))

  φMD : ℕ → FState → ℚ
  φMD m s = φsc m (proj₁ (proj₂ s))

  private
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

    -- triangle facts
    tri-mono : ∀ {a b} → a ≤ b → Comp.triangle a ≤ℚ Comp.triangle b
    tri-mono le = go _ _ (ℕP.≤⇒≤′ le)
      where go : ∀ a b → a ≤′ b → Comp.triangle a ≤ℚ Comp.triangle b
            go a .a ≤′-refl        = ≤-refl
            go a _ (≤′-step {b} pf) = ≤-trans (go a b pf) (x≤c+x _ (0≤fromℕ b))

    sumR-tri : ∀ t j → Comp.triangle t +ℚ sumR t j ≡ Comp.triangle (t + j)
    sumR-tri t zero    = trans (+-identityʳ _) (cong Comp.triangle (sym (ℕP.+-identityʳ t)))
    sumR-tri t (suc j) =
      trans (cong (Comp.triangle t +ℚ_) (fromℕ-+ t (sumN (suc t) j)))
     (trans (sym (+-assoc (Comp.triangle t) (fromℕ t) (sumR (suc t) j)))
     (trans (cong (_+ℚ sumR (suc t) j) (+-comm (Comp.triangle t) (fromℕ t)))
     (trans (sumR-tri (suc t) j) (cong Comp.triangle (sym (ℕP.+-suc t j))))))

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

    suc∸1 : ∀ j → .⦃ _ : NonZero j ⦄ → suc (j ∸ 1) ≡ j
    suc∸1 zero    = ⊥-elim (≢-nonZero⁻¹ zero refl)
    suc∸1 (suc j) = refl

    -- ★ THE WALK MARTINGALE — forward-declared, detach-style
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
               (+-monoʳ-≤ (collC sc) (Γ-mono (pool sc) (length bs'' + m * (k ∸ 1)))))
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
        pr = cong suc (length-toList (chunk k M))
        tail-eq : (length (toBlocks M) ∸ 1) + m * (k ∸ 1) ≡ suc m * (k ∸ 1)
        tail-eq = cong (λ z → (z ∸ 1) + m * (k ∸ 1)) (length-toList (chunk k M))
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
  -- ★ THE CHAIN-FOREST INVARIANT, defined CONCRETELY.  The table is
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
    os-⊤ μ = ListAll.universal (λ _ → tt) (NE.toList (entries μ))

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
      (trans (sym (cong length dec)) (length-toList (chunk k M0))))

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
          0<len = subst (0 <_) (sym (length-toList (chunk k M))) (ℕP.n≢0⇒n>0 (≢-nonZero⁻¹ k))
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
        (walk-supp sc IV (toBlocks M) 1 uk rt (ListAny.here refl) (cong suc (length-toList (chunk k M))))
        (walk-fk sc IV (toBlocks M) 1 (cong suc (length-toList (chunk k M)))))
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


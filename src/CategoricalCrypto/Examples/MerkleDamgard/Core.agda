{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

--------------------------------------------------------------------------------
-- MERKLE–DAMGÅRD: the cryptographic content, machine-free.
--
-- The real and ideal reactive kernels (`respR`, `respG`), the coupling `respB`
-- and the three facts `GamePlaying.Hop.hop-bound` consumes; the protocols, the
-- composite `md ∘ᵖ comp` and the theorem `indistinguishable` are
-- `Examples.MerkleDamgard`, a split that keeps a change to the protocol layer
-- from re-elaborating the crypto.
--
--   • `ideal-marginal` — the coupling's ideal view IS the variable-length RO,
--     exactly.  The coupling raises its flag whenever the MD answer fails to be
--     a fresh uniform, so repeats are answered by the flag's own check
--     (`pointRep`) and an unflagged final call's sample detaches as one uniform
--     draw (`detach`): no combinatorial invariant is needed on this side.
--   • `ghost-erase` — flag and ghost table are invisible to the real world,
--     whose kernel marginalises back to `mdRun` (`walkR`).
--   • `md-cert` — the birthday supermartingale certificate: potential `φMD`,
--     and the chain-forest invariant `MDInv`, whose flag-raising case is the
--     birthday descent `walk-hit-collC`.
--------------------------------------------------------------------------------

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_; Stable)
open import Data.Nat using (_+_; _*_; _≤_; _<_; _∸_; NonZero; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (_<?_)
import Data.Nat.Properties as ℕP
open import Data.Fin using (Fin; zero)
open import Data.Vec using (Vec; []; _∷_; toList) renaming (take to takeᵛ; drop to dropᵛ)
import Data.Vec as DV
open import Data.List
import Data.List as L
open import Data.List.Properties
open import Data.Maybe.Ext
import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.AllPairs
open import Data.Sum
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; nonNegative)
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_; _≟_ to _≟ℚ_)
open import Data.Rational.Properties using
  ( ≤-trans; ≤-refl; ≤-reflexive; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤
  ; *-zeroˡ; *-monoʳ-≤-nonNeg
  ; +-assoc; +-comm; +-identityˡ; +-identityʳ; ≤-antisym; 1≢0 )
open import Data.Rational.Properties.Ext
open import Algebra.Bundles
import Algebra.Properties.CommutativeSemigroup as CSP
import Data.Rational.Properties as ℚP
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ)
open import Data.Maybe.Properties
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as ListAll
open import Data.List.Run
open import Data.Vec.Properties using (length-toList)
open import Data.Vec.Properties.Ext
open import Function.Base
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Partial using (cond; cond-diag)
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform
import ProbabilisticLogic.Distribution.Uniform.Birthday as Birthday

module CategoricalCrypto.Examples.MerkleDamgard.Core where

open CSP (CommutativeMonoid.commutativeSemigroup ℚP.+-0-commutativeMonoid)

-- `k ≥ 1` is REQUIRED: for `k = 0` every message hashes deterministically to
-- `IV` while `bound ≡ 0`, so `indistinguishable` would be false.
module MD (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

  p : ℕ
  p = 1

  CV  : Type
  CV  = Vec Bool n
  Blk : Type
  Blk = Vec Bool n

  -- 4-input compression oracle (Coron–Dodis–Malinaud–Puniya, "Merkle-Damgård
  -- Revisited", the construction in the proof of Thm 3.1; the statement
  -- formalized is weaker, see `Examples.MerkleDamgard`): tagging each call with
  -- the message length and block index — the prefix-free encoding — makes `f`
  -- an independent random oracle per (length, index).
  module Comp    = RandomOracle p (CV × Blk × ℕ × ℕ) n
  module General = RandomOracle p (Vec Bool (k * n)) n

  pack : CV → Blk → ℕ → CV × Blk × ℕ × ℕ
  pack h b idx = (h , b , k , idx)

  chunk : ∀ j → Vec Bool (j * n) → Vec (Vec Bool n) j
  chunk zero    v = []
  chunk (suc j) v = takeᵛ n v ∷ chunk j (dropᵛ n v)

  toBlocks : Vec Bool (k * n) → List Blk
  toBlocks v = toList (chunk k v)

  toBlocks-length : (M : Vec Bool (k * n)) → length (toBlocks M) ≡ k
  toBlocks-length M = length-toList (chunk k M)

  i₀ : Fin p
  i₀ = zero

  mdRun : Comp.Table → CV → List Blk → ℕ → Dist-ℚ (Comp.Table × CV)
  mdRun s h []       idx = return-ℚ (s , h)
  mdRun s h (b ∷ bs) idx =
    Comp.step (s , i₀ , pack h b idx) >>=ᴹ λ o → mdRun (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)

  respR : Comp.Table → General.Input → Dist-ℚ (Comp.Table × General.Output)
  respR s (i , M) = mdRun s IV (toBlocks M) 1 >>=ᴹ λ sh → return-ℚ (proj₁ sh , (i , proj₂ sh))

  -- The *structural* chaining collision: a coincidence among {IV} ∪ {interior
  -- chaining values} (interior = outputs of NON-final calls, idx < len).  A
  -- collision among FINAL hashes is harmless — those values are never extended,
  -- and the ideal RO has exactly such coincidences.
  interior : Comp.Table → Comp.Table
  interior []                                   = []
  interior (e@((_ , _ , len , idx) , _) ∷ es) = case idx <? len of λ where
    (yes _) → e ∷ interior es
    (no  _) → interior es

  ivEntry : (CV × Blk × ℕ × ℕ) × CV
  ivEntry = ((IV , IV , 0 , 0) , IV)

  poolL : Comp.Table → Comp.Table
  poolL sc = ivEntry ∷ interior sc

  pool : Comp.Table → ℕ
  pool sc = length (poolL sc)

  collC : Comp.Table → ℚ
  collC sc = Comp.state-collisions (poolL sc)

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

  FState : Type
  FState = Bool × Comp.Table × General.Table

  callC' : Comp.Table → CV → Blk → ℕ → Maybe CV → Dist-ℚ (Comp.Table × (CV × Bool))
  callC' s h b idx (just hm) = return-ℚ (s , hm , true)
  callC' s h b idx nothing   =
    Comp.uniform-Out >>=ᴹ λ hm → return-ℚ ((pack h b idx , hm) ∷ s , hm , false)

  callC : Comp.Table → CV → Blk → ℕ → Dist-ℚ (Comp.Table × (CV × Bool))
  callC s h b idx = callC' s h b idx (Comp.lookup-bs s (pack h b idx))

  walk : Comp.Table → CV → List Blk → ℕ → Dist-ℚ (Comp.Table × (CV × Bool))
  walk s h []               idx = return-ℚ (s , h , true)   -- no call ⇒ NOT fresh
  walk s h (b ∷ [])         idx = callC s h b idx
  walk s h (b ∷ bs@(_ ∷ _)) idx =
    callC s h b idx >>=ᴹ λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs (suc idx)

  newAns : Fin p → Vec Bool (k * n) → General.Table
         → Bool → Comp.Table → CV
         → Dist-ℚ (FState × (General.Output × General.Output))
  newAns i M sg true  sc' hR = Comp.uniform-Out >>=ᴹ λ u →
    return-ℚ ((true , sc' , (M , u) ∷ sg) , ((i , hR) , (i , u)))
  newAns i M sg false sc' hR =
    return-ℚ ((false , sc' , (M , hR) ∷ sg) , ((i , hR) , (i , hR)))

  repAns : Fin p → General.Table → Bool → CV → Comp.Table × (CV × Bool)
         → FState × (General.Output × General.Output)
  repAns i sg f h w = ((not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ f , proj₁ w , sg)
                    , ((i , proj₁ (proj₂ w)) , (i , h))

  respB' : Fin p → Vec Bool (k * n) → FState → Maybe CV
         → Dist-ℚ (FState × (General.Output × General.Output))
  respB' i M (f , sc , sg) (just h) =
    walk sc IV (toBlocks M) 1 >>=ᴹ λ w → return-ℚ (repAns i sg f h w)
  respB' i M (f , sc , sg) nothing =
    walk sc IV (toBlocks M) 1 >>=ᴹ λ w →
    newAns i M sg (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))

  respB : FState → General.Input → Dist-ℚ (FState × (General.Output × General.Output))
  respB s (i , M) = respB' i M s (General.lookup-bs (proj₂ (proj₂ s)) M)

  module C = Coupling {St = FState} proj₁ respB

  respG : General.Table → General.Input → Dist-ℚ (General.Table × General.Output)
  respG sg q = General.step (sg , q)

  private
    callC-marg : ∀ sc h b idx (P : Comp.Table × CV → ℚ)
               → E (callC sc h b idx) (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w)))
               ≡ E (Comp.step (sc , i₀ , pack h b idx)) (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o)))
    callC-marg sc h b idx P with Comp.lookup-bs sc (pack h b idx)
    ... | just hm = trans (lookupᴰℚ-return (sc , hm , true)
                            (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
                          (sym (lookupᴰℚ-return (sc , i₀ , hm)
                            (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o)))))
    ... | nothing =
      trans (lookupᴰℚ-Dmap (λ hm → (pack h b idx , hm) ∷ sc , hm , false) Comp.uniform-Out
              (λ (w : Comp.Table × (CV × Bool)) → P (proj₁ w , proj₁ (proj₂ w))))
            (sym (lookupᴰℚ-Dmap (λ hm → (pack h b idx , hm) ∷ sc , i₀ , hm) Comp.uniform-Out
                   (λ (o : Comp.Table × Comp.Output) → P (proj₁ o , proj₂ (proj₂ o)))))

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

  private
    ErasesTo : FState → Comp.Table → Type
    ErasesTo s sc = proj₁ (proj₂ s) ≡ sc

    stepR : ∀ s i M (F : FState × General.Output → ℚ) (F′ : Comp.Table × General.Output → ℚ)
          → (∀ t t′ → ErasesTo (proj₁ t) (proj₁ t′) → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
          → E (C.realK s (i , M)) F ≡ E (respR (proj₁ (proj₂ s)) (i , M)) F′
    stepR (f , sc , sg) i M F F′ agree = aux (General.lookup-bs sg M) refl
      where
        μW = walk sc IV (toBlocks M) 1
        μM = mdRun sc IV (toBlocks M) 1

        walkE : E μW (λ (w : Comp.Table × (CV × Bool)) → F′ (proj₁ w , (i , proj₁ (proj₂ w))))
              ≡ E (respR sc (i , M)) F′
        walkE = trans (walkR sc IV (toBlocks M) 1 (λ sh → F′ (proj₁ sh , (i , proj₂ sh))))
                      (sym (lookupᴰℚ-Dmap (λ sh → proj₁ sh , (i , proj₂ sh)) μM F′))

        newAnsE : ∀ bb sc′ hRv → E (newAns i M sg bb sc′ hRv) (λ t → F (C.fR t))
                               ≡ F′ (sc′ , (i , hRv))
        newAnsE true sc′ hRv =
          trans (lookupᴰℚ-Dmap (λ u → (true , sc′ , (M , u) ∷ sg) , ((i , hRv) , (i , u)))
                  Comp.uniform-Out (λ t → F (C.fR t)))
         (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ u →
                   agree ((true , sc′ , (M , u) ∷ sg) , (i , hRv)) (sc′ , (i , hRv)) refl refl))
                (E-const Comp.uniform-Out (F′ (sc′ , (i , hRv)))))
        newAnsE false sc′ hRv =
          trans (lookupᴰℚ-return ((false , sc′ , (M , hRv) ∷ sg) , ((i , hRv) , (i , hRv)))
                  (λ t → F (C.fR t)))
                (agree ((false , sc′ , (M , hRv) ∷ sg) , (i , hRv)) (sc′ , (i , hRv)) refl refl)

        aux : ∀ mv → General.lookup-bs sg M ≡ mv
            → E (C.realK (f , sc , sg) (i , M)) F ≡ E (respR sc (i , M)) F′
        aux (just h) eq =
          trans (cong (λ μ → E (Dmap C.fR μ) F) (cong (respB' i M (f , sc , sg)) eq))
         (trans (lookupᴰℚ-Dmap C.fR (respB' i M (f , sc , sg) (just h)) F)
         (trans (lookupᴰℚ-Dmap tupR μW (λ t → F (C.fR t)))
         (trans (lookupᴰℚ-cong-P (entries μW) (λ w →
                   agree (C.fR (tupR w)) (proj₁ w , (i , proj₁ (proj₂ w))) refl refl))
                walkE)))
          where
            tupR = repAns i sg f h
        aux nothing eq =
          trans (cong (λ μ → E (Dmap C.fR μ) F) (cong (respB' i M (f , sc , sg)) eq))
         (trans (lookupᴰℚ-Dmap C.fR (respB' i M (f , sc , sg) nothing) F)
         (trans (E-bind μW
                  (λ (w : Comp.Table × (CV × Bool)) →
                     newAns i M sg (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w)))
                  (λ t → F (C.fR t)))
         (trans (lookupᴰℚ-cong-P (entries μW)
                  (λ w → newAnsE (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))))
                walkE)))

    stepR-bisim : StepBisim C.realK respR ErasesTo
    stepR-bisim s sc rel (i , M) F F′ agree =
      subst (λ z → E (C.realK s (i , M)) F ≡ E (respR z (i , M)) F′) rel
            (stepR s i M F F′ agree)

  ghost-erase : ∀ f sc sg d
              → Pr₁ (runWith C.realK (f , sc , sg) d) ≡ Pr₁ (runWith respR sc d)
  ghost-erase f sc sg d =
    runWith-bisim C.realK respR ErasesTo stepR-bisim d (f , sc , sg) sc refl

  private
    -- Freshness detachment: walking the chain and testing `G` on the final
    -- value — with the uniform average produced instead whenever the final call
    -- HIT or the flag was already up — IS the uniform average.  At a fresh final
    -- call the sampled value detaches as one uniform draw; every earlier step
    -- averages out (`E-const`).
    dInt : (CV → ℚ) → Bool → Comp.Table × (CV × Bool) → ℚ
    dInt G f w = cond (proj₂ (proj₂ w) ∨ f) (E Comp.uniform-Out G) (G (proj₁ (proj₂ w)))

    condE : ∀ (G : CV → ℚ) f
          → E Comp.uniform-Out (λ hm → cond f (E Comp.uniform-Out G) (G hm))
          ≡ E Comp.uniform-Out G
    condE G true  = E-const Comp.uniform-Out (E Comp.uniform-Out G)
    condE G false = refl

    -- `detachL` takes the lookup result as an ARGUMENT, which keeps the recursion
    -- structurally decreasing (the device at every `walk-*L/C`).
    detach : ∀ (G : CV → ℚ) f sc h bs idx
           → E (walk sc h bs idx) (dInt G f) ≡ E Comp.uniform-Out G
    detachL : ∀ (G : CV → ℚ) f sc h b idx (m : Maybe CV)
            → E (callC' sc h b idx m) (dInt G f) ≡ E Comp.uniform-Out G

    detach G f sc h [] idx = lookupᴰℚ-return (sc , h , true) (dInt G f)
    detach G f sc h (b ∷ []) idx =
      detachL G f sc h b idx (Comp.lookup-bs sc (pack h b idx))
    detach G f sc h (b ∷ b' ∷ bs) idx =
      trans (E-bind (callC sc h b idx)
              (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx)) (dInt G f))
     (trans (lookupᴰℚ-cong-P (entries (callC sc h b idx))
              (λ w → detach G f (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx)))
            (E-const (callC sc h b idx) (E Comp.uniform-Out G)))

    detachL G f sc h b idx (just hm) = lookupᴰℚ-return (sc , hm , true) (dInt G f)
    detachL G f sc h b idx nothing =
      trans (lookupᴰℚ-Dmap (λ hm → (pack h b idx , hm) ∷ sc , hm , false) Comp.uniform-Out
              (dInt G f))
            (condE G f)

    Ghosts : General.Table → FState → Type
    Ghosts sgG s = proj₂ (proj₂ s) ≡ sgG

    stepI : ∀ f sc sg i M (F : General.Table × General.Output → ℚ)
              (F′ : FState × General.Output → ℚ)
          → (∀ t t′ → Ghosts (proj₁ t) (proj₁ t′) → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
          → E (respG sg (i , M)) F ≡ E (C.idealK (f , sc , sg) (i , M)) F′
    stepI f sc sg i M F F′ agree = aux (General.lookup-bs sg M) refl
      where
        μW = walk sc IV (toBlocks M) 1

        G₀ : CV → ℚ
        G₀ u = F ((M , u) ∷ sg , (i , u))

        aux : ∀ mv → General.lookup-bs sg M ≡ mv
            → E (respG sg (i , M)) F ≡ E (C.idealK (f , sc , sg) (i , M)) F′
        aux (just h) eq =
          trans (cong (λ μ → E μ F) (General.step-hit sg i M h eq))
         (trans (lookupᴰℚ-return (sg , i , h) F) (sym idealE))
          where
            tupR = repAns i sg f h

            pointRep : ∀ w → F′ (C.fI (tupR w)) ≡ F (sg , (i , h))
            pointRep w with proj₁ (proj₂ w) ≟ h
            ... | yes q =
              trans (cong (λ z → F′ ((f , proj₁ w , sg) , cond f (i , h) (i , z))) q)
             (trans (cong (λ z → F′ ((f , proj₁ w , sg) , z)) (cond-diag f (i , h)))
                    (sym (agree (sg , (i , h)) ((f , proj₁ w , sg) , (i , h)) refl refl)))
            ... | no ¬q =
              sym (agree (sg , (i , h)) ((true , proj₁ w , sg) , (i , h)) refl refl)

            idealE : E (C.idealK (f , sc , sg) (i , M)) F′ ≡ F (sg , (i , h))
            idealE =
              trans (cong (λ μ → E (Dmap C.fI μ) F′) (cong (respB' i M (f , sc , sg)) eq))
             (trans (lookupᴰℚ-Dmap C.fI (respB' i M (f , sc , sg) (just h)) F′)
             (trans (lookupᴰℚ-Dmap tupR μW (λ t → F′ (C.fI t)))
             (trans (lookupᴰℚ-cong-P (entries μW) pointRep)
                    (E-const μW (F (sg , (i , h)))))))
        aux nothing eq =
          trans (cong (λ μ → E μ F) (General.step-miss sg i M eq))
         (trans lhsE (sym (trans idealE (detach G₀ f sc IV (toBlocks M) 1))))
          where
            lhsE : E (General.uniform-Out >>=ᴹ λ u → return-ℚ ((M , u) ∷ sg , i , u)) F
                 ≡ E Comp.uniform-Out G₀
            lhsE = lookupᴰℚ-Dmap (λ u → (M , u) ∷ sg , i , u) General.uniform-Out F

            newAnsVal : ∀ bb sc′ hRv → E (newAns i M sg bb sc′ hRv) (λ t → F′ (C.fI t))
                                     ≡ cond bb (E Comp.uniform-Out G₀) (G₀ hRv)
            newAnsVal true sc′ hRv =
              trans (lookupᴰℚ-Dmap (λ u → (true , sc′ , (M , u) ∷ sg) , ((i , hRv) , (i , u)))
                      Comp.uniform-Out (λ t → F′ (C.fI t)))
                    (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ u →
                       sym (agree ((M , u) ∷ sg , (i , u))
                              ((true , sc′ , (M , u) ∷ sg) , (i , u)) refl refl)))
            newAnsVal false sc′ hRv =
              trans (lookupᴰℚ-return
                      ((false , sc′ , (M , hRv) ∷ sg) , ((i , hRv) , (i , hRv)))
                      (λ t → F′ (C.fI t)))
                    (sym (agree ((M , hRv) ∷ sg , (i , hRv))
                            ((false , sc′ , (M , hRv) ∷ sg) , (i , hRv)) refl refl))

            idealE : E (C.idealK (f , sc , sg) (i , M)) F′ ≡ E μW (dInt G₀ f)
            idealE =
              trans (cong (λ μ → E (Dmap C.fI μ) F′) (cong (respB' i M (f , sc , sg)) eq))
             (trans (lookupᴰℚ-Dmap C.fI (respB' i M (f , sc , sg) nothing) F′)
             (trans (E-bind μW
                      (λ (w : Comp.Table × (CV × Bool)) →
                         newAns i M sg (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w)))
                      (λ t → F′ (C.fI t)))
                    (lookupᴰℚ-cong-P (entries μW)
                      (λ w → newAnsVal (proj₂ (proj₂ w) ∨ f) (proj₁ w) (proj₁ (proj₂ w))))))

    stepI-bisim : StepBisim respG C.idealK Ghosts
    stepI-bisim sgG (f , sc , sg) rel (i , M) F F′ agree =
      subst (λ z → E (respG z (i , M)) F ≡ E (C.idealK (f , sc , sg) (i , M)) F′) rel
            (stepI f sc sg i M F F′ agree)

  ideal-marginal : ∀ d
    → Pr₁ (runWith respG [] d) ≡ Pr₁ (runWith C.idealK (false , [] , []) d)
  ideal-marginal d =
    runWith-bisim respG C.idealK Ghosts stepI-bisim d [] (false , [] , []) refl

  ------------------------------------------------------------------------
  -- The birthday potential: φ = collision count + triangle budget for the
  -- remaining interior samples, an EXACT martingale along the walk.  An
  -- interior miss creates `pool` expected collision pairs (`E-collisions`) and
  -- spends exactly `pool` from the budget; final calls and hits are free.

  open Birthday n

  sumR : ℕ → ℕ → ℚ
  sumR t j = fromℕ (sumN t j)

  φsc : ℕ → Comp.Table → ℚ
  φsc m sc = collC sc +ℚ Γ (pool sc) (m * (k ∸ 1))

  φMD : ℕ → FState → ℚ
  φMD m s = φsc m (proj₁ (proj₂ s))

  private
    tri-mono : ∀ {a b} → a ≤ b → Comp.triangle a ≤ℚ Comp.triangle b
    tri-mono le = go _ _ (ℕP.≤⇒≤′ le)
      where go : ∀ a b → a ≤′ b → Comp.triangle a ≤ℚ Comp.triangle b
            go a .a ≤′-refl        = ≤-refl
            go a _ (≤′-step {b} pf) = ≤-trans (go a b pf) (p≤q+p _ (0≤fromℕ b))

    sumR-tri : ∀ t j → Comp.triangle t +ℚ sumR t j ≡ Comp.triangle (t + j)
    sumR-tri t zero    = trans (+-identityʳ _) (cong Comp.triangle (sym (ℕP.+-identityʳ t)))
    sumR-tri t (suc j) =
      trans (cong (Comp.triangle t +ℚ_) (fromℕ-+ t (sumN (suc t) j)))
     (trans (sym (+-assoc (Comp.triangle t) (fromℕ t) (sumR (suc t) j)))
     (trans (cong (_+ℚ sumR (suc t) j) (+-comm (Comp.triangle t) (fromℕ t)))
     (trans (sumR-tri (suc t) j) (cong Comp.triangle (sym (ℕP.+-suc t j))))))

    cm-nn : ∀ s h → 0ℚ ≤ℚ Comp.count-matches s h
    cm-nn []            h = ≤-refl
    cm-nn ((_ , v) ∷ s) h = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                    (+-mono-≤ (0≤bool ⌊ h ≟ v ⌋) (cm-nn s h))

    sc-nn : ∀ s → 0ℚ ≤ℚ Comp.state-collisions s
    sc-nn []            = ≤-refl
    sc-nn ((_ , v) ∷ s) = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                                  (+-mono-≤ (cm-nn s v) (sc-nn s))

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
            (interchange (δ IV vv) (Comp.count-matches (interior sc) IV)
                     (Comp.count-matches (interior sc) vv)
                     (Comp.state-collisions (interior sc))))

    interior-step : ∀ idx m → idx + suc (suc m) ≡ suc k → idx < k × suc idx + suc m ≡ suc k
    interior-step idx m pr = ℕP.≤-trans (ℕP.m<m+n idx ℕP.0<1+n) (ℕP.≤-reflexive eq) , cong suc eq
      where eq = ℕP.suc-injective (trans (sym (ℕP.+-suc idx (suc m))) pr)

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
      walk-φC m sc h b (b' ∷ bs) idx (Comp.lookup-bs sc (pack h b idx)) (proj₁ i) (proj₂ i)
      where i = interior-step idx (length bs) pr

    walk-φL m sc h b idx (just hm) _ =
      ≤-reflexive (lookupᴰℚ-return (sc , hm , true) (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
    walk-φL m sc h b idx nothing ¬lt = ≤-reflexive
      (trans (lookupᴰℚ-Dmap (λ hm → (pack h b idx , hm) ∷ sc , hm , false) Comp.uniform-Out
               (λ (w : Comp.Table × (CV × Bool)) → φsc m (proj₁ w)))
      (trans (lookupᴰℚ-cong-P (entries Comp.uniform-Out) (λ hm →
                cong (λ z → Comp.state-collisions (ivEntry ∷ z)
                             +ℚ Γ (length (ivEntry ∷ z)) (m * (k ∸ 1)))
                  (interior-consᶠ h b idx hm sc ¬lt)))
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
        (lookupᴰℚ-Dmap (λ hm → (pack h b idx , hm) ∷ sc , hm , false) Comp.uniform-Out
                 (λ (w : Comp.Table × (CV × Bool)) →
                    E (walk (proj₁ w) (proj₁ (proj₂ w)) (b'' ∷ bs'') (suc idx))
                      (λ (w' : Comp.Table × (CV × Bool)) → φsc m (proj₁ w'))))))
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
                           (cong (λ z → length (ivEntry ∷ z)) (interior-cons< h b idx hm sc lt)))
                         (+-assoc (Comp.count-matches (poolL sc) hm) (collC sc)
                                  (Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))))
         (trans (E-add Comp.uniform-Out
                  (λ hm → Comp.count-matches (poolL sc) hm)
                  (λ _ → collC sc +ℚ Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))
         (trans (cong₂ _+ℚ_
                  (Comp.E-collisions (poolL sc))
                  (E-const Comp.uniform-Out
                    (collC sc +ℚ Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1)))))
         (trans (x∙yz≈y∙xz (fromℕ (pool sc) *ℚ inv-pow-2 n) (collC sc)
                         (Γ (suc (pool sc)) ((length bs'') + m * (k ∸ 1))))
                (cong (collC sc +ℚ_)
                  (Γ-step (pool sc) ((length bs'') + m * (k ∸ 1))))))))))

  private
    newAns-φ : ∀ m i M sg bb sc' hR
             → E (newAns i M sg bb sc' hR) (λ t → φMD m (proj₁ (C.fR t)))
             ≡ φsc m sc'
    newAns-φ m i M sg true sc' hR =
      trans (lookupᴰℚ-Dmap (λ u → (true , sc' , (M , u) ∷ sg) , ((i , hR) , (i , u)))
              Comp.uniform-Out (λ t → φMD m (proj₁ (C.fR t))))
            (E-const Comp.uniform-Out (φsc m sc'))
    newAns-φ m i M sg false sc' hR =
      lookupᴰℚ-return ((false , sc' , (M , hR) ∷ sg) , ((i , hR) , (i , hR)))
        (λ t → φMD m (proj₁ (C.fR t)))

    φ-step : ∀ m s q → E (C.realK s q) (λ sr → φMD m (proj₁ sr)) ≤ℚ φMD (suc m) s
    φ-step m s (i , M) = aux (General.lookup-bs (proj₂ (proj₂ s)) M)
      where
        pr : 1 + length (toBlocks M) ≡ suc k
        pr = cong suc (toBlocks-length M)
        tail-eq : (length (toBlocks M) ∸ 1) + m * (k ∸ 1) ≡ suc m * (k ∸ 1)
        tail-eq = cong (λ z → (z ∸ 1) + m * (k ∸ 1)) (toBlocks-length M)
        aux : (mv : Maybe CV)
            → E (Dmap C.fR (respB' i M s mv)) (λ sr → φMD m (proj₁ sr))
            ≤ℚ φMD (suc m) s
        aux (just h) =
          ≤-trans (≤-reflexive
            (trans (lookupᴰℚ-Dmap C.fR (respB' i M s (just h)) (λ sr → φMD m (proj₁ sr)))
            (lookupᴰℚ-Dmap (repAns i (proj₂ (proj₂ s)) (proj₁ s) h)
                     (walk (proj₁ (proj₂ s)) IV (toBlocks M) 1) (λ t → φMD m (proj₁ (C.fR t))))))
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
      (*-monoʳ-≤-nonNeg _ ⦃ nonNegative (0≤inv-pow-2 n) ⦄
        (≤-trans (≤-reflexive sumR1)
                 (tri-mono arith)))
      where
        N = suc m * (k ∸ 1)
        sumR1 : sumR 1 N ≡ Comp.triangle (suc N)
        sumR1 = trans (sym (+-identityˡ (sumR 1 N)))
               (trans (cong (_+ℚ sumR 1 N) (sym (+-identityʳ 0ℚ)))
                      (sumR-tri 1 N))
        arith : suc N ≤ suc m * k
        arith = ℕP.+-mono-≤ (ℕP.≤-reflexive (ℕP.suc-pred k))
                            (ℕP.*-monoʳ-≤ m (ℕP.m∸n≤m k 1))

  ------------------------------------------------------------------------
  -- The chain-forest invariant.  The table is a labelled transition system on
  -- chaining values (`stepT`); a recorded message denotes a run from IV
  -- (`Chain`) — the shape `unique-run` consumes.

  stepT : Comp.Table → CV → Blk × ℕ → Maybe CV
  stepT sc v (b , j) = Comp.lookup-bs sc (v , b , k , j)

  labels : List Blk → ℕ → List (Blk × ℕ)
  labels []       j = []
  labels (b ∷ bs) j = (b , j) ∷ labels bs (suc j)

  Chain : Comp.Table → Vec Bool (k * n) → CV → Type
  Chain sc M h = runPath (stepT sc) IV (labels (toBlocks M) 1) ≡ just h

  HasVal : Comp.Table → CV → Type
  HasVal t v = ListAny.Any (λ e → proj₂ e ≡ v) t

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
  -- Preservation: the collision count is monotone along the walk, and the
  -- flagged branch of `MDInv`.
  private
    -- Inlined so the single `with ii <? k` reduces `collC` directly —
    -- delegating to `collC-cons<` would create a mismatched second `with`-neutral.
    collC-mono1 : ∀ hh bb ii vv sc → collC sc ≤ℚ collC (((hh , bb , k , ii) , vv) ∷ sc)
    collC-mono1 hh bb ii vv sc with ii <? k
    ... | yes lt = +-mono-≤ (p≤q+p (Comp.count-matches (interior sc) IV) (0≤bool ⌊ IV ≟ vv ⌋))
                            (p≤q+p (Comp.state-collisions (interior sc)) (cm-nn (interior sc) vv))
    ... | no ¬lt = ≤-refl

    callC-collC-mono : ∀ c sc h b idx → c ≤ℚ collC sc
                     → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (callC sc h b idx)
    callC-collC-mono c sc h b idx c≤ = aux (Comp.lookup-bs sc (pack h b idx))
      where aux : ∀ mv → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (callC' sc h b idx mv)
            aux (just hm) = OnSupport-return c≤
            aux nothing   = OnSupport-map Comp.uniform-Out _
              (λ hm → ≤-trans c≤ (collC-mono1 h b idx hm sc))

    walk-collC-mono : ∀ c sc h bs idx → c ≤ℚ collC sc
                    → OnSupport (λ w → c ≤ℚ collC (proj₁ w)) (walk sc h bs idx)
    walk-collC-mono c sc h []            idx c≤ = OnSupport-return c≤
    walk-collC-mono c sc h (b ∷ [])      idx c≤ = callC-collC-mono c sc h b idx c≤
    walk-collC-mono c sc h (b ∷ b' ∷ bs) idx c≤ =
      OnSupport-bind (callC sc h b idx)
        (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx))
        (callC-collC-mono c sc h b idx c≤)
        (λ w c≤w → walk-collC-mono c (proj₁ w) (proj₁ (proj₂ w)) (b' ∷ bs) (suc idx) c≤w)

    MDInv-flagged : ∀ x sc' sg' → 1ℚ ≤ℚ collC sc' → MDInv (x ∨ true , sc' , sg')
    MDInv-flagged x sc' sg' h =
      subst (λ b → MDInv (b , sc' , sg')) (sym (∨-zeroʳ x)) ((λ _ → h) , (λ ()))

    newAns-flagged : ∀ x i' M' sg' sc' hR → 1ℚ ≤ℚ collC sc'
                   → OnSupport (λ t → MDInv (proj₁ t)) (newAns i' M' sg' (x ∨ true) sc' hR)
    newAns-flagged x i' M' sg' sc' hR h rewrite ∨-zeroʳ x =
      OnSupport-map Comp.uniform-Out _
        (λ u → (λ _ → h) , (λ ()))

    flagged-step : ∀ sc sg i M → 1ℚ ≤ℚ collC sc
                 → OnSupport (λ t → MDInv (proj₁ t)) (respB (true , sc , sg) (i , M))
    flagged-step sc sg i M 1≤ = aux (General.lookup-bs sg M)
      where
        aux : ∀ mv → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (true , sc , sg) mv)
        aux (just h) = OnSupport-bind (walk sc IV (toBlocks M) 1)
          (λ w → return-ℚ (repAns i sg true h w))
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
    ⌊≟⌋-refl : ∀ (x : CV) → ⌊ x ≟ x ⌋ ≡ true
    ⌊≟⌋-refl x with x ≟ x
    ... | yes _ = refl
    ... | no ¬p = ⊥-elim (¬p refl)

    walk-replay  : ∀ sc bs v j hf → runPath (stepT sc) v (labels bs j) ≡ just hf
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf) (walk sc v bs j)
    walk-replayL : ∀ sc b v j hf → runPath (stepT sc) v ((b , j) ∷ []) ≡ just hf
                 → (mv : Maybe CV) → Comp.lookup-bs sc (pack v b j) ≡ mv
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf) (callC' sc v b j mv)
    walk-replayC : ∀ sc b bs' v j hf → runPath (stepT sc) v (labels (b ∷ bs') j) ≡ just hf
                 → (mv : Maybe CV) → Comp.lookup-bs sc (pack v b j) ≡ mv
                 → OnSupport (λ w → proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ hf)
                     (callC' sc v b j mv >>=ᴹ (λ u → walk (proj₁ u) (proj₁ (proj₂ u)) bs' (suc j)))

    walk-replay sc []             v j hf rp = OnSupport-return (refl , just-injective rp)
    walk-replay sc (b ∷ [])       v j hf rp = walk-replayL sc b v j hf rp (Comp.lookup-bs sc (pack v b j)) refl
    walk-replay sc (b ∷ b'' ∷ bs) v j hf rp = walk-replayC sc b (b'' ∷ bs) v j hf rp (Comp.lookup-bs sc (pack v b j)) refl

    walk-replayL sc b v j hf rp (just w) eqmv =
      OnSupport-return (refl , just-injective (trans (sym (runPath-step (stepT sc) v (b , j) w [] eqmv)) rp))
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

    mdInv-good-repeat : ∀ sc sg i M h
      → UniqueKeys sc × Rooted sc × RecChains sc sg × OwnedLast sc sg
      → General.lookup-bs sg M ≡ just h
      → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (false , sc , sg) (just h))
    mdInv-good-repeat sc sg i M h str@(uk , rt , rc , ol) eq =
      OnSupport-bind (walk sc IV (toBlocks M) 1)
        (λ w → return-ℚ (repAns i sg false h w))
        (walk-replay sc (toBlocks M) IV 1 h (rc M h eq))
        cont
      where
        cont : ∀ w → (proj₁ w ≡ sc × proj₁ (proj₂ w) ≡ h)
             → OnSupport (λ t → MDInv (proj₁ t))
                 (return-ℚ (repAns i sg false h w))
        cont w (sc≡ , v≡) = OnSupport-return
          (subst (λ fl → MDInv (fl , proj₁ w , sg)) (sym flag≡false)
            (subst (λ tb → MDInv (false , tb , sg)) (sym sc≡) ((λ ()) , (λ _ → str))))
          where
            flag≡false : (not ⌊ proj₁ (proj₂ w) ≟ h ⌋) ∨ false ≡ false
            flag≡false = trans (∨-identityʳ _)
                               (trans (cong (λ z → not ⌊ z ≟ h ⌋) v≡) (cong not (⌊≟⌋-refl h)))

  ------------------------------------------------------------------------
  -- New-message branch: table extension, fresh inserts, walk support and the
  -- final-key tracker
  private
    _⊒_ : Comp.Table → Comp.Table → Type
    sc' ⊒ sc = ∀ key x → Comp.lookup-bs sc key ≡ just x → Comp.lookup-bs sc' key ≡ just x

    ⊒-refl : ∀ sc → sc ⊒ sc
    ⊒-refl sc key x e = e

    ⊒-trans : ∀ a b c → a ⊒ b → b ⊒ c → a ⊒ c
    ⊒-trans a b c ab bc key x e = ab key x (bc key x e)

    present≢fresh : ∀ sc (k₀ : CV × Blk × ℕ × ℕ) key x
                  → Comp.lookup-bs sc key ≡ just x → Comp.lookup-bs sc k₀ ≡ nothing → key ≢ k₀
    present≢fresh sc k₀ key x pres absent refl = nothing≢just (trans (sym absent) pres)

    ⊒-cons-fresh : ∀ (k₀ : CV × Blk × ℕ × ℕ) v₀ sc
                 → Comp.lookup-bs sc k₀ ≡ nothing → ((k₀ , v₀) ∷ sc) ⊒ sc
    ⊒-cons-fresh k₀ v₀ sc absent key x pres =
      trans (Comp.lookup-bs-there sc k₀ v₀ key (present≢fresh sc k₀ key x pres absent)) pres

    runPath-⊒ : ∀ sc' sc → sc' ⊒ sc → ∀ r ls t
              → runPath (stepT sc) r ls ≡ just t → runPath (stepT sc') r ls ≡ just t
    runPath-⊒ sc' sc ext r [] t e = e
    runPath-⊒ sc' sc ext r ((b , j) ∷ ls) t e =
      let (w , hd , tl) = runPath-cons-inv (stepT sc) r (b , j) ls t e
      in trans (runPath-step (stepT sc') r (b , j) w ls (ext (pack r b j) w hd))
               (runPath-⊒ sc' sc ext w ls t tl)

    lookup-nothing⇒All≢ : ∀ sc (k₀ : CV × Blk × ℕ × ℕ) → Comp.lookup-bs sc k₀ ≡ nothing
                        → ListAll.All (λ key → k₀ ≢ key) (L.map proj₁ sc)
    lookup-nothing⇒All≢ []             k₀ absent = ListAll.[]
    lookup-nothing⇒All≢ ((k , v) ∷ sc) k₀ absent with k₀ ≟ k | absent
    ... | yes _ | ab = ⊥-elim (just≢nothing ab)
    ... | no ¬p | ab = ¬p ListAll.∷ lookup-nothing⇒All≢ sc k₀ ab

    UniqueKeys-cons-fresh : ∀ (k₀ : CV × Blk × ℕ × ℕ) v₀ sc
                          → Comp.lookup-bs sc k₀ ≡ nothing → UniqueKeys sc → UniqueKeys ((k₀ , v₀) ∷ sc)
    UniqueKeys-cons-fresh k₀ v₀ sc absent uk = lookup-nothing⇒All≢ sc k₀ absent ∷ uk

    Any-insert : ∀ {A : Type} {P : A → Type} {x z : A} {ys}
               → ListAny.Any P (x ∷ ys) → ListAny.Any P (x ∷ z ∷ ys)
    Any-insert (ListAny.here p)  = ListAny.here p
    Any-insert (ListAny.there a) = ListAny.there (ListAny.there a)

    HasVal-cons-any : ∀ (e : (CV × Blk × ℕ × ℕ) × CV) sc x
                    → HasVal (poolL sc) x → HasVal (poolL (e ∷ sc)) x
    HasVal-cons-any ((hh , bb , len , idx) , vv) sc x hv with idx <? len
    ... | yes _ = Any-insert hv
    ... | no  _ = hv

    new-val-HasVal : ∀ v b idx vv sc → idx < k → HasVal (poolL ((pack v b idx , vv) ∷ sc)) vv
    new-val-HasVal v b idx vv sc lt with idx <? k
    ... | yes _   = ListAny.there (ListAny.here refl)
    ... | no  ¬lt = ⊥-elim (¬lt lt)

    lookup-interior-HasVal : ∀ sc v b idx v'' → idx < k
                           → Comp.lookup-bs sc (pack v b idx) ≡ just v'' → HasVal (poolL sc) v''
    lookup-interior-HasVal ((key , val) ∷ sc) v b idx v'' lt hit with (pack v b idx) ≟ key | hit
    ... | yes p | h = subst (λ K → HasVal (poolL ((K , val) ∷ sc)) v'') p
                        (subst (HasVal (poolL ((pack v b idx , val) ∷ sc))) (just-injective h)
                          (new-val-HasVal v b idx val sc lt))
    ... | no ¬p | h = HasVal-cons-any (key , val) sc v'' (lookup-interior-HasVal sc v b idx v'' lt h)

    Rooted-cons-fresh : ∀ (e : (CV × Blk × ℕ × ℕ) × CV) sc
                      → HasVal (poolL sc) (proj₁ (proj₁ e)) → Rooted sc → Rooted (e ∷ sc)
    Rooted-cons-fresh e sc eroot rt =
      HasVal-cons-any e sc (proj₁ (proj₁ e)) eroot
        ListAll.∷ ListAll.map (λ {ent} hv → HasVal-cons-any e sc (proj₁ (proj₁ ent)) hv) rt

    CBnd : Comp.Table → CV → Blk → ℕ → Comp.Table × (CV × Bool) → Type
    CBnd sc v b idx w = (proj₁ w ⊒ sc) × UniqueKeys (proj₁ w) × Rooted (proj₁ w)
                      × HasVal (poolL (proj₁ w)) (proj₁ (proj₂ w))
                      × (stepT (proj₁ w) v (b , idx) ≡ just (proj₁ (proj₂ w)))

    Bnd : Comp.Table → CV → List Blk → ℕ → Comp.Table × (CV × Bool) → Type
    Bnd sc v bs idx w = (proj₁ w ⊒ sc) × UniqueKeys (proj₁ w) × Rooted (proj₁ w)
                      × (runPath (stepT (proj₁ w)) v (labels bs idx) ≡ just (proj₁ (proj₂ w)))

    callC-supp : ∀ sc v b idx → idx < k → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → OnSupport (CBnd sc v b idx) (callC sc v b idx)
    callC-supp sc v b idx lt uk rt vroot with Comp.lookup-bs sc (pack v b idx) in eq
    ... | just hm = OnSupport-return (⊒-refl sc , uk , rt , lookup-interior-HasVal sc v b idx hm lt eq , eq)
    ... | nothing = OnSupport-map Comp.uniform-Out _
                      (λ hm →
                        ( ⊒-cons-fresh (pack v b idx) hm sc eq
                        , UniqueKeys-cons-fresh (pack v b idx) hm sc eq uk
                        , Rooted-cons-fresh (pack v b idx , hm) sc vroot rt
                        , new-val-HasVal v b idx hm sc lt
                        , Comp.lookup-bs-here sc (pack v b idx) hm ))

    walk-supp  : ∀ sc v bs idx → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → idx + length bs ≡ suc k → OnSupport (Bnd sc v bs idx) (walk sc v bs idx)
    walk-suppL : ∀ sc v b idx (mv : Maybe CV) → UniqueKeys sc → Rooted sc → HasVal (poolL sc) v
               → Comp.lookup-bs sc (pack v b idx) ≡ mv
               → OnSupport (Bnd sc v (b ∷ []) idx) (callC' sc v b idx mv)

    walk-supp sc v []            idx uk rt vroot pr = OnSupport-return (⊒-refl sc , uk , rt , refl)
    walk-supp sc v (b ∷ [])      idx uk rt vroot pr =
      walk-suppL sc v b idx (Comp.lookup-bs sc (pack v b idx)) uk rt vroot refl
    walk-supp sc v (b ∷ bs'@(_ ∷ bs)) idx uk rt vroot pr =
      OnSupport-bind (callC sc v b idx) (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        (callC-supp sc v b idx (proj₁ (interior-step idx (length bs) pr)) uk rt vroot)
        (λ w cb → OnSupport-mono (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)) (mapc w cb)
                    (walk-supp (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx)
                       (proj₁ (proj₂ cb)) (proj₁ (proj₂ (proj₂ cb))) (proj₁ (proj₂ (proj₂ (proj₂ cb)))) pr'))
      where
        pr' = proj₂ (interior-step idx (length bs) pr)
        mapc : ∀ w → CBnd sc v b idx w → ∀ w2 → Bnd (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) w2
             → Bnd sc v (b ∷ bs') idx w2
        mapc w (ext , uk' , rt' , hvroot , stepeq) w2 (ext2 , uk2 , rt2 , seg2) =
          ⊒-trans (proj₁ w2) (proj₁ w) sc ext2 ext , uk2 , rt2
          , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) (proj₁ (proj₂ w))
                    (labels bs' (suc idx)) (ext2 (pack v b idx) (proj₁ (proj₂ w)) stepeq)) seg2

    walk-suppL sc v b idx (just hm) uk rt vroot eq =
      OnSupport-return (⊒-refl sc , uk , rt , runPath-step (stepT sc) v (b , idx) hm [] eq)
    walk-suppL sc v b idx nothing uk rt vroot eq =
      OnSupport-map Comp.uniform-Out _
        (λ hm →
          ( ⊒-cons-fresh (pack v b idx) hm sc eq
          , UniqueKeys-cons-fresh (pack v b idx) hm sc eq uk
          , Rooted-cons-fresh (pack v b idx , hm) sc vroot rt
          , runPath-step (stepT ((pack v b idx , hm) ∷ sc)) v (b , idx) hm [] (Comp.lookup-bs-here sc (pack v b idx) hm) ))

  private
    rec-extend : ∀ sc sg sc' M v' → sc' ⊒ sc → Chain sc' M v'
               → RecChains sc sg → RecChains sc' ((M , v') ∷ sg)
    rec-extend sc sg sc' M v' ext chain rc M₀ h₀ lk with M₀ ≟ M | lk
    ... | yes p | l = subst (λ hh → Chain sc' M₀ hh) (just-injective l)
                        (subst (λ MM → Chain sc' MM v') (sym p) chain)
    ... | no ¬p | l = runPath-⊒ sc' sc ext IV (labels (toBlocks M₀) 1) h₀ (rc M₀ h₀ l)

  private
    final≢interior : ∀ v' b' v b idx → idx < k → (v' , b' , k , k) ≢ pack v b idx
    final≢interior v' b' v b idx lt p =
      ℕP.<-irrefl refl (subst (idx <_) (cong (λ z → proj₂ (proj₂ (proj₂ z))) p) lt)

    FinalCallOf : CV → List Blk → ℕ → Comp.Table → CV → Blk → Type
    FinalCallOf v bs idx sc' v' b' =
      Σ (List Blk) λ pre → (bs ≡ pre ++ (b' ∷ [])) × (runPath (stepT sc') v (labels pre idx) ≡ just v')

    FKout : Comp.Table → CV → List Blk → ℕ → Comp.Table × (CV × Bool) → Type
    FKout sc v bs idx w = (proj₁ w ⊒ sc)
      × (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u'
           → (stepT sc v' (b' , k) ≡ just u')
           ⊎ (FinalCallOf v bs idx (proj₁ w) v' b' × (proj₂ (proj₂ w) ≡ false)))

    FKstep : Comp.Table → CV → Blk → ℕ → Comp.Table × (CV × Bool) → Type
    FKstep sc v b idx w = (proj₁ w ⊒ sc) × (stepT (proj₁ w) v (b , idx) ≡ just (proj₁ (proj₂ w)))
      × (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u' → stepT sc v' (b' , k) ≡ just u')

    callC-fk : ∀ sc v b idx → idx < k → OnSupport (FKstep sc v b idx) (callC sc v b idx)
    callC-fk sc v b idx lt with Comp.lookup-bs sc (pack v b idx) in eq
    ... | just hm = OnSupport-return (⊒-refl sc , eq , λ _ _ _ x → x)
    ... | nothing = OnSupport-map Comp.uniform-Out _
                      (λ hm →
                        ( ⊒-cons-fresh (pack v b idx) hm sc eq
                        , Comp.lookup-bs-here sc (pack v b idx) hm
                        , (λ v' b' u' x → trans (sym (Comp.lookup-bs-there sc (pack v b idx) hm (v' , b' , k , k)
                                                   (final≢interior v' b' v b idx lt))) x) ))

    walk-fk  : ∀ sc v bs idx → idx + length bs ≡ suc k
             → OnSupport (FKout sc v bs idx) (walk sc v bs idx)
    walk-fkL : ∀ sc v b idx (mv : Maybe CV) → Comp.lookup-bs sc (pack v b idx) ≡ mv
             → OnSupport (FKout sc v (b ∷ []) idx) (callC' sc v b idx mv)

    walk-fk sc v []            idx pr = OnSupport-return (⊒-refl sc , λ v' b' u' e → inj₁ e)
    walk-fk sc v (b ∷ [])      idx pr =
      walk-fkL sc v b idx (Comp.lookup-bs sc (pack v b idx)) refl
    walk-fk sc v (b ∷ bs'@(_ ∷ bs)) idx pr =
      OnSupport-bind (callC sc v b idx) (λ w → walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
        (callC-fk sc v b idx (proj₁ (interior-step idx (length bs) pr)))
        (λ w cb → OnSupport-mono (walk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx))
                    (mapc w cb) (walk-fk (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) pr'))
      where
        pr' = proj₂ (interior-step idx (length bs) pr)
        mapc : ∀ w → FKstep sc v b idx w
             → ∀ w2 → FKout (proj₁ w) (proj₁ (proj₂ w)) bs' (suc idx) w2
             → FKout sc v (b ∷ bs') idx w2
        mapc w (exth , steph , finalrev) w2 (ext2 , dich2) =
          ⊒-trans (proj₁ w2) (proj₁ w) sc ext2 exth , dd
          where
            dd : ∀ v' b' u' → stepT (proj₁ w2) v' (b' , k) ≡ just u'
               → (stepT sc v' (b' , k) ≡ just u')
               ⊎ (FinalCallOf v (b ∷ bs') idx (proj₁ w2) v' b' × (proj₂ (proj₂ w2) ≡ false))
            dd v' b' u' e = case dich2 v' b' u' e of λ where
              (inj₁ x) → inj₁ (finalrev v' b' u' x)
              (inj₂ ((pre' , beq , req) , bf)) → inj₂ (((b ∷ pre') , cong (b ∷_) beq
                                                 , trans (runPath-step (stepT (proj₁ w2)) v (b , idx) (proj₁ (proj₂ w)) (labels pre' (suc idx))
                                                           (ext2 (pack v b idx) (proj₁ (proj₂ w)) steph)) req) , bf)

    walk-fkL sc v b idx (just hm) eq = OnSupport-return (⊒-refl sc , λ v' b' u' e → inj₁ e)
    walk-fkL sc v b idx nothing eq =
      OnSupport-map Comp.uniform-Out _
        (λ hm → (⊒-cons-fresh (pack v b idx) hm sc eq , dich hm))
      where
        dich : ∀ hm → ∀ v' b' u' → stepT ((pack v b idx , hm) ∷ sc) v' (b' , k) ≡ just u'
             → (stepT sc v' (b' , k) ≡ just u')
             ⊎ (FinalCallOf v (b ∷ []) idx ((pack v b idx , hm) ∷ sc) v' b' × (false ≡ false))
        dich hm v' b' u' e with (v' , b' , k , k) ≟ pack v b idx | e
        ... | yes p | e' = inj₂ (([] , cong (_∷ []) (sym (cong (λ z → proj₁ (proj₂ z)) p))
                                 , cong just (sym (cong proj₁ p))) , refl)
        ... | no ¬p | e' = inj₁ e'

  ------------------------------------------------------------------------
  -- Birthday descent: collC ≡ 0 ⇒ interior co-determinism
  private
    cm0-all : ∀ L h → Comp.count-matches L h ≡ 0ℚ → ListAll.All (λ e → h ≢ proj₂ e) L
    cm0-all []             h _   = ListAll.[]
    cm0-all ((key , v) ∷ xs) h eq0 with h ≟ v | eq0
    ... | yes _ | eq0' = ⊥-elim (1≢0 (≤-antisym (≤-trans (p≤p+q 1ℚ (cm-nn xs h)) (≤-reflexive eq0')) 0≤1ℚ))
    ... | no ¬p | eq0' = ¬p ListAll.∷ cm0-all xs h (trans (sym (+-identityˡ (Comp.count-matches xs h))) eq0')

    sc0-ap : ∀ L → Comp.state-collisions L ≡ 0ℚ → AllPairs (λ e e' → proj₂ e ≢ proj₂ e') L
    sc0-ap []             _   = []
    sc0-ap ((key , h) ∷ ps) eq0 =
      let s = nonNeg+nonNeg≡0 (Comp.count-matches ps h) (Comp.state-collisions ps) (cm-nn ps h) (sc-nn ps) eq0
      in cm0-all ps h (proj₁ s) ∷ sc0-ap ps (proj₂ s)

    lookup⇒mem : ∀ sc key w → Comp.lookup-bs sc key ≡ just w → ListAny.Any (_≡ (key , w)) sc
    lookup⇒mem ((k' , v') ∷ xs) key w e with key ≟ k' | e
    ... | yes p | e' = ListAny.here (cong₂ _,_ (sym p) (just-injective e'))
    ... | no ¬p | e' = ListAny.there (lookup⇒mem xs key w e')

    ∈interior : ∀ sc v b j w → j < k → ListAny.Any (_≡ ((v , b , k , j) , w)) sc
              → ListAny.Any (_≡ ((v , b , k , j) , w)) (interior sc)
    ∈interior (_ ∷ es) v b j w lt (ListAny.here refl) with j <? k
    ... | yes _   = ListAny.here refl
    ... | no ¬lt = ⊥-elim (¬lt lt)
    ∈interior (((cv' , b' , len' , idx') , val') ∷ es) v b j w lt (ListAny.there a) with idx' <? len'
    ... | yes _ = ListAny.there (∈interior es v b j w lt a)
    ... | no  _ = ∈interior es v b j w lt a

    lookupAll : ∀ {A : Type} {R : A → Type} {y xs} → ListAll.All R xs → ListAny.Any (_≡ y) xs → R y
    lookupAll {R = R} (px ListAll.∷ _)  (ListAny.here e) = subst R e px
    lookupAll         (_  ListAll.∷ ps) (ListAny.there a) = lookupAll ps a

    allpairs-mem : ∀ {A : Type} {R : A → A → Type} {xs} → AllPairs R xs
                 → ∀ {x y} → ListAny.Any (_≡ x) xs → ListAny.Any (_≡ y) xs → (x ≡ y) ⊎ (R x y ⊎ R y x)
    allpairs-mem (_  ∷ _)   (ListAny.here refl) (ListAny.here refl) = inj₁ refl
    allpairs-mem (px ∷ _)   (ListAny.here refl) (ListAny.there qy)  = inj₂ (inj₁ (lookupAll px qy))
    allpairs-mem (px ∷ _)   (ListAny.there qx)  (ListAny.here refl) = inj₂ (inj₂ (lookupAll px qx))
    allpairs-mem (_  ∷ aps) (ListAny.there qx)  (ListAny.there qy)  = allpairs-mem aps qx qy

    codet : ∀ sc' → collC sc' ≡ 0ℚ → ∀ v₁ b₁ j₁ v₂ b₂ j₂ w → j₁ < k → j₂ < k
          → Comp.lookup-bs sc' (v₁ , b₁ , k , j₁) ≡ just w
          → Comp.lookup-bs sc' (v₂ , b₂ , k , j₂) ≡ just w
          → (v₁ , b₁ , k , j₁) ≡ (v₂ , b₂ , k , j₂)
    codet sc' c0 v₁ b₁ j₁ v₂ b₂ j₂ w lt₁ lt₂ e₁ e₂ =
      go (allpairs-mem (sc0-ap (poolL sc') c0)
           (ListAny.there (∈interior sc' v₁ b₁ j₁ w lt₁ (lookup⇒mem sc' (v₁ , b₁ , k , j₁) w e₁)))
           (ListAny.there (∈interior sc' v₂ b₂ j₂ w lt₂ (lookup⇒mem sc' (v₂ , b₂ , k , j₂) w e₂))))
      where
        go : (((v₁ , b₁ , k , j₁) , w) ≡ ((v₂ , b₂ , k , j₂) , w))
           ⊎ ((w ≢ w) ⊎ (w ≢ w)) → (v₁ , b₁ , k , j₁) ≡ (v₂ , b₂ , k , j₂)
        go (inj₁ eq)        = cong proj₁ eq
        go (inj₂ (inj₁ r)) = ⊥-elim (r refl)
        go (inj₂ (inj₂ r)) = ⊥-elim (r refl)

  private
    cm-01 : ∀ L h → (Comp.count-matches L h ≡ 0ℚ) ⊎ (1ℚ ≤ℚ Comp.count-matches L h)
    cm-01 []             h = inj₁ refl
    cm-01 ((_ , v) ∷ xs) h with h ≟ v | cm-01 xs h
    ... | yes _ | _         = inj₂ (p≤p+q 1ℚ (cm-nn xs h))
    ... | no  _ | inj₂ c≥1 = inj₂ (subst (1ℚ ≤ℚ_) (sym (+-identityˡ _)) c≥1)
    ... | no  _ | inj₁ c0  = inj₁ (trans (+-identityˡ _) c0)

    collC-01 : ∀ L → (Comp.state-collisions L ≡ 0ℚ) ⊎ (1ℚ ≤ℚ Comp.state-collisions L)
    collC-01 []             = inj₁ refl
    collC-01 ((_ , h) ∷ ps) with cm-01 ps h | collC-01 ps
    ... | inj₂ cm≥1 | _         = inj₂ (≤-trans cm≥1 (p≤p+q _ (sc-nn ps)))
    ... | inj₁ _    | inj₂ sc≥1 = inj₂ (≤-trans sc≥1 (p≤q+p _ (cm-nn ps h)))
    ... | inj₁ cm0  | inj₁ sc0  = inj₁ (trans (cong₂ _+ℚ_ cm0 sc0) (+-identityˡ 0ℚ))

    snoc-view : ∀ (xs : List Blk) → 0 < length xs
              → Σ (List Blk) λ ys → Σ Blk λ y → xs ≡ ys ++ (y ∷ [])
    snoc-view (x ∷ [])        _ = [] , x , refl
    snoc-view (x ∷ x' ∷ xs')  _ =
      let s = snoc-view (x' ∷ xs') ℕP.0<1+n
      in x ∷ proj₁ s , proj₁ (proj₂ s) , cong (x ∷_) (proj₂ (proj₂ s))

    labels-++ : ∀ bs b j → labels (bs ++ (b ∷ [])) j ≡ labels bs j ++ ((b , j + length bs) ∷ [])
    labels-++ []       b j = cong (λ z → (b , z) ∷ []) (sym (ℕP.+-identityʳ j))
    labels-++ (x ∷ bs) b j = cong ((x , j) ∷_)
      (trans (labels-++ bs b (suc j))
             (cong (λ z → labels bs (suc j) ++ ((b , z) ∷ [])) (sym (ℕP.+-suc j (length bs)))))

    labels-inj : ∀ bs bs' j → labels bs j ≡ labels bs' j → bs ≡ bs'
    labels-inj []       []         j _  = refl
    labels-inj []       (b' ∷ bs') j ()
    labels-inj (b ∷ bs) []         j ()
    labels-inj (b ∷ bs) (b' ∷ bs') j eq =
      cong₂ _∷_ (cong proj₁ (proj₁ (∷-injective eq))) (labels-inj bs bs' (suc j) (proj₂ (∷-injective eq)))

    stepT<k : Comp.Table → CV → Blk × ℕ → Maybe CV
    stepT<k sc v (b , j) = case j <? k of λ where
      (yes _) → Comp.lookup-bs sc (v , b , k , j)
      (no  _) → nothing

    runPath-≡<k : ∀ sc r bs j → j + length bs ≤ k
                → runPath (stepT<k sc) r (labels bs j) ≡ runPath (stepT sc) r (labels bs j)
    runPath-≡<k sc r []       j le = refl
    runPath-≡<k sc r (b ∷ bs) j le with j <? k
    ... | no ¬lt = ⊥-elim (¬lt (ℕP.<-≤-trans (ℕP.m<m+n j ℕP.0<1+n) le))
    ... | yes _ with Comp.lookup-bs sc (r , b , k , j)
    ...   | nothing = refl
    ...   | just w  = runPath-≡<k sc w bs (suc j) (subst (_≤ k) (ℕP.+-suc j (length bs)) le)

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

    snoc-len : ∀ (M0 : Vec Bool (k * n)) pre b → toBlocks M0 ≡ pre ++ (b ∷ []) → 1 + length pre ≡ k
    snoc-len M0 pre b dec =
      trans (sym (ℕP.+-comm (length pre) 1))
      (trans (sym (length-++ pre))
      (trans (sym (cong length dec)) (toBlocks-length M0)))

    stepT<k-inv : ∀ sc v b j w → stepT<k sc v (b , j) ≡ just w
                → (j < k) × (Comp.lookup-bs sc (v , b , k , j) ≡ just w)
    stepT<k-inv sc v b j w e with j <? k | e
    ... | yes lt | e' = lt , e'
    ... | no  _  | ()

    codet<k : ∀ sc' → collC sc' ≡ 0ℚ
            → ∀ {a l a' l' w} → stepT<k sc' a l ≡ just w → stepT<k sc' a' l' ≡ just w → (a , l) ≡ (a' , l')
    codet<k sc' c0 {a} {b1 , j1} {a'} {b1' , j1'} {w} e1 e2 =
      let i1 = stepT<k-inv sc' a  b1  j1  w e1
          i2 = stepT<k-inv sc' a' b1' j1' w e2
          keq = codet sc' c0 a b1 j1 a' b1' j1' w (proj₁ i1) (proj₁ i2) (proj₂ i1) (proj₂ i2)
      in cong₂ _,_ (cong (λ z → proj₁ z) keq)
                   (cong₂ _,_ (cong (λ z → proj₁ (proj₂ z)) keq) (cong (λ z → proj₂ (proj₂ (proj₂ z))) keq))

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
          0<len = subst (0 <_) (sym (toBlocks-length M)) (ℕP.n≢0⇒n>0 (≢-nonZero⁻¹ k))
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

  walk-owned : ∀ sc sg M (w : Comp.Table × (CV × Bool))
             → General.lookup-bs sg M ≡ nothing
             → (proj₁ w ⊒ sc)
             → (∀ v' b' u' → stepT (proj₁ w) v' (b' , k) ≡ just u'
                  → (stepT sc v' (b' , k) ≡ just u') ⊎ FinalCallOf IV (toBlocks M) 1 (proj₁ w) v' b')
             → RecChains sc sg → OwnedLast sc sg
             → OwnedLast (proj₁ w) ((M , proj₁ (proj₂ w)) ∷ sg)
  walk-owned sc sg M w eq ext dich rc ol v' b w'' e with dich v' b w'' e
  ... | inj₂ (pre , blkeq , run') =
        M , proj₁ (proj₂ w) , General.lookup-bs-here sg M (proj₁ (proj₂ w)) , pre , blkeq , run'
  ... | inj₁ old with ol v' b w'' old
  ...   | (M' , h' , lk' , pre , blkeq , run') =
          M' , h'
          , trans (General.lookup-bs-there sg M (proj₁ (proj₂ w)) M' M'≢M) lk'
          , pre , blkeq , runPath-⊒ (proj₁ w) sc ext IV (labels pre 1) v' run'
        where
          M'≢M : M' ≢ M
          M'≢M p = nothing≢just (trans (sym eq)
                     (subst (λ z → General.lookup-bs sg z ≡ just h') p lk'))

  mdInv-good-new : ∀ sc sg i M
    → UniqueKeys sc × Rooted sc × RecChains sc sg × OwnedLast sc sg
    → General.lookup-bs sg M ≡ nothing
    → OnSupport (λ t → MDInv (proj₁ t)) (respB' i M (false , sc , sg) nothing)
  mdInv-good-new sc sg i M (uk , rt , rc , ol) eq =
    OnSupport-bind (walk sc IV (toBlocks M) 1)
      (λ w → newAns i M sg (proj₂ (proj₂ w) ∨ false) (proj₁ w) (proj₁ (proj₂ w)))
      (OnSupport-∧ (walk sc IV (toBlocks M) 1)
        (walk-supp sc IV (toBlocks M) 1 uk rt (ListAny.here refl) (cong suc (toBlocks-length M)))
        (walk-fk sc IV (toBlocks M) 1 (cong suc (toBlocks-length M))))
      cont
    where
      cont : ∀ w → Bnd sc IV (toBlocks M) 1 w × FKout sc IV (toBlocks M) 1 w
           → OnSupport (λ t → MDInv (proj₁ t))
               (newAns i M sg (proj₂ (proj₂ w) ∨ false) (proj₁ w) (proj₁ (proj₂ w)))
      cont w ((ext , uk' , rt' , seg) , (_ , dich)) with proj₂ (proj₂ w)
      ... | true  = OnSupport-map Comp.uniform-Out _
                      (λ u →
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
          dich-owned v' b' u' e = case dich v' b' u' e of λ where
            (inj₁ old) → inj₁ old
            (inj₂ (fc , _)) → inj₂ fc

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

  mdInv-pres : Preserved MDInv C.realK
  mdInv-pres (f , sc , sg) (i , M) inv with f
  ... | true  = OnSupport-Dmap C.fR (respB (true , sc , sg) (i , M))
                  (flagged-step sc sg i M (proj₁ inv refl))
  ... | false = mdInv-pres-good sc sg i M (proj₂ inv refl)

  mdInv : MDInvData
  mdInv = record
    { Inv = MDInv ; inv₀ = MDInv₀ ; pres = mdInv-pres
    ; flag⇒coll = λ s inv eq → proj₁ inv eq }

  md-cert : SuperCert C.realK proj₁ (false , [] , []) bound
  md-cert = record
    { Inv    = MDInvData.Inv mdInv
    ; φ      = φMD
    ; inv₀   = MDInvData.inv₀ mdInv
    ; pres   = MDInvData.pres mdInv
    ; φ-nn   = λ m s _ → φ-nn m s
    ; φ-bad  = λ m s inv eq → ≤-trans (MDInvData.flag⇒coll mdInv s inv eq)
                                      (p≤p+q (collC (proj₁ (proj₂ s)))
                                             (0≤Γ (pool (proj₁ (proj₂ s))) (m * (k ∸ 1))))
    ; φ-step = λ m s q _ → φ-step m s q
    ; φ-init = φ-init
    }

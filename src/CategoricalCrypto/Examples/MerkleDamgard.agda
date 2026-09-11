{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- MERKLE–DAMGÅRD as a protocol, and its concrete-security theorem: SINGLE-
-- ORACLE indistinguishability with the compression function HIDDEN.  The
-- distinguisher is a `Strat (Neg Generalᴵ) (Pos Generalᴵ)` — `Sys = md ∘ᵖ comp`
-- closes `comp` off, so there is no compression-oracle interface — and there is
-- no simulator anywhere.  That is strictly weaker than indifferentiability,
-- i.e. than "MD is a random oracle".
--
--     comp    : Protocol unitᴵ Compᴵ       -- the compression random oracle
--     md      : Protocol Compᴵ Generalᴵ    -- one compression call per block
--     Sys     = md ∘ᵖ comp                 -- the real world
--     general : Protocol unitᴵ Generalᴵ    -- the ideal, variable-length oracle
--
-- `md`'s step is a `Calls` tree with one `call` per block (`chainᶜ`), so the
-- chaining is structural recursion on the block list and `_∘ᵖ_` grafts the two
-- trees: the machine formulation's `_∘ᵍ_` trace, its `Nfuel`/`stableN`
-- saturation and the loop-replay induction all disappear.  What is left is
-- `graft-chain` — one activation of the composite IS the crypto core's
-- `mdRun` — and it is an induction on the block list.
--
-- The cryptography is `Examples.MerkleDamgard.Core`, machine-free and
-- unchanged: the coupling, the Fundamental Lemma of Game-Playing,
-- `ideal-marginal`, `ghost-erase`, the birthday certificate `md-cert` and the
-- adaptive bound `bad-bound`.  All this module adds is the seam between layer
-- 1's `Protocol.Observe.run` and the core's `Interaction.runWith`.
--
-- Warm single-module typecheck: ~7 s (measured 2026-09-10, `+RTS -M8G -H1G`).
--------------------------------------------------------------------------------

open import Data.Bool.Base using (Bool; false)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc; NonZero)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using () renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-trans)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; subst)
import Relation.Binary.Reasoning.Setoid as RS

open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)
open import ProbabilisticLogic.Prelude

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction hiding (run)   -- `run` is `Observe`'s
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Examples.MerkleDamgard.Core as Core

module CategoricalCrypto.Examples.MerkleDamgard where

------------------------------------------------------------------------
-- The seam between the two layers

-- A closed protocol's per-activation distribution, as an interaction-model
-- kernel: `Protocol.Observe.runFrom` IS `Interaction.runWith⊥` at it.
protoK : {B : Iface} (P : Protocol unitᴵ B) → St P → Neg B → Dist⊥ (St P × Pos B)
protoK P s q = evalC (step P s q)

-- The two `run`s agree clause by clause; only `d` being a variable keeps them
-- from being the same term.
runFrom-as-runWith : {B : Iface} (P : Protocol unitᴵ B) (s : St P) (d : Strat (Neg B) (Pos B))
                   → runFrom P s d ≈Mℚ runWith⊥ (protoK P) s d
runFrom-as-runWith P s (out b)    = λ _ → refl
runFrom-as-runWith P s (ask q c)  =
  >>=⊥-congˡ (protoK P s q)
    (λ o → runFrom P (proj₁ o) (c (proj₂ o)))
    (λ o → runWith⊥ (protoK P) (proj₁ o) (c (proj₂ o)))
    (λ o → runFrom-as-runWith P (proj₁ o) (c (proj₂ o)))
runFrom-as-runWith P s (coin μ c) =
  >>=ᴹ-congˡ μ (λ b → runFrom P s (c b)) (λ b → runWith⊥ (protoK P) s (c b))
    (λ b → runFrom-as-runWith P s (c b))

-- So a protocol whose activations are an embedded TOTAL kernel — no `dead`
-- anywhere, and possibly some state the kernel does not carry — runs like that
-- kernel at every strategy.  This is what lets a theorem proved in the
-- `Dist-ℚ` reactive model be read off layer 1's `run`.
runFrom-kernel : {B : Iface} {S : Set} (P : Protocol unitᴵ B)
                 (resp : S → Neg B → Dist-ℚ (S × Pos B)) (emb : S → St P)
               → (∀ s q → protoK P (emb s) q
                          ≈Mℚ (resp s q >>=ᴹ λ o → return⊥ (emb (proj₁ o) , proj₂ o)))
               → ∀ s d → runFrom P (emb s) d ≈Mℚ Dmap just (runWith resp s d)
runFrom-kernel P resp emb ker s d = Mℚ.trans
  {i = runFrom P (emb s) d} {j = runWith⊥ (protoK P) (emb s) d}
  {k = Dmap just (runWith resp s d)}
  (runFrom-as-runWith P (emb s) d) (runWith⊥-emb resp (protoK P) emb ker s d)

------------------------------------------------------------------------
-- The three protocols

module MD (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

  open Core.MD n k IV public

  Compᴵ Generalᴵ : Iface
  Compᴵ    = Comp.Output    ⇿ Comp.Input
  Generalᴵ = General.Output ⇿ General.Input

  -- A lazily sampled oracle as a call tree: repeat from the table, or draw the
  -- `n` output bits one fair coin at a time.  The lookup result is an
  -- ARGUMENT, so that the semantics lemma below can case on it without having
  -- to reach the scrutinee through the record projection (the device
  -- `Core.callC'` uses).
  compStep : Comp.Table → Comp.Input → Maybe CV → Calls unitᴵ (Comp.Table × Comp.Output)
  compStep sc (i , _) (just h) = ret (sc , (i , h))
  compStep sc (i , q) nothing  = uniformVec n λ h → ret ((q , h) ∷ sc , (i , h))

  comp : Protocol unitᴵ Compᴵ
  comp = record { St = Comp.Table ; init = [] ;
                  step = λ sc q → compStep sc q (Comp.lookup-bs sc (proj₂ q)) }

  generalStep : General.Table → General.Input → Maybe CV
              → Calls unitᴵ (General.Table × General.Output)
  generalStep sg (i , _) (just h) = ret (sg , (i , h))
  generalStep sg (i , M) nothing  = uniformVec n λ h → ret ((M , h) ∷ sg , (i , h))

  general : Protocol unitᴵ Generalᴵ
  general = record { St = General.Table ; init = [] ;
                     step = λ sg q → generalStep sg q (General.lookup-bs sg (proj₂ q)) }

  -- Merkle–Damgård itself: one compression call per block, threading the
  -- chaining value.  `p = 1`, so the party a compression query carries is `i₀`
  -- (`Core.mdRun` hardcodes it too).
  chainᶜ : CV → List Blk → ℕ → Calls Compᴵ CV
  chainᶜ h []       idx = ret h
  chainᶜ h (b ∷ bs) idx = call (i₀ , pack h b idx) λ o → chainᶜ (proj₂ o) bs (suc idx)

  -- Between activations MD holds nothing: a whole message is hashed in one
  -- activation, `k` calls deep.
  md : Protocol Compᴵ Generalᴵ
  md = record { St = ⊤ ; init = tt ;
                step = λ _ (i , M) → chainᶜ IV (toBlocks M) 1 >>=ᶜ λ h → ret (tt , (i , h)) }

  Sys : Protocol unitᴵ Generalᴵ
  Sys = md ∘ᵖ comp

  ------------------------------------------------------------------------
  -- One activation is the crypto core's kernel

  private
    Go : (Comp.Output → Calls Compᴵ (⊤ × General.Output))
       → Comp.Table × Comp.Output → Dist⊥ ((⊤ × Comp.Table) × General.Output)
    Go κ o = evalC (graft md comp (κ (proj₂ o)) (proj₁ o))

    Kret : Fin p → Comp.Table × CV → Dist⊥ ((⊤ × Comp.Table) × General.Output)
    Kret i o = return⊥ ((tt , proj₁ o) , (i , proj₂ o))

    -- One compression call of the composite, whichever branch the oracle
    -- takes.  The `with` reaches the scrutinee inside `Comp.step` because the
    -- statement names it (`Core.callC-marg` casts the same spell).
    compStep-eval : ∀ κ sc i q
                  → evalC (serve md comp κ (compStep sc (i , q) (Comp.lookup-bs sc q)))
                    ≈Mℚ (Comp.step (sc , i , q) >>=ᴹ Go κ)
    compStep-eval κ sc i q with Comp.lookup-bs sc q
    ... | just hm = Mℚ.sym {x = return-ℚ (sc , i , hm) >>=ᴹ Go κ} {y = Go κ (sc , i , hm)}
                      (>>=ᴹ-identityˡ (sc , i , hm) (Go κ))
    ... | nothing = begin
      evalC (serve md comp κ (uniformVec n F))
        ≈⟨ uniformVec-bind (λ t → evalC (serve md comp κ t)) (λ _ _ _ → refl) n F ⟩
      (Comp.uniform-Out >>=ᴹ λ hm → evalC (serve md comp κ (F hm)))
        ≈˘⟨ >>=ᴹ-congˡ Comp.uniform-Out (λ hm → Rt hm >>=ᴹ Go κ)
                       (λ hm → evalC (serve md comp κ (F hm)))
              (λ hm → >>=ᴹ-identityˡ ((q , hm) ∷ sc , i , hm) (Go κ)) ⟩
      (Comp.uniform-Out >>=ᴹ λ hm → (Rt hm >>=ᴹ Go κ))
        ≈˘⟨ >>=ᴹ-assoc Comp.uniform-Out Rt (Go κ) ⟩
      ((Comp.uniform-Out >>=ᴹ Rt) >>=ᴹ Go κ)
        ∎
      where
        F  = λ hm → ret ((q , hm) ∷ sc , (i , hm))
        Rt = λ hm → return-ℚ ((q , hm) ∷ sc , i , hm)
        open RS (Mℚ-setoid _)

    -- THE computation: grafting `md`'s chain onto `comp` replays `Core.mdRun`.
    graft-chain : ∀ i sc h bs idx
                → evalC (graft md comp (chainᶜ h bs idx >>=ᶜ λ v → ret (tt , (i , v))) sc)
                  ≈Mℚ (mdRun sc h bs idx >>=ᴹ Kret i)
    graft-chain i sc h []       idx =
      Mℚ.sym {x = return-ℚ (sc , h) >>=ᴹ Kret i} {y = Kret i (sc , h)}
        (>>=ᴹ-identityˡ (sc , h) (Kret i))
    graft-chain i sc h (b ∷ bs) idx = begin
      evalC (serve md comp κ (compStep sc (i₀ , pack h b idx) (Comp.lookup-bs sc (pack h b idx))))
        ≈⟨ compStep-eval κ sc i₀ (pack h b idx) ⟩
      (Comp.step (sc , i₀ , pack h b idx) >>=ᴹ Go κ)
        ≈⟨ >>=ᴹ-congˡ (Comp.step (sc , i₀ , pack h b idx)) (Go κ) (λ o → MR o >>=ᴹ Kret i)
             (λ o → graft-chain i (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)) ⟩
      (Comp.step (sc , i₀ , pack h b idx) >>=ᴹ λ o → (MR o >>=ᴹ Kret i))
        ≈˘⟨ >>=ᴹ-assoc (Comp.step (sc , i₀ , pack h b idx)) MR (Kret i) ⟩
      (mdRun sc h (b ∷ bs) idx >>=ᴹ Kret i)
        ∎
      where
        κ  = λ o → chainᶜ (proj₂ o) bs (suc idx) >>=ᶜ λ v → ret (tt , (i , v))
        MR = λ (o : Comp.Table × Comp.Output) → mdRun (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)
        open RS (Mℚ-setoid _)

    sysStep : ∀ sc q → protoK Sys (tt , sc) q
                       ≈Mℚ (respR sc q >>=ᴹ λ o → return⊥ ((tt , proj₁ o) , proj₂ o))
    sysStep sc (i , M) = begin
      protoK Sys (tt , sc) (i , M)
        ≈⟨ graft-chain i sc IV (toBlocks M) 1 ⟩
      (mdRun sc IV (toBlocks M) 1 >>=ᴹ Kret i)
        ≈˘⟨ >>=ᴹ-congˡ (mdRun sc IV (toBlocks M) 1) (λ sh → Rw sh >>=ᴹ KE) (Kret i)
              (λ sh → >>=ᴹ-identityˡ (proj₁ sh , (i , proj₂ sh)) KE) ⟩
      (mdRun sc IV (toBlocks M) 1 >>=ᴹ λ sh → (Rw sh >>=ᴹ KE))
        ≈˘⟨ >>=ᴹ-assoc (mdRun sc IV (toBlocks M) 1) Rw KE ⟩
      (respR sc (i , M) >>=ᴹ KE)
        ∎
      where
        Rw = λ (sh : Comp.Table × CV) → return-ℚ (proj₁ sh , (i , proj₂ sh))
        KE = λ (o : Comp.Table × General.Output) → return⊥ ((tt , proj₁ o) , proj₂ o)
        open RS (Mℚ-setoid _)

    generalStep-eval : ∀ sg q → protoK general sg q
                                ≈Mℚ (respG sg q >>=ᴹ λ o → return⊥ (proj₁ o , proj₂ o))
    generalStep-eval sg (i , M) with General.lookup-bs sg M
    ... | just h  = Mℚ.sym {x = return-ℚ (sg , i , h) >>=ᴹ KE} {y = return⊥ (sg , (i , h))}
                      (>>=ᴹ-identityˡ (sg , i , h) KE)
      where KE = λ (o : General.Table × General.Output) → return⊥ (proj₁ o , proj₂ o)
    ... | nothing = begin
      evalC (uniformVec n F)
        ≈⟨ uniformVec-bind evalC (λ _ _ _ → refl) n F ⟩
      (General.uniform-Out >>=ᴹ λ h → evalC (F h))
        ≈˘⟨ >>=ᴹ-congˡ General.uniform-Out (λ h → Rt h >>=ᴹ KE) (λ h → evalC (F h))
              (λ h → >>=ᴹ-identityˡ ((M , h) ∷ sg , i , h) KE) ⟩
      (General.uniform-Out >>=ᴹ λ h → (Rt h >>=ᴹ KE))
        ≈˘⟨ >>=ᴹ-assoc General.uniform-Out Rt KE ⟩
      ((General.uniform-Out >>=ᴹ Rt) >>=ᴹ KE)
        ∎
      where
        F  = λ h → ret ((M , h) ∷ sg , (i , h))
        Rt = λ h → return-ℚ ((M , h) ∷ sg , i , h)
        KE = λ (o : General.Table × General.Output) → return⊥ (proj₁ o , proj₂ o)
        open RS (Mℚ-setoid _)

  -- The two runs, read at the core's kernels.
  run-general : ∀ d → run general d ≈Mℚ Dmap just (runWith respG [] d)
  run-general = runFrom-kernel general respG (λ sg → sg) generalStep-eval []

  run-Sys : ∀ d → run Sys d ≈Mℚ Dmap just (runWith respR [] d)
  run-Sys = runFrom-kernel Sys respR (tt ,_) sysStep []

  ------------------------------------------------------------------------
  -- The theorem

  -- The advantage of ANY adaptive `q`-query strategy at EITHER verdict is at
  -- most `bound q`: neither run diverges, so the `false` reading is the
  -- complement of the `true` one and `advᵇ⊥-just` collapses them.  The
  -- strategy queries `Generalᴵ` only — `f` is hidden — and no simulator
  -- appears; see the header for what that does and does not say.
  indistinguishable : general ≈adv[ bound ] Sys
  indistinguishable b q d le =
    subst (_≤ℚ bound q) (sym advEq)
          (≤-trans (C.FLGP (false , [] , []) d) (bad-bound q d le))
    where
      advEq : advᵇ⊥ b (run general d) (run Sys d)
            ≡ ∣ Pr₁ (runWith C.idealK (false , [] , []) d)
                -ℚ Pr₁ (runWith C.realK (false , [] , []) d) ∣ℚ
      advEq =
        trans (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                (run-general d (maybeℚ (indᵇ b))) (run-Sys d (maybeℚ (indᵇ b))))
       (trans (advᵇ⊥-just b (runWith respG [] d) (runWith respR [] d))
              (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                (ideal-marginal d) (sym (ghost-erase false [] [] d))))


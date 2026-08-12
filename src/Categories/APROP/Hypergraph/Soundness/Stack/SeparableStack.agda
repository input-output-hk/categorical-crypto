{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Term-free structural invariants of the decoder's stack search, both frames
-- (postulate-free, `--safe`).  Two sections:
--
--   §1 (`:37`)  RIGHT frame — firing stays inside the prefix: on `xs ++ R`
--               the search that succeeds within `xs` succeeds identically,
--               and the one that fails on `xs` fails identically
--               (`extract-elem-++ˡ`, `extract-prefix-++ˡ`,
--               `prefix-++ˡ-perm`, and their two `nothing`-mirrors).
--               Consumed by `Strict/Decode/Decoder.agda`'s `stack-sepˢ`.
--   §2 (`:161`) LEFT frame — the `++ʳ` family (`extract-elem-++ʳ`,
--               `extract-prefix-++ʳ-nothing`): a frame block `L` disjoint from
--               the searched list passes through whole onto the residual.
--               Consumed by `Decode/DecodeProperties.agda`.
--
-- §2 carries the OBSTRUCTION note (`:174`) explaining why these STACK lemmas
-- are the strongest left-hand statement available — the TERM-level left-frame
-- mirror of `Decoder.term-sepᵛ` is FALSE for a block that fires, because the
-- residual comes out as `eout e ++ (L ++ rest)` where the framed form needs
-- `L ++ (eout e ++ rest)`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Stack.SeparableStack
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)

open import Categories.Hypergraph.ExtractPrefix using (extract-elem)

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- ## Structural invariant: firing stays inside the prefix.
--
-- `extract-elem`/`extract-prefix` walk the stack left-to-right and stop at the
-- FIRST occurrence.  Hence on `xs ++ R`, if the element/prefix is found within
-- `xs`, the suffix `R` is never inspected and is simply carried onto the
-- residual.  These two lemmas pin that: the residual on `xs ++ R` is
-- `(residual on xs) ++ R`, with the SAME firing decision.
--------------------------------------------------------------------------------

-- `extract-elem` on `xs ++ R`: if `k` is found in `xs` with residual `rest`
-- via the EXACT proof `p`, it is found in `xs ++ R` with residual `rest ++ R`
-- via the EXACT proof `++⁺ʳ R p` (the genuine `extract-elem` recursion on
-- `xs ++ R` literally rebuilds `p`'s constructor tree with `R` appended, so the
-- two proofs are *propositionally* equal — no faithfulness/coherence needed).
-- The cod `(k ∷ rest) ++ R` is definitionally `k ∷ (rest ++ R)`.
extract-elem-++ˡ
  : ∀ {n} (k : Fin n) (xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ k ∷ rest}
  → extract-elem k xs ≡ just (rest , p)
  → extract-elem k (xs ++ R) ≡ just (rest ++ R , PermProp.++⁺ʳ R p)
extract-elem-++ˡ k []       R ()
extract-elem-++ˡ k (x ∷ xs) R eq with x ≟ k
extract-elem-++ˡ k (x ∷ xs) R {rest} {p} eq | yes refl with eq
... | refl = refl
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q with extract-elem k xs in eqxs
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q | just (rest' , q') with eq
... | refl rewrite extract-elem-++ˡ k xs R eqxs = refl

-- `extract-prefix` on `xs ++ R`: if `ks` is found in `xs` with residual `rest`
-- via `p`, it is found in `xs ++ R` with residual `rest ++ R` via the EXACT
-- proof `subst₂ _↭_ refl (assoc-of-cod) (++⁺ʳ R p)` — the genuine recursion
-- rebuilds `p`'s tree with `R` appended, then the cod rebrackets from
-- `(ks ++ rest) ++ R` to `ks ++ (rest ++ R)` by `++-assoc`.
prefix-++ˡ-perm
  : ∀ {n} (ks : List (Fin n)) {xs R rest : List (Fin n)}
  → (xs ++ R) Perm.↭ (ks ++ rest) ++ R
  → (xs ++ R) Perm.↭ ks ++ (rest ++ R)
prefix-++ˡ-perm ks {xs} {R} {rest} q =
  subst (λ z → (xs ++ R) Perm.↭ z) (++-assoc ks rest R) q

extract-prefix-++ˡ
  : ∀ {n} (ks xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ ks ++ rest}
  → extract-prefix ks xs ≡ just (rest , p)
  → extract-prefix ks (xs ++ R)
    ≡ just (rest ++ R , prefix-++ˡ-perm ks (PermProp.++⁺ʳ R p))
extract-prefix-++ˡ []       xs R {rest} {p} eq with eq
... | refl = refl
extract-prefix-++ˡ (k ∷ ks) xs R eq with extract-elem k xs in eqe
extract-prefix-++ˡ (k ∷ ks) xs R eq | just (xs' , pe) with extract-prefix ks xs' in eqp
extract-prefix-++ˡ (k ∷ ks) xs R {rest} {p} eq | just (xs' , pe)
  | just (rest' , pp) with eq
... | refl
      rewrite extract-elem-++ˡ k xs R eqe
            | extract-prefix-++ˡ ks xs' R eqp =
      cong (λ z → just (rest' ++ R , z)) perm-eq
  where
    -- The genuine `extract-prefix (k ∷ ks) (xs ++ R)` proof, assembled from the
    -- head `++⁺ʳ R pe` and tail `prefix-++ˡ-perm ks (++⁺ʳ R pp)`, equals the
    -- claimed `prefix-++ˡ-perm (k ∷ ks) (++⁺ʳ R (trans pe (prep k pp)))`.
    -- `++⁺ʳ` distributes over `trans`/`prep`, and the cod assoc on the cons
    -- (`++-assoc (k ∷ ks) rest' R = cong (k ∷_) (++-assoc ks rest' R)`) slides
    -- through the leading `prep k`.
    perm-eq
      : Perm.trans (PermProp.++⁺ʳ R pe)
          (Perm.prep k (prefix-++ˡ-perm ks {xs'} {R} {rest'} (PermProp.++⁺ʳ R pp)))
        ≡ prefix-++ˡ-perm (k ∷ ks) {xs} {R} {rest'}
            (PermProp.++⁺ʳ R (Perm.trans pe (Perm.prep k pp)))
    perm-eq = gen (++-assoc ks rest' R) (PermProp.++⁺ʳ R pp)
      where
        -- Generalise the cod assoc `e` and the tail proof `Q`: the leading
        -- `trans (head)`/`prep k` slide through the `subst`, and the cons assoc
        -- is `cong (k ∷_)` of the tail assoc.  Proven by `J` on `e`.
        gen
          : ∀ {a b : List (Fin _)} (e : a ≡ b)
              (Q : (xs' ++ R) Perm.↭ a)
          → Perm.trans (PermProp.++⁺ʳ R pe)
              (Perm.prep k (subst (λ z → (xs' ++ R) Perm.↭ z) e Q))
            ≡ subst (λ z → (xs ++ R) Perm.↭ z) (cong (k ∷_) e)
                (Perm.trans (PermProp.++⁺ʳ R pe) (Perm.prep k Q))
        gen refl Q = refl

-- NOTHING-direction of `extract-elem-++ˡ`.  CAVEAT: this is NOT unconditionally
-- true — `extract-elem k (xs ++ R)` can be `just` even when `extract-elem k xs`
-- is `nothing`, namely when `k ∈ R`.  For the separability invariant the
-- hypothesis is that the edge block is DISJOINT from `R` (`ein e ∩ R = ∅`), so
-- we require `extract-elem k R ≡ nothing` as a side condition.  Induction on
-- `xs`.
extract-elem-++ˡ-nothing
  : ∀ {n} (k : Fin n) (xs R : List (Fin n))
  → extract-elem k xs ≡ nothing
  → extract-elem k R  ≡ nothing
  → extract-elem k (xs ++ R) ≡ nothing
extract-elem-++ˡ-nothing k []       R eqx eqR = eqR
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR with x ≟ k
... | yes refl with eqx
...   | ()
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR | no ¬q with extract-elem k xs in eqxs
... | nothing rewrite extract-elem-++ˡ-nothing k xs R eqxs eqR = refl

-- FULL `nothing`-transport for `extract-prefix`.  If `ks` fails to extract from
-- `xs` AND every element of `ks` is absent from `R` (the disjointness side
-- condition), then `ks` fails to extract from `xs ++ R`.
extract-prefix-++ˡ-nothing
  : ∀ {n} (ks xs R : List (Fin n))
  → All (λ j → extract-elem j R ≡ nothing) ks
  → extract-prefix ks xs ≡ nothing
  → extract-prefix ks (xs ++ R) ≡ nothing
-- `extract-prefix [] xs ≡ just _`, so the `nothing` hypothesis is absurd.
extract-prefix-++ˡ-nothing []       xs R _          ()
extract-prefix-++ˡ-nothing (k ∷ ks) xs R (dk ∷ dks) eqn with extract-elem k xs in eqe
-- head not found in `xs`: by disjointness not in `R`, so not in `xs ++ R`.
... | nothing rewrite extract-elem-++ˡ-nothing k xs R eqe dk = refl
-- head found in `xs` with residual `xs'`: split on the tail.  `eqn` (whose type
-- reduces along the located head) forces the tail to fail; recurse on `ks` over
-- `xs'`, re-locating `k` in `xs ++ R` (`extract-elem-++ˡ`).
... | just (xs' , pe) with extract-prefix ks xs' in eqp
...     | nothing
          rewrite extract-elem-++ˡ k xs R eqe
                | extract-prefix-++ˡ-nothing ks xs' R dks eqp = refl
...     | just (_ , _) with eqn
...       | ()

--------------------------------------------------------------------------------
-- ## LEFT-frame separability (frame block on the LEFT of the searched list).
--
-- Mirror of the `++ˡ` family above.  `extract-elem`/`extract-prefix` walk
-- left-to-right, so a LEFT frame `F` is only transparent when the searched
-- keys are absent from it (`extract-elem k F ≡ nothing`); otherwise the key
-- would fire inside `F` and the residual shape would break.  That
-- disjointness side condition is exactly what the term-level strict decoder
-- lacks (making left-frame separability false there) but which holds at this
-- stack level for the disjoint `↑ˡ`/`↑ʳ` injections.  With it, `F` passes
-- through whole onto the residual: the residual on `F ++ xs` is
-- `F ++ (residual on xs)`.  Only the `just`/prefix directions are new; the
-- `nothing`-direction reuses `extract-elem-++ˡ-nothing` (which is symmetric).
--
-- OBSTRUCTION — why these stack lemmas are the strongest left-hand statement
-- available, i.e. why there is no LEFT-frame TERM-level mirror of
-- `Decoder.term-sepᵛ` for a block that fires.  Take `es = e ∷ []`, an `xs` with
-- `extract-prefix (H.ein e) xs ≡ just (rest , p)`, and an `L` disjoint from
-- `H.ein e`.  Then the `++ʳ` shape gives residual `L ++ rest`, so
-- `edge-stepˢ` on `L ++ xs` produces the stack
--     proj₁ (process-edgesˢ (e ∷ []) (L ++ xs)) = H.eout e ++ (L ++ rest)
-- whereas the framed form would need
--     L ++ proj₁ (process-edgesˢ (e ∷ []) xs)   = L ++ (H.eout e ++ rest)
-- and the two differ whenever `H.eout e` and `L` are non-empty and distinct:
-- the prepended output lands BEFORE the untouched `L`, so `map vl L` is no
-- longer a left prefix of the codomain and the codomain coherence `Q` of a
-- term-level `castˢ … Q … ≈ˢ idˢ {map vl L} ⊗ˢ …` cannot be supplied at all.
-- That is a list-equality mismatch, not a coherence gap, so no `≈ˢ`/cast
-- manoeuvre repairs it; a left frame for a firing block would have to slide
-- `H.eout e` back past `L` via `σ`, giving a BRAIDED form.  The RIGHT frame
-- survives precisely because outputs prepend, and the pure-permutation left
-- frame is `FreeStrictSMC.Restrict.permuteᵛ-frameˡ`.
--------------------------------------------------------------------------------

-- `extract-elem` on `F ++ xs` with `k` absent from `F`: `k` is located in `xs`
-- with residual `rest`, hence in `F ++ xs` with residual `F ++ rest`.  The
-- payload is existential — the mixed liftings only need `∃`.  Induction on `F`:
-- the head `f` cannot equal `k` (else the `F`-lookup would be `just`), so it is
-- skipped onto the residual.
extract-elem-++ʳ
  : ∀ {n} (k : Fin n) (F xs : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ k ∷ rest}
  → extract-elem k F ≡ nothing
  → extract-elem k xs ≡ just (rest , p)
  → ∃[ q ] extract-elem k (F ++ xs) ≡ just (F ++ rest , q)
extract-elem-++ʳ k []      xs {rest} {p} eqF eqx = p , eqx
extract-elem-++ʳ k (f ∷ F) xs eqF eqx with f ≟ k
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | yes refl with eqF
... | ()
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | no ¬q with extract-elem k F in eqFi
... | nothing with extract-elem-++ʳ k F xs eqFi eqx
...              | _ , e rewrite e = _ , refl
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | no ¬q | just _ with eqF
... | ()

-- NOTHING-direction of the left frame.  Same disjointness side condition;
-- structure mirrors `extract-prefix-via-injective-nothing`.
extract-prefix-++ʳ-nothing
  : ∀ {n} (ks F ys : List (Fin n))
  → All (λ k → extract-elem k F ≡ nothing) ks
  → extract-prefix ks ys ≡ nothing
  → extract-prefix ks (F ++ ys) ≡ nothing
extract-prefix-++ʳ-nothing []       F ys _          ()
extract-prefix-++ʳ-nothing (k ∷ ks) F ys (ak ∷ aks) eq with extract-elem k ys in eqe
-- head absent from `ys` (hyp) and from `F` (side cond) ⇒ absent from `F ++ ys`.
... | nothing rewrite extract-elem-++ˡ-nothing k F ys ak eqe = refl
... | just (ys' , pe) with extract-prefix ks ys' in eqp
...     | nothing with extract-elem-++ʳ k F ys ak eqe
...        | _ , e-elem
             rewrite e-elem
                   | extract-prefix-++ʳ-nothing ks F ys' aks eqp = refl
extract-prefix-++ʳ-nothing (k ∷ ks) F ys (ak ∷ aks) eq | just (ys' , pe)
    | just (_ , _) with eq
...    | ()

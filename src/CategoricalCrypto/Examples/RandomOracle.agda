{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Examples.RandomOracle where

open import categorical-crypto.Prelude hiding (_/_; _>>=_; _*_)

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin using (Fin)
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Properties using
  (*-zeroˡ; *-zeroʳ; *-identityˡ; *-identityʳ; +-identityˡ; +-identityʳ
  ; *-distribʳ-+; *-distribˡ-+; +-*-commutativeRing)
open import Data.Vec hiding (length)
open import Data.Vec.Relation.Unary.All as VecAll using (All)
open import Data.Vec.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Tactic.Solver.Ring using (solve-≈)

open import CategoricalCrypto.SFunM
open import ProbabilisticLogic.Distribution.RationalDist renaming (_>>=ᴹ_ to _>>=_)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform

private
  ℚᴿ = CommutativeRing.commutativeSemiring +-*-commutativeRing

------------------------------------------------------------------------
-- Random oracle functionality for `p` parties, hashing input bytestrings
-- of length `inN` to output bytestrings of length `outN`.

module RandomOracle (p : ℕ) (In : Type) ⦃ _ : DecEq In ⦄ (outN : ℕ) where

  Out : Type
  Out = Vec Bool outN

  uniform-Out : Dist-ℚ Out
  uniform-Out = uniform-Vec outN

  Input  = Fin p × In
  Output = Fin p × Out
  Table  = List (In × Out)

  lookup-bs : Table → In → Maybe Out
  lookup-bs []             _ = nothing
  lookup-bs ((k , v) ∷ xs) q with q ≟ k
  ... | yes _ = just v
  ... | no  _ = lookup-bs xs q

  -- A point already in the table is answered FROM the table.  `lookup-bs`
  -- branches on a `with`, so the reflexive case has to be taken here rather
  -- than rewritten away by `Class.DecEq.Ext.≟-refl`.
  lookup-bs-here : ∀ s q h → lookup-bs ((q , h) ∷ s) q ≡ just h
  lookup-bs-here s q h with q ≟ q
  ... | yes _  = refl
  ... | no ¬eq = ⊥-elim (¬eq refl)

  step : SFunType Input Output Table
  step (s , i , q) = case lookup-bs s q of λ where
    (just h)  → return-ℚ (s , i , h)
    (nothing) → do h ← uniform-Out; return-ℚ ((q , h) ∷ s , i , h)

  Functionality : SFunᵉ {M = Dist-ℚ} Input Output
  Functionality = record
    { State = Table
    ; init  = []
    ; fun   = step
    }

  --------------------------------------------------------------------
  -- Probability claim: for a fresh query, the expected number of
  -- existing entries colliding with the freshly sampled hash is |s|/2ᵒᵘᵗᴺ.

  freshQuery : Table → In → Type
  freshQuery s q = lookup-bs s q ≡ nothing

  -- Expected value of `f` under a `Dist-ℚ`.
  E[_,_] : ∀ {ℓ} {A : Type ℓ} → Dist-ℚ A → (A → ℚ) → ℚ
  E[ μ , f ] = lookupᴰℚ (entries μ) f

  -- Number of entries in `s` whose stored hash equals `h`.
  count-matches : Table → Out → ℚ
  count-matches []             _ = 0ℚ
  count-matches ((_ , v) ∷ xs) h = δ v h + count-matches xs h

  -- For each output triple `(_ , _ , h)` of `step`, the number of
  -- queries already in `s` whose stored hash matches the sampled `h`.
  matching-queries : Table → Table × Fin p × Out → ℚ
  matching-queries s (_ , _ , h) = count-matches s h

  -- Indicator on step's output: 1 if the sampled hash equals the target.
  is-preimage : Out → Table × Fin p × Out → ℚ
  is-preimage target (_ , _ , h) = δ target h

  -- Sum of `1/2ᵒᵘᵗᴺ` over entries — i.e. `|s| · (1/2ᵒᵘᵗᴺ)` — but defined
  -- inductively so the proof can recurse on `s`.
  private
    sum-bound : Table → ℚ
    sum-bound []       = 0ℚ
    sum-bound (_ ∷ xs) = inv-pow-2 outN + sum-bound xs

    -- Closed form: `|s| · (1/2ᵒᵘᵗᴺ)`.
    sum-bound-closed : ∀ s → sum-bound s ≡ fromℕ (length s) * inv-pow-2 outN
    sum-bound-closed []       = sym (*-zeroˡ (inv-pow-2 outN))
    sum-bound-closed (_ ∷ xs) =
      trans (cong (inv-pow-2 outN +_) (sum-bound-closed xs))
            (suc·c (fromℕ (length xs)) (inv-pow-2 outN))

  -- The expected number of entries in `s` whose hash equals a
  -- uniformly-sampled bytestring is `|s|·(1/2ᵒᵘᵗᴺ)`.
  E-collisions : ∀ s
               → lookupᴰℚ (entries uniform-Out) (count-matches s)
               ≡ (fromℕ (length s)) * inv-pow-2 outN
  E-collisions s = trans (E-collisions-rec s) (sum-bound-closed s)
    where
      open ≡-Reasoning
      E-collisions-rec : ∀ s
                       → lookupᴰℚ (entries uniform-Out) (count-matches s) ≡ sum-bound s
      E-collisions-rec []             = lookupᴰℚ-zero (entries uniform-Out)
      E-collisions-rec ((_ , v) ∷ xs) = begin
          lookupᴰℚ (entries uniform-Out) (λ h → δ v h + count-matches xs h)
            ≡⟨ lookupᴰℚ-+ (entries uniform-Out) (δ v) (count-matches xs) ⟩
          lookupᴰℚ (entries uniform-Out) (δ v)
            + lookupᴰℚ (entries uniform-Out) (count-matches xs)
            ≡⟨ cong (_+ lookupᴰℚ (entries uniform-Out) (count-matches xs))
                   (P-uniform-Vec outN v) ⟩
          inv-pow-2 outN + lookupᴰℚ (entries uniform-Out) (count-matches xs)
            ≡⟨ cong (inv-pow-2 outN +_) (E-collisions-rec xs) ⟩
          inv-pow-2 outN + sum-bound xs ∎

  -- When `q` isn't already in the state, `step` just samples uniformly
  -- and prepends the new entry.
  step-fresh : ∀ s i q → freshQuery s q
             → step (s , i , q) ≡ (uniform-Out >>= λ h → return-ℚ ((q , h) ∷ s , i , h))
  step-fresh s i q lookup-q with lookup-bs s q | lookup-q
  ... | nothing | refl = refl

  -- Tying back to `step`: for a fresh query, the expected value of a
  -- function of the step's full output triple is the same as its value
  -- on the freshly-prepended-state output, with the hash drawn from
  -- `uniform-Out`.
  E-step-fresh-on : ∀ s i q → freshQuery s q → (f : Table × Fin p × Out → ℚ)
                  → E[ step (s , i , q) , f ]
                  ≡ E[ uniform-Out , (λ h → f ((q , h) ∷ s , i , h)) ]
  E-step-fresh-on s i q lookup-q f = begin
      E[ step (s , i , q) , f ]
        ≡⟨ cong (λ d → E[ d , f ]) (step-fresh s i q lookup-q) ⟩
      E[ uniform-Out >>= (λ h → return-ℚ ((q , h) ∷ s , i , h)) , f ]
        ≡⟨ lookupᴰℚ-bind (entries uniform-Out)
             (λ h → entries (return-ℚ ((q , h) ∷ s , i , h))) f ⟩
      lookupᴰℚ (entries uniform-Out)
        (λ h → E[ return-ℚ ((q , h) ∷ s , i , h) , f ])
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-Out)
             (λ h → lookupᴰℚ-return ((q , h) ∷ s , i , h) f) ⟩
      E[ uniform-Out , (λ h → f ((q , h) ∷ s , i , h)) ] ∎
    where open ≡-Reasoning

  -- Specialisation observing only the freshly sampled hash.
  E-step-fresh : ∀ s i q → freshQuery s q → (f : Out → ℚ)
               → E[ step (s , i , q) , (λ o → f (proj₂ (proj₂ o))) ]
               ≡ E[ uniform-Out , f ]
  E-step-fresh s i q lookup-q f =
    E-step-fresh-on s i q lookup-q (λ o → f (proj₂ (proj₂ o)))

  -- Probability that a fresh query hits a specific target bit-string is
  -- `1/2ᵒᵘᵗᴺ`.
  preimage-prob : ∀ s i q (target : Out) → freshQuery s q
                → E[ step (s , i , q) , is-preimage target ]
                ≡ inv-pow-2 outN
  preimage-prob s i q target lookup-q =
    trans (E-step-fresh s i q lookup-q (δ target)) (P-uniform-Vec outN target)

  -- Expected number of state entries colliding with a fresh query is
  -- `|s|/2ᵒᵘᵗᴺ`.
  collision-prob : ∀ s i q → freshQuery s q
                 → E[ step (s , i , q) , matching-queries s ]
                 ≡ fromℕ (length s) * inv-pow-2 outN
  collision-prob s i q lookup-q =
    trans (E-step-fresh s i q lookup-q (count-matches s)) (E-collisions s)

  --------------------------------------------------------------------
  -- The birthday paradox.

  -- Drawing `k` independent uniform bytestrings.
  sample-k : (k : ℕ) → Dist-ℚ (Vec Out k)
  sample-k zero    = return-ℚ []
  sample-k (suc k) = uniform-Out >>= λ h → Dmap (h ∷_) (sample-k k)

  -- Number of bytestrings in `hs` equal to `target`.
  count-matches-Vec : ∀ {k} → Vec Out k → Out → ℚ
  count-matches-Vec []       _      = 0ℚ
  count-matches-Vec (h ∷ hs) target = δ h target + count-matches-Vec hs target

  -- Number of unordered index-pairs `(i, j)` with `hs[i] = hs[j]`.
  count-pairs : ∀ {k} → Vec Out k → ℚ
  count-pairs []       = 0ℚ
  count-pairs (h ∷ hs) = count-matches-Vec hs h + count-pairs hs

  -- The triangle number `k · (k-1) / 2`.
  triangle : ℕ → ℚ
  triangle zero    = 0ℚ
  triangle (suc k) = fromℕ k + triangle k

  private
    -- The expectation of a constant under any distribution is that
    -- constant (since mass = 1).
    E-const : ∀ {ℓ} {A : Type ℓ} (μ : Dist-ℚ A) (c : ℚ)
            → E[ μ , (λ _ → c) ] ≡ c
    E-const μ c = begin
        E[ μ , (λ _ → c) ]
          ≡⟨ mass-as-const (entries μ) c ⟩
        mass (entries μ) * c
          ≡⟨ cong (_* c) (mass-1 μ) ⟩
        1ℚ * c
          ≡⟨ *-identityˡ c ⟩
        c ∎
      where open ≡-Reasoning

    -- The expected number of `hs`-elements matching a uniformly
    -- sampled bytestring is `(length hs)/2ᵒᵘᵗᴺ`.
    E-matches-uniform : ∀ {k} (hs : Vec Out k)
                      → E[ uniform-Out , count-matches-Vec hs ] ≡ fromℕ k * inv-pow-2 outN
    E-matches-uniform []              = trans (lookupᴰℚ-zero (entries uniform-Out))
                                              (sym (*-zeroˡ (inv-pow-2 outN)))
    E-matches-uniform {suc k} (h ∷ hs) = begin
        E[ uniform-Out , count-matches-Vec (h ∷ hs) ]
          ≡⟨ lookupᴰℚ-+ (entries uniform-Out) (δ h) (count-matches-Vec hs) ⟩
        E[ uniform-Out , δ h ] + E[ uniform-Out , count-matches-Vec hs ]
          ≡⟨ cong (_+ E[ uniform-Out , count-matches-Vec hs ]) (P-uniform-Vec outN h) ⟩
        inv-pow-2 outN + E[ uniform-Out , count-matches-Vec hs ]
          ≡⟨ cong (inv-pow-2 outN +_) (E-matches-uniform hs) ⟩
        inv-pow-2 outN + fromℕ k * inv-pow-2 outN
          ≡⟨ suc·c (fromℕ k) (inv-pow-2 outN) ⟩
        (1ℚ + fromℕ k) * inv-pow-2 outN ∎
      where open ≡-Reasoning

  -- The birthday paradox.
  birthday : (k : ℕ) → E[ sample-k k , count-pairs ] ≡ triangle k * inv-pow-2 outN
  birthday zero    = trans (lookupᴰℚ-return [] count-pairs)
                           (sym (*-zeroˡ (inv-pow-2 outN)))
  birthday (suc k) = begin
      E[ sample-k (suc k) , count-pairs ]
        ≡⟨ lookupᴰℚ-bind (entries uniform-Out)
             (λ h → entries (Dmap (h ∷_) (sample-k k))) count-pairs ⟩
      E[ uniform-Out , (λ h → E[ Dmap (h ∷_) (sample-k k) , count-pairs ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-Out)
             (λ h → lookupᴰℚ-Dmap (h ∷_) (sample-k k) count-pairs) ⟩
      E[ uniform-Out ,
         (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h + count-pairs hs) ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-Out) (λ h →
             lookupᴰℚ-+ (entries (sample-k k))
                        (λ hs → count-matches-Vec hs h) count-pairs) ⟩
      E[ uniform-Out , (λ h →
           E[ sample-k k , (λ hs → count-matches-Vec hs h) ]
         + E[ sample-k k , count-pairs ]) ]
        ≡⟨ lookupᴰℚ-+ (entries uniform-Out)
             (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h) ])
             (λ _ → E[ sample-k k , count-pairs ]) ⟩
      E[ uniform-Out , (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h) ]) ]
        + E[ uniform-Out , (λ _ → E[ sample-k k , count-pairs ]) ]
        ≡⟨ cong₂ _+_
             (trans (lookupᴰℚ-swap (entries uniform-Out) (entries (sample-k k))
                                   (λ h hs → count-matches-Vec hs h))
              (trans (lookupᴰℚ-cong-P (entries (sample-k k))
                                      (λ hs → E-matches-uniform hs))
                     (E-const (sample-k k) (fromℕ k * inv-pow-2 outN))))
             (trans (E-const uniform-Out E[ sample-k k , count-pairs ])
                    (birthday k)) ⟩
      fromℕ k * inv-pow-2 outN + triangle k * inv-pow-2 outN
        ≡⟨ sym (*-distribʳ-+ (inv-pow-2 outN) (fromℕ k) (triangle k)) ⟩
      (fromℕ k + triangle k) * inv-pow-2 outN ∎
    where open ≡-Reasoning

  --------------------------------------------------------------------
  -- Birthday paradox specialised to the random oracle.

  -- k-times iterated `step` distribution, threading the state.
  step^ : ∀ {k} → Fin p → Vec In k → Table → Dist-ℚ Table
  step^ _ []       s = return-ℚ s
  step^ i (q ∷ qs) s = step (s , i , q) >>= λ (s' , _ , _) → step^ i qs s'

  -- Number of unordered pairs of entries with the same hash.
  state-collisions : Table → ℚ
  state-collisions []             = 0ℚ
  state-collisions ((_ , h) ∷ ps) = count-matches ps h + state-collisions ps

  -- A bytestring is not a key of any entry in the table.
  _∉Keys_ : In → Table → Type
  q ∉Keys s = ListAll.All (λ (k , _) → q ≢ k) s

  private
    -- If every q' in qs is ≢ q and q' ∉Keys s, then q' ∉Keys ((q,h)∷s).
    AllNotIn-cons : ∀ {k} {q h} {qs : Vec In k} {s}
                  → All (q ≢_) qs → All (_∉Keys s) qs
                  → All (_∉Keys ((q , h) ∷ s)) qs
    AllNotIn-cons VecAll.[]               VecAll.[]            = VecAll.[]
    AllNotIn-cons (q≢q' VecAll.∷ q∉qs') (q'∉s VecAll.∷ rest) =
      ((λ q'≡q → q≢q' (sym q'≡q)) ListAll.∷ q'∉s) VecAll.∷ AllNotIn-cons q∉qs' rest

    -- Specialisation observing only the post-step state.
    E-step-state-fresh : ∀ (s : Table) (i : Fin p) (q : In) (P : Table → ℚ)
                       → lookup-bs s q ≡ nothing
                       → E[ step (s , i , q) , (λ o → P (proj₁ o)) ]
                       ≡ E[ uniform-Out , (λ h → P ((q , h) ∷ s)) ]
    E-step-state-fresh s i q P fresh =
      E-step-fresh-on s i q fresh (λ o → P (proj₁ o))

    -- A `∉Keys` proof gives `lookup-bs s q ≡ nothing`.
    ∉Keys⇒lookup-nothing : ∀ {q s} → q ∉Keys s → lookup-bs s q ≡ nothing
    ∉Keys⇒lookup-nothing {s = []}            _                    = refl
    ∉Keys⇒lookup-nothing {q} {(k , _) ∷ xs} (q≢k ListAll.∷ q∉) with q ≟ k
    ... | yes q≡k = ⊥-elim (q≢k q≡k)
    ... | no  _   = ∉Keys⇒lookup-nothing q∉

  -- The generalised birthday lemma: running `k` queries from a state
  -- whose keys are disjoint from `qs`, with `qs` distinct, the expected
  -- collision count grows by `|s|·k/2ᵒᵘᵗᴺ + k(k-1)/2 · (1/2ᵒᵘᵗᴺ)`.
  step^-collision-bound : ∀ {k} (i : Fin p) (qs : Vec In k) (s : Table)
                        → All (_∉Keys s) qs → AllPairs _≢_ qs
                        → E[ step^ i qs s , state-collisions ]
                        ≡ state-collisions s
                        + (fromℕ (length s) * fromℕ k + triangle k) * inv-pow-2 outN
  step^-collision-bound i [] s _ _ = begin
      E[ return-ℚ s , state-collisions ]
        ≡⟨ lookupᴰℚ-return s state-collisions ⟩
      state-collisions s
        ≡⟨ zero-bound (state-collisions s) (fromℕ (length s)) (inv-pow-2 outN) ⟩
      state-collisions s + (fromℕ (length s) * 0ℚ + 0ℚ) * inv-pow-2 outN ∎
    where
      open ≡-Reasoning
      -- fromℕ 0 = 0ℚ and triangle 0 = 0ℚ, so this is `d ≡ d + (a · 0 + 0) · e`.
      zero-bound : ∀ d a e → d ≡ d + (a * 0ℚ + 0ℚ) * e
      zero-bound d a e = begin
          d
            ≡⟨ sym (+-identityʳ d) ⟩
          d + 0ℚ
            ≡⟨ cong (d +_) (sym (*-zeroˡ e)) ⟩
          d + 0ℚ * e
            ≡⟨ cong (λ z → d + z * e) (sym (+-identityʳ 0ℚ)) ⟩
          d + (0ℚ + 0ℚ) * e
            ≡⟨ cong (λ z → d + (z + 0ℚ) * e) (sym (*-zeroʳ a)) ⟩
          d + (a * 0ℚ + 0ℚ) * e ∎
  step^-collision-bound {suc k} i (q ∷ qs) s (q∉s VecAll.∷ notIn) (q∉qs AllPairs.∷ dist) = begin
      E[ step^ i (q ∷ qs) s , state-collisions ]
        ≡⟨ lookupᴰℚ-bind (entries (step (s , i , q)))
             (λ o → entries (step^ i qs (proj₁ o)))
             state-collisions ⟩
      E[ step (s , i , q)
       , (λ o → E[ step^ i qs (proj₁ o) , state-collisions ]) ]
        ≡⟨ E-step-state-fresh s i q
             (λ s' → E[ step^ i qs s' , state-collisions ])
             (∉Keys⇒lookup-nothing q∉s) ⟩
      E[ uniform-Out , (λ h → E[ step^ i qs ((q , h) ∷ s) , state-collisions ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-Out) (λ h →
             step^-collision-bound i qs ((q , h) ∷ s)
               (AllNotIn-cons q∉qs notIn) dist) ⟩
      E[ uniform-Out , (λ h →
           state-collisions ((q , h) ∷ s)
         + (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN) ]
        ≡⟨ lookupᴰℚ-+ (entries uniform-Out)
             (λ h → state-collisions ((q , h) ∷ s))
             (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN) ⟩
      E[ uniform-Out , (λ h → state-collisions ((q , h) ∷ s)) ]
        + E[ uniform-Out
           , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN) ]
        ≡⟨ cong (_+ E[ uniform-Out
                     , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN) ])
             (lookupᴰℚ-+ (entries uniform-Out) (count-matches s) (λ _ → state-collisions s)) ⟩
      (E[ uniform-Out , count-matches s ] + E[ uniform-Out , (λ _ → state-collisions s) ])
        + E[ uniform-Out
           , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN) ]
        ≡⟨ cong₃ (λ a b c → a + b + c)
             (E-collisions s)
             (E-const uniform-Out (state-collisions s))
             (E-const uniform-Out _) ⟩
      (fromℕ (length s) * inv-pow-2 outN + state-collisions s)
        + (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 outN
        ≡⟨ rearrange (fromℕ (length s)) (fromℕ k) (triangle k) (state-collisions s) (inv-pow-2 outN) ⟩
      state-collisions s
        + (fromℕ (length s) * fromℕ (suc k) + triangle (suc k)) * inv-pow-2 outN ∎
    where
      open ≡-Reasoning
      cong₃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
              {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
              (f : A → B → C → D) {a a' b b' c c'}
            → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
      cong₃ f refl refl refl = refl
      -- Algebraic rearrangement:
      --   (a·e + d) + ((1+a)·b + c)·e = d + (a·(1+b) + (b+c))·e
      rearrange : ∀ a b c d e
                → (a * e + d) + ((1ℚ + a) * b + c) * e
                ≡ d + (a * (1ℚ + b) + (b + c)) * e
      rearrange a b c d e = begin
          (a * e + d) + ((1ℚ + a) * b + c) * e
            ≡⟨ cong (λ z → (a * e + d) + (z + c) * e)
                    (trans (*-distribʳ-+ b 1ℚ a)
                           (cong (_+ a * b) (*-identityˡ b))) ⟩
          (a * e + d) + ((b + a * b) + c) * e
            ≡⟨ solve-≈ ℚᴿ ⟩
          d + ((a + a * b) + (b + c)) * e
            ≡⟨ cong (λ z → d + (z + (b + c)) * e)
                    (trans (cong (_+ a * b) (sym (*-identityʳ a)))
                           (sym (*-distribˡ-+ a 1ℚ b))) ⟩
          d + (a * (1ℚ + b) + (b + c)) * e ∎

  -- Birthday paradox for the random oracle.
  RO-collision : ∀ {k} (i : Fin p) (qs : Vec In k) → AllPairs _≢_ qs
    → E[ step^ i qs [] , state-collisions ] ≡ triangle k * inv-pow-2 outN
  RO-collision {k} i qs dist = begin
      E[ step^ i qs [] , state-collisions ]
        ≡⟨ step^-collision-bound i qs [] (VecAll.universal (λ _ → ListAll.[]) qs) dist ⟩
      state-collisions [] + (fromℕ 0 * fromℕ k + triangle k) * inv-pow-2 outN
        ≡⟨⟩
      0ℚ + (0ℚ * fromℕ k + triangle k) * inv-pow-2 outN
        ≡⟨ +-identityˡ _ ⟩
      (0ℚ * fromℕ k + triangle k) * inv-pow-2 outN
        ≡⟨ cong (λ z → (z + triangle k) * inv-pow-2 outN) (*-zeroˡ (fromℕ k)) ⟩
      (0ℚ + triangle k) * inv-pow-2 outN
        ≡⟨ cong (_* inv-pow-2 outN) (+-identityˡ (triangle k)) ⟩
      triangle k * inv-pow-2 outN ∎
    where open ≡-Reasoning

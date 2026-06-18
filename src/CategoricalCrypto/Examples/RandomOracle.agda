{-# OPTIONS --safe #-}

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
-- Random oracle functionality for `p` parties hashing fixed-length
-- bytestrings of length `n`.

module RandomOracle (p n : ℕ) where

  BS : Type
  BS = Vec Bool n

  uniform-BS : Dist-ℚ BS
  uniform-BS = uniform-Vec n

  Input  = Fin p × BS
  Output = Fin p × BS
  Table  = List (BS × BS)

  lookup-bs : Table → BS → Maybe BS
  lookup-bs []             _ = nothing
  lookup-bs ((k , v) ∷ xs) q with q ≟ k
  ... | yes _ = just v
  ... | no  _ = lookup-bs xs q

  step : SFunType Input Output Table
  step (s , i , q) = case lookup-bs s q of λ where
    (just h)  → return-ℚ (s , i , h)
    (nothing) → do h ← uniform-BS; return-ℚ ((q , h) ∷ s , i , h)

  Functionality : SFunᵉ {M = Dist-ℚ} Input Output
  Functionality = record
    { State = Table
    ; init  = []
    ; fun   = step
    }

  --------------------------------------------------------------------
  -- Probability claim: for a fresh query, the expected number of
  -- existing entries colliding with the freshly sampled hash is |s|/2ⁿ.

  freshQuery : Table → BS → Type
  freshQuery s q = lookup-bs s q ≡ nothing

  -- Expected value of `f` under a `Dist-ℚ`.
  E[_,_] : ∀ {ℓ} {A : Type ℓ} → Dist-ℚ A → (A → ℚ) → ℚ
  E[ μ , f ] = lookupᴰℚ (entries μ) f

  -- Number of entries in `s` whose stored hash equals `h`.
  count-matches : Table → BS → ℚ
  count-matches []             _ = 0ℚ
  count-matches ((_ , v) ∷ xs) h = δ v h + count-matches xs h

  -- For each output triple `(_ , _ , h)` of `step`, the number of
  -- queries already in `s` whose stored hash matches the sampled `h`.
  matching-queries : Table → Table × Fin p × BS → ℚ
  matching-queries s (_ , _ , h) = count-matches s h

  -- Indicator on step's output: 1 if the sampled hash equals the target.
  is-preimage : BS → Table × Fin p × BS → ℚ
  is-preimage target (_ , _ , h) = δ target h

  -- Sum of `1/2ⁿ` over entries — i.e. `|s| · (1/2ⁿ)` — but defined
  -- inductively so the proof can recurse on `s`.
  private
    sum-bound : Table → ℚ
    sum-bound []       = 0ℚ
    sum-bound (_ ∷ xs) = inv-pow-2 n + sum-bound xs

    -- Closed form: `|s| · (1/2ⁿ)`.
    sum-bound-closed : ∀ s → sum-bound s ≡ fromℕ (length s) * inv-pow-2 n
    sum-bound-closed []       = sym (*-zeroˡ (inv-pow-2 n))
    sum-bound-closed (_ ∷ xs) =
      trans (cong (inv-pow-2 n +_) (sum-bound-closed xs))
            (suc·c (fromℕ (length xs)) (inv-pow-2 n))

  -- The expected number of entries in `s` whose hash equals a
  -- uniformly-sampled bytestring is `|s|·(1/2ⁿ)`.
  E-collisions : ∀ s
               → lookupᴰℚ (entries uniform-BS) (count-matches s)
               ≡ (fromℕ (length s)) * inv-pow-2 n
  E-collisions s = trans (E-collisions-rec s) (sum-bound-closed s)
    where
      open ≡-Reasoning
      E-collisions-rec : ∀ s
                       → lookupᴰℚ (entries uniform-BS) (count-matches s) ≡ sum-bound s
      E-collisions-rec []             = lookupᴰℚ-zero (entries uniform-BS)
      E-collisions-rec ((_ , v) ∷ xs) = begin
          lookupᴰℚ (entries uniform-BS) (λ h → δ v h + count-matches xs h)
            ≡⟨ lookupᴰℚ-+ (entries uniform-BS) (δ v) (count-matches xs) ⟩
          lookupᴰℚ (entries uniform-BS) (δ v)
            + lookupᴰℚ (entries uniform-BS) (count-matches xs)
            ≡⟨ cong (_+ lookupᴰℚ (entries uniform-BS) (count-matches xs))
                   (P-uniform-Vec n v) ⟩
          inv-pow-2 n + lookupᴰℚ (entries uniform-BS) (count-matches xs)
            ≡⟨ cong (inv-pow-2 n +_) (E-collisions-rec xs) ⟩
          inv-pow-2 n + sum-bound xs ∎

  -- When `q` isn't already in the state, `step` just samples uniformly
  -- and prepends the new entry.
  step-fresh : ∀ s i q → freshQuery s q
             → step (s , i , q) ≡ (uniform-BS >>= λ h → return-ℚ ((q , h) ∷ s , i , h))
  step-fresh s i q lookup-q with lookup-bs s q | lookup-q
  ... | nothing | refl = refl

  -- Tying back to `step`: for a fresh query, the expected value of a
  -- function of the step's full output triple is the same as its value
  -- on the freshly-prepended-state output, with the hash drawn from
  -- `uniform-BS`. `E-step-fresh` and `E-step-state-fresh` below are
  -- thin specialisations.
  E-step-fresh-on : ∀ s i q → freshQuery s q → (f : Table × Fin p × BS → ℚ)
                  → E[ step (s , i , q) , f ]
                  ≡ E[ uniform-BS , (λ h → f ((q , h) ∷ s , i , h)) ]
  E-step-fresh-on s i q lookup-q f = begin
      E[ step (s , i , q) , f ]
        ≡⟨ cong (λ d → E[ d , f ]) (step-fresh s i q lookup-q) ⟩
      E[ uniform-BS >>= (λ h → return-ℚ ((q , h) ∷ s , i , h)) , f ]
        ≡⟨ lookupᴰℚ-bind (entries uniform-BS)
             (λ h → entries (return-ℚ ((q , h) ∷ s , i , h))) f ⟩
      lookupᴰℚ (entries uniform-BS)
        (λ h → E[ return-ℚ ((q , h) ∷ s , i , h) , f ])
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-BS)
             (λ h → lookupᴰℚ-return ((q , h) ∷ s , i , h) f) ⟩
      E[ uniform-BS , (λ h → f ((q , h) ∷ s , i , h)) ] ∎
    where open ≡-Reasoning

  -- Specialisation observing only the freshly sampled hash.
  E-step-fresh : ∀ s i q → freshQuery s q → (f : BS → ℚ)
               → E[ step (s , i , q) , (λ o → f (proj₂ (proj₂ o))) ]
               ≡ E[ uniform-BS , f ]
  E-step-fresh s i q lookup-q f =
    E-step-fresh-on s i q lookup-q (λ o → f (proj₂ (proj₂ o)))

  -- Probability that a fresh query hits a specific target bit-string is
  -- `1/2ⁿ`. So an adversary querying the oracle needs about `2ⁿ⁻¹`
  -- queries to find a preimage of a target with probability `1/2`.
  preimage-prob : ∀ s i q (target : BS) → freshQuery s q
                → E[ step (s , i , q) , is-preimage target ]
                ≡ inv-pow-2 n
  preimage-prob s i q target lookup-q =
    trans (E-step-fresh s i q lookup-q (δ target)) (P-uniform-Vec n target)

  -- Expected number of state entries colliding with a fresh query is
  -- `|s|/2ⁿ`. By the birthday paradox, an adversary populating `s`
  -- needs about `2^(n/2)` queries to find a collision with constant
  -- probability.
  collision-prob : ∀ s i q → freshQuery s q
                 → E[ step (s , i , q) , matching-queries s ]
                 ≡ fromℕ (length s) * inv-pow-2 n
  collision-prob s i q lookup-q =
    trans (E-step-fresh s i q lookup-q (count-matches s)) (E-collisions s)

  --------------------------------------------------------------------
  -- The birthday paradox.
  --
  -- Starting from an empty state, after `k` distinct fresh queries the
  -- expected number of pairs of queries whose hashes coincide is
  -- `k(k-1)/2 · (1/2ⁿ)`. So the expected count reaches order 1 around
  -- `k ≈ 2^(n/2)`.

  -- Drawing `k` independent uniform bytestrings — equivalent to the
  -- distribution over responses of `k` distinct fresh oracle queries.
  sample-k : (k : ℕ) → Dist-ℚ (Vec BS k)
  sample-k zero    = return-ℚ []
  sample-k (suc k) = uniform-BS >>= λ h → Dmap (h ∷_) (sample-k k)

  -- Number of bytestrings in `hs` equal to `target`.
  count-matches-Vec : ∀ {k} → Vec BS k → BS → ℚ
  count-matches-Vec []       _      = 0ℚ
  count-matches-Vec (h ∷ hs) target = δ h target + count-matches-Vec hs target

  -- Number of unordered index-pairs `(i, j)` with `hs[i] = hs[j]`.
  count-pairs : ∀ {k} → Vec BS k → ℚ
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
    -- sampled bytestring is `(length hs)/2ⁿ`.
    E-matches-uniform : ∀ {k} (hs : Vec BS k)
                      → E[ uniform-BS , count-matches-Vec hs ] ≡ fromℕ k * inv-pow-2 n
    E-matches-uniform []              = trans (lookupᴰℚ-zero (entries uniform-BS))
                                              (sym (*-zeroˡ (inv-pow-2 n)))
    E-matches-uniform {suc k} (h ∷ hs) = begin
        E[ uniform-BS , count-matches-Vec (h ∷ hs) ]
          ≡⟨ lookupᴰℚ-+ (entries uniform-BS) (δ h) (count-matches-Vec hs) ⟩
        E[ uniform-BS , δ h ] + E[ uniform-BS , count-matches-Vec hs ]
          ≡⟨ cong (_+ E[ uniform-BS , count-matches-Vec hs ]) (P-uniform-Vec n h) ⟩
        inv-pow-2 n + E[ uniform-BS , count-matches-Vec hs ]
          ≡⟨ cong (inv-pow-2 n +_) (E-matches-uniform hs) ⟩
        inv-pow-2 n + fromℕ k * inv-pow-2 n
          ≡⟨ suc·c (fromℕ k) (inv-pow-2 n) ⟩
        (1ℚ + fromℕ k) * inv-pow-2 n ∎
      where open ≡-Reasoning

  -- The birthday paradox.
  birthday : (k : ℕ) → E[ sample-k k , count-pairs ] ≡ triangle k * inv-pow-2 n
  birthday zero    = trans (lookupᴰℚ-return [] count-pairs)
                           (sym (*-zeroˡ (inv-pow-2 n)))
  birthday (suc k) = begin
      E[ sample-k (suc k) , count-pairs ]
        ≡⟨ lookupᴰℚ-bind (entries uniform-BS)
             (λ h → entries (Dmap (h ∷_) (sample-k k))) count-pairs ⟩
      E[ uniform-BS , (λ h → E[ Dmap (h ∷_) (sample-k k) , count-pairs ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-BS)
             (λ h → lookupᴰℚ-Dmap (h ∷_) (sample-k k) count-pairs) ⟩
      E[ uniform-BS ,
         (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h + count-pairs hs) ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-BS) (λ h →
             lookupᴰℚ-+ (entries (sample-k k))
                        (λ hs → count-matches-Vec hs h) count-pairs) ⟩
      E[ uniform-BS , (λ h →
           E[ sample-k k , (λ hs → count-matches-Vec hs h) ]
         + E[ sample-k k , count-pairs ]) ]
        ≡⟨ lookupᴰℚ-+ (entries uniform-BS)
             (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h) ])
             (λ _ → E[ sample-k k , count-pairs ]) ⟩
      E[ uniform-BS , (λ h → E[ sample-k k , (λ hs → count-matches-Vec hs h) ]) ]
        + E[ uniform-BS , (λ _ → E[ sample-k k , count-pairs ]) ]
        ≡⟨ cong₂ _+_
             (trans (lookupᴰℚ-swap (entries uniform-BS) (entries (sample-k k))
                                   (λ h hs → count-matches-Vec hs h))
              (trans (lookupᴰℚ-cong-P (entries (sample-k k))
                                      (λ hs → E-matches-uniform hs))
                     (E-const (sample-k k) (fromℕ k * inv-pow-2 n))))
             (trans (E-const uniform-BS E[ sample-k k , count-pairs ])
                    (birthday k)) ⟩
      fromℕ k * inv-pow-2 n + triangle k * inv-pow-2 n
        ≡⟨ sym (*-distribʳ-+ (inv-pow-2 n) (fromℕ k) (triangle k)) ⟩
      (fromℕ k + triangle k) * inv-pow-2 n ∎
    where open ≡-Reasoning

  --------------------------------------------------------------------
  -- Birthday paradox specialised to the random oracle.
  --
  -- Running `step` `k` times on distinct queries starting from the
  -- empty state, the expected number of hash collisions in the
  -- resulting state is `k(k-1)/2 · (1/2ⁿ)`.

  -- k-times iterated `step` distribution, threading the state.
  step^ : ∀ {k} → Fin p → Vec BS k → Table → Dist-ℚ Table
  step^ _ []       s = return-ℚ s
  step^ i (q ∷ qs) s = step (s , i , q) >>= λ (s' , _ , _) → step^ i qs s'

  -- Number of unordered pairs of entries with the same hash.
  state-collisions : Table → ℚ
  state-collisions []             = 0ℚ
  state-collisions ((_ , h) ∷ ps) = count-matches ps h + state-collisions ps

  -- A bytestring is not a key of any entry in the table.
  _∉Keys_ : BS → Table → Type
  q ∉Keys s = ListAll.All (λ (k , _) → q ≢ k) s

  private
    -- If every q' in qs is ≢ q and q' ∉Keys s, then q' ∉Keys ((q,h)∷s).
    AllNotIn-cons : ∀ {k} {q h} {qs : Vec BS k} {s}
                  → All (q ≢_) qs → All (_∉Keys s) qs
                  → All (_∉Keys ((q , h) ∷ s)) qs
    AllNotIn-cons VecAll.[]               VecAll.[]            = VecAll.[]
    AllNotIn-cons (q≢q' VecAll.∷ q∉qs') (q'∉s VecAll.∷ rest) =
      ((λ q'≡q → q≢q' (sym q'≡q)) ListAll.∷ q'∉s) VecAll.∷ AllNotIn-cons q∉qs' rest

    -- Specialisation observing only the post-step state.
    E-step-state-fresh : ∀ (s : Table) (i : Fin p) (q : BS) (P : Table → ℚ)
                       → lookup-bs s q ≡ nothing
                       → E[ step (s , i , q) , (λ o → P (proj₁ o)) ]
                       ≡ E[ uniform-BS , (λ h → P ((q , h) ∷ s)) ]
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
  -- collision count grows by `|s|·k/2ⁿ + k(k-1)/2 · (1/2ⁿ)`.
  step^-collision-bound : ∀ {k} (i : Fin p) (qs : Vec BS k) (s : Table)
                        → All (_∉Keys s) qs → AllPairs _≢_ qs
                        → E[ step^ i qs s , state-collisions ]
                        ≡ state-collisions s
                        + (fromℕ (length s) * fromℕ k + triangle k) * inv-pow-2 n
  step^-collision-bound i [] s _ _ = begin
      E[ return-ℚ s , state-collisions ]
        ≡⟨ lookupᴰℚ-return s state-collisions ⟩
      state-collisions s
        ≡⟨ zero-bound (state-collisions s) (fromℕ (length s)) (inv-pow-2 n) ⟩
      state-collisions s + (fromℕ (length s) * 0ℚ + 0ℚ) * inv-pow-2 n ∎
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
      E[ uniform-BS , (λ h → E[ step^ i qs ((q , h) ∷ s) , state-collisions ]) ]
        ≡⟨ lookupᴰℚ-cong-P (entries uniform-BS) (λ h →
             step^-collision-bound i qs ((q , h) ∷ s)
               (AllNotIn-cons q∉qs notIn) dist) ⟩
      E[ uniform-BS , (λ h →
           state-collisions ((q , h) ∷ s)
         + (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n) ]
        ≡⟨ lookupᴰℚ-+ (entries uniform-BS)
             (λ h → state-collisions ((q , h) ∷ s))
             (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n) ⟩
      E[ uniform-BS , (λ h → state-collisions ((q , h) ∷ s)) ]
        + E[ uniform-BS
           , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n) ]
        ≡⟨ cong (_+ E[ uniform-BS
                     , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n) ])
             (lookupᴰℚ-+ (entries uniform-BS) (count-matches s) (λ _ → state-collisions s)) ⟩
      (E[ uniform-BS , count-matches s ] + E[ uniform-BS , (λ _ → state-collisions s) ])
        + E[ uniform-BS
           , (λ _ → (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n) ]
        ≡⟨ cong₃ (λ a b c → a + b + c)
             (E-collisions s)
             (E-const uniform-BS (state-collisions s))
             (E-const uniform-BS _) ⟩
      (fromℕ (length s) * inv-pow-2 n + state-collisions s)
        + (fromℕ (suc (length s)) * fromℕ k + triangle k) * inv-pow-2 n
        ≡⟨ rearrange (fromℕ (length s)) (fromℕ k) (triangle k) (state-collisions s) (inv-pow-2 n) ⟩
      state-collisions s
        + (fromℕ (length s) * fromℕ (suc k) + triangle (suc k)) * inv-pow-2 n ∎
    where
      open ≡-Reasoning
      cong₃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
              {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
              (f : A → B → C → D) {a a' b b' c c'}
            → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
      cong₃ f refl refl refl = refl
      -- Algebraic rearrangement:
      --   (a·e + d) + ((1+a)·b + c)·e = d + (a·(1+b) + (b+c))·e
      -- The two `1ℚ`-bearing endpoints are unfolded by hand; the
      -- pure-variable middle is discharged by the ring solver.
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

  -- Birthday paradox for the random oracle: running `step` on `k`
  -- distinct queries starting from the empty state, the expected number
  -- of hash collisions in the resulting state is `k(k-1)/2 · (1/2ⁿ)`.
  RO-collision : ∀ {k} (i : Fin p) (qs : Vec BS k) → AllPairs _≢_ qs
    → E[ step^ i qs [] , state-collisions ] ≡ triangle k * inv-pow-2 n
  RO-collision {k} i qs dist = begin
      E[ step^ i qs [] , state-collisions ]
        ≡⟨ step^-collision-bound i qs [] (VecAll.universal (λ _ → ListAll.[]) qs) dist ⟩
      state-collisions [] + (fromℕ 0 * fromℕ k + triangle k) * inv-pow-2 n
        ≡⟨⟩
      0ℚ + (0ℚ * fromℕ k + triangle k) * inv-pow-2 n
        ≡⟨ +-identityˡ _ ⟩
      (0ℚ * fromℕ k + triangle k) * inv-pow-2 n
        ≡⟨ cong (λ z → (z + triangle k) * inv-pow-2 n) (*-zeroˡ (fromℕ k)) ⟩
      (0ℚ + triangle k) * inv-pow-2 n
        ≡⟨ cong (_* inv-pow-2 n) (+-identityˡ (triangle k)) ⟩
      triangle k * inv-pow-2 n ∎
    where open ≡-Reasoning

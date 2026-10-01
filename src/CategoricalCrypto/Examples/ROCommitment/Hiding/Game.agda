{-# OPTIONS --safe --without-K #-}

-- The closed hiding game and its ε.
--
-- `respRʰ` is a hand transcription of the real protocol `realʰ` over the
-- resource, drawing the opening randomness at the commitment; `respLʰ` the
-- same with that draw deferred to the step that could read it; `respIʰ` a
-- transcription of `F_com` behind the programming simulator.  No theorem
-- connects the two transcriptions to the machines (`docs/fcom-hiding.md`,
-- "Not delivered").  `hiding-bound` is `respLʰ` against `respIʰ`: they differ
-- only at an oracle query that hits the deferred opening point while a
-- commitment is outstanding, a flag raised by a fresh draw at each query, so
-- `Potential.rare-cert` bounds it by `m·2⁻ᵏ`.  `respLʰ` against `respRʰ` is
-- `Hiding.Defer`'s hop, and `Defer.hiding-bound-total` the ε against `respRʰ`.

open import Class.DecEq

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Vec.Base renaming (_∷_ to _∷ᵛ_)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Partial using (cond; cond-diag)
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.Examples.ROCommitment.Hiding.Game (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k

------------------------------------------------------------------------
-- The alphabet and the three state spaces

data Qʰ : Set where
  askQʰ : Pt → Qʰ
  comQʰ : Bool → Qʰ
  opnQʰ : Qʰ

data Rʰ : Set where
  ansRʰ  : Dig → Rʰ
  comRʰ  : Dig → Rʰ
  opnRʰ  : Bool → Dig → Rʰ
  idleRʰ : Rʰ

-- The commitment on the table: the digest published, the bit, and whether the
-- opening has gone out.
Comʰ : Set
Comʰ = Maybe (Dig × Bool × Bool)

-- …and what the real game keeps instead, the opening randomness included.
ComRʰ : Set
ComRʰ = Maybe (Dig × Bool × Dig × Bool)

St StLʰ StRʰ : Set
St   = Tbl × Comʰ × Bool         -- the coupling: + the hit flag
StLʰ = Tbl × Comʰ                -- the deferred and the ideal games
StRʰ = Maybe Dig × Tbl × ComRʰ

eraseʰ : St → StLʰ
eraseʰ (t , m , _) = t , m

hitOf : St → Bool
hitOf (_ , _ , f) = f

------------------------------------------------------------------------
-- The point the deferred game watches for

-- Does this query name the commitment's own point, for THIS draw of the
-- opening randomness?  Only while a commitment is outstanding: before one
-- there is no point to hit, and after the opening the point is in the table,
-- where both games read it.
hitAt : Comʰ → Pt → Dig → Bool
hitAt (just (_ , b , false)) x ρ = ⌊ head x ≟ b ⌋ ∧ ⌊ ρ ≟ tail x ⌋
hitAt (just (_ , _ , true))  _ _ = false
hitAt nothing                _ _ = false

-- …and what the real committer's own table entry answers there.
pinAt : Comʰ → Dig → Dig
pinAt (just (c , _ , _)) _ = c
pinAt nothing            d = d

-- The outcome of one step in each game, NAMED.  `_>>=ᴹ_` is a defined
-- function, so no `E-bind` rewrite below can recover a continuation from a
-- kernel by unification; every one of them has to be pointed at.
outAskB : Comʰ → Bool → Pt → Tbl × Dig → Dig → St × (Rʰ × Rʰ)
outAskB m f x u ρ = ( (proj₁ u , m , f ∨ hitAt m x ρ)
                    , ( ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))
                      , ansRʰ (proj₂ u) ) )

outAskL : Comʰ → Pt → Tbl × Dig → Dig → StLʰ × Rʰ
outAskL m x u ρ =
  (proj₁ u , m) , ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))

outAskI : Comʰ → Tbl × Dig → StLʰ × Rʰ
outAskI m u = (proj₁ u , m) , ansRʰ (proj₂ u)

outComL : Tbl → Bool → Dig → StLʰ × Rʰ
outComL t b c = (t , just (c , b , false)) , comRʰ c

outOpnL : Tbl → Dig → Bool → Dig → StLʰ × Rʰ
outOpnL t c b r = ((b ∷ᵛ r , c) ∷ t , just (c , b , true)) , opnRʰ b r

outAskR : Maybe Dig → ComRʰ → Tbl × Dig → StRʰ × Rʰ
outAskR mr z u = (mr , proj₁ u , z) , ansRʰ (proj₂ u)

outComR : Dig → Bool → Tbl × Dig → StRʰ × Rʰ
outComR r b u = (just r , proj₁ u , just (proj₂ u , b , r , false)) , comRʰ (proj₂ u)

------------------------------------------------------------------------
-- The real game: the opening randomness drawn at the commitment

-- The first component is the secret, PLANTED or not yet drawn.  `comR` is the
-- only step that looks at it, and it draws it when it is not there; that is
-- what `defer-commit` below is about.
askR : StRʰ → Pt → Dist-ℚ (StRʰ × Rʰ)
askR (mr , t , z) x = fetchT id t x >>=ᴹ λ u → return-ℚ (outAskR mr z u)

comAt : Dig → Tbl → Bool → Dist-ℚ (StRʰ × Rʰ)
comAt r t b = fetchT id t (b ∷ᵛ r) >>=ᴹ λ u → return-ℚ (outComR r b u)

comR : StRʰ → Bool → Dist-ℚ (StRʰ × Rʰ)
comR (just r  , t , nothing) b = comAt r t b
comR (nothing , t , nothing) b = uniform-Vec k >>=ᴹ λ r → comAt r t b
comR (mr , t , just z)       _ = return-ℚ ((mr , t , just z) , idleRʰ)

opnR : StRʰ → Dist-ℚ (StRʰ × Rʰ)
opnR (mr , t , just (c , b , r , false)) =
  return-ℚ ((mr , t , just (c , b , r , true)) , opnRʰ b r)
opnR (mr , t , just (c , b , r , true))  =
  return-ℚ ((mr , t , just (c , b , r , true)) , idleRʰ)
opnR (mr , t , nothing)                  = return-ℚ ((mr , t , nothing) , idleRʰ)

respRʰ : StRʰ → Qʰ → Dist-ℚ (StRʰ × Rʰ)
respRʰ s (askQʰ x) = askR s x
respRʰ s (comQʰ b) = comR s b
respRʰ s opnQʰ     = opnR s

------------------------------------------------------------------------
-- The deferred game and the ideal game

-- The commitment and the opening are the SAME step in both.  At the
-- commitment a fresh uniform digest goes out — in the real world it is
-- `H(b ∷ r)` at a point nothing has queried, in the ideal world the
-- simulator's published digest.  At the opening `r` is drawn and its point is
-- PROGRAMMED to that digest, which is where the real world's table entry
-- already was.
comL : StLʰ → Bool → Dist-ℚ (StLʰ × Rʰ)
comL (t , nothing) b = uniform-Vec k >>=ᴹ λ c → return-ℚ (outComL t b c)
comL (t , just m)  _ = return-ℚ ((t , just m) , idleRʰ)

opnL : StLʰ → Dist-ℚ (StLʰ × Rʰ)
opnL (t , just (c , b , false)) = uniform-Vec k >>=ᴹ λ r → return-ℚ (outOpnL t c b r)
opnL (t , just (c , b , true))  = return-ℚ ((t , just (c , b , true)) , idleRʰ)
opnL (t , nothing)              = return-ℚ ((t , nothing) , idleRʰ)

askL : StLʰ → Pt → Dist-ℚ (StLʰ × Rʰ)
askL (t , m) x =
  fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskL m x u ρ)

askI : StLʰ → Pt → Dist-ℚ (StLʰ × Rʰ)
askI (t , m) x = fetchT id t x >>=ᴹ λ u → return-ℚ (outAskI m u)

respLʰ respIʰ : StLʰ → Qʰ → Dist-ℚ (StLʰ × Rʰ)
respLʰ s (askQʰ x) = askL s x
respLʰ s (comQʰ b) = comL s b
respLʰ s opnQʰ     = opnL s
respIʰ s (askQʰ x) = askI s x
respIʰ s (comQʰ b) = comL s b
respIʰ s opnQʰ     = opnL s

------------------------------------------------------------------------
-- The coupling

askB : St → Pt → Dist-ℚ (St × (Rʰ × Rʰ))
askB (t , m , f) x =
  fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskB m f x u ρ)

-- Off the oracle the two games step alike: the coupling carries the flag
-- along and emits the deferred game's answer on both sides.
liftʰ : Bool → StLʰ × Rʰ → St × (Rʰ × Rʰ)
liftʰ f w = (proj₁ (proj₁ w) , proj₂ (proj₁ w) , f) , (proj₂ w , proj₂ w)

respBʰ : St → Qʰ → Dist-ℚ (St × (Rʰ × Rʰ))
respBʰ s           (askQʰ x) = askB s x
respBʰ (t , m , f) (comQʰ b) = Dmap (liftʰ f) (comL (t , m) b)
respBʰ (t , m , f) opnQʰ     = Dmap (liftʰ f) (opnL (t , m))

module C = Coupling hitOf respBʰ

s₀ : St
s₀ = [] , nothing , false

sL₀ sI₀ : StLʰ
sL₀ = [] , nothing
sI₀ = [] , nothing

sR₀ : StRʰ
sR₀ = nothing , [] , nothing

------------------------------------------------------------------------
-- Both marginals are the reference games

ask-redᴸ : (t : Tbl) (m : Comʰ) (x : Pt) (G : StLʰ × Rʰ → ℚ)
         → E (askL (t , m) x) G
           ≡ E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ → G (outAskL m x u ρ)))
ask-redᴸ t m x = E-bind₂ (fetchT id t x) (uniform-Vec k) (outAskL m x)

private
  ask-redᴮ : (t : Tbl) (m : Comʰ) (f : Bool) (x : Pt) (G : St × (Rʰ × Rʰ) → ℚ)
           → E (askB (t , m , f) x) G
             ≡ E (fetchT id t x)
                 (λ u → E (uniform-Vec k) (λ ρ → G (outAskB m f x u ρ)))
  ask-redᴮ t m f x = E-bind₂ (fetchT id t x) (uniform-Vec k) (outAskB m f x)

  lift-E : (f : Bool) (μ : Dist-ℚ (StLʰ × Rʰ)) (p : St × (Rʰ × Rʰ) → St × Rʰ)
           (F : St × Rʰ → ℚ) (F′ : StLʰ × Rʰ → ℚ)
         → (∀ w → F (p (liftʰ f w)) ≡ F′ w) → E (Dmap p (Dmap (liftʰ f) μ)) F ≡ E μ F′
  lift-E f μ p F F′ h = trans (lookupᴰℚ-Dmap p (Dmap (liftʰ f) μ) F)
    (trans (lookupᴰℚ-Dmap (liftʰ f) μ (F ∘′ p)) (lookupᴰℚ-cong-P (entries μ) h))

  fI-lift : (f : Bool) (w : StLʰ × Rʰ) → C.fI (liftʰ f w) ≡ C.fR (liftʰ f w)
  fI-lift f w = cong (proj₁ (liftʰ f w) ,_) (cond-diag f (proj₂ w))

  collapseᴵ : (g h : Bool) (a d : Dig)
            → cond (g ∨ h) (ansRʰ d) (ansRʰ (cond h a d)) ≡ ansRʰ d
  collapseᴵ true  _     _ _ = refl
  collapseᴵ false true  _ _ = refl
  collapseᴵ false false _ _ = refl

_≋_ : St → StLʰ → Set
s ≋ s′ = eraseʰ s ≡ s′

stepL : StepBisim C.realK respLʰ _≋_
stepL (t , m , f) _ refl (askQʰ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (askB (t , m , f) x) F)
 (trans (ask-redᴮ t m f x (λ w → F (C.fR w)))
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u →
          lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ → pt _ _ refl refl)))
        (sym (ask-redᴸ t m x F′))))
stepL (t , m , f) _ refl (comQʰ b) F F′ pt =
  lift-E f (comL (t , m) b) C.fR F F′ (λ _ → pt _ _ refl refl)
stepL (t , m , f) _ refl opnQʰ F F′ pt =
  lift-E f (opnL (t , m)) C.fR F F′ (λ _ → pt _ _ refl refl)

stepI : StepBisim C.idealK respIʰ _≋_
stepI (t , m , f) _ refl (askQʰ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (askB (t , m , f) x) F)
 (trans (ask-redᴮ t m f x (λ w → F (C.fI w)))
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u → trans
          (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ → trans
            (cong (λ z → F ((proj₁ u , m , f ∨ hitAt m x ρ) , z))
                  (collapseᴵ f (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u)))
            (pt _ _ refl refl)))
          (E-const (uniform-Vec k) (F′ (outAskI m u)))))
        (sym (lookupᴰℚ-Dmap (outAskI m) (fetchT id t x) F′))))
stepI (t , m , f) _ refl (comQʰ b) F F′ pt = lift-E f (comL (t , m) b) C.fI F F′ λ w →
  trans (cong F (fI-lift f w)) (pt _ _ refl refl)
stepI (t , m , f) _ refl opnQʰ F F′ pt = lift-E f (opnL (t , m)) C.fI F F′ λ w →
  trans (cong F (fI-lift f w)) (pt _ _ refl refl)

------------------------------------------------------------------------
-- The potential: the flag rises by 2⁻ᵏ per query

hit-drift : (m : Comʰ) (g : Bool) (x : Pt)
          → E (uniform-Vec k) (λ ρ → bool→ℚ (g ∨ hitAt m x ρ)) ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
hit-drift (just (_ , b , false)) g x = drift-∧ k g ⌊ head x ≟ b ⌋ (tail x)
hit-drift (just (_ , _ , true))  g x = drift-∧ k g false (tail x)
hit-drift nothing                g x = drift-∧ k g false (tail x)

private
  hitP : St × Rʰ → ℚ
  hitP sr = bool→ℚ (hitOf (proj₁ sr))

  lift-flag : (f : Bool) (μ : Dist-ℚ (StLʰ × Rʰ))
            → E (Dmap C.fR (Dmap (liftʰ f) μ)) hitP ≡ bool→ℚ f
  lift-flag f μ = trans (lift-E f μ C.fR hitP (λ _ → bool→ℚ f) (λ _ → refl)) (E-const μ (bool→ℚ f))

rare-raise : RareRaise C.realK hitOf (inv-pow-2 k)
rare-raise (t , m , f) (askQʰ x) = ≤-trans
  (≤-reflexive (trans (lookupᴰℚ-Dmap C.fR (askB (t , m , f) x) hitP)
                      (ask-redᴮ t m f x (λ w → hitP (C.fR w)))))
  (≤-trans (E-mono (fetchT id t x)
             (λ u → E (uniform-Vec k) (λ ρ → hitP (C.fR (outAskB m f x u ρ))))
             (λ _ → bool→ℚ f +ℚ inv-pow-2 k) (λ u → hit-drift m f x))
           (≤-reflexive (E-const (fetchT id t x) (bool→ℚ f +ℚ inv-pow-2 k))))
rare-raise (t , m , f) (comQʰ b) = ≤-trans (≤-reflexive (lift-flag f (comL (t , m) b))) (0≤drift k f)
rare-raise (t , m , f) opnQʰ     = ≤-trans (≤-reflexive (lift-flag f (opnL (t , m)))) (0≤drift k f)

------------------------------------------------------------------------
-- The bound

εᴸ : ℕ → ℚ
εᴸ m = fromℕ m *ℚ inv-pow-2 k

cert : SuperCert C.realK hitOf s₀ εᴸ
cert = rare-cert C.realK hitOf s₀ (inv-pow-2 k) (0≤inv-pow-2 k) refl rare-raise

hiding-bound : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respLʰ sL₀ d) ∣ℚ ≤ℚ εᴸ m
hiding-bound = hop-bound hitOf respBʰ respLʰ respIʰ s₀ sL₀ sI₀
  (λ d → runWith-bisim C.realK respLʰ _≋_ stepL d s₀ sL₀ refl)
  (λ d → runWith-bisim C.idealK respIʰ _≋_ stepI d s₀ sI₀ refl)
  cert

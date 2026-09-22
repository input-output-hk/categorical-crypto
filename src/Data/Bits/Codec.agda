{-# OPTIONS --safe --without-K #-}

-- Self-delimiting encodings into `List Bool`, closed under products, lists
-- and fixed-width vectors.
--
-- A `Codec` carries a decoder that consumes a PREFIX and hands back the
-- unread remainder, together with `decode (encode x ++ r) ≡ just (x , r)`.
-- That law is what makes concatenation unambiguous: the boundary between two
-- encodings is found by the first decoder, so `×-codec` needs no separator
-- and `encode-injective` is one `cong`.
--
-- `ℕ` is encoded in unary (`n` ones then a zero).  A binary encoding would
-- need its own length prefix and a bits/number round-trip proof; the example
-- this serves (`CategoricalCrypto.Examples.ChimericLedger.Serialize`) only
-- needs injectivity, never compactness.

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _>>=_)
  renaming (map to mapᵐ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; map₁)
open import Data.Vec.Base using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality

module Data.Bits.Codec where

private variable
  a b : Level
  A : Set a
  B : Set b
  m : ℕ

record Codec (A : Set a) : Set a where
  field
    encode : A → List Bool
    decode : List Bool → Maybe (A × List Bool)
    decode-encode : (x : A) (r : List Bool)
                  → decode (encode x ++ r) ≡ just (x , r)

  encode-injective : {x y : A} → encode x ≡ encode y → x ≡ y
  encode-injective {x} {y} eq = cong (maybe′ proj₁ x) (begin
    just (x , [])            ≡⟨ decode-encode x [] ⟨
    decode (encode x ++ [])  ≡⟨ cong decode (++-identityʳ (encode x)) ⟩
    decode (encode x)        ≡⟨ cong decode eq ⟩
    decode (encode y)        ≡⟨ cong decode (++-identityʳ (encode y)) ⟨
    decode (encode y ++ [])  ≡⟨ decode-encode y [] ⟩
    just (y , [])            ∎)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- The codecs
------------------------------------------------------------------------

bool-codec : Codec Bool
bool-codec = record
  { encode = _∷ []
  ; decode = λ { [] → nothing ; (c ∷ r) → just (c , r) }
  ; decode-encode = λ _ _ → refl }

ℕ-codec : Codec ℕ
ℕ-codec = record { encode = enc ; decode = dec ; decode-encode = law }
  where
  enc : ℕ → List Bool
  enc zero    = false ∷ []
  enc (suc x) = true ∷ enc x

  dec : List Bool → Maybe (ℕ × List Bool)
  dec []          = nothing
  dec (false ∷ r) = just (0 , r)
  dec (true ∷ bs) = mapᵐ (map₁ suc) (dec bs)

  law : (x : ℕ) (r : List Bool) → dec (enc x ++ r) ≡ just (x , r)
  law zero    r = refl
  law (suc x) r = cong (mapᵐ (map₁ suc)) (law x r)

×-codec : Codec A → Codec B → Codec (A × B)
×-codec {A = A} {B = B} C D =
  record { encode = enc ; decode = dec ; decode-encode = law }
  where
  module C = Codec C
  module D = Codec D

  enc : A × B → List Bool
  enc (x , y) = C.encode x ++ D.encode y

  dec : List Bool → Maybe ((A × B) × List Bool)
  dec bs = C.decode bs >>= λ (x , r) → mapᵐ (map₁ (x ,_)) (D.decode r)

  law : (p : A × B) (r : List Bool) → dec (enc p ++ r) ≡ just (p , r)
  law (x , y) r rewrite ++-assoc (C.encode x) (D.encode y) r
                      | C.decode-encode x (D.encode y ++ r)
                      | D.decode-encode y r = refl

-- Length-prefixed: the count is what the decoder recurses on, so the
-- element decoder may consume any number of bits.
list-codec : Codec A → Codec (List A)
list-codec {A = A} C =
  record { encode = enc ; decode = dec ; decode-encode = law }
  where
  module C = Codec C
  module N = Codec ℕ-codec

  encs : List A → List Bool
  encs []       = []
  encs (x ∷ xs) = C.encode x ++ encs xs

  decs : (k : ℕ) → List Bool → Maybe (List A × List Bool)
  decs zero    bs = just ([] , bs)
  decs (suc k) bs = C.decode bs >>= λ (x , r) → mapᵐ (map₁ (x ∷_)) (decs k r)

  encs-law : (xs : List A) (r : List Bool)
           → decs (length xs) (encs xs ++ r) ≡ just (xs , r)
  encs-law []       r = refl
  encs-law (x ∷ xs) r rewrite ++-assoc (C.encode x) (encs xs) r
                            | C.decode-encode x (encs xs ++ r)
                            | encs-law xs r = refl

  enc : List A → List Bool
  enc xs = N.encode (length xs) ++ encs xs

  dec : List Bool → Maybe (List A × List Bool)
  dec bs = N.decode bs >>= λ (k , r) → decs k r

  law : (xs : List A) (r : List Bool) → dec (enc xs ++ r) ≡ just (xs , r)
  law xs r rewrite ++-assoc (N.encode (length xs)) (encs xs) r
                 | N.decode-encode (length xs) (encs xs ++ r)
                 | encs-law xs r = refl

-- The width is already known to both sides, so no prefix is written.
vec-codec : Codec A → (n : ℕ) → Codec (Vec A n)
vec-codec {A = A} C n =
  record { encode = enc ; decode = dec n ; decode-encode = law }
  where
  module C = Codec C

  enc : Vec A m → List Bool
  enc []ᵛ       = []
  enc (x ∷ᵛ xs) = C.encode x ++ enc xs

  dec : (k : ℕ) → List Bool → Maybe (Vec A k × List Bool)
  dec zero    bs = just ([]ᵛ , bs)
  dec (suc k) bs = C.decode bs >>= λ (x , r) → mapᵐ (map₁ (x ∷ᵛ_)) (dec k r)

  law : (xs : Vec A m) (r : List Bool) → dec m (enc xs ++ r) ≡ just (xs , r)
  law []ᵛ       r = refl
  law (x ∷ᵛ xs) r rewrite ++-assoc (C.encode x) (enc xs) r
                        | C.decode-encode x (enc xs ++ r)
                        | law xs r = refl

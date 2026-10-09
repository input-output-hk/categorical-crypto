{-# OPTIONS --safe --without-K #-}

-- Interactive Turing machines between port interfaces, and the free monoidal
-- category `𝕋ᴹ` they generate (`docs/uc-setup-itm.md` §3).
--
-- A port interface is a TREE of bitstring ports, read as an `Iface` polarity
-- by polarity (`⁺` answers out to the caller, `⁻` takes queries in).  Read as
-- a tree, `⟦ A ⊗₀ B ⟧` is `⟦ A ⟧ ⊗ᴵ ⟦ B ⟧` on the nose, which is what keeps the
-- interpretation functor strict (`ITM.Functor`); `⟦ unit ⟧` is empty at
-- `Data.Empty.Polymorphic`'s `⊥` because that is the sealed bundle's unit
-- (`UC.Model.Seal.unitᵒ`).
--
-- A machine is a finite table over one work tape, a read-once input tape
-- holding the activation's message, one fair coin per `flip` and an output
-- buffer; `send` ends the activation, and the control state and work tape
-- survive it (`Mem`, [Can20 Def 4–5]).  Composition and tensor are the free
-- category's constructors, so a system is a term and never a product table.

module CategoricalCrypto.ITM.Core where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal

open import Data.Bool.Base
open import Data.Empty
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥ₚ)
open import Data.Fin.Base
open import Data.List.Base as List
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface

------------------------------------------------------------------------
-- Port interfaces
------------------------------------------------------------------------

data Pol : Set where ⁺ ⁻ : Pol

open FreeMonoidalHelper Mon Pol

Ports Bits : Set
Ports = ObjTerm
Bits  = List Bool

Port : Pol → Ports → Set
Port p unit     = ⊥
Port p (A ⊗₀ B) = Port p A ⊎ Port p B
Port ⁺ (Var ⁺)  = ⊤
Port ⁺ (Var ⁻)  = ⊥
Port ⁻ (Var ⁺)  = ⊥
Port ⁻ (Var ⁻)  = ⊤

Msg : Pol → Ports → Set
Msg p unit     = ⊥ₚ
Msg p (A ⊗₀ B) = Msg p A ⊎ Msg p B
Msg ⁺ (Var ⁺)  = Bits
Msg ⁺ (Var ⁻)  = ⊥ₚ
Msg ⁻ (Var ⁺)  = ⊥ₚ
Msg ⁻ (Var ⁻)  = Bits

⟦_⟧ : Ports → Iface
⟦ A ⟧ = Msg ⁺ A ⇿ Msg ⁻ A

decode : (p : Pol) (A : Ports) → Msg p A → Port p A × Bits
decode _ unit     (lift ())
decode p (A ⊗₀ B) (inj₁ m) = map₁ inj₁ (decode p A m)
decode p (A ⊗₀ B) (inj₂ m) = map₁ inj₂ (decode p B m)
decode ⁺ (Var ⁺)  w        = tt , w
decode ⁺ (Var ⁻)  (lift ())
decode ⁻ (Var ⁺)  (lift ())
decode ⁻ (Var ⁻)  w        = tt , w

encode : (p : Pol) (A : Ports) → Port p A × Bits → Msg p A
encode _ unit     (() , _)
encode p (A ⊗₀ B) (inj₁ i , w) = inj₁ (encode p A (i , w))
encode p (A ⊗₀ B) (inj₂ i , w) = inj₂ (encode p B (i , w))
encode ⁺ (Var ⁺)  (_ , w)      = w
encode ⁺ (Var ⁻)  (() , _)
encode ⁻ (Var ⁺)  (() , _)
encode ⁻ (Var ⁻)  (_ , w)      = w

decode-encode : (p : Pol) (A : Ports) (x : Port p A × Bits) → decode p A (encode p A x) ≡ x
decode-encode _ unit     (() , _)
decode-encode p (A ⊗₀ B) (inj₁ i , w) = cong (map₁ inj₁) (decode-encode p A (i , w))
decode-encode p (A ⊗₀ B) (inj₂ i , w) = cong (map₁ inj₂) (decode-encode p B (i , w))
decode-encode ⁺ (Var ⁺)  _            = refl
decode-encode ⁺ (Var ⁻)  (() , _)
decode-encode ⁻ (Var ⁺)  (() , _)
decode-encode ⁻ (Var ⁻)  _            = refl

encode-decode : (p : Pol) (A : Ports) (m : Msg p A) → encode p A (decode p A m) ≡ m
encode-decode _ unit     (lift ())
encode-decode p (A ⊗₀ B) (inj₁ m) = cong inj₁ (encode-decode p A m)
encode-decode p (A ⊗₀ B) (inj₂ m) = cong inj₂ (encode-decode p B m)
encode-decode ⁺ (Var ⁺)  _        = refl
encode-decode ⁺ (Var ⁻)  (lift ())
encode-decode ⁻ (Var ⁺)  (lift ())
encode-decode ⁻ (Var ⁻)  _        = refl

-- A hom `A ⇒ B` reads `Pos A ⊎ Neg B` and writes `Neg A ⊎ Pos B`
-- (`UC.Machine.Proc`).
In Out : Ports → Ports → Set
In  A B = Port ⁺ A ⊎ Port ⁻ B
Out A B = Port ⁻ A ⊎ Port ⁺ B

decodeᴵ : (A B : Ports) → Pos ⟦ A ⟧ ⊎ Neg ⟦ B ⟧ → In A B × Bits
decodeᴵ A B (inj₁ m) = map₁ inj₁ (decode ⁺ A m)
decodeᴵ A B (inj₂ m) = map₁ inj₂ (decode ⁻ B m)

encodeᴼ : (A B : Ports) → Out A B × Bits → Neg ⟦ A ⟧ ⊎ Pos ⟦ B ⟧
encodeᴼ A B (inj₁ o , w) = inj₁ (encode ⁻ A (o , w))
encodeᴼ A B (inj₂ o , w) = inj₂ (encode ⁺ B (o , w))

ports : ℕ → ℕ → Ports
ports n m = wires (replicate n ⁺) ⊗₀ wires (replicate m ⁻)

------------------------------------------------------------------------
-- Machines
------------------------------------------------------------------------

data Sym : Set where ␣ 𝟎 𝟏 : Sym

data Move : Set where ◁ ▷ ∙ : Move

infix 4.5 _‹_›_

-- `left` is stored nearest-first; both ends are blank beyond the lists.
record Tape : Set where
  constructor _‹_›_
  field left  : List Sym
        here  : Sym
        right : List Sym

bit : Bool → Sym
bit b = if b then 𝟏 else 𝟎

tape : Bits → Tape
tape []       = [] ‹ ␣ › []
tape (b ∷ bs) = [] ‹ bit b › List.map bit bs

move : Move → Tape → Tape
move ◁ ([]    ‹ h › r) = [] ‹ ␣ › h ∷ r
move ◁ (x ∷ l ‹ h › r) = l ‹ x › h ∷ r
move ▷ (l ‹ h › [])    = h ∷ l ‹ ␣ › []
move ▷ (l ‹ h › x ∷ r) = h ∷ l ‹ x › r
move ∙ t               = t

data Instr (Q O : Set) : Set where
  run  : (q : Q) (w : Sym) (mʷ mⁱ : Move) (b : Maybe Bool) → Instr Q O
  flip : (q₀ q₁ : Q) → Instr Q O
  send : (o : O) (q : Q) → Instr Q O

record TM (I O : Set) : Set where
  field #Q    : ℕ
        start : Fin #Q
        δ     : Fin #Q → I → Sym → Sym → Instr (Fin #Q) O

Gen : Ports → Ports → Set
Gen A B = TM (In A B) (Out A B)

module _ {I O : Set} (M : TM I O) where
  open TM M

  Mem : Set
  Mem = Fin #Q × Tape

  blank : Mem
  blank = start , [] ‹ ␣ › []

  record Conf : Set where
    field state : Fin #Q
          work  : Tape
          port  : I
          input : Tape
          buf   : List Bool

  open Conf

  δ-at : Conf → Instr (Fin #Q) O
  δ-at c = δ (state c) (port c) (Tape.here (work c)) (Tape.here (input c))

  load : Mem → I × Bits → Conf
  load (q , t) (i , w) = record { state = q ; work = t ; port = i ; input = tape w ; buf = [] }

  exec : Fin #Q → Sym → Move → Move → Maybe Bool → Conf → Conf
  exec q w mʷ mⁱ b c = record c
    { state = q ; work = move mʷ (record (work c) { here = w })
    ; input = move mⁱ (input c) ; buf = maybe′ (_∷ buf c) (buf c) b }

  goto : Fin #Q → Conf → Conf
  goto q c = record c { state = q }

------------------------------------------------------------------------
-- The free monoidal category of systems
------------------------------------------------------------------------

itmData : FreeMonoidalData
itmData = record { v = Mon ; X = Pol ; mor = Gen }

𝕋ᴹ : MonoidalCategory 0ℓ 0ℓ 0ℓ
𝕋ᴹ = FreeMonoidal.FMC itmData

/-
Copyright (c) 2023 François G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

/-
  ## UInt8 -- Unsigned 8-bit integers
-/

namespace UInt8

instance : Neg UInt8 where
  neg x := 0 - x

/-- Attempt to convert `Nat` to `UInt8`.

  `ofNat? x` succeeds if `x < 2^8`.
-/
@[inline]
def ofNat? (n : Nat) : Option UInt8 :=
  if h : n < UInt8.size then some ⟨n, h⟩ else none

/-- Attempt to convert `Nat` to `UInt8`.

  `ofNat! x` panics if `x ≥ 2^8`.
-/
@[inline]
def ofNat! (n : Nat) : UInt8 :=
  match ofNat? n with
  | some x => x
  | none => panic! "integer out of range"

/-- Natural left shift.

  The result of `shiftRightNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftRight x n`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 15)) ? #1 << lean_unbox(#2) : UINT8_C(0))"]
def shiftLeftNat : UInt8 → @& Nat → UInt8
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft UInt8 Nat UInt8 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times.
  Note that this is not the same as `shiftRight x n`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 15)) ? #1 >> lean_unbox(#2) : UINT8_C(0))"]
def shiftRightNat : UInt8 → @& Nat → UInt8
| x, 0 => x
| x, n+1 => shiftRightNat (x / 2) n

instance : HShiftRight UInt8 Nat UInt8 where
  hShiftRight := shiftRightNat

end UInt8

/-
  ## UInt16 -- Unsigned 16-bit integers
-/

namespace UInt16

instance : Neg UInt16 where
  neg x := 0 - x

/-- Attempt to convert `Nat` to `UInt16`.

  `ofNat? x` succeeds if `x < 2^16`.
-/
@[inline]
def ofNat? (n : Nat) : Option UInt16 :=
  if h : n < UInt16.size then some ⟨n, h⟩ else none

/-- Attempt to convert `Nat` to `UInt16`.

  `ofNat! x` panics if `x ≥ 2^16`.
-/
@[inline]
def ofNat! (n : Nat) : UInt16 :=
  match ofNat? n with
  | some x => x
  | none => panic! "integer out of range"

/-- Reverse byte order.

  Used to convert between big endian and little endian.
-/
@[inline]
def byteswap (x : UInt16) : UInt16 :=
  (x <<< 8) ||| (x >>> 8)

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 31) ? #1 << lean_unbox(#2) : UINT16_C(0)))"]
def shiftLeftNat : UInt16 → @& Nat → UInt16
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft UInt16 Nat UInt16 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times.
  Note that this is not the same as `shiftRight x n`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 31) ? #1 >> lean_unbox(#2) : UINT16_C(0)))"]
def shiftRightNat : UInt16 → @& Nat → UInt16
| x, 0 => x
| x, n+1 => shiftRightNat (x / 2) n

instance : HShiftRight UInt16 Nat UInt16 where
  hShiftRight := shiftRightNat

end UInt16

/-
  ## UInt32 -- Unsigned 32-bit integers
-/

namespace UInt32

instance : Neg UInt32 where
  neg x := 0 - x

/-- Attempt to convert `Nat` to `UInt32`.

  `ofNat? x` succeeds if `x < 2^32`.
-/
@[inline]
def ofNat? (n : Nat) : Option UInt32 :=
  if h : n < UInt32.size then some ⟨n, h⟩ else none

/-- Attempt to convert `Nat` to `UInt32`.

  `ofNat! x` panics if `x ≥ 2^32`.
-/
@[inline]
def ofNat! (n : Nat) : UInt32 :=
  match ofNat? n with
  | some x => x
  | none => panic! "integer out of range"

/-- Reverse byte order.

  Used to convert between big endian and little endian.
-/
@[inline]
def byteswap (x : UInt32) : UInt32 :=
  let x := ((x &&& 0x00ff00ff) <<< 8) ||| ((x &&& 0xff00ff00) >>> 8)
  (x <<< 16) ||| (x >>> 16)

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/

@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 63)) ? #1 << lean_unbox(#2) : UINT32_C(0))"]
def shiftLeftNat : UInt32 → @& Nat → UInt32
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft UInt32 Nat UInt32 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times.
  Note that this is not the same as `shiftRight`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 63))) ? #1 >> lean_unbox(#2) : UINT32_C(0)"]
def shiftRightNat : UInt32 → @& Nat → UInt32
| x, 0 => x
| x, n+1 => shiftRightNat (x / 2) n

instance : HShiftRight UInt32 Nat UInt32 where
  hShiftRight := shiftRightNat

end UInt32

/-
  ## UInt64 -- Unsigned 64-bit integers
-/

namespace UInt64

instance : Neg UInt64 where
  neg x := 0 - x

/-- Attempt to convert `Nat` to `UInt64`.

  `ofNat? x` succeeds if `x < 2^64`.
-/
@[inline]
def ofNat? (n : Nat) : Option UInt64 :=
  if h : n < UInt64.size then some ⟨n, h⟩ else none

/-- Attempt to convert `Nat` to `UInt64`.

  `ofNat! x` panics if `x ≥ 2^64`.
-/
@[inline]
def ofNat! (n : Nat) : UInt64 :=
  match ofNat? n with
  | some x => x
  | none => panic! "integer out of range"

/-- Reverse byte order.

  Used to convert between big endian and little endian.
-/
@[inline]
def byteswap (x : UInt64) : UInt64 :=
  let x := ((x &&& 0x00ff00ff00ff00ff) <<< 8) ||| ((x &&& 0xff00ff00ff00ff00) >>> 8)
  let x := ((x &&& 0x0000ffff0000ffff) <<< 16) ||| ((x &&& 0xffff0000ffff0000) >>> 16)
  (x <<< 32) ||| (x >>> 32)

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 127)) ? #1 << lean_unbox(#2) : UINT64_C(0))"]
def shiftLeftNat : UInt64 → @& Nat → UInt64
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft UInt64 Nat UInt64 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times.
  Note that this is not the same as `shiftRight`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 127)) ? #1 >> lean_unbox(#2) : UINT64_C(0))"]
def shiftRightNat : UInt64 → @& Nat → UInt64
| x, 0 => x
| x, n+1 => shiftRightNat (x / 2) n

instance : HShiftRight UInt64 Nat UInt64 where
  hShiftRight := shiftRightNat

end UInt64

/-
  ## Int8 -- Signed 8-bit integers
-/

/-- The type of signed 8-bit integers.
  This type has special support in the compiler to make it actually 8 bits rather than wrapping an `Int`. -/
structure Int8 extends UInt8
deriving Inhabited, BEq, Repr

instance (n : Nat) [OfNat UInt8 n] : OfNat Int8 n where
  ofNat := ⟨OfNat.ofNat n⟩

/-- Cast `UInt8` to `Int8` -/
abbrev UInt8.toInt8 := Int8.mk

namespace Int8

private def signBit : UInt8 := 0x80

/-- Maximum `Int8` value: `2^7-1`. -/
protected def max : Int8 := ⟨~~~signBit⟩

/-- Minimum `Int8` value: `-2^7`. -/
protected def min : Int8 := ⟨signBit⟩

/-- Test if zero. -/
@[inline, extern c inline "(bool)((int8_t)#1 == INT8_C(0))"]
def isZero : Int8 → Bool
| ⟨x⟩ => x == 0

/-- Test if negative using the sign bit. -/
@[inline, extern c inline "(bool)((int8_t)#1 < INT8_C(0))"]
def isNeg : Int8 → Bool
| ⟨x⟩ => x &&& signBit != 0

/-- Cast `Int8` to `Int`. -/
def toInt (x : Int8) : Int :=
  bif x.isNeg then
    -(-x.toUInt8).toNat
  else
    x.toUInt8.toNat

instance : ToString Int8 where
  toString x := toString (toInt x)

/-- Attempt to convert from `Int` to `Int8`.

  `ofInt? x` succeeds if `-2^7 ≤ x < 2^7`.
-/
def ofInt? : Int → Option Int8
| .ofNat x => bif x ≤ 0x7f then some ⟨x.toUInt8⟩ else none
| .negSucc x => bif x ≤ 0x7f then some ⟨~~~x.toUInt8⟩ else none

/-- Attempt to convert from `Int` to `Int8`.

  `ofInt! x` panics if `-2^7 > x` or `x ≥ 2^7`.
-/
def ofInt! (x : Int) : Int8 :=
  match ofInt? x with
  | some x => x
  | none => panic! "integer out of range"

/-- Cast `Int` to `Int8`. -/
def _root_.Int.toInt8 (x : Int) : Int8 :=
  match Int8.ofInt? x with
  | some x => x
  | none => default

/-- Boolean less than or equal comparison. -/
@[inline, extern c inline "(bool)((int8_t)#1 <= (int8_t)#2)"]
def ble : Int8 → Int8 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit ≤ y + signBit

instance : LE Int8 where
  le x y := ble x y = true

instance (x y : Int8) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ = true))

/-- Boolean less than comparison. -/
@[inline, extern c inline "(bool)((int8_t)#1 <= (int8_t)#2)"]
def blt : Int8 → Int8 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit < y + signBit

instance : LT Int8 where
  lt x y := blt x y = true

instance (x y : Int8) : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ = true))

instance : Neg Int8 where
  neg | ⟨x⟩ => ⟨-x⟩

instance : Add Int8 where
  add | ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

instance : Sub Int8 where
  sub | ⟨x⟩, ⟨y⟩ => ⟨x - y⟩

instance : Mul Int8 where
  mul | ⟨x⟩, ⟨y⟩ => ⟨x * y⟩

instance : Complement Int8 where
  complement | ⟨x⟩ => ⟨~~~x⟩

instance : AndOp Int8 where
  and | ⟨x⟩, ⟨y⟩ => ⟨x &&& y⟩

instance : OrOp Int8 where
  or | ⟨x⟩, ⟨y⟩ => ⟨x ||| y⟩

instance : Xor Int8 where
  xor | ⟨x⟩, ⟨y⟩ => ⟨x ^^^ y⟩

@[inline, extern c inline "(int8_t)#1 / (int8_t)#2"]
private def divAux (x y : Int8) : Int8 := (Int.div x.toInt y.toInt).toInt8

@[inline, extern c inline "(int8_t)#1 % (int8_t)#2"]
private def modAux (x y : Int8) : Int8 := (Int.mod x.toInt y.toInt).toInt8

/-- Truncated division.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def div (x y : Int8) : Int8 := bif y.isZero then 0 else divAux x y

/-- Truncated remainder.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def mod (x y : Int8) : Int8 := bif y.isZero then x else modAux x y

/-- Euclidean division.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def ediv (x y : Int8) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        divAux x y + 1
      else
        divAux x y - 1
    else
      divAux x y

/-- Euclidean remainder.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def emod (x y : Int8) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        modAux x y - y
      else
        modAux x y + y
    else
      modAux x y

/-- Flooring division.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fdiv (x y : Int8) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        divAux x y
      else
        divAux x y - 1
    else
      divAux x y

/-- Flooring remainder.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fmod (x y : Int8) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        modAux x y
      else
        modAux x y + y
    else
      modAux x y

instance : Div Int8 where
  div := Int8.div

instance : Mod Int8 where
  mod := Int8.mod

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 15)) ? (int8_t)#1 << (uint8_t)lean_unbox(#2) : INT8_C(0))"]
def shiftLeftNat : Int8 → @& Nat → Int8
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft Int8 Nat Int8 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times,
  rounding to negative infinity (flooring division). Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 15)) ? (int8_t)#1 >> (uint8_t)lean_unbox(#2) : INT8_C(0))"]
def shiftRightNat : Int8 → @& Nat → Int8
| x, 0 => x
| x, n+1 => shiftRightNat (fdiv x 2) n

instance : HShiftRight Int8 Nat Int8 where
  hShiftRight := shiftRightNat

/-- Left shift.

  `shiftLeft x n` first calculates `n % 8` to obtain an integer from 0 to 7. The bits of `x` are
  then shifted left (toward the most significant bit) by this amount, filling in with zero bits.
-/
@[inline, extern c inline "(int8_t)#1 << ((uint8_t)#2 & UINT8_C(7))"]
def shiftLeft (x y : Int8) : Int8 :=
  shiftLeftNat x (y &&& 7).toNat

instance : ShiftLeft Int8 where
  shiftLeft := shiftLeft

/-- Right shift.

  `shiftRight x n` first calculates `n % 8` to obtain an integer from 0 to 7. The bits of `x` are
  then shifted right (toward the least significant bit) by this amount, filling in with sign bits.
-/
@[inline, extern c inline "(int8_t)#1 >> ((uint8_t)#2 & UINT8_C(7))"]
def shiftRight (x y : Int8) : Int8 :=
  shiftRightNat x (y &&& 7).toNat

instance : ShiftRight Int8 where
  shiftRight := shiftRight

end Int8

/-
  ## Int16 -- Signed 16-bit integers
-/

/-- The type of signed 16-bit integers.

  This type has special support in the compiler to make it actually 8 bits rather than wrapping an `Int`. -/
structure Int16 extends UInt16
deriving Inhabited, BEq, Repr

instance (n : Nat) [OfNat UInt16 n] : OfNat Int16 n where
  ofNat := ⟨OfNat.ofNat n⟩

/-- Cast `UInt16` to `Int16`. -/
abbrev UInt16.toInt16 := Int16.mk

namespace Int16

private def signBit : UInt16 := 0x8000

/-- Maximum `Int16` value: `2^15-1`. -/
protected def max : Int16 := ⟨~~~signBit⟩

/-- Minimum `Int16` value: `-2^15`. -/
protected def min : Int16 := ⟨signBit⟩

/-- Test if zero. -/
@[inline, extern c inline "(bool)((int16_t)#1 == INT16_C(0))"]
def isZero : Int16 → Bool
| ⟨x⟩ => x == 0

/-- Test if negative using the sign bit. -/
@[inline, extern c inline "(bool)((int16_t)#1 < INT16_C(0))"]
def isNeg : Int16 → Bool
| ⟨x⟩ => x &&& signBit != 0

/-- Cast `Int16` to `Int`. -/
def toInt (x : Int16) : Int :=
  bif x.isNeg then
    -(-x.toUInt16).toNat
  else
    x.toUInt16.toNat

instance : ToString Int16 where
  toString x := toString (toInt x)

/-- Attempt to convert from `Int` to `Int16`.

  `ofInt? x` succeeds if `-2^15 ≤ x < 2^15`.
-/
def ofInt? : Int → Option Int16
| .ofNat x => bif x ≤ 0x7f then some ⟨x.toUInt16⟩ else none
| .negSucc x => bif x ≤ 0x7f then some ⟨~~~x.toUInt16⟩ else none

/-- Attempt to convert from `Int` to `Int16`.

  `ofInt! x` succeeds if `-2^15 > x` or `x ≥ 2^15`.
-/
def ofInt! (x : Int) : Int16 :=
  match ofInt? x with
  | some x => x
  | none => panic! "integer out of range"

/-- Cast `Int` to `Int16`. -/
def _root_.Int.toInt16 (x : Int) : Int16 :=
  match Int16.ofInt? x with
  | some x => x
  | none => default

/-- Boolean less than or equal comparison. -/
@[inline, extern c inline "(bool)((int16_t)#1 <= (int16_t)#2)"]
def ble : Int16 → Int16 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit ≤ y + signBit

instance : LE Int16 where
  le x y := ble x y = true

instance (x y : Int16) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ = true))

/-- Boolean less than comparison. -/
@[inline, extern c inline "(bool)((int16_t)#1 <= (int16_t)#2)"]
def blt : Int16 → Int16 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit < y + signBit

instance : LT Int16 where
  lt x y := blt x y = true

instance (x y : Int16) : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ = true))

instance : Neg Int16 where
  neg | ⟨x⟩ => ⟨-x⟩

instance : Add Int16 where
  add | ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

instance : Sub Int16 where
  sub | ⟨x⟩, ⟨y⟩ => ⟨x - y⟩

instance : Mul Int16 where
  mul | ⟨x⟩, ⟨y⟩ => ⟨x * y⟩

instance : Complement Int16 where
  complement | ⟨x⟩ => ⟨~~~x⟩

instance : AndOp Int16 where
  and | ⟨x⟩, ⟨y⟩ => ⟨x &&& y⟩

instance : OrOp Int16 where
  or | ⟨x⟩, ⟨y⟩ => ⟨x ||| y⟩

instance : Xor Int16 where
  xor | ⟨x⟩, ⟨y⟩ => ⟨x ^^^ y⟩

@[inline, extern c inline "(int16_t)#1 / (int16_t)#2"]
private def divAux (x y : Int16) : Int16 := (Int.div x.toInt y.toInt).toInt16

@[inline, extern c inline "(int16_t)#1 % (int16_t)#2"]
private def modAux (x y : Int16) : Int16 := (Int.mod x.toInt y.toInt).toInt16

/-- Truncated division.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def div (x y : Int16) : Int16 := bif y.isZero then 0 else divAux x y

/-- Truncated remainder.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def mod (x y : Int16) : Int16 := bif y.isZero then x else modAux x y

/-- Euclidean division.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def ediv (x y : Int16) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        divAux x y + 1
      else
        divAux x y - 1
    else
      divAux x y

/-- Euclidean remainder.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def emod (x y : Int16) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        modAux x y - y
      else
        modAux x y + y
    else
      modAux x y

/-- Flooring division.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fdiv (x y : Int16) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        divAux x y
      else
        divAux x y - 1
    else
      divAux x y

/-- Flooring remainder.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fmod (x y : Int16) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        modAux x y
      else
        modAux x y + y
    else
      modAux x y

instance : Div Int16 where
  div := Int16.div

instance : Mod Int16 where
  mod := Int16.mod

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 31)) ? (int16_t)#1 << (uint16_t)lean_unbox(#2) : INT16_C(0))"]
def shiftLeftNat : Int16 → @& Nat → Int16
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft Int16 Nat Int16 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times,
  rounding to negative infinity (flooring division). Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 31)) ? (int16_t)#1 >> (uint16_t)lean_unbox(#2) : INT16_C(0))"]
def shiftRightNat : Int16 → @& Nat → Int16
| x, 0 => x
| x, n+1 => shiftRightNat (fdiv x 2) n

instance : HShiftRight Int16 Nat Int16 where
  hShiftRight := shiftRightNat

/-- Left shift.

  `shiftLeft x n` first calculates `n % 16` to obtain an integer from 0 to 15. The bits of `x` are
  then shifted left (toward the most significant bit) by this amount, filling in with zero bits.
-/
@[inline, extern c inline "(int16_t)#1 << ((uint16_t)#2 & UINT16_C(15))"]
def shiftLeft (x y : Int16) : Int16 :=
  shiftLeftNat x (y &&& 15).toNat

instance : ShiftLeft Int16 where
  shiftLeft := shiftLeft

/-- Right shift.

  `shiftRight x n` first calculates `n % 16` to obtain an integer from 0 to 15. The bits of `x` are
  then shifted right (toward the least significant bit) by this amount, filling in with sign bits.
-/
@[inline, extern c inline "(int16_t)#1 >> ((uint16_t)#2 & UINT16_C(15))"]
def shiftRight (x y : Int16) : Int16 :=
  shiftRightNat x (y &&& 15).toNat

instance : ShiftRight Int16 where
  shiftRight := shiftRight

end Int16

/-
  ## Int32 -- Signed 32-bit integers
-/

/-- The type of signed 32-bit integers.

  This type has special support in the compiler to make it actually 8 bits rather than wrapping an `Int`. -/
structure Int32 extends UInt32
deriving Inhabited, BEq, Repr

instance (n : Nat) [OfNat UInt32 n] : OfNat Int32 n where
  ofNat := ⟨OfNat.ofNat n⟩

/-- Cast `UInt32` to `Int32`. -/
abbrev UInt32.toInt32 := Int32.mk

namespace Int32

private def signBit : UInt32 := 0x80000000

/-- Maximum `Int32` value: `2^31-1`. -/
protected def max : Int32 := ⟨~~~signBit⟩

/-- Minimum `Int32` value: `-2^31`. -/
protected def min : Int32 := ⟨signBit⟩

/-- Test if zero. -/
@[inline, extern c inline "(bool)((int32_t)#1 == INT32_C(0))"]
def isZero : Int32 → Bool
| ⟨x⟩ => x == 0

/-- Test if negative using the sign bit. -/
@[inline, extern c inline "(bool)((int32_t)#1 < INT32_C(0))"]
def isNeg : Int32 → Bool
| ⟨x⟩ => x &&& signBit != 0

/-- Cast `Int32` to `Int`. -/
def toInt (x : Int32) : Int :=
  bif x.isNeg then
    -(-x.toUInt32).toNat
  else
    x.toUInt32.toNat

instance : ToString Int32 where
  toString x := toString (toInt x)

/-- Attempt to convert from `Int` to `Int32`.

  `ofInt? x` succeeds if `-2^31 ≤ x < 2^31`.
-/
def ofInt? : Int → Option Int32
| .ofNat x => bif x ≤ 0x7f then some ⟨x.toUInt32⟩ else none
| .negSucc x => bif x ≤ 0x7f then some ⟨~~~x.toUInt32⟩ else none

/-- Attempt to convert from `Int` to `Int32`.

  `ofInt! x` panics if `-2^31 > x` or `x ≥ 2^31`.
-/
def ofInt! (x : Int) : Int32 :=
  match ofInt? x with
  | some x => x
  | none => panic! "integer out of range"

/-- Cast `Int` to `Int32`. -/
def _root_.Int.toInt32 (x : Int) : Int32 :=
  match Int32.ofInt? x with
  | some x => x
  | none => default

/-- Boolean less than or equal comparison. -/
@[inline, extern c inline "(bool)((int32_t)#1 <= (int32_t)#2)"]
def ble : Int32 → Int32 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit ≤ y + signBit

instance : LE Int32 where
  le x y := ble x y = true

instance (x y : Int32) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ = true))

/-- Boolean less than comparison. -/
@[inline, extern c inline "(bool)((int32_t)#1 <= (int32_t)#2)"]
def blt : Int32 → Int32 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit < y + signBit

instance : LT Int32 where
  lt x y := blt x y = true

instance (x y : Int32) : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ = true))

instance : Neg Int32 where
  neg | ⟨x⟩ => ⟨-x⟩

instance : Add Int32 where
  add | ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

instance : Sub Int32 where
  sub | ⟨x⟩, ⟨y⟩ => ⟨x - y⟩

instance : Mul Int32 where
  mul | ⟨x⟩, ⟨y⟩ => ⟨x * y⟩

instance : Complement Int32 where
  complement | ⟨x⟩ => ⟨~~~x⟩

instance : AndOp Int32 where
  and | ⟨x⟩, ⟨y⟩ => ⟨x &&& y⟩

instance : OrOp Int32 where
  or | ⟨x⟩, ⟨y⟩ => ⟨x ||| y⟩

instance : Xor Int32 where
  xor | ⟨x⟩, ⟨y⟩ => ⟨x ^^^ y⟩

@[inline, extern c inline "(int32_t)#1 / (int32_t)#2"]
private def divAux (x y : Int32) : Int32 := (Int.div x.toInt y.toInt).toInt32

@[inline, extern c inline "(int32_t)#1 % (int32_t)#2"]
private def modAux (x y : Int32) : Int32 := (Int.mod x.toInt y.toInt).toInt32

/-- Truncated division.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def div (x y : Int32) : Int32 := bif y.isZero then 0 else divAux x y

/-- Truncated remainder.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def mod (x y : Int32) : Int32 := bif y.isZero then x else modAux x y

/-- Euclidean division.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def ediv (x y : Int32) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        divAux x y + 1
      else
        divAux x y - 1
    else
      divAux x y

/-- Euclidean remainder.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def emod (x y : Int32) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        modAux x y - y
      else
        modAux x y + y
    else
      modAux x y

/-- Flooring division.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fdiv (x y : Int32) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        divAux x y
      else
        divAux x y - 1
    else
      divAux x y

/-- Flooring remainder.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fmod (x y : Int32) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        modAux x y
      else
        modAux x y + y
    else
      modAux x y

instance : Div Int32 where
  div := Int32.div

instance : Mod Int32 where
  mod := Int32.mod

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 63)) ? (int32_t)#1 << (uint32_t)lean_unbox(#2) : INT32_C(0))"]
def shiftLeftNat : Int32 → @& Nat → Int32
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft Int32 Nat Int32 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times,
  rounding to negative infinity (flooring division). Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 63)) ? (int32_t)#1 >> (uint32_t)lean_unbox(#2) : INT32_C(0))"]
def shiftRightNat : Int32 → @& Nat → Int32
| x, 0 => x
| x, n+1 => shiftRightNat (fdiv x 2) n

instance : HShiftRight Int32 Nat Int32 where
  hShiftRight := shiftRightNat

/-- Left shift.

  `shiftLeft x n` first calculates `n % 32` to obtain an integer from 0 to 31. The bits of `x` are
  then shifted left (toward the most significant bit) by this amount, filling in with zero bits.
-/
@[inline, extern c inline "(int32_t)#1 << ((uint32_t)#2 & UINT8_C(31))"]
def shiftLeft (x y : Int32) : Int32 :=
  shiftLeftNat x (y &&& 31).toNat

instance : ShiftLeft Int32 where
  shiftLeft := shiftLeft

/-- Right shift.

  `shiftRight x n` first calculates `n % 32` to obtain an integer from 0 to 31. The bits of `x` are
  then shifted right (toward the least significant bit) by this amount, filling in with sign bits.
-/
@[inline, extern c inline "(int32_t)#1 >> ((uint32_t)#2 & UINT8_C(31))"]
def shiftRight (x y : Int32) : Int32 :=
  shiftRightNat x (y &&& 31).toNat

instance : ShiftRight Int32 where
  shiftRight := shiftRight

end Int32

/-
  ## Int64 -- Signed 64-bit integers
-/

/-- The type of signed 64-bit integers.

  This type has special support in the compiler to make it actually 8 bits rather than wrapping an `Int`. -/
structure Int64 extends UInt64
deriving Inhabited, BEq, Repr

instance (n : Nat) [OfNat UInt64 n] : OfNat Int64 n where
  ofNat := ⟨OfNat.ofNat n⟩

/-- Cast `UInt64` to `Int64` -/
abbrev UInt64.toInt64 := Int64.mk

namespace Int64

private def signBit : UInt64 := 0x8000000000000000

/-- Maximum `Int64` value: `2^63-1`. -/
protected def max : Int64 := ⟨~~~signBit⟩

/-- Minimum `Int64` value: `-2^63`. -/
protected def min : Int64 := ⟨signBit⟩

/-- Test if zero. -/
@[inline, extern c inline "(bool)((int64_t)#1 == INT64_C(0))"]
def isZero : Int64 → Bool
| ⟨x⟩ => x == 0

/-- Test if negative using the sign bit. -/
@[inline, extern c inline "(bool)((int64_t)#1 < INT64_C(0))"]
def isNeg : Int64 → Bool
| ⟨x⟩ => x &&& signBit != 0

/-- Cast `Int64` to `Int`. -/
def toInt (x : Int64) : Int :=
  bif x.isNeg then
    -(-x.toUInt64).toNat
  else
    x.toUInt64.toNat

instance : ToString Int64 where
  toString x := toString (toInt x)

/-- Attempt to convert from `Int` to `Int64`.

  `ofInt? x` succeeds if `-2^63 ≤ x < 2^63`.
-/
def ofInt? : Int → Option Int64
| .ofNat x => bif x ≤ 0x7f then some ⟨x.toUInt64⟩ else none
| .negSucc x => bif x ≤ 0x7f then some ⟨~~~x.toUInt64⟩ else none

/-- Attempt to convert from `Int` to `Int64`.

  `ofInt! x` panics if `-2^63 > x` or `x ≥ 2^63`.
-/
def ofInt! (x : Int) : Int64 :=
  match ofInt? x with
  | some x => x
  | none => panic! "integer out of range"

/-- Cast `Int` to `Int64`. -/
def _root_.Int.toInt64 (x : Int) : Int64 :=
  match Int64.ofInt? x with
  | some x => x
  | none => default

/-- Boolean less than or equal comparison. -/
@[inline, extern c inline "(bool)((int64_t)#1 <= (int64_t)#2)"]
def ble : Int64 → Int64 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit ≤ y + signBit

instance : LE Int64 where
  le x y := ble x y = true

instance (x y : Int64) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ = true))

/-- Boolean less than comparison. -/
@[inline, extern c inline "(bool)((int64_t)#1 <= (int64_t)#2)"]
def blt : Int64 → Int64 → Bool
| ⟨x⟩, ⟨y⟩ => x + signBit < y + signBit

instance : LT Int64 where
  lt x y := blt x y = true

instance (x y : Int64) : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ = true))

instance : Neg Int64 where
  neg | ⟨x⟩ => ⟨-x⟩

instance : Add Int64 where
  add | ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

instance : Sub Int64 where
  sub | ⟨x⟩, ⟨y⟩ => ⟨x - y⟩

instance : Mul Int64 where
  mul | ⟨x⟩, ⟨y⟩ => ⟨x * y⟩

instance : Complement Int64 where
  complement | ⟨x⟩ => ⟨~~~x⟩

instance : AndOp Int64 where
  and | ⟨x⟩, ⟨y⟩ => ⟨x &&& y⟩

instance : OrOp Int64 where
  or | ⟨x⟩, ⟨y⟩ => ⟨x ||| y⟩

instance : Xor Int64 where
  xor | ⟨x⟩, ⟨y⟩ => ⟨x ^^^ y⟩

@[inline, extern c inline "(int64_t)#1 / (int64_t)#2"]
private def divAux (x y : Int64) : Int64 := (Int.div x.toInt y.toInt).toInt64

@[inline, extern c inline "(int64_t)#1 % (int64_t)#2"]
private def modAux (x y : Int64) : Int64 := (Int.mod x.toInt y.toInt).toInt64

/-- Truncated division.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/

@[inline]
def div (x y : Int64) : Int64 := bif y.isZero then 0 else divAux x y

/-- Truncated remainder.

  Truncated division and remainder always satisfy `x = y * div x y + mod x y` and
  `0 ≤ |mod x y| < |y|`, provided `y ≠ 0`. If `mod x y` is nonzero, then its sign  matches that
  of `x`. By convention, `div x 0 = 0` and `mod x 0 = x`.
-/
@[inline]
def mod (x y : Int64) : Int64 := bif y.isZero then x else modAux x y

/-- Euclidean division.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def ediv (x y : Int64) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        divAux x y + 1
      else
        divAux x y - 1
    else
      divAux x y

/-- Euclidean remainder.

  Euclidean division and remainder always satisfy `x = y * ediv x y + emod x y` and
  `0 ≤ emod x y < |y|`, provided `y ≠ 0`. By convention, `ediv x 0 = 0` and `emod x 0 = x`.
-/
@[inline]
def emod (x y : Int64) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg then
      bif y.isNeg then
        modAux x y - y
      else
        modAux x y + y
    else
      modAux x y

/-- Flooring division.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fdiv (x y : Int64) :=
  bif y.isZero then y else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        divAux x y
      else
        divAux x y - 1
    else
      divAux x y

/-- Flooring remainder.

  Flooring division and remainder always satisfy `x = y * fdiv x y + fmod x y`. If `y > 0` then
  `0 ≤ fmod x y < y`, and if `y < 0` then `y < fmod x y ≤ 0`. By convention, `div x 0 = 0` and
  `mod x 0 = x`.
-/
@[inline]
def fmod (x y : Int64) :=
  bif y.isZero then x else
    bif (modAux x y).isNeg != y.isNeg then
      bif (modAux x y).isZero then
        modAux x y
      else
        modAux x y + y
    else
      modAux x y

instance : Div Int64 where
  div := Int64.div

instance : Mod Int64 where
  mod := Int64.mod

/-- Natural left shift.

  The result of `shiftLeftNat x n` is the same as repeatedly multiplying `x` by two `n` times.
  Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 127)) ? (int64_t)#1 << (uint64_t)lean_unbox(#2) : INT64_C(0))"]
def shiftLeftNat : Int64 → @& Nat → Int64
| x, 0 => x
| x, n+1 => shiftLeftNat (x * 2) n

instance : HShiftLeft Int64 Nat Int64 where
  hShiftLeft := shiftLeftNat

/-- Natural right shift.

  The result of `shiftRightNat x n` is the same as repeatedly dividing `x` by two `n` times,
  rounding to negative infinity (flooring division). Note that this is not the same as `shiftLeft`.
-/
@[inline, extern c inline "((lean_is_scalar(#2) && ((size_t)#2 <= 127)) ? (int64_t)#1 >> (uint64_t)lean_unbox(#2) : INT64_C(0))"]
def shiftRightNat : Int64 → @& Nat → Int64
| x, 0 => x
| x, n+1 => shiftRightNat (fdiv x 2) n

instance : HShiftRight Int64 Nat Int64 where
  hShiftRight := shiftRightNat

/-- Left shift.

  `shiftLeft x n` first calculates `n % 64` to obtain an integer from 0 to 63. The bits of `x` are
  then shifted left (toward the most significant bit) by this amount, filling in with zero bits.
-/
@[inline, extern c inline "(int64_t)#1 << ((uint64_t)#2 & UINT64_C(63))"]
def shiftLeft (x y : Int64) : Int64 :=
  shiftLeftNat x (y &&& 63).toNat

instance : ShiftLeft Int64 where
  shiftLeft := shiftLeft

/-- Right shift.

  `shiftRight x n` first calculates `n % 8` to obtain an integer from 0 to 7. The bits of `x` are
  then shifted right (toward the least significant bit) by this amount, filling in with sign bits.
-/
@[inline, extern c inline "(int64_t)#1 >> ((uint64_t)#2 & UINT64_C(63))"]
def shiftRight (x y : Int64) : Int64 :=
  shiftRightNat x (y &&& 63).toNat

instance : ShiftRight Int64 where
  shiftRight := shiftRight

end Int64

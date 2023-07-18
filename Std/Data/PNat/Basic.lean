import Std.Tactic.Ext
import Std.Data.Nat.Lemmas

/-- Positive integer type -/
@[ext] structure PNat where
  /-- Coercion from `PNat` to `Nat` -/
  protected toNat : Nat
  /-- Positive integers are nonzero -/
  protected ne_zero : toNat ≠ 0
deriving DecidableEq

namespace PNat

instance : Coe PNat Nat := ⟨PNat.toNat⟩

protected theorem zero_lt (x : PNat) : 0 < x.toNat := Nat.zero_lt_of_ne_zero x.ne_zero

instance : OfNat PNat (n+1) := ⟨n+1, Nat.noConfusion⟩

@[simp] theorem toNat_one : PNat.toNat 1 = 1 := rfl
@[simp] theorem toNat_two : PNat.toNat 2 = 2 := rfl
@[simp] theorem toNat_ofNat_succ (x : Nat) : PNat.toNat (OfNat.ofNat (x+1)) = x+1 := rfl

/-- Comparison of positive integers -/

instance : LE PNat where le a b := a.toNat ≤ b.toNat
instance : LT PNat where lt a b := a.toNat < b.toNat
instance : Ord PNat where compare a b := compare a.toNat b.toNat

instance (a b : PNat) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance (a b : PNat) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))

theorem toNat_eq (a b : PNat) : (a = b) = (a.toNat = b.toNat) := propext (PNat.ext_iff ..)
theorem toNat_ne (a b : PNat) : (a ≠ b) = (a.toNat ≠ b.toNat) := congrArg Not (toNat_eq ..)
theorem toNat_le (a b : PNat) : (a ≤ b) = (a.toNat ≤ b.toNat) := rfl
theorem toNat_lt (a b : PNat) : (a < b) = (a.toNat < b.toNat) := rfl
theorem toNat_ge (a b : PNat) : (a ≥ b) = (a.toNat ≥ b.toNat) := rfl
theorem toNat_gt (a b : PNat) : (a > b) = (a.toNat > b.toNat) := rfl
theorem toNat_compare (a b : PNat) : compare a b = compare a.toNat b.toNat := rfl

/-- Maximum of two positive integers -/
protected def max (x y : PNat) : PNat := if x ≤ y then y else x
instance : Max PNat := ⟨PNat.max⟩

theorem toNat_max (x y : PNat) : (max x y).toNat = max x.toNat y.toNat := by
  simp only [Max.max, PNat.max, Nat.max_def]; split
  next h => rw [toNat_le] at h; rw [if_pos h]
  next h => rw [toNat_le] at h; rw [if_neg h]

/-- Minimum of two positive integers -/
protected def min (x y : PNat) : PNat := if x ≤ y then x else y
instance : Min PNat := ⟨PNat.min⟩

theorem toNat_min (x y : PNat) : (min x y).toNat = min x.toNat y.toNat := by
  simp only [Min.min, PNat.min, Nat.min_def]; split
  next h => rw [toNat_le] at h; rw [if_pos h]
  next h => rw [toNat_le] at h; rw [if_neg h]

/-- Addition of positive integers -/
protected def add : PNat → PNat → PNat
  | ⟨x+1,_⟩, ⟨y+1,_⟩ => ⟨(x+1)+(y+1), Nat.noConfusion⟩
instance : Add PNat := ⟨PNat.add⟩

theorem toNat_add : ∀ (x y : PNat), (x + y).toNat = x.toNat + y.toNat
  | ⟨_+1,_⟩, ⟨_+1,_⟩ => rfl

/-- Partial subtraction of positive integers -/
protected def sub? (x y : PNat) : Option PNat :=
  match x.toNat - y.toNat with
  | 0 => none
  | r+1 => some ⟨r+1, Nat.noConfusion⟩

theorem toNat_sub? (x y : PNat) : (PNat.sub? x y).rec 0 PNat.toNat = x.toNat - y.toNat := by
  unfold PNat.sub?; split <;> next h => rw [h]

/-- Multiplication of positive integers -/
protected def mul : PNat → PNat → PNat
  | ⟨x+1,_⟩, ⟨y+1,_⟩ => ⟨(x+1)*(y+1), Nat.noConfusion⟩
instance : Mul PNat := ⟨PNat.mul⟩

theorem toNat_mul : ∀ (x y : PNat), (x * y).toNat = x.toNat * y.toNat
  | ⟨_+1,_⟩, ⟨_+1,_⟩ => rfl

/-- Exponentiation of positive integers -/
protected def pow (x : PNat) (y : Nat) : PNat :=
  ⟨x.toNat ^ y, Nat.not_eq_zero_of_lt (Nat.pos_pow_of_pos _ x.zero_lt)⟩

instance : HPow PNat Nat PNat := ⟨PNat.pow⟩

theorem toNat_pow (x : PNat) (y : Nat) : (instHPowPNatNat.hPow x y).toNat = x.toNat ^ y := rfl

end PNat

import Std.Tactic.Ext
import Std.Data.Nat.Lemmas

/-- Positive integer type -/
@[ext] structure Pos where
  /-- Coercion from `Pos` to `Nat` -/
  protected toNat : Nat
  /-- Positive integers are nonzero -/
  ne_zero : toNat ≠ 0

namespace Pos

theorem zero_lt (x : Pos) : 0 < x.toNat := Nat.zero_lt_of_ne_zero x.ne_zero

instance : OfNat Pos (nat_lit 1) := ⟨1, Nat.noConfusion⟩
instance : OfNat Pos (nat_lit 2) := ⟨2, Nat.noConfusion⟩
instance : OfNat Pos (n+1) := ⟨n+1, Nat.noConfusion⟩

@[simp] theorem toNat_one : Pos.toNat 1 = 1 := rfl
@[simp] theorem toNat_two : Pos.toNat 2 = 2 := rfl
@[simp] theorem toNat_ofNat_succ (x : Nat) : Pos.toNat (OfNat.ofNat (x+1)) = x+1 := rfl

/-- Addition of positive integers -/
protected def add : Pos → Pos → Pos
  | ⟨x+1,_⟩, ⟨y+1,_⟩ => ⟨(x+1)+(y+1), Nat.noConfusion⟩
instance : Add Pos := ⟨Pos.add⟩

@[local simp] theorem toNat_add : ∀ (x y : Pos), (x + y).toNat = x.toNat + y.toNat
  | ⟨_+1,_⟩, ⟨_+1,_⟩ => rfl

/-- Partial subtraction of positive integers -/
protected def sub? (x y : Pos) : Option Pos :=
  match x.toNat - y.toNat with
  | 0 => none
  | r+1 => some ⟨r+1, Nat.noConfusion⟩

theorem toNat_sub? (x y : Pos) : (Pos.sub? x y).rec 0 Pos.toNat = x.toNat - y.toNat := by
  unfold Pos.sub?; split <;> next h => rw [h]

/-- Multiplication of positive integers -/
protected def mul : Pos → Pos → Pos
  | ⟨x+1,_⟩, ⟨y+1,_⟩ => ⟨(x+1)*(y+1), Nat.noConfusion⟩
instance : Mul Pos := ⟨Pos.mul⟩

@[local simp] theorem toNat_mul : ∀ (x y : Pos), (x * y).toNat = x.toNat * y.toNat
  | ⟨_+1,_⟩, ⟨_+1,_⟩ => rfl

/-- Exponentiation of positive integers -/
@[local simp] protected def pow (x : Pos) (y : Nat) : Pos :=
  ⟨x.toNat ^ y, Nat.not_eq_zero_of_lt (Nat.pos_pow_of_pos _ x.zero_lt)⟩

instance : HPow Pos Nat Pos := ⟨Pos.pow⟩

theorem toNat_pow (x : Pos) (y : Nat) : (x ^ y).toNat = x.toNat ^ y := rfl

/-! ## Successor View

The _successor view_ of a positive integer corresponds to the alternate inductive definition:
```
inductive Pos
| one : Pos
| succ : Pos → Pos
```
where `one` represents `1` and `succ` represents the function `fun x => x+1`.
-/

/-- Inductive type for successor view of positive intgers -/
inductive IndView
  | /-- Case `1` -/ one
  | /-- Case `x+1` -/ succ (x : Pos)

/-- Return the successor view of a positive integer -/
@[inline] def toIndView : Pos → IndView
  | ⟨1, _⟩ => .one
  | ⟨x+2, _⟩ => .succ ⟨x+1, Nat.noConfusion⟩

/-- Return the positive integer represented by a successor view -/
@[inline] def ofIndView : IndView → Pos
  | .one => 1
  | .succ ⟨x, _⟩ => ⟨x+1, Nat.noConfusion⟩

@[simp] theorem toIndView_ofIndView (x) : toIndView (ofIndView x) = x := by
  rw [toIndView, ofIndView]
  match x with
  | .one => rfl
  | .succ ⟨x+1, _⟩ => rfl

@[simp] theorem ofIndView_toIndView (x) : ofIndView (toIndView x) = x := by
  rw [ofIndView, toIndView]
  match x with
  | ⟨1, _⟩ => rfl
  | ⟨x+2, _⟩ => rfl

theorem toIndView_eq_iff_ofIndView_eq : toIndView x = y ↔ ofIndView y = x := by
  constructor <;> intro | rfl => simp

/-! ### Successor View Helpers

Using the successor view for recursive definitions currently requires some helper lemmas to help
with termination proofs. The basic shape of a recursive definition using successor view is this:
```
def foo (x : Pos) : Widget :=
  match h : x.toIndView with
  | .one =>
    ...
  | .succ x =>
    have := IndView.succ_helper h
    ...
```
Eventually, we may see an extension of match syntax to automatically insert these boilerplate
elements.
-/
namespace IndView

theorem succ_helper {x y : Pos} : y.toIndView = .succ x → sizeOf x < sizeOf y := by
  intro h
  simp [toIndView] at h
  split at h
  next => contradiction
  next => cases h; simp_arith

end IndView

/-! ### Successor View Recursors

The successor view can also be used in proofs using the `induction` and `cases` tactics using
custom recursors. The basic syntax for these are
```
theorem foo (x : Pos) : ... := by
  induction x using Pos.recInd with
  | one => ...
  | succ x ih => ...
```
and
```
theorem bar (x : Pos) : ... := by
  cases x using Pos.casesInd with
  | one => ...
  | succ x => ...
```
-/
section
variable {motive : Pos → Sort _} (one : motive 1)
  (succ : (x : Pos) → motive x → motive (x+1))

/-- Recursor for successor view of positive integers -/
@[specialize, elab_as_elim]
protected def recInd (t : Pos) : motive t :=
  match h : t.toIndView with
  | .one =>
    have : t = 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView]
    this ▸ one
  | .succ x =>
    have := IndView.succ_helper h
    have : t = x + 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView, Pos.ext_iff, toNat_add, toNat_one]
    this ▸ succ _ (Pos.recInd x)

@[simp] theorem recInd_one : Pos.recInd one succ 1 = one := rfl

theorem recInd_succ (x) : Pos.recInd one succ (x+1) = succ x (Pos.recInd one succ x) := by
  have heq : toIndView (x+1) = .succ x := by
    simp [toIndView_eq_iff_ofIndView_eq, ofIndView, Pos.ext_iff]
  rw [Pos.recInd]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

variable (succ : (x : Pos) → motive (x+1))

/-- Cases matcher for successor view of positive integers -/
@[specialize, elab_as_elim]
protected def casesInd (t : Pos) : motive t :=
  match h : t.toIndView with
  | .one =>
    have : t = 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView]
    this ▸ one
  | .succ x =>
    have : t = x + 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView, Pos.ext_iff, toNat_add, toNat_one]
    this ▸ succ _

@[simp] theorem casesInd_one : Pos.casesInd one succ 1 = one := rfl

@[simp] theorem casesInd_succ (x) : Pos.casesInd one succ (x+1) = succ x := by
  have heq : toIndView (x+1) = .succ x := by
    simp [toIndView_eq_iff_ofIndView_eq, ofIndView, Pos.ext_iff]
  rw [Pos.casesInd]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

end

/-! ## Binary View

The _binary view_ of a positive integer corresponds to the alternate inductive definition:
```
inductive Pos
| one : Pos
| bit0 : Pos → Pos
| bit1 : Pos → Pos
```
where `one` represents `1` and `bit0`, `bit1` represents the functions `fun x => 2 * x`,
`fun x => 2 * x + 1`, respectively.
-/

/-- Inductive type for binary view of positive integers -/
inductive BinView
  | /-- Case `1` -/ one
  | /-- Case `2 * x` -/ bit0 (x : Pos)
  | /-- Case `2 * x + 1` -/ bit1 (x : Pos)

/-- Return the binary view of a positive integer -/
@[inline] def toBinView (x : Pos) : BinView :=
  match hq : x.toNat / 2, hr : x.toNat % 2 with
  | 0, 0 =>
    have : x.toNat = 0 := by rw [←Nat.div_add_mod x.toNat 2, hq, hr]
    absurd this x.ne_zero
  | 0, 1 => .one
  | q+1, 0 => .bit0 ⟨q+1, Nat.noConfusion⟩
  | q+1, 1 => .bit1 ⟨q+1, Nat.noConfusion⟩
  | _, _+2 => absurd (Nat.mod_lt x.toNat (show 0 < 2 by decide)) (by rw [hr]; intro; contradiction)

/-- Return the positive integer represented by a binary view -/
@[inline] def ofBinView : BinView → Pos
  | .one => 1
  | .bit0 x => 2 * x
  | .bit1 x => 2 * x + 1

/-! ### Binary View Helpers

Using the binary view for recursive definitions currently requires some helper lemmas to help
with termination proofs. The basic shape of a recursive definition usin binary view is this:
```
def foo (x : Pos) : Widget :=
  match h : x.toBinView with
  | .one =>
    ...
  | .bit0 x =>
    have := BinView.bit0_helper h
    ...
  | .bit1 x =>
    have := BinView.bit1_helper h
    ...
```
Eventually, we may see an extension of match syntax to automatically insert these boilerplate
elements.
-/
namespace BinView

theorem bit0_helper {x y : Pos} : y.toBinView = .bit0 x → sizeOf x < sizeOf y := by
  intro h
  simp [toBinView] at h
  split at h
  next hq hr =>
    apply absurd _ y.ne_zero
    rw [←Nat.div_add_mod y.toNat 2, hq, hr]
  next => contradiction
  next hq hr =>
    match x, y with
    | ⟨x, _⟩, ⟨y, _⟩ =>
    simp at h hq hr ⊢
    cases h
    rw [←Nat.div_add_mod y 2, hq, hr]
    simp_arith
  next => contradiction
  next hr =>
    apply absurd (Nat.mod_lt y.toNat (show 0 < 2 by decide))
    rw [hr]; intro; contradiction

theorem bit1_helper {x y : Pos} : y.toBinView = .bit1 x → sizeOf x < sizeOf y := by
  intro h
  simp [toBinView] at h
  split at h
  next hq hr =>
    apply absurd _ y.ne_zero
    rw [←Nat.div_add_mod y.toNat 2, hq, hr]
  next => contradiction
  next => contradiction
  next hq hr =>
    match x, y with
    | ⟨x, _⟩, ⟨y, _⟩ =>
    simp at h hq hr ⊢
    cases h
    rw [←Nat.div_add_mod y 2, hq, hr]
    simp_arith
  next hr =>
    apply absurd (Nat.mod_lt y.toNat (show 0 < 2 by decide))
    rw [hr]; intro; contradiction

end BinView

@[simp] theorem toBinView_ofBinView (x) : toBinView (ofBinView x) = x := by
  rw [toBinView, ofBinView]
  cases x with simp
  | bit0 x =>
    have := x.ne_zero
    split
    next hq hr => simp at hq hr; contradiction
    next hq hr => simp at hq hr
    next hq hr =>
      simp at hq hr; congr 1; ext; exact hq.symm
    next hq hr => simp at hq hr
    next heq =>
      apply absurd (Nat.mod_lt (2 * x).toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction
  | bit1 x =>
    have := x.ne_zero
    split
    next hq hr =>
      simp [Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr; done
    next hq hr =>
      simp [Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr; contradiction
    next hq hr =>
      simp [Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr; done
    next hq hr =>
      simp [Nat.add_comm _ 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr
      congr 1; ext; exact hq.symm
    next heq =>
      apply absurd (Nat.mod_lt (2 * x + 1).toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction

@[simp] theorem ofBinView_toBinView (x) : ofBinView (toBinView x) = x := by
  have hnz := x.ne_zero
  rw [ofBinView]
  cases h : x.toBinView with
  | one =>
    rw [toBinView] at h
    split at h
    next hq hr =>
      rw [←Nat.div_add_mod x.toNat 2, hq, hr] at hnz
      contradiction
    next hq hr =>
      ext; rw [←Nat.div_add_mod x.toNat 2, hq, hr]; rfl
    next hq hr => contradiction; done
    next hq hr => contradiction; done
    next heq =>
      apply absurd (Nat.mod_lt x.toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction
  | bit0 =>
    rw [toBinView] at h
    split at h
    next hq hr =>
      rw [←Nat.div_add_mod x.toNat 2, hq, hr] at hnz
      contradiction
    next hq hr => contradiction; done
    next hq hr =>
      simp [Pos.ext_iff] at h ⊢
      rw [←h, ←Nat.div_add_mod x.toNat 2, hq, hr]; rfl
    next hq hr => contradiction; done
    next heq =>
      apply absurd (Nat.mod_lt x.toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction
  | bit1 =>
    rw [toBinView] at h
    split at h
    next hq hr =>
      rw [←Nat.div_add_mod x.toNat 2, hq, hr] at hnz
      contradiction
    next hq hr => contradiction; done
    next hq hr => contradiction; done
    next hq hr =>
      simp [Pos.ext_iff] at h ⊢
      rw [←h, ←Nat.div_add_mod x.toNat 2, hq, hr]
    next heq =>
      apply absurd (Nat.mod_lt x.toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction

theorem toBinView_eq_iff_ofBinView_eq : toBinView x = y ↔ ofBinView y = x := by
  constructor <;> intro | rfl => simp

/-! ### Binary View Recursors

The successor view can also be used in proofs using the `induction` and `cases` tactics using
custom recursors. The basic syntax for these are
```
theorem foo (x : Pos) : ... := by
  induction x using Pos.recBin with
  | one => ...
  | bit0 x ih => ...
  | bit1 x ih => ...
```
and
```
theorem bar (x : Pos) : ... := by
  cases x using Pos.casesInd with
  | one => ...
  | bit0 x => ...
  | bit1 x => ...
```
-/
section Recursors
variable {motive : Pos → Sort _} (one : motive 1)
  (bit0 : (x : Pos) → motive x → motive (2 * x))
  (bit1 : (x : Pos) → motive x → motive (2 * x + 1))

/-- Recursor for binary view of positive integers -/
@[specialize, elab_as_elim]
protected def recBin (t : Pos) : motive t :=
  match h : t.toBinView with
  | .one =>
    have : 1 = t := by
      simp [toBinView_eq_iff_ofBinView_eq, ofBinView] at h
      exact h
    this ▸ one
  | .bit0 x =>
    have := BinView.bit0_helper h
    have : 2 * x = t := by
      simp [toBinView_eq_iff_ofBinView_eq, ofBinView] at h
      exact h
    this ▸ bit0 x (Pos.recBin x)
  | .bit1 x =>
    have := BinView.bit1_helper h
    have : 2 * x + 1 = t := by
      simp [toBinView_eq_iff_ofBinView_eq, ofBinView] at h
      exact h
    this ▸ bit1 x (Pos.recBin x)

@[simp] theorem recBin_one : Pos.recBin one bit0 bit1 1 = one := rfl

theorem recBin_bit0 (x : Pos) : Pos.recBin one bit0 bit1 (2 * x) = bit0 x (Pos.recBin one bit0 bit1 x) := by
    have heq : toBinView (2 * x) = .bit0 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
    rw [Pos.recBin]
    split
    next h => rw [heq] at h; contradiction
    next h => rw [heq] at h; cases h; rfl
    next h => rw [heq] at h; contradiction

theorem recBin_bit1 (x : Pos) : Pos.recBin one bit0 bit1 (2 * x + 1) = bit1 x (Pos.recBin one bit0 bit1 x) := by
    have heq : toBinView (2 * x + 1) = .bit1 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
    rw [Pos.recBin]
    split
    next h => rw [heq] at h; contradiction
    next h => rw [heq] at h; contradiction
    next h => rw [heq] at h; cases h; rfl

variable (bit0 : (x : Pos) → motive (2 * x)) (bit1 : (x : Pos) → motive (2 * x + 1))

/-- Matcher for binary view of positive integers -/
@[specialize, elab_as_elim]
protected def casesBin (t : Pos) : motive t :=
  match h : t.toBinView with
  | .one =>
    have : t = 1 := by
      rw [toBinView_eq_iff_ofBinView_eq] at h
      rw [←h, ofBinView]
    this ▸ one
  | .bit0 x =>
    have : t = 2 * x := by
      rw [toBinView_eq_iff_ofBinView_eq] at h
      rw [←h, ofBinView]
    this ▸ bit0 _
  | .bit1 x =>
    have : t = 2 * x + 1 := by
      rw [toBinView_eq_iff_ofBinView_eq] at h
      rw [←h, ofBinView]
    this ▸ bit1 _

@[simp] theorem casesBin_one : Pos.casesBin one bit0 bit1 1 = one := rfl

@[simp] theorem casesBin_bit0 (x) : Pos.casesBin one bit0 bit1 (2 * x) = bit0 x := by
  have heq : toBinView (2 * x) = .bit0 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [Pos.casesBin]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl
  next h => rw [heq] at h; contradiction

@[simp] theorem casesBin_bit1 (x) : Pos.casesBin one bit0 bit1 (2 * x + 1) = bit1 x := by
  have heq : toBinView (2 * x + 1) = .bit1 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [Pos.casesBin]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

end Recursors

/-- Tail recursive version of `Pos.log2` -/
private def log2TR (x : Pos) : Nat :=
  let rec loop (l : Nat) (x : Pos) : Nat :=
    match h : x.toBinView with
    | .one => l
    | .bit0 x =>
      have := BinView.bit0_helper h
      loop (l+1) x
    | .bit1 x =>
      have := BinView.bit1_helper h
      loop (l+1) x
  loop 0 x

/-- Logarithm base 2, rounded down -/
@[implemented_by log2TR]
protected def log2 (x : Pos) : Nat :=
  Pos.recBin 0 (fun _ l => l+1) (fun _ l => l+1) x

@[simp] theorem log2_one : Pos.log2 1 = 0 := rfl

theorem log2_bit0 (x) : Pos.log2 (2 * x) = Pos.log2 x + 1 := Pos.recBin_bit0 ..

theorem log2_bit1 (x) : Pos.log2 (2 * x + 1) = Pos.log2 x + 1 := Pos.recBin_bit1 ..

end Pos

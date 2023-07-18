import Std.Data.PNat.Basic

namespace PNat

/-! ## Binary View

The _binary view_ of a positive integer corresponds to the alternate inductive definition:
```
inductive PNat
| one : PNat
| bit0 : PNat → PNat
| bit1 : PNat → PNat
```
where `one` represents `1` and `bit0`, `bit1` represents the functions `fun x => 2 * x`,
`fun x => 2 * x + 1`, respectively.
-/

/-- Inductive type for binary view of positive integers -/
inductive BinView
  | /-- Case `1` -/ one
  | /-- Case `2 * x` -/ bit0 (x : PNat)
  | /-- Case `2 * x + 1` -/ bit1 (x : PNat)

/-- Return the binary view of a positive integer -/
@[inline] def toBinView (x : PNat) : BinView :=
  match hq : x.toNat / 2, hr : x.toNat % 2 with
  | 0, 0 =>
    have : x.toNat = 0 := by rw [←Nat.div_add_mod x.toNat 2, hq, hr]
    absurd this x.ne_zero
  | 0, 1 => .one
  | q+1, 0 => .bit0 ⟨q+1, Nat.noConfusion⟩
  | q+1, 1 => .bit1 ⟨q+1, Nat.noConfusion⟩
  | _, _+2 => absurd (Nat.mod_lt x.toNat (show 0 < 2 by decide)) (by rw [hr]; intro; contradiction)

/-- Return the positive integer represented by a binary view -/
@[inline] def ofBinView : BinView → PNat
  | .one => 1
  | .bit0 x => 2 * x
  | .bit1 x => 2 * x + 1

@[simp] theorem ofBinView_one : ofBinView .one = 1 := rfl

@[simp] theorem ofBinView_bit0 (x) : ofBinView (.bit0 x) = 2 * x := rfl

@[simp] theorem ofBinView_bit1 (x) : ofBinView (.bit1 x) = 2 * x + 1 := rfl

/-! ### Binary View Helpers

Using the binary view for recursive definitions currently requires some helper lemmas to help
with termination proofs. The basic shape of a recursive definition usin binary view is this:
```
def foo (x : PNat) : Widget :=
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

theorem bit0_helper {x y : PNat} : y.toBinView = .bit0 x → sizeOf x < sizeOf y := by
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

theorem bit1_helper {x y : PNat} : y.toBinView = .bit1 x → sizeOf x < sizeOf y := by
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
    next hq hr => simp [toNat_add, toNat_mul] at hq hr; contradiction
    next hq hr => simp [toNat_add, toNat_mul] at hq hr
    next hq hr =>
      simp [toNat_add, toNat_mul] at hq hr; congr 1; ext; exact hq.symm
    next hq hr => simp [toNat_add, toNat_mul] at hq hr
    next heq =>
      apply absurd (Nat.mod_lt (2 * x).toNat (show 0 < 2 by decide))
      rw [heq]; intro; contradiction
  | bit1 x =>
    have := x.ne_zero
    split
    next hq hr =>
      simp [toNat_add, toNat_mul, Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr
    next hq hr =>
      simp [toNat_add, toNat_mul, Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr; contradiction
    next hq hr =>
      simp [toNat_add, toNat_mul, Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr
    next hq hr =>
      simp [toNat_add, toNat_mul, Nat.add_comm (2 * _) 1, Nat.add_mul_div_left, Nat.div_eq_of_lt] at hq hr
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
      simp [toNat_mul, toNat_add, PNat.ext_iff] at h ⊢
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
      simp [toNat_add, toNat_mul, PNat.ext_iff] at h ⊢
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
theorem foo (x : PNat) : ... := by
  induction x using PNat.recBin with
  | one => ...
  | bit0 x ih => ...
  | bit1 x ih => ...
```
and
```
theorem bar (x : PNat) : ... := by
  cases x using PNat.casesInd with
  | one => ...
  | bit0 x => ...
  | bit1 x => ...
```
-/
section Recursors
variable {motive : PNat → Sort _} (one : motive 1)
  (bit0 : (x : PNat) → motive x → motive (2 * x))
  (bit1 : (x : PNat) → motive x → motive (2 * x + 1))

/-- Recursor for binary view of positive integers -/
@[specialize, elab_as_elim]
protected def recBin (t : PNat) : motive t :=
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
    this ▸ bit0 x (PNat.recBin x)
  | .bit1 x =>
    have := BinView.bit1_helper h
    have : 2 * x + 1 = t := by
      simp [toBinView_eq_iff_ofBinView_eq, ofBinView] at h
      exact h
    this ▸ bit1 x (PNat.recBin x)

@[simp] theorem recBin_one : PNat.recBin one bit0 bit1 1 = one := rfl

theorem recBin_bit0 (x : PNat) :
    PNat.recBin one bit0 bit1 (2 * x) = bit0 x (PNat.recBin one bit0 bit1 x) := by
  have heq : toBinView (2 * x) = .bit0 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [PNat.recBin]
  split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl
  next h => rw [heq] at h; contradiction

theorem recBin_bit1 (x : PNat) :
    PNat.recBin one bit0 bit1 (2 * x + 1) = bit1 x (PNat.recBin one bit0 bit1 x) := by
  have heq : toBinView (2 * x + 1) = .bit1 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [PNat.recBin]
  split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

variable (bit0 : (x : PNat) → motive (2 * x)) (bit1 : (x : PNat) → motive (2 * x + 1))

/-- Matcher for binary view of positive integers -/
@[specialize, elab_as_elim]
protected def casesBin (t : PNat) : motive t :=
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

@[simp] theorem casesBin_one : PNat.casesBin one bit0 bit1 1 = one := rfl

@[simp] theorem casesBin_bit0 (x) : PNat.casesBin one bit0 bit1 (2 * x) = bit0 x := by
  have heq : toBinView (2 * x) = .bit0 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [PNat.casesBin]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl
  next h => rw [heq] at h; contradiction

@[simp] theorem casesBin_bit1 (x) : PNat.casesBin one bit0 bit1 (2 * x + 1) = bit1 x := by
  have heq : toBinView (2 * x + 1) = .bit1 x := by rw [toBinView_eq_iff_ofBinView_eq]; rfl
  rw [PNat.casesBin]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

end Recursors

/-- Tail recursive version of `PNat.log2` -/
private def log2TR (x : PNat) : Nat :=
  let rec loop (l : Nat) (x : PNat) : Nat :=
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
protected def log2 (x : PNat) : Nat :=
  PNat.recBin 0 (fun _ l => l+1) (fun _ l => l+1) x

@[simp] theorem log2_one : PNat.log2 1 = 0 := rfl

theorem log2_bit0 (x) : PNat.log2 (2 * x) = PNat.log2 x + 1 := PNat.recBin_bit0 ..

theorem log2_bit1 (x) : PNat.log2 (2 * x + 1) = PNat.log2 x + 1 := PNat.recBin_bit1 ..

end PNat

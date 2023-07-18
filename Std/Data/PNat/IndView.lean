import Std.Data.PNat.Basic

namespace PNat

/-! ## Successor View

The _successor view_ of a positive integer corresponds to the alternate inductive definition:
```
inductive PNat
| one : PNat
| succ : PNat → PNat
```
where `one` represents `1` and `succ` represents the function `fun x => x+1`.
-/

/-- Inductive type for successor view of positive intgers -/
inductive IndView
  | /-- Case `1` -/ one
  | /-- Case `x+1` -/ succ (x : PNat)

/-- Return the successor view of a positive integer -/
@[inline] def toIndView : PNat → IndView
  | ⟨1, _⟩ => .one
  | ⟨x+2, _⟩ => .succ ⟨x+1, Nat.noConfusion⟩

/-- Return the positive integer represented by a successor view -/
@[inline] def ofIndView : IndView → PNat
  | .one => 1
  | .succ ⟨x, _⟩ => ⟨x+1, Nat.noConfusion⟩

@[simp] theorem ofIndView_one : ofIndView .one = 1 := rfl

@[simp] theorem ofIndView_succ (x) : ofIndView (.succ x) = x + 1 := by
  simp only [toNat_eq, toNat_one, toNat_add, ofIndView]

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
def foo (x : PNat) : Widget :=
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

theorem succ_helper {x y : PNat} : y.toIndView = .succ x → sizeOf x < sizeOf y := by
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
theorem foo (x : PNat) : ... := by
  induction x using PNat.recInd with
  | one => ...
  | succ x ih => ...
```
and
```
theorem bar (x : PNat) : ... := by
  cases x using PNat.casesInd with
  | one => ...
  | succ x => ...
```
-/
section
variable {motive : PNat → Sort _} (one : motive 1)
  (succ : (x : PNat) → motive x → motive (x+1))

/-- Recursor for successor view of positive integers -/
@[specialize, elab_as_elim]
protected def recInd (t : PNat) : motive t :=
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
      rw [←h, ofIndView, PNat.ext_iff, toNat_add, toNat_one]
    this ▸ succ _ (PNat.recInd x)

@[simp] theorem recInd_one : PNat.recInd one succ 1 = one := rfl

theorem recInd_succ (x) : PNat.recInd one succ (x+1) = succ x (PNat.recInd one succ x) := by
  have heq : toIndView (x+1) = .succ x := by
    simp [toNat_add, toIndView_eq_iff_ofIndView_eq, ofIndView, PNat.ext_iff]
  rw [PNat.recInd]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

variable (succ : (x : PNat) → motive (x+1))

/-- Cases matcher for successor view of positive integers -/
@[specialize, elab_as_elim]
protected def casesInd (t : PNat) : motive t :=
  match h : t.toIndView with
  | .one =>
    have : t = 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView]
    this ▸ one
  | .succ x =>
    have : t = x + 1 := by
      rw [toIndView_eq_iff_ofIndView_eq] at h
      rw [←h, ofIndView, PNat.ext_iff, toNat_add, toNat_one]
    this ▸ succ _

@[simp] theorem casesInd_one : PNat.casesInd one succ 1 = one := rfl

@[simp] theorem casesInd_succ (x) : PNat.casesInd one succ (x+1) = succ x := by
  have heq : toIndView (x+1) = .succ x := by
    simp [toNat_add, toIndView_eq_iff_ofIndView_eq, ofIndView, PNat.ext_iff]
  rw [PNat.casesInd]; split
  next h => rw [heq] at h; contradiction
  next h => rw [heq] at h; cases h; rfl

end

end PNat

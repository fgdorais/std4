import Std.Logic
import Std.Data.PNat.Basic

namespace PNat

attribute [pnat_to_nat] toNat_one toNat_two toNat_min toNat_max toNat_add toNat_mul toNat_pow
      toNat_eq toNat_ne toNat_le toNat_lt toNat_ge toNat_gt

local syntax "toNat" (colGt ident)? : tactic
local macro_rules
| `(tactic| toNat) =>
  `(tactic| simp only [pnat_to_nat])
| `(tactic| toNat $n:ident) =>
  let n := Lean.mkIdent (`Nat ++ n.getId)
  `(tactic| simp only [pnat_to_nat]; apply $n)

/-! ## Ordering -/

@[simp] protected theorem not_le {a b : PNat} : ¬ a ≤ b ↔ b < a := by
  toNat not_le

@[simp] protected theorem not_lt {a b : PNat} : ¬ a < b ↔ b ≤ a := by
  toNat not_lt

protected theorem le_of_lt {a b : PNat} : a < b → a ≤ b := by
  toNat le_of_lt

protected theorem le_of_eq {a b : PNat} : a = b → a ≤ b := by
  toNat le_of_eq

protected theorem le_of_eq' {a b : PNat} (h : b = a) : a ≤ b :=
  PNat.le_of_eq h.symm

protected theorem ne_of_lt {a b : PNat} : a < b → a ≠ b := by
  toNat ne_of_lt

protected theorem ne_of_lt' {a b : PNat} (h : b < a) : a ≠ b :=
  PNat.ne_of_lt h |>.symm

@[simp] protected theorem le_refl (a : PNat) : a ≤ a := by
  toNat le_refl

protected theorem le_trans {a b c : PNat} : a ≤ b → b ≤ c → a ≤ c := by
  toNat le_trans

protected theorem le_antisymm {a b : PNat} : a ≤ b → b ≤ a → a = b := by
  toNat le_antisymm

protected theorem le_antisymm' {a b : PNat} : a ≤ b ∧ b ≤ a → a = b
  | ⟨h₁, h₂⟩ => PNat.le_antisymm h₁ h₂

protected theorem le_antisymm_iff {a b : PNat} : a = b ↔ a ≤ b ∧ b ≤ a := by
  toNat le_antisymm_iff

protected theorem le_total (a b : PNat) : a ≤ b ∨ b ≤ a := by
  toNat le_total

@[simp] protected theorem lt_irrefl (a : PNat) : ¬ a < a := by
  toNat lt_irrefl

protected theorem lt_trans {a b c : PNat} : a < b → b < c → a < c := by
  toNat lt_trans

protected theorem lt_of_le_of_lt {a b c : PNat} : a ≤ b → b < c → a < c := by
  toNat lt_of_le_of_lt

protected theorem lt_of_lt_of_le {a b c : PNat} : a < b → b ≤ c → a < c := by
  toNat lt_of_lt_of_le

protected theorem lt_connex {a b : PNat} : a ≠ b → a < b ∨ b < a := by
  simp only [←PNat.not_le, ←Decidable.not_and, and_comm]; apply mt PNat.le_antisymm'

protected theorem lt_connex_iff {a b : PNat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨PNat.lt_connex, fun | .inl h => PNat.ne_of_lt h | .inr h => PNat.ne_of_lt' h⟩

protected theorem lt_of_le_of_ne {a b : PNat} : a ≤ b → a ≠ b → a < b := by
  rw [←PNat.not_le]; intro hle hne hge; exact hne <| PNat.le_antisymm hle hge

protected theorem one_le (a : PNat) : 1 ≤ a := a.zero_lt

protected theorem eq_one_of_le_one {a : PNat} (h : a ≤ 1) : a = 1 :=
  PNat.le_antisymm h (PNat.one_le _)

protected theorem not_lt_one (a : PNat) : ¬ a < 1 := by
  simp; exact PNat.one_le ..

protected theorem one_lt_of_ne_one {a : PNat} (h : a ≠ 1) : 1 < a :=
  PNat.lt_of_le_of_ne (PNat.one_le ..) h.symm

/-! ## Min/Max -/

protected theorem min_le_left (a b : PNat) : min a b ≤ a := by
  toNat min_le_left

protected theorem min_le_right (a b : PNat) : min a b ≤ b := by
  toNat min_le_right

protected theorem le_min_iff {a b c : PNat} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  toNat le_min_iff

protected theorem lt_min_iff {a b c : PNat} : a < min b c ↔ a < b ∧ a < c := by
  toNat lt_min_iff

protected theorem min_eq_left {a b : PNat} : a ≤ b → min a b = a := by
  toNat min_eq_left

protected theorem min_eq_right {a b : PNat} : b ≤ a → min a b = b := by
  toNat min_eq_right

protected theorem min_one_left (a : PNat) : min 1 a = 1 :=
  PNat.min_eq_left (PNat.one_le _)

protected theorem min_one_right (a : PNat) : min a 1 = 1 :=
  PNat.min_eq_right (PNat.one_le _)

protected theorem min_self (a : PNat) : min a a = a :=
  PNat.min_eq_left (PNat.le_refl _)

protected theorem min_comm (a b : PNat) : min a b = min b a := by
  toNat min_comm

protected theorem min_assoc (a b c : PNat) : min (min a b) c = min a (min b c) := by
  toNat min_assoc

protected theorem min_add_add_left (a b c : PNat) : min (a + b) (a + c) = a + min b c := by
  toNat min_add_add_left

protected theorem min_add_add_right (a b c : PNat) : min (a + b) (c + b) = min a c + b := by
  toNat min_add_add_right

protected theorem min_mul_mul_left (a b c : PNat) : min (a * b) (a * c) = a * min b c := by
  toNat min_mul_mul_left

protected theorem min_mul_mul_right (a b c : PNat) : min (a * b) (c * b) = min a c * b := by
  toNat min_mul_mul_right

protected theorem le_max_left (a b : PNat) : a ≤ max a b := by
  toNat le_max_left

protected theorem le_max_right (a b : PNat) : b ≤ max a b := by
  toNat le_max_right

protected theorem max_le_iff {a b c : PNat} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  toNat max_le_iff

protected theorem max_lt_iff {a b c : PNat} : max a b < c ↔ a < c ∧ b < c := by
  toNat max_lt_iff

protected theorem max_eq_left {a b : PNat} : b ≤ a → max a b = a := by
  toNat max_eq_left

protected theorem max_eq_right {a b : PNat} : a ≤ b → max a b = b := by
  toNat max_eq_right

protected theorem max_one_left (a : PNat) : max 1 a = a :=
  PNat.max_eq_right (PNat.one_le _)

protected theorem max_one_right (a : PNat) : max a 1 = a :=
  PNat.max_eq_left (PNat.one_le _)

protected theorem max_self (a : PNat) : max a a = a :=
  PNat.max_eq_left (PNat.le_refl _)

protected theorem max_comm (a b : PNat) : max a b = max b a := by
  toNat max_comm

protected theorem max_assoc (a b c : PNat) : max (max a b) c = max a (max b c) := by
   toNat max_assoc

protected theorem max_add_add_left (a b c : PNat) : max (a + b) (a + c) = a + max b c := by
  toNat max_add_add_left

protected theorem max_add_add_right (a b c : PNat) : max (a + b) (c + b) = max a c + b := by
  toNat max_add_add_right

protected theorem max_mul_mul_left (a b c : PNat) : max (a * b) (a * c) = a * max b c := by
  toNat max_mul_mul_left

protected theorem max_mul_mul_right (a b c : PNat) : max (a * b) (c * b) = max a c * b := by
  toNat max_mul_mul_right

protected theorem max_min_distrib_left (a b c : PNat) : max a (min b c) = min (max a b) (max a c) := by
  toNat max_min_distrib_left

protected theorem max_min_distrib_right (a b c : Nat) : max (min a b) c = min (max a c) (max b c) := by
  toNat max_min_distrib_right

protected theorem min_max_distrib_left (a b c : PNat) : min a (max b c) = max (min a b) (min a c) := by
  toNat min_max_distrib_left

protected theorem min_max_distrib_right (a b c : Nat) : min (max a b) c = max (min a c) (min b c) := by
  toNat min_max_distrib_right

/-! ## Addition -/

protected theorem add_comm (a b : PNat) : a + b = b + a := by
  toNat add_comm

protected theorem add_assoc (a b c : PNat) : a + b + c = a + (b + c) := by
  toNat add_assoc

protected theorem add_left_comm (a b c : PNat) : a + (b + c) = b + (a + c) := by
  toNat add_left_comm

protected theorem add_right_comm (a b c : PNat) : a + b + c = a + c + b := by
  toNat add_right_comm

protected theorem add_add_add_comm (a b c d : PNat) : a + b + (c + d) = a + c + (b + d) := by
  toNat add_add_add_comm

protected theorem add_left_cancel {a b c : PNat} : a + b = a + c → b = c := by
  toNat add_left_cancel

protected theorem add_right_cancel {a b c : PNat} : a + b = c + b → a = c := by
  toNat add_right_cancel

protected theorem add_le_add_left {a b c : PNat} : a ≤ b → c + a ≤ c + b := by
  toNat; intro h; apply Nat.add_le_add_left h c.toNat

protected theorem add_le_add_iff_left {a b c : PNat} : c + a ≤ c + b ↔ a ≤ b := by
  toNat add_le_add_iff_left

protected theorem add_le_add_right {a b c : PNat} : a ≤ b → a + c ≤ b + c := by
  toNat; intro h; apply Nat.add_le_add_right h c.toNat

protected theorem add_le_add_iff_right {a b c : PNat} : a + c ≤ b + c ↔ a ≤ b := by
  toNat add_le_add_iff_right

protected theorem add_lt_add_left {a b c : PNat} : a < b → c + a < c + b := by
  toNat; intro h; apply Nat.add_lt_add_left h

protected theorem add_lt_add_iff_left {a b c : PNat} : c + a < c + b ↔ a < b := by
  toNat add_lt_add_iff_left

protected theorem add_lt_add_right {a b c : PNat} : a < b → a + c < b + c := by
  toNat; intro h; apply Nat.add_lt_add_right h

protected theorem add_lt_add_iff_right {a b c : PNat} : a + c < b + c ↔ a < b := by
  toNat add_lt_add_iff_right

protected theorem lt_of_add_one_le {a b : PNat} : a + 1 ≤ b → a < b := by
  toNat lt_of_succ_le

protected theorem add_one_le_of_lt {a b : PNat} : a < b → a + 1 ≤ b := by
  toNat succ_le_of_lt

protected theorem lt_iff_add_one_le {a b : PNat} : a < b ↔ a + 1 ≤ b :=
  ⟨PNat.add_one_le_of_lt, PNat.lt_of_add_one_le⟩

protected theorem le_of_lt_add_one {a b : PNat} : a < b + 1 → a ≤ b := by
  toNat le_of_lt_succ

protected theorem lt_add_one_of_le {a b : PNat} : a ≤ b → a < b + 1 := by
  toNat lt_succ_of_le

protected theorem le_iff_lt_add_one {a b : PNat} : a ≤ b ↔ a < b + 1 :=
  ⟨PNat.lt_add_one_of_le, PNat.le_of_lt_add_one⟩

protected theorem lt_add_left (a b : PNat) : a < b + a := by
  toNat; apply Nat.lt_add_of_pos_left b.zero_lt

protected theorem lt_add_right (a b : PNat) : a < a + b := by
  toNat; apply Nat.lt_add_of_pos_right b.zero_lt

protected theorem add_ne_one (a b : PNat) : a + b ≠ 1 :=
  PNat.ne_of_lt' (PNat.lt_of_le_of_lt (PNat.one_le a) (PNat.lt_add_right ..))

protected theorem add_ne_left (a b : PNat) : a + b ≠ a :=
  PNat.ne_of_lt' (PNat.lt_add_right ..)

protected theorem add_ne_right (a b : PNat) : a + b ≠ b :=
  PNat.ne_of_lt' (PNat.lt_add_left ..)

/-! ## Multiplication -/

@[simp] protected theorem mul_one (a : PNat) : a * 1 = a := by
  toNat mul_one

@[simp] protected theorem one_mul (a : PNat) : 1 * a = a := by
  toNat one_mul

protected theorem mul_two (a : PNat) : a * 2 = a + a := by
  toNat mul_two

protected theorem two_mul (a : PNat) : 2 * a = a + a := by
  toNat two_mul

protected theorem mul_comm (a b : PNat) : a * b = b * a := by
  toNat mul_comm

protected theorem mul_assoc (a b c : PNat) : a * b * c = a * (b * c) := by
  toNat mul_assoc

protected theorem mul_left_comm (a b c : PNat) : a * (b * c) = b * (a * c) := by
  toNat mul_left_comm

protected theorem mul_right_comm (a b c : PNat) : a * b * c = a * c * b := by
  toNat mul_right_comm

protected theorem mul_mul_mul_comm (a b c d : PNat) : a * b * (c * d) = a * c * (b * d) := by
  toNat mul_mul_mul_comm

protected theorem mul_add (a b c : PNat) : a * (b + c) = a * b + a * c := by
  toNat mul_add

protected theorem add_mul (a b c : PNat) : (a + b) * c = a * c + b * c := by
  toNat add_mul

protected theorem mul_left_cancel {a b c : PNat} : a * b = a * c → b = c := by
  toNat; apply Nat.eq_of_mul_eq_mul_left a.zero_lt

protected theorem mul_right_cancel {a b c : PNat} : a * b = c * b → a = c := by
  toNat; apply Nat.eq_of_mul_eq_mul_right b.zero_lt

protected theorem mul_le_mul_left (a : PNat) {b c : PNat} : b ≤ c → a * b ≤ a * c := by
  toNat mul_le_mul_left

protected theorem le_of_mul_le_mul_left {a b c : PNat} : a * b ≤ a * c → b ≤ c := by
  toNat; intro h; apply Nat.le_of_mul_le_mul_left h a.zero_lt

protected theorem mul_le_mul_iff_left {a b c : PNat} : b ≤ c ↔ a * b ≤ a * c :=
  ⟨PNat.mul_le_mul_left _, PNat.le_of_mul_le_mul_left⟩

protected theorem mul_le_mul_right (a : PNat) {b c : PNat} : b ≤ c → b * a ≤ c * a := by
  toNat mul_le_mul_right

protected theorem le_of_mul_le_mul_right {a b c : PNat} : a * b ≤ c * b → a ≤ c := by
  rw [PNat.mul_comm a, PNat.mul_comm c]; apply PNat.le_of_mul_le_mul_left

protected theorem mul_le_mul_iff_right {a b c : PNat} : b ≤ c ↔ b * a ≤ c * a :=
  ⟨PNat.mul_le_mul_right _, PNat.le_of_mul_le_mul_right⟩

protected theorem le_mul_left (a b : PNat) : a ≤ b * a := by
  have h := PNat.mul_le_mul_right a (PNat.one_le b)
  rwa [PNat.one_mul] at h

protected theorem le_mul_right (a b : PNat) : a ≤ a * b := by
  have h := PNat.mul_le_mul_left a (PNat.one_le b)
  rwa [PNat.mul_one] at h

protected theorem mul_lt_mul_left (a : PNat) {b c : PNat} : b < c → a * b < a * c := by
  toNat; intro h; apply Nat.mul_lt_mul_of_pos_left h a.zero_lt

protected theorem lt_of_mul_lt_mul_left {a b c : PNat} : a * b < a * c → b < c := by
  simp only [←PNat.not_le]; apply mt; apply PNat.mul_le_mul_left

protected theorem mul_lt_mul_iff_left {a b c : PNat} : b < c ↔ a * b < a * c :=
  ⟨PNat.mul_lt_mul_left _, PNat.lt_of_mul_lt_mul_left⟩

protected theorem mul_lt_mul_right (a : PNat) {b c : PNat} : b < c → b * a < c * a := by
  toNat; intro h; apply Nat.mul_lt_mul_of_pos_right h a.zero_lt

protected theorem lt_of_mul_lt_mul_right {a b c : PNat} : a * b < c * b → a < c := by
  simp only [←PNat.not_le]; apply mt; apply PNat.mul_le_mul_right

protected theorem mul_lt_mul_iff_right {a b c : PNat} : b < c ↔ b * a < c * a :=
  ⟨PNat.mul_lt_mul_right _, PNat.lt_of_mul_lt_mul_right⟩

protected theorem mul_lt_mul_of_le_of_lt {a b c d : PNat} : a ≤ b → c < d → a * c < b * d := by
  intro hle hlt
  apply PNat.lt_of_le_of_lt
  apply PNat.mul_le_mul_right _ hle
  apply PNat.mul_lt_mul_left _ hlt

protected theorem mul_lt_mul_of_lt_of_le {a b c d : PNat} : a < b → c ≤ d → a * c < b * d := by
  intro hlt hle
  apply PNat.lt_of_lt_of_le
  apply PNat.mul_lt_mul_right _ hlt
  apply PNat.mul_le_mul_left _ hle

protected theorem mul_lt_mul {a b c d : PNat} : a < b → c < d → a * c < b * d := by
  intro h₁ h₂
  apply PNat.lt_trans
  apply PNat.mul_lt_mul_right _ h₁
  apply PNat.mul_lt_mul_left _ h₂

protected theorem lt_mul_left_of_one_lt (a : PNat) : 1 < b → a < b * a := by
  intro h; have h := PNat.mul_lt_mul_right a h
  rwa [PNat.one_mul] at h

protected theorem lt_mul_right_of_one_lt (a : PNat) : 1 < b → a < a * b := by
  intro h; have h := PNat.mul_lt_mul_left a h
  rwa [PNat.mul_one] at h

protected theorem eq_one_of_mul_eq_one_left {a b : PNat} (h : a * b = 1) : a = 1 := by
  match a, b with
  | ⟨1,_⟩, _ => rfl
  | ⟨_+2,_⟩, ⟨_+1,_⟩ => simp [PNat.toNat_mul, PNat.ext_iff, Nat.mul_succ, Nat.add_succ] at h

protected theorem eq_one_of_mul_eq_one_right {a b : PNat} (h : a * b = 1) : b = 1 := by
  match a, b with
  | _, ⟨1, _⟩ => rfl
  | ⟨_+1,_⟩, ⟨_+2,_⟩ => simp [PNat.toNat_mul, PNat.ext_iff, Nat.succ_mul, Nat.add_succ] at h

protected theorem mul_eq_one_iff {a b : PNat} : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨PNat.eq_one_of_mul_eq_one_left h, PNat.eq_one_of_mul_eq_one_right h⟩,
    fun ⟨h₁, h₂⟩ => by rw [h₁, h₂, PNat.mul_one]⟩

/-! ## Exponentiation -/

-- Fix for  https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

@[simp] protected theorem one_pow (a : Nat) : (1 : PNat) ^ a = 1 := by
  toNat one_pow

@[simp] protected theorem pow_zero (a : PNat) : a ^ 0 = 1 := by
  toNat pow_zero

@[simp] protected theorem pow_one (a : PNat) : a ^ 1 = a := by
  toNat pow_one

protected theorem pow_two (a : PNat) : a ^ 2 = a * a := by
  toNat pow_two

protected theorem pow_add (a : PNat) (b c : Nat) : a ^ (b + c) = a ^ b * a ^ c := by
  toNat pow_add

protected theorem mul_pow (a b : PNat) (c : Nat) : (a * b) ^ c = a ^ c * b ^ c := by
  toNat mul_pow

protected theorem pow_mul (a : PNat) (b c : Nat) : a ^ (b * c) = (a ^ b) ^ c := by
  toNat pow_mul

protected theorem pow_mul' (a : PNat) (b c : Nat) : a ^ (b * c) = (a ^ c) ^ b := by
  toNat pow_mul'

protected theorem pow_right_comm (a : PNat) (b c : Nat) : (a ^ b) ^ c = (a ^ c) ^ b := by
  toNat pow_right_comm

protected theorem pow_le_pow_left (a : PNat) {b c : Nat} : b ≤ c → a ^ b ≤ a ^ c := by
  toNat; apply Nat.pow_le_pow_of_le_right a.zero_lt

protected theorem pow_le_pow_right (a : Nat) {b c : PNat} : b ≤ c → b ^ a ≤ c ^ a := by
  toNat; intro h; apply Nat.pow_le_pow_of_le_left h

protected theorem pow_lt_pow_left_of_one_lt {a : PNat} : ∀ {b c : Nat}, b < c → 1 < a → a ^ b < a ^ c
  | 0, c+1, _, h1 => by
    simp [PNat.pow_add]
    apply PNat.lt_of_le_of_lt
    apply PNat.one_le (a ^ c)
    apply PNat.lt_mul_right_of_one_lt _ h1
  | b+1, c+1, h, h1 => by
    simp [PNat.pow_add]
    apply PNat.mul_lt_mul_right
    exact PNat.pow_lt_pow_left_of_one_lt (Nat.lt_of_succ_lt_succ h) h1

protected theorem pow_lt_pow_right_of_zero_lt : ∀ {a : Nat} {b c : PNat}, b < c → 0 < a → b ^ a < c ^ a
  | a+1, b, c, h, _ => by
    simp [PNat.pow_add]
    apply PNat.mul_lt_mul_of_le_of_lt _ h
    exact PNat.pow_le_pow_right _ (Nat.le_of_lt h)

end PNat

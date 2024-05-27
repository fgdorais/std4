/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/-- `Union` captures a value of arbitrary type from the indexed family `type`. -/
structure Union {κ : Type _} (α : κ → Type _) where
  /-- Type of the object. -/
  {idx : κ}
  /-- Value of the object. -/
  val : α idx

namespace Union

@[ext]
protected theorem ext : {a b : Union type} → a.idx = b.idx → HEq a.val b.val → a = b
  | {..}, {..}, rfl, .rfl => rfl

/-- Type of an `Union` object. -/
protected abbrev type (a : Union α) : Type _ := α a.idx

/-- Casts an `Union` object to  a value of compatible type. -/
protected def cast : (a : Union α) → a.type = β → β
  | {val := a}, rfl => a

/-- Casts an `Union` object to  a value of compatible index. -/
protected def castIdx : (a : Union α) → a.idx = i → α i
  | {val := a}, rfl => a

@[simp]
theorem mk_val (a : Union type) : ⟨a.val⟩ = a := rfl

@[simp]
theorem cast_heq_val : (a : Union α) → (h : a.type = β) → HEq (a.cast h) a.val
  | {..}, rfl => .rfl

@[simp]
theorem castIdx_heq_val : (a : Union α) → (h : a.idx = i) → HEq (a.castIdx h) a.val
  | {..}, rfl => .rfl

/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
eleased under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Std

/-- General stream class -/
protected class Stream (m : outParam (Type _ → Type _)) (σ : Type _) (α : outParam (Type _)) where
  /-- Get the next stream element -/
  next : σ → m (α × σ)

/-- `Std.Stream` instances from core `Stream` -/
instance (priority := low) [Monad m] [Stream σ α] : Std.Stream (OptionT m) σ α where
  next s : m (Option (α × σ)) := pure <| Stream.next? s

/-- `ForIn` implementation for `Std.Stream` -/
protected partial def Stream.forIn [Monad m] [Std.Stream (OptionT m) σ α]
  (s : σ) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  let _ : Inhabited (m β) := ⟨pure b⟩
  let rec visit (s : σ) (b : β) : m β := do
    match ← (Stream.next s : m (Option (α × σ))) with
    | some (a, s) =>
      match (← f a b) with
      | ForInStep.done b  => return b
      | ForInStep.yield b => visit s b
    | none => return b
  visit s b

/-- `ForIn` instance for `Std.Stream` -/
instance (priority := low) [Monad m] [Std.Stream (OptionT m) σ α] : ForIn m σ α where
  forIn := Stream.forIn

/-- Byte stream instance for `IO.FS.Stream` -/
instance : Std.Stream (OptionT IO) IO.FS.Stream UInt8 where
  next s : IO (Option (UInt8 × IO.FS.Stream)) := do
    let bs ← s.read 1
    if h : bs.size > 0 then
      return some (bs.get ⟨0,h⟩, s)
    else
      return none

/-- Line stream instance for `IO.FS.Stream` -/
instance : Std.Stream (OptionT IO) IO.FS.Stream String where
  next s : IO (Option (String × IO.FS.Stream)) := do
    let ln ← s.getLine
    if ln.length > 0 then
      return some (ln.dropRightWhile (·=='\n'), s)
    else
      return none

end Std

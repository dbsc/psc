import Test.Funs

open Primitives
open Result
open test

@[pspec] -- the [pspec] attribute saves the theorem in a database, for [progress] to use it
theorem mul2_add1_spec (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1.mul2_add1 x = ret y ∧
  ↑ y = 2 * ↑x + (1 : Int)
  := by
  rw [test.mul2_add1.mul2_add1]
  -- progress with U32.add_spec as ⟨ x1 ⟩
  progress as ⟨ x1 .. ⟩ -- [progress] automatically lookups [U32.add_spec]
  progress as ⟨ x2 .. ⟩ -- same
  simp at *; scalar_tac

import Test.Funs

open Primitives
open Result
open test

namespace test

namespace arithmetics

def BigInt.valImpl (l : List U64) : Int :=
  match l with
  | a::b => a.val + (valImpl b) * (2 ^ 64)
  | [] => 0

def BigInt.val {N : Usize} (x : BigInt N) : Int := valImpl x.num.val

def BigInt.max_value (N : Usize) : Int := (U64.max + 1) ^ (Int.toNat N.val) - 1

theorem adc_for_add_with_carry_spec (a : U64) (b : U64) (carry : U8) :
  match adc_for_add_with_carry a b carry with
  | ret new_carry => new_carry = (a.val + b.val + carry.val) / (2 ^ 64)
  | _ => ⊥
  := by sorry

theorem adc_for_add_with_carry_back_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_a, adc_for_add_with_carry_back a b carry = .ret new_a ∧
  new_a = (a.val + b.val + carry.val) * 2 ^ 64 := by sorry


lemma add_with_carry_overflow : 
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b, arithmetics.BigInt.add_with_carry N self other = .ret b ∧
  ¬b ↔ self.val + other.val ≤ BigInt.max_value N := sorry
    -- by unfold arithmetics.BigInt.add_with_carry

lemma add_with_carry_correct :
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ v, arithmetics.BigInt.add_with_carry_back N self other = .ret v ∧
  v.val = (self.val + other.val) % (BigInt.max_value N) := sorry

end arithmetics

end test

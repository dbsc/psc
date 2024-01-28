import Test.Funs
import Base

open Primitives
open Result
open test

namespace test

namespace arithmetics

def BigInt.valImpl [Inhabited U64] (l : List U64) : Int :=
  if l.len = 0
  then 0
  else (l.index 0) + (valImpl (l.idrop 1)) * (2 ^ 64)
termination_by BigInt.valImpl l => l.len.toNat
decreasing_by
  simp_wf
  have : 1 ≤ l.len := by scalar_tac
  simp [Int.toNat_sub_of_le, *]
  sorry


-- def BigInt.valImpl (l : List U64) : Int :=
--   match l with
--   | a::b => a.val + (valImpl b) * (2 ^ 64)
--   | [] => 0

def BigInt.val {N : Usize} [Inhabited U64] (x : BigInt N) : Int := valImpl x.num.val

def BigInt.max_value [Inhabited U64] (N : Usize) : Int := (U64.max + 1) ^ (Int.toNat N.val) - 1

lemma tmp: 
  ∀ (N : Usize) (self : arithmetics.BigInt N),
  self.num.val.len = N.val := by intro N; intro self; simp [List.len_eq_length]; sorry

theorem adc_for_add_with_carry_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_carry, adc_for_add_with_carry a b carry = .ret new_carry ∧ 
  new_carry = (a.val + b.val + carry.val) / (2 ^ 64) := by sorry

theorem adc_for_add_with_carry_back_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_a, adc_for_add_with_carry_back a b carry = .ret new_a ∧
  new_a = (a.val + b.val + carry.val) % 2 ^ 64 := by sorry


lemma add_with_carry_overflow [Inhabited U64] : 
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b, arithmetics.BigInt.add_with_carry N self other = .ret b ∧
  ¬b ↔ self.val + other.val ≤ BigInt.max_value N := sorry
    -- by unfold arithmetics.BigInt.add_with_carry

lemma add_with_carry_correct [Inhabited U64] :
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ v, arithmetics.BigInt.add_with_carry_back N self other = .ret v ∧
  v.val = (self.val + other.val) % (BigInt.max_value N) := by
    simp [arithmetics.BigInt.add_with_carry_back]
    intro N
    if hx : N = 1#usize then
      rw [hx]
      intro self other
      simp 
      progress with Array.index_usize_spec as ⟨ i, hi ⟩
      progress with Array.index_usize_spec as ⟨ i0, hi0 ⟩
      progress with adc_for_add_with_carry_back_spec as ⟨ i1, hi1 ⟩
      progress with Array.update_usize_spec as ⟨ a1, ha1 ⟩
      simp [BigInt.val, BigInt.max_value]
      have h_self_val : i = self.val := by simp [hi, BigInt.val]; unfold BigInt.valImpl; simp [tmp, *]; unfold BigInt.valImpl; simp [tmp, *];
      have h_bi_1_val : ∀ (bi : arithmetics.BigInt 1#usize), BigInt.valImpl bi.num.val = (bi.num.val).index 0#usize.val  := by intros; simp [hi, BigInt.val]; unfold BigInt.valImpl; simp [tmp, *]; unfold BigInt.valImpl; simp [tmp, *];
      simp [h_bi_1_val]
      simp [ha1]
      unfold BigInt.valImpl
      simp []
      sorry
    else 
    sorry

end arithmetics

end test

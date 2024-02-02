import Test.Funs
import Base

open Primitives
open Result
open test

namespace test

namespace arithmetics

def BigInt.valImpl (l : List U64) : Int :=
  match l with
  | a::b => a.val + (valImpl b) * (2 ^ 64)
  | [] => 0

@[simp]
lemma tmp : Inhabited U64 := by
  constructor
  apply 0#u64

-- Biggest part by Son Ho
lemma BigInt.update_eq [Inhabited U64] (l : List U64) (i : Int) (x : U64)
  (h0 : 0 ≤ i) (h1 : i < l.len) :
  BigInt.valImpl (l.update i x) = BigInt.valImpl l + (x - l.index i) * ((2 ^ 64) ^ i.toNat) := by
  match l with
  | [] =>
    -- Contradiction: 0 ≤ i ∧ i < 0
    simp at h1
    scalar_tac
  | h :: tl =>
    simp at *
    if i = 0 then
      simp [*] -- By writing [*] I'm using the hypothesis i = 0
      unfold valImpl
      scalar_tac
    else
      have hnz : i ≠ 0 := by scalar_tac
      -- This uses update_nzero_cons and index_nzero_cons
      simp [*] -- By writing [*] I'm using the hypothesis i ≠ 0
      unfold valImpl
      -- Recursive call
      have heq := update_eq tl (i - 1) x (by scalar_tac) (by scalar_tac)
      rw [heq]
      rw [add_mul]
      simp []
      have hexpr (y : Int) : y * (2 ^ 64) ^ (Int.toNat i - 1) * 2 ^ 64 = y * (2 ^ 64) ^ Int.toNat i := by {
        rw [←pow_mul]
        rw [mul_assoc]
        simp []
        rw [←pow_add]
        rw [←pow_mul]
        rw [Nat.mul_sub_left_distrib]
        rw [←Nat.sub_add_comm]
        simp [*]
        have hgone : i ≥ 1 := by scalar_tac
        simp [hgone, *]
      }
      rw [hexpr]
      simp [add_assoc]


lemma BigInt.len_spec
  (N : Usize) (self : arithmetics.BigInt N) :
  self.num.val.len = N.val := by
  have h := self.num.property
  rw [List.len_eq_length]
  apply h

def BigInt.val {N : Usize} [Inhabited U64] (x : BigInt N) : Int := valImpl x.num.val

def BigInt.mod_value (N : Usize) : Int := (U64.max + 1) ^ (Int.toNat N.val)

def BigInt.max_value (N : Usize) : Int := BigInt.mod_value N - 1

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

-- Biggest part by Son Ho
lemma add_with_carry_correct [Inhabited U64] :
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ v, arithmetics.BigInt.add_with_carry_back N self other = .ret v ∧
  v.val = (self.val + other.val) % (BigInt.mod_value N) := by
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
      -- have h_self_val : i = self.val := by simp [hi, BigInt.val]; unfold BigInt.valImpl; simp [tmp, *]; unfold BigInt.valImpl; simp [tmp, *];
      have h_bi_1_val : ∀ (bi : arithmetics.BigInt 1#usize), BigInt.valImpl bi.num.val = (bi.num.val).index 0#usize.val  := by intros; simp [hi, BigInt.val]; unfold BigInt.valImpl; sorry
      -- Proving that a1.val.len = 1 (remark: scalar_tac does it automatically)
      -- have h_array := a1.property
      have h_valImpl := BigInt.update_eq self.num.val 0 i1 (by simp) (by scalar_tac)
      simp [h_bi_1_val]
      simp [ha1]
      rw [h_valImpl]
      simp
      -- Because length = 1
      have hself : BigInt.valImpl self.num.val = (self.num.val.index 0).val := by unfold BigInt.valImpl; sorry
      rw [hself]
      
      rw [hi1]
      
      have h64 : BigInt.mod_value 1#usize = 2 ^ 64 := by unfold BigInt.mod_value; simp []
      rw [h64]
      -- Finishing the proof
      rw [hi0]
      simp
      rw [hi]
      simp
    else
      sorry

end arithmetics

end test

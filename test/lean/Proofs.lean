import Test.Funs
import Base

open Primitives
open Result
open test

namespace test

namespace arithmetics

attribute [-simp] Bool.exists_bool

def BigInt.valImpl (l : List U64) : Int :=
  match l with
  | a::b => a.val + (valImpl b) * (2 ^ 64)
  | [] => 0

lemma valImpl_ge_zero (l : List U64) : BigInt.valImpl l ≥ 0 := by
  unfold BigInt.valImpl
  match l with
  | a::b => {
    have ha : 0 ≤ a.val := by scalar_tac
    have hb : 0 ≤ BigInt.valImpl b * 2 ^ 64 := by simp[valImpl_ge_zero]
    have hc := Int.add_le_add ha hb
    simp at hc
    simp [*]
  }
  | [] => simp

@[simp]
lemma tmp : Inhabited U64 := by
  constructor
  apply 0#u64

-- Biggest part by Son Ho
lemma BigInt.update_eq (l : List U64) (i : Int) (x : U64)
  (h0 : 0 ≤ i) (h1 : i < l.len) :
  BigInt.valImpl (l.update i x) = BigInt.valImpl l + (x - l.index i) * ((2 ^ 64) ^ i.toNat) := by
  match l with
  | [] =>
    -- Contradiction: 0 ≤ i ∧ i < 0
    simp at h1
    scalar_tac
  | h :: tl =>
    simp at h1
    if i = 0 then
      simp [*] -- By writing [*] I'm using the hypothesis i = 0
      unfold valImpl
      scalar_tac
    else
      have hnz : i ≠ 0 := by scalar_tac
      -- This uses update_nzero_cons and index_nzero_cons
      simp only [h1, hnz, ne_eq, not_false_eq_true, List.update_nzero_cons, List.index_nzero_cons] -- By writing [*] I'm using the hypothesis i ≠ 0
      unfold valImpl
      -- Recursive call
      have heq := update_eq tl (i - 1) x (by scalar_tac) (by scalar_tac)
      rw [heq]
      rw [add_mul]
      simp only [Int.pred_toNat]
      have hexpr : ((2: Int) ^ 64) ^ (Int.toNat i - 1) * 2 ^ 64 = (2 ^ 64) ^ Int.toNat i := by {
        rw [←pow_mul]
        rw [←pow_add]
        rw [←pow_mul]
        rw [Nat.mul_sub_left_distrib]
        rw [←Nat.sub_add_comm]
        simp [*]
        have hgone : i ≥ 1 := by scalar_tac
        simp [hgone, *]
      }
      simp only [mul_assoc]
      rw [hexpr]
      simp [add_assoc]


@[simp] lemma BigInt.len_spec
  (N : Usize) (self : arithmetics.BigInt N) :
  (self.num.val).len = N.val := by
  have h := self.num.property
  rw [List.len_eq_length]
  apply h

def BigInt.val {N : Usize} (x : BigInt N) : Int := valImpl x.num.val

def BigInt.mod_value (n : Int) : Int := (U64.max + 1) ^ (Int.toNat n)

def BigInt.max_value (n : Int) : Int := BigInt.mod_value n - 1

lemma BigInt.mod_value_add_one (n : Int) (hn : 0 ≤ n) : BigInt.mod_value n * (2 ^ 64) = BigInt.mod_value (n + 1) := by
  rw [BigInt.mod_value]
  rw [BigInt.mod_value]
  rw [U64.max]
  simp
  rw [mul_comm]
  rw [←pow_succ]
  simp []
  have hf := Int.toNat_add_nat hn 1
  rw [←hf]
  simp

lemma valImpl_lt_mod (l : List U64) : BigInt.valImpl l < BigInt.mod_value l.len := by
  unfold BigInt.valImpl
  match h : l with
  | a::b => {
    simp only [List.len_cons, gt_iff_lt]
    have ha := valImpl_lt_mod b
    have hb : a.val < 2 ^ 64 := by scalar_tac
    have hc := Int.le_sub_one_of_lt ha
    have hd : 1 + b.len = b.len + 1 := by scalar_tac
    have hf : (0 : Int) ≤ 2 ^ 64 := by simp 
    have hg := Int.mul_le_mul_of_nonneg_right hc hf
    simp only [Int.sub_mul] at hg
    simp only [one_mul] at hg
    have hh := add_lt_add_of_le_of_lt hg hb
    simp only [sub_add_cancel] at hh
    rw [Int.add_comm] at hh
    rw [hd]
    rw [←BigInt.mod_value_add_one]
    simp only [hh]
    scalar_tac
  }
  | [] => {
    simp
    unfold BigInt.mod_value
    simp
  }


lemma BigInt.val_lt_mod (N : Usize) (bn : Array U64 N) : BigInt.valImpl bn.val < BigInt.mod_value N.val := by
  have hi := valImpl_lt_mod bn.val
  have he := bn.property
  simp [*, List.len_eq_length] at hi
  simp [*]

theorem adc_for_add_with_carry_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_carry r, adc_for_add_with_carry a b carry = .ret (new_carry, r) ∧ 
  new_carry = (a.val + b.val + carry.val) / (2 ^ 64) ∧
  r = (a.val + b.val + carry.val) % 2 ^ 64 := by sorry


lemma add_with_carry_overflow [Inhabited U64] : 
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b val, arithmetics.BigInt.add_with_carry N self other = .ret (b, val) ∧
  ¬b ↔ self.val + other.val ≤ BigInt.max_value N := sorry

lemma BigInt.ha_0_val (N: Usize) (bi : Array U64 N) : N = 0#usize → BigInt.valImpl bi.val = 0 := 
by {
      unfold BigInt.valImpl;
      intro hN;
      have h := bi.property;
      match hq0 : bi.val with
        | [] => scalar_tac;
        | hd :: tl => {
            simp [BigInt.len_spec, hN, List.len_eq_length, *] at h; scalar_tac;
        }
  }

lemma BigInt.h_1_val (N: Usize) (bi : arithmetics.BigInt N) : N = 1#usize → BigInt.valImpl bi.num.val = (bi.num.val).index 0#usize.val  := 
by {
        simp [BigInt.val]; 
        unfold BigInt.valImpl;
        have h := BigInt.len_spec N bi;
        match hq0 : bi.num.val with
        | [] => simp [List.len_nil, Usize.ofInt_val_eq, hq0] at h; scalar_tac;
        | hd :: tl => {
          simp []
          unfold BigInt.valImpl
          match hq1 : tl with
          | [] => simp [];
          | hd::tl2 => simp [*, List.len_eq_length] at h; scalar_tac;
        }
      }

lemma BigInt.slice_eq (l : List U64) (i : Int) (N : Int)
  (h0 : 0 ≤ i) (h1 : i < N) (h2 : N ≤ l.len) :
  BigInt.valImpl (l.slice i N) = (2 ^ 64) * BigInt.valImpl (l.slice (i + 1) N) + (l.index i) := by
    match l with
    | h::tl => {
      if hi : i = 0
      then {
        rw [hi]
        simp only [zero_add, ne_eq, zero_ne_one, not_false_eq_true, neq_imp,
          List.slice_nzero_cons, sub_self, List.index_zero_cons]
        rw [List.slice]
        simp only [sub_zero, List.idrop_zero]
        rw [List.itake]
        have h3 := lt_of_le_of_lt h0 h1
        have h4 := ne_of_lt h3
        simp only [h4, not_false_eq_true, neq_imp, ↓reduceIte]
        rw [valImpl]
        rw [add_comm]
        rw [mul_comm]
        rw [List.slice]
        simp
      }
      else {
        have hi1 : i + 1 ≠ 0 := by scalar_tac
        simp only [ne_eq, not_false_eq_true, List.slice_nzero_cons, List.index_nzero_cons, hi, hi1]
        rw [BigInt.slice_eq]
        simp
        scalar_tac
        scalar_tac
        simp [*] at h2
        rw [add_comm] at h2
        simp [*]
      }
    }
    | [] => {
      simp at h2
      have h3 := lt_of_le_of_lt h0 h1
      have h4 := not_le_of_lt h3
      simp [h2] at h4
    }

lemma BigInt.mod_value_eq (n : Int) : BigInt.mod_value n = (2 ^ 64) ^ n.toNat := by
  rw [BigInt.mod_value]
  rw [U64.max]
  simp
  
lemma add_with_carry_loop_correct :
  ∀ (N : Usize) (self : Array U64 N) (other : Array U64 N) (carry : U8) (i : Usize) (h : i ≤ N),
  ∃ b v, arithmetics.BigInt.add_with_carry_loop N self other carry i = .ret (b, v) ∧
  (BigInt.valImpl v.val) = (BigInt.valImpl self.val + (BigInt.mod_value i.val) * (BigInt.valImpl (other.val.slice i.val N.val) + carry.val)) % (BigInt.mod_value N.val) := by
    intro N
    intro self other
    intro carry
    intro i
    intro h
    rw [BigInt.add_with_carry_loop]
    if hind : (N.val - i.val).toNat = 0 then
      have hieqN : i = N := by {
        simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add] at hind; 
        simp [Scalar.le_equiv] at h
        scalar_tac
      }
      simp only [hieqN, Scalar.lt_equiv, lt_self_iff_false, ↓reduceIte, ret.injEq, Prod.mk.injEq,
        Int.add_mul_emod_self_left]
      exists (carry != 0#u8), self
      have modh := Int.emod_eq_of_lt (valImpl_ge_zero self.val) (BigInt.val_lt_mod N self)
      simp only [and_self, true_and]
      simp [*]
    else
      have hiltN : i < N := by {
        simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, not_le] at hind 
        simp [Scalar.lt_equiv]
        scalar_tac
      }
      simp only [hiltN, lt_self_iff_false, ↓reduceIte]

      progress with Array.index_mut_usize_spec as ⟨ i1, hi1, hi1d, hi1a ⟩
      progress with Array.index_usize_spec as ⟨ i2, hi2 ⟩
      progress with adc_for_add_with_carry_spec as ⟨ i3, hi3, hi3d, hi3a ⟩
      progress as ⟨ w1, hw1 ⟩
      simp only [hi1a, hi3a]
      progress with Array.update_usize_spec as ⟨ a1, ha1 ⟩
      progress with add_with_carry_loop_correct as ⟨ i4, hi4, hi4d ⟩
      . scalar_tac
      exists i4, hi4
      simp only [true_and]
      rw [hi4d]
      -- rw [hi3d]
      rw [ha1]
      -- rw [hi1d]
      -- rw [hi2]
      rw [BigInt.update_eq]
      -- have hEliminSelf {m : Int} {k : Int} := @Int.emod_add_cancel_left m (BigInt.mod_value N) k (BigInt.valImpl self.val)
      rw [add_assoc]
      rw [Int.emod_add_cancel_left]
      have hOldSlice := BigInt.slice_eq other.val i.val N.val (by scalar_tac) (by scalar_tac) (by scalar_tac)
      -- rw [BigInt.slice_eq]

      rw [hOldSlice]

      rw [hw1]
      -- rw [hi3a]
      -- rw [hi2]
      -- rw [hi3d]
      simp only [Scalar.ofInt_val_eq]
      simp only [Int.mul_add]
      rw [←Int.mul_assoc]
      rw [BigInt.mod_value_add_one]
      rw [Int.add_comm]
      rw [Int.add_assoc]
      rw [Int.add_assoc]
      rw [Int.emod_add_cancel_left]
      rw [←BigInt.mod_value_add_one]
      rw [←BigInt.mod_value_eq]
      rw [Int.mul_assoc]
      have htmp : (hi3.val - ((self.val).index i.val).val) * BigInt.mod_value i.val = BigInt.mod_value i.val * (hi3.val - ((self.val).index i.val).val) := by simp [Int.mul_comm]
      rw [htmp]
      rw [←Int.mul_add]
      rw [←Int.mul_add]
      rw [hi3d]
      rw [hi3a]
      rw [←add_sub_assoc]
      rw [Int.ediv_add_emod]
      have htmp1 : i1.val + i2.val + carry.val = i2.val + carry.val + i1.val := by scalar_tac
      rw [htmp1]
      rw [hi1d]
      rw [add_sub_assoc]
      simp only [sub_self, add_zero]

      rw [hi2]
      --------------------------------------------

      scalar_tac
      scalar_tac
      scalar_tac
      scalar_tac
termination_by (N.val - i.val).toNat
decreasing_by
  simp_wf
  rw [hw1]
  simp [sub_add_eq_sub_sub, *]
  -- scalar_decr_tac


lemma full_itake (l : List α) (N: Int) (h : N = l.len): List.itake N l = l := by
  unfold List.itake;
  match hl : l with
  | [] => simp [hl];
  | hs::tl => {
    if hn : N = 0 then
      simp at h;
      scalar_tac;
    else
      simp only [hn, not_false_eq_true, neq_imp, ↓reduceIte, List.cons.injEq, true_and];
      simp [full_itake, *]
  }

lemma full_slice (l : List α) (N: Int) (h : N = l.len): List.slice 0 N l = l := by
  unfold List.slice
  simp only [sub_zero, List.idrop_zero]
  simp only [full_itake, h]


lemma add_with_carry_correct :
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b v, arithmetics.BigInt.add_with_carry N self other = .ret (b, v) ∧
  v.val = (self.val + other.val) % (BigInt.mod_value N.val) := by
    intro N
    intro self other
    simp only [arithmetics.BigInt.add_with_carry]
    progress with add_with_carry_loop_correct as ⟨ i, hi, hid ⟩
    . scalar_tac
    exists i, { num := hi }
    simp only [true_and] 
    unfold BigInt.mod_value at hid
    simp only [Scalar.ofInt_val_eq, Int.toNat_zero, pow_zero, one_mul] at hid
    have other_full_slice : List.slice 0 N.val other.num.val = other.num.val := by simp only [BigInt.len_spec, full_slice]
    simp only [other_full_slice] at hid 
    unfold BigInt.val
    unfold BigInt.mod_value
    simp [*]

end arithmetics

end test

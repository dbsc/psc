import Test.Funs
import Base

open Primitives
open Result

namespace test

namespace biginteger

attribute [-simp] Bool.exists_bool

def valImpl (l : List U64) : Int :=
  match l with
  | a::b => a.val + (valImpl b) * (2 ^ 64)
  | [] => 0

lemma valImpl_ge_zero (l : List U64) : valImpl l ≥ 0 := by
  unfold valImpl
  match l with
  | a::b => {
    have ha : 0 ≤ a.val := by scalar_tac
    have hb : 0 ≤ valImpl b * 2 ^ 64 := by simp[valImpl_ge_zero]
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
  valImpl (l.update i x) = valImpl l + (x - l.index i) * ((2 ^ 64) ^ i.toNat) := by
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
  (N : Usize) (self : biginteger.BigInt N) :
  (self.val).len = N.val := by
  have h := self.property
  rw [List.len_eq_length]
  apply h

def BigInt.val {N : Usize} (x : biginteger.BigInt N) : Int := valImpl x.v

def BigInt.mod_value (n : Int) : Int := (U64.max + 1) ^ (Int.toNat n)

def BigInt.max_value (n : Int) : Int := BigInt.mod_value n - 1

lemma BigInt.mod_value_add_one (n : Int) (hn : 0 ≤ n) : BigInt.mod_value n * (2 ^ 64) = BigInt.mod_value (n + 1) := by
  rw [BigInt.mod_value]
  rw [BigInt.mod_value]
  rw [U64.max]
  simp
  -- rw [mul_comm]
  rw [←pow_succ]
  -- simp []
  have hf := Int.toNat_add_nat hn 1
  rw [←hf]
  simp

lemma valImpl_lt_mod (l : List U64) : valImpl l < BigInt.mod_value l.len := by
  unfold valImpl
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

lemma BigInt.val_lt_mod (N : Usize) (bn : Array U64 N) : valImpl bn.val < BigInt.mod_value N.val := by
  have hi := valImpl_lt_mod bn.val
  have he := bn.property
  simp [*, List.len_eq_length] at hi
  simp [*]

lemma BigInt.slice_eq (l : List U64) (i : Int) (N : Int)
  (h0 : 0 ≤ i) (h1 : i < N) (h2 : N ≤ l.len) :
  valImpl (l.slice i N) = (2 ^ 64) * valImpl (l.slice (i + 1) N) + (l.index i) := by
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

def bool_to_int (b:Bool) := if b then 0 else 1

end biginteger

end test
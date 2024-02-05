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
        -- simp? []
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

def BigInt.mod_value (N : Usize) : Int := (U64.max + 1) ^ (Int.toNat N.val)

def BigInt.max_value (N : Usize) : Int := BigInt.mod_value N - 1

theorem adc_for_add_with_carry_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_carry r, adc_for_add_with_carry a b carry = .ret (new_carry, r) ∧ 
  new_carry = (a.val + b.val + carry.val) / (2 ^ 64) ∧
  r = (a.val + b.val + carry.val) % 2 ^ 64 := by sorry


lemma add_with_carry_overflow [Inhabited U64] : 
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b val, arithmetics.BigInt.add_with_carry N self other = .ret (b, val) ∧
  ¬b ↔ self.val + other.val ≤ BigInt.max_value N := sorry

lemma BigInt.h_1_val (N: Usize) (bi : arithmetics.BigInt N) : N = 1#usize → BigInt.valImpl bi.num.val = (bi.num.val).index 0#usize.val  := 
by {
        simp [BigInt.val]; 
        unfold BigInt.valImpl;
        have h := BigInt.len_spec N bi;
        -- intro
        -- | ⟨w, bi.num.val = []⟩ => 

        -- cases bi.num.val
        -- . case nil hb => simp at h

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

-- Biggest part by Son Ho
lemma add_with_carry_correct :
  ∀ (N : Usize) (self : arithmetics.BigInt N) (other : arithmetics.BigInt N),
  ∃ b v, arithmetics.BigInt.add_with_carry N self other = .ret (b, v) ∧
  v.val = (self.val + other.val) % (BigInt.mod_value N) := by
    intro N
    intro self other
    simp only [arithmetics.BigInt.add_with_carry]
    if hx : N = 1#usize then
      simp only [hx, Usize.ofInt_val_eq]
      simp only [Scalar.le_equiv, Scalar.ofInt_val_eq, le_refl, ↓reduceIte]
      -- rw [hx]
      progress with Array.index_mut_usize_spec as ⟨ i, hi, hid, hia ⟩
      progress with Array.index_usize_spec as ⟨ i0, hi0 ⟩
      progress with adc_for_add_with_carry_spec as ⟨ i1, hi1, hid1, hia1 ⟩
      simp only [hia, hia1]
      progress with Array.update_usize_spec as ⟨ a1, ha1 ⟩
      simp only [BigInt.val, BigInt.max_value]
      -- have h_self_val : i = self.val := by simp [hi, BigInt.val]; unfold BigInt.valImpl; simp [tmp, *]; unfold BigInt.valImpl; simp [tmp, *];
      -- Proving that a1.val.len = 1 (remark: scalar_tac does it automatically)
      -- have h_array := a1.property
      have h_valImpl := BigInt.update_eq self.num.val 0 hi1 (by simp) (by scalar_tac)

      -- simp [hx] at self
      -- simp [hx] at other
      rw [BigInt.h_1_val]
      simp only [BigInt.h_1_val, hx]
      exists i1 != 0#u8, { num := a1 }
      simp only [and_self, Scalar.ofInt_val_eq, le_refl, BigInt.len_spec, zero_lt_one,
        List.index_update_eq, add_zero, Int.reducePow, true_and]
      simp only [ha1]
      simp only [Scalar.ofInt_val_eq, le_refl]
      -- Because length = 1
      -- have hself : BigInt.valImpl self.num.val = (self.num.val.index 0).val := by unfold BigInt.valImpl; sorry
      -- rw [hself]
      
      simp [List.index_update_eq, hx, BigInt.len_spec]
      rw [hia1]
      
      have h64 : BigInt.mod_value 1#usize = 2 ^ 64 := by unfold BigInt.mod_value; simp [U64.max]
      rw [h64]
      -- Finishing the proof
      rw [hi0]
      rw [hid]
      simp only [Scalar.ofInt_val_eq, add_zero]
      simp only [hx]
    else
      sorry

end arithmetics

end test

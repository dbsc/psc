import Common.Base

open Primitives
open Result

namespace test

namespace biginteger

attribute [-simp] Bool.exists_bool

theorem adc_for_add_with_carry_spec (a : U64) (b : U64) (carry : U8) :
  ∃ new_carry r, biginteger.arithmetic.adc_for_add_with_carry a b carry = .ok (new_carry, r) ∧ 
  new_carry = (a.val + b.val + carry.val) / (2 ^ 64) ∧
  r = (a.val + b.val + carry.val) % 2 ^ 64 := by sorry

lemma add_with_carry_loop_correct :
  ∀ (N : Usize) (self : Array U64 N) (other : Array U64 N) (carry : U8) (i : Usize) (h : i ≤ N),
  ∃ b v, biginteger.BigIntegertestbigintegerBigIntN.add_with_carry_loop N self other carry i = .ok (b, v) ∧
  (valImpl v.v) = (valImpl self.val + (BigInt.mod_value i.val) * (valImpl (other.val.slice i.val N.val) + carry.val)) % (BigInt.mod_value N.val) := by
    intro N
    intro self other
    intro carry
    intro i
    intro h
    rw [biginteger.BigIntegertestbigintegerBigIntN.add_with_carry_loop]
    if hind : (N.val - i.val).toNat = 0 then
      have hieqN : i = N := by {
        simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add] at hind; 
        simp [Scalar.le_equiv] at h
        scalar_tac
      }
      simp only [hieqN, Scalar.lt_equiv, lt_self_iff_false, ↓reduceIte, ok.injEq, Prod.mk.injEq,
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
      -- have hEliminSelf {m : Int} {k : Int} := @Int.emod_add_cancel_left m (BigInt.mod_value N) k (valImpl self.val)
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
  apply Arith.to_int_sub_to_nat_lt
  simp [sub_one_lt, Int.toNat_sub, Int.toNat_sub_of_le, h, *]
  scalar_tac
  simp [sub_one_lt, *]

lemma add_with_carry_correct :
  ∀ (N : Usize) (self : BigInt N) (other : BigInt N),
  ∃ b v, biginteger.BigIntegertestbigintegerBigIntN.add_with_carry N self other = .ok (b, v) ∧
  v.val = (self.val + other.val) % (BigInt.mod_value N.val) := by
    intro N
    intro self other
    simp only [biginteger.BigIntegertestbigintegerBigIntN.add_with_carry]
    progress with add_with_carry_loop_correct as ⟨ i, hi, hid ⟩
    . scalar_tac
    exists i, hi
    simp only [true_and] 
    unfold BigInt.mod_value at hid
    simp only [Scalar.ofInt_val_eq, Int.toNat_zero, pow_zero, one_mul] at hid
    have other_full_slice : List.slice 0 N.val other.v = other.v := by simp only [BigInt.len_spec, full_slice]
    simp only [other_full_slice] at hid 
    unfold BigInt.val
    unfold BigInt.mod_value
    simp [*]

lemma add_with_carry_loop_overflow_correct
  (N : Usize) (self : Array U64 N) (other : Array U64 N) (carry : U8) (i : Usize)
  (h : i ≤ N) (hc : carry.val ≤ 1) :
  ∃ b v, biginteger.BigIntegertestbigintegerBigIntN.add_with_carry_loop N self other carry i = .ok (b, v) ∧
  (b ↔ valImpl self.val + (valImpl (other.val.slice i.val N.val) + carry.val)* (BigInt.mod_value i) > BigInt.max_value N) := by
  rw [biginteger.BigIntegertestbigintegerBigIntN.add_with_carry_loop]
  if hind : (N.val - i.val).toNat = 0 then
    have hieqN : i = N := by 
      {
        simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add] at hind; 
        simp [Scalar.le_equiv] at h
        scalar_tac
      }
    simp only [hieqN, Scalar.lt_equiv, lt_self_iff_false, ↓reduceIte, ok.injEq, Prod.mk.injEq,
        Int.add_mul_emod_self_left]
    exists (carry != 0#u8), self
    simp only [and_self, bne_iff_ne, ne_eq, Scalar.neq_to_neq_val, Scalar.ofInt_val_eq, gt_iff_lt,
      true_and]
    rw[List.slice]
    simp
    have he0: valImpl [] =0 :=
     by 
     unfold valImpl
     linarith
    rw[he0]
    simp
    apply Iff.intro
    intro h₀
    have hχ: carry.val=1:=
      by scalar_tac
    rw[hχ]
    simp
    rw [BigInt.max_value]
    have hvg0:=valImpl_ge_zero self.val
    linarith
    intro h₁
    contrapose! h₁
    rw[h₁]
    simp
    have hn: 0 ≤ valImpl self.val:= 
     by exact valImpl_ge_zero self.val
    have h2n: valImpl self.val < BigInt.mod_value N.val := 
     by exact BigInt.val_lt_mod N self
    unfold BigInt.max_value
    linarith
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
   progress with add_with_carry_loop_overflow_correct as ⟨ i4, hi4, hi4d ⟩
   . scalar_tac
   have hii1:i1.val < 2^64 :=
    by .scalar_tac
   have hii2:i2.val < 2^64 :=
    by .scalar_tac
   have hii12:i1.val+i2.val+carry.val<2*2^64:=
    by
    linarith
   have hdivineq : (i1.val+i2.val+carry.val)/2^64<2 :=
    by 
     rw[Int.ediv_lt_iff_lt_mul]
     exact hii12
     linarith
   rw [hi3d]
   linarith
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
   have hOldSlice := BigInt.slice_eq other.val i.val N.val (by scalar_tac) (by scalar_tac) (by scalar_tac)
      -- rw [BigInt.slice_eq]

   rw [hOldSlice]

   rw [hw1]
      -- rw [hi3a]
      -- rw [hi2]
      -- rw [hi3d]
   simp only [Scalar.ofInt_val_eq]
   --simp only [Int.mul_add]
   rw [Int.add_comm]
   rw [Int.add_assoc]
   rw [Int.add_assoc]
   rw [hi3d]
   rw [hi3a]
   have hsep: ((i1.val + i2.val + carry.val) % 2 ^ 64 - ((self.val).index i.val).val) * (2 ^ 64) ^ Int.toNat i.val
   =((i1.val + i2.val + carry.val) % 2 ^ 64)* (2 ^ 64) ^ Int.toNat i.val - (((self.val).index i.val).val) * (2 ^ 64) ^ Int.toNat i.val:=
    by .scalar_tac
   rw [hsep]

   have hsep2:((valImpl (List.slice (i.val + 1) N.val other.val) + (i1.val + i2.val + carry.val) / 2 ^ 64) *
          BigInt.mod_value (i.val + 1))= (valImpl (List.slice (i.val + 1) N.val other.val))*
          BigInt.mod_value (i.val + 1) + ((i1.val + i2.val + carry.val) / 2 ^ 64) *
          BigInt.mod_value (i.val + 1):=
          by .scalar_tac
   rw [hsep2]
   unfold BigInt.mod_value
   have hitn: Int.toNat 1 = 1 :=
      by simp
   have hmax:U64.max+1=2^64:=
      by 
       .scalar_tac
   have h_pow_plus_one: (U64.max + 1) ^ Int.toNat (i.val + 1)=(U64.max + 1) ^ Int.toNat (i.val)*2^64:=
    by 
     rw [Int.toNat_add]
     rw[pow_add]
     rw [hitn]
     rw[hmax]
     linarith
     .scalar_tac
     .scalar_tac
   rw [h_pow_plus_one]
   rw [hmax]
   have hff: (i1.val + i2.val + carry.val) % 2 ^ 64 * (2 ^ 64) ^ Int.toNat i.val -
        ((self.val).index i.val).val * (2 ^ 64) ^ Int.toNat i.val +
      (valImpl (List.slice (i.val + 1) N.val other.val) * ((2 ^ 64) ^ Int.toNat i.val * 2 ^ 64) +
          ((i1.val + i2.val + carry.val) / 2 ^ 64 )* ((2 ^ 64) ^ Int.toNat i.val * 2 ^ 64) +
        valImpl self.val)=((i1.val + i2.val + carry.val) % 2 ^ 64 +((i1.val + i2.val + carry.val) / 2 ^ 64 )* 2 ^ 64 )* ((2 ^ 64) ^ Int.toNat i.val)
         -((self.val).index i.val).val * (2 ^ 64) ^ Int.toNat i.val +
      (valImpl (List.slice (i.val + 1) N.val other.val) * ((2 ^ 64) ^ Int.toNat i.val * 2 ^ 64)+ valImpl self.val):=
       by .scalar_tac
   rw[hff]
   have hmd: (i1.val + i2.val + carry.val) % 2 ^ 64 + (i1.val + i2.val + carry.val) / 2 ^ 64 * 2 ^ 64 =(i1.val + i2.val + carry.val):=
    by 
     have hmdd:= Int.emod_add_ediv (i1.val + i2.val + carry.val) (2^64)
     .scalar_tac
   rw[hmd]
   rw[hi1d,hi2]
   have hfp: (((self.val).index i.val).val + ((other.val).index i.val).val + carry.val) * (2 ^ 64) ^ Int.toNat i.val -
        ((self.val).index i.val).val * (2 ^ 64) ^ Int.toNat i.val +
      (valImpl (List.slice (i.val + 1) N.val other.val) * ((2 ^ 64) ^ Int.toNat i.val * 2 ^ 64) +
        valImpl self.val) = valImpl self.val +
      (2 ^ 64 * valImpl (List.slice (i.val + 1) N.val other.val) + (((other.val).index i.val).val + carry.val)) *
        (2 ^ 64) ^ Int.toNat i.val:=
         by .scalar_tac
   rw [hfp]
   .scalar_tac
   .scalar_tac
  termination_by (N.val - i.val).toNat
    decreasing_by
    simp_wf
    rw [hw1]
    simp [sub_add_eq_sub_sub, *]
    apply Arith.to_int_sub_to_nat_lt
    simp [sub_one_lt, Int.toNat_sub, Int.toNat_sub_of_le, h, *]
    scalar_tac
    simp [sub_one_lt, *]

lemma add_with_carry_overflow [Inhabited U64] : 
  ∀ (N : Usize) (self : BigInt N) (other : BigInt N),
  ∃ b val, biginteger.BigIntegertestbigintegerBigIntN.add_with_carry N self other = .ok (b, val) ∧
  (¬b ↔ self.val + other.val ≤ BigInt.max_value N) :=
by
  intro N₁
  intro s₁ o₁
  simp only [biginteger.BigIntegertestbigintegerBigIntN.add_with_carry]
  progress with add_with_carry_loop_overflow_correct as ⟨ i, hi, hid ⟩
  . scalar_tac
  exists i, hi
  simp
  have other_full_slice : List.slice 0 N₁.val o₁.v = o₁.v := by simp only [BigInt.len_spec, full_slice]
  apply Iff.intro
  intro h₀
  rw [h₀] at hid
  simp at hid
  rw [BigInt.val]
  rw [BigInt.mod_value] at hid
  simp at hid 
  simp only [other_full_slice] at hid
  exact hid
  intro h₁
  simp [BigInt.val] at h₁
  contrapose! h₁
  simp at h₁
  rw [h₁] at hid
  simp at hid
  simp only [other_full_slice] at hid
  rw [BigInt.mod_value] at hid
  simp at hid 
  exact hid

lemma add_with_carry_spec (N : Usize) (self : BigInt N) (other : BigInt N) :
  ∃ b v, biginteger.BigIntegertestbigintegerBigIntN.add_with_carry N self other = .ok (b, v) ∧
  (bool_to_int b) * (BigInt.mod_value N.val) + v.val = self.val + other.val
  := by
  sorry

end biginteger

end test
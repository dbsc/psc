import Common.Base

open Primitives
open Result

namespace test

namespace biginteger

lemma const_is_even_correct :
  ∀ (N : Usize) (self: BigInt N) (h: 0 < N.val),
  ∃ b, biginteger.BigInt.const_is_even N self = .ok b ∧ b = (self.val % 2 = 0) := by {
    intro N self h
    unfold biginteger.BigInt.const_is_even
    progress with Array.index_usize_spec as ⟨ idef, idecl ⟩ 
    progress as ⟨ is_even_def, is_even_decl ⟩
    simp
    rw [Scalar.eq_equiv]
    rw [is_even_decl]
    rw [idecl]
    simp [*]
    unfold BigInt.val
    unfold valImpl
    match h_self : self.v with
    | x::xs => {
      unfold List.index
      simp only [h_self]
      simp only [↓reduceIte]
      rw [Int.add_emod]
      rw [Int.mul_emod]
      simp
    }
    | [] => {
      have h_contr := BigInt.len_spec N self
      simp [h_self] at h_contr
      rw [←h_contr] at h
      simp at h
    }
  }

lemma is_odd_correct :
  ∀ (N : Usize) (self: BigInt N) (h: 0 < N.val),
  ∃ b, biginteger.BigIntegertestbigintegerBigIntN.is_odd N self = .ok b ∧ b = (self.val % 2 = 1) := by {
    intro N self h
    unfold biginteger.BigIntegertestbigintegerBigIntN.is_odd
    progress with Array.index_usize_spec as ⟨ idef, idecl ⟩ 
    simp
    rw [idecl]
    simp [*]
    unfold BigInt.val
    unfold valImpl
    match h_self : self.v with
    | x::xs => {
      unfold List.index
      simp only [h_self]
      simp only [↓reduceIte]
      rw [Int.add_emod]
      rw [Int.mul_emod]
      simp
      sorry
    }
    | [] => {
      have h_contr := BigInt.len_spec N self
      simp [h_self] at h_contr
      rw [←h_contr] at h
      simp at h
    }
  } 

lemma is_even_correct :
  ∀ (N : Usize) (self: BigInt N) (h: 0 < N.val),
  ∃ b, biginteger.BigIntegertestbigintegerBigIntN.is_even N self = .ok b ∧ b = (self.val % 2 = 0) := by {
    intro N self h
    unfold biginteger.BigIntegertestbigintegerBigIntN.is_even
    progress with is_odd_correct as ⟨ idef, idecl ⟩
    simp [*]
    have hemod_2 := Int.emod_two_eq (BigInt.val self)
    cases hemod_2
    . simp [*]
    . simp [*]
  }

lemma slice_i_i (i: Int) : List.slice i i (ls : List α) = [] := by cases ls <;> simp [List.slice]

lemma ind_base (N: Usize) (i: Usize) (h : i ≤ N) (hind : (N.val - i.val).toNat = 0) : i = N := by
    simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add] at hind; 
    simp [Scalar.le_equiv] at h
    scalar_tac

lemma ind_trans (N: Usize) (i: Usize) (h : i ≤ N) (hind : ¬(N.val - i.val).toNat = 0) : i < N := by
    simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add] at hind; 
    simp [Scalar.le_equiv] at h
    scalar_tac

lemma is_zero_loop_correct :
  ∀ (N : Usize) (self: BigInt N) (is_zero: Bool) (i: Usize) (h : i ≤ N),
  biginteger.BigIntegertestbigintegerBigIntN.is_zero_loop N self is_zero i = .ok (is_zero ∧ (valImpl (self.v.slice i.val N) = 0)) := by {
    intro N self is_zero i h
    rw [biginteger.BigIntegertestbigintegerBigIntN.is_zero_loop]
    if hind : (N.val - i.val).toNat = 0 then {
      have hieqN := ind_base N i h hind
      simp [*, slice_i_i]
      unfold valImpl
      simp
    }
    else {
      have hiltN := ind_trans N i h hind
      cases hz : is_zero
      . {
        simp [*]
        progress as ⟨ i1_def, i1_decl ⟩
        simp at i1_decl
        have h_ind_is_zero := is_zero_loop_correct N self false i1_def (by scalar_tac)
        simp at h_ind_is_zero
        simp [*]
      }
      . {
        simp [*]
        progress as ⟨ xi_def, xi_decl ⟩
        progress as ⟨ i1_def, i1_decl ⟩
        have h_ind_is_zero := is_zero_loop_correct N self (xi_def = 0#u64) i1_def (by scalar_tac)
        rw [h_ind_is_zero]
        simp [*]
        rw [←Bool.decide_and, decide_eq_decide]
        have htmp := BigInt.slice_eq self.v i N (by scalar_tac) (by scalar_tac) (by scalar_tac)
        rw [htmp]
        apply Iff.intro
        . {
          rw [and_imp]
          intro h_xi_zero h_xrest_zero
          simp [*]
        }
        . {
          intro h_val_is_zero
          have h_xi_pos : ↑((Array.v self).index ↑i) ≥ (0: Int) := by scalar_tac
          have h_xrest_pos :  (2: Int) ^ 64 * valImpl (List.slice (↑i + 1) (↑N) self.v) ≥ (0: Int) := by simp [valImpl_ge_zero, *]
          have htmp1 := add_eq_zero_iff' h_xrest_pos h_xi_pos
          -- apply h_val_is_zero at htmp1
          -- have htmp2 : (2: Int) ^ 64 * ↑((Array.v self).index ↑i) = (0: Int) ∧ ↑((Array.v self).index ↑i) = (0: Int) := by sorry
          -- rw [htmp1] at h_val_is_zero
          rw [htmp1] at h_val_is_zero
          rw [mul_eq_zero] at h_val_is_zero
          simp at h_val_is_zero
          simp [*]
          -- have htmp2 := Scalar.val_eq_of_eq (Eq ((↑self).index ↑i) 0#u64)
          scalar_tac
        }
      }
    }
  }
  termination_by (N.val - i.val).toNat
    decreasing_by
    simp_wf
    rw [i1_decl]
    simp [sub_add_eq_sub_sub, *]
    apply Arith.to_int_sub_to_nat_lt
    simp [sub_one_lt, Int.toNat_sub, Int.toNat_sub_of_le, h, *]
    scalar_tac
    simp [sub_one_lt, *]

    -- Because I have the same induction
    simp_wf
    rw [i1_decl]
    simp [sub_add_eq_sub_sub, *]
    apply Arith.to_int_sub_to_nat_lt
    simp [sub_one_lt, Int.toNat_sub, Int.toNat_sub_of_le, h, *]
    scalar_tac
    simp [sub_one_lt, *]

lemma is_zero_correct :
  ∀ (N : Usize) (self: BigInt N),
  ∃ b, biginteger.BigIntegertestbigintegerBigIntN.is_zero N self = .ok b ∧ b = (self.val = 0) := by {
    intro N self
    unfold BigIntegertestbigintegerBigIntN.is_zero
    progress with is_zero_loop_correct as ⟨ ⟩
    scalar_tac
    simp [*]
    unfold BigInt.val
    rw [full_slice]
    simp [*]
  }

end biginteger

end test
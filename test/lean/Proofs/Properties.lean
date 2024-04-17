import Common.Base

open Primitives
open Result

namespace test

namespace biginteger

lemma is_even_correct :
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

end biginteger

end test
import BitWord.AddressLinear
import Transpose.Tape.Encode

namespace BitWord
open Transpose

/-- A contiguous field of a most-significant-first address. -/
def addressSlice {N : ℕ} (start width : ℕ) (hw : start+width ≤ N)
    (a : Address N) : Address width := fun i => a ⟨start+i.val,by have := i.isLt; omega⟩

 theorem addressSlice_whole {N : ℕ} (a : Address N) : addressSlice 0 N (by omega) a = a := by
   funext i
   apply congrArg a
   apply Fin.ext
   simp

 theorem addressSlice_append {N : ℕ} (a : Address N) (o n m : ℕ)
     (h : o+(n+m) ≤ N) :
     Fin.append (addressSlice o n (by omega) a)
       (addressSlice (o+n) m (by omega) a) = addressSlice o (n+m) h a := by
   funext i
   refine Fin.addCases ?_ ?_ i
   · intro j
     rw [Fin.append_left]
     rfl
   · intro j
     rw [Fin.append_right]
     apply congrArg a
     apply Fin.ext
     simp only [Fin.val_natAdd]
     omega

 theorem addressValue_slice_split {N : ℕ} (a : Address N) (o n m : ℕ)
     (h : o+(n+m) ≤ N) :
     addressValue (addressSlice o (n+m) h a) =
       addressValue (addressSlice o n (by omega) a)*2^m +
       addressValue (addressSlice (o+n) m (by omega) a) := by
   rw [← addressSlice_append a o n m h, addressValue_append]

 def rowAddress {h w : ℕ} (a : Address (2*h+w)) : Address h :=
   addressSlice 0 h (by omega) a
 def columnAddress {h w : ℕ} (a : Address (2*h+w)) : Address h :=
   addressSlice h h (by omega) a
 def laneAddress {h w : ℕ} (a : Address (2*h+w)) : Address w :=
   addressSlice (2*h) w le_rfl a

 theorem addressValue_slice_congr {N o n o' n' : ℕ} (a : Address N)
     (h : o+n ≤ N) (h' : o'+n' ≤ N) (ho : o=o') (hn : n=n') :
     addressValue (addressSlice o n h a) = addressValue (addressSlice o' n' h' a) := by
   subst o'
   subst n'
   rfl

 theorem addressValue_fields {h w : ℕ} (a : Address (2*h+w)) :
     addressValue a = (addressValue (rowAddress a)*2^h + addressValue (columnAddress a))*2^w +
       addressValue (laneAddress a) := by
   have h₁ := addressValue_slice_split a 0 (2*h) w (by omega)
   have h₂ := addressValue_slice_split a 0 h h (by omega)
   have he : addressSlice 0 (2*h+w) (by omega) a = a := addressSlice_whole a
   rw [he] at h₁
   have hf : addressValue (addressSlice 0 (2*h) (by omega) a) =
       addressValue (rowAddress a)*2^h+addressValue (columnAddress a) := by
     calc
       _ = addressValue (addressSlice 0 (h+h) (by omega) a) :=
         addressValue_slice_congr a _ _ rfl (by omega)
       _ = _ := h₂
       _ = _ := by
         apply congrArg (fun x => addressValue (rowAddress a)*2^h+x)
         exact addressValue_slice_congr a _ _ (by omega) rfl
   rw [hf] at h₁
   calc
     _ = _ := h₁
     _ = _ := by
       apply congrArg (fun x => (addressValue (rowAddress a)*2^h+addressValue (columnAddress a))*2^w+x)
       exact addressValue_slice_congr a _ _ (by omega) rfl

/-- Matrix bits placed at the ordinary row/column/lane address fields. -/
def matrixBank (h w : ℕ) (A : Matrix) : Address (2*h+w) → Bool :=
  fun a => A (addressValue (rowAddress a)) (addressValue (columnAddress a))
    (addressValue (laneAddress a))

 theorem matrixBank_head (h w : ℕ) (A : Matrix) :
     moveBank (headEquiv h w) (matrixBank h w A) = matrixBank h w (transpose A) := by
   funext a
   change A (addressValue (rowAddress ((addressEquiv (headEquiv h w)).symm a)))
       (addressValue (columnAddress ((addressEquiv (headEquiv h w)).symm a)))
       (addressValue (laneAddress ((addressEquiv (headEquiv h w)).symm a))) = _
   have hr : rowAddress ((addressEquiv (headEquiv h w)).symm a) = columnAddress a := by
     funext i
     change a ⟨headSwap h (0+i.val),_⟩ = a ⟨h+i.val,_⟩
     apply congrArg a
     apply Fin.ext
     have hi := i.isLt
     simp [headSwap,hi,Nat.add_comm]
   have hc : columnAddress ((addressEquiv (headEquiv h w)).symm a) = rowAddress a := by
     funext i
     change a ⟨headSwap h (h+i.val),_⟩ = a ⟨0+i.val,_⟩
     apply congrArg a
     apply Fin.ext
     change headSwap h (h+i.val) = 0+i.val
     have hi := i.isLt
     unfold headSwap
     split_ifs <;> omega
   have hl : laneAddress ((addressEquiv (headEquiv h w)).symm a) = laneAddress a := by
     funext i
     exact headAddress_tail i.isLt a
   rw [hr,hc,hl]
   rfl

 theorem matrixBank_flatten (h w : ℕ) (A : Matrix) :
     flattenBank (matrixBank h w A) = encode (2^h) (2^w) A := by
   have hlen : 2^(2*h+w) = (2^h)*(2^h)*2^w := by
     rw [pow_add, show 2*h=h+h by omega, pow_add]
   apply List.ext_getElem (by simp [flattenBank_length, Tape.Impl.length_encode, hlen])
   intro i hi hi'
   have hib : i<2^(2*h+w) := by simpa only [flattenBank_length] using hi
   let a := (addressFin (2*h+w)).symm ⟨i,hib⟩
   have hv : addressValue a = i := by
     rw [← addressFin_val, Equiv.apply_symm_apply]
   have hd := addressValue_fields a
   have hr := addressValue_lt (rowAddress a)
   have hc := addressValue_lt (columnAddress a)
   have hl := addressValue_lt (laneAddress a)
   have hn := Transpose.nth_encode A
     (addressValue (rowAddress a)) (addressValue (columnAddress a))
     (addressValue (laneAddress a)) hr hc hl
   rw [← hd, hv, Tape.Impl.nth_eq_getElem?, List.getElem?_eq_getElem hi'] at hn
   have he := flattenBank_get (matrixBank h w A) a
   have he' : (flattenBank (matrixBank h w A))[i] = matrixBank h w A a := by
     simpa only [hv] using he
   exact he'.trans (Option.some.inj hn).symm

 theorem canonical_flatten_transpose {h : ℕ} (hh : 0<h) (A : Matrix) :
     flattenBank (moveBank (gatesEquiv _ (canonicalGates h) (canonicalGates_legal hh))
       (matrixBank h (tailBits h) A)) = encode (2^h) (2^tailBits h) (transpose A) := by
   rw [canonical_bank_action hh, matrixBank_head, matrixBank_flatten]

end BitWord

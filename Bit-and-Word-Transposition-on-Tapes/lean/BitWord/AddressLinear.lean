import BitWord.AddressBanks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

namespace BitWord
open scoped BigOperators

/-- Reverse position order only at the interface to mathlib's little-endian
finite-digit equivalence. Public addresses remain most-significant first. -/
def addressDigits (N : ℕ) : Address N ≃ (Fin N → Fin 2) where
  toFun a i := finTwoEquiv.symm (a i.rev)
  invFun f i := finTwoEquiv (f i.rev)
  left_inv a := by funext i; simp
  right_inv f := by funext i; simp

/-- Ordinary numerical address, with the leading address bit most significant. -/
def addressFin (N : ℕ) : Address N ≃ Fin (2^N) :=
  (addressDigits N).trans finFunctionFinEquiv

def addressValue {N : ℕ} (a : Address N) : ℕ :=
  ∑ i : Fin N, (finTwoEquiv.symm (a i)).val * 2^(N-1-i.val)

 theorem addressFin_val {N : ℕ} (a : Address N) :
     (addressFin N a).val = addressValue a := by
   change (∑ i : Fin N, (finTwoEquiv.symm (a i.rev)).val * 2^i.val) = _
   have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
     (fun i => (finTwoEquiv.symm (a i)).val * 2^(N-1-i.val))
   have hex (i : Fin N) : N-1-(N-(i.val+1)) = i.val := by have := i.isLt; omega
   simpa only [addressValue, Fin.revPerm_apply, Fin.val_rev, hex] using he

 theorem addressValue_lt {N : ℕ} (a : Address N) : addressValue a < 2^N := by
   rw [← addressFin_val]
   exact (addressFin N a).isLt

 theorem addressValue_append {n m : ℕ} (a : Address n) (b : Address m) :
     addressValue (Fin.append a b) = addressValue a * 2^m + addressValue b := by
   unfold addressValue
   rw [Fin.sum_univ_add]
   simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
   congr 1
   · rw [Finset.sum_mul]
     apply Finset.sum_congr rfl
     intro i _
     have he : n+m-1-i.val = (n-1-i.val)+m := by have := i.isLt; omega
     rw [he, pow_add]
     ring
   · apply Finset.sum_congr rfl
     intro i _
     have he : n+m-1-(n+i.val)=m-1-i.val := by have := i.isLt; omega
     rw [he]

/-- Flatten a bank in numerical, hence lexicographic binary-address order. -/
def flattenBank {N : ℕ} {α : Type*} (bank : Address N → α) : List α :=
  List.ofFn (fun i : Fin (2^N) => bank ((addressFin N).symm i))

@[simp] theorem flattenBank_length {N : ℕ} {α : Type*} (bank : Address N → α) :
    (flattenBank bank).length = 2^N := by simp [flattenBank]

 theorem flattenBank_get {N : ℕ} {α : Type*} (bank : Address N → α) (a : Address N) :
     (flattenBank bank)[addressValue a]'(by rw [flattenBank_length]; exact addressValue_lt a) = bank a := by
   simp only [flattenBank, List.getElem_ofFn]
   have he : (⟨addressValue a, addressValue_lt a⟩ : Fin (2^N)) = addressFin N a :=
     Fin.ext (addressFin_val a).symm
   rw [he, Equiv.symm_apply_apply]

end BitWord

namespace BitWord

 theorem addressValue_inverse {N : ℕ} (i : Fin (2^N)) :
     addressValue ((addressFin N).symm i) = i.val := by
   rw [← addressFin_val, Equiv.apply_symm_apply]

 theorem ofFn_castLength {n m : ℕ} {α : Type*} (h : n=m) (f : Fin m → α) :
     List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
   subst m
   rfl

/-- Numerical bank order groups any fixed leading address field into consecutive
blocks; this is a list identity, not a free tape rearrangement. -/
 theorem flattenBank_blocks {n m : ℕ} {α : Type*} (bank : Address (n+m) → α) :
     flattenBank bank = (List.ofFn (fun p : Fin (2^n) =>
       flattenBank (fun a : Address m => bank (Fin.append ((addressFin n).symm p) a)))).flatten := by
   let f : Fin (2^n*2^m) → α := fun i => bank ((addressFin (n+m)).symm
     (Fin.cast (pow_add 2 n m).symm i))
   have he : flattenBank bank = List.ofFn f :=
     (ofFn_castLength (pow_add 2 n m).symm (fun i => bank ((addressFin (n+m)).symm i))).symm
   rw [he, List.ofFn_mul]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext p
   unfold flattenBank
   apply congrArg List.ofFn
   funext q
   apply congrArg bank
   apply (addressFin (n+m)).injective
   apply Fin.ext
   simp only [Equiv.apply_symm_apply, Fin.val_cast]
   rw [addressFin_val, addressValue_append, addressValue_inverse, addressValue_inverse]

end BitWord

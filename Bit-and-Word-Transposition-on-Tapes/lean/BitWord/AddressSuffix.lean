import BitWord.AddressFields

namespace BitWord

/-- Total decoding of a raw list; out-of-range data are zero.  Every use below
with a bank has the exact prescribed length. -/
def bankOfList (N : ℕ) (xs : List Bool) : Address N → Bool :=
  fun a => xs[addressValue a]?.getD false

@[simp] theorem bankOfList_flatten {N : ℕ} (bank : Address N → Bool) :
    bankOfList N (flattenBank bank) = bank := by
  funext a
  unfold bankOfList
  rw [List.getElem?_eq_getElem (by simpa using addressValue_lt a)]
  exact flattenBank_get bank a

 theorem flattenBank_bankOfList {N : ℕ} (xs : List Bool) (h : xs.length=2^N) :
     flattenBank (bankOfList N xs) = xs := by
   apply List.ext_getElem (by simpa using h.symm)
   intro i hi hi'
   simp only [flattenBank, List.getElem_ofFn, bankOfList, addressValue_inverse]
   rw [List.getElem?_eq_getElem hi']
   rfl

/-- The total bit-transpose map used for each contiguous oracle block. -/
def bitTranspose (k : ℕ) (xs : List Bool) : List Bool :=
  flattenBank (moveBank (headEquiv k 0) (bankOfList (2*k+0) xs))

 theorem bitTranspose_encode (k : ℕ) (A : Transpose.Matrix) :
     bitTranspose k (Transpose.encode (2^k) 1 A) =
       Transpose.encode (2^k) 1 (Transpose.transpose A) := by
   change bitTranspose k (Transpose.encode (2^k) (2^0) A) = _
   rw [← matrixBank_flatten k 0 A]
   unfold bitTranspose
   rw [bankOfList_flatten, matrixBank_head, matrixBank_flatten]
   rfl

 theorem bitTranspose_spec (k : ℕ) (xs : List Bool) (h : xs.length=4^k) :
     ∃ A : Transpose.Matrix, Transpose.encode (2^k) 1 A=xs ∧
       Transpose.encode (2^k) 1 (Transpose.transpose A)=bitTranspose k xs := by
   have he : xs.length=(2^k)*(2^k)*1 := by
     rw [h, Nat.mul_one, ← pow_add, ← two_mul]
     rw [show 4=2^2 by norm_num, ← pow_mul]
   have hm : xs ∈ Transpose.Tape.matrixInputs (2^k) 1 := by
     rw [Transpose.Tape.Impl.matrixInputs_eq]
     exact he
   obtain ⟨A,hA⟩ := hm
   exact ⟨A,hA,by rw [← hA,bitTranspose_encode]⟩

 theorem bitTranspose_flatten (k : ℕ) (bank : Address (2*k) → Bool) :
     bitTranspose k (flattenBank bank) = flattenBank (moveBank (headEquiv k 0) bank) := by
   simp only [bitTranspose, bankOfList_flatten]

 theorem suffixAddress_append (p k : ℕ) (a : Address p) (b : Address (2*k)) :
     addressEquiv (suffixEquiv (p+2*k) k (by omega))
       (Fin.append a b) = Fin.append a (addressEquiv (headEquiv k 0) b) := by
   funext i
   refine Fin.addCases (m := p) (n := 2*k) (fun j => ?_) (fun j => ?_) i
   · apply Eq.trans ?_ (Fin.append_left a (addressEquiv (headEquiv k 0) b) j).symm
     change (Fin.append a b) ⟨suffixSwap (p+2*k) k j.val, _⟩ = a j
     have he : suffixSwap (p+2*k) k j.val = j.val := by
       unfold suffixSwap
       have := j.isLt
       split_ifs <;> omega
     simp only [he]
     exact Fin.append_left a b j
   · apply Eq.trans ?_ (Fin.append_right a (addressEquiv (headEquiv k 0) b) j).symm
     change (Fin.append a b) ⟨suffixSwap (p+2*k) k (p+j.val), _⟩ =
       b ⟨headSwap k j.val, _⟩
     have he : suffixSwap (p+2*k) k (p+j.val) = p+headSwap k j.val := by
       unfold suffixSwap headSwap
       have := j.isLt
       split_ifs <;> omega
     simp only [he]
     exact Fin.append_right a b ⟨headSwap k j.val, by unfold headSwap; split_ifs <;> omega⟩

/-- The actual suffix gate acts separately on consecutive raw square blocks. -/
 theorem flattenBank_suffix (p k : ℕ) (bank : Address (p+2*k) → Bool) :
     flattenBank (moveBank
       (Gate.equiv (p+2*k) (.suffix k) (by change 2*k≤p+2*k; omega)) bank) =
       (List.ofFn (fun i : Fin (2^p) => bitTranspose k
         (flattenBank (fun a : Address (2*k) =>
           bank (Fin.append ((addressFin p).symm i) a))))).flatten := by
   rw [flattenBank_blocks (n := p) (m := 2*k)]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext i
   rw [bitTranspose_flatten]
   apply congrArg flattenBank
   funext a
   change bank (addressEquiv
     (suffixEquiv (p+2*k) k (by omega)) (Fin.append ((addressFin p).symm i) a)) =
     bank (Fin.append ((addressFin p).symm i) (addressEquiv (headEquiv k 0) a))
   rw [suffixAddress_append]

 theorem suffix_block_length (p k : ℕ) (bank : Address (p+2*k) → Bool) (i : Fin (2^p)) :
     (flattenBank (fun a : Address (2*k) => bank (Fin.append ((addressFin p).symm i) a))).length = 4^k := by
   rw [flattenBank_length]
   rw [show 4=2^2 by norm_num, ← pow_mul]

end BitWord

namespace BitWord

/-- A legal suffix stage on any bank is exactly a batch of genuine square bit
transposes.  The witness blocks are consecutive, exhaustive and uniformly sized. -/
 theorem suffix_block_decomposition {N k : ℕ} (hk : 2*k≤N) (bank : Address N → Bool) :
     ∃ blocks : List (List Bool), blocks.flatten=flattenBank bank ∧
       (∀ xs ∈ blocks, xs.length=4^k) ∧
       flattenBank (moveBank (Gate.equiv N (.suffix k) hk) bank)=
         blocks.flatMap (bitTranspose k) := by
   obtain ⟨p,hp⟩ := Nat.exists_eq_add_of_le hk
   have he : N=p+2*k := by omega
   clear hp
   subst N
   let blocks := List.ofFn (fun i : Fin (2^p) => flattenBank (fun a : Address (2*k) =>
     bank (Fin.append ((addressFin p).symm i) a)))
   refine ⟨blocks,?_,?_,?_⟩
   · exact (flattenBank_blocks bank).symm
   · intro xs hx
     obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
     subst xs
     exact suffix_block_length p k bank i
   · simpa [blocks,List.flatMap_def,List.map_ofFn,Function.comp_def] using flattenBank_suffix p k bank

end BitWord

import BitWord.AddressLinear
import BitWord.NativeSplitScan
import BitWord.NativeInterleaveScan

namespace BitWord
open scoped BigOperators

 theorem addressValue_cons {n : ℕ} (b : Bool) (a : Address n) :
     addressValue (Fin.cons b a) = (finTwoEquiv.symm b).val*2^n+addressValue a := by
   unfold addressValue
   rw [Fin.sum_univ_succ]
   simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ,
     Nat.add_sub_cancel, Nat.sub_zero]
   congr 1
   apply Finset.sum_congr rfl
   intro i _
   have he : n-(i.val+1)=n-1-i.val := by omega
   rw [he]

 theorem addressValue_snoc {n : ℕ} (a : Address n) (b : Bool) :
     addressValue (Fin.snoc a b) = addressValue a*2+(finTwoEquiv.symm b).val := by
   unfold addressValue
   rw [Fin.sum_univ_castSucc]
   simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
     Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
   congr 1
   rw [Finset.sum_mul]
   apply Finset.sum_congr rfl
   intro i _
   have he : n-i.val=(n-1-i.val)+1 := by have := i.isLt; omega
   rw [he, pow_succ]
   ring

 theorem right_snoc {n : ℕ} (a : Address n) (b : Bool) :
     addressEquiv (Gate.equiv (n+1) .right (by exact Nat.succ_pos _)) (Fin.snoc a b) =
       Fin.cons b a := by
   funext i
   refine Fin.cases ?_ (fun j => ?_) i
   · change (Fin.snoc (α := fun _ : Fin (n+1) => Bool) a b) (Fin.last n) = b
     simp only [Fin.snoc_last]
   · change (Fin.snoc (α := fun _ : Fin (n+1) => Bool) a b) j.castSucc = a j
     simp only [Fin.snoc_castSucc]

 theorem flattenBank_cons {n : ℕ} (bank : Address (n+1) → Bool) :
     flattenBank bank = flattenBank (fun a => bank (Fin.cons false a)) ++
       flattenBank (fun a => bank (Fin.cons true a)) := by
   have hlen : 2^n+2^n=2^(n+1) := by rw [pow_succ]; omega
   let f : Fin (2^n+2^n) → Bool := fun i => bank ((addressFin (n+1)).symm (Fin.cast hlen i))
   have he : flattenBank bank = List.ofFn f := (ofFn_castLength hlen _).symm
   rw [he, List.ofFn_add]
   congr 1
   · apply congrArg List.ofFn
     funext i
     apply congrArg bank
     apply (addressFin (n+1)).injective
     apply Fin.ext
     simp only [Equiv.apply_symm_apply, Fin.val_cast, Fin.val_castLE]
     rw [addressFin_val, addressValue_cons, addressValue_inverse]
     simp [finTwoEquiv]
   · apply congrArg List.ofFn
     funext i
     apply congrArg bank
     apply (addressFin (n+1)).injective
     apply Fin.ext
     simp only [Equiv.apply_symm_apply, Fin.val_cast, Fin.val_natAdd]
     rw [addressFin_val, addressValue_cons, addressValue_inverse]
     simp [finTwoEquiv]

 theorem flattenBank_pairs {n : ℕ} (bank : Address (n+1) → Bool) :
     flattenBank bank = (List.ofFn (fun i : Fin (2^n) =>
       [bank (Fin.snoc ((addressFin n).symm i) false),
        bank (Fin.snoc ((addressFin n).symm i) true)])).flatten := by
   have hlen : 2^n*2=2^(n+1) := (pow_succ 2 n).symm
   let f : Fin (2^n*2) → Bool := fun i => bank ((addressFin (n+1)).symm (Fin.cast hlen i))
   have he : flattenBank bank = List.ofFn f := (ofFn_castLength hlen _).symm
   rw [he, List.ofFn_mul]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext i
   rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
   congr 1
   · apply congrArg bank
     apply (addressFin (n+1)).injective
     apply Fin.ext
     simp only [Equiv.apply_symm_apply, Fin.val_cast, Fin.val_zero]
     rw [addressFin_val, addressValue_snoc, addressValue_inverse]
     simp [finTwoEquiv]
   · congr 1
     apply congrArg bank
     apply (addressFin (n+1)).injective
     apply Fin.ext
     simp only [Equiv.apply_symm_apply, Fin.val_cast, Fin.val_zero, Fin.val_succ]
     rw [addressFin_val, addressValue_snoc, addressValue_inverse]
     simp [finTwoEquiv]

 theorem selected_pairs (xs : List (Bool×Bool)) :
     NativeSplitScan.selected false false (xs.flatMap (fun p => [p.1,p.2])) = xs.map Prod.fst ∧
     NativeSplitScan.selected true false (xs.flatMap (fun p => [p.1,p.2])) = xs.map Prod.snd := by
   induction xs with
   | nil => simp [NativeSplitScan.selected]
   | cons p xs ih => simpa [NativeSplitScan.selected] using ih

/-- A right rotation of binary address positions is exactly the physical stable
parity split, including data order inside both halves. -/
 theorem flattenBank_right {n : ℕ} (bank : Address (n+1) → Bool) :
     flattenBank (moveBank (Gate.equiv (n+1) .right (by exact Nat.succ_pos _)) bank) =
       NativeSplitScan.selected false false (flattenBank bank) ++
       NativeSplitScan.selected true false (flattenBank bank) := by
   rw [flattenBank_cons]
   have hc (b : Bool) : (fun a : Address n =>
       moveBank (Gate.equiv (n+1) .right (by exact Nat.succ_pos _)) bank (Fin.cons b a)) =
       fun a => bank (Fin.snoc a b) := by
     funext a
     change bank ((addressEquiv (Gate.equiv (n+1) .right _)).symm (Fin.cons b a)) = _
     rw [← right_snoc a b, Equiv.symm_apply_apply]
   rw [hc, hc, flattenBank_pairs bank]
   let xs := List.ofFn (fun i : Fin (2^n) =>
     (bank (Fin.snoc ((addressFin n).symm i) false),bank (Fin.snoc ((addressFin n).symm i) true)))
   have he : xs.flatMap (fun p => [p.1,p.2]) =
       (List.ofFn (fun i : Fin (2^n) =>
         [bank (Fin.snoc ((addressFin n).symm i) false),
          bank (Fin.snoc ((addressFin n).symm i) true)])).flatten := by
     simp [xs, List.flatMap, List.map_ofFn, Function.comp_def]
   rw [← he, (selected_pairs xs).1, (selected_pairs xs).2]
   simp [xs, flattenBank, List.map_ofFn, Function.comp_def]

end BitWord

namespace BitWord

 theorem interleave_pairs (xs : List (Bool×Bool)) :
     NativeInterleaveScan.interleave (xs.map Prod.fst) (xs.map Prod.snd) =
       xs.flatMap (fun p => [p.1,p.2]) := by
   induction xs with
   | nil => rfl
   | cons p xs ih => simpa [NativeInterleaveScan.interleave] using ih

/-- The inverse address rotation is the literal alternating merge of the two
consecutive equal halves of the original bank. -/
 theorem flattenBank_left {n : ℕ} (bank : Address (n+1) → Bool) :
     flattenBank (moveBank (Gate.equiv (n+1) .left (by exact Nat.succ_pos _)) bank) =
       NativeInterleaveScan.interleave
         (flattenBank (fun a : Address n => bank (Fin.cons false a)))
         (flattenBank (fun a : Address n => bank (Fin.cons true a))) := by
   rw [flattenBank_pairs]
   have hc (b : Bool) (a : Address n) :
       moveBank (Gate.equiv (n+1) .left (by exact Nat.succ_pos _)) bank (Fin.snoc a b) =
       bank (Fin.cons b a) := by
     change bank (addressEquiv (Gate.equiv (n+1) .right (by exact Nat.succ_pos _)) (Fin.snoc a b)) = _
     rw [right_snoc]
   simp_rw [hc]
   let xs := List.ofFn (fun i : Fin (2^n) =>
     (bank (Fin.cons false ((addressFin n).symm i)),bank (Fin.cons true ((addressFin n).symm i))))
   have hi := interleave_pairs xs
   simpa [xs, flattenBank, List.flatMap, List.map_ofFn, Function.comp_def] using hi.symm

 theorem flattenBank_left_halves {n : ℕ} (bank : Address (n+1) → Bool) :
     flattenBank (moveBank (Gate.equiv (n+1) .left (by exact Nat.succ_pos _)) bank) =
       NativeInterleaveScan.interleave ((flattenBank bank).take (2^n))
         ((flattenBank bank).drop (2^n)) := by
   rw [flattenBank_left, flattenBank_cons bank]
   have hlen : (flattenBank (fun a : Address n => bank (Fin.cons false a))).length = 2^n :=
     flattenBank_length _
   rw [← hlen, List.take_left, List.drop_left]

end BitWord

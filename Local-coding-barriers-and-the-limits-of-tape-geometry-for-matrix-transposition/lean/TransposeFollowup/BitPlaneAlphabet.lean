import Mathlib
import Transpose.Statement

/-! A finite, executable alphabet table for bit-plane tapes. Width depends
only on the fixed source alphabet. Symbol zero is encoded by all blanks;
unused target alphabet symbols are harmless off the simulation invariant. -/
namespace TransposeFollowup.BitPlaneAlphabet
set_option autoImplicit false

def width (g : ℕ) : ℕ := max 1 g.size

def encode (g : ℕ) (x : Fin (g+1)) (i : Fin (width g)) : Fin 5 :=
  if x.val.testBit i.val then 1 else 0

def matchesWord (g : ℕ) (v : Fin (width g) → Fin 5) (x : Fin (g+1)) : Bool :=
  (List.finRange (width g)).all (fun i => encode g x i == v i)

def decode (g : ℕ) (v : Fin (width g) → Fin 5) : Fin (g+1) :=
  ((List.finRange (g+1)).find? (matchesWord g v)).getD 0

theorem width_positive (g : ℕ) : 0<width g := by unfold width;omega

theorem encode_zero (g : ℕ) : encode g 0=(fun _ => 0) := by
  funext i
  simp [encode]

theorem encode_injective (g : ℕ) : Function.Injective (encode g) := by
  intro x y he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<width g
  · have h:=congrFun he ⟨i,hi⟩
    cases hx : x.val.testBit i <;> cases hy : y.val.testBit i <;> simp_all [encode]
  · have hwi : max 1 g.size ≤ i := by simpa only [width] using (Nat.le_of_not_gt hi)
    have hx : x.val<2^i := Nat.size_le.mp
      ((Nat.size_le_size (Nat.le_of_lt_succ x.isLt)).trans ((le_max_right 1 g.size).trans hwi))
    have hy : y.val<2^i := Nat.size_le.mp
      ((Nat.size_le_size (Nat.le_of_lt_succ y.isLt)).trans ((le_max_right 1 g.size).trans hwi))
    rw [Nat.testBit_eq_false_of_lt hx,Nat.testBit_eq_false_of_lt hy]

theorem matchesWord_iff (g : ℕ) (v : Fin (width g) → Fin 5) (x : Fin (g+1)) :
    matchesWord g v x=true ↔ encode g x=v := by
  simp only [matchesWord,List.all_eq_true,List.mem_finRange,forall_true_left,beq_iff_eq]
  exact funext_iff.symm

theorem decode_encode (g : ℕ) (x : Fin (g+1)) : decode g (encode g x)=x := by
  unfold decode
  cases hf : (List.finRange (g+1)).find? (matchesWord g (encode g x)) with
  | none =>
    have h:=(List.find?_eq_none.mp hf) x (by simp)
    exact False.elim (h ((matchesWord_iff g _ x).mpr rfl))
  | some y =>
    have h:=(matchesWord_iff g _ y).mp (List.find?_some hf)
    exact encode_injective g h

theorem decode_zero (g : ℕ) : decode g (fun _ => 0)=0 := by
  rw [← encode_zero g]
  exact decode_encode g 0

end TransposeFollowup.BitPlaneAlphabet

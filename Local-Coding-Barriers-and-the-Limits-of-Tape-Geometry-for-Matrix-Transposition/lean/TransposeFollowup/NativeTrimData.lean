import TransposeFollowup.SeedMultipleMeaning
import Mathlib.Data.Nat.Size

/-! The mathematical contract for physical high-zero trimming. Words are
little endian. Zero is the empty word; every nonzero normalized word ends
in one. These specifications are not machine instructions. -/
namespace TransposeFollowup.NativeTrim
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def Normalized (xs : List Bool) : Prop := xs=[] ∨ ∃ pre,xs=pre++[true]

theorem decomposition (xs : List Bool) :
    ∃ ys k,Normalized ys ∧ xs=ys++List.replicate k false := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[],0,Or.inl rfl,rfl⟩
  | append_singleton xs b ih =>
    cases b with
    | false =>
      obtain ⟨ys,k,hy,hx⟩ := ih
      refine ⟨ys,k+1,hy,?_⟩
      rw [hx,List.replicate_succ',List.append_assoc]
    | true => exact ⟨xs++[true],0,Or.inr ⟨xs,rfl⟩,by simp⟩

theorem append_value (xs ys : List Bool) :
    Counter.value (xs++ys)=Counter.value xs+2^xs.length*Counter.value ys := by
  induction xs with
  | nil => simp [Counter.value]
  | cons b xs ih =>
    cases b <;> simp only [List.cons_append,Counter.value,ih,List.length_cons,pow_succ] <;> ring

theorem normalized_length (xs : List Bool) (h : Normalized xs) :
    xs.length=(Counter.value xs).size := by
  have hu : (Counter.value xs).size ≤ xs.length :=
    Nat.size_le.mpr (by rw [NativeCounter.word_value];exact BinaryCarry.value_lt xs)
  rcases h with rfl | ⟨pre,rfl⟩
  · rfl
  · have hv : 2^pre.length ≤ Counter.value (pre++[true]) := by
      simp only [append_value,Counter.value];omega
    have hl := Nat.lt_size.mpr hv
    simp only [List.length_append,List.length_singleton] at hu ⊢
    omega

end TransposeFollowup.NativeTrim

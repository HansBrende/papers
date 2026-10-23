import TransposeFollowup.ExpanderShearNativeBridge

/-! Raw A-then-B row-major serialization covers every input bit string of
the specified length. This is an encoding lemma, not a free machine step. -/
namespace TransposeFollowup.ExpanderShear
open ExpanderShearRowStream
set_option autoImplicit false

theorem boolShear_involutive {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) :
    Function.Involutive (boolShear (W := W) L) := by
  intro x
  have hL : L + L = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (L i j)
  rw [boolShear_add_comp,hL,boolShear_zero]

def rawBank {m W : ℕ} (x : BoolBank m W) : List Bool :=
  rawHalf (fun i => x (.inl i)) ++ rawHalf (fun j => x (.inr j))

@[simp] theorem rawBank_length {m W : ℕ} (x : BoolBank m W) :
    (rawBank x).length = 2*m*W := by simp [rawBank,two_mul,Nat.add_mul]

theorem rawHalf_surjective {m W : ℕ} (w : List Bool) (hw : w.length=m*W) :
    ∃ A : Fin m → Word W, rawHalf A=w := by
  let f : Fin (m*W) → Bool := fun i => w.get (Fin.cast hw.symm i)
  let A : Fin m → Word W := fun i j => f (finProdFinEquiv (i,j))
  refine ⟨A,?_⟩
  have h : rawHalf A=List.ofFn f := by
    rw [List.ofFn_mul]
    simp [rawHalf,rawWords,Function.comp_def,List.ofFn_eq_map,List.flatMap_def,
      A,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [h]
  simpa only [List.ofFn_get] using (List.ofFn_congr hw w.get).symm

theorem rawBank_surjective {m W : ℕ} (w : List Bool) (hw : w.length=2*m*W) :
    ∃ x : BoolBank m W, rawBank x=w := by
  have ha : (w.take (m*W)).length=m*W := by
    rw [List.length_take,hw,Nat.min_eq_left (by nlinarith)]
  have hb : (w.drop (m*W)).length=m*W := by rw [List.length_drop,hw,Nat.mul_assoc]; omega
  obtain ⟨A,hA⟩ := rawHalf_surjective (w.take (m*W)) ha
  obtain ⟨B,hB⟩ := rawHalf_surjective (w.drop (m*W)) hb
  refine ⟨Sum.elim A B,?_⟩
  change rawHalf A ++ rawHalf B=w
  rw [hA,hB,List.take_append_drop]

end TransposeFollowup.ExpanderShear

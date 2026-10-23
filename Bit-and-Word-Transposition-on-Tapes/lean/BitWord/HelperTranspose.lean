import BitWord.HelperSpread

/-! Exact transpose demands in equal aligned bins. The matrix side k*B is a
multiple of the bin width; no lane oracle or obliviousness assumption is used. -/
namespace BitWord
open Classical
set_option autoImplicit false

/-- Split an aligned bin label into its matrix row and within-row bin. -/
def gridMatrixEquiv (k B : ℕ) : Grid ((k*B)*k) B ≃ (Fin (k*B) × Fin (k*B)) :=
  (Equiv.prodCongr (finProdFinEquiv.symm) (Equiv.refl (Fin B))).trans
    ((Equiv.prodAssoc (Fin (k*B)) (Fin k) (Fin B)).trans
      (Equiv.prodCongr (Equiv.refl (Fin (k*B))) finProdFinEquiv))

/-- The actual square transpose, expressed on the aligned-bin grid. -/
def gridTranspose (k B : ℕ) : Equiv.Perm (Grid ((k*B)*k) B) :=
  (gridMatrixEquiv k B).trans
    ((Equiv.prodComm (Fin (k*B)) (Fin (k*B))).trans (gridMatrixEquiv k B).symm)

/-- The matrix coordinates really are swapped by the grid endpoint. -/
@[simp] theorem gridMatrix_transpose (k B : ℕ) (v : Grid ((k*B)*k) B) :
    gridMatrixEquiv k B (gridTranspose k B v) =
      ((gridMatrixEquiv k B v).2,(gridMatrixEquiv k B v).1) := by
  simp [gridTranspose,Prod.swap]

@[simp] theorem gridMatrix_symm_transpose (k B : ℕ) (v : Grid ((k*B)*k) B) :
    gridMatrixEquiv k B ((gridTranspose k B).symm v) =
      ((gridMatrixEquiv k B v).2,(gridMatrixEquiv k B v).1) := by
  simp [gridTranspose,Prod.swap]

theorem gridTranspose_spread (k B : ℕ) : BinSpread (gridTranspose k B) := by
  intro j i i' he
  have hr := congrArg (fun z : Fin ((k*B)*k) => (finProdFinEquiv.symm z).1) he
  have hrow (p : Grid ((k*B)*k) B) :
      (gridMatrixEquiv k B p).1 = (finProdFinEquiv.symm p.1).1 := rfl
  change (finProdFinEquiv.symm ((gridTranspose k B).symm (j,i)).1).1 =
    (finProdFinEquiv.symm ((gridTranspose k B).symm (j,i')).1).1 at hr
  rw [← hrow,← hrow,gridMatrix_symm_transpose,gridMatrix_symm_transpose] at hr
  change (finProdFinEquiv ((finProdFinEquiv.symm j).2,i) : Fin (k*B)) =
    finProdFinEquiv ((finProdFinEquiv.symm j).2,i') at hr
  exact congrArg Prod.snd (finProdFinEquiv.injective hr)

/-- A raw flattening agrees with ordinary row-major matrix flattening. -/
theorem gridMatrix_flatten (k B : ℕ) (v : Grid ((k*B)*k) B) :
    (finProdFinEquiv (gridMatrixEquiv k B v)).val = (finProdFinEquiv v).val := by
  obtain ⟨j,i⟩ := v
  have hj := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
  change (finProdFinEquiv.symm j).2.val + k*(finProdFinEquiv.symm j).1.val = j.val at hj
  change (finProdFinEquiv ((finProdFinEquiv.symm j).2,i)).val +
    (k*B)*(finProdFinEquiv.symm j).1.val = i.val+B*j.val
  change i.val+B*(finProdFinEquiv.symm j).2.val +
    (k*B)*(finProdFinEquiv.symm j).1.val = i.val+B*j.val
  nlinarith

namespace ScanProgram

/-- Transpose-specific finite bound, with exact actual scan/record semantics. -/
theorem transpose_bound {k B q L : ℕ} {State : Type*} [Fintype State]
    (C : ScanProgram ((k*B)*k) B q L State)
    (V : ∀ t a, PermutationView ((C.layer t).perm a))
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hcorrect : ∀ x p, (C.run x L).1 p out = x ((gridTranspose k B).symm p)) :
    (((k*B)*k)*B : ℝ) - ((k*B)*k)*(11*q)^L ≤
      (((11*q)^L+1:ℕ):ℝ) * (C.badVolume V + s*L*((k*B)*k)) := by
  simpa only [Nat.cast_mul] using
    C.spread_target_bound V s hstate out (gridTranspose k B) (gridTranspose_spread k B) hcorrect

end ScanProgram
end BitWord

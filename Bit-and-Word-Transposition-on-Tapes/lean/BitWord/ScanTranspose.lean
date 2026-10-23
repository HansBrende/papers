import BitWord.HelperTranspose
import BitWord.ScanScaleBudget
import BitWord.ScanGeometry

/-! The scan bound applies to the actual row-major bit transpose on one fixed
raw program, not to a family allowed to choose its scans after the bin scale. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

namespace RawScanProgram
variable {d k B q L : ℕ} {State : Type*}

/-- Exact all-input correctness, in ordinary row-major raw bit coordinates. -/
def Transposes (C : RawScanProgram (d*d) q L State) (out : Fin q) : Prop :=
  ∀ (x : Fin (d*d) → Bool) (r c : Fin d),
    (C.run x L).1 (finProdFinEquiv (r,c)) out = x (finProdFinEquiv (c,r))

noncomputable def views {n : ℕ} (C : RawScanProgram (n*B) q L State) (hB : 0<B) :
    ∀ t a, PermutationView ((C.onGrid.layer t).perm a) :=
  fun t a => stageView ((C.layer t).stage a) hB

theorem views_badVolume {n : ℕ} (C : RawScanProgram (n*B) q L State) (hB : 0<B) :
    C.onGrid.badVolume (C.views hB) = C.badVolume B := by
  unfold ScanProgram.badVolume badVolume views
  exact Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl
    (fun a _ => stageView_bad_card ((C.layer t).stage a) hB))

private theorem flat_grid_matrix (k B : ℕ)
    (h : ((k*B)*k)*B=(k*B)*(k*B)) (p : Grid ((k*B)*k) B) :
    Fin.cast h (finProdFinEquiv p) = finProdFinEquiv (gridMatrixEquiv k B p) := by
  apply Fin.ext
  exact (gridMatrix_flatten k B p).symm

/-- Correctness is transported through proved raw regrouping and no extra data
rearrangement. The casts change only equality proofs for the bank length. -/
theorem regrouped_transposes (C : RawScanProgram ((k*B)*(k*B)) q L State)
    (out : Fin q) (hc : C.Transposes out) (h : ((k*B)*k)*B=(k*B)*(k*B)) :
    ∀ x p, ((C.castLength h.symm).onGrid.run x L).1 p out =
      x ((gridTranspose k B).symm p) := by
  intro x p
  let xr : Fin (((k*B)*k)*B) → Bool := fun z => x (finProdFinEquiv.symm z)
  have he : (fun v => xr (finProdFinEquiv v)) = x := by
    funext v
    simp only [xr,Equiv.symm_apply_apply]
  have hh := (C.castLength h.symm).run_onGrid xr L
  rw [he] at hh
  rw [hh,C.run_castLength]
  change (C.run (fun z => xr (Fin.cast h.symm z)) L).1
      (Fin.cast h (finProdFinEquiv p)) out = _
  rw [flat_grid_matrix k B h p]
  rw [hc]
  have hp := flat_grid_matrix k B h ((gridTranspose k B).symm p)
  rw [gridMatrix_symm_transpose] at hp
  rw [← hp]
  simp only [Fin.cast_cast,Fin.cast_refl,id_eq,xr,Equiv.symm_apply_apply]

/-- Exact one-scale inequality for a real raw transpose computation. -/
theorem transpose_finite_bound [Fintype State]
    (C : RawScanProgram ((k*B)*(k*B)) q L State) (hB : 0<B)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hc : C.Transposes out) :
    (((k*B)*(k*B) : ℕ):ℝ) - (((k*B)*k : ℕ):ℝ)*(11*q)^L ≤
      (((11*q)^L+1:ℕ):ℝ) * (C.badVolume B + s*L*((k*B)*k)) := by
  have hlen : ((k*B)*k)*B=(k*B)*(k*B) := by ring
  let C' := C.castLength hlen.symm
  have hh := C'.onGrid.transpose_bound (C'.views hB) s hstate out
    (C.regrouped_transposes out hc hlen)
  rw [C'.views_badVolume hB] at hh
  have he : C'.badVolume B = C.badVolume B := C.badVolume_castLength hlen.symm B
  rw [he] at hh
  push_cast at hh ⊢
  nlinarith only [hh]
/-- Division-form bound at every positive aligned scale dividing the side. -/
theorem transpose_bound_of_dvd [Fintype State]
    (C : RawScanProgram (d*d) q L State) (hB : 0<B) (hBd : B ∣ d)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hc : C.Transposes out) :
    (((d*d:ℕ):ℝ) - ((11*q)^L:ℕ)*((d*d:ℕ):ℝ)/B) ≤
      (((11*q)^L+1:ℕ):ℝ) *
        (C.badVolume B + (s:ℝ)*L*(((d*d:ℕ):ℝ)/B)) := by
  obtain ⟨k,hk⟩ := hBd
  have hd : d=k*B := hk.trans (Nat.mul_comm B k)
  clear hk
  subst d
  have hh := C.transpose_finite_bound hB s hstate out hc
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hdiv : (((k*B)*(k*B):ℕ):ℝ)/(B:ℝ) = (((k*B)*k:ℕ):ℝ) := by
    push_cast
    field_simp
  rw [mul_div_assoc,hdiv]
  push_cast at hh ⊢
  nlinarith only [hh]

end RawScanProgram
end BitWord

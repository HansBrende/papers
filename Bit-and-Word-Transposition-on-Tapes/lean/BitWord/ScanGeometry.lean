import BitWord.ScanAncestry
import BitWord.GeometryStageScales

namespace BitWord
open Classical
open Geometry

/-- Conjugate the actual raw-position endpoint into aligned bin coordinates. -/
def stageGrid {n B : ℕ} (T : Stage (n * B)) : Equiv.Perm (Grid n B) :=
  finProdFinEquiv.trans (T.endpoint.trans finProdFinEquiv.symm)

 theorem grid_flat_div {n B : ℕ} (hB : 0 < B) (p : Grid n B) :
     (finProdFinEquiv p).val / B = p.1.val := by
   change (p.2.val + B * p.1.val) / B = p.1.val
   rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt p.2.isLt]
   simp

 theorem stageGrid_inverse_flat {n B : ℕ} (T : Stage (n * B)) (p : Grid n B) :
     finProdFinEquiv ((stageGrid T).symm p) = T.endpoint.symm (finProdFinEquiv p) := by
   change finProdFinEquiv (finProdFinEquiv.symm (T.endpoint.symm (finProdFinEquiv p))) = _
   exact finProdFinEquiv.apply_symm_apply _

 noncomputable def stageBad {n B : ℕ} (T : Stage (n * B)) : Finset (Grid n B) :=
   Finset.univ.filter (fun p => (finProdFinEquiv p).val ∈ T.bad B)

 noncomputable def stageView {n B : ℕ} (T : Stage (n * B)) (hB : 0 < B) :
     PermutationView (stageGrid T) where
   bad := stageBad T
   pred j := Finset.univ.filter (fun k : Fin n => k.val ∈ T.predecessors B j.val)
   pred_card j := by
     have hc : (Finset.univ.filter (fun k : Fin n => k.val ∈ T.predecessors B j.val)).card ≤
         (T.predecessors B j.val).card := by
       apply Finset.card_le_card_of_injOn Fin.val
       · intro k hk
         exact (Finset.mem_filter.mp hk).2
       · exact fun _ _ _ _ h => Fin.ext h
     exact hc.trans (T.predecessors_card_le hB j.val)
   good_pred p hp := by
     apply Finset.mem_filter.mpr
     refine ⟨Finset.mem_univ _, ?_⟩
     have hf : T.act true (finProdFinEquiv p).val =
         (finProdFinEquiv ((stageGrid T).symm p)).val := by
       rw [stageGrid_inverse_flat]
       change finiteAct T.endpoint.symm (finProdFinEquiv p).val = _
       simp only [finiteAct, dite_eq_left (finProdFinEquiv p).isLt]
     have hn : T.act true (finProdFinEquiv p).val ∉ T.bad B := by
       rw [hf]
       simpa [stageBad] using hp
     have hm := T.predecessor_mem (finProdFinEquiv p).isLt hn
     rw [hf, grid_flat_div hB, grid_flat_div hB] at hm
     exact hm

 theorem stageBad_card {n B : ℕ} (T : Stage (n * B)) :
     (stageBad T).card = (T.bad B).card := by
   let f : Grid n B → ℕ := fun p => (finProdFinEquiv p).val
   have hi : Function.Injective f := fun x y h => finProdFinEquiv.injective (Fin.ext h)
   have he : (stageBad T).image f = T.bad B := by
     ext x
     constructor
     · intro hx
       obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
       exact (Finset.mem_filter.mp hp).2
     · intro hx
       have hxp : x < n * B := Finset.mem_range.mp (T.bad_subset_range B hx)
       let p : Grid n B := finProdFinEquiv.symm ⟨x, hxp⟩
       have hp : f p = x := by
         exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨x, hxp⟩)
       exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [f, hp] using hx⟩, hp⟩
   rw [← he, Finset.card_image_of_injective _ hi]

 @[simp] theorem stageView_bad_card {n B : ℕ} (T : Stage (n * B)) (hB : 0 < B) :
     (stageView T hB).bad.card = (T.bad B).card := stageBad_card T

end BitWord

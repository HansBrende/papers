import BitWord.GeometryStage

namespace BitWord.Geometry

namespace BlockOperation
/-- A zero marker for operations that are never bad at any positive scale. -/
def entryWidth : BlockOperation → ℕ
  | .entries k _ _ _ _ => k
  | _ => 0

theorem bad_eq (op : BlockOperation) (B : ℕ) : op.bad B ↔ BadAt B op.entryWidth := by
  cases op <;> simp [bad, entryWidth, BadAt, volume]
end BlockOperation

namespace PartitionStage
variable {P : ℕ} (T : PartitionStage P)

 theorem bad_eq_badBlocks (B : ℕ) : T.bad B =
     badBlocks Finset.univ T.intervals.points
       (fun i => (T.operation i).entryWidth) B := by
   classical
   ext x
   simp only [mem_bad, badBlocks, Finset.mem_biUnion, Finset.mem_filter,
     Finset.mem_univ, true_and, IntervalFamily.mem_points]
   simp only [BlockOperation.bad_eq]

 theorem total_bad_volume_le {m : ℕ} (B : Fin m → ℕ)
     (hsep : ∀ i j, i < j → volume (B i) ≤ B j) :
     ∑ i, (T.bad (B i)).card ≤ P := by
   classical
   simp_rw [T.bad_eq_badBlocks]
   apply (Geometry.total_bad_volume_le Finset.univ T.intervals.points
     (fun i => (T.operation i).entryWidth) B hsep (Finset.range P) ?_ ?_).trans_eq
   · exact Finset.card_range P
   · intro i hi x hx
     have hmem := (T.intervals.mem_points i x).mp hx
     exact Finset.mem_range.mpr (lt_of_lt_of_le hmem.2 (T.bounded i))
   · intro i hi j hj hij
     apply Finset.disjoint_left.mpr
     intro x hxi hxj
     exact hij (T.intervals.contains_unique
       ((T.intervals.mem_points i x).mp hxi) ((T.intervals.mem_points j x).mp hxj))

end PartitionStage

namespace Stage
 theorem total_bad_volume_le {P m : ℕ} (T : Stage P) (B : Fin m → ℕ)
     (hsep : ∀ i j, i < j → volume (B i) ≤ B j) :
     ∑ i, (T.bad (B i)).card ≤ P := by
   cases T with
   | partition T => exact T.total_bad_volume_le B hsep
   | parity he dir => simp [bad]
end Stage
end BitWord.Geometry

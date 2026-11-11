import AdaptiveTransfer.ClusterGeometry
import AdaptiveTransfer.ClusterChart
import AdaptiveTransfer.NativeTimelyData

/-! The signed carrier is the sum of actual native unit head walks. Its
bounded-speed geometry is derived from those walks and actual append times. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations BoundedNesting MergeDepth
open scoped BigOperators

theorem clusterCarrier_step_bound {k : ℕ} (σ : ClusterSignature k) {xs : Fin k → ℕ → ℤ}
    (hx : ∀ h, IsWalk (xs h)) (t : ℕ) :
    (clusterCarrier σ xs (t + 1) - clusterCarrier σ xs t).natAbs ≤ k := by
  have hh : |clusterCarrier σ xs (t + 1) - clusterCarrier σ xs t| ≤ (k : ℤ) := by
    unfold clusterCarrier
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ h : ClusterHeads σ,
          |clusterOrient (σ h.val) (xs h.val (t + 1)) - clusterOrient (σ h.val) (xs h.val t)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h : ClusterHeads σ, (1 : ℤ) := by
        apply sum_le_sum
        intro h _
        have he := hx h.val t
        simp only [clusterOrient]
        split_ifs
        · simpa only [neg_sub_neg, abs_sub_comm] using he
        · exact he
      _ ≤ k := by simpa only [sum_const, card_univ, nsmul_eq_mul, mul_one] using
          (show (Fintype.card (ClusterHeads σ) : ℤ) ≤ k by exact_mod_cast clusterHeads_card_le σ)
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh

/-- Actual native geometry for each specified input-dependent coherent chart.
The real chart is not encoded and no desired chunk is assumed. -/
theorem native_cluster_slab_geometry {M : TM} {d b a : ℕ} {c J : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (g : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime J) :
    let τ := trace M (List.ofFn X)
    ∃ (ell : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ τ.haltTime ∧
      let C := selectedSlab g.carrier (slabWidth (d * d * b) a c) ell s e
      C.card ≤ (d * d * b) / 2 ∧ (runStarts C).card ≤ clusterRunCap M.k a c ∧
      clusterSaving d b M.k a c ≤
        ((omittedSlabBits d b τ.input (fun j => appendTime τ τ.haltTime j.val) C).card : ℝ) -
          (a : ℝ) * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ) + M.k) := by
  let τ := trace M (List.ofFn X)
  have hX : X ∈ fibre M (d * d * b) τ := mem_fibre.mpr rfl
  obtain ⟨hT, happ⟩ := fibre_haltTime hX hcorrect
  have hpos : 0 < d * d * b := by omega
  have hTpos := prefix_pos hd hb happ.ge
  exact exists_cluster_slab_geometry hd hb hP (by exact_mod_cast ha) g.k_pos hc
    τ.abs_input_succ_sub_le (fun t _ => clusterCarrier_step_bound g.signature τ.work_isWalk t)
    (fun i j hij => appendTime_strictMonoOn τ τ.haltTime
      (by simpa only [Set.mem_Iio, happ] using i.isLt)
      (by simpa only [Set.mem_Iio, happ] using j.isLt) hij)
    (fun i => appendTime_lt τ τ.haltTime (by simpa only [happ] using i.isLt))
    (runtime_le hpos hTpos hT)

end AdaptiveTransfer

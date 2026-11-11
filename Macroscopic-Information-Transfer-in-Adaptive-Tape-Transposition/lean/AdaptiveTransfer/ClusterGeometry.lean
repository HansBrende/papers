import AdaptiveTransfer.SlabGeometry
import AdaptiveTransfer.ClusterWalls

/-! Actual finite slab selection for a speed-k carrier, including the paid
multi-core snapshot surcharge and the original raw-head stripe margin. -/

namespace AdaptiveTransfer
open Finset NativeRelations BoundedNesting MergeDepth Transpose

noncomputable def clusterRunCap (k a : ℕ) (c : ℝ) : ℕ := slabRunCap ((a : ℝ) * k) c

noncomputable def clusterSaving (d b k a : ℕ) (c : ℝ) : ℝ :=
  (d * d * b : ℕ) / (4 * (clusterRunCap k a c : ℝ)) -
    3 * (clusterRunCap k a c : ℝ) * d * b - (a : ℝ) * (k + 1)

/-- Genuine finite slab selection, including the initial-blank short case and
the paid snapshot in the long case. The input width is arbitrary positive. -/
theorem exists_cluster_slab_geometry {d b T k : ℕ} {a c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hk : 1 ≤ k) (hc : 1 ≤ c)
    {x y : ℕ → ℤ} (hx : IsWalk x) (hy : ∀ t < T - 1, (y (t + 1) - y t).natAbs ≤ k)
    {ot : Fin (d * d * b) → ℕ} (hot : StrictMono ot) (hotT : ∀ r, ot r < T)
    (hT : (T : ℝ) ≤ 2 * c * (d * d * b : ℕ)) :
    ∃ (ell : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      let C := selectedSlab y (slabWidth (d * d * b) a c) ell s e
      C.card ≤ (d * d * b) / 2 ∧ (runStarts C).card ≤ slabRunCap (a * k) c ∧
      (d * d * b : ℕ) / (4 * (slabRunCap (a * k) c : ℝ)) -
          3 * (slabRunCap (a * k) c : ℝ) * d * b - a * (k + 1) ≤
        ((omittedSlabBits d b x ot C).card : ℝ) -
          a * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ) + k) := by
  classical
  let P := d * d * b
  let W := slabWidth P a c
  let N := slabRunCap (a * k) c
  have hPpos : 0 < P := by dsimp [P]; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hW : 1 ≤ W := Nat.one_le_ceil_iff.mpr (by positivity)
  have hN : (0 : ℝ) < N := by dsimp [N, slabRunCap]; positivity
  obtain ⟨u, _, hKdiv⟩ := exists_offset_slabTransitions_le_speed hW T hy
  let K := slabTransitions y W T u
  let m : ℕ → ℤ := fun t => slabIdx W u (y t)
  have hKmem : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K := fun t ht hne =>
    mem_filter.mpr ⟨mem_range.mpr ht, hne⟩
  have hKN : K.card + 1 ≤ N :=
    (Nat.add_le_add_right hKdiv 1).trans (slab_wall_count_bound ha hc hPpos hT)
  have hex : ∃ (ms : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      ((Ico s e).filter fun t => m t = ms).card ≤ P / 2 ∧
      ((s = 0 ∧ P ≤ 2 * N * (outIn ot ((Ico s e).filter fun t => m t = ms)).card) ∨
        P * (P / 2) < 4 * T * (outIn ot ((Ico s e).filter fun t => m t = ms)).card) := by
    rcases exists_slab_chunk_dichotomy hP hKmem hotT with
      ⟨ms, hh, ho⟩ | ⟨ms, s, e, hse, he, hh, ho⟩
    · exact ⟨ms, 0, T, Nat.zero_le _, le_rfl, hh, Or.inl ⟨rfl,
        ho.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hKN))⟩⟩
    · exact ⟨ms, s, e, hse, he, hh, Or.inr ho⟩
  obtain ⟨ms, s, e, hse, heT, hhalf, hcases⟩ := hex
  let C := (Ico s e).filter fun t => m t = ms
  have hCT : ∀ t ∈ C, t < T := fun t ht =>
    (mem_Ico.mp (mem_filter.mp ht).1).2.trans_le heT
  have hruns : (runStarts C).card ≤ N := (card_runStarts_chunk_le heT hKmem).trans hKN
  have hstripe := outIn_card_le_two_indep_add_six_runs hd hb hx hot hCT hhalf
  have hstripe' : ((outIn ot C).card : ℝ) ≤
      2 * ((omittedSlabBits d b x ot C).card : ℝ) + 6 * (N : ℝ) * d * b := by
    exact_mod_cast hstripe.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 6 hruns))) _)
  have hCeq : selectedSlab y W ((u : ℤ) + ms * W) s e = C := by
    ext t
    simp only [selectedSlab, C, mem_filter]
    exact and_congr_right fun _ => (slab_index_iff hW (y t) ms).symm
  refine ⟨(u : ℤ) + ms * W, s, e, hse, heT, ?_⟩
  change (selectedSlab y W ((u : ℤ) + ms * W) s e).card ≤ P / 2 ∧ _
  rw [hCeq]
  refine ⟨hhalf, hruns, ?_⟩
  change (P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a * (k + 1) ≤
    ((omittedSlabBits d b x ot C).card : ℝ) - a * (if s = 0 then 0 else (W : ℝ) + k)
  rcases hcases with ⟨hs, hshort⟩ | hlong
  · have hshort' : (P : ℝ) ≤ 2 * (N : ℝ) * (outIn ot C).card := by exact_mod_cast hshort
    have hmargin : (P : ℝ) / (4 * (N : ℝ)) ≤
        (omittedSlabBits d b x ot C).card + 3 * (N : ℝ) * d * b := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hstripe' (show 0 ≤ (N : ℝ) by positivity)]
    simp only [hs, ite_true, mul_zero, sub_zero]
    have hcost : 0 ≤ a * ((k : ℝ) + 1) := by positivity
    linarith
  · have hhalf3 : P ≤ 3 * (P / 2) := by dsimp [P] at *; omega
    have hhalf3' : (P : ℝ) ≤ 3 * (P / 2 : ℕ) := by exact_mod_cast hhalf3
    have hlong' : (P : ℝ) * (P / 2 : ℕ) < 4 * (T : ℝ) * (outIn ot C).card := by
      exact_mod_cast hlong
    have hTout := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (outIn ot C).card)
    have hpoly : (P : ℝ) * P < (P : ℝ) * (24 * c * (outIn ot C).card) := by
      nlinarith [mul_le_mul_of_nonneg_left hhalf3' hPr.le]
    have hout : (P : ℝ) / (24 * c) < (outIn ot C).card := by
      apply (div_lt_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using (mul_lt_mul_iff_right₀ hPr).mp hpoly
    have hU : (P : ℝ) / (48 * c) - 3 * (N : ℝ) * d * b <
        (omittedSlabBits d b x ot C).card := by
      have he : (P : ℝ) / (24 * c) = 2 * ((P : ℝ) / (48 * c)) := by field_simp; ring
      linarith
    have hcost : a * (if s = 0 then 0 else (W : ℝ) + k) ≤ (P : ℝ) / (80 * c) + a * (k + 1) := by
      have hs := slab_snapshot_bound (P := P) ha hc
      change a * (W : ℝ) ≤ (P : ℝ) / (80 * c) + a at hs
      split_ifs <;> nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    have hcomp := slab_cap_comparison (P := P) (a := a * k)
      (one_le_mul_of_one_le_of_one_le ha (by exact_mod_cast hk)) hc
    have he : (P : ℝ) / (48 * c) - (P : ℝ) / (80 * c) = (P : ℝ) / (120 * c) := by
      field_simp; ring
    change (P : ℝ) / (4 * (N : ℝ)) ≤ (P : ℝ) / (120 * c) at hcomp
    linarith


end AdaptiveTransfer

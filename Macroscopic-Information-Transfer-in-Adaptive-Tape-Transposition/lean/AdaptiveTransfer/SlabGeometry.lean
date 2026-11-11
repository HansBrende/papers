import NativeRelations.OneFreeHeadSmallExcursion

/-! # Finite slab selection with the snapshot-adjusted margin

The finite theorem constructs a chunk from two walks and actual ordered append
times. The native endpoint obtains all these data from the one input's own
execution; it assumes neither a common trace nor the desired chunk.
-/

namespace AdaptiveTransfer

open Finset NativeRelations BoundedNesting MergeDepth Transpose

noncomputable def slabWidth (P : ℕ) (a c : ℝ) : ℕ := ⌈(P : ℝ) / (80 * a * c)⌉₊

noncomputable def slabRunCap (a c : ℝ) : ℕ := ⌊160 * a * c ^ 2⌋₊ + 1

def selectedSlab (y : ℕ → ℤ) (W : ℕ) (ell : ℤ) (s e : ℕ) : Finset ℕ :=
  (Ico s e).filter fun t => ell ≤ y t ∧ y t < ell + W

def omittedSlabBits (d b : ℕ) (x : ℕ → ℤ) (ot : Fin (d * d * b) → ℕ)
    (C : Finset ℕ) : Finset (Fin (d * d * b)) :=
  (outIn ot C).image (tposOf d b) \ inCells (d * d * b) x C

/-- Integer slab indices describe the same half-open cell intervals used by
ordinary, clustered and multiport replay. -/
theorem slab_index_iff {W u : ℕ} (hW : 1 ≤ W) (y m : ℤ) :
    slabIdx W u y = m ↔
      (u : ℤ) + m * W ≤ y ∧ y < (u : ℤ) + m * W + W := by
  have hWz : (0 : ℤ) < W := by exact_mod_cast hW
  unfold slabIdx
  rw [Int.ediv_eq_iff_of_pos hWz]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

/-- The common wall-count budget for a carrier of any natural speed. -/
theorem slab_wall_count_bound {P T k : ℕ} {a c : ℝ} (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hP : 0 < P) (hT : (T : ℝ) ≤ 2 * c * P) :
    k * (T - 1) / slabWidth P a c + 1 ≤ slabRunCap (a * k) c := by
  apply Nat.add_le_add_right
  apply Nat.le_floor
  have hd : 0 < 80 * a * c := by positivity
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hmul : (((k * (T - 1)) / slabWidth P a c : ℕ) : ℝ) * (slabWidth P a c : ℝ) ≤ k * T := by
    exact_mod_cast (Nat.div_mul_le_self (k * (T - 1)) (slabWidth P a c)).trans
      (Nat.mul_le_mul_left k (Nat.sub_le T 1))
  have hwidth : (P : ℝ) / (80 * a * c) ≤ slabWidth P a c := Nat.le_ceil _
  have hh := (mul_le_mul_of_nonneg_left hwidth
    (Nat.cast_nonneg ((k * (T - 1)) / slabWidth P a c))).trans
    (hmul.trans (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg k)))
  have hquot : 0 < (P : ℝ) / (80 * a * c) := div_pos hPr hd
  apply (le_div_iff₀ hquot).mpr at hh
  convert hh using 1
  field_simp
  ring

theorem slab_snapshot_bound {P : ℕ} {a c : ℝ} (ha : 1 ≤ a) (hc : 1 ≤ c) :
    a * (slabWidth P a c : ℝ) ≤ (P : ℝ) / (80 * c) + a := by
  have hd : 0 < 80 * a * c := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (Nat.ceil_lt_add_one (show 0 ≤ (P : ℝ) / (80 * a * c) by positivity)).le
    (show 0 ≤ a by linarith)
  calc
    a * (slabWidth P a c : ℝ) ≤ a * ((P : ℝ) / (80 * a * c) + 1) := hh
    _ = (P : ℝ) / (80 * c) + a := by field_simp

theorem slab_cap_comparison {P : ℕ} {a c : ℝ} (ha : 1 ≤ a) (hc : 1 ≤ c) :
    (P : ℝ) / (4 * (slabRunCap a c : ℝ)) ≤ (P : ℝ) / (120 * c) := by
  have hN : 160 * a * c ^ 2 < (slabRunCap a c : ℝ) := by
    simpa [slabRunCap] using Nat.lt_floor_add_one (160 * a * c ^ 2)
  have hc2 : c ≤ c ^ 2 := by nlinarith
  have hac2 : c ^ 2 ≤ a * c ^ 2 := by nlinarith [sq_nonneg c]
  have hd : 120 * c ≤ 4 * (slabRunCap a c : ℝ) := by nlinarith
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg P) (by positivity) hd

/-- Genuine finite slab selection, including the initial-blank short case and
the paid snapshot in the long case. The input width is arbitrary positive. -/
theorem exists_slab_geometry {d b T : ℕ} {a c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {x y : ℕ → ℤ} (hx : IsWalk x) (hy : IsWalk y)
    {ot : Fin (d * d * b) → ℕ} (hot : StrictMono ot) (hotT : ∀ r, ot r < T)
    (hT : (T : ℝ) ≤ 2 * c * (d * d * b : ℕ)) :
    ∃ (ell : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      let C := selectedSlab y (slabWidth (d * d * b) a c) ell s e
      C.card ≤ (d * d * b) / 2 ∧ (runStarts C).card ≤ slabRunCap a c ∧
      (d * d * b : ℕ) / (4 * (slabRunCap a c : ℝ)) -
          3 * (slabRunCap a c : ℝ) * d * b - a ≤
        ((omittedSlabBits d b x ot C).card : ℝ) -
          a * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
  classical
  let P := d * d * b
  let W := slabWidth P a c
  let N := slabRunCap a c
  have hPpos : 0 < P := by dsimp [P]; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hW : 1 ≤ W := Nat.one_le_ceil_iff.mpr (by positivity)
  have hN : (0 : ℝ) < N := by dsimp [N, slabRunCap]; positivity
  obtain ⟨u, _, hKdiv⟩ := exists_offset_slabTransitions_le hy hW T
  let K := slabTransitions y W T u
  let m : ℕ → ℤ := fun t => slabIdx W u (y t)
  have hKmem : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K := fun t ht hne =>
    mem_filter.mpr ⟨mem_range.mpr ht, hne⟩
  have hKN : K.card + 1 ≤ N :=
    (Nat.add_le_add_right hKdiv 1).trans
      (by simpa only [one_mul, Nat.cast_one, mul_one] using
        slab_wall_count_bound (k := 1) ha hc hPpos hT)
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
  change (P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a ≤
    ((omittedSlabBits d b x ot C).card : ℝ) - a * (if s = 0 then 0 else (W : ℝ))
  rcases hcases with ⟨hs, hshort⟩ | hlong
  · have hshort' : (P : ℝ) ≤ 2 * (N : ℝ) * (outIn ot C).card := by exact_mod_cast hshort
    have hmargin : (P : ℝ) / (4 * (N : ℝ)) ≤
        (omittedSlabBits d b x ot C).card + 3 * (N : ℝ) * d * b := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hstripe' (show 0 ≤ (N : ℝ) by positivity)]
    simp only [hs, ite_true, mul_zero, sub_zero]
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
    have hcost : a * (if s = 0 then 0 else (W : ℝ)) ≤ (P : ℝ) / (80 * c) + a := by
      apply le_trans _ (slab_snapshot_bound (P := P) ha hc)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      split_ifs <;> simp [W]
    have hcomp := slab_cap_comparison (P := P) ha hc
    have he : (P : ℝ) / (48 * c) - (P : ℝ) / (80 * c) = (P : ℝ) / (120 * c) := by
      field_simp; ring
    change (P : ℝ) / (4 * (N : ℝ)) ≤ (P : ℝ) / (120 * c) at hcomp
    linarith

/-- The finite geometry lemma on the actual native execution of one timely
correct input. No all-input correctness or shared-trace hypothesis occurs. -/
theorem native_slab_geometry {M : TM} {d b : ℕ} {a c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} (htr : TransposesInput M d b c X) (f : Fin M.k) :
    let τ := trace M (List.ofFn X)
    let T := τ.haltTime
    let ot : Fin (d * d * b) → ℕ := fun r => appendTime τ T r.val
    ∃ (ell : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      let C := selectedSlab (τ.work f) (slabWidth (d * d * b) a c) ell s e
      C.card ≤ (d * d * b) / 2 ∧ (runStarts C).card ≤ slabRunCap a c ∧
      (d * d * b : ℕ) / (4 * (slabRunCap a c : ℝ)) -
          3 * (slabRunCap a c : ℝ) * d * b - a ≤
        ((omittedSlabBits d b τ.input ot C).card : ℝ) -
          a * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
  classical
  let τ := trace M (List.ofFn X)
  have hX : X ∈ fibre M (d * d * b) τ := mem_fibre.mpr rfl
  obtain ⟨hT, happ⟩ := fibre_haltTime hX htr
  have hpos : 0 < d * d * b := by omega
  have hTpos := prefix_pos hd hb happ.ge
  apply exists_slab_geometry hd hb hP ha hc τ.abs_input_succ_sub_le (τ.work_isWalk f)
  · intro i j hij
    exact appendTime_strictMonoOn τ τ.haltTime
      (by simpa only [Set.mem_Iio, happ] using i.isLt)
      (by simpa only [Set.mem_Iio, happ] using j.isLt) hij
  · intro i
    exact appendTime_lt τ τ.haltTime (by simpa only [happ] using i.isLt)
  · exact runtime_le hpos hTpos hT

end AdaptiveTransfer

import GapAreaMemo.Z3DDensity

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: the time cover

Bank C before `C_W` (`W = 2^ℓ`) is the sequence of segments: the first rise
of `C_1`, the descent of `C_1`, the first rise of `C_2`, …, the descent of
`C_{W-1}`, the first rise of `C_W`. Every landing of block `ℓ` is copied by
the bank-C chain into all of them at its relative level, so every window of
a segment of relative length about `1152/W²` meets the orbit. The segment
window lemma then covers the whole range by windows of a fixed length.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies

variable (P : Index)

/-- The bank-C chain of a landing, at a lower zigzag `C_i`. -/
theorem land_chain (F : Finset (ActualFamily P.heads P.T)) {ℓ j q N : ℕ} (hF : P.Needs F ℓ)
    (hℓν : ℓ ≤ P.ν) (hL : P.Land F (P.root j) ℓ q N) {i : ℕ} (hi1 : 1 ≤ i) (hiq : i ≤ q) :
    ∃ e, ((e + 1 : ℕ) : ℚ) = P.cc i * (((2 * N + 1 : ℕ) : ℚ) / P.cc q) ∧ 0 < e ∧
      e + 1 < P.cc i ∧ P.U i - e ∈ shadowOrbit F (P.root j) ∧
      P.U (i - 1) + fC i * (e + 1) - 1 ∈ shadowOrbit F (P.root j) := by
  obtain ⟨hq1, hq2, hstart, hN0, hNc⟩ := hL
  have h2l := Nat.one_le_two_pow (n := ℓ)
  have hqK := P.block_le_K hℓν hq2
  have hch := P.early_chain F (P.root j) q (2 * N) (by omega) hqK hstart
    (fun i' h1 h2 => ⟨(hF.1 i' true h1 (by omega)).2.2, (hF.1 i' false h1 (by omega)).2.2⟩)
    (by omega) (by omega) (q - i) (by omega)
  rw [show q - (q - i) = i by omega] at hch
  obtain ⟨e, he1, he0, he2, -, he3, he4⟩ := hch
  refine ⟨e, ?_, he0, he2, he3, he4⟩
  have hcq : (0 : ℚ) < P.cc q := by exact_mod_cast P.cc_pos q
  have h : ((e + 1 : ℕ) : ℚ) * P.cc q = P.cc i * ((2 * N + 1 : ℕ) : ℚ) := by exact_mod_cast he1
  rw [mul_div_assoc', eq_div_iff hcq.ne']
  exact h

/-- A hit in the first rise of `C_i`, `1 ≤ i ≤ W`. -/
theorem rise_hit (F : Finset (ActualFamily P.heads P.T)) {ℓ j i : ℕ} (hF : P.Needs F ℓ)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hj1 : 1 ≤ j) (hjd : j < P.d) (hi1 : 1 ≤ i) (hiW : i ≤ 2 ^ ℓ)
    {z w : ℕ} (hz : P.U (i - 1) ≤ z) (hzw : z + w ≤ P.U (i - 1) + fC i * P.cc i)
    (hw : ((fC i * P.cc i : ℕ) : ℚ) * (1152 / ((2 : ℚ) ^ ℓ) ^ 2 + 4 / (P.a (2 ^ ℓ) : ℚ)) ≤
      (w : ℚ) - 1)
    (hsmall : 4 / (P.a (2 ^ ℓ) : ℚ) + 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ 1) :
    ∃ u ∈ shadowOrbit F (P.root j), z ≤ u ∧ u ≤ z + w := by
  have hpos : 0 < fC i * P.cc i := Nat.mul_pos (fC_pos i) (P.cc_pos i)
  have hhq : (0 : ℚ) < (fC i * P.cc i : ℕ) := by exact_mod_cast hpos
  have hA1 : ((z - P.U (i - 1) + 1 : ℕ) : ℚ) / (fC i * P.cc i : ℕ) ≤
      1 - ((w : ℚ) - 1) / (fC i * P.cc i : ℕ) := by
    rw [le_sub_iff_add_le, ← add_div, div_le_one hhq]
    have : z - P.U (i - 1) + 1 + w ≤ fC i * P.cc i + 1 := by omega
    have : ((z - P.U (i - 1) + 1 : ℕ) : ℚ) + w ≤ (fC i * P.cc i : ℕ) + 1 := by exact_mod_cast this
    linarith
  obtain ⟨q, N, hL, hy0, hy1⟩ := P.levels_window F hF hℓ6 hℓν hj1 hjd hpos (by positivity) hA1 hw
    hsmall
  obtain ⟨e, he, he0, he2, -, hmem⟩ := P.land_chain F hF hℓν hL hi1 (le_trans hiW hL.1)
  refine ⟨P.U (i - 1) + fC i * (e + 1) - 1, hmem, ?_, ?_⟩
  · have key : ((z - P.U (i - 1) + 1 : ℕ) : ℚ) < ((fC i * (e + 1) : ℕ) : ℚ) := by
      have : ((fC i * (e + 1) : ℕ) : ℚ) =
          ((fC i * P.cc i : ℕ) : ℚ) * (((2 * N + 1 : ℕ) : ℚ) / P.cc q) := by
        rw [Nat.cast_mul, he]; push_cast; ring
      rw [this]
      rw [div_lt_iff₀ hhq] at hy0
      linarith
    have : z - P.U (i - 1) + 1 < fC i * (e + 1) := by exact_mod_cast key
    omega
  · have key : ((fC i * (e + 1) : ℕ) : ℚ) < ((z - P.U (i - 1) + 1 : ℕ) : ℚ) + w := by
      have : ((fC i * (e + 1) : ℕ) : ℚ) =
          ((fC i * P.cc i : ℕ) : ℚ) * (((2 * N + 1 : ℕ) : ℚ) / P.cc q) := by
        rw [Nat.cast_mul, he]; push_cast; ring
      rw [this]
      have h' := hy1
      rw [← add_div, lt_div_iff₀ hhq] at h'
      linarith
    have : fC i * (e + 1) < z - P.U (i - 1) + 1 + w := by exact_mod_cast key
    omega

/-- A hit in the descent of `C_i`, `1 ≤ i < W`. -/
theorem descent_hit (F : Finset (ActualFamily P.heads P.T)) {ℓ j i : ℕ} (hF : P.Needs F ℓ)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hj1 : 1 ≤ j) (hjd : j < P.d) (hi1 : 1 ≤ i) (hiW : i < 2 ^ ℓ)
    {z w : ℕ} (hz : P.U i - P.cc i ≤ z) (hzw : z + w ≤ P.U i)
    (hw : (P.cc i : ℚ) * (1152 / ((2 : ℚ) ^ ℓ) ^ 2 + 4 / (P.a (2 ^ ℓ) : ℚ)) ≤ (w : ℚ) - 1)
    (hsmall : 4 / (P.a (2 ^ ℓ) : ℚ) + 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ 1) :
    ∃ u ∈ shadowOrbit F (P.root j), z ≤ u ∧ u ≤ z + w := by
  have hpos := P.cc_pos i
  have hhq : (0 : ℚ) < P.cc i := by exact_mod_cast hpos
  have hUi := P.U_ge i hi1
  have hA1 : ((P.U i + 1 - (z + w) : ℕ) : ℚ) / P.cc i ≤ 1 - ((w : ℚ) - 1) / P.cc i := by
    rw [le_sub_iff_add_le, ← add_div, div_le_one hhq]
    have : P.U i + 1 - (z + w) + w ≤ P.cc i + 1 := by omega
    have : ((P.U i + 1 - (z + w) : ℕ) : ℚ) + w ≤ P.cc i + 1 := by exact_mod_cast this
    linarith
  obtain ⟨q, N, hL, hy0, hy1⟩ := P.levels_window F hF hℓ6 hℓν hj1 hjd hpos (by positivity) hA1 hw
    hsmall
  obtain ⟨e, he, he0, he2, hmem, -⟩ := P.land_chain F hF hℓν hL hi1 (le_trans hiW.le hL.1)
  refine ⟨P.U i - e, hmem, ?_, ?_⟩
  · have key : ((e + 1 : ℕ) : ℚ) < ((P.U i + 1 - (z + w) : ℕ) : ℚ) + w := by
      rw [he]
      have h' := hy1
      rw [← add_div, lt_div_iff₀ hhq] at h'
      linarith
    have : e + 1 < P.U i + 1 - (z + w) + w := by exact_mod_cast key
    omega
  · have key : ((P.U i + 1 - (z + w) : ℕ) : ℚ) < ((e + 1 : ℕ) : ℚ) := by
      rw [he]
      rw [div_lt_iff₀ hhq] at hy0
      linarith
    have : P.U i + 1 - (z + w) < e + 1 := by exact_mod_cast key
    omega

/-! ### The segments of bank C -/

/-- Start of segment `s`: even `s = 2k` is the first rise of `C_{k+1}`, odd `s = 2k+1` its
descent. -/
def segStart (s : ℕ) : ℕ :=
  if s % 2 = 0 then P.U (s / 2) else P.U (s / 2) + fC (s / 2 + 1) * P.cc (s / 2 + 1)

def segLen (s : ℕ) : ℕ :=
  if s % 2 = 0 then fC (s / 2 + 1) * P.cc (s / 2 + 1) else P.cc (s / 2 + 1)

/-- The window length of segment `s`. -/
def segW (ℓ s : ℕ) : ℕ := P.segLen s * 1152 / 4 ^ ℓ + P.segLen s * 4 / P.a (2 ^ ℓ) + 3

/-- The window length of the whole cover. -/
def capG (ℓ : ℕ) : ℕ := 2 * (2 * P.L * 1152 / 4 ^ ℓ + 2 * P.L * 4 / P.a (2 ^ ℓ) + 3)

theorem segStart_succ (s : ℕ) : P.segStart (s + 1) = P.segStart s + P.segLen s := by
  rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
  · simp only [segStart, segLen]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
  · simp only [segStart, segLen]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega]
    rfl

theorem nat_div_gt (x y : ℕ) (hy : 0 < y) : (x : ℚ) / y - 1 < ((x / y : ℕ) : ℚ) := by
  have h := Nat.lt_div_mul_add (a := x) hy
  have hy' : (0 : ℚ) < y := by exact_mod_cast hy
  have h' : (x : ℚ) < (x / y : ℕ) * y + y := by exact_mod_cast h
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hy']
  linarith

theorem segW_ge (ℓ s : ℕ) :
    (P.segLen s : ℚ) * (1152 / ((2 : ℚ) ^ ℓ) ^ 2 + 4 / (P.a (2 ^ ℓ) : ℚ)) ≤ (P.segW ℓ s : ℚ) - 1 := by
  have h1 := nat_div_gt (P.segLen s * 1152) (4 ^ ℓ) (by positivity)
  have h2 := nat_div_gt (P.segLen s * 4) (P.a (2 ^ ℓ)) (P.a_pos _)
  have h4 : ((2 : ℚ) ^ ℓ) ^ 2 = ((4 ^ ℓ : ℕ) : ℚ) := by
    push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold segW
  push_cast at h1 h2 ⊢
  rw [h4]
  push_cast
  have e1 : (P.segLen s : ℚ) * (1152 / 4 ^ ℓ + 4 / (P.a (2 ^ ℓ) : ℚ)) =
      (P.segLen s : ℚ) * 1152 / 4 ^ ℓ + (P.segLen s : ℚ) * 4 / (P.a (2 ^ ℓ) : ℚ) := by ring
  rw [e1]
  linarith

theorem a_ge_block {ℓ k : ℕ} (hk : k ≤ 2 ^ ℓ) (hℓν : ℓ ≤ P.ν) :
    P.a (2 ^ ℓ) ≤ P.a k := by
  have hl : lev k ≤ ℓ := by
    have := lev_mono hk
    rwa [show lev (2 ^ ℓ) = ℓ from Nat.log_pow (by norm_num) ℓ] at this
  have he := P.exponent_ok (k := 2 ^ ℓ) (P.block_le_K hℓν (by have := Nat.one_le_two_pow (n := ℓ); omega))
  unfold a
  apply Nat.pow_le_pow_right (by norm_num)
  rw [show lev (2 ^ ℓ) = ℓ from Nat.log_pow (by norm_num) ℓ] at he ⊢
  omega

theorem cc_le_two_L (k : ℕ) : P.cc k ≤ 2 * P.L := by
  have := P.a_le_a_one k; have := P.a_one; unfold cc; omega

theorem segLen_le (s : ℕ) (hs : s / 2 + 1 ≤ P.K) : P.segLen s ≤ 2 * P.L := by
  unfold segLen
  split_ifs
  · rcases Nat.lt_or_ge (s / 2 + 1) 2 with h | h
    · have : fC (s / 2 + 1) = 1 := by unfold fC; rw [ite_eq_left (by omega)]
      rw [this, one_mul]; exact P.cc_le_two_L _
    · rw [P.fC_mul h hs]; exact P.cc_le_two_L _
  · exact P.cc_le_two_L _

theorem segLen_ge {ℓ s : ℕ} (hℓν : ℓ ≤ P.ν) (hs : s / 2 + 1 ≤ 2 ^ ℓ) :
    8 * P.a (2 ^ ℓ) ≤ P.segLen s := by
  have h := P.a_ge_block (k := s / 2 + 1) hs hℓν
  unfold segLen cc
  split_ifs
  · have := fC_pos (s / 2 + 1)
    nlinarith
  · omega

/-- **The time cover.** -/
theorem time_cover (F : Finset (ActualFamily P.heads P.T)) {ℓ j : ℕ} (hF : P.Needs F ℓ)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hj1 : 1 ≤ j) (hjd : j < P.d) (hα : 16 ≤ P.a (2 ^ ℓ)) :
    ∀ z, 1 ≤ z → z + P.capG ℓ ≤ P.segStart (2 * 2 ^ ℓ - 1) →
      ∃ u ∈ shadowOrbit F (P.root j), z ≤ u ∧ u ≤ z + P.capG ℓ := by
  have h2l := Nat.one_le_two_pow (n := ℓ)
  have h4l : 4096 ≤ 4 ^ ℓ := by
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ 4 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ6
  have hαq : (16 : ℚ) ≤ P.a (2 ^ ℓ) := by exact_mod_cast hα
  have hsmall : 4 / (P.a (2 ^ ℓ) : ℚ) + 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ 1 := by
    have h1 : 4 / (P.a (2 ^ ℓ) : ℚ) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ 1 / 2 := by
      have : (4096 : ℚ) ≤ ((2 : ℚ) ^ ℓ) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
        exact_mod_cast h4l
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hseglen : ∀ s, s < 2 * 2 ^ ℓ - 1 → P.segW ℓ s ≤ P.segLen s := by
    intro s hs
    have hge := P.segLen_ge (s := s) hℓν (by omega)
    have d1 : P.segLen s * 1152 / 4 ^ ℓ ≤ P.segLen s * 1152 / 4096 := Nat.div_le_div_left h4l (by norm_num)
    have d2 : P.segLen s * 4 / P.a (2 ^ ℓ) ≤ P.segLen s * 4 / 16 := Nat.div_le_div_left hα (by norm_num)
    unfold segW
    omega
  have hsegmax : ∀ s, s < 2 * 2 ^ ℓ - 1 → P.segW ℓ s ≤ P.capG ℓ / 2 := by
    intro s hs
    have hle := P.segLen_le s (by have := P.block_le_K hℓν (k := s / 2 + 1) (by omega); omega)
    have d1 : P.segLen s * 1152 / 4 ^ ℓ ≤ 2 * P.L * 1152 / 4 ^ ℓ :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ hle)
    have d2 : P.segLen s * 4 / P.a (2 ^ ℓ) ≤ 2 * P.L * 4 / P.a (2 ^ ℓ) :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ hle)
    unfold segW capG
    omega
  have hcover := SourceCovers.GapBound.window_cover (α := P.segStart) (w := P.segW ℓ)
    (N := 2 * 2 ^ ℓ - 1) (G := P.capG ℓ) (S := shadowOrbit F (P.root j))
    (fun s hs => by rw [P.segStart_succ]; have := hseglen s hs; omega)
    (fun s hs z hz hzw => by
      rw [P.segStart_succ] at hzw
      rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
      · have e1 : P.segStart (2 * k) = P.U k := by
          simp only [segStart]; rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]
        have e2 : P.segLen (2 * k) = fC (k + 1) * P.cc (k + 1) := by
          simp only [segLen]; rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega]
        have hw := P.segW_ge ℓ (2 * k)
        rw [e2] at hw
        rw [e1, e2] at hzw
        rw [e1] at hz
        exact P.rise_hit F hF hℓ6 hℓν hj1 hjd (i := k + 1) (by omega) (by omega)
          (by simpa using hz) (by simpa using hzw) (by exact_mod_cast hw) hsmall
      · have e1 : P.segStart (2 * k + 1) = P.U (k + 1) - P.cc (k + 1) := by
          simp only [segStart]; rw [ite_eq_right (by omega), show (2 * k + 1) / 2 = k by omega]
          have : P.U (k + 1) = P.U k + fC (k + 1) * P.cc (k + 1) + P.cc (k + 1) := rfl
          omega
        have e2 : P.segLen (2 * k + 1) = P.cc (k + 1) := by
          simp only [segLen]; rw [ite_eq_right (by omega), show (2 * k + 1) / 2 = k by omega]
        have hw := P.segW_ge ℓ (2 * k + 1)
        rw [e2] at hw
        rw [e2] at hzw
        rw [e1] at hz hzw
        have hUi := P.U_ge (k + 1) (by omega)
        exact P.descent_hit F hF hℓ6 hℓν hj1 hjd (i := k + 1) (by omega) (by omega) hz
          (by omega) hw hsmall)
    (fun s hs => by have := hsegmax s hs; omega)
    (fun s hs => by have := hsegmax s (by omega); have := hsegmax (s + 1) hs; omega)
    (by
      simp only [capG]
      generalize 2 * P.L * 1152 / 4 ^ ℓ = A
      generalize 2 * P.L * 4 / P.a (2 ^ ℓ) = B
      omega)
  have h0 : P.segStart 0 = 1 := by simp [segStart, U]
  intro z hz1 hz2
  exact hcover z (by rw [h0]; exact hz1) hz2

end SourceCovers.Z3D.Index

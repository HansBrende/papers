import GapAreaMemo.Z3DLandings
import GapAreaMemo.GapBound

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: dense landings

Fix a block level `ℓ` (`W = 2^ℓ`). If the orbit families contain the bank
zigzags of indices below `2W` and both exceptions, the landings of a column
root in the second rises of `C_q`, `W ≤ q < 2W`, have relative levels that
meet every window of relative length about `1152/W²` (van der Corput rows with
the dyadic offsets). The bank-C chains copy each landing level into every
segment of bank C before `C_W`: the first rises and the descents.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies

variable (P : Index)

/-- The families an orbit uses for block level `ℓ`. -/
def Needs (F : Finset (ActualFamily P.heads P.T)) (ℓ : ℕ) : Prop :=
  (∀ i up, 1 ≤ i → i < 2 * 2 ^ ℓ → P.famA i up ∈ F ∧ P.famB i up ∈ F ∧ P.famC i up ∈ F) ∧
    P.eFam ∈ F ∧ P.gFam ∈ F

theorem lev_block {ℓ k : ℕ} (h1 : 2 ^ ℓ ≤ k) (h2 : k < 2 * 2 ^ ℓ) : lev k = ℓ :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 (by rw [pow_succ]; omega)

theorem a_block {ℓ k : ℕ} (h1 : 2 ^ ℓ ≤ k) (h2 : k < 2 * 2 ^ ℓ) : P.a k = P.a (2 ^ ℓ) := by
  unfold a; rw [lev_block h1 h2, lev_block le_rfl (by have := Nat.one_le_two_pow (n := ℓ); omega)]

theorem block_le_K {ℓ k : ℕ} (hℓ : ℓ ≤ P.ν) (h2 : k < 2 * 2 ^ ℓ) : k ≤ P.K := by
  have := P.K_succ
  have : 2 * 2 ^ ℓ ≤ 2 ^ (P.ν + 1) := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) hℓ)
  omega

/-- A landing of block `ℓ` in the orbit of `s`. -/
def Land (F : Finset (ActualFamily P.heads P.T)) (s ℓ q N : ℕ) : Prop :=
  2 ^ ℓ ≤ q ∧ q < 2 * 2 ^ ℓ ∧ P.U q + 2 * N ∈ shadowOrbit F s ∧ 0 < N ∧ 2 * N + 2 ≤ P.cc q

/-- **Dense landing levels.** -/
theorem levels_dense (F : Finset (ActualFamily P.heads P.T)) {ℓ j : ℕ} (hF : P.Needs F ℓ)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hj1 : 1 ≤ j) (hjd : j < P.d) {x₀ x₁ : ℚ}
    (hx0 : 2 / (P.a (2 ^ ℓ) : ℚ) ≤ x₀) (hx1 : x₁ ≤ 1 - 2 / (P.a (2 ^ ℓ) : ℚ))
    (hx : x₀ + 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ x₁) :
    ∃ q N, P.Land F (P.root j) ℓ q N ∧
      x₀ - 1 / (P.a (2 ^ ℓ) : ℚ) < ((2 * N + 1 : ℕ) : ℚ) / P.cc q ∧
      ((2 * N + 1 : ℕ) : ℚ) / P.cc q < x₁ + 1 / (P.a (2 ^ ℓ) : ℚ) := by
  have hα : (0 : ℚ) < P.a (2 ^ ℓ) := by exact_mod_cast P.a_pos _
  have hd : (0 : ℚ) < P.d := by exact_mod_cast P.d_pos'
  have hθ0 : (0 : ℚ) ≤ (j : ℚ) / P.d := by positivity
  have hθ1 : (j : ℚ) / P.d ≤ 1 := by
    rw [div_le_one hd]; exact_mod_cast hjd.le
  have hx00 : (0 : ℚ) ≤ x₀ := le_trans (by positivity) hx0
  have hx11 : x₁ ≤ 1 := le_trans hx1 (by linarith [show (0 : ℚ) ≤ 2 / P.a (2 ^ ℓ) by positivity])
  obtain ⟨z, hz, hz0, hz1⟩ := Covering.rowPoints_dense_of_le (k₀ := 2 ^ ℓ) (m := ℓ) (D := 2 ^ ℓ)
    (θ := (j : ℚ) / P.d) hℓ6 hθ0 hθ1 (by omega) hx00 hx11 hx
  obtain ⟨k, hk1, hk2, o, ho, hzo⟩ := hz
  rw [Finset.mem_coe] at ho
  simp only [Covering.offsets, mem_union, mem_image, mem_Icc] at ho
  have hk2' : k < 2 * 2 ^ ℓ := by omega
  have hkK := P.block_le_K hℓν hk2'
  have hak := P.a_block hk1 hk2'
  -- the landing parameters
  obtain ⟨p, sA, hp1, hpW, rfl⟩ : ∃ p sA, 1 ≤ p ∧ p ≤ 2 ^ ℓ ∧ o = offs ((j : ℚ) / P.d) p sA := by
    rcases ho with ⟨p, ⟨hp1, hpW⟩, rfl⟩ | ⟨p, ⟨hp1, hpW⟩, rfl⟩
    · exact ⟨p, false, hp1, hpW, by simp [offs]⟩
    · exact ⟨p, true, hp1, hpW, by simp [offs]⟩
  obtain ⟨sB, hsB⟩ : ∃ sB, z = zst ((j : ℚ) / P.d) p k sA sB := by
    rcases hzo with h | h
    · exact ⟨false, by rw [h]; simp only [zst, Bool.false_eq_true, ite_false]; ring⟩
    · exact ⟨true, by rw [h]; simp only [zst, ite_true]; ring⟩
  have hpK : p ≤ P.K := P.block_le_K hℓν (by omega)
  have hFA : ∀ i, 1 ≤ i → i ≤ p → P.famA i true ∈ F ∧ P.famA i false ∈ F := fun i h1 h2 =>
    ⟨(hF.1 i true h1 (by omega)).1, (hF.1 i false h1 (by omega)).1⟩
  have hFB : ∀ i, 1 ≤ i → i ≤ k → P.famB i true ∈ F ∧ P.famB i false ∈ F := fun i h1 h2 =>
    ⟨(hF.1 i true h1 (by omega)).2.1, (hF.1 i false h1 (by omega)).2.1⟩
  have hk1' : 1 ≤ k := le_trans Nat.one_le_two_pow hk1
  obtain ⟨N, hN, hN0, hNc, herr⟩ := P.landing F sA sB hj1 hjd hp1 hpK hk1' hkK hFA hFB hF.2.2
    hF.2.1 (by rw [hak, ← hsB]; linarith) (by rw [hak, ← hsB]; linarith)
  rw [hak, ← hsB] at herr
  refine ⟨k, N, ⟨hk1, hk2', hN, hN0, hNc⟩, ?_, ?_⟩
  · have := (abs_lt.mp herr).1; linarith
  · have := (abs_lt.mp herr).2; linarith

/-- **Landing levels in a window.** If `A ≥ 0`, `A + (w-1)/h ≤ 1` and the window is wide
enough, some landing level lies strictly between `A` and `A + w/h`. -/
theorem levels_window (F : Finset (ActualFamily P.heads P.T)) {ℓ j : ℕ} (hF : P.Needs F ℓ)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hj1 : 1 ≤ j) (hjd : j < P.d) {A : ℚ} {h w : ℕ} (hh : 0 < h)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1 - ((w : ℚ) - 1) / h)
    (hw : (h : ℚ) * (1152 / ((2 : ℚ) ^ ℓ) ^ 2 + 4 / (P.a (2 ^ ℓ) : ℚ)) ≤ (w : ℚ) - 1)
    (hsmall : 4 / (P.a (2 ^ ℓ) : ℚ) + 1152 / ((2 : ℚ) ^ ℓ) ^ 2 ≤ 1) :
    ∃ q N, P.Land F (P.root j) ℓ q N ∧ A < ((2 * N + 1 : ℕ) : ℚ) / P.cc q ∧
      ((2 * N + 1 : ℕ) : ℚ) / P.cc q < A + (w : ℚ) / h := by
  have hα : (0 : ℚ) < P.a (2 ^ ℓ) := by exact_mod_cast P.a_pos _
  have hhq : (0 : ℚ) < h := by exact_mod_cast hh
  set c := 1152 / ((2 : ℚ) ^ ℓ) ^ 2 with hc
  set e := 1 / (P.a (2 ^ ℓ) : ℚ) with he
  have hc0 : 0 ≤ c := by positivity
  have he0 : 0 < e := by positivity
  have h4 : 4 / (P.a (2 ^ ℓ) : ℚ) = 4 * e := by rw [he]; ring
  have h2 : 2 / (P.a (2 ^ ℓ) : ℚ) = 2 * e := by rw [he]; ring
  rw [h4] at hw hsmall
  have hc1 : c + 4 * e ≤ ((w : ℚ) - 1) / h := by rw [le_div_iff₀ hhq]; linarith
  have hc2 : ((w : ℚ) - 1) / h + 1 / h = (w : ℚ) / h := by rw [← add_div, sub_add_cancel]
  have hh1 : (0 : ℚ) < 1 / h := by positivity
  obtain ⟨q, N, hL, hy0, hy1⟩ := P.levels_dense F hF hℓ6 hℓν hj1 hjd
    (x₀ := max (A + e) (2 * e)) (x₁ := min (A + (w : ℚ) / h - e) (1 - 2 * e))
    (by rw [h2]; exact le_max_right _ _) (by rw [h2]; exact min_le_right _ _)
    (by
      rw [← hc]
      rcases le_total (A + e) (2 * e) with h₁ | h₁ <;>
      rcases le_total (A + (w : ℚ) / h - e) (1 - 2 * e) with h₂ | h₂ <;>
      simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h₁, h₂] <;> linarith)
  refine ⟨q, N, hL, ?_, ?_⟩
  · have := le_max_left (A + e) (2 * e)
    rw [← he] at hy0; linarith
  · have := min_le_left (A + (w : ℚ) / h - e) (1 - 2 * e)
    rw [← he] at hy1; linarith

end SourceCovers.Z3D.Index

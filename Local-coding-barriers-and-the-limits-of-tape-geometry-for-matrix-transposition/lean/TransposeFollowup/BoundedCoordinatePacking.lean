import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Explicit coordinate bins and a finite four-coordinate packing estimate. -/
namespace TransposeFollowup.BoundedCoordinatePacking
open Classical
set_option autoImplicit false

noncomputable def binCount (N δ : ℝ) : ℕ := ⌊2 * N / δ⌋₊ + 1

theorem binCount_pos (N δ : ℝ) : 0 < binCount N δ := Nat.succ_pos _

noncomputable def bin (N δ x : ℝ) : ℕ := ⌊(x + N) / δ⌋₊

theorem bin_lt {N δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ N) :
    bin N δ x < binCount N δ := by
  apply Nat.lt_succ_of_le
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hδ.le
  linarith [(abs_le.mp hx).2]

theorem same_bin_close {N δ x y : ℝ} (hδ : 0 < δ)
    (hx : |x| ≤ N) (hy : |y| ≤ N) (h : bin N δ x = bin N δ y) :
    |x - y| < δ := by
  have hx0 : 0 ≤ (x + N) / δ := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hy0 : 0 ≤ (y + N) / δ := div_nonneg (by linarith [(abs_le.mp hy).1]) hδ.le
  have hxl := Nat.floor_le hx0
  have hyl := Nat.floor_le hy0
  have hxu := Nat.lt_floor_add_one ((x + N) / δ)
  have hyu := Nat.lt_floor_add_one ((y + N) / δ)
  change ⌊(x + N) / δ⌋₊ = ⌊(y + N) / δ⌋₊ at h
  rw [h] at hxl hxu
  have hxy : (x + N) / δ - (y + N) / δ < 1 := by linarith
  have hyx : (y + N) / δ - (x + N) / δ < 1 := by linarith
  rw [← sub_div] at hxy hyx
  have hxy' := (div_lt_iff₀ hδ).mp hxy
  have hyx' := (div_lt_iff₀ hδ).mp hyx
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem binCount_le {N δ : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) :
    (binCount N δ : ℝ) ≤ 2 * N / δ + 1 := by
  simp only [binCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le (show 0 ≤ 2 * N / δ by positivity)]

theorem binCount_near_identity_le {N η : ℝ} (hN : 1 ≤ N)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    (binCount N (η / (8 * N)) : ℝ) ≤ 17 * N ^ 2 / η := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have h := binCount_le hN0.le (show 0 < η / (8 * N) by positivity)
  have he : 2 * N / (η / (8 * N)) = 16 * N ^ 2 / η := by field_simp; ring
  rw [he] at h
  have hsq : η ≤ N ^ 2 := by nlinarith
  have hone : 1 ≤ N ^ 2 / η := (le_div_iff₀ hη).mpr (by simpa using hsq)
  calc
    _ ≤ 16 * N ^ 2 / η + 1 := h
    _ ≤ 16 * N ^ 2 / η + N ^ 2 / η := by linarith
    _ = _ := by ring

theorem exists_cluster {α : Type*} [Fintype α]
    (a : α → Fin 2 → Fin 2 → ℝ) {N δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ x i j, |a x i j| ≤ N) {m : ℕ}
    (hcard : binCount N δ ^ 4 * m ≤ Fintype.card α) :
    ∃ S : Finset α, m ≤ S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |a x i j - a y i j| < δ := by
  let K := binCount N δ
  let : NeZero K := ⟨ne_of_gt (binCount_pos N δ)⟩
  let f : α → (Fin 2 → Fin 2 → Fin K) :=
    fun x i j => ⟨bin N δ (a x i j), bin_lt hδ (ha x i j)⟩
  have hc : Fintype.card (Fin 2 → Fin 2 → Fin K) = K ^ 4 := by
    simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  obtain ⟨z, hz⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f (by simpa only [hc] using hcard)
  refine ⟨Finset.univ.filter (fun x => f x = z), hz, ?_⟩
  intro x hx y hy i j
  have hxz := (Finset.mem_filter.mp hx).2
  have hyz := (Finset.mem_filter.mp hy).2
  apply same_bin_close hδ (ha x i j) (ha y i j)
  exact congrArg (fun v => (v i j).val) (hxz.trans hyz.symm)

end TransposeFollowup.BoundedCoordinatePacking

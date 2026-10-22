import Mathlib.Combinatorics.HalesJewett
import TransposeFollowup.SL2SpanCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A fixed finite coloring bound, imported from Hales--Jewett, lets a
second-order trace recurrence avoid four bad values simultaneously. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false

theorem exists_bounded_four_color_progression :
    ∃ N : ℕ, 0 < N ∧ ∀ C : ℕ → Fin 4,
      ∃ a d : ℕ, 0 < d ∧ a + 2 * d ≤ N ∧
        C a = C (a + d) ∧ C (a + d) = C (a + 2 * d) := by
  classical
  obtain ⟨ι, inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin 3) (Fin 4)
  let := inst
  refine ⟨2 * Fintype.card ι + 1, by omega, ?_⟩
  intro C
  obtain ⟨l, c, hc⟩ := hι (fun v => C (∑ i, (v i).val))
  let s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  let a := ∑ i, (l 0 i).val
  let d := s.card
  have hd : 0 < d := Finset.card_pos.mpr
    ⟨l.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  have hsum (k : Fin 3) : (∑ i, (l k i).val) = a + d * k.val := by
    have he (i : ι) : (l k i).val = (l 0 i).val + (if l.idxFun i = none then 1 else 0) * k.val := by
      cases h : l.idxFun i <;> simp [h]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_boole]
    rfl
  have hbound : a + 2 * d ≤ 2 * Fintype.card ι + 1 := by
    have hh : (∑ i, (l 2 i).val) ≤ ∑ _i : ι, 2 :=
      Finset.sum_le_sum (fun i _ => by omega)
    rw [hsum] at hh
    simp only [Fin.val_two, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
    omega
  have h0 := hc (0 : Fin 3)
  have h1 := hc (1 : Fin 3)
  have h2 := hc (2 : Fin 3)
  change C (∑ i, (l 0 i).val) = c at h0
  change C (∑ i, (l 1 i).val) = c at h1
  change C (∑ i, (l 2 i).val) = c at h2
  rw [hsum] at h0 h1 h2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, add_zero, mul_one] at h0 h1 h2
  exact ⟨a, d, hd, hbound, h0.trans h1.symm, by simpa only [mul_comm d 2] using h1.trans h2.symm⟩

theorem exists_simultaneous_recurrence_escape :
    ∃ N : ℕ, 0 < N ∧ ∀ (f : Fin 4 → ℕ → ℝ) (t : ℕ → ℝ) (Δ : ℝ),
      0 < Δ →
      (∀ d, 0 < d → d ≤ N → Δ ≤ |t d - 2| ∧ |t d| ≤ 3) →
      (∀ i a d, 0 < d → a + 2 * d ≤ N →
        f i (a + 2 * d) + f i a = t d * f i (a + d)) →
      ∃ m ≤ N, ∀ i, Δ / 4 < |f i m - 2| := by
  obtain ⟨N, hN, hprogression⟩ := exists_bounded_four_color_progression
  refine ⟨N, hN, ?_⟩
  intro f t Δ hΔ ht hrec
  by_contra! hbad
  classical
  let C : ℕ → Fin 4 := fun m => if h : m ≤ N then (hbad m h).choose else 0
  have hC (m : ℕ) (hm : m ≤ N) : |f (C m) m - 2| ≤ Δ / 4 := by
    simpa only [C, dite_eq_left hm] using (hbad m hm).choose_spec
  obtain ⟨a, d, hd, hbound, h01, h12⟩ := hprogression C
  have h0 := hC a (by omega)
  have h1 := hC (a + d) (by omega)
  have h2 := hC (a + 2 * d) hbound
  rw [← h01] at h1
  rw [← h12, ← h01] at h2
  obtain ⟨hgap, htd⟩ := ht d hd (by omega)
  have heq : 2 * (t d - 2) =
      (f (C a) (a + 2 * d) - 2) + (f (C a) a - 2) - t d * (f (C a) (a + d) - 2) := by
    have hh := hrec (C a) a d hd hbound
    nlinarith only [hh]
  have hupper : |2 * (t d - 2)| ≤ 5 * (Δ / 4) := by
    rw [heq]
    calc
      _ ≤ |f (C a) (a + 2 * d) - 2| + |f (C a) a - 2| +
          |t d * (f (C a) (a + d) - 2)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Δ / 4 + Δ / 4 + 3 * (Δ / 4) := by
        rw [abs_mul]
        exact add_le_add (add_le_add h2 h0) (mul_le_mul htd h1 (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at hupper
  linarith only [hgap, hupper, hΔ]

end TransposeFollowup.SL2Projection

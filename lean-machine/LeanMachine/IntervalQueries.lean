import LeanMachine.QueryMovement

/-! Repeated query types served during intervals. Discard expensive intervals,
charge lost types by their repetitions, and reuse the movement-clock count.
Only disjoint internal edge sets are needed; endpoints may coincide. -/

namespace LeanMachine.QueryMovement

open Finset
open scoped BigOperators
noncomputable section

/-- Deleting occurrences loses at most one type per `r` deleted occurrences. -/
theorem card_image_le_retained {τ α : Type*} [DecidableEq τ] [DecidableEq α]
    (T G : Finset τ) (f : τ → α) (hG : G ⊆ T) {r : ℝ} (hr : 0 < r)
    (hrepeat : ∀ A ∈ T.image f, r ≤ ((T.filter fun t => f t = A).card : ℝ)) :
    ((T.image f).card : ℝ) ≤ (G.image f).card + (T \ G).card / r := by
  classical
  let L := T.image f \ G.image f
  have hsub : T.filter (fun t => f t ∈ L) ⊆ T \ G := by
    intro t ht
    obtain ⟨htT, htL⟩ := mem_filter.mp ht
    exact mem_sdiff.mpr ⟨htT, fun htG =>
      (mem_sdiff.mp htL).2 (mem_image_of_mem f htG)⟩
  have hlost : (L.card : ℝ) * r ≤ (T \ G).card := by
    calc
      _ = ∑ _A ∈ L, r := by simp
      _ ≤ ∑ A ∈ L, ((T.filter fun t => f t = A).card : ℝ) :=
        sum_le_sum fun A hA => hrepeat A (mem_sdiff.mp hA).1
      _ = ((T.filter fun t => f t ∈ L).card : ℝ) := by
        exact_mod_cast sum_card_fiberwise_eq_card_filter T L f
      _ ≤ ((T \ G).card : ℝ) := by exact_mod_cast card_le_card hsub
  have he : L.card + (G.image f).card = (T.image f).card :=
    card_sdiff_add_card_eq_card (image_subset_image hG)
  have he' : (L.card : ℝ) + (G.image f).card = (T.image f).card := by exact_mod_cast he
  have hl := (le_div_iff₀ hr).mpr hlost
  linarith

/-- Disjoint time intervals in particular have disjoint internal edges. -/
theorem edges_disjoint_of_intervals {τ : Type*} (T : Finset τ) (a b : τ → ℕ)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Icc (a j) (b j)) :
    (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j) := by
  intro i hi j hj hij
  apply (hdisj hi hj hij).mono
  · exact fun e he => mem_Icc.mpr ⟨(mem_Ico.mp he).1, (mem_Ico.mp he).2.le⟩
  · exact fun e he => mem_Icc.mpr ⟨(mem_Ico.mp he).1, (mem_Ico.mp he).2.le⟩

/-- The internal edge bills of edge-disjoint intervals fit in the full
timeline budget, which also includes every gap between intervals. -/
theorem sum_interval_charge_le {τ : Type*} [DecidableEq τ]
    (T : Finset τ) (a b : τ → ℕ) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ e < n, 0 ≤ w e)
    (hab : ∀ j ∈ T, a j ≤ b j) (hbn : ∀ j ∈ T, b j ≤ n)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j)) :
    (∑ j ∈ T, (elapsed w (b j) - elapsed w (a j))) ≤ elapsed w n := by
  calc
    _ = ∑ j ∈ T, ∑ e ∈ Ico (a j) (b j), w e :=
      sum_congr rfl fun j hj => (sum_Ico_eq_sub w (hab j hj)).symm
    _ = ∑ e ∈ T.biUnion (fun j => Ico (a j) (b j)), w e := (sum_biUnion hdisj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by
        intro e he
        obtain ⟨j, hj, he⟩ := mem_biUnion.mp he
        exact mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp he).2 (hbn j hj)))
      (fun e he _ => hw e (mem_range.mp he))

/-- Frozen starts of inexpensive intervals cover each query within its raw
radius, recovery radius, and internal movement budget. -/
theorem frozen_interval_cover {X α ι τ : Type*} [PseudoMetricSpace X]
    {T : Finset τ} {S : τ → Finset α} {c : α → X} {Y : ι → ℕ → X}
    {a b : τ → ℕ} {charge : ℕ → ℝ} {n : ℕ} {ρ w δ : ℝ}
    (hw : ∀ e < n, 0 ≤ charge e)
    (hstep : ∀ i, ∀ e < n, dist (Y i e) (Y i (e + 1)) ≤ charge e)
    (hbn : ∀ j ∈ T, b j ≤ n)
    (hraw : ∀ j ∈ T, ∀ x ∈ S j, ∃ t ∈ Icc (a j) (b j), ∃ i, ∃ z,
      dist z (c x) ≤ w ∧ dist z (Y i t) ≤ ρ)
    {j : τ} (hj : j ∈ T) (hgood : elapsed charge (b j) - elapsed charge (a j) ≤ δ) :
    ∀ x ∈ S j, ∃ i, dist (c x) (Y i (a j)) ≤ ρ + w + δ := by
  intro x hx
  obtain ⟨t, ht, i, z, hzc, hzy⟩ := hraw j hj x hx
  obtain ⟨hat, htb⟩ := mem_Icc.mp ht
  have ht' := htb.trans (hbn j hj)
  have hd := dist_le_elapsed_sub (hstep i) hat ht'
  have hm := elapsed_mono hw htb (hbn j hj)
  have htri := dist_triangle (c x) z (Y i (a j))
  have htri' := dist_triangle z (Y i t) (Y i (a j))
  rw [dist_comm (c x) z] at htri
  rw [dist_comm (Y i t) (Y i (a j))] at htri'
  exact ⟨i, by linarith⟩

/-- General interval-query bound. `δ` is the allowed internal movement;
`η` is the independent width used to group the frozen starts. -/
theorem card_interval_types_le {X α ι τ : Type*} [PseudoMetricSpace X]
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq τ]
    (T : Finset τ) (S : τ → Finset α) (c : α → X) (Y : ι → ℕ → X)
    (a b : τ → ℕ) (charge : ℕ → ℝ) (n k s : ℕ)
    (ρ w δ η r : ℝ) (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (hw : ∀ e < n, 0 ≤ charge e)
    (hstep : ∀ i, ∀ e < n, dist (Y i e) (Y i (e + 1)) ≤ charge e)
    (hab : ∀ j ∈ T, a j ≤ b j) (hbn : ∀ j ∈ T, b j ≤ n)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j))
    (hsize : ∀ j ∈ T, (S j).card = k)
    (hrepeat : ∀ A ∈ T.image S, r ≤ ((T.filter fun j => S j = A).card : ℝ))
    (hraw : ∀ j ∈ T, ∀ x ∈ S j, ∃ t ∈ Icc (a j) (b j), ∃ i, ∃ z,
      dist z (c x) ≤ w ∧ dist z (Y i t) ≤ ρ)
    (hcapacity : ∀ y : ι → X, (covered c y (ρ + w + δ + η)).card ≤ s) :
    ((T.image S).card : ℝ) ≤
      ((⌊elapsed charge n / η⌋₊ : ℝ) + 1) * s.choose k + elapsed charge n / (δ * r) := by
  classical
  let E := elapsed charge n
  let bill (j : τ) := elapsed charge (b j) - elapsed charge (a j)
  let G := T.filter fun j => bill j ≤ δ
  have hGT : G ⊆ T := filter_subset _ _
  have hbill {j : τ} (hj : j ∈ T) : 0 ≤ bill j :=
    sub_nonneg.mpr (elapsed_mono hw (hab j hj) (hbn j hj))
  have hbad : ((T \ G).card : ℝ) * δ ≤ E := by
    calc
      _ = ∑ _j ∈ T \ G, δ := by simp
      _ ≤ ∑ j ∈ T \ G, bill j := by
        apply sum_le_sum
        intro j hj
        obtain ⟨hjT, hjG⟩ := mem_sdiff.mp hj
        have : ¬bill j ≤ δ := fun h => hjG (mem_filter.mpr ⟨hjT, h⟩)
        exact le_of_lt (lt_of_not_ge this)
      _ ≤ ∑ j ∈ T, bill j := sum_le_sum_of_subset_of_nonneg sdiff_subset
        (fun j hj _ => hbill hj)
      _ ≤ E := sum_interval_charge_le T a b charge n hw hab hbn hdisj
  have hcount : (G.image S).card ≤ (⌊E / η⌋₊ + 1) * s.choose k := by
    apply card_types_le G S c (fun i j => Y i (a j))
      (fun j => elapsed charge (a j)) E (ρ + w + δ) η k s hη
    · intro j hj
      have ht := (hab j (hGT hj)).trans (hbn j (hGT hj))
      exact ⟨elapsed_nonneg hw ht, elapsed_mono hw ht le_rfl⟩
    · intro i j hj l hl
      exact dist_le_elapsed_abs (hstep i)
        ((hab j (hGT hj)).trans (hbn j (hGT hj)))
        ((hab l (hGT hl)).trans (hbn l (hGT hl)))
    · exact fun j hj => hsize j (hGT hj)
    · intro j hj
      exact frozen_interval_cover hw hstep hbn hraw (hGT hj) (mem_filter.mp hj).2
    · exact hcapacity
  have hcountR : ((G.image S).card : ℝ) ≤ ((⌊E / η⌋₊ : ℝ) + 1) * s.choose k :=
    by exact_mod_cast hcount
  have hlost := card_image_le_retained T G S hGT hr hrepeat
  have hbad' := div_le_div_of_nonneg_right ((le_div_iff₀ hδ).mpr hbad) hr.le
  rw [div_div] at hbad'
  linarith

/-- Smooth and invert the interval-query inequality with independent
internal (`δ`) and grouping (`η`) widths. No positive capacity is needed. -/
theorem interval_real_bounds_general {F B : ℕ} {E δ η r : ℝ}
    (hE : 0 ≤ E) (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (h : (F : ℝ) ≤ ((⌊E / η⌋₊ : ℝ) + 1) * B + E / (δ * r)) :
    (F : ℝ) - E / (δ * r) ≤ (1 + E / η) * B ∧
      η * (((F : ℝ) - B) / (B + η / (δ * r))) ≤ E := by
  have hfloor := Nat.floor_le (div_nonneg hE hη.le)
  have hs : (F : ℝ) - E / (δ * r) ≤ (1 + E / η) * B := by nlinarith
  refine ⟨hs, ?_⟩
  have hden : 0 < (B : ℝ) + η / (δ * r) := by positivity
  have heq : (1 + E / η) * (B : ℝ) + E / (δ * r) =
          B + (E / η) * (B + η / (δ * r)) := by field_simp; ring
  have hf : (F : ℝ) - B ≤ (E / η) * (B + η / (δ * r)) := by linarith
  have hd := (div_le_iff₀ hden).mpr hf
  have hm := mul_le_mul_of_nonneg_left hd hη.le
  simpa only [mul_div_cancel₀ _ hη.ne'] using hm

/-- The original equal-width bound is a specialization of the general one. -/
theorem interval_real_bounds {F B : ℕ} {E δ r : ℝ}
    (hE : 0 ≤ E) (hδ : 0 < δ) (hr : 0 < r)
    (h : (F : ℝ) ≤ ((⌊E / δ⌋₊ : ℝ) + 1) * B + E / (δ * r)) :
    (F : ℝ) - E / (δ * r) ≤ (1 + E / δ) * B ∧
      δ * (((F : ℝ) - B) / (B + 1 / r)) ≤ E := by
  have he : δ / (δ * r) = 1 / r := by field_simp
  simpa only [he] using interval_real_bounds_general hE hδ hδ hr h

end
end LeanMachine.QueryMovement

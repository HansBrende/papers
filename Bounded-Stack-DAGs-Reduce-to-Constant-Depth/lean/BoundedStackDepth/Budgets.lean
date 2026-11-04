import BoundedStackDepth.ViewInvariance
import BoundedStackDepth.FrameWeight
import BoundedStackDepth.Events
import BoundedStackDepth.Wrap

/-!
# Budgets of the standard events

The standard events of a frame system at offset `r` are its rises (`RiseAt t g`: the innermost running
maximum crosses the floor of group `g`) and its last-stint ends (`LastStintAt t g`). Each is attached to a
segment: the segment of `t` for a rise, that of `t − 1` for a last-stint end.

* `rise_unique`, `lastStint_unique`: a segment rises into a given group once, and ends its last stint
  once;
* their floors lie within the segment's scale (`flr_le_of_rise`, `flr_le_of_lastStint`);
* `sum_stdWeight_le`: summed over the `h₀` offsets, the events weighted by `2^{θ}` total at most
  `8 Σ_σ 2^{scale σ}` (the floors below a scale sum geometrically, and `sum_two_pow_flr_grp_le` averages
  the top one).
-/

namespace BoundedStackDepth

namespace FrameSystem

open Finset

variable {S : FrameSystem} {h₀ r : ℕ}

/-- Without a change of segment start, the running maximum does not decrease. -/
theorem runMax_mono_of_segStart_eq {F : ℕ × ℕ} {t t' : ℕ} (hFt : F.1 ≤ t) (htt : t ≤ t')
    (hs : S.segStart F t' = S.segStart F t) : S.runMax F t ≤ S.runMax F t' := by
  induction t', htt using Nat.le_induction with
  | base => exact le_rfl
  | succ t' htt ih =>
    have h1 := segStart_mono (S := S) (F := F) htt
    have h2 := segStart_mono (S := S) (F := F) (show t' ≤ t' + 1 by omega)
    have hs' : S.segStart F t' = S.segStart F t := by omega
    have hnr : ¬ S.Restart F (t' + 1) := fun h => by
      have := segStart_of_restart h
      have := segStart_le (S := S) hFt
      omega
    have := runMax_le_succ (S := S) (show F.1 < t' + 1 by omega) hnr
    simp only [Nat.add_sub_cancel] at this
    exact (ih hs').trans this

/-- A segment rises into a given group at most once. -/
theorem rise_unique {t t' g : ℕ} (h : S.RiseAt h₀ r t g) (h' : S.RiseAt h₀ r t' g)
    (hσ : S.segOf t = S.segOf t') : t = t' := by
  wlog hlt : t < t' generalizing t t'
  · rcases (not_lt.mp hlt).lt_or_eq with h1 | h1
    · exact (this h' h hσ.symm h1).symm
    · exact h1.symm
  exfalso
  have hK : S.inner t = S.inner t' := congrArg Prod.fst hσ
  have hs : S.segStart (S.inner t) t = S.segStart (S.inner t') t' := congrArg Prod.snd hσ
  have hmono := runMax_mono_of_segStart_eq (S := S) (F := S.inner t) (t := t) (t' := t' - 1)
    (by have := h.2.2.1; omega) (by omega) (by
      have a1 := segStart_mono (S := S) (F := S.inner t) (show t ≤ t' - 1 by omega)
      have a2 := segStart_mono (S := S) (F := S.inner t) (show t' - 1 ≤ t' by omega)
      rw [hK] at a1 a2 ⊢
      rw [hK] at hs
      omega)
  have := h.2.2.2.2.2
  have := h'.2.2.2.2.1
  rw [← hK] at this
  have := band_mono hmono
  omega

/-- A segment's last stint ends at most once. -/
theorem lastStint_unique {t t' g g' : ℕ} (htT : t < S.T) (htT' : t' < S.T)
    (h : S.LastStintAt h₀ r t g) (h' : S.LastStintAt h₀ r t' g')
    (hσ : S.segOf (t - 1) = S.segOf (t' - 1)) : t = t' := by
  have hK : S.inner (t - 1) = S.inner (t' - 1) := congrArg Prod.fst hσ
  have hs : S.segStart (S.inner (t - 1)) (t - 1) = S.segStart (S.inner (t' - 1)) (t' - 1) :=
    congrArg Prod.snd hσ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine h.2.2 (t' - 1) (by omega) ?_ ?_
    · rw [hK]; exact own_inner (by omega)
    · rw [hK] at hs ⊢; exact hs.symm
  · refine h'.2.2 (t - 1) (by omega) ?_ ?_
    · rw [← hK]; exact own_inner (by omega)
    · rw [← hK] at hs ⊢; exact hs

/-- The scale of a segment is the band of its maximum. -/
theorem segScale_eq (F : ℕ × ℕ) (s : ℕ) : segScale S F s = band (S.segMax (F, s)) := by
  classical
  unfold segScale segMax segTimes
  congr 1
  refine sup_congr (filter_congr fun t ht => ?_) fun _ _ => rfl
  unfold segOf
  have ht' := mem_range.mp ht
  constructor
  · rintro ⟨hown, hs⟩
    rw [inner_eq hown, hs]
  · intro he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only at h1 h2
    rw [← h1]
    exact ⟨own_inner ht', h2⟩

/-- The floor of a rise lies within the scale of its segment. -/
theorem flr_le_of_rise {t g : ℕ} (htT : t < S.T) (h : S.RiseAt h₀ r t g) :
    flr h₀ r g ≤ band (S.segMax (S.segOf t)) := by
  rw [← segScale_eq]
  exact h.2.2.2.2.2.trans (beta_le_segScale htT)

/-- The floor of a last-stint end lies within the scale of its segment. -/
theorem flr_le_of_lastStint {t g : ℕ} (htT : t < S.T) (h : S.LastStintAt h₀ r t g) :
    flr h₀ r g ≤ band (S.segMax (S.segOf (t - 1))) := by
  rw [← segScale_eq]
  exact h.2.1.trans (beta_le_segScale (by omega))

/-- The floors `θ(g)`, `1 ≤ g`, below a scale `s` sum geometrically: at most `2 · 2^{θ(G(s))}`, and nothing
when `G(s) = 0`. -/
theorem sum_two_pow_flr_le (hr : r < h₀) (s N : ℕ) :
    ∑ g ∈ (range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ s), 2 ^ flr h₀ r g ≤
      if 1 ≤ grp h₀ r s then 2 * 2 ^ flr h₀ r (grp h₀ r s) else 0 := by
  have hh : 0 < h₀ := by omega
  have hsub : ∀ g ∈ (range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ s), 1 ≤ g ∧ g ≤ grp h₀ r s :=
    fun g hg => ⟨(mem_filter.mp hg).2.1, (flr_le_iff hh r g s).mp (mem_filter.mp hg).2.2⟩
  split_ifs with hG
  · have hinj : Set.InjOn (flr h₀ r) ((range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ s) : Set ℕ) := by
      intro a ha b hb h
      have ha1 := (hsub a ha).1
      have hb1 := (hsub b hb).1
      unfold flr at h
      have h1 : r ≤ h₀ * a := by nlinarith
      have h2 : r ≤ h₀ * b := by nlinarith
      exact Nat.eq_of_mul_eq_mul_left hh (by omega)
    calc ∑ g ∈ (range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ s), 2 ^ flr h₀ r g
        = ∑ i ∈ ((range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ s)).image (flr h₀ r), 2 ^ i :=
          (sum_image (f := fun i => 2 ^ i) hinj).symm
      _ ≤ ∑ i ∈ range (flr h₀ r (grp h₀ r s) + 1), 2 ^ i := by
          refine sum_le_sum_of_subset fun i hi => ?_
          obtain ⟨g, hg, rfl⟩ := mem_image.mp hi
          have := (hsub g hg).2
          refine mem_range.mpr (Nat.lt_succ_of_le ?_)
          unfold flr
          have : h₀ * g ≤ h₀ * grp h₀ r s := Nat.mul_le_mul_left _ this
          omega
      _ ≤ 2 * 2 ^ flr h₀ r (grp h₀ r s) := by
          have := sum_range_two_pow_lt (flr h₀ r (grp h₀ r s) + 1)
          rw [pow_succ] at this
          omega
  · rw [Finset.sum_eq_zero fun g hg => absurd (hsub g hg) (by omega)]

/-- **Averaging the top floor.** Over the `h₀` offsets, `2 · 2^{θ(G(s))}` (when `G(s) ≥ 1`) sums to at
most `4 · 2^s`. -/
theorem sum_offsets_top_floor_le (s : ℕ) :
    ∑ r ∈ range h₀, (if 1 ≤ grp h₀ r s then 2 * 2 ^ flr h₀ r (grp h₀ r s) else 0) ≤ 4 * 2 ^ s := by
  rw [← sum_filter]
  have hfilt : (range h₀).filter (fun r => 1 ≤ grp h₀ r s) =
      (range h₀).filter (fun r => 1 ≤ flr h₀ r (grp h₀ r s)) := by
    refine filter_congr fun r hr => ?_
    have hr' := mem_range.mp hr
    unfold flr
    constructor
    · intro h; have : h₀ ≤ h₀ * grp h₀ r s := Nat.le_mul_of_pos_right _ h; omega
    · intro h; by_contra h0; push Not at h0
      rw [show grp h₀ r s = 0 by omega] at h; simp at h
  rw [hfilt, ← mul_sum]
  have := sum_two_pow_flr_grp_le (h₀ := h₀) s
  rw [pow_succ] at this
  omega

variable (S h₀ r)

open Classical in
/-- The rises at offset `r`, as pairs (time, group) with group below `N`. -/
noncomputable def rises (N : ℕ) : Finset (ℕ × ℕ) :=
  (range S.T ×ˢ range N).filter fun tg => S.RiseAt h₀ r tg.1 tg.2

open Classical in
/-- The last-stint ends at offset `r`, as pairs (time, group) with group below `N`. -/
noncomputable def lastStints (N : ℕ) : Finset (ℕ × ℕ) :=
  (range S.T ×ˢ range N).filter fun tg => 1 ≤ tg.1 ∧ S.LastStintAt h₀ r tg.1 tg.2

variable {S h₀ r}

/-- A sum over a filtered product, as an iterated sum. -/
theorem sum_filter_product {α : Type*} (A : Finset α) (C : Finset ℕ) (P : α → ℕ → Prop)
    [∀ a c, Decidable (P a c)] (f : ℕ → ℕ) :
    ∑ y ∈ (A ×ˢ C).filter (fun y => P y.1 y.2), f y.2 = ∑ a ∈ A, ∑ c ∈ C.filter (P a), f c := by
  rw [sum_filter, sum_product]
  exact sum_congr rfl fun a _ => (sum_filter _ _).symm

open Classical in
/-- The rises inject into (segment, group) pairs with the floor within the segment's scale. -/
theorem sum_rises_le (N : ℕ) :
    ∑ tg ∈ S.rises h₀ r N, 2 ^ flr h₀ r tg.2 ≤
      ∑ σ ∈ S.segments, ∑ g ∈ (range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ band (S.segMax σ)),
        2 ^ flr h₀ r g := by
  have hinj : Set.InjOn (fun tg : ℕ × ℕ => (S.segOf tg.1, tg.2)) (S.rises h₀ r N : Set (ℕ × ℕ)) := by
    intro x hx y hy h
    have hx' := (mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hy' := (mem_filter.mp (Finset.mem_coe.mp hy)).2
    simp only [Prod.mk.injEq] at h
    rw [h.2] at hx'
    exact Prod.ext (rise_unique hx' hy' h.1) h.2
  rw [← sum_filter_product]
  calc ∑ tg ∈ S.rises h₀ r N, 2 ^ flr h₀ r tg.2
      = ∑ y ∈ (S.rises h₀ r N).image (fun tg : ℕ × ℕ => (S.segOf tg.1, tg.2)), 2 ^ flr h₀ r y.2 :=
        (sum_image (f := fun y : ((ℕ × ℕ) × ℕ) × ℕ => 2 ^ flr h₀ r y.2) hinj).symm
    _ ≤ _ := by
        refine sum_le_sum_of_subset fun y hy => ?_
        obtain ⟨tg, htg, rfl⟩ := mem_image.mp hy
        obtain ⟨hmem, hrise⟩ := mem_filter.mp htg
        obtain ⟨ht, hg⟩ := mem_product.mp hmem
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ ht, hg⟩, hrise.1,
          flr_le_of_rise (mem_range.mp ht) hrise⟩

open Classical in
/-- The last-stint ends inject into (segment, group) pairs with the floor within the segment's
scale. -/
theorem sum_lastStints_le (N : ℕ) :
    ∑ tg ∈ S.lastStints h₀ r N, 2 ^ flr h₀ r tg.2 ≤
      ∑ σ ∈ S.segments, ∑ g ∈ (range N).filter (fun g => 1 ≤ g ∧ flr h₀ r g ≤ band (S.segMax σ)),
        2 ^ flr h₀ r g := by
  have hinj : Set.InjOn (fun tg : ℕ × ℕ => (S.segOf (tg.1 - 1), tg.2))
      (S.lastStints h₀ r N : Set (ℕ × ℕ)) := by
    intro x hx y hy h
    obtain ⟨hxm, -, hx'⟩ := mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hym, -, hy'⟩ := mem_filter.mp (Finset.mem_coe.mp hy)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (lastStint_unique (mem_range.mp (mem_product.mp hxm).1)
      (mem_range.mp (mem_product.mp hym).1) hx' hy' h.1) h.2
  rw [← sum_filter_product]
  calc ∑ tg ∈ S.lastStints h₀ r N, 2 ^ flr h₀ r tg.2
      = ∑ y ∈ (S.lastStints h₀ r N).image (fun tg : ℕ × ℕ => (S.segOf (tg.1 - 1), tg.2)),
          2 ^ flr h₀ r y.2 :=
        (sum_image (f := fun y : ((ℕ × ℕ) × ℕ) × ℕ => 2 ^ flr h₀ r y.2) hinj).symm
    _ ≤ _ := by
        refine sum_le_sum_of_subset fun y hy => ?_
        obtain ⟨tg, htg, rfl⟩ := mem_image.mp hy
        obtain ⟨hmem, h1, hls⟩ := mem_filter.mp htg
        obtain ⟨ht, hg⟩ := mem_product.mp hmem
        have ht' := mem_range.mp ht
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_range.mpr (by omega)), hg⟩,
          hls.1, flr_le_of_lastStint ht' hls⟩

/-- **The budget of the standard events.** Averaged over the offsets, the rises and last-stint ends
weighted by `2^{θ}` total at most `8 Σ_σ 2^{scale σ}`. -/
theorem sum_stdWeight_le (N : ℕ) :
    ∑ r ∈ range h₀, (∑ tg ∈ S.rises h₀ r N, 2 ^ flr h₀ r tg.2 +
      ∑ tg ∈ S.lastStints h₀ r N, 2 ^ flr h₀ r tg.2) ≤
      8 * ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ) := by
  calc ∑ r ∈ range h₀, (∑ tg ∈ S.rises h₀ r N, 2 ^ flr h₀ r tg.2 +
        ∑ tg ∈ S.lastStints h₀ r N, 2 ^ flr h₀ r tg.2)
      ≤ ∑ r ∈ range h₀, 2 * ∑ σ ∈ S.segments,
          (if 1 ≤ grp h₀ r (band (S.segMax σ)) then 2 * 2 ^ flr h₀ r (grp h₀ r (band (S.segMax σ)))
            else 0) := sum_le_sum fun r hr => by
        have hr' := mem_range.mp hr
        have hseg : ∑ σ ∈ S.segments, ∑ g ∈ (range N).filter
            (fun g => 1 ≤ g ∧ flr h₀ r g ≤ band (S.segMax σ)), 2 ^ flr h₀ r g ≤
            ∑ σ ∈ S.segments, (if 1 ≤ grp h₀ r (band (S.segMax σ)) then
              2 * 2 ^ flr h₀ r (grp h₀ r (band (S.segMax σ))) else 0) :=
          sum_le_sum fun σ _ => sum_two_pow_flr_le hr' _ N
        have := sum_rises_le (S := S) (h₀ := h₀) (r := r) N
        have := sum_lastStints_le (S := S) (h₀ := h₀) (r := r) N
        omega
    _ = 2 * ∑ σ ∈ S.segments, ∑ r ∈ range h₀,
          (if 1 ≤ grp h₀ r (band (S.segMax σ)) then 2 * 2 ^ flr h₀ r (grp h₀ r (band (S.segMax σ)))
            else 0) := by rw [← mul_sum, sum_comm]
    _ ≤ 2 * ∑ σ ∈ S.segments, 4 * 2 ^ band (S.segMax σ) :=
        Nat.mul_le_mul_left _ (sum_le_sum fun σ _ => sum_offsets_top_floor_le _)
    _ = 8 * ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ) := by rw [← mul_sum, ← mul_assoc]; norm_num

end FrameSystem

end BoundedStackDepth

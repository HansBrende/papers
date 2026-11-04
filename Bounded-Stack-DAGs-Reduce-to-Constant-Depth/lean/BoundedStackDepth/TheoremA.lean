import BoundedStackDepth.LadderBands
import BoundedStackDepth.HopData
import BoundedStackDepth.TopProminence
import BoundedStackDepth.PerExcursion

/-!
# Theorem A: the per-excursion bound and the summation

For a walk `x` (pauses allowed), the frame system `S = upperFrames x T hx` of class U, and a top `τ`
of height `H` with canonical excursion `[a, b]`, base `y` and `B = band H`:

* `cstar_exc_le` (the base hop): `c*(exc τ) ≤ B`. If the frame of the excursion starts at `a + 1`
  (the first excursion of a descent structure) or ends at `b` (the last excursion of a hanging
  structure), the σ cap applies: the parent top is an earlier point at least as high, or a
  later point strictly higher, reached without the walk dropping below `y`, so `prom τ ≤ H`
  (`prom_le_of_left`, `prom_le_of_right`). Otherwise `a` and `b` lie in the frame, both bands and
  the home band are at most `B`, and the hop is frame-micro only if `H = 1`, where `β(b) = 0`.
* `cstar_ladder_le`: the ladder hop at cell `y + d`, `1 ≤ d < H`, costs at most
  `(B − band (d − 1)) + (B − uband H d)`: the per-hop estimate with the bands of `LadderBands.lean`;
  eventfulness holds below the top passage because the segment of `D τ (y + d)` starts after `L τ (y + d)`,
  and above it because `β ≤ B ≤ σ` (`height_le_prom`).
* `sum_ladder_cstar_le`: the ladder of `τ` costs at most `6H` (`sum_range_le_six_of_ladder`).
* **Theorem A** (`thmA_upper`, `thmA_lower`): summed over the `h₀` grid offsets, at most `6` times
  the number of upper (lower) hops are lost. The lower class is class U of `−x` (`upperHops_neg`).
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {x : ℕ → ℤ} {T τ : ℕ}

/-- The top of a ladder hop. -/
theorem hopOwner_ladL (hx : IsWalk x) {z : ℤ} (hz1 : base x T τ ≤ z) (hz2 : z < x τ) :
    hopOwner x (ladL x T τ z) (ladD x T τ z) = τ :=
  (mem_filter.mp (ladL_mem hx hz1 hz2)).2

/-- The owner scale of a ladder hop of `τ` is `band (prom τ)`. -/
theorem ownerScale_ladderHop (hx : IsWalk x) {z : ℤ} (hz1 : base x T τ ≤ z) (hz2 : z < x τ) :
    ownerScale (upperFrames x T hx) (ladderHop x T τ z) = band (prom x T τ) := by
  show band (prom x T (hopOwner x (ladL x T τ z) (ladD x T τ z))) = _
  rw [hopOwner_ladL hx hz1 hz2]

/-- **The base hop.** The canonical excursion of a top `τ` costs `c* ≤ band H`. -/
theorem cstar_exc_le (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    cstar (upperFrames x T hx) (exc x T τ) ≤ band (height x T τ) := by
  have hxτ := x_top x T τ
  have hσ : ownerScale (upperFrames x T hx) (exc x T τ) = band (prom x T τ) :=
    ownerScale_ladderHop hx le_rfl (base_lt hτ)
  -- the σ cap
  have hcap : (prom x T τ : ℤ) ≤ x τ - base x T τ →
      cstar (upperFrames x T hx) (exc x T τ) ≤ band (height x T τ) := fun h => by
    unfold cstar
    rw [hσ]
    exact (min_le_right _ _).trans (band_mono (by omega))
  obtain ⟨h1τ, hτT, hup, -⟩ := top_spec hx hτ
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  have hF := own_inner_top hx hτ
  rcases inner_fst_cases hx hτ with ⟨P, hP, hyP, hFeq, hDa⟩ | hF1
  · -- the first excursion of a descent structure: the parent top is earlier and at least as high
    apply hcap
    obtain ⟨hy1, hy2⟩ := mem_levels.mp hyP
    have hc1 : base x T P ≤ base x T τ - 1 := by omega
    have hc2 : base x T τ - 1 < x P := by omega
    have hτF := hF.2.1
    rw [hFeq] at hτF
    have hτ1 : ladD x T P (base x T τ) + 1 ≤ τ := hτF.1
    have hτ2 : τ < ladD x T P (base x T τ - 1) := hτF.2
    have hPD := lt_ladD hx hy1.le hy2
    have hLP := ladL_lt hx hy1.le hy2
    have hLP' := ladL_lt hx hc1 hc2
    have ho : IsOwner x (ladL x T P (base x T τ - 1)) (ladD x T P (base x T τ - 1)) P :=
      ((mem_ladder hx).mp (ladL_mem hx hc1 hc2)).2.2
    refine prom_le_of_left h1τ hup (s := P) (by omega) (ho.max τ (by omega) hτ2)
      fun r hr1 hr2 => ?_
    rcases lt_or_ge r (exc x T τ).1 with h | h
    · have := ladL_above hx hy1.le hy2 (t := r) (by omega) (by omega)
      omega
    · exact (exc_range hx hτ h (by omega)).1
  rcases inner_snd_cases hx hτ with ⟨P, hP, hyP, hFeq, hLb⟩ | hF2
  · -- the last excursion of a hanging structure: the parent top is later and strictly higher
    apply hcap
    obtain ⟨hy1, hy2⟩ := mem_levels.mp hyP
    have hc1 : base x T P ≤ base x T τ - 1 := by omega
    have hc2 : base x T τ - 1 < x P := by omega
    have hτF := hF.2.1
    rw [hFeq] at hτF
    have hτ1 : ladL x T P (base x T τ - 1) + 1 ≤ τ := hτF.1
    have hτ2 : τ < ladL x T P (base x T τ) := hτF.2
    have hLP := ladL_lt hx hy1.le hy2
    have hPD := lt_ladD hx hy1.le hy2
    have hDT := ladD_lt_T hx hy1.le hy2
    have ho : IsOwner x (ladL x T P (base x T τ - 1)) (ladD x T P (base x T τ - 1)) P :=
      ((mem_ladder hx).mp (ladL_mem hx hc1 hc2)).2.2
    refine prom_le_of_right h1τ hup (s := P) (by omega) (by omega)
      (ho.first τ (by omega) (by omega)) fun r hr1 hr2 => ?_
    rcases le_or_gt r (exc x T τ).2 with h | h
    · exact (exc_range hx hτ (by omega) h).1
    · have := ladL_above hx hy1.le hy2 (t := r) (by omega) (by omega)
      omega
  -- otherwise `a` and `b` lie in the frame of the excursion: the per-hop estimate with `B = band H`
  have hmem := fun c (h1 : (exc x T τ).1 ≤ c) (h2 : c ≤ (exc x T τ).2) =>
    segStart_inner_mem_Icc hx hτ hF1 hF2 h1 h2
  have hbp : bandP (upperFrames x T hx) (exc x T τ) ≤ band (height x T τ) :=
    band_mono (runMax_le_height hx hτ (hmem _ le_rfl (by omega)).1 (by omega))
  have hbu : bandU (upperFrames x T hx) (exc x T τ) ≤ band (height x T τ) :=
    band_mono (runMax_le_height hx hτ (hmem _ (by omega) le_rfl).1 le_rfl)
  have hS : homeBand (upperFrames x T hx) (exc x T τ) ≤ band (height x T τ) := by
    refine band_mono (Finset.sup_le fun c hc => ?_)
    obtain ⟨hc1, hc2⟩ := mem_Icc.mp hc
    have hs := hmem c hc1 hc2
    have hr := exc_range hx hτ hs.1 (by omega)
    show (x (exc x T τ).1 - x ((upperFrames x T hx).segStart
      ((upperFrames x T hx).inner c) c)).natAbs ≤ height x T τ
    rw [x_exc_fst hx hτ]
    omega
  have hev : FrameMicro (upperFrames x T hx) (exc x T τ) →
      bandU (upperFrames x T hx) (exc x T τ) ≤
        max (ownerScale (upperFrames x T hx) (exc x T τ))
          (pushMax (upperFrames x T hx) (exc x T τ)) := by
    intro hfm
    rcases Nat.lt_or_ge (height x T τ) 2 with hH | hH
    · -- `H = 1`: `β(b) ≤ band 1 = 0`
      have hH1 : height x T τ = 1 := by have := one_le_height hτ; omega
      rw [hH1, show band 1 = 0 from Nat.log_one_right 2] at hbu
      omega
    · -- `H ≥ 2`: the segment at `b` started after `a`, at the passage `D τ (y + 1)` or later
      exfalso
      have hPmem : ladD x T τ (base x T τ + ((2 ^ 0 : ℕ) : ℤ)) ∈ passages x T τ :=
        mem_passages.mpr ⟨0, by norm_num; omega, rfl⟩
      obtain ⟨hτP, hPb, hPR, hPf⟩ := passage_spec hx hτ hPmem
      have hFb := inner_top_bounds hx hτ
      have hfm' : (upperFrames x T hx).segStart ((upperFrames x T hx).inner (exc x T τ).2)
          (exc x T τ).2 ≤ (exc x T τ).1 := hfm
      rcases inner_exc_snd hx hτ hF2 with h | h
      · rw [h] at hfm'
        have := le_segStart (S := upperFrames x T hx) (F := (upperFrames x T hx).inner τ)
          (t := (exc x T τ).2)
          (Or.inr ⟨hPR, by omega, own_of_free hx hτ (by omega) hPb hPf⟩) hPb.le
        omega
      · have := start_le_segStart (S := upperFrames x T hx)
          ((upperFrames x T hx).inner (exc x T τ).2) (exc x T τ).2
        omega
  unfold cstar
  exact (min_le_left _ _).trans ((hopCost_le_of_bands hbp hbu hS hev).trans (Nat.sub_le _ _))

/-- **The ladder hops.** For `1 ≤ d < H`, the ladder hop of `τ` at cell `y + d` costs at most
`(B − band (d − 1)) + (B − uband H d)`. -/
theorem cstar_ladder_le (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) :
    cstar (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) ≤
      (band (height x T τ) - band (d - 1)) + (band (height x T τ) - uband (height x T τ) d) := by
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  obtain ⟨hp1, hp2⟩ := beta_ladL_bounds hx hτ hd1 hdH
  obtain ⟨hu1, hu2⟩ := beta_ladD_bounds hx hτ hd1 hdH
  have hL := ladL_lt_ladL hx le_rfl (show base x T τ < base x T τ + d by omega) hz2
  have hL1 : (exc x T τ).1 < ladL x T τ (base x T τ + d) := hL.1
  have hD2 : ladD x T τ (base x T τ + d) < (exc x T τ).2 := hL.2
  have hLD := (ladL_lt hx hz1 hz2).trans (lt_ladD hx hz1 hz2)
  have hbp : bandP (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) ≤
      band (height x T τ) := hp2
  have hbu : bandU (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) ≤
      band (height x T τ) := hu2
  -- the home band
  have hS : homeBand (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) ≤
      band (height x T τ) := by
    refine band_mono (Finset.sup_le fun c hc => ?_)
    have hc' : ladL x T τ (base x T τ + d) ≤ c ∧ c ≤ ladD x T τ (base x T τ + d) := mem_Icc.mp hc
    have hh := home_mem_exc hx hτ (t := c) (by omega) (by omega)
    have hxL := x_ladL hx hz1 hz2
    have hxτ := x_top x T τ
    show (x (ladL x T τ (base x T τ + d)) - (upperFrames x T hx).home c).natAbs ≤ height x T τ
    omega
  -- eventfulness
  have hev : FrameMicro (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) →
      bandU (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) ≤
        max (ownerScale (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)))
          (pushMax (upperFrames x T hx) (ladderHop x T τ (base x T τ + d))) := by
    intro hfm
    by_cases hpass : 2 ^ Nat.clog 2 d < height x T τ
    · exact absurd hfm (not_le.mpr (ladL_lt_segStart_ladD hx hτ hd1 hdH hpass))
    · rw [ownerScale_ladderHop hx hz1 hz2]
      exact le_max_of_le_left (hbu.trans (band_mono (height_le_prom hx hτ)))
  unfold cstar
  refine (min_le_left _ _).trans ((hopCost_le_of_bands hbp hbu hS hev).trans ?_)
  have : bandP (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) =
      (upperFrames x T hx).beta (ladL x T τ (base x T τ + d)) := rfl
  have : bandU (upperFrames x T hx) (ladderHop x T τ (base x T τ + d)) =
      (upperFrames x T hx).beta (ladD x T τ (base x T τ + d)) := rfl
  omega

/-- **The per-excursion bound.** The ladder hops of a top `τ` cost at most `6H` in total. -/
theorem sum_ladder_cstar_le (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    ∑ e ∈ ladder x T τ, cstar (upperFrames x T hx) e ≤ 6 * height x T τ := by
  have hinj : Set.InjOn (fun d : ℕ => ladderHop x T τ (base x T τ + d))
      (range (height x T τ) : Set ℕ) := by
    intro d hd d' hd' h
    obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) (mem_range.mp (mem_coe.mp hd))
    obtain ⟨hz1', hz2'⟩ := cell_bounds (x := x) (T := T) (τ := τ) (mem_range.mp (mem_coe.mp hd'))
    have e1 := x_ladL hx hz1 hz2
    have h1 : ladL x T τ (base x T τ + d) = ladL x T τ (base x T τ + d') := congrArg Prod.fst h
    rw [h1, x_ladL hx hz1' hz2'] at e1
    omega
  have himg : (range (height x T τ)).image (fun d : ℕ => ladderHop x T τ (base x T τ + d)) =
      ladder x T τ := by
    refine eq_of_subset_of_card_le (fun e he => ?_) ?_
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp he
      obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) (mem_range.mp hd)
      exact ladL_mem hx hz1 hz2
    · rw [card_image_of_injOn hinj, card_range]
      exact le_rfl
  rw [← himg, sum_image hinj]
  refine sum_range_le_six_of_ladder _ ?_ fun d hd1 hdH => cstar_ladder_le hx hτ hd1 hdH
  show cstar (upperFrames x T hx) (ladderHop x T τ (base x T τ + ((0 : ℕ) : ℤ))) ≤ _
  rw [Nat.cast_zero, add_zero]
  exact cstar_exc_le hx hτ

open Classical in
/-- **Theorem A, class U.** Summed over the `h₀` grid offsets, the lost upper hops number at most
`6` times the upper hops. -/
theorem thmA_upper (hx : IsWalk x) (h₀ : ℕ) :
    ∑ r ∈ range h₀, ((upperHops x T).filter (Lost (upperFrames x T hx) h₀ r)).card ≤
      6 * (upperHops x T).card :=
  (sum_card_lost_le_sum_cstar _ h₀ _).trans
    (sum_cstar_le_of_ladders _ fun _ hτ => sum_ladder_cstar_le hx hτ)

open Classical in
/-- **Theorem A, class L.** The lower hops of `x` are the upper hops of `−x`, with the frames of
class U of `−x`. -/
theorem thmA_lower (hx : IsWalk x) (h₀ : ℕ) :
    ∑ r ∈ range h₀,
        ((lowerHops x T).filter (Lost (upperFrames (fun t => -x t) T hx.neg) h₀ r)).card ≤
      6 * (lowerHops x T).card := by
  have := thmA_upper (x := fun t => -x t) (T := T) hx.neg h₀
  rwa [upperHops_neg] at this

end BoundedStackDepth

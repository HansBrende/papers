import AdaptiveTransfer.TransferCrossingEpochs

/-! Canonical labels for literal crossing lower endpoints. A label fixes
two signed epoch extrema and their prefix/suffix overlap. Both endpoint
roles and both polarities are constructed from actual consecutive revisits.
-/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations MergeDepth

noncomputable def overlapLow (y : ℕ → ℤ) (U H : ℕ) (sign : Bool) (e₁ e₂ : ℕ) : ℤ :=
  max (signed y sign (prefixMin y sign (epochMax y U H sign e₁)))
    (signed y sign (epochMin y U H sign e₂))

noncomputable def overlapHigh (y : ℕ → ℤ) (U H : ℕ) (sign : Bool) (e₁ e₂ : ℕ) : ℤ :=
  min (signed y sign (epochMax y U H sign e₁))
    (signed y sign (suffixMax y U sign (epochMin y U H sign e₂)))

structure CrossingFrame (y : ℕ → ℤ) (U H v : ℕ) where
  sign : Bool
  firstEpoch : ℕ
  secondEpoch : ℕ
  second : Bool
  epoch_order : firstEpoch < secondEpoch
  epoch_bound : secondEpoch ≤ (tapeSkeleton y U H).length
  finish : ℕ
  hop : IsHop y U v finish
  excursion : HasHopExcursionGTAt y (2 * H) v finish
  inside : v < (if second then epochMin y U H sign secondEpoch else epochMax y U H sign firstEpoch) ∧
    (if second then epochMin y U H sign secondEpoch else epochMax y U H sign firstEpoch) < finish
  left_before : prefixMin y sign (epochMax y U H sign firstEpoch) ≤ v
  role_time : if second then epochMax y U H sign firstEpoch ≤ v else v < epochMax y U H sign firstEpoch
  target_valley : v < epochMin y U H sign secondEpoch
  peak_valley : epochMax y U H sign firstEpoch < epochMin y U H sign secondEpoch
  valley_right : epochMin y U H sign secondEpoch < suffixMax y U sign (epochMin y U H sign secondEpoch)
  right_lt : suffixMax y U sign (epochMin y U H sign secondEpoch) < U
  level : overlapLow y U H sign firstEpoch secondEpoch ≤ signed y sign v ∧
    signed y sign v ≤ overlapHigh y U H sign firstEpoch secondEpoch
  one_sided : ∀ r ∈ Icc v (if second then epochMin y U H sign secondEpoch else epochMax y U H sign firstEpoch),
    if second then signed y sign r ≤ signed y sign v else signed y sign v ≤ signed y sign r

private theorem normalized_frames {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H p p' u u' : ℕ} (hH : 1 ≤ H) (sign : Bool)
    (hh : IsHop y U p u) (he : HasHopExcursionGTAt y (2 * H) p u)
    (hh' : IsHop y U p' u') (he' : HasHopExcursionGTAt y (2 * H) p' u')
    (hpp : p < p') (hpu : p' < u) (huu : u < u')
    (hab : signed y sign p < signed y sign p')
    (hupper : ∀ r ∈ Ioo p u, signed y sign p < signed y sign r)
    (hlower : ∀ r ∈ Ioo p' u', signed y sign r < signed y sign p') :
    Nonempty (CrossingFrame y U H p) ∧ Nonempty (CrossingFrame y U H p') := by
  classical
  let w := signed y sign
  let r := maximizeOn w (Ioo p u)
  let r' := minimizeOn w (Ioo p' u')
  have hr := maximizeOn_spec (f := w) (show (Ioo p u).Nonempty from ⟨p', mem_Ioo.mpr ⟨hpp, hpu⟩⟩)
  have hr' := minimizeOn_spec (f := w) (show (Ioo p' u').Nonempty from ⟨u, mem_Ioo.mpr ⟨hpu, huu⟩⟩)
  have hr_in : r ∈ Ioo p u := hr.1
  have hr'_in : r' ∈ Ioo p' u' := hr'.1
  have hrT : r < U := (mem_Ioo.mp hr_in).2.trans hh.2.1
  have hr'T : r' < U := (mem_Ioo.mp hr'_in).2.trans hh'.2.1
  have wend : w u = w p := by simp only [w, signed, hh.2.2.1]
  have hrb : w p' ≤ w r := hr.2 p' (mem_Ioo.mpr ⟨hpp, hpu⟩)
  have hr'a : w r' ≤ w p := by simpa only [wend] using hr'.2 u (mem_Ioo.mpr ⟨hpu, huu⟩)
  have hfar : 2 * (H : ℤ) < w r - w p := by
    obtain ⟨z, hz, hzx⟩ := he
    have hzup : w p < w z := hupper z hz
    have hzm : w z ≤ w r := hr.2 z hz
    rw [← signed_abs_sub y sign z p] at hzx
    change ((2 * H : ℕ) : ℤ) < |w z - w p| at hzx
    rw [abs_of_pos (by omega)] at hzx
    push_cast at hzx
    change 2 * (H : ℤ) < w z - w p at hzx
    omega
  have hfar' : 2 * (H : ℤ) < w p' - w r' := by
    obtain ⟨z, hz, hzx⟩ := he'
    have hzlow : w z < w p' := hlower z hz
    have hzm : w r' ≤ w z := hr'.2 z hz
    rw [← signed_abs_sub y sign z p'] at hzx
    change ((2 * H : ℕ) : ℤ) < |w z - w p'| at hzx
    rw [abs_of_neg (by omega)] at hzx
    push_cast at hzx
    change 2 * (H : ℤ) < -(w z - w p') at hzx
    omega
  let e₁ := epochIdx y H r
  let e₂ := epochIdx y H r'
  let A := epochMax y U H sign e₁
  let B := epochMin y U H sign e₂
  have hA := epochMax_spec (y := y) (H := H) hrT sign
  have hB := epochMin_spec (y := y) (H := H) hr'T sign
  have hAT : A < U := mem_range.mp (mem_filter.mp hA.1).1
  have hBT : B < U := mem_range.mp (mem_filter.mp hB.1).1
  have hAe : epochIdx y H A = e₁ := (mem_filter.mp hA.1).2
  have hBe : epochIdx y H B = e₂ := (mem_filter.mp hB.1).2
  have hrA : w r ≤ w A := hA.2
  have hBr : w B ≤ w r' := hB.2
  have hAin : A ∈ Ioo p u := epoch_inside_long_hop hy hy0 hH hh hr_in
    (by rw [← signed_abs_sub y sign r p, abs_of_pos (by have := hupper r hr_in; omega)]; exact hfar)
    hAT hAe
  have hBin : B ∈ Ioo p' u' := epoch_inside_long_hop hy hy0 hH hh' hr'_in
    (by
      rw [← signed_abs_sub y sign r' p']
      change ((2 * H : ℕ) : ℤ) < |w r' - w p'|
      rw [abs_of_neg (by omega)]
      push_cast
      omega)
    hBT hBe
  have hAp : A ≤ p' := by
    by_contra hbad
    have hz : w A < w p' := hlower A (mem_Ioo.mpr ⟨by omega, (mem_Ioo.mp hAin).2.trans huu⟩)
    omega
  have huB : u ≤ B := by
    by_contra hbad
    have hz : w p < w B := hupper B (mem_Ioo.mpr ⟨hpp.trans (mem_Ioo.mp hBin).1, by omega⟩)
    omega
  have hAB : A < B := hAp.trans_lt (hpu.trans_le huB)
  have heorder : e₁ < e₂ := by
    have hmono := epochIdx_mono (y := y) (Λ := H) hAB.le
    rw [hAe, hBe] at hmono
    by_contra hbad
    have heq : epochIdx y H A = epochIdx y H B := by omega
    have hd := epoch_diameter hy hy0 hH hAT hBT heq sign
    have hpos : 0 ≤ w A - w B := by omega
    rw [abs_of_nonneg hpos] at hd
    omega
  have hebound : e₂ ≤ (tapeSkeleton y U H).length := by
    rw [← hBe]
    exact epochIdx_le_length hBT
  let t₀ := prefixMin y sign A
  let t₃ := suffixMax y U sign B
  have hmin := minimizeOn_spec (f := w) (show (Icc 0 A).Nonempty from ⟨0, by simp⟩)
  have hmax := maximizeOn_spec (f := w) (show (Ico B U).Nonempty from ⟨B, mem_Ico.mpr ⟨le_rfl, hBT⟩⟩)
  have ht₀A : t₀ ≤ A := (mem_Icc.mp hmin.1).2
  have hBt₃ : B ≤ t₃ := (mem_Ico.mp hmax.1).1
  have ht₃T : t₃ < U := (mem_Ico.mp hmax.1).2
  have ht₀val : w t₀ ≤ w p := hmin.2 p (mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioo.mp hAin).1.le⟩)
  have ht₃val : w p' ≤ w t₃ := by
    have hhmax := hmax.2 u' (mem_Ico.mpr ⟨(mem_Ioo.mp hBin).2.le, hh'.2.1⟩)
    have hw' : w u' = w p' := by simp only [w, signed, hh'.2.2.1]
    rwa [hw'] at hhmax
  have ht₀p : t₀ ≤ p := by
    by_contra hbad
    have hz : w p < w t₀ := hupper t₀ (mem_Ioo.mpr ⟨by omega, ht₀A.trans_lt (mem_Ioo.mp hAin).2⟩)
    omega
  have hu't₃ : u' ≤ t₃ := by
    by_contra hbad
    have hz : w t₃ < w p' := hlower t₃ (mem_Ioo.mpr ⟨(mem_Ioo.mp hBin).1.trans_le hBt₃, by omega⟩)
    omega
  have hlow : overlapLow y U H sign e₁ e₂ ≤ w p := by
    change max (w t₀) (w B) ≤ w p
    exact max_le ht₀val (hBr.trans hr'a)
  have hhigh : w p' ≤ overlapHigh y U H sign e₁ e₂ := by
    change w p' ≤ min (w A) (w t₃)
    exact le_min (hrb.trans hrA) ht₃val
  constructor
  · refine ⟨{
      sign := sign, firstEpoch := e₁, secondEpoch := e₂, second := false,
      epoch_order := heorder, epoch_bound := hebound, finish := u, hop := hh, excursion := he,
      inside := mem_Ioo.mp hAin, left_before := ht₀p, role_time := (mem_Ioo.mp hAin).1,
      target_valley := (mem_Ioo.mp hAin).1.trans hAB, peak_valley := hAB,
      valley_right := (mem_Ioo.mp hBin).2.trans_le hu't₃, right_lt := ht₃T,
      level := ⟨hlow, hab.le.trans hhigh⟩,
      one_sided := ?_ }⟩
    intro z hz
    have hzi := mem_Icc.mp hz
    rcases eq_or_lt_of_le hzi.1 with heq | hpz
    · subst z
      exact le_rfl
    · exact (hupper z (mem_Ioo.mpr ⟨hpz, hzi.2.trans_lt (mem_Ioo.mp hAin).2⟩)).le
  · refine ⟨{
      sign := sign, firstEpoch := e₁, secondEpoch := e₂, second := true,
      epoch_order := heorder, epoch_bound := hebound, finish := u', hop := hh', excursion := he',
      inside := mem_Ioo.mp hBin, left_before := ht₀p.trans hpp.le, role_time := hAp,
      target_valley := (mem_Ioo.mp hBin).1, peak_valley := hAB,
      valley_right := (mem_Ioo.mp hBin).2.trans_le hu't₃, right_lt := ht₃T,
      level := ⟨hlow.trans hab.le, hhigh⟩,
      one_sided := ?_ }⟩
    intro z hz
    have hzi := mem_Icc.mp hz
    rcases eq_or_lt_of_le hzi.1 with heq | hpz
    · subst z
      exact le_rfl
    · exact (hlower z (mem_Ioo.mpr ⟨hpz, hzi.2.trans_lt (mem_Ioo.mp hBin).2⟩)).le

/-- Every literal crossing lower endpoint receives a canonical finite
epoch/sign/role label; no extremizer or assignment certificate is supplied. -/
theorem crossing_frame_exists {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H v : ℕ} (hH : 1 ≤ H) (hv : v ∈ tapeCrossingLowers y U H) :
    Nonempty (CrossingFrame y U H v) := by
  classical
  obtain ⟨_, u, hh, he, p', u', hh', he', hcr⟩ := mem_filter.mp hv
  have core {p p' u u' : ℕ} (hh : IsHop y U p u) (he : HasHopExcursionGTAt y (2 * H) p u)
      (hh' : IsHop y U p' u') (he' : HasHopExcursionGTAt y (2 * H) p' u')
      (h₁ : p < p') (h₂ : p' < u) (h₃ : u < u') :
      Nonempty (CrossingFrame y U H p) ∧ Nonempty (CrossingFrame y U H p') := by
    rcases crossing_isHop_opposite_polarity hy hh hh' h₁ h₂ h₃ with
      ⟨ha, hup, hlo⟩ | ⟨ha, hlo, hup⟩
    · exact normalized_frames hy hy0 hH true hh he hh' he' h₁ h₂ h₃ ha hup hlo
    · apply normalized_frames hy hy0 hH false hh he hh' he' h₁ h₂ h₃
      · simpa only [signed, Bool.false_eq_true, ↓reduceIte, neg_lt_neg_iff] using ha
      · intro r hr
        simpa only [signed, Bool.false_eq_true, ↓reduceIte, neg_lt_neg_iff] using hlo r hr
      · intro r hr
        simpa only [signed, Bool.false_eq_true, ↓reduceIte, neg_lt_neg_iff] using hup r hr
  rcases hcr with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact (core hh he hh' he' h₁ h₂ h₃).1
  · exact (core hh' he' hh he h₁ h₂ h₃).2

end AdaptiveTransfer.TransferCrossing

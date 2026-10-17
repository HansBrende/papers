import Transpose.Tape.MStarAnalysis

/-!
# Labelling-free consequences of (★), and the non-triviality of (★)

(★) holds for every labelling. Taking `S = ∅` and the labels `⌊m u⌋` (`θ = 1/m`) and letting
`m → ∞` removes the labelling: almost every consecutive pair of a level set then carries different
labels. Everything here is TM-free; the walk core (`MStarWalk.lean`) states its conclusion with it.

* `levelCross_le_levelExcess`: `κ(p) ≤ #Λ(p) − 1` for every `S` and `β`.
* `pc_floorMul`, `class_floorMul`: the labelling `⌊m u⌋` (`m ≥ 1`) is admissible with `S = ∅` and
  `θ = 1/m`.
* `one_le_excess_of_star`: if (★) holds for every `θ ∈ (0, ½)`, `S` and `β`, then
  `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1`: the limit head paths revisit levels, with total excess multiplicity
  at least `1`. (`levelExcess` is `⊤` on infinite level sets; for 1-Lipschitz paths these are a null
  set of levels and `∫⁻ levelExcess ≤ c₀ < ⊤`, so the convention trivializes nothing.)
* `excess_add_range_le`: for 1-Lipschitz `P` on `[0, c₀]`,
  `∫⁻ (#Λ(p) − 1) dp + |P([0, c₀])| ≤ c₀` (the easy half of Banach's indicatrix,
  `lintegral_encard_levelSet_le`).
* `range_add_one_le_of_star`: hence `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`: the ranges of the `k` limit
  paths fall short of their maximum `c₀` by at least `1` in total.
* `lintegral_levelExcess_eq_zero_of_monotone`, `not_all_monotone_of_star`: a monotone path has excess
  `0` off a countable set of levels, so the `k` limit paths cannot all be monotone (or antitone): some
  head must make a macroscopic U-turn.
* `excess_of_star`: the three together, for 1-Lipschitz paths satisfying (★).
* `theoremMStar_conclusion_can_fail`: for `P = 0`, `S = ∅`, `β u = ⌊4u⌋` and `θ = 1/4` the
  hypotheses on `S`, `β`, `θ` hold and (★) fails (`κ ≡ 0`, since a monotone path has no excess), so
  (★) is a genuine constraint.

The machine forms are elsewhere: `theoremMStar_excess` and `no_stationary_limits` (oblivious) in
`MStar.lean`, `theoremMStar_excess_nonuniform` and `theoremMStar_excess_robust` in
`MStarRobust.lean`, `no_stationary_limits_class` in `MStarAdaptive.lean`.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-! ### `κ ≤ #Λ − 1` -/

/-- Consecutive pairs with the same first point coincide. -/
theorem consecIn_snd_unique {Λ : Set ℝ} {s s' s'' : ℝ} (h' : ConsecIn Λ s s')
    (h'' : ConsecIn Λ s s'') : s' = s'' := by
  rcases lt_trichotomy s' s'' with hlt | heq | hgt
  · exact absurd ⟨h'.2.2.1, hlt⟩ (h''.2.2.2 s' h'.2.1)
  · exact heq
  · exact absurd ⟨h''.2.2.1, hgt⟩ (h'.2.2.2 s'' h''.2.1)

/-- A finite level set with `N` points has at most `N − 1` consecutive pairs. -/
theorem ncard_crossPairs_le {P : ℝ → ℝ} {S : Set ℝ} {β : ℝ → ℕ} {c₀ p : ℝ}
    (hfin : (levelSet P c₀ p).Finite) :
    (crossPairs P S β c₀ p).ncard ≤ (levelSet P c₀ p).ncard - 1 := by
  classical
  rcases (crossPairs P S β c₀ p).eq_empty_or_nonempty with h0 | ⟨q₀, hq₀⟩
  · rw [h0, Set.ncard_empty]; exact Nat.zero_le _
  obtain ⟨m, hmΛ, hmax⟩ := Set.exists_max_image (levelSet P c₀ p) id hfin ⟨q₀.1, hq₀.1.1⟩
  have hinj : Set.InjOn Prod.fst (crossPairs P S β c₀ p) := by
    intro q hq q' hq' h
    exact Prod.ext h (consecIn_snd_unique hq.1 (h ▸ hq'.1))
  have hsub : Prod.fst '' crossPairs P S β c₀ p ⊆ levelSet P c₀ p \ {m} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq.1.1, fun hqm => ?_⟩
    have h2 := hmax q.2 hq.1.2.1
    have h3 := hq.1.2.2.1
    rw [Set.mem_singleton_iff] at hqm
    simp only [id] at h2
    linarith
  calc (crossPairs P S β c₀ p).ncard = (Prod.fst '' crossPairs P S β c₀ p).ncard :=
        hinj.ncard_image.symm
    _ ≤ (levelSet P c₀ p \ {m}).ncard := Set.ncard_le_ncard hsub (hfin.subset Set.sdiff_subset)
    _ = (levelSet P c₀ p).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hmΛ

/-- **`κ(p) ≤ #Λ(p) − 1`** for every excised set `S` and labelling `β`. -/
theorem levelCross_le_levelExcess (P : ℝ → ℝ) (S : Set ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) :
    levelCross P S β c₀ p ≤ levelExcess P c₀ p := by
  unfold levelCross levelExcess
  split_ifs with hfin
  · rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe]
    have h := ncard_crossPairs_le (S := S) (β := β) hfin
    calc ((crossPairs P S β c₀ p).ncard : ℝ≥0∞)
        ≤ (((levelSet P c₀ p).ncard - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      _ = _ := by rw [ENNReal.natCast_sub, Nat.cast_one]
  · exact zero_le

/-! ### The labellings `⌊m u⌋` -/

theorem finUnionIcc_empty : FinUnionIcc (∅ : Set ℝ) := ⟨∅, by simp⟩

theorem pc_floorMul {m : ℕ} (hm : 0 < m) (c₀ : ℝ) :
    PiecewiseConstOn (fun u : ℝ => ⌊(m : ℝ) * u⌋₊) ∅ c₀ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(Finset.range (⌈(m : ℝ) * c₀⌉₊ + 2)).image (fun j : ℕ => (j : ℝ) / m), ?_⟩
  intro u v hu huv hvc hav
  by_contra hne
  have hmv : (m : ℝ) * u ≤ m * v := mul_le_mul_of_nonneg_left huv hm'.le
  have hmono : ⌊(m : ℝ) * u⌋₊ ≤ ⌊(m : ℝ) * v⌋₊ := Nat.floor_le_floor hmv
  have hlt : ⌊(m : ℝ) * u⌋₊ < ⌊(m : ℝ) * v⌋₊ := lt_of_le_of_ne hmono hne
  set j := ⌊(m : ℝ) * u⌋₊ + 1 with hj
  have hjv : (j : ℝ) ≤ m * v := by
    have : j ≤ ⌊(m : ℝ) * v⌋₊ := hlt
    have h2 : ((⌊(m : ℝ) * v⌋₊ : ℕ) : ℝ) ≤ m * v :=
      Nat.floor_le (mul_nonneg hm'.le (le_trans hu huv))
    have : (j : ℝ) ≤ ((⌊(m : ℝ) * v⌋₊ : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hju : (m : ℝ) * u < (j : ℝ) := by
    rw [hj]; push_cast; exact Nat.lt_floor_add_one _
  have hmem : (j : ℝ) / m ∈ Set.Icc u v :=
    ⟨by rw [le_div_iff₀ hm']; linarith, by rw [div_le_iff₀ hm']; linarith⟩
  apply (hav _ hmem).2
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  refine ⟨j, ?_, rfl⟩
  have h1 : (j : ℝ) ≤ m * c₀ := le_trans hjv (mul_le_mul_of_nonneg_left hvc hm'.le)
  have h2 : (m : ℝ) * c₀ ≤ (⌈(m : ℝ) * c₀⌉₊ : ℝ) := Nat.le_ceil _
  have : (j : ℝ) < (⌈(m : ℝ) * c₀⌉₊ : ℝ) + 2 := by linarith
  exact_mod_cast this

theorem class_floorMul {m : ℕ} (hm : 0 < m) (c₀ : ℝ) (ℓ : ℕ) :
    volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ (∅ : Set ℝ) ∧ (fun u : ℝ => ⌊(m : ℝ) * u⌋₊) u = ℓ} ≤
      ENNReal.ofReal (1 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub : {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ (∅ : Set ℝ) ∧ (fun u : ℝ => ⌊(m : ℝ) * u⌋₊) u = ℓ} ⊆
      Set.Ico ((ℓ : ℝ) / m) (((ℓ : ℝ) + 1) / m) := by
    rintro u ⟨hu, -, hfl⟩
    simp only at hfl
    have h0 : 0 ≤ (m : ℝ) * u := mul_nonneg hm'.le hu.1
    have h1 : ((⌊(m : ℝ) * u⌋₊ : ℕ) : ℝ) ≤ m * u := Nat.floor_le h0
    have h2 : (m : ℝ) * u < ((⌊(m : ℝ) * u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hfl] at h1 h2
    constructor
    · rw [div_le_iff₀ hm']; linarith
    · rw [lt_div_iff₀ hm']; linarith
  calc _ ≤ volume (Set.Ico ((ℓ : ℝ) / m) (((ℓ : ℝ) + 1) / m)) := measure_mono hsub
    _ = ENNReal.ofReal (1 / m) := by rw [Real.volume_Ico]; congr 1; ring

/-! ### The labelling-free inequalities -/

/-- **(★) for all labellings gives total excess multiplicity `≥ 1`.** -/
theorem one_le_excess_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) c₀ p := by
  have key : ∀ m : ℕ, 3 ≤ m →
      1 ≤ (∑ t, ∫⁻ p, levelExcess (P t) c₀ p) + 2 * ENNReal.ofReal (1 / m) := by
    intro m hm3
    have hm : 0 < m := by omega
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hθ0 : 0 < ENNReal.ofReal (1 / m) := ENNReal.ofReal_pos.2 (by positivity)
    have hθ1 : ENNReal.ofReal (1 / m) < 1 / 2 := by
      have e : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      rw [e, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
      rw [div_lt_div_iff₀ hm' (by norm_num)]
      linarith
    have h := hstar (ENNReal.ofReal (1 / m)) hθ0 hθ1 ∅ (fun u => ⌊(m : ℝ) * u⌋₊) finUnionIcc_empty
      (pc_floorMul hm c₀) (class_floorMul hm c₀)
    simp only [Set.empty_inter, measure_empty, mul_zero, add_zero] at h
    refine le_trans h ?_
    gcongr with t _ p
    exact levelCross_le_levelExcess _ _ _ _ _
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨m₁, hm⟩ := exists_nat_gt (2 / (ε : ℝ))
  set m := max m₁ 3 with hmdef
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hm3 : 3 ≤ m := le_max_right _ _
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm : 2 / (ε : ℝ) < m := lt_of_lt_of_le hm (by exact_mod_cast le_max_left m₁ 3)
  refine le_trans (key m hm3) ?_
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_lt_iff₀ hε'] at hm
  rw [mul_one_div, div_le_iff₀ hm']
  linarith

/-- **The easy half of Banach's indicatrix, with the range split off:**
`∫⁻ (#Λ(p) − 1) dp + |P([0, c₀])| ≤ c₀` for 1-Lipschitz `P` on `[0, c₀]`. -/
theorem excess_add_range_le {P : ℝ → ℝ} {c₀ : ℝ} (hP : LipschitzOnWith 1 P (Set.Icc 0 c₀)) :
    (∫⁻ p, levelExcess P c₀ p) + volume (P '' Set.Icc 0 c₀) ≤ ENNReal.ofReal c₀ := by
  have hmeas : MeasurableSet (P '' Set.Icc 0 c₀) :=
    (isCompact_Icc.image_of_continuousOn hP.continuousOn).isClosed.measurableSet
  have hpt : ∀ p, levelExcess P c₀ p + (P '' Set.Icc 0 c₀).indicator 1 p ≤
      ((levelSet P c₀ p).encard : ℝ≥0∞) := by
    intro p
    unfold levelExcess
    by_cases hp : p ∈ P '' Set.Icc 0 c₀
    · rw [Set.indicator_of_mem hp, Pi.one_apply]
      have hne : (levelSet P c₀ p).Nonempty := by
        obtain ⟨s, hs, rfl⟩ := hp
        exact ⟨s, hs, rfl⟩
      have h1 : (1 : ℝ≥0∞) ≤ ((levelSet P c₀ p).encard : ℝ≥0∞) := by
        have := Set.one_le_encard_iff_nonempty.2 hne
        exact_mod_cast this
      exact (tsub_add_cancel_of_le h1).le
    · rw [Set.indicator_of_notMem hp, add_zero]
      exact tsub_le_self
  calc (∫⁻ p, levelExcess P c₀ p) + volume (P '' Set.Icc 0 c₀)
      = (∫⁻ p, levelExcess P c₀ p) + ∫⁻ p, (P '' Set.Icc 0 c₀).indicator 1 p := by
        rw [lintegral_indicator_one hmeas]
    _ = ∫⁻ p, (levelExcess P c₀ p + (P '' Set.Icc 0 c₀).indicator 1 p) :=
        (lintegral_add_right _ (measurable_one.indicator hmeas)).symm
    _ ≤ ∫⁻ p, ((levelSet P c₀ p).encard : ℝ≥0∞) := lintegral_mono hpt
    _ ≤ ENNReal.ofReal c₀ := by
        have := lintegral_encard_levelSet_le (K := 1) hP
        simpa using this

/-- **(★) for all labellings caps the total range:** `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`. -/
theorem range_add_one_le_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hlip : ∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 c₀))
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    1 + ∑ t, volume (P t '' Set.Icc 0 c₀) ≤ k * ENNReal.ofReal c₀ := by
  have h1 := one_le_excess_of_star hstar
  calc 1 + ∑ t, volume (P t '' Set.Icc 0 c₀)
      ≤ (∑ t, ∫⁻ p, levelExcess (P t) c₀ p) + ∑ t, volume (P t '' Set.Icc 0 c₀) :=
        by gcongr
    _ = ∑ t, ((∫⁻ p, levelExcess (P t) c₀ p) + volume (P t '' Set.Icc 0 c₀)) :=
        (Finset.sum_add_distrib).symm
    _ ≤ ∑ _t : Fin k, ENNReal.ofReal c₀ := Finset.sum_le_sum fun t _ => excess_add_range_le (hlip t)
    _ = k * ENNReal.ofReal c₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Monotone paths -/

/-- `#Λ(p) − 1 = 0` exactly when `Λ(p)` has at most one point. -/
theorem levelExcess_eq_zero_iff {P : ℝ → ℝ} {c₀ p : ℝ} :
    levelExcess P c₀ p = 0 ↔ (levelSet P c₀ p).encard ≤ 1 := by
  unfold levelExcess
  rw [tsub_eq_zero_iff_le, ← ENat.toENNReal_one, ENat.toENNReal_le]

/-- **A monotone path has excess `0` off a countable set of levels**: if `P` is monotone or antitone
on `[0, c₀]`, every level with two preimages is the value of `P` at a rational point between them.
So `∫⁻ (#Λ(p) − 1) dp = 0`. -/
theorem lintegral_levelExcess_eq_zero_of_monotone {P : ℝ → ℝ} {c₀ : ℝ}
    (hmono : MonotoneOn P (Set.Icc 0 c₀) ∨ AntitoneOn P (Set.Icc 0 c₀)) :
    ∫⁻ p, levelExcess P c₀ p = 0 := by
  set C := P '' (Set.range ((↑) : ℚ → ℝ) ∩ Set.Icc 0 c₀) with hC
  have hCc : C.Countable := ((Set.countable_range _).mono Set.inter_subset_left).image P
  have hsub : {p | levelExcess P c₀ p ≠ 0} ⊆ C := by
    intro p hp
    simp only [Set.mem_ofPred_eq, ne_eq, levelExcess_eq_zero_iff, not_le,
      Set.one_lt_encard_iff] at hp
    obtain ⟨s, s', hs, hs', hne⟩ := hp
    have key : ∀ a b, a ∈ levelSet P c₀ p → b ∈ levelSet P c₀ p → a < b → p ∈ C := by
      intro a b ha hb hab
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
      have hqI : (q : ℝ) ∈ Set.Icc 0 c₀ := ⟨le_trans ha.1.1 hq1.le, le_trans hq2.le hb.1.2⟩
      refine ⟨q, ⟨⟨q, rfl⟩, hqI⟩, ?_⟩
      rcases hmono with hm | hm
      · have h1 := hm ha.1 hqI hq1.le
        have h2 := hm hqI hb.1 hq2.le
        rw [ha.2] at h1
        rw [hb.2] at h2
        exact le_antisymm h2 h1
      · have h1 := hm ha.1 hqI hq1.le
        have h2 := hm hqI hb.1 hq2.le
        rw [ha.2] at h1
        rw [hb.2] at h2
        exact le_antisymm h1 h2
    rcases lt_or_gt_of_ne hne with h | h
    · exact key s s' hs hs' h
    · exact key s' s hs' hs h
  have hnull : volume {p | levelExcess P c₀ p ≠ 0} = 0 :=
    measure_mono_null hsub (hCc.measure_zero _)
  have hae : (fun p => levelExcess P c₀ p) =ᵐ[volume] fun _ => 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    simpa only [ne_eq] using hnull
  rw [lintegral_congr_ae hae, lintegral_zero]

/-- **(★) for every labelling rules out monotone limits:** the `k` paths cannot all be monotone or
antitone on `[0, c₀]`. -/
theorem not_all_monotone_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 c₀) ∨ AntitoneOn (P t) (Set.Icc 0 c₀) := by
  intro hmono
  have h := one_le_excess_of_star hstar
  simp only [lintegral_levelExcess_eq_zero_of_monotone (hmono _), Finset.sum_const_zero] at h
  exact absurd h (by norm_num)

/-! ### The package, and non-triviality -/

/-- **The labelling-free package**: 1-Lipschitz paths satisfying (★) for every labelling have total
excess multiplicity `≥ 1` and total range `≤ k c₀ − 1`, and are not all monotone. -/
theorem excess_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hlip : ∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 c₀))
    (hstar : ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S c₀ →
      (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) c₀ p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 c₀) ≤ k * ENNReal.ofReal c₀ ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 c₀) ∨ AntitoneOn (P t) (Set.Icc 0 c₀) :=
  have h := fun θ (_ : 0 < θ) (_ : θ < 1 / 2) => hstar θ
  ⟨one_le_excess_of_star h, range_add_one_le_of_star hlip h, not_all_monotone_of_star h⟩

/-- **The conclusion of (★) can fail**: for `P = 0`, `S = ∅`, `β u = ⌊4u⌋` and `θ = 1/4`, every
hypothesis on `S`, `β` and `θ` holds and the inequality fails (`κ ≤ #Λ − 1`, whose integral vanishes
for the monotone path `0`). -/
theorem theoremMStar_conclusion_can_fail (k : ℕ) (c₀ : ℝ) :
    FinUnionIcc (∅ : Set ℝ) ∧ PiecewiseConstOn (fun u : ℝ => ⌊4 * u⌋₊) ∅ c₀ ∧
    (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ (∅ : Set ℝ) ∧ (fun u : ℝ => ⌊4 * u⌋₊) u = ℓ} ≤
      ENNReal.ofReal (1 / 4)) ∧
    ¬ (1 ≤ (∑ _t : Fin k, ∫⁻ p, levelCross (fun _ => 0) ∅ (fun u : ℝ => ⌊4 * u⌋₊) c₀ p) +
        2 * ENNReal.ofReal (1 / 4) + 2 * k * volume ((∅ : Set ℝ) ∩ Set.Icc 0 c₀)) := by
  refine ⟨finUnionIcc_empty, by simpa using pc_floorMul (m := 4) (by norm_num) c₀,
    fun ℓ => by simpa using class_floorMul (m := 4) (by norm_num) c₀ ℓ, ?_⟩
  have h0 : ∫⁻ p, levelCross (fun _ => (0 : ℝ)) ∅ (fun u : ℝ => ⌊4 * u⌋₊) c₀ p = 0 :=
    le_antisymm ((lintegral_mono fun p => levelCross_le_levelExcess _ _ _ _ p).trans_eq
      (lintegral_levelExcess_eq_zero_of_monotone (Or.inl monotoneOn_const))) zero_le
  simp only [h0, Finset.sum_const_zero, zero_add, Set.empty_inter, measure_empty, mul_zero,
    add_zero]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

end Transpose.Tape.Impl

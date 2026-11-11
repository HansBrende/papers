import NativeRelations.ZeroFreeHeadQWindow
import MergeDepth.SkeletonCones
import DirectedRecovery.StorageCode

/-!
# Two Long-Range Work Heads and Off-Carrier Expansion (Theorem H)

Defines vertex cuts (`IsMengerVertexCut`), proves the slab-chunk trapping inequality
(`frozenTrace_subpop_deficit_le`, `depStep_trapped_in_chunk`), and establishes Theorem H: part (c)
(`offCarrier_vertexExpansion_of_linearTimeTransposer`, `offCarrier_vertexExpansion_of_obliviousLinTime`),
and parts (a) (`oneFreeHead_smallExcursion_excludes`) and (b)
(`twoMacroscopicHeads_of_linearTimeTransposer`, `twoMacroscopicHeads_of_oblivious_linearTimeTransposer`,
and the counting forms `twoHeads_manyLongRevisits_of_linearTimeTransposer`,
`twoHeads_manyLongRevisits_of_oblivious_linearTimeTransposer`) as corollaries of (c); and Corollary 4.2
(`oneFreeHead_sublinearExcursion_excludes`, `atMostOneWorkTape_lowAdaptivity_excludes`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting SourceCovers
  MergeDepth MotionDepthCodes
open scoped BigOperators Topology

/-! ## §1. Explicit Constants of Theorem 4.1 (Theorem H) -/

/-- Maximum number of 1D spatial slab transitions `⌊160 β c²⌋` on the unrestricted work head. -/
noncomputable def slabWallCap (c β : ℝ) : ℕ :=
  ⌊160 * β * c ^ 2⌋₊

/-- Adaptivity / autonomy deficit exponent `ε_*(c, β) = 1 / (8 (N_wall(c, β) + 1)) > 0`. -/
noncomputable def slabAutonomyEps (c β : ℝ) : ℝ :=
  1 / (8 * ((slabWallCap c β : ℝ) + 1))

/-- Maximum hop-excursion fraction `ε_small(c, β, k) > 0` on the remaining `≤ k` work heads. -/
noncomputable def slabSmallExcursion (c β : ℝ) (k : ℕ) : ℝ :=
  slabAutonomyEps c β /
    (4 * β * ((slabWallCap c β : ℝ) + 2) * ((max 1 (2 * k) : ℕ) : ℝ))

/-- Explicit dimension threshold `d_H(c, β) = 160 (N_wall + 1) (N_wall + 2) = 20 (N_wall + 2) / ε_*` of
Theorem 4.1 (Theorem H). It does not depend on the number of work tapes. -/
noncomputable def slabDimThreshold (c β : ℝ) : ℕ :=
  160 * (slabWallCap c β + 1) * (slabWallCap c β + 2)

theorem slabAutonomyEps_pos (c β : ℝ) : 0 < slabAutonomyEps c β := by
  unfold slabAutonomyEps
  positivity

theorem ten_le_slabDimThreshold (c β : ℝ) : 10 ≤ slabDimThreshold c β := by
  unfold slabDimThreshold
  nlinarith [Nat.zero_le (slabWallCap c β)]

/-- `d_H = 20 (N_wall + 2) / ε_*`, the form in which the threshold enters the error budget. -/
theorem slabDimThreshold_cast_eq (c β : ℝ) :
    (slabDimThreshold c β : ℝ) = 20 * ((slabWallCap c β : ℝ) + 2) / slabAutonomyEps c β := by
  unfold slabDimThreshold slabAutonomyEps
  push_cast
  field_simp
  ring

/-- `80 β c ≤ d_H`, so the slab width `⌈L / (80 β c)⌉` is positive once `d ≥ d_H`. -/
theorem eighty_mul_le_slabDimThreshold {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) :
    80 * β * c ≤ (slabDimThreshold c β : ℝ) := by
  have hN : 160 * β * c ^ 2 < (slabWallCap c β : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN0 : (0 : ℝ) ≤ (slabWallCap c β : ℝ) := Nat.cast_nonneg _
  unfold slabDimThreshold
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 80 * β * c)]

theorem slabSmallExcursion_pos {c β : ℝ} (hβ : 0 < β) (k : ℕ) :
    0 < slabSmallExcursion c β k := by
  unfold slabSmallExcursion
  have h1 : 0 < slabAutonomyEps c β := slabAutonomyEps_pos c β
  have hmax : (0 : ℝ) < ((max 1 (2 * k) : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 (2 * k))
  positivity

/-! ## §2. Standalone Averaged-Offset Slab Grid and Contiguous Run Decomposition -/

/-- Spatial 1D slab index `⌊(z - u) / W⌋` at slab width `W` and integer offset `u`. -/
def slabIdx (W u : ℕ) (z : ℤ) : ℤ :=
  (z - (u : ℤ)) / (W : ℤ)

/-- Steps `t < T - 1` where `x` crosses a boundary of the `u`-shifted `W`-slab grid. -/
noncomputable def slabTransitions (x : ℕ → ℤ) (W T u : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (T - 1)).filter fun t => slabIdx W u (x t) ≠ slabIdx W u (x (t + 1))

private theorem int_ediv_mul_add_emod (a b : ℤ) : (a / b) * b + a % b = a := by
  rw [Int.emod_def]
  ring

private theorem sub_one_ediv_eq_of_emod_ne_zero {n w : ℤ} (hw : 0 < w) (hmod : n % w ≠ 0) :
    (n - 1) / w = n / w := by
  have hr0 : 0 ≤ n % w := Int.emod_nonneg n hw.ne'
  have hrw : n % w < w := Int.emod_lt_of_pos n hw
  have hr1 : 1 ≤ n % w := by omega
  have hdecomp : n - 1 = (n % w - 1) + (n / w) * w := by
    have hdiv := int_ediv_mul_add_emod n w
    linarith
  rw [hdecomp, Int.add_mul_ediv_right _ _ hw.ne',
    Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

/-- A unit step `|z₂ - z₁| ≤ 1` changes `slabIdx W u` for at most **one** offset `u ∈ [0, W)`. -/
theorem card_offset_transitions_step_le_one {W : ℕ} (hW : 1 ≤ W) {z₁ z₂ : ℤ}
    (hstep : |z₂ - z₁| ≤ 1) :
    ((Finset.range W).filter fun u => slabIdx W u z₁ ≠ slabIdx W u z₂).card ≤ 1 := by
  classical
  have hWz : (0 : ℤ) < (W : ℤ) := by exact_mod_cast hW
  obtain ⟨hlo, hhi⟩ := abs_le.mp hstep
  refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
  obtain ⟨hu₁W, hne₁⟩ := Finset.mem_filter.mp hu₁
  obtain ⟨hu₂W, hne₂⟩ := Finset.mem_filter.mp hu₂
  have hu₁_lt : u₁ < W := Finset.mem_range.mp hu₁W
  have hu₂_lt : u₂ < W := Finset.mem_range.mp hu₂W
  rcases (show z₂ = z₁ ∨ z₂ = z₁ + 1 ∨ z₁ = z₂ + 1 by omega) with rfl | hup | hdn
  · exact absurd rfl hne₁
  · have hm₁ : (z₂ - (u₁ : ℤ)) % (W : ℤ) = 0 := by
      by_contra hnz
      apply hne₁
      unfold slabIdx
      have hz : z₁ - (u₁ : ℤ) = (z₂ - (u₁ : ℤ)) - 1 := by omega
      rw [hz]
      exact sub_one_ediv_eq_of_emod_ne_zero hWz hnz
    have hm₂ : (z₂ - (u₂ : ℤ)) % (W : ℤ) = 0 := by
      by_contra hnz
      apply hne₂
      unfold slabIdx
      have hz : z₁ - (u₂ : ℤ) = (z₂ - (u₂ : ℤ)) - 1 := by omega
      rw [hz]
      exact sub_one_ediv_eq_of_emod_ne_zero hWz hnz
    have hd₁ := int_ediv_mul_add_emod (z₂ - (u₁ : ℤ)) (W : ℤ)
    have hd₂ := int_ediv_mul_add_emod (z₂ - (u₂ : ℤ)) (W : ℤ)
    rw [hm₁, add_zero] at hd₁
    rw [hm₂, add_zero] at hd₂
    set q₁ := (z₂ - (u₁ : ℤ)) / (W : ℤ)
    set q₂ := (z₂ - (u₂ : ℤ)) / (W : ℤ)
    have hdiff : (u₂ : ℤ) - (u₁ : ℤ) = (q₁ - q₂) * (W : ℤ) := by
      linarith [hd₁, hd₂]
    have hq_eq : q₁ = q₂ := by
      by_contra hq_ne
      rcases lt_or_gt_of_ne hq_ne with hlt | hgt
      · have : (q₁ - q₂) * (W : ℤ) ≤ -(W : ℤ) := by nlinarith
        omega
      · have : (W : ℤ) ≤ (q₁ - q₂) * (W : ℤ) := by nlinarith
        omega
    rw [hq_eq, sub_self, zero_mul] at hdiff
    omega
  · have hm₁ : (z₁ - (u₁ : ℤ)) % (W : ℤ) = 0 := by
      by_contra hnz
      apply hne₁
      unfold slabIdx
      have hz : z₂ - (u₁ : ℤ) = (z₁ - (u₁ : ℤ)) - 1 := by omega
      rw [hz]
      exact (sub_one_ediv_eq_of_emod_ne_zero hWz hnz).symm
    have hm₂ : (z₁ - (u₂ : ℤ)) % (W : ℤ) = 0 := by
      by_contra hnz
      apply hne₂
      unfold slabIdx
      have hz : z₂ - (u₂ : ℤ) = (z₁ - (u₂ : ℤ)) - 1 := by omega
      rw [hz]
      exact (sub_one_ediv_eq_of_emod_ne_zero hWz hnz).symm
    have hd₁ := int_ediv_mul_add_emod (z₁ - (u₁ : ℤ)) (W : ℤ)
    have hd₂ := int_ediv_mul_add_emod (z₁ - (u₂ : ℤ)) (W : ℤ)
    rw [hm₁, add_zero] at hd₁
    rw [hm₂, add_zero] at hd₂
    set q₁ := (z₁ - (u₁ : ℤ)) / (W : ℤ)
    set q₂ := (z₁ - (u₂ : ℤ)) / (W : ℤ)
    have hdiff : (u₂ : ℤ) - (u₁ : ℤ) = (q₁ - q₂) * (W : ℤ) := by
      linarith [hd₁, hd₂]
    have hq_eq : q₁ = q₂ := by
      by_contra hq_ne
      rcases lt_or_gt_of_ne hq_ne with hlt | hgt
      · have : (q₁ - q₂) * (W : ℤ) ≤ -(W : ℤ) := by nlinarith
        omega
      · have : (W : ℤ) ≤ (q₁ - q₂) * (W : ℤ) := by nlinarith
        omega
    rw [hq_eq, sub_self, zero_mul] at hdiff
    omega

/-- **Averaged-offset pigeonhole**: for every unit-step walk `x`, slab
width `W ≥ 1`, and horizon `T`, some offset `u < W` yields at most `(T - 1) / W` slab transitions. -/
theorem exists_offset_slabTransitions_le {x : ℕ → ℤ} (hx : IsWalk x) {W : ℕ} (hW : 1 ≤ W)
    (T : ℕ) :
    ∃ u < W, (slabTransitions x W T u).card ≤ (T - 1) / W := by
  classical
  have hsum : ∑ u ∈ Finset.range W, (slabTransitions x W T u).card ≤ T - 1 := by
    calc ∑ u ∈ Finset.range W, (slabTransitions x W T u).card
        = ∑ u ∈ Finset.range W, ∑ t ∈ Finset.range (T - 1),
            if slabIdx W u (x t) ≠ slabIdx W u (x (t + 1)) then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          unfold slabTransitions
          rw [Finset.card_filter]
      _ = ∑ t ∈ Finset.range (T - 1), ∑ u ∈ Finset.range W,
            if slabIdx W u (x t) ≠ slabIdx W u (x (t + 1)) then 1 else 0 := Finset.sum_comm
      _ = ∑ t ∈ Finset.range (T - 1),
            ((Finset.range W).filter fun u => slabIdx W u (x t) ≠ slabIdx W u (x (t + 1))).card := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
      _ ≤ ∑ _t ∈ Finset.range (T - 1), 1 :=
          Finset.sum_le_sum fun t _ => card_offset_transitions_step_le_one hW (hx t)
      _ = T - 1 := by simp
  by_contra hall
  push Not at hall
  have hlower : ∑ _u ∈ Finset.range W, ((T - 1) / W + 1) ≤
      ∑ u ∈ Finset.range W, (slabTransitions x W T u).card :=
    Finset.sum_le_sum fun u hu => hall u (Finset.mem_range.mp hu)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hlower
  have hdiv := Nat.div_add_mod (T - 1) W
  have hmod := Nat.mod_lt (T - 1) (by omega : 0 < W)
  nlinarith

/-- If `K` contains every `t < T - 1` where `m t ≠ m (t + 1)`, at most `K.card + 1` values of `m`
occur on `[0, T)`. -/
theorem card_activeSlabs_le {m : ℕ → ℤ} {T : ℕ} {K : Finset ℕ}
    (hK : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K) :
    ((Finset.range T).image m).card ≤ K.card + 1 := by
  classical
  have hmem : ∀ t < T, m t ∈ insert (m 0) (K.image fun s => m (s + 1)) := by
    intro t ht
    induction t with
    | zero => exact Finset.mem_insert_self _ _
    | succ t ih =>
      by_cases heq : m t = m (t + 1)
      · rw [← heq]
        exact ih (by omega)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t, hK t (by omega) heq, rfl⟩)
  have hsub : (Finset.range T).image m ⊆ insert (m 0) (K.image fun s => m (s + 1)) := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    exact hmem t (Finset.mem_range.mp ht)
  calc ((Finset.range T).image m).card
      ≤ (insert (m 0) (K.image fun s => m (s + 1))).card := Finset.card_le_card hsub
    _ ≤ (K.image fun s => m (s + 1)).card + 1 := Finset.card_insert_le _ _
    _ ≤ K.card + 1 := Nat.add_le_add_right Finset.card_image_le 1

/-- Left endpoints of maximal contiguous intervals of a finite timestamp set `C`. -/
def runStarts (C : Finset ℕ) : Finset ℕ :=
  C.filter fun a => a = 0 ∨ a - 1 ∉ C

/-- Exclusive right endpoint `min {s ∈ [a + 1, T] | s ∉ C}` of the maximal run starting at `a`. -/
def runEnd (C : Finset ℕ) (T a : ℕ) : ℕ :=
  if h : ((Finset.Icc (a + 1) T).filter (· ∉ C)).Nonempty then
    ((Finset.Icc (a + 1) T).filter (· ∉ C)).min' h
  else
    T

/-- Any slab chunk `C = {t ∈ [t_start, t_end) | m t = m_star}` (`t_end ≤ T`) has at most
`K.card + 1` maximal contiguous runs. -/
theorem card_runStarts_chunk_le {m : ℕ → ℤ} {T t_start t_end : ℕ} (hend : t_end ≤ T)
    {m_star : ℤ} {K : Finset ℕ} (hK : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K) :
    (runStarts ((Finset.Ico t_start t_end).filter (fun t => m t = m_star))).card ≤ K.card + 1 := by
  classical
  set C := (Finset.Ico t_start t_end).filter (fun t => m t = m_star)
  have hsub : runStarts C ⊆ insert t_start (K.image (· + 1)) := by
    intro a ha
    obtain ⟨haC, hstart⟩ := Finset.mem_filter.mp ha
    obtain ⟨haIco, hma⟩ := Finset.mem_filter.mp haC
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp haIco
    by_cases ha_eq : a = t_start
    · exact Finset.mem_insert.mpr (Or.inl ha_eq)
    · have ha_gt : t_start < a := by omega
      have ha1_not : a - 1 ∉ C := hstart.resolve_left (by omega)
      have ha1_ico : a - 1 ∈ Finset.Ico t_start t_end := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hne : m (a - 1) ≠ m a := by
        intro heq
        exact ha1_not (Finset.mem_filter.mpr ⟨ha1_ico, heq.trans hma⟩)
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a - 1, ?_, by omega⟩)
      apply hK (a - 1) (by omega)
      simpa [show a - 1 + 1 = a by omega] using hne
  calc (runStarts C).card
      ≤ (insert t_start (K.image (· + 1))).card := Finset.card_le_card hsub
    _ ≤ (K.image (· + 1)).card + 1 := Finset.card_insert_le _ _
    _ ≤ K.card + 1 := Nat.add_le_add_right Finset.card_image_le 1

theorem runEnd_spec {C : Finset ℕ} {T a : ℕ} (hCT : ∀ t ∈ C, t < T) (ha : a ∈ runStarts C) :
    a < runEnd C T a ∧ runEnd C T a ≤ T ∧ runEnd C T a ∉ C ∧
      ∀ t ∈ Finset.Ico a (runEnd C T a), t ∈ C := by
  have haC : a ∈ C := (Finset.mem_filter.mp ha).1
  have haT : a < T := hCT a haC
  have hT_not : T ∉ C := fun h => Nat.lt_irrefl T (hCT T h)
  have hne : ((Finset.Icc (a + 1) T).filter (· ∉ C)).Nonempty :=
    ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, hT_not⟩⟩
  have hdef : runEnd C T a = ((Finset.Icc (a + 1) T).filter (· ∉ C)).min' hne := by
    simp [runEnd, hne]
  have hmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem.1
  rw [← hdef] at hlo hhi hmem
  refine ⟨by omega, hhi, hmem.2, fun t ht => ?_⟩
  obtain ⟨hta, htb⟩ := Finset.mem_Ico.mp ht
  rcases eq_or_lt_of_le hta with rfl | hgt
  · exact haC
  · by_contra ht_not
    have ht_in : t ∈ (Finset.Icc (a + 1) T).filter (· ∉ C) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ht_not⟩
    have hmin_le : runEnd C T a ≤ t := by
      rw [hdef]
      exact Finset.min'_le _ t ht_in
    omega

theorem pairwiseDisjoint_runInterval {C : Finset ℕ} {T : ℕ} (hCT : ∀ t ∈ C, t < T) :
    (runStarts C : Set ℕ).PairwiseDisjoint fun a => Finset.Ico a (runEnd C T a) := by
  intro a₁ ha₁ a₂ ha₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  have ha₁' : a₁ ∈ runStarts C := Finset.mem_coe.mp ha₁
  have ha₂' : a₂ ∈ runStarts C := Finset.mem_coe.mp ha₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have ha₂_prev_not : a₂ - 1 ∉ C := (Finset.mem_filter.mp ha₂').2.resolve_left (by omega)
    have ha₁_in : a₁ ∈ C := (Finset.mem_filter.mp ha₁').1
    have ha₂_T : a₂ < T := hCT a₂ (Finset.mem_filter.mp ha₂').1
    have hne_prev : a₂ - 1 ≠ a₁ := fun h => ha₂_prev_not (h ▸ ha₁_in)
    have hne_set : ((Finset.Icc (a₁ + 1) T).filter (· ∉ C)).Nonempty :=
      ⟨a₂ - 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ha₂_prev_not⟩⟩
    have hb₁_le : runEnd C T a₁ ≤ a₂ - 1 := by
      simp only [runEnd, hne_set, ↓reduceDIte]
      exact Finset.min'_le _ (a₂ - 1)
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ha₂_prev_not⟩)
    obtain ⟨_, htb₁⟩ := Finset.mem_Ico.mp ht₁
    obtain ⟨ha₂t, _⟩ := Finset.mem_Ico.mp ht₂
    omega
  · have ha₁_prev_not : a₁ - 1 ∉ C := (Finset.mem_filter.mp ha₁').2.resolve_left (by omega)
    have ha₂_in : a₂ ∈ C := (Finset.mem_filter.mp ha₂').1
    have ha₁_T : a₁ < T := hCT a₁ (Finset.mem_filter.mp ha₁').1
    have hne_prev : a₁ - 1 ≠ a₂ := fun h => ha₁_prev_not (h ▸ ha₂_in)
    have hne_set : ((Finset.Icc (a₂ + 1) T).filter (· ∉ C)).Nonempty :=
      ⟨a₁ - 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ha₁_prev_not⟩⟩
    have hb₂_le : runEnd C T a₂ ≤ a₁ - 1 := by
      simp only [runEnd, hne_set, ↓reduceDIte]
      exact Finset.min'_le _ (a₁ - 1)
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ha₁_prev_not⟩)
    obtain ⟨ha₁t, _⟩ := Finset.mem_Ico.mp ht₁
    obtain ⟨_, htb₂⟩ := Finset.mem_Ico.mp ht₂
    omega

/-- Every `C ⊆ [0, T)` equals the disjoint union over `a ∈ runStarts C` of `[a, runEnd C T a)`. -/
theorem eq_biUnion_runInterval {C : Finset ℕ} {T : ℕ} (hCT : ∀ t ∈ C, t < T) :
    C = (runStarts C).biUnion fun a => Finset.Ico a (runEnd C T a) := by
  ext t
  constructor
  · intro htC
    have hex_le : ∃ a ∈ runStarts C, a ≤ t := by
      induction t using Nat.strong_induction_on with
      | _ s ih =>
        by_cases hstart : s = 0 ∨ s - 1 ∉ C
        · exact ⟨s, Finset.mem_filter.mpr ⟨htC, hstart⟩, le_rfl⟩
        · push Not at hstart
          obtain ⟨a, ha, has⟩ := ih (s - 1) (by omega) hstart.2
          exact ⟨a, ha, has.trans (by omega)⟩
    set A := (runStarts C).filter (· ≤ t)
    have hAne : A.Nonempty := by
      obtain ⟨a, ha, hat⟩ := hex_le
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, hat⟩⟩
    set a := A.max' hAne
    have ha_mem := Finset.mem_filter.mp (Finset.max'_mem A hAne)
    have ha_start : a ∈ runStarts C := ha_mem.1
    have hat : a ≤ t := ha_mem.2
    refine Finset.mem_biUnion.mpr ⟨a, ha_start, Finset.mem_Ico.mpr ⟨hat, ?_⟩⟩
    by_contra hge
    push Not at hge
    have hb_spec := runEnd_spec hCT ha_start
    have hb_lt_t : runEnd C T a < t := lt_of_le_of_ne hge fun heq => hb_spec.2.2.1 (heq ▸ htC)
    set B := (Finset.Icc (runEnd C T a + 1) t).filter (· ∈ C)
    have hBne : B.Nonempty :=
      ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, htC⟩⟩
    set a' := B.min' hBne
    have ha'_mem := Finset.mem_filter.mp (Finset.min'_mem B hBne)
    obtain ⟨ha'_lo, ha'_hi⟩ := Finset.mem_Icc.mp ha'_mem.1
    have ha'_prev_not : a' - 1 ∉ C := by
      rcases eq_or_lt_of_le ha'_lo with heq | hgt
      · have : a' - 1 = runEnd C T a := by omega
        rw [this]
        exact hb_spec.2.2.1
      · intro hprevC
        have hprevB : a' - 1 ∈ B :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hprevC⟩
        have := Finset.min'_le B (a' - 1) hprevB
        omega
    have ha'_start : a' ∈ runStarts C :=
      Finset.mem_filter.mpr ⟨ha'_mem.2, Or.inr ha'_prev_not⟩
    have ha'_le_a : a' ≤ a := Finset.le_max' A a' (Finset.mem_filter.mpr ⟨ha'_start, ha'_hi⟩)
    omega
  · intro ht
    obtain ⟨a, ha, htIco⟩ := Finset.mem_biUnion.mp ht
    exact (runEnd_spec hCT ha).2.2.2 t htIco

/-! ## §3. Standalone Short-vs-Long Slab Chunk Dichotomy -/

/-- Output indices `r : Fin L` whose append time `ot r` falls in `S`. -/
def outIn {L : ℕ} (ot : Fin L → ℕ) (S : Finset ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun r => ot r ∈ S

/-- Timestamps in `[0, T)` belonging to slab `m₀`. -/
def slabSteps (m : ℕ → ℤ) (T : ℕ) (m₀ : ℤ) : Finset ℕ :=
  (Finset.range T).filter fun t => m t = m₀

/-- Chronological partitioning of a single long slab `S ⊆ range T` (`H < S.card`, `1 ≤ H`) into
`q_cnt = (S.card + H - 1) / H` half-open time slices `S ∩ [t_lo, t_hi)` of size `≤ H`, with
`q_cnt * H ≤ 2 * S.card`. -/
theorem long_slab_chunks {m : ℕ → ℤ} {T H : ℕ} (hH : 1 ≤ H) (m₀ : ℤ)
    (hlong : H < (slabSteps m T m₀).card) {L : ℕ} (ot : Fin L → ℕ) :
    let S := slabSteps m T m₀
    let q_cnt := (S.card + H - 1) / H
    q_cnt * H ≤ 2 * S.card ∧
      ∃ t_lo t_hi : ℕ → ℕ,
        (∀ q < q_cnt, t_lo q ≤ t_hi q ∧ t_hi q ≤ T ∧
          ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀)).card ≤ H) ∧
        (outIn ot S).card ≤
          ∑ q ∈ Finset.range q_cnt,
            (outIn ot ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀))).card := by
  classical
  set S := slabSteps m T m₀
  set n := S.card
  set q_cnt := (n + H - 1) / H
  have hmul_le : q_cnt * H ≤ 2 * n := by
    have h1 := Nat.div_mul_le_self (n + H - 1) H
    change q_cnt * H ≤ n + H - 1 at h1
    omega
  refine ⟨hmul_le, ?_⟩
  let emb := S.orderEmbOfFin rfl
  have hq_lt_n : ∀ {q : ℕ}, q < q_cnt → q * H < n := by
    intro q hq
    by_contra hge
    push Not at hge
    have h1 : n + H - 1 < (q + 1) * H := by
      calc n + H - 1 ≤ q * H + H - 1 := by omega
        _ < q * H + H := by omega
        _ = (q + 1) * H := by ring
    have h2 : q_cnt ≤ q := by
      dsimp [q_cnt]
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega : 0 < H)).mpr h1)
    omega
  let t_lo : ℕ → ℕ := fun q => if h : q * H < n then emb ⟨q * H, h⟩ else T
  let t_hi : ℕ → ℕ := fun q => if h : (q + 1) * H < n then emb ⟨(q + 1) * H, h⟩ else T
  have hemb_lt_T : ∀ i : Fin n, emb i < T := fun i =>
    Finset.mem_range.mp (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem S rfl i)).1
  have hchunk_sub : ∀ q < q_cnt,
      (Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀) ⊆
        ((Finset.Ico (q * H) ((q + 1) * H)).attach.image fun j =>
          if hj : j.1 < n then emb ⟨j.1, hj⟩ else 0) := by
    intro q hq t ht
    obtain ⟨htIco, hmt⟩ := Finset.mem_filter.mp ht
    obtain ⟨hlo_t, hhi_t⟩ := Finset.mem_Ico.mp htIco
    have hqn : q * H < n := hq_lt_n hq
    have htT : t < T := by
      dsimp [t_hi] at hhi_t
      split_ifs at hhi_t with h1
      · exact hhi_t.trans (hemb_lt_T ⟨(q + 1) * H, h1⟩)
      · exact hhi_t
    have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htT, hmt⟩
    have hrange : t ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact htS
    obtain ⟨i, rfl⟩ := hrange
    have hi_lo : q * H ≤ i.1 := by
      dsimp [t_lo] at hlo_t
      rw [dite_eq_left hqn] at hlo_t
      exact emb.le_iff_le.mp hlo_t
    have hi_hi : i.1 < (q + 1) * H := by
      dsimp [t_hi] at hhi_t
      split_ifs at hhi_t with h1
      · exact emb.lt_iff_lt.mp hhi_t
      · omega
    have hi_mem : i.1 ∈ Finset.Ico (q * H) ((q + 1) * H) := Finset.mem_Ico.mpr ⟨hi_lo, hi_hi⟩
    have hin : i.1 < n := i.2
    refine Finset.mem_image.mpr ⟨⟨i.1, hi_mem⟩, Finset.mem_attach _ _, ?_⟩
    simp [hin]
  refine ⟨t_lo, t_hi, fun q hq => ?_, ?_⟩
  · have hqn : q * H < n := hq_lt_n hq
    refine ⟨?_, ?_, ?_⟩
    · dsimp [t_lo, t_hi]
      rw [dite_eq_left hqn]
      split_ifs with h1
      · exact emb.monotone (Fin.mk_le_mk.mpr (by nlinarith))
      · exact (hemb_lt_T ⟨q * H, hqn⟩).le
    · dsimp [t_hi]
      split_ifs with h1
      · exact (hemb_lt_T ⟨(q + 1) * H, h1⟩).le
      · exact le_rfl
    · calc ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀)).card
          ≤ (((Finset.Ico (q * H) ((q + 1) * H)).attach.image fun j =>
              if hj : j.1 < n then emb ⟨j.1, hj⟩ else 0)).card :=
            Finset.card_le_card (hchunk_sub q hq)
        _ ≤ (Finset.Ico (q * H) ((q + 1) * H)).attach.card := Finset.card_image_le
        _ = (Finset.Ico (q * H) ((q + 1) * H)).card := Finset.card_attach
        _ = H := by rw [Nat.card_Ico]; ring_nf; omega
  · have hcov : outIn ot S ⊆ (Finset.range q_cnt).biUnion fun q =>
        outIn ot ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀)) := by
      intro r hr
      have hotS : ot r ∈ S := (Finset.mem_filter.mp hr).2
      have hmt : m (ot r) = m₀ := (Finset.mem_filter.mp hotS).2
      have hrange : ot r ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]
        exact hotS
      obtain ⟨i, hi_eq⟩ := hrange
      set q := i.1 / H
      have hq_lt : q < q_cnt := by
        have hin : i.1 < n := i.2
        have hdiv : q * H ≤ i.1 := Nat.div_mul_le_self i.1 H
        have hmul : (q + 1) * H ≤ n + H - 1 := by
          calc (q + 1) * H = q * H + H := by ring
            _ ≤ i.1 + H := Nat.add_le_add_right hdiv H
            _ ≤ n + H - 1 := by omega
        have hle : q + 1 ≤ q_cnt := (Nat.le_div_iff_mul_le (by omega : 0 < H)).mpr hmul
        omega
      have hqn : q * H < n := hq_lt_n hq_lt
      have hq_lo : q * H ≤ i.1 := by
        dsimp [q]
        exact Nat.div_mul_le_self i.1 H
      have hq_hi : i.1 < (q + 1) * H := by
        dsimp [q]
        have hdiv := Nat.div_add_mod i.1 H
        have hmod := Nat.mod_lt i.1 (by omega : 0 < H)
        nlinarith
      refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_range.mpr hq_lt, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, hmt⟩⟩
      rw [← hi_eq]
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · dsimp [t_lo]
        rw [dite_eq_left hqn]
        exact emb.monotone hq_lo
      · dsimp [t_hi]
        split_ifs with h1
        · exact emb.strictMono hq_hi
        · exact hemb_lt_T i
    exact (Finset.card_le_card hcov).trans Finset.card_biUnion_le

/-- **Short-vs-Long Slab Dichotomy**:
either a short slab (`|T_{m_*}| ≤ L / 2`, `t_start = 0`, `t_end = T`) captures at least
`L / (2 (|K| + 1))` outputs, or a half-open slice `T_{m_*} ∩ [t_start, t_end)` of size `≤ L / 2`
satisfies `L * (L / 2) < 4 * T * |O(C_*)|`. -/
theorem exists_slab_chunk_dichotomy {L T : ℕ} (hL : 2 ≤ L) {m : ℕ → ℤ} {K : Finset ℕ}
    (hK : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K) {ot : Fin L → ℕ} (hot : ∀ r, ot r < T) :
    (∃ m_star : ℤ,
      ((Finset.Ico 0 T).filter (fun t => m t = m_star)).card ≤ L / 2 ∧
      L ≤ 2 * (K.card + 1) *
        (outIn ot ((Finset.Ico 0 T).filter (fun t => m t = m_star))).card) ∨
    (∃ (m_star : ℤ) (t_start t_end : ℕ),
      t_start ≤ t_end ∧ t_end ≤ T ∧
      ((Finset.Ico t_start t_end).filter (fun t => m t = m_star)).card ≤ L / 2 ∧
      L * (L / 2) < 4 * T *
        (outIn ot ((Finset.Ico t_start t_end).filter (fun t => m t = m_star))).card) := by
  classical
  set M_act := (Finset.range T).image m
  have hM_card : M_act.card ≤ K.card + 1 := card_activeSlabs_le hK
  have hcov_all : (Finset.univ : Finset (Fin L)) ⊆
      M_act.biUnion fun m₀ => outIn ot (slabSteps m T m₀) := by
    intro r _
    have hrT : ot r < T := hot r
    refine Finset.mem_biUnion.mpr ⟨m (ot r), Finset.mem_image_of_mem m (Finset.mem_range.mpr hrT), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrT, rfl⟩⟩
  have hsum_all : L ≤ ∑ m₀ ∈ M_act, (outIn ot (slabSteps m T m₀)).card := by
    calc L = (Finset.univ : Finset (Fin L)).card := by simp
      _ ≤ (M_act.biUnion fun m₀ => outIn ot (slabSteps m T m₀)).card := Finset.card_le_card hcov_all
      _ ≤ ∑ m₀ ∈ M_act, (outIn ot (slabSteps m T m₀)).card := Finset.card_biUnion_le
  set H := L / 2
  have hH_pos : 1 ≤ H := by dsimp [H]; omega
  set M_short := M_act.filter fun m₀ => (slabSteps m T m₀).card ≤ H
  set M_long := M_act.filter fun m₀ => ¬ (slabSteps m T m₀).card ≤ H
  have hsplit := Finset.sum_filter_add_sum_filter_not M_act
    (fun m₀ => (slabSteps m T m₀).card ≤ H)
    (fun m₀ => (outIn ot (slabSteps m T m₀)).card)
  change (∑ m₀ ∈ M_short, (outIn ot (slabSteps m T m₀)).card) +
      (∑ m₀ ∈ M_long, (outIn ot (slabSteps m T m₀)).card) =
      ∑ m₀ ∈ M_act, (outIn ot (slabSteps m T m₀)).card at hsplit
  by_cases hcaseA : L ≤ 2 * ∑ m₀ ∈ M_short, (outIn ot (slabSteps m T m₀)).card
  · left
    have hMs_le : M_short.card ≤ K.card + 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans hM_card
    by_contra hnone
    push Not at hnone
    have hico_eq : ∀ m₀ : ℤ, (Finset.Ico 0 T).filter (fun t => m t = m₀) = slabSteps m T m₀ := by
      intro m₀
      ext t
      simp [slabSteps]
    have hlt_each : ∀ m₀ ∈ M_short,
        2 * (K.card + 1) * (outIn ot (slabSteps m T m₀)).card ≤ L - 1 := by
      intro m₀ hm₀
      have hsh : (slabSteps m T m₀).card ≤ H := (Finset.mem_filter.mp hm₀).2
      have hlt := hnone m₀ (by rwa [hico_eq])
      rw [hico_eq] at hlt
      omega
    have h1 : (K.card + 1) * L ≤
        ∑ m₀ ∈ M_short, 2 * (K.card + 1) * (outIn ot (slabSteps m T m₀)).card := by
      calc (K.card + 1) * L
          ≤ (K.card + 1) * (2 * ∑ m₀ ∈ M_short, (outIn ot (slabSteps m T m₀)).card) :=
            Nat.mul_le_mul_left _ hcaseA
        _ = ∑ m₀ ∈ M_short, 2 * (K.card + 1) * (outIn ot (slabSteps m T m₀)).card := by
            rw [← mul_assoc, mul_comm (K.card + 1) 2, Finset.mul_sum]
    have h2 : ∑ m₀ ∈ M_short, 2 * (K.card + 1) * (outIn ot (slabSteps m T m₀)).card ≤
        M_short.card * (L - 1) := by
      calc ∑ m₀ ∈ M_short, 2 * (K.card + 1) * (outIn ot (slabSteps m T m₀)).card
          ≤ ∑ _m₀ ∈ M_short, (L - 1) := Finset.sum_le_sum hlt_each
        _ = M_short.card * (L - 1) := by simp
    have h3 : M_short.card * (L - 1) ≤ (K.card + 1) * (L - 1) :=
      Nat.mul_le_mul_right _ hMs_le
    have hcomb : (K.card + 1) * L ≤ (K.card + 1) * (L - 1) := h1.trans (h2.trans h3)
    have hL_le : L ≤ L - 1 := Nat.le_of_mul_le_mul_left hcomb (Nat.succ_pos K.card)
    omega
  · right
    have hcaseB : L < 2 * ∑ m₀ ∈ M_long, (outIn ot (slabSteps m T m₀)).card := by omega
    have hlong_gt : ∀ m₀ ∈ M_long, H < (slabSteps m T m₀).card := by
      intro m₀ hm₀
      have := (Finset.mem_filter.mp hm₀).2
      omega
    let q_cnt : ℤ → ℕ := fun m₀ => ((slabSteps m T m₀).card + H - 1) / H
    have hex_chunks : ∀ m₀ : ℤ, m₀ ∈ M_long →
        q_cnt m₀ * H ≤ 2 * (slabSteps m T m₀).card ∧
          ∃ t_lo t_hi : ℕ → ℕ,
            (∀ q < q_cnt m₀, t_lo q ≤ t_hi q ∧ t_hi q ≤ T ∧
              ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀)).card ≤ H) ∧
            (outIn ot (slabSteps m T m₀)).card ≤
              ∑ q ∈ Finset.range (q_cnt m₀),
                (outIn ot ((Finset.Ico (t_lo q) (t_hi q)).filter (fun t => m t = m₀))).card :=
      fun m₀ hm₀ => long_slab_chunks hH_pos m₀ (hlong_gt m₀ hm₀) ot
    -- Bound total chunks `Q_long * H ≤ 2 * T`.
    set Q_long := ∑ m₀ ∈ M_long, q_cnt m₀
    have hdisj_slabs : (M_long : Set ℤ).PairwiseDisjoint (slabSteps m T) := by
      intro m₁ _ m₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro t ht₁ ht₂
      exact hne ((Finset.mem_filter.mp ht₁).2.symm.trans (Finset.mem_filter.mp ht₂).2)
    have hsum_slabs_le_T : ∑ m₀ ∈ M_long, (slabSteps m T m₀).card ≤ T := by
      rw [← Finset.card_biUnion hdisj_slabs]
      calc (M_long.biUnion (slabSteps m T)).card
          ≤ (Finset.range T).card := Finset.card_le_card fun t ht => by
              obtain ⟨m₀, _, htS⟩ := Finset.mem_biUnion.mp ht
              exact (Finset.mem_filter.mp htS).1
        _ = T := Finset.card_range T
    have hQ_mul_H : Q_long * H ≤ 2 * T := by
      calc Q_long * H
          = ∑ m₀ ∈ M_long, q_cnt m₀ * H := Finset.sum_mul _ _ _
        _ ≤ ∑ m₀ ∈ M_long, 2 * (slabSteps m T m₀).card :=
            Finset.sum_le_sum fun m₀ hm₀ => (hex_chunks m₀ hm₀).1
        _ = 2 * ∑ m₀ ∈ M_long, (slabSteps m T m₀).card := (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * T := Nat.mul_le_mul_left 2 hsum_slabs_le_T
    -- Pick a chunk `(m_star, q_star)` with `L < 2 * Q_long * |O(C_*)|`.
    let t_lo_of : ℤ → ℕ → ℕ := fun m₀ =>
      if hm₀ : m₀ ∈ M_long then Classical.choose (hex_chunks m₀ hm₀).2 else fun _ => 0
    let t_hi_of : ℤ → ℕ → ℕ := fun m₀ =>
      if hm₀ : m₀ ∈ M_long then
        Classical.choose (Classical.choose_spec (hex_chunks m₀ hm₀).2)
      else fun _ => 0
    have ht_spec : ∀ m₀ ∈ M_long,
        (∀ q < q_cnt m₀, t_lo_of m₀ q ≤ t_hi_of m₀ q ∧ t_hi_of m₀ q ≤ T ∧
          ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter (fun t => m t = m₀)).card ≤ H) ∧
        (outIn ot (slabSteps m T m₀)).card ≤
          ∑ q ∈ Finset.range (q_cnt m₀),
            (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
              (fun t => m t = m₀))).card := by
      intro m₀ hm₀
      have hsp := Classical.choose_spec (Classical.choose_spec (hex_chunks m₀ hm₀).2)
      simpa only [t_lo_of, t_hi_of, hm₀, ↓reduceDIte] using hsp
    have hL_lt_double : L < 2 * ∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
        (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
          (fun t => m t = m₀))).card :=
      hcaseB.trans_le (Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun m₀ hm₀ => (ht_spec m₀ hm₀).2))
    have hQ_pos : 0 < Q_long := by
      by_contra hQ0
      have hQ_eq0 : Q_long = 0 := by omega
      have hall0 : ∀ m₀ ∈ M_long, q_cnt m₀ = 0 :=
        (Finset.sum_eq_zero_iff.mp hQ_eq0)
      have hsum0 : (∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
          (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
            (fun t => m t = m₀))).card) = 0 := by
        refine Finset.sum_eq_zero fun m₀ hm₀ => ?_
        rw [hall0 m₀ hm₀, Finset.range_zero, Finset.sum_empty]
      rw [hsum0] at hL_lt_double
      omega
    have hex_good : ∃ m₀ ∈ M_long, ∃ q < q_cnt m₀,
        L < 2 * Q_long *
          (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
            (fun t => m t = m₀))).card := by
      by_contra hall_le
      push Not at hall_le
      have h1 : Q_long * L < ∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
          2 * Q_long *
            (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
              (fun t => m t = m₀))).card := by
        calc Q_long * L
            < Q_long * (2 * ∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
                (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
                  (fun t => m t = m₀))).card) :=
              Nat.mul_lt_mul_of_pos_left hL_lt_double hQ_pos
          _ = ∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
                2 * Q_long *
                  (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
                    (fun t => m t = m₀))).card := by
              rw [← mul_assoc, mul_comm Q_long 2, Finset.mul_sum]
              refine Finset.sum_congr rfl fun _ _ => ?_
              rw [Finset.mul_sum]
      have h2 : (∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
          2 * Q_long *
            (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
              (fun t => m t = m₀))).card) ≤ Q_long * L := by
        calc (∑ m₀ ∈ M_long, ∑ q ∈ Finset.range (q_cnt m₀),
              2 * Q_long *
                (outIn ot ((Finset.Ico (t_lo_of m₀ q) (t_hi_of m₀ q)).filter
                  (fun t => m t = m₀))).card)
            ≤ ∑ m₀ ∈ M_long, ∑ _q ∈ Finset.range (q_cnt m₀), L :=
              Finset.sum_le_sum fun m₀ hm₀ =>
                Finset.sum_le_sum fun q hq => hall_le m₀ hm₀ q (Finset.mem_range.mp hq)
          _ = ∑ m₀ ∈ M_long, q_cnt m₀ * L := by simp
          _ = Q_long * L := (Finset.sum_mul _ _ _).symm
      omega
    obtain ⟨m_star, hm_star, q_star, hq_star, hgt_out⟩ := hex_good
    obtain ⟨hlo_hi, hhi_T, hcard_H⟩ := (ht_spec m_star hm_star).1 q_star hq_star
    refine ⟨m_star, t_lo_of m_star q_star, t_hi_of m_star q_star, hlo_hi, hhi_T, hcard_H, ?_⟩
    set C_card := (outIn ot ((Finset.Ico (t_lo_of m_star q_star) (t_hi_of m_star q_star)).filter
      (fun t => m t = m_star))).card
    calc L * H < (2 * Q_long * C_card) * H := Nat.mul_lt_mul_of_pos_right hgt_out hH_pos
      _ = 2 * (Q_long * H) * C_card := by ring
      _ ≤ 2 * (2 * T) * C_card :=
          Nat.mul_le_mul_right C_card (Nat.mul_le_mul_left 2 hQ_mul_H)
      _ = 4 * T * C_card := by ring

/-! ## §4. Slab-Chunk Genie and `DepDag` Cone Trapping -/

/-- Lower endpoints `p ≤ θ` of long hops `(p, u)` of `y` before `T` that strictly pass `θ`
(`θ < u < T`). -/
noncomputable def crossingLowers (y : ℕ → ℤ) (T θ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter fun p => p ≤ θ ∧ ∃ u, θ < u ∧ IsHop y T p u

/-- Cells `[u + m_* W, u + (m_* + 1) W) ∩ ℤ` belonging to 1D slab `m_*`. -/
def slabCells (W u_off : ℕ) (m_star : ℤ) : Finset ℤ :=
  (Finset.range W).image fun r : ℕ => (u_off : ℤ) + m_star * (W : ℤ) + (r : ℤ)

theorem mem_slabCells_of_slabIdx_eq {W u_off : ℕ} (hW : 1 ≤ W) {z m_star : ℤ}
    (hm : slabIdx W u_off z = m_star) :
    z ∈ slabCells W u_off m_star := by
  have hWz : (0 : ℤ) < (W : ℤ) := by exact_mod_cast hW
  unfold slabIdx at hm
  have hdiv := int_ediv_mul_add_emod (z - (u_off : ℤ)) (W : ℤ)
  rw [hm] at hdiv
  have hr0 : 0 ≤ (z - (u_off : ℤ)) % (W : ℤ) := Int.emod_nonneg _ hWz.ne'
  have hrW : (z - (u_off : ℤ)) % (W : ℤ) < (W : ℤ) := Int.emod_lt_of_pos _ hWz
  refine Finset.mem_image.mpr ⟨((z - (u_off : ℤ)) % (W : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
  linarith [Int.toNat_of_nonneg hr0, hdiv]

/-- Last-visit timestamps `< t_start` of `x_free` to each cell of `slabCells W u_off m_star`
(automatically `∅` when `t_start = 0`). -/
noncomputable def slabEntryGenie (x_free : ℕ → ℤ) (W u_off : ℕ) (m_star : ℤ) (t_start : ℕ) :
    Finset ℕ := by
  classical
  exact (slabCells W u_off m_star).biUnion fun z =>
    if h : ((Finset.range t_start).filter fun s => x_free s = z).Nonempty then
      {((Finset.range t_start).filter fun s => x_free s = z).max' h}
    else
      ∅

theorem slabEntryGenie_zero (x_free : ℕ → ℤ) (W u_off : ℕ) (m_star : ℤ) :
    slabEntryGenie x_free W u_off m_star 0 = ∅ := by
  classical
  ext t
  simp [slabEntryGenie]

theorem card_slabEntryGenie_le (x_free : ℕ → ℤ) (W u_off : ℕ) (m_star : ℤ) (t_start : ℕ) :
    (slabEntryGenie x_free W u_off m_star t_start).card ≤ W := by
  classical
  unfold slabEntryGenie
  calc ((slabCells W u_off m_star).biUnion _).card
      ≤ ∑ z ∈ slabCells W u_off m_star,
          (if h : ((Finset.range t_start).filter fun s => x_free s = z).Nonempty then
            ({((Finset.range t_start).filter fun s => x_free s = z).max' h} : Finset ℕ)
          else ∅).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ slabCells W u_off m_star, 1 := by
        refine Finset.sum_le_sum fun z _ => ?_
        split_ifs <;> simp
    _ = (slabCells W u_off m_star).card := by simp
    _ ≤ (Finset.range W).card := Finset.card_image_le
    _ = W := Finset.card_range W

/-- Complete whole-step genie `Γ_* = K_all ∪ Γ_cross ∪ Γ_slab` for Theorem 4.1 (Theorem H). -/
noncomputable def slabChunkGenie {k : ℕ} (xs : Fin k → ℕ → ℤ) (S_free : Finset (Fin k))
    (x_free : ℕ → ℤ) (W u_off T t_start : ℕ) (m_star : ℤ) : Finset ℕ := by
  classical
  let K := slabTransitions x_free W T u_off
  let K_all := if t_start = 0 then K else insert (t_start - 1) K
  let Γ_cross := (Finset.univ \ S_free).biUnion fun j =>
    K_all.biUnion fun θ => crossingLowers (xs j) T θ
  let Γ_slab := slabEntryGenie x_free W u_off m_star t_start
  exact K_all ∪ Γ_cross ∪ Γ_slab

private theorem exists_transition_between {m : ℕ → ℤ} {b a : ℕ} (hba : b < a) (hne : m b ≠ m a) :
    ∃ θ, b ≤ θ ∧ θ < a ∧ m θ ≠ m (θ + 1) := by
  by_contra hnone
  push Not at hnone
  have hconst : ∀ n, b + n ≤ a → m (b + n) = m b := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := ih (by omega)
      have h2 := hnone (b + n) (by omega) (by omega)
      rw [show b + (n + 1) = b + n + 1 by omega, ← h2, h1]
  have := hconst (a - b) (by omega)
  rw [show b + (a - b) = a by omega] at this
  exact hne this.symm

/-- **Single-edge cone trapping**:
every backward `DepStep xs T a b` from `a ∈ C_*` whose target `b` avoids `slabChunkGenie` remains
inside `C_*`. -/
theorem depStep_trapped_in_chunk {k : ℕ} {xs : Fin k → ℕ → ℤ} {S_free : Finset (Fin k)}
    {x_free : ℕ → ℤ} (hfree_eq : ∀ i ∈ S_free, xs i = x_free) {W u_off T t_start t_end : ℕ}
    (hW : 1 ≤ W) (hend : t_end ≤ T) {m_star : ℤ} {a b : ℕ}
    (ha : a ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star))
    (hstep : DepStep xs T a b)
    (hb_not : b ∉ slabChunkGenie xs S_free x_free W u_off T t_start m_star) :
    b ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star) := by
  classical
  set m : ℕ → ℤ := fun t => slabIdx W u_off (x_free t)
  set K := slabTransitions x_free W T u_off
  set K_all := if t_start = 0 then K else insert (t_start - 1) K
  set Γ_cross := (Finset.univ \ S_free).biUnion fun j =>
    K_all.biUnion fun θ => crossingLowers (xs j) T θ
  set Γ_slab := slabEntryGenie x_free W u_off m_star t_start
  have hb_not_Kall : b ∉ K_all := fun h =>
    hb_not (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hb_not_cross : b ∉ Γ_cross := fun h =>
    hb_not (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hb_not_slab : b ∉ Γ_slab := fun h =>
    hb_not (Finset.mem_union_right _ h)
  obtain ⟨haIco, hma⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha_lo, ha_hi⟩ := Finset.mem_Ico.mp haIco
  have hba : b < a := (depStep_lt hstep).1
  rcases hstep with ⟨hpred, haT⟩ | hhop_mem
  · -- State edge `b + 1 = a`.
    have hb_lo : t_start ≤ b := by
      by_contra hlt
      have hts_pos : t_start ≠ 0 := by omega
      have hb_eq : b = t_start - 1 := by omega
      apply hb_not_Kall
      simp [K_all, hts_pos, hb_eq]
    have hmb : m b = m_star := by
      by_contra hne
      have hbK : b ∈ K := by
        unfold K slabTransitions
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
        rw [hpred]
        exact fun h => hne (h.trans hma)
      apply hb_not_Kall
      dsimp [K_all]
      split_ifs
      · exact hbK
      · exact Finset.mem_insert_of_mem hbK
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hb_lo, by omega⟩, hmb⟩
  · -- Long hop `(b, a)` on some head `j : Fin k`.
    obtain ⟨⟨j, b', a'⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hb', ha'⟩ := heq
    rw [hb', ha'] at hη
    have hhop : IsHop (xs j) T b a := mem_allHops.mp hη
    by_cases hj : j ∈ S_free
    · -- Free-head hop: `xs j = x_free`, so `x_free b = x_free a`, hence `m b = m_star`.
      rw [hfree_eq j hj] at hhop
      have hxb_eq : x_free b = x_free a := hhop.2.2.1.symm
      have hmb : m b = m_star := by
        dsimp [m]
        rw [hxb_eq]
        exact hma
      have hb_lo : t_start ≤ b := by
        by_contra hlt
        push Not at hlt
        let z := x_free a
        have hz_mem : z ∈ slabCells W u_off m_star :=
          mem_slabCells_of_slabIdx_eq hW (show slabIdx W u_off z = m_star from hma)
        set S_z := (Finset.range t_start).filter fun s => x_free s = z
        have hb_Sz : b ∈ S_z :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hxb_eq⟩
        have hSne : S_z.Nonempty := ⟨b, hb_Sz⟩
        have hb_le_max : b ≤ S_z.max' hSne := Finset.le_max' S_z b hb_Sz
        have hmax_mem := Finset.mem_filter.mp (Finset.max'_mem S_z hSne)
        have hmax_lt : S_z.max' hSne < t_start := Finset.mem_range.mp hmax_mem.1
        have hb_eq_max : b = S_z.max' hSne := by
          rcases eq_or_lt_of_le hb_le_max with heq | hgt
          · exact heq
          · exfalso
            exact hhop.2.2.2 (S_z.max' hSne) (Finset.mem_Ioo.mpr ⟨hgt, hmax_lt.trans_le ha_lo⟩)
              (by have := hmax_mem.2; omega)
        apply hb_not_slab
        unfold Γ_slab slabEntryGenie
        refine Finset.mem_biUnion.mpr ⟨z, hz_mem, ?_⟩
        simp only [S_z, hSne, ↓reduceDIte, Finset.mem_singleton]
        exact hb_eq_max
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hb_lo, by omega⟩, hmb⟩
    · -- Bounded-head hop `j ∉ S_free`.
      by_contra hb_out
      have hj_sdiff : j ∈ Finset.univ \ S_free :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
      by_cases hlt : b < t_start
      · have hts_pos : t_start ≠ 0 := by omega
        have hθ_mem : t_start - 1 ∈ K_all := by simp [K_all, hts_pos]
        have hb_cr : b ∈ crossingLowers (xs j) T (t_start - 1) := by
          unfold crossingLowers
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (hba.trans hhop.2.1), by omega, a, by omega, hhop⟩
        exact hb_not_cross (Finset.mem_biUnion.mpr ⟨j, hj_sdiff,
          Finset.mem_biUnion.mpr ⟨t_start - 1, hθ_mem, hb_cr⟩⟩)
      · have hb_ico : b ∈ Finset.Ico t_start t_end := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        have hmb_ne : m b ≠ m a := by
          change m b ≠ slabIdx W u_off (x_free a)
          rw [hma]
          exact fun heq => hb_out (Finset.mem_filter.mpr ⟨hb_ico, heq⟩)
        obtain ⟨θ, hbθ, hθa, hmθ⟩ := exists_transition_between hba hmb_ne
        have hθK : θ ∈ K := by
          unfold K slabTransitions
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmθ⟩
        have hθ_mem : θ ∈ K_all := by
          dsimp [K_all]
          split_ifs
          · exact hθK
          · exact Finset.mem_insert_of_mem hθK
        have hb_cr : b ∈ crossingLowers (xs j) T θ := by
          unfold crossingLowers
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (hba.trans hhop.2.1), hbθ, a, hθa, hhop⟩
        exact hb_not_cross (Finset.mem_biUnion.mpr ⟨j, hj_sdiff,
          Finset.mem_biUnion.mpr ⟨θ, hθ_mem, hb_cr⟩⟩)

/-! ## §5. Standalone Untouched-Raw-Row and Transposed-Column Coverage Lemmas -/

/-- Valid input bit indices `q : Fin L` visited by `x_in` during `S`. -/
def inCells (L : ℕ) (x_in : ℕ → ℤ) (S : Finset ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun q => ∃ t ∈ S, x_in t = (q.1 : ℤ)

/-- Raw matrix row `⌊q / (d * b)⌋ ∈ Fin d` of bit position `q : Fin (d * d * b)`. -/
def slabRawRow {d b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) (q : Fin (d * d * b)) : Fin d :=
  ⟨q.1 / (d * b), by
    have hW : 0 < d * b := Nat.mul_pos hd hb
    rw [Nat.div_lt_iff_lt_mul hW]
    simpa [mul_assoc, mul_comm, mul_left_comm] using q.2⟩

/-- During a single contiguous interval `[a, b_end)` (`a < b_end`), a unit-step input walk `x_in`
touches at most `(b_end - a) / (d * b) + 2` raw rows. -/
theorem card_badRawRows_interval_le {d b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) {x_in : ℕ → ℤ}
    (hx_in : IsWalk x_in) {a b_end : ℕ} (hab : a < b_end) :
    (((inCells (d * d * b) x_in (Finset.Ico a b_end)).image (slabRawRow hd hb)).card) ≤
      (b_end - a) / (d * b) + 2 := by
  classical
  set W := d * b
  have hW_pos : 0 < W := Nat.mul_pos hd hb
  set J := Finset.Ico a b_end
  set R_J := (inCells (d * d * b) x_in J).image (slabRawRow hd hb)
  rcases R_J.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  · set i_min := R_J.min' hne
    set i_max := R_J.max' hne
    have hsub : R_J.image Fin.val ⊆ Finset.Icc i_min.1 i_max.1 := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le R_J i hi, Finset.le_max' R_J i hi⟩
    have hcard_le : R_J.card ≤ i_max.1 + 1 - i_min.1 := by
      calc R_J.card
          = (R_J.image Fin.val).card :=
            (Finset.card_image_of_injective R_J Fin.val_injective).symm
        _ ≤ (Finset.Icc i_min.1 i_max.1).card := Finset.card_le_card hsub
        _ = i_max.1 + 1 - i_min.1 := Nat.card_Icc _ _
    obtain ⟨q₁, hq₁, hmin_eq⟩ := Finset.mem_image.mp (Finset.min'_mem R_J hne)
    obtain ⟨q₂, hq₂, hmax_eq⟩ := Finset.mem_image.mp (Finset.max'_mem R_J hne)
    obtain ⟨_, t₁, ht₁J, hxt₁⟩ := Finset.mem_filter.mp hq₁
    obtain ⟨_, t₂, ht₂J, hxt₂⟩ := Finset.mem_filter.mp hq₂
    obtain ⟨ht₁a, ht₁b⟩ := Finset.mem_Ico.mp ht₁J
    obtain ⟨ht₂a, ht₂b⟩ := Finset.mem_Ico.mp ht₂J
    have hq_diff : (q₂.1 : ℤ) - (q₁.1 : ℤ) ≤ ((b_end - a - 1 : ℕ) : ℤ) := by
      rw [← hxt₂, ← hxt₁]
      rcases le_total t₁ t₂ with hle | hge
      · have hlip := (hx_in.lip hle).1
        omega
      · have hlip := (hx_in.lip hge).2
        omega
    have hq₁_div : q₁.1 / W = i_min.1 := congrArg Fin.val hmin_eq
    have hq₂_div : q₂.1 / W = i_max.1 := congrArg Fin.val hmax_eq
    have hq₁_lt : q₁.1 < (i_min.1 + 1) * W := by
      have hdiv := Nat.div_add_mod q₁.1 W
      have hmod := Nat.mod_lt q₁.1 hW_pos
      rw [hq₁_div] at hdiv
      nlinarith
    have hq₂_ge : i_max.1 * W ≤ q₂.1 := by
      rw [← hq₂_div, mul_comm]
      exact Nat.mul_div_le q₂.1 W
    by_cases hgap : i_max.1 ≤ i_min.1 + 1
    · have hle2 : R_J.card ≤ 2 := by omega
      exact hle2.trans (Nat.le_add_left 2 _)
    · have hgap2 : i_min.1 + 2 ≤ i_max.1 := by omega
      have hmul_le : (i_max.1 - i_min.1 - 1) * W ≤ b_end - a := by
        have h1 : (i_max.1 - i_min.1 - 1) * W + (i_min.1 + 1) * W = i_max.1 * W := by
          rw [← Nat.add_mul]
          congr 1
          omega
        omega
      have hdiv_le : i_max.1 - i_min.1 - 1 ≤ (b_end - a) / W :=
        (Nat.le_div_iff_mul_le hW_pos).mpr hmul_le
      omega

/-- **Total bad raw rows**:
if `C ⊆ [0, T)` has `|C| ≤ L / 2`, at most `d / 2 + 2 * (runStarts C).card` raw rows intersect
`inCells L x_in C` (`2 * badRows.card ≤ d + 4 * (runStarts C).card`). -/
theorem card_badRawRows_mul_le {d b T : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) {x_in : ℕ → ℤ}
    (hx_in : IsWalk x_in) {C : Finset ℕ} (hCT : ∀ t ∈ C, t < T)
    (hC_half : C.card ≤ (d * d * b) / 2) :
    2 * ((inCells (d * d * b) x_in C).image (slabRawRow hd hb)).card ≤
      d + 4 * (runStarts C).card := by
  classical
  set W := d * b
  have hW_pos : 0 < W := Nat.mul_pos hd hb
  set L := d * d * b
  have hC_decomp := eq_biUnion_runInterval hCT
  have hdisj := pairwiseDisjoint_runInterval hCT
  have hC_card_eq : C.card = ∑ a ∈ runStarts C, (Finset.Ico a (runEnd C T a)).card := by
    conv_lhs => rw [hC_decomp]
    exact Finset.card_biUnion hdisj
  have hbad_sub : (inCells L x_in C).image (slabRawRow hd hb) ⊆
      (runStarts C).biUnion fun a =>
        (inCells L x_in (Finset.Ico a (runEnd C T a))).image (slabRawRow hd hb) := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨_, t, htC, hxt⟩ := Finset.mem_filter.mp hq
    rw [hC_decomp] at htC
    obtain ⟨a, ha, htIco⟩ := Finset.mem_biUnion.mp htC
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨q, ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htIco, hxt⟩
  have hW_mul : W * ((inCells L x_in C).image (slabRawRow hd hb)).card ≤
      C.card + 2 * (runStarts C).card * W := by
    calc W * ((inCells L x_in C).image (slabRawRow hd hb)).card
        ≤ W * ((runStarts C).biUnion fun a =>
            (inCells L x_in (Finset.Ico a (runEnd C T a))).image (slabRawRow hd hb)).card :=
          Nat.mul_le_mul_left W (Finset.card_le_card hbad_sub)
      _ ≤ W * ∑ a ∈ runStarts C,
            ((inCells L x_in (Finset.Ico a (runEnd C T a))).image (slabRawRow hd hb)).card :=
          Nat.mul_le_mul_left W Finset.card_biUnion_le
      _ = ∑ a ∈ runStarts C,
            W * ((inCells L x_in (Finset.Ico a (runEnd C T a))).image (slabRawRow hd hb)).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ a ∈ runStarts C, ((Finset.Ico a (runEnd C T a)).card + 2 * W) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hab : a < runEnd C T a := (runEnd_spec hCT ha).1
          have h1 : ((inCells L x_in (Finset.Ico a (runEnd C T a))).image (slabRawRow hd hb)).card ≤
              (runEnd C T a - a) / W + 2 :=
            card_badRawRows_interval_le hd hb hx_in hab
          have h2 := Nat.mul_div_le (runEnd C T a - a) W
          have h3 := Nat.mul_le_mul_left W h1
          rw [Nat.card_Ico]
          nlinarith [h2, h3]
      _ = C.card + 2 * (runStarts C).card * W := by
          rw [Finset.sum_add_distrib, ← hC_card_eq, Finset.sum_const, smul_eq_mul]
          ring
  have h2C_le : 2 * C.card ≤ d * W := by
    have h := Nat.mul_div_le L 2
    dsimp [L, W] at h hC_half ⊢
    nlinarith
  have hmul_W : W * (2 * ((inCells L x_in C).image (slabRawRow hd hb)).card) ≤
      W * (d + 4 * (runStarts C).card) := by
    nlinarith [hW_mul, h2C_le]
  exact Nat.le_of_mul_le_mul_left hmul_W hW_pos

/-- **Single-interval transposed row coverage**:
for strictly monotone append times `ot : Fin (d² b) → ℕ`, every contiguous time interval `[a, b_end)`
and every raw row `i : Fin d` satisfy
`(outIn ot [a, b_end)).card ≤ d * |Π(O([a, b_end))) ∩ R_i| + 2 * d * b`. -/
theorem outIn_interval_le_d_mul_rowHits {d b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    {ot : Fin (d * d * b) → ℕ} (hot_mono : StrictMono ot) (a b_end : ℕ) (i : Fin d) :
    (outIn ot (Finset.Ico a b_end)).card ≤
      d * (((outIn ot (Finset.Ico a b_end)).image (tposOf d b)).filter
        fun q => slabRawRow hd hb q = i).card + 2 * d * b := by
  classical
  let L := d * d * b
  let W := d * b
  have hW_pos : 0 < W := Nat.mul_pos hd hb
  set O_J := outIn ot (Finset.Ico a b_end)
  set hit := (O_J.image (tposOf d b)).filter fun q => slabRawRow hd hb q = i
  rcases O_J.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]
    omega
  · set r_min := O_J.min' hne
    set r_max := O_J.max' hne
    set ℓ₀ := r_min.1
    set ℓ₁ := r_max.1 + 1
    have hℓ₁_le_L : ℓ₁ ≤ L := r_max.2
    have hOJ_sub : O_J.image Fin.val ⊆ Finset.Ico ℓ₀ ℓ₁ := by
      intro v hv
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
      have h1 : r_min ≤ r := Finset.min'_le O_J r hr
      have h2 : r ≤ r_max := Finset.le_max' O_J r hr
      exact Finset.mem_Ico.mpr ⟨h1, Nat.lt_succ_of_le h2⟩
    have hOJ_card_le : O_J.card ≤ ℓ₁ - ℓ₀ := by
      calc O_J.card
          = (O_J.image Fin.val).card :=
            (Finset.card_image_of_injective O_J Fin.val_injective).symm
        _ ≤ (Finset.Ico ℓ₀ ℓ₁).card := Finset.card_le_card hOJ_sub
        _ = ℓ₁ - ℓ₀ := Nat.card_Ico ℓ₀ ℓ₁
    have hIco_mem_OJ : ∀ r : Fin L, ℓ₀ ≤ r.1 → r.1 < ℓ₁ → r ∈ O_J := by
      intro r hlo hhi
      have hr_min_mem := (Finset.mem_filter.mp (Finset.min'_mem O_J hne)).2
      have hr_max_mem := (Finset.mem_filter.mp (Finset.max'_mem O_J hne)).2
      obtain ⟨ha_min, _⟩ := Finset.mem_Ico.mp hr_min_mem
      obtain ⟨_, hb_max⟩ := Finset.mem_Ico.mp hr_max_mem
      have hle1 : ot r_min ≤ ot r := hot_mono.monotone hlo
      have hle2 : ot r ≤ ot r_max := hot_mono.monotone (Nat.le_of_lt_succ hhi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ico.mpr ⟨ha_min.trans hle1, hle2.trans_lt hb_max⟩⟩
    -- Full output columns `j ∈ Ico (ℓ₀ / W + 1) (ℓ₁ / W)` lie inside `[ℓ₀, ℓ₁)`.
    set cols := Finset.Ico (ℓ₀ / W + 1) (ℓ₁ / W)
    let pairSet := cols ×ˢ Finset.range b
    let mkHit : ℕ × ℕ → Fin L := fun p =>
      if hp : (i.1 * d + p.1) * b + p.2 < L then ⟨(i.1 * d + p.1) * b + p.2, hp⟩
      else ⟨0, Nat.mul_pos (Nat.mul_pos hd hd) hb⟩
    have hpair_props : ∀ p ∈ pairSet,
        p.1 < d ∧ p.2 < b ∧
        (p.1 * d + i.1) * b + p.2 < L ∧
        (i.1 * d + p.1) * b + p.2 < L ∧
        ℓ₀ ≤ (p.1 * d + i.1) * b + p.2 ∧ (p.1 * d + i.1) * b + p.2 < ℓ₁ := by
      intro p hp
      obtain ⟨hj_cols, hs_b⟩ := Finset.mem_product.mp hp
      obtain ⟨hj_lo, hj_hi⟩ := Finset.mem_Ico.mp hj_cols
      have hs_lt : p.2 < b := Finset.mem_range.mp hs_b
      have hj_mul_hi : (p.1 + 1) * W ≤ ℓ₁ := by
        calc (p.1 + 1) * W ≤ (ℓ₁ / W) * W := Nat.mul_le_mul_right W hj_hi
          _ ≤ ℓ₁ := Nat.div_mul_le_self ℓ₁ W
      have hj_lt_d : p.1 < d := by
        have : (p.1 + 1) * W ≤ d * W := hj_mul_hi.trans (by dsimp [L, W] at hℓ₁_le_L ⊢; linarith)
        have := le_of_mul_le_mul_right this hW_pos
        omega
      have hout_hi : (p.1 * d + i.1) * b + p.2 < (p.1 + 1) * W := by
        dsimp [W]
        calc (p.1 * d + i.1) * b + p.2
            < (p.1 * d + i.1) * b + b := Nat.add_lt_add_left hs_lt _
          _ = (p.1 * d + i.1 + 1) * b := by ring
          _ ≤ (p.1 * d + d) * b := Nat.mul_le_mul_right b (by omega)
          _ = (p.1 + 1) * (d * b) := by ring
      have hout_lo : ℓ₀ ≤ (p.1 * d + i.1) * b + p.2 := by
        have h1 : ℓ₀ < (ℓ₀ / W + 1) * W := by
          have hd_mod := Nat.div_add_mod ℓ₀ W
          have hm_lt := Nat.mod_lt ℓ₀ hW_pos
          nlinarith
        have h2 : (ℓ₀ / W + 1) * W ≤ p.1 * W := Nat.mul_le_mul_right W hj_lo
        have h3 : p.1 * W ≤ (p.1 * d + i.1) * b + p.2 := by
          dsimp [W]; nlinarith
        omega
      have hin_lt_L : (i.1 * d + p.1) * b + p.2 < L := by
        dsimp [L]
        calc (i.1 * d + p.1) * b + p.2
            < (i.1 * d + p.1) * b + b := Nat.add_lt_add_left hs_lt _
          _ = (i.1 * d + p.1 + 1) * b := by ring
          _ ≤ (i.1 * d + d) * b := Nat.mul_le_mul_right b (by omega)
          _ = (i.1 + 1) * d * b := by ring
          _ ≤ d * d * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
      exact ⟨hj_lt_d, hs_lt, hout_hi.trans_le (hj_mul_hi.trans hℓ₁_le_L), hin_lt_L,
        hout_lo, hout_hi.trans_le hj_mul_hi⟩
    have hinj_mkHit : Set.InjOn mkHit (pairSet : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨hj₁, hs₁, _, hin₁, _, _⟩ := hpair_props p₁ (Finset.mem_coe.mp hp₁)
      obtain ⟨hj₂, hs₂, _, hin₂, _, _⟩ := hpair_props p₂ (Finset.mem_coe.mp hp₂)
      have hval : (mkHit p₁).1 = (mkHit p₂).1 := congrArg Fin.val heq
      simp only [mkHit, hin₁, hin₂, ↓reduceDIte] at hval
      have hd₁ : ((i.1 * d + p₁.1) * b + p₁.2) / b = i.1 * d + p₁.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hs₁, zero_add]
      have hd₂ : ((i.1 * d + p₂.1) * b + p₂.2) / b = i.1 * d + p₂.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hs₂, zero_add]
      have hm₁ : ((i.1 * d + p₁.1) * b + p₁.2) % b = p₁.2 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs₁]
      have hm₂ : ((i.1 * d + p₂.1) * b + p₂.2) % b = p₂.2 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs₂]
      have hdiv_eq : i.1 * d + p₁.1 = i.1 * d + p₂.1 := by rw [← hd₁, ← hd₂, hval]
      have hmod_eq : p₁.2 = p₂.2 := by rw [← hm₁, ← hm₂, hval]
      exact Prod.ext (by omega) hmod_eq
    have hsub_hit : pairSet.image mkHit ⊆ hit := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hj, hs, hout_L, hin_L, hout_lo, hout_hi⟩ := hpair_props p hp
      let r_out : Fin L := ⟨(p.1 * d + i.1) * b + p.2, hout_L⟩
      have hr_OJ : r_out ∈ O_J := hIco_mem_OJ r_out hout_lo hout_hi
      have htpos_eq : tposOf d b r_out = mkHit p := by
        apply Fin.ext
        rw [tposOf_val]
        simp only [r_out, mkHit, hin_L, ↓reduceDIte]
        exact tpos_spec i.2 hs
      have hrow_eq : slabRawRow hd hb (mkHit p) = i := by
        apply Fin.ext
        simp only [slabRawRow, mkHit, hin_L, ↓reduceDIte]
        have hd_b : ((i.1 * d + p.1) * b + p.2) / b = i.1 * d + p.1 := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hs, zero_add]
        have hd_d : (i.1 * d + p.1) / d = i.1 := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, zero_add]
        rw [Nat.mul_comm d b, ← Nat.div_div_eq_div_mul, hd_b, hd_d]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨r_out, hr_OJ, htpos_eq⟩, hrow_eq⟩
    have hhit_ge : cols.card * b ≤ hit.card := by
      calc cols.card * b
          = pairSet.card := by simp [pairSet]
        _ = (pairSet.image mkHit).card := (Finset.card_image_of_injOn hinj_mkHit).symm
        _ ≤ hit.card := Finset.card_le_card hsub_hit
    have hcols_card : cols.card = ℓ₁ / W - (ℓ₀ / W + 1) := Nat.card_Ico _ _
    have hdiv_hi : ℓ₁ < (ℓ₁ / W + 1) * W := by
      have hd_mod := Nat.div_add_mod ℓ₁ W
      have hm_lt := Nat.mod_lt ℓ₁ hW_pos
      nlinarith
    have hdiv_lo : (ℓ₀ / W) * W ≤ ℓ₀ := Nat.div_mul_le_self ℓ₀ W
    have hspan_le : ℓ₁ - ℓ₀ ≤ (cols.card + 2) * W := by
      have hmul_col : (ℓ₁ / W + 1) * W ≤ (cols.card + ℓ₀ / W + 2) * W :=
        Nat.mul_le_mul_right W (by omega)
      have h1 : ℓ₁ < (cols.card + 2) * W + (ℓ₀ / W) * W := by
        calc ℓ₁ < (ℓ₁ / W + 1) * W := hdiv_hi
          _ ≤ (cols.card + ℓ₀ / W + 2) * W := hmul_col
          _ = (cols.card + 2) * W + (ℓ₀ / W) * W := by ring
      omega
    calc O_J.card
        ≤ ℓ₁ - ℓ₀ := hOJ_card_le
      _ ≤ (cols.card + 2) * W := hspan_le
      _ = d * (cols.card * b) + 2 * d * b := by dsimp [W]; ring
      _ ≤ d * hit.card + 2 * d * b :=
          Nat.add_le_add_right (Nat.mul_le_mul_left d hhit_ge) (2 * d * b)

/-- **Combined stripe-discrepancy independent-set cardinality**:
for any `C ⊆ [0, T)` with `|C| ≤ (d² b) / 2`, setting
`U_* := (outIn ot C).image (tposOf d b) \ inCells (d² b) x_in C`, we have
`(outIn ot C).card ≤ 2 * U_*.card + 6 * (runStarts C).card * d * b`. -/
theorem outIn_card_le_two_indep_add_six_runs {d b T : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    {x_in : ℕ → ℤ} (hx_in : IsWalk x_in) {ot : Fin (d * d * b) → ℕ} (hot_mono : StrictMono ot)
    {C : Finset ℕ} (hCT : ∀ t ∈ C, t < T) (hC_half : C.card ≤ (d * d * b) / 2) :
    (outIn ot C).card ≤
      2 * ((outIn ot C).image (tposOf d b) \ inCells (d * d * b) x_in C).card +
        6 * (runStarts C).card * d * b := by
  classical
  let L := d * d * b
  set s_star := (runStarts C).card
  set U_star := (outIn ot C).image (tposOf d b) \ inCells L x_in C
  set badRows := (inCells L x_in C).image (slabRawRow hd hb)
  set freeRows := (Finset.univ : Finset (Fin d)) \ badRows
  have hbad_le : 2 * badRows.card ≤ d + 4 * s_star :=
    card_badRawRows_mul_le hd hb hx_in hCT hC_half
  have hpart_rows : freeRows.card + badRows.card = d := by
    dsimp [freeRows]
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin d)) badRows
    rw [Finset.univ_inter, Finset.card_fin] at h
    exact h
  have hfree_ge : d ≤ 2 * freeRows.card + 4 * s_star := by omega
  -- Sum the single-interval coverage bound over the disjoint runs of `C`.
  have hC_decomp := eq_biUnion_runInterval hCT
  have hdisj_runs := pairwiseDisjoint_runInterval hCT
  have htpos_inj : Function.Injective (tposOf d b) :=
    Function.Involutive.injective (tposOf_tposOf d b)
  let hitC : Fin d → Finset (Fin L) := fun i =>
    ((outIn ot C).image (tposOf d b)).filter fun q => slabRawRow hd hb q = i
  have hrow_cover : ∀ i : Fin d, (outIn ot C).card ≤ d * (hitC i).card + 2 * s_star * d * b := by
    intro i
    let hitRun : ℕ → Finset (Fin L) := fun a =>
      ((outIn ot (Finset.Ico a (runEnd C T a))).image (tposOf d b)).filter
        fun q => slabRawRow hd hb q = i
    have houtC_eq : outIn ot C =
        (runStarts C).biUnion fun a => outIn ot (Finset.Ico a (runEnd C T a)) := by
      ext r
      simp only [outIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      conv_lhs => rw [hC_decomp]
      exact Finset.mem_biUnion
    have hdisj_out : (runStarts C : Set ℕ).PairwiseDisjoint
        (fun a => outIn ot (Finset.Ico a (runEnd C T a))) := by
      intro a₁ ha₁ a₂ ha₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro r hr₁ hr₂
      exact Finset.disjoint_left.mp (hdisj_runs ha₁ ha₂ hne)
        (Finset.mem_filter.mp hr₁).2 (Finset.mem_filter.mp hr₂).2
    have hdisj_hitRun : (runStarts C : Set ℕ).PairwiseDisjoint hitRun := by
      intro a₁ ha₁ a₂ ha₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      obtain ⟨r₁, hr₁, htp₁⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq₁).1
      obtain ⟨r₂, hr₂, htp₂⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq₂).1
      have hr_eq : r₁ = r₂ := htpos_inj (htp₁.trans htp₂.symm)
      rw [hr_eq] at hr₁
      exact Finset.disjoint_left.mp (hdisj_out ha₁ ha₂ hne) hr₁ hr₂
    have hsub_hitC : (runStarts C).biUnion hitRun ⊆ hitC i := by
      intro q hq
      obtain ⟨a, ha, hqa⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨hq_img, hq_row⟩ := Finset.mem_filter.mp hqa
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq_img
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r, ?_, rfl⟩, hq_row⟩
      rw [houtC_eq]
      exact Finset.mem_biUnion.mpr ⟨a, ha, hr⟩
    have hsum_hitRun : ∑ a ∈ runStarts C, (hitRun a).card ≤ (hitC i).card := by
      rw [← Finset.card_biUnion hdisj_hitRun]
      exact Finset.card_le_card hsub_hitC
    calc (outIn ot C).card
        = ∑ a ∈ runStarts C, (outIn ot (Finset.Ico a (runEnd C T a))).card := by
          rw [houtC_eq, Finset.card_biUnion hdisj_out]
      _ ≤ ∑ a ∈ runStarts C, (d * (hitRun a).card + 2 * d * b) :=
          Finset.sum_le_sum fun a _ =>
            outIn_interval_le_d_mul_rowHits hd hb hot_mono a (runEnd C T a) i
      _ = d * (∑ a ∈ runStarts C, (hitRun a).card) + 2 * s_star * d * b := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ d * (hitC i).card + 2 * s_star * d * b :=
          Nat.add_le_add_right (Nat.mul_le_mul_left d hsum_hitRun) _
  -- Disjoint union of `hitC i` over `i ∈ freeRows` lies inside `U_star`.
  have hdisj_free : (freeRows : Set (Fin d)).PairwiseDisjoint hitC := by
    intro i₁ _ i₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    exact hne ((Finset.mem_filter.mp hq₁).2.symm.trans (Finset.mem_filter.mp hq₂).2)
  have hsub_U : freeRows.biUnion hitC ⊆ U_star := by
    intro q hq
    obtain ⟨i, hi_free, hqi⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hq_img, hq_row⟩ := Finset.mem_filter.mp hqi
    have hi_not_bad : i ∉ badRows := (Finset.mem_sdiff.mp hi_free).2
    refine Finset.mem_sdiff.mpr ⟨hq_img, fun hq_in => ?_⟩
    exact hi_not_bad (hq_row ▸ Finset.mem_image_of_mem (slabRawRow hd hb) hq_in)
  have hsum_U : ∑ i ∈ freeRows, (hitC i).card ≤ U_star.card := by
    rw [← Finset.card_biUnion hdisj_free]
    exact Finset.card_le_card hsub_U
  -- Conclude `(outIn ot C).card ≤ 2 * U_star.card + 6 * s_star * d * b` via ℝ arithmetic.
  set O_card := (outIn ot C).card
  have hO_le_L : O_card ≤ d * d * b :=
    (outIn ot C).card_le_univ.trans_eq (Fintype.card_fin (d * d * b))
  by_cases hsmall : O_card ≤ 2 * s_star * d * b
  · calc O_card
        ≤ 2 * s_star * d * b := hsmall
      _ ≤ 6 * s_star * d * b :=
          Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (Nat.mul_le_mul_right s_star (by omega)))
      _ ≤ 2 * U_star.card + 6 * s_star * d * b := Nat.le_add_left _ _
  · have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hterm_pos : (0 : ℝ) < (O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ) := by
      rw [sub_pos, lt_div_iff₀ hd_posR]
      have : (2 * s_star * d * b : ℝ) < (O_card : ℝ) := by
        exact_mod_cast (show 2 * s_star * d * b < O_card by omega)
      linarith
    have hhit_geR : ∀ i ∈ freeRows,
        (O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ) ≤ ((hitC i).card : ℝ) := by
      intro i _
      have hi_nat := hrow_cover i
      have hi_R : (O_card : ℝ) ≤
          (d : ℝ) * ((hitC i).card : ℝ) + 2 * (s_star : ℝ) * (d : ℝ) * (b : ℝ) := by
        exact_mod_cast hi_nat
      rw [sub_le_iff_le_add, div_le_iff₀ hd_posR]
      linarith
    have hU_geR : (freeRows.card : ℝ) * ((O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ)) ≤
        (U_star.card : ℝ) := by
      calc (freeRows.card : ℝ) * ((O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ))
          = ∑ _i ∈ freeRows, ((O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ freeRows, ((hitC i).card : ℝ) := Finset.sum_le_sum hhit_geR
        _ ≤ (U_star.card : ℝ) := by exact_mod_cast hsum_U
    have hfree_geR : (d : ℝ) / 2 - 2 * (s_star : ℝ) ≤ (freeRows.card : ℝ) := by
      have : (d : ℝ) ≤ 2 * (freeRows.card : ℝ) + 4 * (s_star : ℝ) := by exact_mod_cast hfree_ge
      linarith
    have hprod_ge : ((d : ℝ) / 2 - 2 * (s_star : ℝ)) *
        ((O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ)) ≤ (U_star.card : ℝ) :=
      (mul_le_mul_of_nonneg_right hfree_geR hterm_pos.le).trans hU_geR
    have hOd_le : (O_card : ℝ) / (d : ℝ) ≤ (d : ℝ) * (b : ℝ) := by
      rw [div_le_iff₀ hd_posR]
      have : (O_card : ℝ) ≤ (d : ℝ) * (d : ℝ) * (b : ℝ) := by exact_mod_cast hO_le_L
      linarith
    have hexpand : ((d : ℝ) / 2 - 2 * (s_star : ℝ)) *
        ((O_card : ℝ) / (d : ℝ) - 2 * (s_star : ℝ) * (b : ℝ)) =
        (O_card : ℝ) / 2 - (s_star : ℝ) * (d : ℝ) * (b : ℝ) -
          2 * (s_star : ℝ) * ((O_card : ℝ) / (d : ℝ)) +
          4 * (s_star : ℝ) ^ 2 * (b : ℝ) := by
      field_simp [hd_posR.ne']
      ring
    have hnonneg_sq : (0 : ℝ) ≤ 4 * (s_star : ℝ) ^ 2 * (b : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Nat.cast_nonneg _)
    have hs_nn : (0 : ℝ) ≤ 2 * (s_star : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have h2s_Od : 2 * (s_star : ℝ) * ((O_card : ℝ) / (d : ℝ)) ≤
        2 * (s_star : ℝ) * ((d : ℝ) * (b : ℝ)) :=
      mul_le_mul_of_nonneg_left hOd_le hs_nn
    have hfinalR : (O_card : ℝ) ≤
        2 * (U_star.card : ℝ) + 6 * (s_star : ℝ) * (d : ℝ) * (b : ℝ) := by
      linarith [hprod_ge, hexpand, hnonneg_sq, h2s_Od]
    exact_mod_cast hfinalR

/-! ## §6. Frozen-Trace Genie Bridge and the Slab-Chunk Error Budget -/

private theorem getLastD_mem_cons_self : ∀ (t : ℕ) (ρ : List ℕ), (t :: ρ).getLastD t ∈ t :: ρ
  | t, [] => by simp
  | t, s :: σ => by
      rw [LinNet.getLastD_cons_cons]
      exact List.mem_cons_of_mem t (getLastD_mem_cons_self s σ)

/-- **Subpopulation-generalized `BlockFunDag` + `DirectedRecovery` storage-code bridge**:
for any output-index subset `O_sub : Finset (Fin L)` whose `Γ`-free `DepPath`s starting in
`O_sub.image ot` stay inside `C`, `U_sub := O_sub.image (tposOf d b) \ inCells L τ₀.input C`
satisfies `U_sub.card - β * Γ.card ≤ η * L`. -/
theorem frozenTrace_subpop_deficit_le {M : TM} {β c η : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hvw : (valueWidth M : ℝ) ≤ β) (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀) :
    let b := entryBits d
    let T := τ₀.haltTime
    let ot : Fin (d * d * b) → ℕ := fun r => appendTime τ₀ T r.1
    T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ ∧
    0 < T ∧
    (T : ℝ) ≤ 2 * c * ((d * d * b : ℕ) : ℝ) ∧
    StrictMono ot ∧
    (∀ r : Fin (d * d * b), ot r < T) ∧
    ∀ (C Γ : Finset ℕ) (O_sub : Finset (Fin (d * d * b))),
      (∀ (π : List ℕ) (t₀ : ℕ), t₀ ∈ O_sub.image ot → IsDepPath τ₀.work T (t₀ :: π) →
        LinNet.GFree Γ (t₀ :: π) → ∀ v ∈ t₀ :: π, v ∈ C) →
      (((O_sub.image (tposOf d b) \ inCells (d * d * b) τ₀.input C).card : ℝ) -
        β * (Γ.card : ℝ)) ≤ η * ((d * d * b : ℕ) : ℝ) := by
  classical
  let b := entryBits d
  let L := d * d * b
  have hb : 1 ≤ b := one_le_entryBits d
  have hL_pos : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hL_eq : inputLength d = L := rfl
  obtain ⟨_, hfib_ne⟩ := fibre_facts hL_pos (hL_eq ▸ hprob)
  obtain ⟨X₀, hX₀⟩ := hfib_ne
  obtain ⟨hT_floor, happ_eq⟩ := fibre_haltTime hX₀ (htr.transposesInput X₀)
  let T := τ₀.haltTime
  have hT_pos : 0 < T := prefix_pos hd hb happ_eq.ge
  have hT_real : (T : ℝ) ≤ 2 * c * (L : ℝ) := runtime_le hL_pos hT_pos hT_floor
  let ot : Fin L → ℕ := fun r => appendTime τ₀ T r.1
  have hot_mono : StrictMono ot := by
    intro r₁ r₂ hlt
    have hr₁ : r₁.1 < (appendList τ₀ T).length := happ_eq ▸ r₁.2
    have hr₂ : r₂.1 < (appendList τ₀ T).length := happ_eq ▸ r₂.2
    exact appendTime_strictMonoOn τ₀ T hr₁ hr₂ hlt
  have hot_lt : ∀ r : Fin L, ot r < T := fun r =>
    appendTime_lt τ₀ T (happ_eq ▸ r.2)
  refine ⟨hT_floor, hT_pos, hT_real, hot_mono, hot_lt, fun C Γ O_sub htrap => ?_⟩
  let dfltVal : Value M := (⟨0, Nat.succ_pos _⟩, fun _ => ⟨0, Nat.succ_pos _⟩, none)
  let G : BlockFunDag L (Value M) :=
    { out := fun t => (Finset.range T).filter fun s => DepStep τ₀.work T t s
      out_lt := fun t s hs => (depStep_lt (Finset.mem_filter.mp hs).2).1
      blk := fun t => if t < T then inCells L τ₀.input {t} else ∅
      S := (fibre M L τ₀ : Set (Fin L → Bool))
      val := fun X t => if t < T then stepValue M (List.ofFn X) t else dfltVal
      det := fun X hX Y hY t hpar hblk => by
        split_ifs with ht
        · have hX' : trace M (List.ofFn X) = τ₀ := mem_fibre.mp (Finset.mem_coe.mp hX)
          have hY' : trace M (List.ofFn Y) = τ₀ := mem_fibre.mp (Finset.mem_coe.mp hY)
          refine stepValue_eq_of_parents
            (fun s _ => by rw [hX']) (fun s _ => by rw [hY']) ht
            (fun p hp hpL => ?_) (fun u hu => ?_)
          · apply hblk ⟨p, hpL⟩
            simp only [ht, ↓reduceIte, inCells, Finset.mem_filter, Finset.mem_univ,
              Finset.mem_singleton, true_and]
            exact ⟨t, rfl, hp.symm⟩
          · have hdep_u : DepStep τ₀.work T t u := by
              rcases mem_actualParents.mp hu with rfl | ⟨h, h1, h2, h3, h4⟩
              · exact Or.inl ⟨rfl, ht⟩
              · exact Or.inr (Finset.mem_image.mpr
                  ⟨(h, u, t), mem_allHops.mpr ⟨h1, h2, h3, h4⟩, rfl⟩)
            have hu_lt : u < T := (depStep_lt hdep_u).1.trans ht
            have hu_out : u ∈ (Finset.range T).filter (fun s => DepStep τ₀.work T t s) :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt, hdep_u⟩
            have hp_eq := hpar u hu_out
            simpa only [hu_lt, ↓reduceIte] using hp_eq
        · rfl }
  have hdep_out : ∀ t, ∀ s ∈ G.net.out t, DepStep τ₀.work T t s :=
    fun _ _ hs => (Finset.mem_filter.mp hs).2
  let N_rel : Fin L → Finset (Fin L) := fun q => G.coneJ Γ (ot (tposOf d b q))
  let U_star := O_sub.image (tposOf d b) \ inCells L τ₀.input C
  -- `U_star` is `DirectedRecovery.IsIndependent` for `N_rel`.
  have hInd : DirectedRecovery.IsIndependent N_rel U_star := by
    intro q hq p hp hpU
    obtain ⟨hq_img, _⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨_, hp_not_in⟩ := Finset.mem_sdiff.mp hpU
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hq_img
    have hr_in_O : tposOf d b (tposOf d b r₀) ∈ O_sub := by
      rwa [tposOf_tposOf]
    have hot_in_src : ot (tposOf d b (tposOf d b r₀)) ∈ O_sub.image ot :=
      Finset.mem_image_of_mem ot hr_in_O
    obtain ⟨u, hu_cone, hp_blk⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨π, hπ_path, hπ_free, rfl⟩ := (mem_coneV G.net).mp hu_cone
    obtain ⟨ρ, hπ_eq⟩ := G.net.mem_paths_head hπ_path
    have hπ_dep : IsDepPath τ₀.work T π := isDepPath_of_paths hdep_out π _ hπ_path
    rw [hπ_eq] at hπ_dep hπ_free hp_blk
    have hlast_C : (ot (tposOf d b (tposOf d b r₀)) :: ρ).getLastD
        (ot (tposOf d b (tposOf d b r₀))) ∈ C :=
      htrap ρ _ hot_in_src hπ_dep hπ_free _ (getLastD_mem_cons_self _ ρ)
    dsimp [G] at hp_blk
    split_ifs at hp_blk with hlt_T
    · obtain ⟨_, s, hs_eq, hxs⟩ := Finset.mem_filter.mp hp_blk
      rw [Finset.mem_singleton] at hs_eq
      subst hs_eq
      exact hp_not_in (Finset.mem_filter.mpr ⟨Finset.mem_univ p, _, hlast_C, hxs⟩)
    · simp at hp_blk
  -- Output decoding along `G` on `fibre M L τ₀`.
  have hdec : ∀ X ∈ G.S, ∀ r : Fin L,
      X (tposOf d b r) = (G.val X (ot r)).2.2.getD false := by
    intro X hX r
    have hX_tr : trace M (List.ofFn X) = τ₀ := mem_fibre.mp (Finset.mem_coe.mp hX)
    have hp_out := (prefix_output happ_eq.ge (fun s _ => by rw [hX_tr])
      (htr.transposesInput X).outputsTranspose).2 (tposOf d b r)
    have htpos_r : Transpose.Tape.tpos d b (tposOf d b r) = r.1 :=
      congrArg Fin.val (tposOf_tposOf d b r)
    rw [htpos_r] at hp_out
    have hot_r : ot r < T := hot_lt r
    dsimp [G, ot]
    rw [ite_eq_left hot_r]
    change X (tposOf d b r) = (outBit M (List.ofFn X) (appendTime τ₀ T r.1)).getD false
    rw [hp_out]
    rfl
  -- Partition `fibre M L τ₀` by revealed values on `Γ`.
  let W_fib := fibre M L τ₀
  let evalΓ : (Fin L → Bool) → (Γ → Value M) := fun X u => G.val X u.1
  have hfib_sum : W_fib.card =
      ∑ g₀ ∈ (Finset.univ : Finset (Γ → Value M)),
        (W_fib.filter fun X => evalΓ X = g₀).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  have hsubfib_le : ∀ g₀ : Γ → Value M,
      (W_fib.filter fun X => evalΓ X = g₀).card ≤ 2 ^ (L - U_star.card) := by
    intro g₀
    let g_ext : ℕ → Value M := fun v => if hv : v ∈ Γ then g₀ ⟨v, hv⟩ else dfltVal
    have hsub : W_fib.filter (fun X => evalΓ X = g₀) ⊆ G.fibre Γ g_ext := by
      intro X hX
      obtain ⟨hXW, hev⟩ := Finset.mem_filter.mp hX
      simp only [BlockFunDag.fibre, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.mem_coe.mpr hXW, fun v hv => ?_⟩
      have hv_eq := congrFun hev ⟨v, hv⟩
      simpa only [evalΓ, g_ext, hv, ↓reduceDIte] using hv_eq
    have hSC : MotionDepthCodes.IsStorageCode N_rel (G.fibre Γ g_ext) :=
      G.isStorageCode_fibre Γ ot (tposOf d b) (tposOf_tposOf d b)
        (fun X r => X (tposOf d b r)) (fun _ v => v.2.2.getD false)
        hdec (fun _ _ _ => rfl) g_ext
    have hcard_SC := DirectedRecovery.storageCode_card_le_of_independent hInd hSC
    simp only [Fintype.card_bool, Fintype.card_fin] at hcard_SC
    exact (Finset.card_le_card hsub).trans hcard_SC
  have hcod_card : (Finset.univ : Finset (Γ → Value M)).card ≤ 2 ^ (valueWidth M * Γ.card) := by
    calc (Finset.univ : Finset (Γ → Value M)).card
        = Fintype.card (Value M) ^ Γ.card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
      _ ≤ (2 ^ valueWidth M) ^ Γ.card := Nat.pow_le_pow_left (card_value_le M) Γ.card
      _ = 2 ^ (valueWidth M * Γ.card) := (pow_mul 2 (valueWidth M) Γ.card).symm
  have hW_card_le : W_fib.card ≤ 2 ^ (valueWidth M * Γ.card + (L - U_star.card)) := by
    calc W_fib.card
        = ∑ g₀ ∈ (Finset.univ : Finset (Γ → Value M)),
            (W_fib.filter fun X => evalΓ X = g₀).card := hfib_sum
      _ ≤ ∑ _g₀ ∈ (Finset.univ : Finset (Γ → Value M)), 2 ^ (L - U_star.card) :=
          Finset.sum_le_sum fun g₀ _ => hsubfib_le g₀
      _ = (Finset.univ : Finset (Γ → Value M)).card * 2 ^ (L - U_star.card) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (valueWidth M * Γ.card) * 2 ^ (L - U_star.card) :=
          Nat.mul_le_mul_right _ hcod_card
      _ = 2 ^ (valueWidth M * Γ.card + (L - U_star.card)) := (pow_add 2 _ _).symm
  have hU_le_L : U_star.card ≤ L :=
    U_star.card_le_univ.trans_eq (Fintype.card_fin L)
  have hW_rpow_lo : (2 : ℝ) ^ ((1 - η) * (L : ℝ)) ≤ (W_fib.card : ℝ) :=
    two_rpow_le_card_fibre (hL_eq ▸ hprob)
  have hW_rpow_hi : (W_fib.card : ℝ) ≤
      (2 : ℝ) ^ ((valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U_star.card : ℝ))) := by
    calc (W_fib.card : ℝ)
        ≤ ((2 ^ (valueWidth M * Γ.card + (L - U_star.card)) : ℕ) : ℝ) := by
          exact_mod_cast hW_card_le
      _ = (2 : ℝ) ^ ((valueWidth M * Γ.card + (L - U_star.card) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U_star.card : ℝ))) := by
          congr 1
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hU_le_L]
  have hexp_le : (1 - η) * (L : ℝ) ≤
      (valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U_star.card : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp (hW_rpow_lo.trans hW_rpow_hi)
  have hvw_mul : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ β * (Γ.card : ℝ) :=
    mul_le_mul_of_nonneg_right hvw (Nat.cast_nonneg _)
  linarith

private theorem slab_wall_cap_bound {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    {L T : ℕ} (hL_pos : 0 < L) (hT_2c : (T : ℝ) ≤ 2 * c * (L : ℝ)) :
    (T - 1) / ⌈(L : ℝ) / (80 * β * c)⌉₊ ≤ slabWallCap c β := by
  refine Nat.le_floor ?_
  set W_cut := ⌈(L : ℝ) / (80 * β * c)⌉₊
  have h80_pos : 0 < 80 * β * c := by positivity
  have hL_posR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
  have hmul_nat : ((T - 1) / W_cut) * W_cut ≤ T :=
    (Nat.div_mul_le_self (T - 1) W_cut).trans (Nat.sub_le T 1)
  have hmul_R : (((T - 1) / W_cut : ℕ) : ℝ) * ((L : ℝ) / (80 * β * c)) ≤ 2 * c * (L : ℝ) := by
    calc (((T - 1) / W_cut : ℕ) : ℝ) * ((L : ℝ) / (80 * β * c))
        ≤ (((T - 1) / W_cut : ℕ) : ℝ) * (W_cut : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
      _ ≤ (T : ℝ) := by exact_mod_cast hmul_nat
      _ ≤ 2 * c * (L : ℝ) := hT_2c
  have hdiv_pos : 0 < (L : ℝ) / (80 * β * c) := div_pos hL_posR h80_pos
  rw [← le_div_iff₀ hdiv_pos] at hmul_R
  refine hmul_R.trans_eq ?_
  field_simp [hL_posR.ne', h80_pos.ne']
  ring

/-- Error budget of the slab-chunk count. The crossing part `Γcr_card` of the genie counts, for each
of at most `k` heads and each of at most `N_wall + 1` walls `θ`, the earlier ends other than `θ`
itself of short revisits spanning `θ` (at most `2 H_max` each); the walls are counted in
`Kall_card`. -/
private theorem slab_step4_net_ge {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    {d b k T O_card U_card Kall_card Γcr_card Γsl_card Γ_card runs_card : ℕ}
    (hd : d ≥ slabDimThreshold c β) (hb1 : 1 ≤ b)
    (hT_floor : T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊)
    (hKall_le : Kall_card ≤ slabWallCap c β + 1)
    (hcross_le : Γcr_card ≤ k * (slabWallCap c β + 1) *
      (2 * ⌊slabSmallExcursion c β k * ((d * d * b : ℕ) : ℝ)⌋₊))
    (hslab_le : Γsl_card ≤ ⌈((d * d * b : ℕ) : ℝ) / (80 * β * c)⌉₊)
    (hΓ_le : Γ_card ≤ Kall_card + Γcr_card + Γsl_card)
    (hruns_le : runs_card ≤ slabWallCap c β + 1)
    (hcov_U : O_card ≤ 2 * U_card + 6 * runs_card * d * b)
    (hcases : (Γsl_card = 0 ∧ d * d * b ≤ 2 * (slabWallCap c β + 1) * O_card) ∨
      (d * d * b) * ((d * d * b) / 2) < 4 * T * O_card) :
    3 * slabAutonomyEps c β * ((d * d * b : ℕ) : ℝ) ≤ (O_card : ℝ) ∧
    slabAutonomyEps c β * ((d * d * b : ℕ) : ℝ) ≤ (U_card : ℝ) - β * (Γ_card : ℝ) := by
  have hd10 : 10 ≤ d := (ten_le_slabDimThreshold c β).trans hd
  set L := d * d * b with hL_def
  have hL100 : 100 ≤ L := by
    calc 100 = 10 * 10 * 1 := by norm_num
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul hd10 hd10) hb1
  have hL_posR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  set N_wall := slabWallCap c β
  set ε_star := slabAutonomyEps c β
  have hε_pos : 0 < ε_star := slabAutonomyEps_pos c β
  have hdR : (slabDimThreshold c β : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_80 : 80 * β * c ≤ (d : ℝ) := (eighty_mul_le_slabDimThreshold hc hβ).trans hdR
  have hd_20 : 20 * ((N_wall : ℝ) + 2) / ε_star ≤ (d : ℝ) :=
    (slabDimThreshold_cast_eq c β).symm.le.trans hdR
  have hd2_le_L : (d : ℝ) * (d : ℝ) ≤ (L : ℝ) := by
    have : d * d ≤ d * d * b := by
      calc d * d = d * d * 1 := by ring
        _ ≤ d * d * b := Nat.mul_le_mul le_rfl hb1
    exact_mod_cast this
  have h80_pos : 0 < 80 * β * c := by positivity
  -- Convert stripe-discrepancy bound to `ℝ`.
  have hcov_N : O_card ≤ 2 * U_card + 6 * (N_wall + 1) * d * b :=
    hcov_U.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 6 hruns_le))) _)
  have hU_ge : (O_card : ℝ) / 2 - 3 * ((N_wall : ℝ) + 1) * (d : ℝ) * (b : ℝ) ≤ (U_card : ℝ) := by
    have hcovR : (O_card : ℝ) ≤
        2 * (U_card : ℝ) + 6 * ((N_wall : ℝ) + 1) * (d : ℝ) * (b : ℝ) := by
      exact_mod_cast hcov_N
    linarith only [hcovR]
  -- Bound the four small error terms by `(1 / 2) * ε_star * L`.
  have hβN_le : β * ((N_wall : ℝ) + 2) ≤ (1 / 1600) * ε_star * (L : ℝ) := by
    have hprod_d : (80 * β * c) * (20 * ((N_wall : ℝ) + 2) / ε_star) ≤ (L : ℝ) :=
      (mul_le_mul hd_80 hd_20 (by positivity) (by positivity)).trans hd2_le_L
    have h1600 : 1600 * β * ((N_wall : ℝ) + 2) / ε_star ≤
        (80 * β * c) * (20 * ((N_wall : ℝ) + 2) / ε_star) := by
      have h1 : 1600 * β * ((N_wall : ℝ) + 2) ≤ 1600 * β * ((N_wall : ℝ) + 2) * c :=
        le_mul_of_one_le_right (by positivity) hc
      calc 1600 * β * ((N_wall : ℝ) + 2) / ε_star
          ≤ (1600 * β * ((N_wall : ℝ) + 2) * c) / ε_star :=
            div_le_div_of_nonneg_right h1 hε_pos.le
        _ = (80 * β * c) * (20 * ((N_wall : ℝ) + 2) / ε_star) := by ring
    have h2 : 1600 * β * ((N_wall : ℝ) + 2) ≤ (L : ℝ) * ε_star :=
      (div_le_iff₀ hε_pos).mp (h1600.trans hprod_d)
    have h2' : 1600 * (β * ((N_wall : ℝ) + 2)) ≤ ε_star * (L : ℝ) := by
      calc 1600 * (β * ((N_wall : ℝ) + 2)) = 1600 * β * ((N_wall : ℝ) + 2) := by ring
        _ ≤ (L : ℝ) * ε_star := h2
        _ = ε_star * (L : ℝ) := by ring
    linarith only [h2']
  have herr_Kall : β * (Kall_card : ℝ) ≤ (1 / 1600) * ε_star * (L : ℝ) := by
    have hkR : (Kall_card : ℝ) ≤ (N_wall : ℝ) + 2 := by
      have : Kall_card ≤ N_wall + 2 := by omega
      exact_mod_cast this
    exact (mul_le_mul_of_nonneg_left hkR (by positivity)).trans hβN_le
  have herr_cross : β * (Γcr_card : ℝ) ≤ (1 / 4) * ε_star * (L : ℝ) := by
    set H_max := ⌊slabSmallExcursion c β k * (L : ℝ)⌋₊
    have hcrR : (Γcr_card : ℝ) ≤ 2 * (k : ℝ) * ((N_wall : ℝ) + 1) * (H_max : ℝ) := by
      have h1 : Γcr_card ≤ 2 * k * (N_wall + 1) * H_max := by
        calc Γcr_card ≤ k * (N_wall + 1) * (2 * H_max) := hcross_le
          _ = 2 * k * (N_wall + 1) * H_max := by ring
      exact_mod_cast h1
    have hH_le : (H_max : ℝ) ≤ slabSmallExcursion c β k * (L : ℝ) :=
      Nat.floor_le (mul_nonneg (slabSmallExcursion_pos (by positivity) k).le hL_posR.le)
    have h2k_le : 2 * (k : ℝ) ≤ ((max 1 (2 * k) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 1 (2 * k)
    have hmax_pos : (0 : ℝ) < ((max 1 (2 * k) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 (2 * k))
    have hterm1 : β * (2 * (k : ℝ) * ((N_wall : ℝ) + 1) * (H_max : ℝ)) ≤
        (1 / 4) * ε_star * (L : ℝ) := by
      calc β * (2 * (k : ℝ) * ((N_wall : ℝ) + 1) * (H_max : ℝ))
          ≤ β * (((max 1 (2 * k) : ℕ) : ℝ) * ((N_wall : ℝ) + 2) *
              (slabSmallExcursion c β k * (L : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul ?_ hH_le (Nat.cast_nonneg _) (by positivity)
            exact mul_le_mul h2k_le (by linarith only) (by positivity) hmax_pos.le
        _ = (1 / 4) * ε_star * (L : ℝ) := by
            unfold slabSmallExcursion
            change β * (((max 1 (2 * k) : ℕ) : ℝ) * ((N_wall : ℝ) + 2) *
              (ε_star / (4 * β * ((N_wall : ℝ) + 2) * ((max 1 (2 * k) : ℕ) : ℝ)) * (L : ℝ))) = _
            have hβ_ne : β ≠ 0 := by linarith only [hβ]
            have hN2_ne : (N_wall : ℝ) + 2 ≠ 0 := by positivity
            field_simp [hβ_ne, hN2_ne, hmax_pos.ne']
    exact (mul_le_mul_of_nonneg_left hcrR (by positivity)).trans hterm1
  have herr_rows : 3 * ((N_wall : ℝ) + 1) * (d : ℝ) * (b : ℝ) ≤ (3 / 20) * ε_star * (L : ℝ) := by
    have h20 : 20 * ((N_wall : ℝ) + 2) ≤ (d : ℝ) * ε_star := (div_le_iff₀ hε_pos).mp hd_20
    have hN1 : 20 * ((N_wall : ℝ) + 1) ≤ (d : ℝ) * ε_star := by linarith only [h20]
    have hdb_nn : (0 : ℝ) ≤ (d : ℝ) * (b : ℝ) := by positivity
    have hL_cast : (L : ℝ) = (d : ℝ) * (d : ℝ) * (b : ℝ) := by
      rw [hL_def]; push_cast; rfl
    have hmul : 20 * (3 * ((N_wall : ℝ) + 1) * (d : ℝ) * (b : ℝ)) ≤
        3 * (ε_star * (L : ℝ)) := by
      rw [hL_cast]
      calc 20 * (3 * ((N_wall : ℝ) + 1) * (d : ℝ) * (b : ℝ))
          = 3 * ((20 * ((N_wall : ℝ) + 1)) * ((d : ℝ) * (b : ℝ))) := by ring
        _ ≤ 3 * (((d : ℝ) * ε_star) * ((d : ℝ) * (b : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN1 hdb_nn) (by norm_num)
        _ = 3 * (ε_star * ((d : ℝ) * (d : ℝ) * (b : ℝ))) := by ring
    linarith only [hmul]
  -- Bound the main term `O_card / 2 - β * Γsl_card` in Case A vs Case B.
  have hmain_ge : 2 * ε_star * (L : ℝ) - (1 / 1600) * ε_star * (L : ℝ) ≤
      (O_card : ℝ) / 2 - β * (Γsl_card : ℝ) := by
    rcases hcases with ⟨hsl0, hO_short⟩ | hO_long
    · rw [hsl0, Nat.cast_zero, mul_zero, sub_zero]
      have hO_R : (L : ℝ) ≤ 2 * ((N_wall : ℝ) + 1) * (O_card : ℝ) := by exact_mod_cast hO_short
      have hN2_pos : (0 : ℝ) < 2 * ((N_wall : ℝ) + 1) := by positivity
      have hO_A : 4 * ε_star * (L : ℝ) ≤ (O_card : ℝ) := by
        have hlhs : 4 * ε_star * (L : ℝ) = (L : ℝ) / (2 * ((N_wall : ℝ) + 1)) := by
          show 4 * (1 / (8 * ((N_wall : ℝ) + 1))) * (L : ℝ) = _
          field_simp [hN2_pos.ne']
          ring
        rw [hlhs, div_le_iff₀ hN2_pos]
        linarith only [hO_R]
      have hnn : 0 ≤ (1 / 1600) * ε_star * (L : ℝ) := by positivity
      linarith only [hO_A, hnn]
    · have hT_101 : (T : ℝ) ≤ (101 / 100) * c * (L : ℝ) := by
        have hfl : (T : ℝ) ≤ c * ((L : ℝ) + 1) :=
          (Nat.cast_le.mpr hT_floor).trans (Nat.floor_le (by positivity))
        have hL100R : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
        have hL1 : (L : ℝ) + 1 ≤ (101 / 100) * (L : ℝ) := by linarith only [hL100R]
        calc (T : ℝ) ≤ c * ((L : ℝ) + 1) := hfl
          _ ≤ c * ((101 / 100) * (L : ℝ)) := mul_le_mul_of_nonneg_left hL1 (by positivity)
          _ = (101 / 100) * c * (L : ℝ) := by ring
      have hLhalf_R : (99 / 200) * (L : ℝ) ≤ ((L / 2 : ℕ) : ℝ) := by
        have hdiv2 : L ≤ 2 * (L / 2) + 1 := by omega
        have hdiv2R : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdiv2
        have hL100R : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
        linarith only [hdiv2R, hL100R]
      have hlongR : (L : ℝ) * ((L / 2 : ℕ) : ℝ) < 4 * (T : ℝ) * (O_card : ℝ) := by
        exact_mod_cast hO_long
      have hlhs_le : ((99 / 200) * (L : ℝ)) * (L : ℝ) ≤ (L : ℝ) * ((L / 2 : ℕ) : ℝ) := by
        calc ((99 / 200) * (L : ℝ)) * (L : ℝ) = (L : ℝ) * ((99 / 200) * (L : ℝ)) := by ring
          _ ≤ (L : ℝ) * ((L / 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hLhalf_R hL_posR.le
      have hrhs_le : 4 * (T : ℝ) * (O_card : ℝ) ≤
          ((404 / 100) * c * (O_card : ℝ)) * (L : ℝ) := by
        calc 4 * (T : ℝ) * (O_card : ℝ) = (4 * (O_card : ℝ)) * (T : ℝ) := by ring
          _ ≤ (4 * (O_card : ℝ)) * ((101 / 100) * c * (L : ℝ)) :=
              mul_le_mul_of_nonneg_left hT_101 (by positivity)
          _ = ((404 / 100) * c * (O_card : ℝ)) * (L : ℝ) := by ring
      have hchain : (99 / 200) * (L : ℝ) < (404 / 100) * c * (O_card : ℝ) :=
        lt_of_mul_lt_mul_right (lt_of_le_of_lt hlhs_le (lt_of_lt_of_le hlongR hrhs_le)) hL_posR.le
      have hO_B : (L : ℝ) / (10 * c) ≤ (O_card : ℝ) := by
        have h10c_pos : 0 < 10 * c := by positivity
        rw [div_le_iff₀ h10c_pos]
        have hchain' : (99 / 200) * (L : ℝ) < (404 / 1000) * ((O_card : ℝ) * (10 * c)) := by
          calc (99 / 200) * (L : ℝ) < (404 / 100) * c * (O_card : ℝ) := hchain
            _ = (404 / 1000) * ((O_card : ℝ) * (10 * c)) := by ring
        have hnn_Oc : 0 ≤ (O_card : ℝ) * (10 * c) := by positivity
        linarith only [hchain', hnn_Oc, hL_posR]
      have hslab_R : (Γsl_card : ℝ) ≤ (L : ℝ) / (80 * β * c) + 1 :=
        (Nat.cast_le.mpr hslab_le).trans (Nat.ceil_lt_add_one (div_nonneg hL_posR.le h80_pos.le)).le
      have hβ_slab : β * (Γsl_card : ℝ) ≤ (L : ℝ) / (80 * c) + β := by
        calc β * (Γsl_card : ℝ)
            ≤ β * ((L : ℝ) / (80 * β * c) + 1) :=
              mul_le_mul_of_nonneg_left hslab_R (by positivity)
          _ = (L : ℝ) / (80 * c) + β := by
              have hβ_ne : β ≠ 0 := by linarith only [hβ]
              field_simp [hβ_ne]
      have hβ_tiny : β ≤ (1 / 1600) * ε_star * (L : ℝ) := by
        have h1 : β ≤ β * ((N_wall : ℝ) + 2) := by
          have hN_nn : (0 : ℝ) ≤ (N_wall : ℝ) := Nat.cast_nonneg _
          calc β = β * 1 := by ring
            _ ≤ β * ((N_wall : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left (by linarith only [hN_nn]) (by positivity)
        exact h1.trans hβN_le
      have hNwall_gt : 160 * c < (N_wall : ℝ) + 1 := by
        have hc1 : 1 ≤ β * c := one_le_mul_of_one_le_of_one_le hβ hc
        have hc2 : 160 * c ≤ 160 * β * c ^ 2 := by
          calc 160 * c = (160 * c) * 1 := by ring
            _ ≤ (160 * c) * (β * c) := mul_le_mul_of_nonneg_left hc1 (by positivity)
            _ = 160 * β * c ^ 2 := by ring
        exact lt_of_le_of_lt hc2 (Nat.lt_floor_add_one _)
      have h2ε_le : 2 * ε_star ≤ 3 / (80 * c) := by
        show 2 * (1 / (8 * ((N_wall : ℝ) + 1))) ≤ 3 / (80 * c)
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith only [hNwall_gt]
      have h380 : 2 * ε_star * (L : ℝ) ≤ (3 / (80 * c)) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right h2ε_le hL_posR.le
      have hdiff_L : (L : ℝ) / (20 * c) - (L : ℝ) / (80 * c) = (3 / (80 * c)) * (L : ℝ) := by
        have hc_ne : c ≠ 0 := by linarith only [hc]
        field_simp [hc_ne]
        ring
      have hO_half : (L : ℝ) / (20 * c) ≤ (O_card : ℝ) / 2 := by
        have hc_ne : c ≠ 0 := by linarith only [hc]
        have heq : (L : ℝ) / (10 * c) / 2 = (L : ℝ) / (20 * c) := by field_simp [hc_ne]; ring
        linarith only [hO_B, heq]
      linarith only [hO_half, hβ_slab, hβ_tiny, h380, hdiff_L]
  have hΓ_R : β * (Γ_card : ℝ) ≤
      β * (Kall_card : ℝ) + β * (Γcr_card : ℝ) + β * (Γsl_card : ℝ) := by
    have h1 : (Γ_card : ℝ) ≤ (Kall_card : ℝ) + (Γcr_card : ℝ) + (Γsl_card : ℝ) := by
      exact_mod_cast hΓ_le
    calc β * (Γ_card : ℝ)
        ≤ β * ((Kall_card : ℝ) + (Γcr_card : ℝ) + (Γsl_card : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = β * (Kall_card : ℝ) + β * (Γcr_card : ℝ) + β * (Γsl_card : ℝ) := by ring
  have hεL_pos : 0 < ε_star * (L : ℝ) := mul_pos hε_pos hL_posR
  have hnet_ge : ε_star * (L : ℝ) ≤ (U_card : ℝ) - β * (Γ_card : ℝ) := by
    linarith only [hU_ge, hmain_ge, hΓ_R, herr_Kall, herr_cross, herr_rows, hεL_pos]
  have hβΓsl_nn : 0 ≤ β * (Γsl_card : ℝ) := mul_nonneg (by positivity) (Nat.cast_nonneg _)
  have hO_ge : 3 * ε_star * (L : ℝ) ≤ (O_card : ℝ) := by
    linarith only [hmain_ge, hβΓsl_nn, hεL_pos]
  exact ⟨hO_ge, hnet_ge⟩

/-- An oblivious linear-time transposer transposes at `(d, c)`, and its common trace halts at `T`
with probability `1 = 2^{-0 L}`. -/
private theorem obliviousLinTime_to_transposesAt_prob {M : TM} {d T : ℕ} {c : ℝ}
    (hoblT : ObliviousLinTime M d (entryBits d) c T) :
    TransposesAt M d c ∧
      (traceAt M (inputLength d)).haltTime = T ∧
      (2 : ℝ) ^ (-(0 : ℝ) * (inputLength d : ℝ)) ≤
        traceProb M (inputLength d) (traceAt M (inputLength d)) := by
  obtain ⟨hobl, hT, htr⟩ := hoblT
  let L := inputLength d
  have hL_eq : d * d * entryBits d = L := rfl
  have htrAt : TransposesAt M d c := by
    intro A
    obtain ⟨s, hs⟩ := htr A
    obtain ⟨s', _, hhalt_s', hout_s'⟩ := (computesWithin_iff _ _).mp hs
    have hhalt_T : HaltsAt M (encode d (entryBits d) A) T :=
      hobl.1 _ (length_encode d (entryBits d) A)
    have hs'T : s' = T := haltsAt_unique hhalt_s' hhalt_T
    rw [hs'T] at hout_s'
    exact (computesWithin_iff _ _).mpr ⟨T, Nat.le_floor hT, hhalt_T, hout_s'⟩
  let τ₀ : Trace M.k := traceAt M L
  have hhalt_zero : HaltsAt M (List.ofFn fun _ : Fin L => false) T :=
    hobl.1 _ List.length_ofFn
  have hτ₀_halts : τ₀.HaltsAt T := (haltsAt_iff_trace T).mp hhalt_zero
  have hT_eq : τ₀.haltTime = T :=
    (τ₀.haltsAt_haltTime ⟨T, hτ₀_halts.2⟩).unique hτ₀_halts
  have hfib_univ : fibre M L τ₀ = Finset.univ := by
    ext X
    simp only [mem_fibre, Finset.mem_univ, iff_true]
    have hf := followsTrace_of_obliviousOn (hL_eq ▸ hobl) (fun _ : Fin L => false) X
    have hhalt_X : HaltsAt M (List.ofFn X) T := hobl.1 _ List.length_ofFn
    funext t
    rcases lt_or_ge t T with ht | ht
    · exact hf t ht
    · have hnone1 : transAt M (List.ofFn X) t = none :=
        transAt_of_le_of_none hhalt_X.2 ht
      have hnone2 : transAt M (List.ofFn fun _ : Fin L => false) t = none :=
        transAt_of_le_of_none hhalt_zero.2 ht
      show trace M (List.ofFn X) t = trace M (List.ofFn fun _ : Fin L => false) t
      rw [(trace_eq_none_iff t).mpr hnone1, (trace_eq_none_iff t).mpr hnone2]
  have hprob1 : (2 : ℝ) ^ (-(0 : ℝ) * (L : ℝ)) ≤ traceProb M L τ₀ := by
    rw [neg_zero, zero_mul, Real.rpow_zero]
    unfold traceProb
    rw [hfib_univ, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (div_self (by positivity)).symm
  exact ⟨htrAt, hT_eq, hprob1⟩

/-! ## §7. Unconditional All-Machines Off-Carrier Vertex-Expansion Necessary Condition -/

/-- Lower endpoints `p ≤ θ` of revisit hops `(p, u)` (`p ≤ θ < u`) on `y` whose excursion is at
most `H` (`∀ t ∈ Ioo p u, |y t - y p| ≤ H`). -/
noncomputable def smallCrossingLowers (y : ℕ → ℤ) (T H θ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter fun p =>
    p ≤ θ ∧ ∃ u, θ < u ∧ IsHop y T p u ∧ ∀ t ∈ Finset.Ioo p u, |y t - y p| ≤ (H : ℤ)

/-- Without `θ` itself, `smallCrossingLowers y T H θ` has at most `2 * H` elements: a revisit
`(p, u)` with `p < θ < u` is away from its cell at step `θ`, so the later ends lie at distinct cells
within distance `H` of `y θ`, none of them at `y θ`. (The genie of Theorem H contains `θ` anyway.) -/
theorem card_smallCrossingLowers_erase_le (y : ℕ → ℤ) (T H θ : ℕ) :
    ((smallCrossingLowers y T H θ).erase θ).card ≤ 2 * H := by
  classical
  set P := (smallCrossingLowers y T H θ).erase θ
  let u_of : ℕ → ℕ := fun p =>
    if h : ∃ u, θ < u ∧ IsHop y T p u ∧ ∀ t ∈ Finset.Ioo p u, |y t - y p| ≤ (H : ℤ) then
      Classical.choose h
    else 0
  have hu_spec : ∀ p ∈ P,
      p < θ ∧ θ < u_of p ∧ IsHop y T p (u_of p) ∧
      ∀ t ∈ Finset.Ioo p (u_of p), |y t - y p| ≤ (H : ℤ) := by
    intro p hp
    obtain ⟨hpθ_ne, hp⟩ := Finset.mem_erase.mp hp
    obtain ⟨_, hpθ, hex⟩ := Finset.mem_filter.mp hp
    have hch := Classical.choose_spec hex
    simpa only [u_of, hex, ↓reduceDIte] using
      ⟨lt_of_le_of_ne hpθ hpθ_ne, hch.1, hch.2.1, hch.2.2⟩
  have hinj : Set.InjOn u_of (P : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨_, _, hh₁, _⟩ := hu_spec p₁ (Finset.mem_coe.mp hp₁)
    obtain ⟨_, _, hh₂, _⟩ := hu_spec p₂ (Finset.mem_coe.mp hp₂)
    change u_of p₁ = u_of p₂ at heq
    rw [← heq] at hh₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hh₁.2.2.2 p₂ (Finset.mem_Ioo.mpr ⟨hlt, by have := hh₂.1; omega⟩)
        (by have := hh₁.2.2.1; have := hh₂.2.2.1; omega)
    · exact hh₂.2.2.2 p₁ (Finset.mem_Ioo.mpr ⟨hgt, by have := hh₁.1; omega⟩)
        (by have := hh₁.2.2.1; have := hh₂.2.2.1; omega)
  let G := P.image u_of
  have hsub : G ⊆ crossingHops y T (θ + 1) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hpθ, hθu, hhop, _⟩ := hu_spec p hp
    unfold crossingHops
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhop.2.1, by omega, p, by omega, hhop⟩
  have hinj_y : Set.InjOn y (G : Set ℕ) :=
    (hop_upper_injOn y T (θ + 1)).mono (Finset.coe_subset.mpr hsub)
  -- Cells within distance `H` of `y θ`, other than `y θ`.
  let box : Finset ℤ :=
    ((Finset.range (2 * H + 1)).erase H).image fun i : ℕ => y θ - (H : ℤ) + (i : ℤ)
  have hbox : G.image y ⊆ box := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hpθ, hθu, hhop, hle_H⟩ := hu_spec p hp
    have hy_eq : y (u_of p) = y p := hhop.2.2.1
    have hθ_mem : θ ∈ Finset.Ioo p (u_of p) := Finset.mem_Ioo.mpr ⟨hpθ, hθu⟩
    have hne : y θ ≠ y p := hhop.2.2.2 θ hθ_mem
    have hex := abs_le.mp (hle_H θ hθ_mem)
    refine Finset.mem_image.mpr ⟨(y (u_of p) - (y θ - (H : ℤ))).toNat,
      Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr ?_⟩, ?_⟩ <;> omega
  calc P.card
      = G.card := (Finset.card_image_of_injOn hinj).symm
    _ = (G.image y).card := (Finset.card_image_of_injOn hinj_y).symm
    _ ≤ box.card := Finset.card_le_card hbox
    _ ≤ ((Finset.range (2 * H + 1)).erase H).card := Finset.card_image_le
    _ = 2 * H := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
        omega

/-- Unconditional spatial-injectivity bound `|smallCrossingLowers y T H θ| ≤ 2 * H + 1` on **any**
walk `y : ℕ → ℤ` (no global excursion bound on `y` required). -/
theorem card_smallCrossingLowers_le (y : ℕ → ℤ) (T H θ : ℕ) :
    (smallCrossingLowers y T H θ).card ≤ 2 * H + 1 := by
  have h1 := Finset.pred_card_le_card_erase (s := smallCrossingLowers y T H θ) (a := θ)
  have h2 := card_smallCrossingLowers_erase_le y T H θ
  omega

/-- **Intrinsic Off-Carrier `> H` Revisit Step Set** (defined from head motion alone):
lower endpoints `p < T` of revisit hops `(p, u)` on any head `j ∉ S_free` whose excursion exceeds `H`
(`∃ t ∈ Ioo p u, H < |xs j t - xs j p|`). -/
noncomputable def offCarrierLargeLowers {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (S_free : Finset (Fin k)) (T H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ \ S_free).biUnion fun j =>
    (Finset.range T).filter fun p =>
      ∃ u, IsHop (xs j) T p u ∧ ∃ t ∈ Finset.Ioo p u, (H : ℤ) < |xs j t - xs j p|

/-- **Literal Menger Vertex Separator Predicate**:
`B` disconnects `Src` from `Dst` in `DepStep xs T` if every dependency path starting at `t₀ ∈ Src`
and ending in `Dst` meets `B` (whether at the root `t₀`, an internal vertex, or the endpoint). -/
def IsMengerVertexCut {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (Src Dst B : Finset ℕ) : Prop :=
  ∀ (π : List ℕ) (t₀ : ℕ), t₀ ∈ Src → IsDepPath xs T (t₀ :: π) →
    (t₀ :: π).getLastD t₀ ∈ Dst → ∃ v ∈ t₀ :: π, v ∈ B

/-- Small-hop slab genie `K_all ∪ Γ_small_cross ∪ Γ_slab` using only `≤ H`-excursion crossers. -/
noncomputable def slabSmallChunkGenie {k : ℕ} (xs : Fin k → ℕ → ℤ) (S_free : Finset (Fin k))
    (x_free : ℕ → ℤ) (W u_off T H t_start : ℕ) (m_star : ℤ) : Finset ℕ := by
  classical
  let K := slabTransitions x_free W T u_off
  let K_all := if t_start = 0 then K else insert (t_start - 1) K
  let Γ_small := (Finset.univ \ S_free).biUnion fun j =>
    K_all.biUnion fun θ => smallCrossingLowers (xs j) T H θ
  let Γ_slab := slabEntryGenie x_free W u_off m_star t_start
  exact K_all ∪ Γ_small ∪ Γ_slab

private theorem depStep_trapped_or_largeLower {k : ℕ} {xs : Fin k → ℕ → ℤ}
    {S_free : Finset (Fin k)} {x_free : ℕ → ℤ} (hfree_eq : ∀ i ∈ S_free, xs i = x_free)
    {W u_off T H t_start t_end : ℕ} (hW : 1 ≤ W) (hend : t_end ≤ T) {m_star : ℤ} {a b : ℕ}
    (ha : a ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star))
    (hstep : DepStep xs T a b)
    (hb_not : b ∉ slabSmallChunkGenie xs S_free x_free W u_off T H t_start m_star) :
    b ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star) ∨
      b ∈ offCarrierLargeLowers xs S_free T H := by
  classical
  by_cases hb_full : b ∈ slabChunkGenie xs S_free x_free W u_off T t_start m_star
  · right
    unfold slabChunkGenie at hb_full
    unfold slabSmallChunkGenie at hb_not
    rcases Finset.mem_union.mp hb_full with hKcr | hsl
    · rcases Finset.mem_union.mp hKcr with hK | hcr
      · exfalso
        exact hb_not (Finset.mem_union_left _ (Finset.mem_union_left _ hK))
      · obtain ⟨j, hj, hθb⟩ := Finset.mem_biUnion.mp hcr
        obtain ⟨θ, hθ, hb_cl⟩ := Finset.mem_biUnion.mp hθb
        have hb_not_sm : b ∉ smallCrossingLowers (xs j) T H θ := fun hsm =>
          hb_not (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_biUnion.mpr ⟨θ, hθ, hsm⟩⟩)))
        unfold crossingLowers at hb_cl
        obtain ⟨hbT, hbθ, u, hθu, hhop⟩ := Finset.mem_filter.mp hb_cl
        have hnot_le : ¬ ∀ t ∈ Finset.Ioo b u, |xs j t - xs j b| ≤ (H : ℤ) := fun hall =>
          hb_not_sm (Finset.mem_filter.mpr ⟨hbT, hbθ, u, hθu, hhop, hall⟩)
        push Not at hnot_le
        obtain ⟨t, ht, hgt⟩ := hnot_le
        unfold offCarrierLargeLowers
        exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hbT, u, hhop, t, ht, hgt⟩⟩
    · exfalso
      exact hb_not (Finset.mem_union_right _ hsl)
  · exact Or.inl (depStep_trapped_in_chunk hfree_eq hW hend ha hstep hb_full)

private def AvoidsDstFrom {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (Dst B : Finset ℕ) (a : ℕ) :
    Prop :=
  a ∉ B ∧ ∀ π : List ℕ, IsDepPath xs T (a :: π) → LinNet.GFree B (a :: π) →
    (a :: π).getLastD a ∉ Dst

private theorem avoidsDstFrom_step {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} {Dst B : Finset ℕ}
    {a b : ℕ} (ha : AvoidsDstFrom xs T Dst B a) (hstep : DepStep xs T a b) (hbB : b ∉ B) :
    AvoidsDstFrom xs T Dst B b := by
  refine ⟨hbB, fun ρ hpath hfree => ?_⟩
  have hpath' : IsDepPath xs T (a :: b :: ρ) := ⟨hstep, hpath⟩
  have hfree' : LinNet.GFree B (a :: b :: ρ) := gfree_cons_cons.mpr ⟨hbB, hfree⟩
  have hnot := ha.2 (b :: ρ) hpath' hfree'
  rwa [LinNet.getLastD_cons_cons] at hnot

private theorem depPath_trapped_of_avoidsDst {k : ℕ} {xs : Fin k → ℕ → ℤ}
    {S_free : Finset (Fin k)} {x_free : ℕ → ℤ} (hfree_eq : ∀ i ∈ S_free, xs i = x_free)
    {W u_off T H t_start t_end : ℕ} (hW : 1 ≤ W) (hend : t_end ≤ T) {m_star : ℤ} {B : Finset ℕ} :
    ∀ (π : List ℕ) (t₀ : ℕ),
      t₀ ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star) →
      AvoidsDstFrom xs T (offCarrierLargeLowers xs S_free T H) B t₀ →
      IsDepPath xs T (t₀ :: π) →
      LinNet.GFree (slabSmallChunkGenie xs S_free x_free W u_off T H t_start m_star ∪ B) (t₀ :: π) →
      ∀ v ∈ t₀ :: π,
        v ∈ (Finset.Ico t_start t_end).filter (fun t => slabIdx W u_off (x_free t) = m_star)
  | [], t₀, ht₀, _, _, _ => fun v hv => by
      simp only [List.mem_singleton] at hv
      rwa [hv]
  | t₁ :: ρ, t₀, ht₀, hav, ⟨hstep, htail⟩, hfree => by
      obtain ⟨ht₁_not, hfree'⟩ := gfree_cons_cons.mp hfree
      have ht₁_not_sm : t₁ ∉ slabSmallChunkGenie xs S_free x_free W u_off T H t_start m_star :=
        fun h => ht₁_not (Finset.mem_union_left B h)
      have ht₁_not_B : t₁ ∉ B := fun h => ht₁_not (Finset.mem_union_right _ h)
      have hav₁ := avoidsDstFrom_step hav hstep ht₁_not_B
      rcases depStep_trapped_or_largeLower hfree_eq hW hend ht₀ hstep ht₁_not_sm with ht₁_in | hdst
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact ht₀
        · exact depPath_trapped_of_avoidsDst hfree_eq hW hend ρ t₁ ht₁_in hav₁ htail hfree' v hv'
      · exfalso
        exact hav₁.2 [] trivial (by simp [LinNet.GFree]) hdst

/-- **Theorem H(c) (`offCarrier_vertexExpansion_of_linearTimeTransposer`, Unconditional All-Machines
Off-Carrier Vertex-Expansion Necessary Condition — Low-Adaptivity Form)**:
Fix `c ≥ 1`, `β ≥ 1`, and `k : ℕ`. For **every** machine `M : TM` with `M.k ≤ k` and
`(valueWidth M : ℝ) ≤ β`, **every** adaptivity rate `η < slabAutonomyEps c β`, **every**
`d ≥ slabDimThreshold c β` with `TransposesAt M d c`, **every** trace `τ₀` of probability
`≥ 2^{-η L}`, **every** excluded carrier head set `S_free` of size `≤ 1`, and **every** excursion
threshold `H ≤ ⌊slabSmallExcursion c β k * L⌋₊` (in particular `H = 2 * W` for large `d`), there
exists an output subpopulation `V_* ⊆ Fin L` of size `3 * ε_* L ≤ |V_*| ≤ L / 2` such that **every**
Menger vertex cut `B` disconnecting `V_*`'s output steps `Src_*` from
`offCarrierLargeLowers τ₀.work S_free τ₀.haltTime H` satisfies
`(slabAutonomyEps c β - η) * L ≤ β * |B| + |B ∩ Src_*|` (so `β * |B| ≥ (ε_* - η) * L` whenever `B`
is disjoint from `Src_*`, and `(β + 1) * |B| ≥ (ε_* - η) * L` unconditionally). -/
theorem offCarrier_vertexExpansion_of_linearTimeTransposer {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {η : ℝ} {d : ℕ} (hd : slabDimThreshold c β ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀)
    (S_free : Finset (Fin M.k)) (hS_card : S_free.card ≤ 1)
    {H : ℕ} (hH : H ≤ ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊) :
    let b := entryBits d
    let L := d * d * b
    let ot : Fin L → ℕ := fun r => appendTime τ₀ τ₀.haltTime r.1
    ∃ V_star : Finset (Fin L),
      3 * slabAutonomyEps c β * (L : ℝ) ≤ (V_star.card : ℝ) ∧
      V_star.card ≤ L / 2 ∧
      ∀ B : Finset ℕ,
        let Src := (V_star.image (tposOf d b)).image ot
        IsMengerVertexCut τ₀.work τ₀.haltTime Src
          (offCarrierLargeLowers τ₀.work S_free τ₀.haltTime H) B →
        (slabAutonomyEps c β - η) * (L : ℝ) ≤ β * (B.card : ℝ) + ((B ∩ Src).card : ℝ) := by
  classical
  have hd10 : 10 ≤ d := (ten_le_slabDimThreshold c β).trans hd
  have hd1 : 1 ≤ d := by omega
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  let b := entryBits d
  let L := d * d * b
  obtain ⟨hT_floor, _, hT_2c, hot_mono, hot_lt, hsub⟩ :=
    frozenTrace_subpop_deficit_le hd1 hvw htr hprob
  have hex_free : ∃ x_free : ℕ → ℤ, IsWalk x_free ∧ ∀ i ∈ S_free, τ₀.work i = x_free := by
    by_cases hSne : S_free.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hSne
      refine ⟨τ₀.work i₀, τ₀.work_isWalk i₀, fun i hi => ?_⟩
      rw [Finset.card_le_one.mp hS_card i hi i₀ hi₀]
    · rw [Finset.not_nonempty_iff_eq_empty] at hSne
      refine ⟨fun _ => 0, fun _ => by simp, fun i hi => ?_⟩
      rw [hSne] at hi; simp at hi
  obtain ⟨x_free, hx_free, hfree_eq⟩ := hex_free
  let W_cut := ⌈((L : ℕ) : ℝ) / (80 * β * c)⌉₊
  have hW_pos : 1 ≤ W_cut := by
    have h80_pos : 0 < 80 * β * c := by positivity
    have hd_80 : 80 * β * c ≤ (d : ℝ) :=
      (eighty_mul_le_slabDimThreshold hc hβ).trans (by exact_mod_cast hd)
    have hd_le_L : (d : ℝ) ≤ (L : ℝ) := by
      have : d ≤ d * d * b := by
        calc d = d * 1 * 1 := by ring
          _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) hb1
      exact_mod_cast this
    have h1 : (1 : ℝ) ≤ (L : ℝ) / (80 * β * c) :=
      (le_div_iff₀ h80_pos).mpr (by simpa only [one_mul] using hd_80.trans hd_le_L)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  obtain ⟨u_star, _, hK_div⟩ := exists_offset_slabTransitions_le hx_free hW_pos τ₀.haltTime
  let K := slabTransitions x_free W_cut τ₀.haltTime u_star
  let m : ℕ → ℤ := fun t => slabIdx W_cut u_star (x_free t)
  have hK_mem : ∀ t < τ₀.haltTime - 1, m t ≠ m (t + 1) → t ∈ K := fun t ht hne =>
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hne⟩
  have hK_le_Nwall : K.card ≤ slabWallCap c β :=
    hK_div.trans (slab_wall_cap_bound hc hβ (Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1) hT_2c)
  let ot : Fin L → ℕ := fun r => appendTime τ₀ τ₀.haltTime r.1
  have hex_chunk : ∃ (m_star : ℤ) (t_start t_end : ℕ),
      t_end ≤ τ₀.haltTime ∧
      ((Finset.Ico t_start t_end).filter (fun t => m t = m_star)).card ≤ L / 2 ∧
      ((t_start = 0 ∧ L ≤ 2 * (slabWallCap c β + 1) *
          (outIn ot ((Finset.Ico t_start t_end).filter (fun t => m t = m_star))).card) ∨
        L * (L / 2) < 4 * τ₀.haltTime *
          (outIn ot ((Finset.Ico t_start t_end).filter (fun t => m t = m_star))).card) := by
    have hL2 : 2 ≤ L := by
      calc 2 ≤ 10 * 10 * 1 := by norm_num
        _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul hd10 hd10) hb1
    rcases exists_slab_chunk_dichotomy hL2 hK_mem hot_lt with
      ⟨m_star, hC_half, hO_short⟩ | ⟨m_star, t_start, t_end, _, hend_T, hC_half, hO_long⟩
    · refine ⟨m_star, 0, τ₀.haltTime, le_rfl, hC_half, Or.inl ⟨rfl, ?_⟩⟩
      exact hO_short.trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hK_le_Nwall 1)))
    · exact ⟨m_star, t_start, t_end, hend_T, hC_half, Or.inr hO_long⟩
  obtain ⟨m_star, t_start, t_end, hend_T, hC_half, hO_cases⟩ := hex_chunk
  let C_star := (Finset.Ico t_start t_end).filter (fun t => m t = m_star)
  have hCT : ∀ t ∈ C_star, t < τ₀.haltTime := fun t ht =>
    (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2.trans_le hend_T
  let O_star := outIn ot C_star
  let V_star := O_star.image (tposOf d b)
  have htpos_inj : Function.Injective (tposOf d b) := Function.Involutive.injective (tposOf_tposOf d b)
  have hV_card_eq : V_star.card = O_star.card := Finset.card_image_of_injective O_star htpos_inj
  have hO_le_C : O_star.card ≤ C_star.card := by
    calc O_star.card
        = (O_star.image ot).card := (Finset.card_image_of_injective O_star hot_mono.injective).symm
      _ ≤ C_star.card := Finset.card_le_card fun t ht => by
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
          exact (Finset.mem_filter.mp hr).2
  -- Bound the small-crosser genie `Γ₀` and `U_*`.
  let Γ₀ := slabSmallChunkGenie τ₀.work S_free x_free W_cut u_star τ₀.haltTime H t_start m_star
  let K_all := if t_start = 0 then K else insert (t_start - 1) K
  let Γ_small := (Finset.univ \ S_free).biUnion fun j =>
    K_all.biUnion fun θ => smallCrossingLowers (τ₀.work j) τ₀.haltTime H θ
  let Γ_slab := slabEntryGenie x_free W_cut u_star m_star t_start
  let H_max := ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊
  -- The walls `θ ∈ K_all` are already in `Γ₀`; the other crossers number `≤ 2 H` per head and wall.
  let Γ_cross := (Finset.univ \ S_free).biUnion fun j =>
    K_all.biUnion fun θ => (smallCrossingLowers (τ₀.work j) τ₀.haltTime H θ).erase θ
  have hKall_le : K_all.card ≤ slabWallCap c β + 1 := by
    dsimp [K_all]
    split_ifs
    · exact hK_le_Nwall.trans (Nat.le_succ _)
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hK_le_Nwall 1)
  have hcross_le : Γ_cross.card ≤ k * (slabWallCap c β + 1) * (2 * H_max) := by
    have hcard_j : (Finset.univ \ S_free).card ≤ k :=
      ((Finset.univ \ S_free).card_le_univ.trans_eq (Fintype.card_fin M.k)).trans hMk
    have h2H : 2 * H ≤ 2 * H_max := by omega
    calc Γ_cross.card
        ≤ ∑ j ∈ Finset.univ \ S_free,
            (K_all.biUnion fun θ =>
              (smallCrossingLowers (τ₀.work j) τ₀.haltTime H θ).erase θ).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.univ \ S_free,
            ∑ θ ∈ K_all, ((smallCrossingLowers (τ₀.work j) τ₀.haltTime H θ).erase θ).card :=
          Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.univ \ S_free, ∑ _θ ∈ K_all, 2 * H_max :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun θ _ =>
            (card_smallCrossingLowers_erase_le (τ₀.work j) τ₀.haltTime H θ).trans h2H
      _ = (Finset.univ \ S_free).card * (K_all.card * (2 * H_max)) := by
          simp [Finset.sum_const, smul_eq_mul]
      _ ≤ k * ((slabWallCap c β + 1) * (2 * H_max)) :=
          Nat.mul_le_mul hcard_j (Nat.mul_le_mul_right _ hKall_le)
      _ = k * (slabWallCap c β + 1) * (2 * H_max) := (Nat.mul_assoc _ _ _).symm
  have hslab_le : Γ_slab.card ≤ W_cut :=
    card_slabEntryGenie_le x_free W_cut u_star m_star t_start
  have hΓ₀_le : Γ₀.card ≤ K_all.card + Γ_cross.card + Γ_slab.card := by
    have hsub : Γ₀ ⊆ K_all ∪ Γ_cross ∪ Γ_slab := by
      intro t ht
      change t ∈ K_all ∪ Γ_small ∪ Γ_slab at ht
      rcases Finset.mem_union.mp ht with hKs | hsl
      · rcases Finset.mem_union.mp hKs with hK | hs
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hK)
        · obtain ⟨j, hj, hjt⟩ := Finset.mem_biUnion.mp hs
          obtain ⟨θ, hθ, htθ⟩ := Finset.mem_biUnion.mp hjt
          by_cases hteq : t = θ
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hteq ▸ hθ))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨j, hj, Finset.mem_biUnion.mpr ⟨θ, hθ, Finset.mem_erase.mpr ⟨hteq, htθ⟩⟩⟩))
      · exact Finset.mem_union_right _ hsl
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcases_sl : (Γ_slab.card = 0 ∧ L ≤ 2 * (slabWallCap c β + 1) * O_star.card) ∨
      L * (L / 2) < 4 * τ₀.haltTime * O_star.card := by
    rcases hO_cases with ⟨hts0, hA⟩ | hB
    · refine Or.inl ⟨?_, hA⟩
      dsimp [Γ_slab]
      rw [hts0, slabEntryGenie_zero]; rfl
    · exact Or.inr hB
  have hs_le : (runStarts C_star).card ≤ slabWallCap c β + 1 :=
    (card_runStarts_chunk_le hend_T hK_mem).trans (Nat.add_le_add_right hK_le_Nwall 1)
  let U_star := V_star \ inCells L τ₀.input C_star
  have hcov_U := outIn_card_le_two_indep_add_six_runs hd1 hb1 τ₀.abs_input_succ_sub_le
    hot_mono hCT hC_half
  obtain ⟨hO_ge, hnet_ge⟩ := slab_step4_net_ge hc hβ hd hb1 hT_floor hKall_le hcross_le hslab_le
    hΓ₀_le hs_le hcov_U hcases_sl
  refine ⟨V_star, hO_ge.trans_eq (by exact_mod_cast hV_card_eq.symm),
    hV_card_eq.trans_le (hO_le_C.trans hC_half), fun B hcut => ?_⟩
  let Src := (V_star.image (tposOf d b)).image ot
  have hV_img : V_star.image (tposOf d b) = O_star := by
    ext r
    simp only [V_star, Finset.mem_image]
    constructor
    · rintro ⟨q, ⟨r', hr', rfl⟩, rfl⟩
      rwa [tposOf_tposOf]
    · intro hr
      exact ⟨tposOf d b r, ⟨r, hr, rfl⟩, tposOf_tposOf d b r⟩
  have hSrc_eq : Src = O_star.image ot := by
    dsimp [Src]
    rw [hV_img]
  let O_surv := O_star.filter fun r => ot r ∉ B
  let U_surv := O_surv.image (tposOf d b) \ inCells L τ₀.input C_star
  have htrap_surv : ∀ (π : List ℕ) (t₀ : ℕ), t₀ ∈ O_surv.image ot →
      IsDepPath τ₀.work τ₀.haltTime (t₀ :: π) →
      LinNet.GFree (Γ₀ ∪ B) (t₀ :: π) → ∀ v ∈ t₀ :: π, v ∈ C_star := by
    intro π t₀ ht₀ hpath hfree
    obtain ⟨r, hr_surv, rfl⟩ := Finset.mem_image.mp ht₀
    obtain ⟨hr_O, hot_notB⟩ := Finset.mem_filter.mp hr_surv
    have hot_C : ot r ∈ C_star := (Finset.mem_filter.mp hr_O).2
    have hav : AvoidsDstFrom τ₀.work τ₀.haltTime
        (offCarrierLargeLowers τ₀.work S_free τ₀.haltTime H) B (ot r) := by
      refine ⟨hot_notB, fun ρ hp hf hdst => ?_⟩
      have hot_Src : ot r ∈ Src := hSrc_eq.symm ▸ Finset.mem_image_of_mem ot hr_O
      obtain ⟨v, hv_mem, hvB⟩ := hcut ρ (ot r) hot_Src hp hdst
      rcases List.mem_cons.mp hv_mem with rfl | hv_tail
      · exact hot_notB hvB
      · exact hf v hv_tail hvB
    exact depPath_trapped_of_avoidsDst hfree_eq hW_pos hend_T π (ot r) hot_C hav hpath hfree
  have hdef_surv := hsub C_star (Γ₀ ∪ B) O_surv htrap_surv
  -- Relate `U_star.card` to `U_surv.card + (B ∩ Src).card`.
  have hU_diff_le : U_star.card ≤ U_surv.card + (B ∩ Src).card := by
    let O_cut := O_star.filter fun r => ot r ∈ B
    have hcov : U_star ⊆ U_surv ∪ O_cut.image (tposOf d b) := by
      intro q hq
      obtain ⟨hqV, hq_nin⟩ := Finset.mem_sdiff.mp hq
      obtain ⟨r, hrO, rfl⟩ := Finset.mem_image.mp hqV
      by_cases hrb : ot r ∈ B
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hrO, hrb⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hrO, hrb⟩), hq_nin⟩)
    have hOcut_le : (O_cut.image (tposOf d b)).card ≤ (B ∩ Src).card := by
      calc (O_cut.image (tposOf d b)).card
          = O_cut.card := Finset.card_image_of_injective O_cut htpos_inj
        _ = (O_cut.image ot).card := (Finset.card_image_of_injective O_cut hot_mono.injective).symm
        _ ≤ (B ∩ Src).card := Finset.card_le_card fun t ht => by
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
            obtain ⟨hrO, hrb⟩ := Finset.mem_filter.mp hr
            exact Finset.mem_inter.mpr ⟨hrb, hSrc_eq.symm ▸ Finset.mem_image_of_mem ot hrO⟩
    exact (Finset.card_le_card hcov).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left hOcut_le _))
  have hΓB_le : ((Γ₀ ∪ B).card : ℝ) ≤ (Γ₀.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast Finset.card_union_le Γ₀ B
  have hU_R : (U_star.card : ℝ) ≤ (U_surv.card : ℝ) + ((B ∩ Src).card : ℝ) := by
    exact_mod_cast hU_diff_le
  have hβΓB : β * ((Γ₀ ∪ B).card : ℝ) ≤ β * (Γ₀.card : ℝ) + β * (B.card : ℝ) := by
    calc β * ((Γ₀ ∪ B).card : ℝ)
        ≤ β * ((Γ₀.card : ℝ) + (B.card : ℝ)) := mul_le_mul_of_nonneg_left hΓB_le (by positivity)
      _ = β * (Γ₀.card : ℝ) + β * (B.card : ℝ) := mul_add _ _ _
  linarith only [hnet_ge, hdef_surv, hU_R, hβΓB]

/-- **Theorem H(c) (`offCarrier_vertexExpansion_of_obliviousLinTime`, Unconditional All-Machines
Off-Carrier Vertex-Expansion Necessary Condition — Oblivious Form)**:
Every oblivious linear-time transposer (`ObliviousLinTime M d (entryBits d) c T`) with `M.k ≤ k` and
`(valueWidth M : ℝ) ≤ β` has, for **every** excluded carrier set `S_free` (`S_free.card ≤ 1`) and
**every** threshold `H ≤ ⌊slabSmallExcursion c β k * L⌋₊` (including `H = 2 * W` for large `d`), an
output subpopulation `V_* ⊆ Fin L` of size `3 * ε_* L ≤ |V_*| ≤ L / 2` such that **every** Menger
vertex separator `B` disconnecting `V_*`'s output steps `Src_*` from
`offCarrierLargeLowers (traceAt M L).work S_free T H` satisfies
`slabAutonomyEps c β * L ≤ β * |B| + |B ∩ Src_*|` (hence `(β + 1) * |B| ≥ slabAutonomyEps c β * L`
for arbitrary `B`, and `β * |B| ≥ slabAutonomyEps c β * L` when `Disjoint B Src_*`). -/
theorem offCarrier_vertexExpansion_of_obliviousLinTime {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {d : ℕ} (hd : slabDimThreshold c β ≤ d) {T : ℕ}
    (hobl : ObliviousLinTime M d (entryBits d) c T)
    (S_free : Finset (Fin M.k)) (hS_card : S_free.card ≤ 1)
    {H : ℕ} (hH : H ≤ ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊) :
    let b := entryBits d
    let L := d * d * b
    let τ₀ := traceAt M (inputLength d)
    let ot : Fin L → ℕ := fun r => appendTime τ₀ T r.1
    ∃ V_star : Finset (Fin L),
      3 * slabAutonomyEps c β * (L : ℝ) ≤ (V_star.card : ℝ) ∧
      V_star.card ≤ L / 2 ∧
      ∀ B : Finset ℕ,
        let Src := (V_star.image (tposOf d b)).image ot
        IsMengerVertexCut τ₀.work T Src (offCarrierLargeLowers τ₀.work S_free T H) B →
        slabAutonomyEps c β * (L : ℝ) ≤ β * (B.card : ℝ) + ((B ∩ Src).card : ℝ) := by
  obtain ⟨htrAt, hT_eq, hprob1⟩ := obliviousLinTime_to_transposesAt_prob hobl
  obtain ⟨V_star, hV_lo, hV_hi, hsep⟩ :=
    offCarrier_vertexExpansion_of_linearTimeTransposer hc hβ k M hMk hvw hd htrAt hprob1
      S_free hS_card hH
  refine ⟨V_star, hV_lo, hV_hi, fun B hcut => ?_⟩
  have h1 := hsep B (by simpa only [hT_eq] using hcut)
  simpa only [hT_eq, sub_zero] using h1

/-! ## §8. Theorem 4.1 (Theorem H) (a) and (b) from Theorem H(c), and Corollary 4.2 -/

/-- **Theorem 4.1 (Theorem H)**:
Fix `c ≥ 1`, `β ≥ 1`, and `k : ℕ`. For every machine `M : TM` with `M.k ≤ k` and
`(valueWidth M : ℝ) ≤ β`, every adaptivity rate `η < slabAutonomyEps c β`, and every dimension
`d ≥ slabDimThreshold c β`, `M` cannot simultaneously satisfy `TransposesAt M d c` and possess a
trace `τ₀` of probability `≥ 2^{-η L}` on which all work heads outside a set `S_free` of size `≤ 1`
have hop excursion at most `⌊slabSmallExcursion c β k * L⌋₊` (`τ₀.input` and `S_free` unrestricted).
A corollary of Theorem H(c) at `H = ⌊slabSmallExcursion c β k * L⌋₊`: the target set is empty, so
`B = ∅` separates, and `(slabAutonomyEps c β - η) * L ≤ 0` contradicts `η < slabAutonomyEps c β`. -/
theorem oneFreeHead_smallExcursion_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) (k : ℕ) :
    ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β →
      ∀ η < slabAutonomyEps c β, ∀ d ≥ slabDimThreshold c β,
        ¬ (TransposesAt M d c ∧
          ∃ (τ₀ : Trace M.k) (S_free : Finset (Fin M.k)),
            (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀ ∧
            S_free.card ≤ 1 ∧
            ∀ j : Fin M.k, j ∉ S_free →
              HopExcursionLEOn (τ₀.work j) 0 τ₀.haltTime
                ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊) := by
  classical
  intro M hMk hvw η hη d hd ⟨htr, τ₀, S_free, hprob, hS_card, hhop_small⟩
  obtain ⟨V_star, _, _, hsep⟩ := offCarrier_vertexExpansion_of_linearTimeTransposer hc hβ k M hMk
    hvw hd htr hprob S_free hS_card (H := ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊) le_rfl
  -- Every work head outside `S_free` keeps its excursions small, so the target set is empty.
  have hempty : offCarrierLargeLowers τ₀.work S_free τ₀.haltTime
      ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊ = ∅ := by
    unfold offCarrierLargeLowers
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨-, u, hhop, t, ht, hgt⟩ := Finset.mem_filter.mp hpj
    obtain ⟨hpt, htu⟩ := Finset.mem_Ioo.mp ht
    have hle := hhop_small j (Finset.mem_sdiff.mp hj).2 p u (Nat.zero_le p) hhop.2.1 hhop t hpt htu
    omega
  -- Hence `B = ∅` separates, and Theorem H(c) gives `(ε_* - η) L ≤ 0`.
  have h0 := hsep ∅ fun π t₀ _ _ hdst => by
    rw [hempty] at hdst
    exact absurd hdst (Finset.notMem_empty _)
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, Finset.empty_inter, add_zero] at h0
  have hd1 : 1 ≤ d := le_trans (by norm_num) ((ten_le_slabDimThreshold c β).trans hd)
  have hL : (0 : ℝ) < ((d * d * entryBits d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  nlinarith

/-! ### Two-Macroscopic-Heads Contrapositive (Theorem 4.1 / Theorem H) -/

/-- Walk `y` makes a completed hop `(p, u)` strictly before `T` (`IsHop y T p u`) whose interior
spatial excursion `|(y t : ℝ) - (y p : ℝ)|` at some step `t ∈ (p, u)` strictly exceeds `B`. -/
def HasHopExcursionGT (y : ℕ → ℤ) (T : ℕ) (B : ℝ) : Prop :=
  ∃ p u : ℕ, u < T ∧ IsHop y T p u ∧ ∃ t : ℕ, p < t ∧ t < u ∧ B < |(y t : ℝ) - (y p : ℝ)|

/-- Equivalence between `HasHopExcursionGT y T B` and `¬ HopExcursionLEOn y 0 T ⌊B⌋₊` for `0 ≤ B`. -/
theorem hasHopExcursionGT_iff_not_hopExcursionLEOn {y : ℕ → ℤ} {T : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    HasHopExcursionGT y T B ↔ ¬ HopExcursionLEOn y 0 T ⌊B⌋₊ := by
  constructor
  · rintro ⟨p, u, huT, hhop, t, hpt, htu, hgt⟩ hLE
    have hle_z : |y t - y p| ≤ (⌊B⌋₊ : ℤ) := hLE p u (Nat.zero_le p) huT hhop t hpt htu
    have hle_r : |(y t : ℝ) - (y p : ℝ)| ≤ (⌊B⌋₊ : ℝ) := by
      have hcast : ((|y t - y p| : ℤ) : ℝ) ≤ ((⌊B⌋₊ : ℤ) : ℝ) := by exact_mod_cast hle_z
      simpa only [Int.cast_abs, Int.cast_sub, Int.cast_natCast] using hcast
    exact not_le_of_gt hgt (hle_r.trans (Nat.floor_le hB))
  · intro hnot
    unfold HopExcursionLEOn at hnot
    push Not at hnot
    obtain ⟨p, u, _, huT, hhop, t, hpt, htu, hlt_z⟩ := hnot
    refine ⟨p, u, huT, hhop, t, hpt, htu, ?_⟩
    have hn_eq : ((y t - y p).natAbs : ℤ) = |y t - y p| := Int.natCast_natAbs _
    have hlt_n : ⌊B⌋₊ < (y t - y p).natAbs := by
      exact_mod_cast hlt_z.trans_eq hn_eq.symm
    have hlt_r : B < ((y t - y p).natAbs : ℝ) := (Nat.floor_lt hB).mp hlt_n
    have hr_eq : ((y t - y p).natAbs : ℝ) = |(y t : ℝ) - (y p : ℝ)| := by
      have hcast : (((y t - y p).natAbs : ℤ) : ℝ) = ((|y t - y p| : ℤ) : ℝ) :=
        congrArg Int.cast hn_eq
      simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using hcast
    exact hlt_r.trans_eq hr_eq

/-- **Theorem 4.1 (Theorem H, two-macroscopic-heads lower bound, low-adaptivity form)**:
every linear-time transposer (`TransposesAt M d c`) with `M.k ≤ k`, `(valueWidth M : ℝ) ≤ β`, and
a trace `τ₀` of probability `≥ 2^{-η L}` (`η < slabAutonomyEps c β`) has, for all
`d ≥ slabDimThreshold c β`, **at least two distinct work heads** that each make a completed hop
of spatial excursion strictly greater than `slabSmallExcursion c β k * L`. -/
theorem twoMacroscopicHeads_of_linearTimeTransposer {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {η : ℝ} (hη : η < slabAutonomyEps c β)
    {d : ℕ} (hd : slabDimThreshold c β ≤ d)
    (htr : TransposesAt M d c)
    {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀) :
    ∃ j₁ j₂ : Fin M.k, j₁ ≠ j₂ ∧
      HasHopExcursionGT (τ₀.work j₁) τ₀.haltTime
        (slabSmallExcursion c β k * (inputLength d : ℝ)) ∧
      HasHopExcursionGT (τ₀.work j₂) τ₀.haltTime
        (slabSmallExcursion c β k * (inputLength d : ℝ)) := by
  classical
  let B : ℝ := slabSmallExcursion c β k * (inputLength d : ℝ)
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg (slabSmallExcursion_pos (by positivity) k).le (Nat.cast_nonneg _)
  let S_free : Finset (Fin M.k) :=
    Finset.univ.filter fun j => ¬ HopExcursionLEOn (τ₀.work j) 0 τ₀.haltTime ⌊B⌋₊
  have hcard : 1 < S_free.card := by
    by_contra hle
    push Not at hle
    refine oneFreeHead_smallExcursion_excludes hc hβ k M hMk hvw η hη d hd
      ⟨htr, τ₀, S_free, hprob, hle, fun j hj => ?_⟩
    by_contra hnot
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnot⟩)
  obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨j₁, j₂, hne,
    (hasHopExcursionGT_iff_not_hopExcursionLEOn hB_nonneg).mpr (Finset.mem_filter.mp hj₁).2,
    (hasHopExcursionGT_iff_not_hopExcursionLEOn hB_nonneg).mpr (Finset.mem_filter.mp hj₂).2⟩

/-- **Theorem 4.1 (Theorem H, two-macroscopic-heads lower bound, oblivious form)**:
every oblivious linear-time transposer (`ObliviousLinTime M d (entryBits d) c T`) with `M.k ≤ k`
and `(valueWidth M : ℝ) ≤ β` has, for all `d ≥ slabDimThreshold c β`, **at least two distinct
work heads** that each make a completed hop of spatial excursion strictly greater than
`slabSmallExcursion c β k * L`. -/
theorem twoMacroscopicHeads_of_oblivious_linearTimeTransposer {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {d : ℕ} (hd : slabDimThreshold c β ≤ d) {T : ℕ}
    (hobl : ObliviousLinTime M d (entryBits d) c T) :
    ∃ j₁ j₂ : Fin M.k, j₁ ≠ j₂ ∧
      HasHopExcursionGT ((traceAt M (inputLength d)).work j₁) T
        (slabSmallExcursion c β k * (inputLength d : ℝ)) ∧
      HasHopExcursionGT ((traceAt M (inputLength d)).work j₂) T
        (slabSmallExcursion c β k * (inputLength d : ℝ)) := by
  obtain ⟨htrAt, hT_eq, hprob1⟩ := obliviousLinTime_to_transposesAt_prob hobl
  obtain ⟨j₁, j₂, hne, hh₁, hh₂⟩ :=
    twoMacroscopicHeads_of_linearTimeTransposer hc hβ k M hMk hvw
      (slabAutonomyEps_pos c β) hd htrAt hprob1
  rw [hT_eq] at hh₁ hh₂
  exact ⟨j₁, j₂, hne, hh₁, hh₂⟩

/-! ### Two Heads with Linearly Many Long Revisits (Theorem 4.1 / Theorem H(b), Counting Form) -/

/-- Earlier ends `p < T` of revisit hops `(p, u)` of `y` whose excursion exceeds `H`
(`∃ t ∈ Ioo p u, H < |y t - y p|`); `offCarrierLargeLowers` is the union of these sets over the work
heads outside the carrier set. A step is the earlier end of at most one hop of `y`. -/
noncomputable def largeLowers (y : ℕ → ℤ) (T H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter fun p =>
    ∃ u, IsHop y T p u ∧ ∃ t ∈ Finset.Ioo p u, (H : ℤ) < |y t - y p|

theorem offCarrierLargeLowers_eq_biUnion {k : ℕ} (xs : Fin k → ℕ → ℤ) (S_free : Finset (Fin k))
    (T H : ℕ) :
    offCarrierLargeLowers xs S_free T H =
      (Finset.univ \ S_free).biUnion fun j => largeLowers (xs j) T H := rfl

/-- **Theorem H(c) with `B` the target set**: for every set `S_free` of at most one work head and
every `H ≤ ⌊slabSmallExcursion c β k * L⌋₊`, the earlier ends of revisits of excursion greater than
`H` on the work heads outside `S_free` number at least `(slabAutonomyEps c β - η) * L / (β + 1)`.
The target set separates itself from every source set, so Theorem H(c) applies with `B` equal to it. -/
theorem offCarrier_longRevisits_card_ge {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {η : ℝ} {d : ℕ} (hd : slabDimThreshold c β ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀)
    (S_free : Finset (Fin M.k)) (hS_card : S_free.card ≤ 1)
    {H : ℕ} (hH : H ≤ ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊) :
    (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤
      (β + 1) * ((offCarrierLargeLowers τ₀.work S_free τ₀.haltTime H).card : ℝ) := by
  classical
  obtain ⟨V_star, _, _, hsep⟩ := offCarrier_vertexExpansion_of_linearTimeTransposer hc hβ k M hMk
    hvw hd htr hprob S_free hS_card hH
  set Dst := offCarrierLargeLowers τ₀.work S_free τ₀.haltTime H
  -- Every dependency path ending in `Dst` meets `Dst` at its last vertex.
  have h := hsep Dst fun π t₀ _ _ hdst => ⟨_, getLastD_mem_cons_self t₀ π, hdst⟩
  have hinter : (((Dst ∩ ((V_star.image (tposOf d (entryBits d))).image
      fun r : Fin (d * d * entryBits d) => appendTime τ₀ τ₀.haltTime r.1)).card : ℕ) : ℝ) ≤
      (Dst.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  show (slabAutonomyEps c β - η) * ((d * d * entryBits d : ℕ) : ℝ) ≤ _
  linarith

/-- **Theorem 4.1 (Theorem H(b), two heads with linearly many long revisits, low-adaptivity form)**:
every linear-time transposer (`TransposesAt M d c`) with `M.k ≤ k`, `(valueWidth M : ℝ) ≤ β`, and a
trace `τ₀` of probability `≥ 2^{-η L}` (`η < slabAutonomyEps c β`) has, for all
`d ≥ slabDimThreshold c β`, **two distinct work heads** each of which is the earlier end of a revisit
of excursion greater than `⌊slabSmallExcursion c β k * L⌋₊` at no fewer than
`(slabAutonomyEps c β - η) * L / ((β + 1) * (k - 1))` steps. Let `j₁` be a head with the most such
steps: `offCarrier_longRevisits_card_ge` off `{j₁}` and pigeonhole over the other `≤ k - 1` heads
give `j₂`. -/
theorem twoHeads_manyLongRevisits_of_linearTimeTransposer {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {η : ℝ} (hη : η < slabAutonomyEps c β)
    {d : ℕ} (hd : slabDimThreshold c β ≤ d)
    (htr : TransposesAt M d c)
    {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀) :
    ∃ j₁ j₂ : Fin M.k, j₁ ≠ j₂ ∧
      (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤ (β + 1) * ((k : ℝ) - 1) *
        ((largeLowers (τ₀.work j₁) τ₀.haltTime
          ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊).card : ℝ) ∧
      (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤ (β + 1) * ((k : ℝ) - 1) *
        ((largeLowers (τ₀.work j₂) τ₀.haltTime
          ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊).card : ℝ) := by
  classical
  set H₀ := ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊
  set cnt : Fin M.k → ℕ := fun j => (largeLowers (τ₀.work j) τ₀.haltTime H₀).card
  have hd1 : 1 ≤ d := le_trans (by norm_num) ((ten_le_slabDimThreshold c β).trans hd)
  have hL_pos : (0 : ℝ) < (inputLength d : ℝ) := by
    exact_mod_cast inputLength_pos (by omega : 0 < d)
  have hgap : 0 < (slabAutonomyEps c β - η) * (inputLength d : ℝ) :=
    mul_pos (sub_pos.mpr hη) hL_pos
  have hβ1 : 0 < β + 1 := by linarith
  -- Off every set `S` of at most one head: `(ε_* - η) L ≤ (β + 1) ∑_{j ∉ S} cnt j`.
  have hoff : ∀ S : Finset (Fin M.k), S.card ≤ 1 →
      (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤
        (β + 1) * ∑ j ∈ Finset.univ \ S, (cnt j : ℝ) := by
    intro S hS
    have h := offCarrier_longRevisits_card_ge hc hβ k M hMk hvw hd htr hprob S hS le_rfl
    have hsum : ((offCarrierLargeLowers τ₀.work S τ₀.haltTime H₀).card : ℝ) ≤
        ∑ j ∈ Finset.univ \ S, (cnt j : ℝ) := by
      rw [offCarrierLargeLowers_eq_biUnion]
      exact_mod_cast Finset.card_biUnion_le
    exact h.trans (mul_le_mul_of_nonneg_left hsum hβ1.le)
  -- `j₁`: a head with the most long-revisit steps.
  have huniv : (Finset.univ : Finset (Fin M.k)).Nonempty := by
    by_contra hemp
    have h := hoff ∅ (by simp)
    rw [Finset.sdiff_empty, Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty,
      mul_zero] at h
    linarith
  obtain ⟨j₁, -, hj₁⟩ := Finset.exists_max_image Finset.univ cnt huniv
  -- `j₂`: a head other than `j₁` with the most long-revisit steps.
  have hoff₁ := hoff {j₁} (Finset.card_singleton j₁).le
  have hrest : (Finset.univ \ {j₁}).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty, mul_zero] at hoff₁
    linarith
  obtain ⟨j₂, hj₂, hj₂max⟩ := Finset.exists_max_image (Finset.univ \ {j₁}) cnt hrest
  have hne : j₁ ≠ j₂ := fun h => (Finset.mem_sdiff.mp hj₂).2 (Finset.mem_singleton.mpr h.symm)
  have hcard : ((Finset.univ \ {j₁}).card : ℝ) ≤ (k : ℝ) - 1 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ {j₁})
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h1
    have h2 : ((Finset.univ \ {j₁}).card : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h1.trans_le hMk
    linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := (Nat.cast_nonneg _).trans hcard
  have hsum₂ : ∑ j ∈ Finset.univ \ {j₁}, (cnt j : ℝ) ≤ ((k : ℝ) - 1) * (cnt j₂ : ℝ) := by
    calc ∑ j ∈ Finset.univ \ {j₁}, (cnt j : ℝ)
        ≤ ∑ _j ∈ Finset.univ \ {j₁}, (cnt j₂ : ℝ) :=
          Finset.sum_le_sum fun j hj => by exact_mod_cast hj₂max j hj
      _ = ((Finset.univ \ {j₁}).card : ℝ) * (cnt j₂ : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℝ) - 1) * (cnt j₂ : ℝ) := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
  have h₂ : (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤
      (β + 1) * ((k : ℝ) - 1) * (cnt j₂ : ℝ) := by
    calc (slabAutonomyEps c β - η) * (inputLength d : ℝ)
        ≤ (β + 1) * ∑ j ∈ Finset.univ \ {j₁}, (cnt j : ℝ) := hoff₁
      _ ≤ (β + 1) * (((k : ℝ) - 1) * (cnt j₂ : ℝ)) := mul_le_mul_of_nonneg_left hsum₂ hβ1.le
      _ = (β + 1) * ((k : ℝ) - 1) * (cnt j₂ : ℝ) := by ring
  have h₁ : (slabAutonomyEps c β - η) * (inputLength d : ℝ) ≤
      (β + 1) * ((k : ℝ) - 1) * (cnt j₁ : ℝ) :=
    h₂.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hj₁ j₂ (Finset.mem_univ _))
      (mul_nonneg hβ1.le hk1))
  exact ⟨j₁, j₂, hne, h₁, h₂⟩

/-- **Theorem 4.1 (Theorem H(b), two heads with linearly many long revisits, oblivious form)**:
every oblivious linear-time transposer (`ObliviousLinTime M d (entryBits d) c T`) with `M.k ≤ k`
and `(valueWidth M : ℝ) ≤ β` has, for all `d ≥ slabDimThreshold c β`, **two distinct work heads**
each of which is, on the common trace, the earlier end of a revisit of excursion greater than
`⌊slabSmallExcursion c β k * L⌋₊` at no fewer than `slabAutonomyEps c β * L / ((β + 1) * (k - 1))`
steps. -/
theorem twoHeads_manyLongRevisits_of_oblivious_linearTimeTransposer {c β : ℝ} (hc : 1 ≤ c)
    (hβ : 1 ≤ β) (k : ℕ) (M : TM) (hMk : M.k ≤ k) (hvw : (valueWidth M : ℝ) ≤ β)
    {d : ℕ} (hd : slabDimThreshold c β ≤ d) {T : ℕ}
    (hobl : ObliviousLinTime M d (entryBits d) c T) :
    ∃ j₁ j₂ : Fin M.k, j₁ ≠ j₂ ∧
      slabAutonomyEps c β * (inputLength d : ℝ) ≤ (β + 1) * ((k : ℝ) - 1) *
        ((largeLowers ((traceAt M (inputLength d)).work j₁) T
          ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊).card : ℝ) ∧
      slabAutonomyEps c β * (inputLength d : ℝ) ≤ (β + 1) * ((k : ℝ) - 1) *
        ((largeLowers ((traceAt M (inputLength d)).work j₂) T
          ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊).card : ℝ) := by
  obtain ⟨htrAt, hT_eq, hprob1⟩ := obliviousLinTime_to_transposesAt_prob hobl
  obtain ⟨j₁, j₂, hne, h₁, h₂⟩ :=
    twoHeads_manyLongRevisits_of_linearTimeTransposer hc hβ k M hMk hvw
      (slabAutonomyEps_pos c β) hd htrAt hprob1
  rw [hT_eq, sub_zero] at h₁ h₂
  exact ⟨j₁, j₂, hne, h₁, h₂⟩

/-! ### Corollary 4.2 -/

private theorem hopExcursionLEOn_mono {y : ℕ → ℤ} {lo hi H₁ H₂ : ℕ} (hH : H₁ ≤ H₂)
    (hhop : HopExcursionLEOn y lo hi H₁) :
    HopExcursionLEOn y lo hi H₂ :=
  fun p u hlo hhi hh t hpt htu => (hhop p u hlo hhi hh t hpt htu).trans (by exact_mod_cast hH)

/-- **Corollary 4.2 (low-adaptivity sublinear-excursion form)**:
for any `H(d) = o(inputLength d)`, there is `d₁` above which no machine with `M.k ≤ k` and
`(valueWidth M : ℝ) ≤ β` can transpose in time `c (L + 1)` with a trace of probability
`≥ 2^{-η L}` (`η < slabAutonomyEps c β`) whose work heads outside at most one unrestricted head
have hop excursion `≤ H(d)`. -/
theorem oneFreeHead_sublinearExcursion_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) (k : ℕ)
    {H : ℕ → ℕ}
    (hH : Tendsto (fun d : ℕ => (H d : ℝ) / (inputLength d : ℝ)) atTop (nhds 0)) :
    ∃ d₁ : ℕ, ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β →
      ∀ η < slabAutonomyEps c β, ∀ d ≥ d₁,
        ¬ (TransposesAt M d c ∧
          ∃ (τ₀ : Trace M.k) (S_free : Finset (Fin M.k)),
            (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀ ∧
            S_free.card ≤ 1 ∧
            ∀ j : Fin M.k, j ∉ S_free →
              HopExcursionLEOn (τ₀.work j) 0 τ₀.haltTime (H d)) := by
  have hε_sm : 0 < slabSmallExcursion c β k := slabSmallExcursion_pos (by positivity) k
  have hev := (tendsto_order.mp hH).2 (slabSmallExcursion c β k) hε_sm
  rw [Filter.eventually_atTop] at hev
  obtain ⟨d_H, hd_H⟩ := hev
  refine ⟨max (slabDimThreshold c β) d_H, fun M hMk hvw η hη d hd ⟨htr, τ₀, S_free, hp, hS, hh⟩ => ?_⟩
  have hd_thr : slabDimThreshold c β ≤ d := le_of_max_le_left hd
  have hd1 : 1 ≤ d := by
    have := ten_le_slabDimThreshold c β
    omega
  have hL_pos : (0 : ℝ) < (inputLength d : ℝ) := by
    exact_mod_cast inputLength_pos (by omega : 0 < d)
  have hH_le : H d ≤ ⌊slabSmallExcursion c β k * (inputLength d : ℝ)⌋₊ := by
    apply Nat.le_floor
    exact ((div_lt_iff₀ hL_pos).mp (hd_H d (le_of_max_le_right hd))).le
  exact oneFreeHead_smallExcursion_excludes hc hβ k M hMk hvw η hη d hd_thr
    ⟨htr, τ₀, S_free, hp, hS, fun j hj => hopExcursionLEOn_mono hH_le (hh j hj)⟩

/-- **Corollary 4.2 (oblivious sublinear-excursion form)**:
specialization of `oneFreeHead_sublinearExcursion_excludes` to `ObliviousLinTime` (`η = 0`). -/
theorem oneFreeHead_sublinearExcursion_oblivious_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β)
    (k : ℕ) {H : ℕ → ℕ}
    (hH : Tendsto (fun d : ℕ => (H d : ℝ) / (inputLength d : ℝ)) atTop (nhds 0)) :
    ∃ d₁ : ℕ, ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β → ∀ d ≥ d₁, ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) c T ∧
        ∃ S_free : Finset (Fin M.k),
          S_free.card ≤ 1 ∧
          ∀ j : Fin M.k, j ∉ S_free →
            HopExcursionLEOn ((traceAt M (inputLength d)).work j) 0 T (H d)) := by
  obtain ⟨d₁, hexcl⟩ := oneFreeHead_sublinearExcursion_excludes hc hβ k hH
  refine ⟨d₁, fun M hMk hvw d hd T ⟨hoblT, S_free, hS, hh⟩ => ?_⟩
  obtain ⟨htrAt, hT_eq, hprob1⟩ := obliviousLinTime_to_transposesAt_prob hoblT
  exact hexcl M hMk hvw 0 (slabAutonomyEps_pos c β) d hd
    ⟨htrAt, traceAt M (inputLength d), S_free, hprob1, hS, fun j hj => by rw [hT_eq]; exact hh j hj⟩

/-- Every complete-family height bound `famd ≤ H` outside `S_free` implies `HopExcursionLEOn _ 0 T H`
outside `S_free`. -/
theorem hopExcursionLEOn_of_famd_le {k T H : ℕ} {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h))
    {S_free : Finset (Fin k)}
    (hfam : ∀ F : Keys xs (allHops xs T) (owners xs), F.1.1 ∉ S_free →
      famd xs (allHops xs T) (owners xs) F ≤ H) :
    ∀ j : Fin k, j ∉ S_free → HopExcursionLEOn (xs j) 0 T H := by
  intro j hj p u _ _ hhop t hpt htu
  let η : Fin k × ℕ × ℕ := (j, p, u)
  have hη : η ∈ allHops xs T := mem_allHops.mpr hhop
  let F : Keys xs (allHops xs T) (owners xs) :=
    ⟨key xs (owners xs) η, Finset.mem_image_of_mem _ hη⟩
  have hη_fam : η ∈ fam xs (allHops xs T) (owners xs) F.1 :=
    Finset.mem_filter.mpr ⟨hη, rfl⟩
  have hF_not : F.1.1 ∉ S_free := hj
  exact (hop_excursion_le_famd hx F hη_fam hpt htu).trans (by exact_mod_cast hfam F hF_not)

/-- **Corollary 4.2 (`BoundedNesting` family-height form, low-adaptivity)**:
if every complete family `F` outside at most one unrestricted work head has height
`famd ≤ H(d) = o(L)` (with no bound on `OwnerLoadLE`, cell entries, or scale-window count `q`),
transposition fails for all `d ≥ d₁` whenever `η < slabAutonomyEps c β`. -/
theorem oneFreeHead_sublinearFamHeight_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) (k : ℕ)
    {H : ℕ → ℕ}
    (hH : Tendsto (fun d : ℕ => (H d : ℝ) / (inputLength d : ℝ)) atTop (nhds 0)) :
    ∃ d₁ : ℕ, ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β →
      ∀ η < slabAutonomyEps c β, ∀ d ≥ d₁,
        ¬ (TransposesAt M d c ∧
          ∃ (τ₀ : Trace M.k) (S_free : Finset (Fin M.k)),
            (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀ ∧
            S_free.card ≤ 1 ∧
            ∀ F : Keys τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work),
              F.1.1 ∉ S_free →
              famd τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work) F ≤ H d) := by
  obtain ⟨d₁, hexcl⟩ := oneFreeHead_sublinearExcursion_excludes hc hβ k hH
  refine ⟨d₁, fun M hMk hvw η hη d hd ⟨htr, τ₀, S_free, hp, hS, hfam⟩ => ?_⟩
  exact hexcl M hMk hvw η hη d hd
    ⟨htr, τ₀, S_free, hp, hS, hopExcursionLEOn_of_famd_le τ₀.work_isWalk hfam⟩

/-- **Corollary 4.2 (`M.k ≤ 1` low-adaptivity exclusion)**:
no machine with at most one work tape (`M.k ≤ 1`) and `(valueWidth M : ℝ) ≤ β` can transpose in
time `c (L + 1)` with a trace of probability `≥ 2^{-η L}` (`η < slabAutonomyEps c β`) for any
`d ≥ slabDimThreshold c β`. -/
theorem atMostOneWorkTape_lowAdaptivity_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) :
    ∀ M : TM, M.k ≤ 1 → (valueWidth M : ℝ) ≤ β →
      ∀ η < slabAutonomyEps c β, ∀ d ≥ slabDimThreshold c β,
        ¬ (TransposesAt M d c ∧
          ∃ τ₀ : Trace M.k,
            (2 : ℝ) ^ (-η * (inputLength d : ℝ)) ≤ traceProb M (inputLength d) τ₀) := by
  intro M hMk hvw η hη d hd ⟨htr, τ₀, hprob⟩
  refine oneFreeHead_smallExcursion_excludes hc hβ 1 M hMk hvw η hη d hd
    ⟨htr, τ₀, Finset.univ, hprob, ?_, fun j hj => absurd (Finset.mem_univ j) hj⟩
  simpa using hMk

/-- **Corollary 4.2 (`M.k ≤ 1` oblivious exclusion)**:
no oblivious linear-time machine with `M.k ≤ 1` and `(valueWidth M : ℝ) ≤ β` transposes at
dimension `d ≥ slabDimThreshold c β`. -/
theorem atMostOneWorkTape_oblivious_excludes {c β : ℝ} (hc : 1 ≤ c) (hβ : 1 ≤ β) :
    ∀ M : TM, M.k ≤ 1 → (valueWidth M : ℝ) ≤ β →
      ∀ d ≥ slabDimThreshold c β, ∀ T : ℕ,
        ¬ ObliviousLinTime M d (entryBits d) c T := by
  intro M hMk hvw d hd T hoblT
  obtain ⟨htrAt, _, hprob1⟩ := obliviousLinTime_to_transposesAt_prob hoblT
  exact atMostOneWorkTape_lowAdaptivity_excludes hc hβ M hMk hvw 0
    (slabAutonomyEps_pos c β) d hd ⟨htrAt, traceAt M (inputLength d), hprob1⟩

end NativeRelations

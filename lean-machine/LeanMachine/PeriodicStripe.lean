import Mathlib.Data.Nat.Periodic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Sharp discrepancy for a periodic block of occupied integer coordinates. -/

namespace LeanMachine.PeriodicStripe

open Finset

variable {d b j n : ℕ}

/-- The `j`th block of width `b` in each period of length `d * b`. -/
def occupied (d b j z : ℕ) : Prop :=
  j * b ≤ z % (d * b) ∧ z % (d * b) < (j + 1) * b

instance (d b j : ℕ) : DecidablePred (occupied d b j) :=
  fun _z => inferInstanceAs (Decidable (_ ∧ _))

theorem occupied_periodic (d b j : ℕ) :
    Function.Periodic (occupied d b j) (d * b) := by
  intro z
  simp [occupied]

/-- The occupied block is exactly the source column recovered by bit transposition. -/
theorem occupied_iff_column (hb : 0 < b) (d j z : ℕ) :
    occupied d b j z ↔ z / b % d = j := by
  rw [← Nat.mod_mul_left_div_self z b d]
  unfold occupied
  constructor
  · rintro ⟨hlo, hhi⟩
    have hle := (Nat.le_div_iff_mul_le hb).mpr hlo
    have hlt := (Nat.div_lt_iff_lt_mul hb).mpr hhi
    omega
  · intro h
    have hlo := (Nat.le_div_iff_mul_le hb).mp (Nat.le_of_eq h.symm)
    have hhi := (Nat.div_lt_iff_lt_mul hb).mp (show z % (d * b) / b < j + 1 by omega)
    exact ⟨hlo, hhi⟩

theorem count_prefix_short (hn : n ≤ d * b) :
    Nat.count (occupied d b j) n = min b (n - j * b) := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (range n).filter (occupied d b j) = Ico (j * b) (min n ((j + 1) * b)) := by
    ext z
    simp only [mem_filter, mem_range, occupied, mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨hzn, hlo, hhi⟩
      have hzW : z < d * b := lt_of_lt_of_le hzn hn
      simpa [Nat.mod_eq_of_lt hzW] using And.intro hlo (And.intro hzn hhi)
    · rintro ⟨hlo, hzn, hhi⟩
      have hzW : z < d * b := lt_of_lt_of_le hzn hn
      simp [Nat.mod_eq_of_lt hzW, hzn, hlo, hhi]
  rw [hset, Nat.card_Ico]
  have he : (j + 1) * b = j * b + b := by ring
  rw [he]
  omega

theorem count_period (_hd : 0 < d) (hb : 0 < b) (hj : j < d) :
    Nat.count (occupied d b j) (d * b) = b := by
  rw [count_prefix_short le_rfl]
  have : j * b + b ≤ d * b := by nlinarith
  omega

theorem count_add_period (hd : 0 < d) (hb : 0 < b) (hj : j < d) (n : ℕ) :
    Nat.count (occupied d b j) (n + d * b) =
      Nat.count (occupied d b j) n + b := by
  rw [Nat.count_add', count_period hd hb hj]
  congr 1
  congr 1
  funext z
  exact occupied_periodic d b j z

theorem count_mul_period (hd : 0 < d) (hb : 0 < b) (hj : j < d) (q : ℕ) :
    Nat.count (occupied d b j) (q * (d * b)) = q * b := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, count_add_period hd hb hj, ih, Nat.succ_mul]

/-- Exact prefix count; only the last, incomplete period needs truncation. -/
theorem count_prefix (hd : 0 < d) (hb : 0 < b) (hj : j < d) (n : ℕ) :
    Nat.count (occupied d b j) n =
      n / (d * b) * b + min b (n % (d * b) - j * b) := by
  have hW : 0 < d * b := Nat.mul_pos hd hb
  have he : n = n / (d * b) * (d * b) + n % (d * b) := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n (d * b)).symm
  conv_lhs => rw [he, Nat.count_add]
  rw [count_mul_period hd hb hj]
  congr 1
  rw [← count_prefix_short (Nat.le_of_lt (Nat.mod_lt _ hW))]
  congr 1
  funext k
  simp [occupied, Nat.add_mod]

/-- Prefix discrepancy scaled by `d`, avoiding division. -/
def centered (d b j n : ℕ) : ℤ :=
  (d : ℤ) * Nat.count (occupied d b j) n - n

theorem centered_eq_remainder (hd : 0 < d) (hb : 0 < b) (hj : j < d) (n : ℕ) :
    centered d b j n =
      (d : ℤ) * (min b (n % (d * b) - j * b) : ℕ) - (n % (d * b) : ℕ) := by
  rw [centered, count_prefix hd hb hj]
  simp only [Nat.cast_add, Nat.cast_mul]
  have he : (n : ℤ) = (n / (d * b) : ℕ) * (d : ℤ) * b + (n % (d * b) : ℕ) := by
    have h := Nat.div_add_mod n (d * b)
    have h' : (d : ℤ) * b * (n / (d * b) : ℕ) + (n % (d * b) : ℕ) = n := by
      exact_mod_cast h
    nlinarith
  rw [he]
  ring

theorem centered_bounds (hd : 0 < d) (hb : 0 < b) (hj : j < d) (n : ℕ) :
    -(j : ℤ) * b ≤ centered d b j n ∧
      centered d b j n ≤ (b : ℤ) * (d - 1) - j * b := by
  rw [centered_eq_remainder hd hb hj]
  let r := n % (d * b)
  change -(j : ℤ) * b ≤ (d : ℤ) * min b (r - j * b) - r ∧
    (d : ℤ) * min b (r - j * b) - r ≤ (b : ℤ) * (d - 1) - j * b
  have hr : r < d * b := Nat.mod_lt _ (Nat.mul_pos hd hb)
  have hdr : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hbr : (0 : ℤ) ≤ b := by positivity
  have hjr : (j : ℤ) + 1 ≤ d := by exact_mod_cast hj
  have hrr : (r : ℤ) < (d : ℤ) * b := by exact_mod_cast hr
  by_cases hbefore : r < j * b
  · have he : min b (r - j * b) = 0 := by omega
    have hbef : (r : ℤ) < (j : ℤ) * b := by exact_mod_cast hbefore
    rw [he]
    norm_num
    constructor <;> nlinarith
  · by_cases hafter : j * b + b ≤ r
    · have he : min b (r - j * b) = b := by omega
      have haft : (j : ℤ) * b + b ≤ r := by exact_mod_cast hafter
      rw [he]
      constructor <;> nlinarith
    · have hrlo : j * b ≤ r := by omega
      have hrhi : r ≤ j * b + b := by omega
      have he : min b (r - j * b) = r - j * b := by omega
      have hlo : (j : ℤ) * b ≤ r := by exact_mod_cast hrlo
      have hhi : (r : ℤ) ≤ (j : ℤ) * b + b := by exact_mod_cast hrhi
      rw [he, Nat.cast_sub hrlo]
      push_cast
      constructor <;> nlinarith

/-- Number of occupied offsets in an interval, before reducing modulo the circle. -/
def arcCount (d b j a ell : ℕ) : ℕ :=
  ((range ell).filter (fun k => occupied d b j (a + k))).card

theorem scaled_arcCount_eq_centered_sub (d b j a ell : ℕ) :
    (d : ℤ) * arcCount d b j a ell - ell =
      centered d b j (a + ell) - centered d b j a := by
  have hc : (Nat.count (occupied d b j) (a + ell) : ℤ) =
      Nat.count (occupied d b j) a + arcCount d b j a ell := by
    simpa only [arcCount, Nat.count_eq_card_filter_range, Nat.cast_add] using
      congrArg (fun q : ℕ => (q : ℤ)) (Nat.count_add (occupied d b j) a ell)
  unfold centered
  rw [hc]
  push_cast
  ring

/-- Sharp interval discrepancy, valid even for intervals longer than one period. -/
theorem abs_scaled_arcCount_sub_le (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (a ell : ℕ) :
    |(d : ℤ) * arcCount d b j a ell - ell| ≤ (b : ℤ) * (d - 1) := by
  rw [scaled_arcCount_eq_centered_sub]
  have ha := centered_bounds hd hb hj a
  have hbnd := centered_bounds hd hb hj (a + ell)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual transpose demand stripe on `d` periods. -/
def stripe (d b j : ℕ) : Finset ℕ :=
  (range (d * (d * b))).filter (occupied d b j)

theorem mem_stripe_iff (hd : 0 < d) (hb : 0 < b) (hj : j < d) (z : ℕ) :
    z ∈ stripe d b j ↔
      ∃ i < d, ∃ k < b, z = i * (d * b) + j * b + k := by
  have hW : 0 < d * b := Nat.mul_pos hd hb
  have hblock : j * b + b ≤ d * b := by nlinarith
  simp only [stripe, mem_filter, mem_range, occupied]
  constructor
  · rintro ⟨hz, hlo, hhi⟩
    have hi : z / (d * b) < d := (Nat.div_lt_iff_lt_mul hW).mpr hz
    refine ⟨z / (d * b), hi, z % (d * b) - j * b, ?_, ?_⟩
    · have he : (j + 1) * b = j * b + b := by ring
      rw [he] at hhi
      omega
    · have he := Nat.div_add_mod z (d * b)
      rw [Nat.mul_comm (d * b)] at he
      omega
  · rintro ⟨i, hi, k, hk, rfl⟩
    have hr : j * b + k < d * b := by omega
    have hmod : (i * (d * b) + j * b + k) % (d * b) = j * b + k := by
      simp [Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt hr]
    rw [hmod]
    constructor
    · nlinarith
    · constructor
      · omega
      · nlinarith

theorem occupied_mod_circle (d b j z : ℕ) :
    occupied d b j (z % (d * (d * b))) ↔ occupied d b j z := by
  have hdvd : d * b ∣ d * (d * b) := dvd_mul_left (d * b) d
  simp [occupied, Nat.mod_mod_of_dvd _ hdvd]

/-- Different transpose columns have disjoint source stripes. -/
theorem pairwiseDisjoint_stripe (hb : 0 < b) (d : ℕ) :
    (range d : Set ℕ).PairwiseDisjoint (stripe d b) := by
  intro j _ k _ hjk
  apply disjoint_left.mpr
  intro z hzj hzk
  have hj := (occupied_iff_column hb d j z).mp (mem_filter.mp hzj).2
  have hk := (occupied_iff_column hb d k z).mp (mem_filter.mp hzk).2
  exact hjk (hj.symm.trans hk)

/-- The source stripes partition the full input coordinate set. -/
theorem biUnion_stripe (hd : 0 < d) (hb : 0 < b) :
    (range d).biUnion (stripe d b) = range (d * (d * b)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, _, hzj⟩ := mem_biUnion.mp hz
    exact (mem_filter.mp hzj).1
  · intro hz
    apply mem_biUnion.mpr
    exact ⟨z / b % d, mem_range.mpr (Nat.mod_lt _ hd),
      mem_filter.mpr ⟨hz, (occupied_iff_column hb d (z / b % d) z).mpr rfl⟩⟩

/-- Counting any fixed selection by source stripe is exact. -/
theorem sum_stripe_inter_card (hd : 0 < d) (hb : 0 < b) (D : Finset ℕ) :
    (∑ j ∈ range d, ((stripe d b j) ∩ D).card) = ((range (d * (d * b))) ∩ D).card := by
  have hdisj : (range d : Set ℕ).PairwiseDisjoint (fun j => stripe d b j ∩ D) := by
    intro j hj k hk hjk
    exact ((pairwiseDisjoint_stripe hb d) hj hk hjk).mono inter_subset_left inter_subset_left
  rw [← card_biUnion hdisj]
  rw [← biUnion_inter, biUnion_stripe hd hb]

/-- Counting the stripe on a circular interval equals counting its injective offsets. -/
theorem stripe_inter_arc_card (hd : 0 < d) (hb : 0 < b) (j a ell : ℕ)
    (hell : ell ≤ d * (d * b)) :
    ((stripe d b j) ∩ ((range ell).image (fun k => (a + k) % (d * (d * b))))).card =
      arcCount d b j a ell := by
  let L := d * (d * b)
  have hL : 0 < L := Nat.mul_pos hd (Nat.mul_pos hd hb)
  symm
  apply card_bij (fun k _ => (a + k) % L)
  · intro k hk
    obtain ⟨hk, hp⟩ := mem_filter.mp hk
    apply mem_inter.mpr
    constructor
    · apply mem_filter.mpr
      exact ⟨mem_range.mpr (Nat.mod_lt _ hL), (occupied_mod_circle d b j (a + k)).mpr hp⟩
    · exact mem_image.mpr ⟨k, hk, rfl⟩
  · intro k hk l hl he
    have hk' : k < L := lt_of_lt_of_le (mem_range.mp (mem_filter.mp hk).1) hell
    have hl' : l < L := lt_of_lt_of_le (mem_range.mp (mem_filter.mp hl).1) hell
    have := Nat.mod_injOn_Ico a L
      (mem_Ico.mpr (show a ≤ a + k ∧ a + k < a + L by omega))
      (mem_Ico.mpr (show a ≤ a + l ∧ a + l < a + L by omega)) he
    omega
  · intro z hz
    obtain ⟨hzS, hzA⟩ := mem_inter.mp hz
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hzA
    refine ⟨k, mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
    exact (occupied_mod_circle d b j (a + k)).mp (mem_filter.mp hzS).2

/-- The sharp real discrepancy bound, with no circular or short-interval restriction. -/
theorem abs_arcCount_sub_density_le (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (a ell : ℕ) :
    |(arcCount d b j a ell : ℝ) - (ell : ℝ) / d| ≤ (b : ℝ) * (1 - 1 / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h : |(d : ℝ) * arcCount d b j a ell - ell| ≤ (b : ℝ) * (d - 1) := by
    exact_mod_cast abs_scaled_arcCount_sub_le hd hb hj a ell
  calc
    |(arcCount d b j a ell : ℝ) - (ell : ℝ) / d| =
        |((d : ℝ) * arcCount d b j a ell - ell) / d| := by
      congr 1
      field_simp
    _ = |(d : ℝ) * arcCount d b j a ell - ell| / d := by
      rw [abs_div, abs_of_pos hdR]
    _ ≤ ((b : ℝ) * (d - 1)) / d := div_le_div_of_nonneg_right h hdR.le
    _ = (b : ℝ) * (1 - 1 / d) := by field_simp

theorem abs_stripe_inter_arc_sub_density_le (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (a ell : ℕ) (hell : ell ≤ d * (d * b)) :
    |(((stripe d b j) ∩ ((range ell).image (fun k => (a + k) % (d * (d * b))))).card : ℝ)
      - (ell : ℝ) / d| ≤ (b : ℝ) * (1 - 1 / d) := by
  rw [stripe_inter_arc_card hd hb j a ell hell]
  exact abs_arcCount_sub_density_le hd hb hj a ell

/-- Weighted lower discrepancy. The intervals may overlap; disjointness is only needed
when an application interprets the weighted sum as a selection probability. -/
theorem weighted_arcCount_lower_bound {ι : Type*}
    (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (I : Finset ι) (weight : ι → ℝ) (start length : ι → ℕ)
    (hweight : ∀ i ∈ I, 0 ≤ weight i) :
    (∑ i ∈ I, weight i * (length i : ℝ)) / d -
      (b : ℝ) * (1 - 1 / d) * ∑ i ∈ I, weight i ≤
        ∑ i ∈ I, weight i * (arcCount d b j (start i) (length i) : ℝ) := by
  let c : ℝ := (b : ℝ) * (1 - 1 / d)
  change (∑ i ∈ I, weight i * (length i : ℝ)) / d - c * ∑ i ∈ I, weight i ≤ _
  calc
    _ = ∑ i ∈ I, weight i * ((length i : ℝ) / d - c) := by
      simp only [mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div, ← sum_mul]
      ring
    _ ≤ _ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (by
      have h := (abs_le.mp (abs_arcCount_sub_density_le hd hb hj (start i) (length i))).1
      linarith) (hweight i hi)

end LeanMachine.PeriodicStripe

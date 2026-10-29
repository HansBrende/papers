import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# Query types covered by moving source banks

Partition by the integer part of a cumulative movement clock. The counting
argument works in any pseudometric space, with any positive partition width
and any charge dominating the movement of each individual slot.
-/

namespace LeanMachine.QueryMovement

open Finset
open scoped BigOperators
noncomputable section

/-- Centres covered by a bank of balls. -/
def covered {X α ι : Type*} [PseudoMetricSpace X] [Fintype α] [Fintype ι]
    (c : α → X) (y : ι → X) (R : ℝ) : Finset α :=
  univ.filter fun a => ∃ i, dist (c a) (y i) ≤ R

@[simp] theorem mem_covered {X α ι : Type*} [PseudoMetricSpace X]
    [Fintype α] [Fintype ι] {c : α → X} {y : ι → X} {R : ℝ} {a : α} :
    a ∈ covered c y R ↔ ∃ i, dist (c a) (y i) ≤ R := by
  classical
  simp [covered]

/-- Equal clock buckets have diameter strictly less than their width. -/
theorem abs_sub_lt_of_floor_eq {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : 0 < δ) (h : ⌊a / δ⌋₊ = ⌊b / δ⌋₊) : |a - b| < δ := by
  have ha₀ := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg ha hδ.le))
  have hb₀ := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hb hδ.le))
  have ha₁ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (a / δ))
  have hb₁ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (b / δ))
  rw [h] at ha₀ ha₁
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A scalar movement clock gives an exact, integer-valued bound on query
types. The finite set of query times need not be consecutive or nonempty. -/
theorem card_types_le {X α ι τ : Type*} [PseudoMetricSpace X]
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq τ]
    (T : Finset τ) (S : τ → Finset α) (c : α → X) (Y : ι → τ → X)
    (clock : τ → ℝ) (V ρ δ : ℝ) (k s : ℕ) (hδ : 0 < δ)
    (hclock : ∀ t ∈ T, 0 ≤ clock t ∧ clock t ≤ V)
    (hpath : ∀ i, ∀ t ∈ T, ∀ u ∈ T,
      dist (Y i t) (Y i u) ≤ |clock t - clock u|)
    (hsize : ∀ t ∈ T, (S t).card = k)
    (hcover : ∀ t ∈ T, ∀ a ∈ S t, ∃ i, dist (c a) (Y i t) ≤ ρ)
    (hcapacity : ∀ y : ι → X, (covered c y (ρ + δ)).card ≤ s) :
    (T.image S).card ≤ (⌊V / δ⌋₊ + 1) * s.choose k := by
  classical
  let bucket (t : τ) := ⌊clock t / δ⌋₊
  let times (q : ℕ) := T.filter fun t => bucket t = q
  let types (q : ℕ) := (times q).image S
  have hbucket {t : τ} (ht : t ∈ T) : bucket t ∈ range (⌊V / δ⌋₊ + 1) := by
    exact mem_range.mpr (Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right (hclock t ht).2 hδ.le)))
  have hlocal (q : ℕ) : (types q).card ≤ s.choose k := by
    rcases (times q).eq_empty_or_nonempty with h | ⟨u, hu⟩
    · simp [types, h]
    obtain ⟨huT, huq⟩ := mem_filter.mp hu
    let C := covered c (fun i => Y i u) (ρ + δ)
    have hsub : types q ⊆ C.powersetCard k := by
      intro A hA
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hA
      obtain ⟨htT, htq⟩ := mem_filter.mp ht
      refine mem_powersetCard.mpr ⟨?_, hsize t htT⟩
      intro a ha
      obtain ⟨i, hi⟩ := hcover t htT a ha
      apply mem_covered.mpr
      refine ⟨i, (dist_triangle (c a) (Y i t) (Y i u)).trans ?_⟩
      have hd := abs_sub_lt_of_floor_eq (hclock t htT).1 (hclock u huT).1
        hδ (htq.trans huq.symm)
      linarith [hpath i t htT u huT]
    exact (card_le_card hsub).trans (by
      rw [card_powersetCard]
      exact Nat.choose_le_choose k (hcapacity _))
  calc
    (T.image S).card ≤ ((range (⌊V / δ⌋₊ + 1)).biUnion types).card := by
      apply card_le_card
      intro A hA
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hA
      exact mem_biUnion.mpr ⟨bucket t, hbucket ht,
        mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, rfl⟩, rfl⟩⟩
    _ ≤ ∑ q ∈ range (⌊V / δ⌋₊ + 1), (types q).card := card_biUnion_le
    _ ≤ ∑ _q ∈ range (⌊V / δ⌋₊ + 1), s.choose k := sum_le_sum fun q _ => hlocal q
    _ = _ := by simp

/-- Cumulative nonnegative edge charge. -/
def elapsed (w : ℕ → ℝ) (t : ℕ) : ℝ := ∑ e ∈ range t, w e

theorem elapsed_nonneg {w : ℕ → ℝ} {n t : ℕ}
    (hw : ∀ e < n, 0 ≤ w e) (ht : t ≤ n) : 0 ≤ elapsed w t := by
  exact sum_nonneg fun e he => hw e (lt_of_lt_of_le (mem_range.mp he) ht)

theorem elapsed_mono {w : ℕ → ℝ} {n a b : ℕ}
    (hw : ∀ e < n, 0 ≤ w e) (hab : a ≤ b) (hb : b ≤ n) :
    elapsed w a ≤ elapsed w b := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hab)
    (fun e he _ => hw e (lt_of_lt_of_le (mem_range.mp he) hb))

theorem dist_le_elapsed_sub {X : Type*} [PseudoMetricSpace X]
    {Y : ℕ → X} {w : ℕ → ℝ} {n a b : ℕ}
    (hw : ∀ e < n, dist (Y e) (Y (e + 1)) ≤ w e) (hab : a ≤ b) (hb : b ≤ n) :
    dist (Y a) (Y b) ≤ elapsed w b - elapsed w a := by
  calc
    _ ≤ ∑ e ∈ Ico a b, dist (Y e) (Y (e + 1)) := dist_le_Ico_sum_dist Y hab
    _ ≤ ∑ e ∈ Ico a b, w e := sum_le_sum fun e he =>
      hw e (lt_of_lt_of_le (mem_Ico.mp he).2 hb)
    _ = _ := by simp [elapsed, sum_Ico_eq_sub _ hab]

theorem dist_le_elapsed_abs {X : Type*} [PseudoMetricSpace X]
    {Y : ℕ → X} {w : ℕ → ℝ} {n a b : ℕ}
    (hw : ∀ e < n, dist (Y e) (Y (e + 1)) ≤ w e) (ha : a ≤ n) (hb : b ≤ n) :
    dist (Y a) (Y b) ≤ |elapsed w a - elapsed w b| := by
  rcases le_total a b with h | h
  · exact (dist_le_elapsed_sub hw h hb).trans (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
  · rw [dist_comm]
    exact (dist_le_elapsed_sub hw h ha).trans (le_abs_self _)

/-- Finite path version, for an arbitrary charge dominating each slot's
step. In particular, one may use the maximum slot movement at each step. -/
theorem card_types_le_charge {X α ι : Type*} [PseudoMetricSpace X]
    [Fintype α] [Fintype ι] [DecidableEq α]
    (S : ℕ → Finset α) (c : α → X) (Y : ι → ℕ → X)
    (w : ℕ → ℝ) (n k s : ℕ) (ρ δ : ℝ) (hδ : 0 < δ)
    (hw : ∀ e < n, 0 ≤ w e)
    (hstep : ∀ i, ∀ e < n, dist (Y i e) (Y i (e + 1)) ≤ w e)
    (hsize : ∀ t ≤ n, (S t).card = k)
    (hcover : ∀ t ≤ n, ∀ a ∈ S t, ∃ i, dist (c a) (Y i t) ≤ ρ)
    (hcapacity : ∀ y : ι → X, (covered c y (ρ + δ)).card ≤ s) :
    ((range (n + 1)).image S).card ≤
      (⌊elapsed w n / δ⌋₊ + 1) * s.choose k := by
  apply card_types_le (range (n + 1)) S c Y (elapsed w) (elapsed w n) ρ δ k s hδ
  · intro t ht
    have ht' : t ≤ n := by simpa using ht
    exact ⟨elapsed_nonneg hw ht', elapsed_mono hw ht' le_rfl⟩
  · intro i t ht u hu
    exact dist_le_elapsed_abs (hstep i) (by simpa using ht) (by simpa using hu)
  · intro t ht
    exact hsize t (by simpa using ht)
  · intro t ht
    exact hcover t (by simpa using ht)
  · exact hcapacity

/-- Summed movement of every labelled slot, in the paper's order of summation. -/
def variation {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]
    (Y : ι → ℕ → X) (n : ℕ) : ℝ :=
  ∑ i, ∑ e ∈ range n, dist (Y i e) (Y i (e + 1))

/-- The largest movement of any slot at one step. -/
def maxStep {X ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (Y : ι → ℕ → X) (e : ℕ) : ℝ :=
  univ.sup' univ_nonempty fun i => dist (Y i e) (Y i (e + 1))

theorem step_le_maxStep {X ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (Y : ι → ℕ → X) (e : ℕ) (i : ι) :
    dist (Y i e) (Y i (e + 1)) ≤ maxStep Y e := by
  exact le_sup' (fun j : ι => dist (Y j e) (Y j (e + 1))) (mem_univ i)

theorem maxStep_nonneg {X ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (Y : ι → ℕ → X) (e : ℕ) : 0 ≤ maxStep Y e := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact dist_nonneg.trans (step_le_maxStep Y e i)

theorem elapsed_maxStep_le_variation {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (Y : ι → ℕ → X) (n : ℕ) :
    elapsed (maxStep Y) n ≤ variation Y n := by
  unfold elapsed variation
  rw [sum_comm]
  apply sum_le_sum
  intro e _
  exact sup'_le _ _ fun i _ => single_le_sum
    (f := fun j : ι => dist (Y j e) (Y j (e + 1))) (fun _ _ => dist_nonneg) (mem_univ i)

/-- Real-valued counting bound and its inversion, extracted once from the
integer bound. Positivity of the number of types forces positive capacity. -/
theorem real_bounds {F B : ℕ} {C δ : ℝ} (hF : 0 < F) (hC : 0 ≤ C)
    (hδ : 0 < δ) (h : F ≤ (⌊C / δ⌋₊ + 1) * B) :
    0 < B ∧ (F : ℝ) ≤ (1 + C / δ) * B ∧
      δ * ((F : ℝ) / B - 1) ≤ C := by
  have hB : 0 < B := by nlinarith
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have h' : (F : ℝ) ≤ ((⌊C / δ⌋₊ : ℝ) + 1) * B := by exact_mod_cast h
  have hc := Nat.floor_le (div_nonneg hC hδ.le)
  have hcount : (F : ℝ) ≤ (1 + C / δ) * B := by nlinarith
  refine ⟨hB, hcount, ?_⟩
  have hf := (div_le_iff₀ hBR).mpr hcount
  have hh := mul_le_mul_of_nonneg_left hf hδ.le
  field_simp at hh ⊢
  nlinarith

end
end LeanMachine.QueryMovement

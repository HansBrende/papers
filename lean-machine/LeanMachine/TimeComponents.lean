import LeanMachine.IntervalOscillation
import Mathlib.Data.Finset.Max

/-!
# Canonical components of a finite time path

An allowed elementary edge joins its two endpoint times. Counting forbidden
earlier edges labels the resulting interval components canonically, including
isolated vertices. Their raw-coordinate ranges charge each allowed edge once.
-/

namespace LeanMachine.TimeComponents

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Number of forbidden edges strictly before a time. -/
def label (B : Finset ℕ) (t : ℕ) : ℕ := ((range t) \ B).card

theorem label_mono (B : Finset ℕ) : Monotone (label B) := by
  intro u t hut
  exact card_le_card (sdiff_subset_sdiff_left B (range_mono hut))

/-- Traversing only allowed edges does not change the component label. -/
theorem label_eq_of_Ico_subset {B : Finset ℕ} {u t : ℕ}
    (hut : u ≤ t) (hB : Ico u t ⊆ B) : label B u = label B t := by
  unfold label
  congr 1
  ext e
  simp only [mem_sdiff, mem_range]
  constructor
  · exact fun ⟨he, hn⟩ => ⟨he.trans_le hut, hn⟩
  · rintro ⟨he, hn⟩
    refine ⟨?_, hn⟩
    by_contra h
    exact hn (hB (mem_Ico.mpr ⟨by omega, he⟩))

/-- Equal labels leave no forbidden edge between the two times. -/
theorem Ico_subset_of_label_eq {B : Finset ℕ} {u t : ℕ}
    (hut : u ≤ t) (heq : label B u = label B t) : Ico u t ⊆ B := by
  have hs : (range u) \ B = (range t) \ B :=
    eq_of_subset_of_card_le (sdiff_subset_sdiff_left B (range_mono hut)) heq.ge
  intro e he
  by_contra hn
  have hem : e ∈ (range t) \ B := mem_sdiff.mpr ⟨mem_range.mpr (mem_Ico.mp he).2, hn⟩
  rw [← hs] at hem
  have := mem_range.mp (mem_sdiff.mp hem).1
  have := (mem_Ico.mp he).1
  omega

theorem label_eq_iff_Ico_subset {B : Finset ℕ} {u t : ℕ} (hut : u ≤ t) :
    label B u = label B t ↔ Ico u t ⊆ B :=
  ⟨Ico_subset_of_label_eq hut, label_eq_of_Ico_subset hut⟩

/-- A component fiber contains every time between any two of its times. -/
theorem label_eq_of_between {B : Finset ℕ} {u s t : ℕ}
    (hus : u ≤ s) (hst : s ≤ t) (heq : label B u = label B t) :
    label B s = label B u :=
  le_antisymm ((label_mono B hst).trans_eq heq.symm) (label_mono B hus)

/-- Component labels actually represented among times `0,...,n`. -/
def components (B : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).image (label B)

theorem label_mem_components {B : Finset ℕ} {n t : ℕ} (ht : t ≤ n) :
    label B t ∈ components B n :=
  mem_image.mpr ⟨t, mem_range.mpr (by omega), rfl⟩

/-- The canonical component containing a specified time. -/
def ofTime (B : Finset ℕ) (n t : ℕ) (ht : t ≤ n) : components B n :=
  ⟨label B t, label_mem_components ht⟩

/-- Complete finite time fiber of a represented component label. -/
def times {B : Finset ℕ} {n : ℕ} (c : components B n) : Finset ℕ :=
  (range (n + 1)).filter fun t => label B t = c.val

theorem mem_times {B : Finset ℕ} {n t : ℕ} {c : components B n} :
    t ∈ times c ↔ t ≤ n ∧ label B t = c.val := by
  simp only [times, mem_filter, mem_range]
  omega

theorem times_nonempty {B : Finset ℕ} {n : ℕ} (c : components B n) :
    (times c).Nonempty := by
  obtain ⟨t, ht, he⟩ := mem_image.mp c.property
  exact ⟨t, mem_filter.mpr ⟨ht, he⟩⟩

def first {B : Finset ℕ} {n : ℕ} (c : components B n) : ℕ :=
  (times c).min' (times_nonempty c)

def last {B : Finset ℕ} {n : ℕ} (c : components B n) : ℕ :=
  (times c).max' (times_nonempty c)

theorem first_mem {B : Finset ℕ} {n : ℕ} (c : components B n) : first c ∈ times c :=
  min'_mem _ _

theorem last_mem {B : Finset ℕ} {n : ℕ} (c : components B n) : last c ∈ times c :=
  max'_mem _ _

theorem first_le_last {B : Finset ℕ} {n : ℕ} (c : components B n) : first c ≤ last c :=
  min'_le_max' _ (times_nonempty c)

theorem last_le {B : Finset ℕ} {n : ℕ} (c : components B n) : last c ≤ n :=
  (mem_times.mp (last_mem c)).1

theorem times_eq_Icc {B : Finset ℕ} {n : ℕ} (c : components B n) :
    times c = Icc (first c) (last c) := by
  ext t
  constructor
  · intro ht
    exact mem_Icc.mpr ⟨min'_le _ _ ht, le_max' _ _ ht⟩
  · intro ht
    obtain ⟨hfirst, hlast⟩ := mem_Icc.mp ht
    apply mem_times.mpr
    refine ⟨hlast.trans (last_le c), ?_⟩
    have heq := (mem_times.mp (first_mem c)).2.trans (mem_times.mp (last_mem c)).2.symm
    exact (label_eq_of_between hfirst hlast heq).trans (mem_times.mp (first_mem c)).2

/-- Internal elementary edges of the component, excluding its last time. -/
def edges {B : Finset ℕ} {n : ℕ} (c : components B n) : Finset ℕ :=
  Ico (first c) (last c)

theorem edges_subset {B : Finset ℕ} {n : ℕ} (c : components B n) : edges c ⊆ B :=
  Ico_subset_of_label_eq (first_le_last c)
    ((mem_times.mp (first_mem c)).2.trans (mem_times.mp (last_mem c)).2.symm)

theorem edges_subset_range {B : Finset ℕ} {n : ℕ} (c : components B n) :
    edges c ⊆ range n := by
  intro e he
  exact mem_range.mpr ((mem_Ico.mp he).2.trans_le (last_le c))

theorem edges_pairwiseDisjoint {B : Finset ℕ} {n : ℕ} :
    Pairwise (fun c d : components B n => Disjoint (edges c) (edges d)) := by
  intro c d hne
  apply disjoint_left.mpr
  intro e hec hed
  have htc : e ∈ times c := by
    rw [times_eq_Icc]
    exact mem_Icc.mpr ⟨(mem_Ico.mp hec).1, (mem_Ico.mp hec).2.le⟩
  have htd : e ∈ times d := by
    rw [times_eq_Icc]
    exact mem_Icc.mpr ⟨(mem_Ico.mp hed).1, (mem_Ico.mp hed).2.le⟩
  exact hne (Subtype.ext ((mem_times.mp htc).2.symm.trans (mem_times.mp htd).2))

/-- The internal edges partition exactly the allowed edges in the horizon. -/
theorem biUnion_edges {B : Finset ℕ} {n : ℕ} :
    univ.biUnion (fun c : components B n => edges c) = B ∩ range n := by
  ext e
  constructor
  · intro he
    obtain ⟨c, _, hc⟩ := mem_biUnion.mp he
    exact mem_inter.mpr ⟨edges_subset c hc, edges_subset_range c hc⟩
  · intro he
    obtain ⟨heB, hen⟩ := mem_inter.mp he
    have hen' := mem_range.mp hen
    let c := ofTime B n e hen'.le
    have heq : label B e = label B (e + 1) := by
      apply label_eq_of_Ico_subset (by omega)
      intro q hq
      have hqe : q = e := by have := mem_Ico.mp hq; omega
      exact hqe ▸ heB
    have ht₀ : e ∈ times c := mem_times.mpr ⟨hen'.le, rfl⟩
    have ht₁ : e + 1 ∈ times c := mem_times.mpr ⟨by omega, heq.symm⟩
    rw [times_eq_Icc] at ht₀ ht₁
    exact mem_biUnion.mpr ⟨c, mem_univ _, mem_Ico.mpr
      ⟨(mem_Icc.mp ht₀).1, by have := (mem_Icc.mp ht₁).2; omega⟩⟩

/-- Any selected distinct components charge each internal edge at most once. -/
theorem sum_edge_cost_le {B : Finset ℕ} {n : ℕ}
    (I : Finset (components B n)) (cost : ℕ → ℝ)
    (hcost : ∀ e ∈ B, 0 ≤ cost e) :
    (∑ c ∈ I, ∑ e ∈ edges c, cost e) ≤ ∑ e ∈ B ∩ range n, cost e := by
  calc
    _ = ∑ e ∈ I.biUnion edges, cost e :=
      (sum_biUnion (fun c _ d _ hcd => edges_pairwiseDisjoint hcd)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by
        intro e he
        obtain ⟨c, _, hc⟩ := mem_biUnion.mp he
        exact mem_inter.mpr ⟨edges_subset c hc, edges_subset_range c hc⟩)
      (fun e he _ => hcost e (mem_inter.mp he).1)

/-- The component interval and the reusable oscillation interval coincide. -/
theorem times_eq_intervalTimes {B : Finset ℕ} {n : ℕ} (c : components B n) :
    times c = IntervalOscillation.times (first c) (last c) := by
  rw [times_eq_Icc, IntervalOscillation.times, max_eq_right (first_le_last c)]

def rawLower {B : Finset ℕ} {n : ℕ} (x : ℕ → ℕ) (c : components B n) : ℕ :=
  IntervalOscillation.lower x (first c) (last c)

def rawUpper {B : Finset ℕ} {n : ℕ} (x : ℕ → ℕ) (c : components B n) : ℕ :=
  IntervalOscillation.upper x (first c) (last c)

/-- Diameter of the closed raw-coordinate interval, not its cardinality. -/
def rawWidth {B : Finset ℕ} {n : ℕ} (x : ℕ → ℕ) (c : components B n) : ℕ :=
  rawUpper x c - rawLower x c

def rawInterval {B : Finset ℕ} {n : ℕ} (x : ℕ → ℕ) (c : components B n) : Finset ℕ :=
  Icc (rawLower x c) (rawUpper x c)

theorem rawLower_le_rawUpper {B : Finset ℕ} {n : ℕ}
    (x : ℕ → ℕ) (c : components B n) : rawLower x c ≤ rawUpper x c :=
  IntervalOscillation.lower_le_upper x (first c) (last c)

theorem rawLower_attained {B : Finset ℕ} {n : ℕ}
    (x : ℕ → ℕ) (c : components B n) : ∃ t ∈ times c, rawLower x c = x t := by
  rw [times_eq_intervalTimes]
  exact IntervalOscillation.lower_attained x (first c) (last c)

theorem rawUpper_attained {B : Finset ℕ} {n : ℕ}
    (x : ℕ → ℕ) (c : components B n) : ∃ t ∈ times c, rawUpper x c = x t := by
  rw [times_eq_intervalTimes]
  exact IntervalOscillation.upper_attained x (first c) (last c)

theorem mem_rawInterval_of_mem_times {B : Finset ℕ} {n t : ℕ}
    {x : ℕ → ℕ} {c : components B n} (ht : t ∈ times c) : x t ∈ rawInterval x c := by
  rw [times_eq_intervalTimes] at ht
  exact mem_Icc.mpr ⟨IntervalOscillation.lower_le ht, IntervalOscillation.le_upper ht⟩

theorem mem_rawInterval_ofTime {B : Finset ℕ} {n t : ℕ}
    (x : ℕ → ℕ) (ht : t ≤ n) : x t ∈ rawInterval x (ofTime B n t ht) :=
  mem_rawInterval_of_mem_times (mem_times.mpr ⟨ht, rfl⟩)

theorem rawInterval_card {B : Finset ℕ} {n : ℕ}
    (x : ℕ → ℕ) (c : components B n) : (rawInterval x c).card = rawWidth x c + 1 := by
  rw [rawInterval, Nat.card_Icc]
  have := rawLower_le_rawUpper x c
  unfold rawWidth
  omega

theorem rawUpper_lt {B : Finset ℕ} {n L : ℕ} {x : ℕ → ℕ}
    (hx : ∀ t ≤ n, x t < L) (c : components B n) : rawUpper x c < L := by
  obtain ⟨t, ht, heq⟩ := rawUpper_attained x c
  rw [heq]
  exact hx t (mem_times.mp ht).1

theorem rawInterval_subset_range {B : Finset ℕ} {n L : ℕ} {x : ℕ → ℕ}
    (hx : ∀ t ≤ n, x t < L) (c : components B n) : rawInterval x c ⊆ range L := by
  intro z hz
  exact mem_range.mpr ((mem_Icc.mp hz).2.trans_lt (rawUpper_lt hx c))

/-- Range lengths of any distinct selected components charge only allowed
elementary movement, with no factor for the number of selected components. -/
theorem sum_rawWidth_le {B : Finset ℕ} {n : ℕ} (x : ℕ → ℕ)
    (I : Finset (components B n)) :
    (∑ c ∈ I, (rawWidth x c : ℝ)) ≤
      ∑ e ∈ B ∩ range n, dist (x e : ℝ) (x (e + 1) : ℝ) := by
  calc
    _ ≤ ∑ c ∈ I, ∑ e ∈ edges c, dist (x e : ℝ) (x (e + 1) : ℝ) :=
      sum_le_sum fun c _ => IntervalOscillation.oscillation_le_interval_variation x (first_le_last c)
    _ ≤ _ := sum_edge_cost_le I _ (fun _ _ => dist_nonneg)

end
end LeanMachine.TimeComponents

import BoundedNesting.WalkDag
import LeanMachine.FiniteIncidence

/-!
# Accounting for complete actual return families

Reuse Paper 8's actual hops, first-maximum owners, complete families,
and nesting/height estimates. Selections are sets of complete families;
no hop is removed before a family is formed.
-/

namespace SourceCovers

open BoundedNesting Finset
open scoped BigOperators

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- Finite unit-step walks extend constantly, so the infinite-time convention
in the reused library imposes no requirement on a finite computation. -/
theorem constant_extension_isWalk (x : ℕ → ℤ) (B : ℕ)
    (hx : ∀ t < B, |x (t + 1) - x t| ≤ 1) : IsWalk (fun t => x (min t B)) := by
  intro t
  by_cases ht : t < B
  · simpa only [min_eq_left ht.le, min_eq_left (show t + 1 ≤ B by omega)] using hx t ht
  · have hBt : B ≤ t := Nat.le_of_not_gt ht
    simp only [min_eq_right hBt, min_eq_right (hBt.trans (Nat.le_succ t)), sub_self, abs_zero]
    exact zero_le_one

/-- The first maximum-distance owner of each actual hop, as in Paper 8. -/
abbrev actualOwner (xs : Fin k → ℕ → ℤ) (η : Fin k × ℕ × ℕ) : ℕ :=
  hopOwner (xs η.1) η.2.1 η.2.2

/-- Complete families formed from all actual long hops, before selection. -/
abbrev ActualFamily (xs : Fin k → ℕ → ℤ) (T : ℕ) :=
  Keys xs (allHops xs T) (actualOwner xs)

namespace ActualFamily

abbrev hops (q : ActualFamily xs T) := fam xs (allHops xs T) (actualOwner xs) q.1
abbrev start (q : ActualFamily xs T) := famP xs (allHops xs T) (actualOwner xs) q
abbrev stop (q : ActualFamily xs T) := famU xs (allHops xs T) (actualOwner xs) q
abbrev owner (q : ActualFamily xs T) := q.1.2.2

/-- Elementary edges of the full span: `e` denotes the boundary `e | e+1`. -/
def edges (q : ActualFamily xs T) : Finset ℕ := Ico q.start q.stop

end ActualFamily

/-- Edge indexing agrees exactly with the full half-open span `(p,U]`. -/
theorem mem_family_edges_iff (q : ActualFamily xs T) (e : ℕ) :
    e ∈ q.edges ↔ q.start < e + 1 ∧ e + 1 ≤ q.stop := by
  simp only [ActualFamily.edges, mem_Ico]
  omega

private theorem actual_hops (η : Fin k × ℕ × ℕ) (hη : η ∈ allHops xs T) :
    IsHop (xs η.1) T η.2.1 η.2.2 := mem_allHops.mp hη

private theorem actual_owners (η : Fin k × ℕ × ℕ) (hη : η ∈ allHops xs T) :
    η.2.1 < actualOwner xs η ∧ actualOwner xs η < η.2.2 := by
  have h := hopOwner_spec (xs η.1) (actual_hops η hη).1
  exact ⟨h.1, h.2.1⟩

/-- Every hop contains its owner strictly; no geometric hypothesis is needed. -/
theorem family_owner_inside (q : ActualFamily xs T) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ q.hops) : η.2.1 < q.owner ∧ q.owner < η.2.2 := by
  obtain ⟨hH, _, _, ho⟩ := mem_fam.mp hη
  simpa only [ho] using actual_owners η hH

/-- Increasing ends have strictly decreasing starts in each actual family. -/
theorem family_hop_order (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T)
    {η η' : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) (hη' : η' ∈ q.hops)
    (hu : η.2.2 < η'.2.2) : η'.2.1 < η.2.1 := by
  by_contra h
  have := fam_nested hx actual_hops actual_owners hη hη' (Nat.le_of_not_gt h)
  omega

/-- Distinct hops of one family are strictly nested, including both endpoints. -/
theorem family_hops_nested (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T)
    {η η' : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) (hη' : η' ∈ q.hops) (hne : η ≠ η') :
    (η.2.1 < η'.2.1 ∧ η'.2.2 < η.2.2) ∨
      (η'.2.1 < η.2.1 ∧ η.2.2 < η'.2.2) := by
  rcases lt_trichotomy η.2.2 η'.2.2 with hu | hu | hu
  · exact Or.inr ⟨family_hop_order hx q hη hη' hu, hu⟩
  · have hh : η.1 = η'.1 := (mem_fam.mp hη).2.1.trans (mem_fam.mp hη').2.1.symm
    have h' : IsHop (xs q.1.1) T η'.2.1 η.2.2 := by
      rw [hu]
      exact fam_hop actual_hops hη'
    exact False.elim (hne (Prod.ext hh (Prod.ext (hop_end_unique (fam_hop actual_hops hη) h') hu)))
  · exact Or.inl ⟨family_hop_order hx q hη' hη hu, hu⟩

/-- The outer span is itself an actual hop of the family. -/
theorem family_span_hop (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T) :
    ∃ η ∈ q.hops, η.2.1 = q.start ∧ η.2.2 = q.stop :=
  fam_span hx actual_hops actual_owners q

/-- Keeping the owner's location gives a stronger bound than half the span. -/
theorem family_size_le_owner_arms (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T) :
    q.hops.card ≤ min (q.owner - q.start) (q.stop - q.owner) := by
  have hc := card_fam_le hx actual_hops actual_owners q
  obtain ⟨hp, hu, hhigh⟩ := fam_owner hx actual_hops actual_owners q
  have hw := isWalk_sw hx q.1.1 q.1.2.1
  have hleft := hw.lip hp.le
  have hright := hw.lip hu.le
  obtain ⟨η, hη, hP, hU⟩ := family_span_hop hx q
  have he := (fam_up hx actual_hops hη).2
  rw [hP, hU] at he
  unfold famd at hc
  have hn := Int.toNat_of_nonneg (sub_nonneg.mpr hhigh.le)
  change q.hops.card ≤ _ at hc
  change q.start < q.owner at hp
  change q.owner < q.stop at hu
  dsimp only [ActualFamily.start, ActualFamily.stop, ActualFamily.owner,
    ActualFamily.hops] at *
  exact le_min (by omega) (by omega)

/-- Integral half-span bound, including odd span lengths. -/
theorem two_mul_family_size_le_span (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T) :
    2 * q.hops.card ≤ q.stop - q.start := by
  have hc := family_size_le_owner_arms hx q
  have ho := fam_owner hx actual_hops actual_owners q
  change q.start < q.owner ∧ q.owner < q.stop ∧ _ at ho
  omega

private theorem family_edges_subset (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T) :
    q.edges ⊆ range (T - 1) := by
  obtain ⟨η, hη, _, hU⟩ := family_span_hop hx q
  have ht := (actual_hops η (mem_fam.mp hη).1).2.1
  intro e he
  obtain ⟨_, he⟩ := mem_Ico.mp he
  exact mem_range.mpr (by omega)

/-- Families whose full spans cross an elementary time boundary. -/
def activeFamilies (K : Finset (ActualFamily xs T)) (e : ℕ) : Finset (ActualFamily xs T) :=
  K.filter (fun q => e ∈ q.edges)

/-- An explicit partition into `N` disjoint-span classes, empty classes allowed. -/
def HasSpanColoring (K : Finset (ActualFamily xs T)) (N : ℕ) : Prop :=
  ∃ color : ActualFamily xs T → ℕ, (∀ q ∈ K, color q < N) ∧
    ∀ q ∈ K, ∀ q' ∈ K, q ≠ q' → color q = color q' → Disjoint q.edges q'.edges

/-- Restrict a full-system span partition to any selected or unselected subfamily. -/
theorem HasSpanColoring.mono {K K' : Finset (ActualFamily xs T)} {N : ℕ}
    (hc : HasSpanColoring K N) (hsub : K' ⊆ K) : HasSpanColoring K' N := by
  obtain ⟨color, hb, hd⟩ := hc
  exact ⟨color, fun q hq => hb q (hsub hq),
    fun q hq q' hq' => hd q (hsub hq) q' (hsub hq')⟩

/-- A span coloring bounds the actual multiplicity at every boundary. -/
theorem activeFamilies_card_le {K : Finset (ActualFamily xs T)} {N : ℕ}
    (hc : HasSpanColoring K N) (e : ℕ) : (activeFamilies K e).card ≤ N := by
  obtain ⟨color, hcolor, hd⟩ := hc
  simpa only [activeFamilies, ActualFamily.edges, mem_Ico, card_range] using
    LeanMachine.FiniteIncidence.multiplicity_le_of_coloring K ActualFamily.edges
      (range N) color (fun q hq => mem_range.mpr (hcolor q hq)) hd e

/-- Exact edge-weight accounting. Nonnegativity is unnecessary for the identity. -/
theorem sum_family_edge_weights {M : Type*} [AddCommMonoid M]
    (hx : ∀ h, IsWalk (xs h)) (K : Finset (ActualFamily xs T)) (w : ℕ → M) :
    (∑ q ∈ K, ∑ e ∈ q.edges, w e) =
      ∑ e ∈ range (T - 1), (activeFamilies K e).card • w e := by
  simpa only [activeFamilies, ActualFamily.edges, mem_Ico] using
    LeanMachine.FiniteIncidence.sum_eq_sum_multiplicity K (range (T - 1))
      ActualFamily.edges w (fun q _ => family_edges_subset hx q)

/-- The exact overlap profile bounds total hop mass. -/
theorem two_mul_sum_family_size_le (hx : ∀ h, IsWalk (xs h))
    (K : Finset (ActualFamily xs T)) :
    2 * (∑ q ∈ K, q.hops.card) ≤ ∑ e ∈ range (T - 1), (activeFamilies K e).card := by
  calc
    _ = ∑ q ∈ K, 2 * q.hops.card := by rw [mul_sum]
    _ ≤ ∑ q ∈ K, q.edges.card := by
      apply sum_le_sum
      intro q _
      simpa [ActualFamily.edges] using two_mul_family_size_le_span hx q
    _ = _ := by simpa using sum_family_edge_weights hx K (fun _ => (1 : ℕ))

/-- Bounded overlap suffices, even without supplying a span coloring. -/
theorem family_size_sum_le (hx : ∀ h, IsWalk (xs h))
    (K : Finset (ActualFamily xs T)) (N : ℕ)
    (hN : ∀ e ∈ range (T - 1), (activeFamilies K e).card ≤ N) :
    2 * (∑ q ∈ K, q.hops.card) ≤ N * (T - 1) := by
  calc
    _ ≤ ∑ e ∈ range (T - 1), (activeFamilies K e).card := two_mul_sum_family_size_le hx K
    _ ≤ ∑ _e ∈ range (T - 1), N := sum_le_sum hN
    _ = _ := by simp [Nat.mul_comm]

/-- Real variation is counted with its actual edge multiplicity. -/
theorem sum_family_variation_eq (hx : ∀ h, IsWalk (xs h))
    (K : Finset (ActualFamily xs T)) (Y : ℕ → ℝ) :
    (∑ q ∈ K, ∑ e ∈ q.edges, |Y (e + 1) - Y e|) =
      ∑ e ∈ range (T - 1), ((activeFamilies K e).card : ℝ) * |Y (e + 1) - Y e| := by
  simpa only [nsmul_eq_mul] using sum_family_edge_weights hx K (fun e => |Y (e + 1) - Y e|)

/-- Variation bound for any real path, without a unit-step hypothesis on that path. -/
theorem sum_family_variation_le (hx : ∀ h, IsWalk (xs h))
    (K : Finset (ActualFamily xs T)) (Y : ℕ → ℝ) (N : ℕ)
    (hN : ∀ e ∈ range (T - 1), (activeFamilies K e).card ≤ N) :
    (∑ q ∈ K, ∑ e ∈ q.edges, |Y (e + 1) - Y e|) ≤
      N * ∑ e ∈ range (T - 1), |Y (e + 1) - Y e| := by
  rw [sum_family_variation_eq hx, mul_sum]
  exact sum_le_sum fun e he => mul_le_mul_of_nonneg_right (by exact_mod_cast hN e he) (abs_nonneg _)

/-- The manuscript's Q2 estimates are direct specializations of the overlap bounds. -/
theorem q2_accounting (hx : ∀ h, IsWalk (xs h))
    (K : Finset (ActualFamily xs T)) (hc : HasSpanColoring K 2) (Y : ℕ → ℝ)
    (hstep : ∀ e ∈ range (T - 1), |Y (e + 1) - Y e| ≤ 1) :
    (∑ q ∈ K, q.hops.card) ≤ T - 1 ∧
      (∑ q ∈ K, ∑ e ∈ q.edges, |Y (e + 1) - Y e|) ≤
        2 * (∑ e ∈ range (T - 1), |Y (e + 1) - Y e|) ∧
      2 * (∑ e ∈ range (T - 1), |Y (e + 1) - Y e|) ≤ 2 * (T - 1 : ℕ) := by
  have hN : ∀ e ∈ range (T - 1), (activeFamilies K e).card ≤ 2 := fun e _ => activeFamilies_card_le hc e
  refine ⟨by have := family_size_sum_le hx K 2 hN; omega,
    sum_family_variation_le hx K Y 2 hN, ?_⟩
  have hv : (∑ e ∈ range (T - 1), |Y (e + 1) - Y e|) ≤ (T - 1 : ℕ) := by
    simpa using sum_le_sum hstep
  linarith

/-- Actual long hops crossing the elementary boundary `e | e+1`. -/
def crossingHops (q : ActualFamily xs T) (e : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  q.hops.filter (fun η => η.2.1 ≤ e ∧ e < η.2.2)

/-- The state lower endpoint and the distinct crossing-work lower endpoints.
For `e < T - 1` this is exactly the boundary set for the families in `K`. -/
def boundaryLowers (K : Finset (ActualFamily xs T)) (e : ℕ) : Finset ℕ :=
  insert e ((activeFamilies K e).biUnion (fun q => (crossingHops q e).image (fun η => η.2.1)))

/-- Restricting the union to active families discards no crossing hop. -/
theorem mem_boundaryLowers {K : Finset (ActualFamily xs T)} {e a : ℕ} :
    a ∈ boundaryLowers K e ↔ a = e ∨ ∃ q ∈ K, ∃ η ∈ q.hops,
      η.2.1 ≤ e ∧ e < η.2.2 ∧ η.2.1 = a := by
  classical
  constructor
  · intro ha
    rcases mem_insert.mp ha with he | ha
    · exact Or.inl he
    · obtain ⟨q, hq, ha⟩ := mem_biUnion.mp ha
      obtain ⟨η, hη, he⟩ := mem_image.mp ha
      obtain ⟨hη, hp, hu⟩ := mem_filter.mp hη
      exact Or.inr ⟨q, (mem_filter.mp hq).1, η, hη, hp, hu, he⟩
  · rintro (rfl | ⟨q, hq, η, hη, hp, hu, he⟩)
    · exact mem_insert_self _ _
    · have hb := fam_bounds hη
      have hactive : q ∈ activeFamilies K e :=
        mem_filter.mpr ⟨hq, mem_Ico.mpr ⟨hb.1.trans hp, hu.trans_le hb.2⟩⟩
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨q, hactive,
        mem_image.mpr ⟨η, mem_filter.mpr ⟨hη, hp, hu⟩, he⟩⟩)

/-- Keep each family's actual number of crossing hops before any uniform bound. -/
theorem boundary_lowers_le_crossings (K : Finset (ActualFamily xs T)) (e : ℕ) :
    (boundaryLowers K e).card ≤ 1 + ∑ q ∈ activeFamilies K e, (crossingHops q e).card := by
  classical
  calc
    _ ≤ ((activeFamilies K e).biUnion
        (fun q => (crossingHops q e).image (fun η => η.2.1))).card + 1 := card_insert_le _ _
    _ ≤ (∑ q ∈ activeFamilies K e, (crossingHops q e).card) + 1 := by
      apply Nat.add_le_add_right
      exact card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)
    _ = _ := Nat.add_comm _ _

/-- The local family-size bill retains the actual set of active families. -/
theorem boundary_lowers_le_family_sizes (K : Finset (ActualFamily xs T)) (e : ℕ) :
    (boundaryLowers K e).card ≤ 1 + ∑ q ∈ activeFamilies K e, q.hops.card := by
  exact (boundary_lowers_le_crossings K e).trans (Nat.add_le_add_left
    (sum_le_sum fun q _ => card_le_card (filter_subset _ _)) 1)

/-- The original `1 + N a` estimate needs only local overlap and size bounds. -/
theorem boundary_lowers_le (K : Finset (ActualFamily xs T)) (e a N : ℕ)
    (hsize : ∀ q ∈ K, q.hops.card ≤ a) (hN : (activeFamilies K e).card ≤ N) :
    (boundaryLowers K e).card ≤ 1 + N * a := by
  calc
    _ ≤ 1 + ∑ q ∈ activeFamilies K e, q.hops.card := boundary_lowers_le_family_sizes K e
    _ ≤ 1 + ∑ _q ∈ activeFamilies K e, a :=
      Nat.add_le_add_left (sum_le_sum fun q hq => hsize q (mem_filter.mp hq).1) 1
    _ = 1 + (activeFamilies K e).card * a := by simp
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right a hN) 1

end
end SourceCovers

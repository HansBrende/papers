import SourceCovers.ContinuationCovers
import SourceCovers.FractionalGap
import LeanMachine.IndexedSourceBank
import LeanMachine.IntervalClusterErosion

/-! Clustered complete older continuations. Clusters may overlap; only an
interval cover of the nonroot suppliers and one anchor per interval is needed. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators ENNReal
noncomputable section

def rawBankHull (B : Bank) (x : ℕ → ℕ) (R : Finset ℕ) : Finset ℕ :=
  (R.biUnion (values B)).image x

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)}

theorem rawBankHull_range {F : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank F B) (x : ℕ → ℕ) {L : ℕ}
    (hx : ∀ u < T, x u < L) {R : Finset ℕ} (hR : ∀ u ∈ R, u < T) :
    rawBankHull B x R ⊆ range L := by
  rintro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  obtain ⟨r, hr, hur⟩ := mem_biUnion.mp hu
  exact mem_range.mpr (hx u ((shadowOrbit_le ((hB r).subset hur)).trans_lt (hR r hr)))

theorem olderBank_hull_fractional_bound (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (e : Option (ActualFamily xs T)) {B : Bank}
    (hB : ExactCoreBank (retainedCore K M ρ ∪ e.toList.toFinset) B)
    (x : ℕ → ℕ) (S : Finset ℕ) (hS : ∀ u ∈ S, u < T) :
    fractionalCoreCover (phaseSurvivors K M ρ) x (rawBankHull B x S) ≠ ⊤ ∧
      (fractionalCoreCover (phaseSurvivors K M ρ) x (rawBankHull B x S)).toReal ≤
        (2 * (M : ℝ) + 4) * S.card := by
  let hA := coreBank_exact hc hM hρ
  have heq (u : ℕ) : values (oneExceptionBank (coreBank (ρ := ρ) hc hM) e) u = values B u :=
    coe_injective ((oneExceptionBank_exact hA e u).trans (hB u).symm)
  obtain ⟨R, hR, he⟩ := hA.closure.hull_extension_core_cover_uniform
    (oneExceptionBank_exact hA e).closure (exceptionMap e)
    (oneExceptionBank_decomposition hA e) (coreBank_values_card hc hM hρ) S
  have he' : hA.closure.hull R = S.biUnion (values B) := by
    simpa only [CausalClosure.hull, ExactCoreBank.closure, funext heq] using he
  have h := fractionalCoreCover_le_time_roots hc hρ x (S := rawBankHull B x S) R (by
    intro r hr
    have hm : r ∈ hA.closure.hull R := mem_biUnion.mpr ⟨r, hr, hA.root_mem r⟩
    rw [he'] at hm
    obtain ⟨u, hu, hru⟩ := mem_biUnion.mp hm
    exact (shadowOrbit_le ((hB u).subset hru)).trans_lt (hS u hu)) (by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    rw [← he'] at hu
    obtain ⟨r, hr, hur⟩ := mem_biUnion.mp hu
    exact ⟨r, hr, u, (hA r).subset hur, rfl⟩)
  exact ⟨h.1, h.2.trans (by exact_mod_cast hR)⟩

def clusterRoots {ι : Type*} [Fintype ι] (t : ℕ) (rep : ι → ℕ) : Finset ℕ :=
  insert t (univ.image rep)

theorem clusterRoots_card {ι : Type*} [Fintype ι] (t : ℕ) (rep : ι → ℕ) :
    (clusterRoots t rep).card ≤ Fintype.card ι + 1 :=
  (card_insert_le ..).trans (Nat.add_le_add_right (card_image_le.trans_eq (card_univ)) 1)

theorem clusterRoots_lt {ι : Type*} [Fintype ι] {t T : ℕ} {rep : ι → ℕ}
    (ht : t < T) (hrep : ∀ v, rep v < T) : ∀ u ∈ clusterRoots t rep, u < T := by
  simpa [clusterRoots] using And.intro ht hrep

def clusterVariation {ι : Type*} [Fintype ι] (B : Bank) (x : ℕ → ℕ)
    (first last : ι → ℕ) : ℝ :=
  ∑ v, ∑ i : Fin B.length, ∑ u ∈ Ico (first v) (last v),
    dist (x (indexed B i u) : ℝ) (x (indexed B i (u + 1)) : ℝ)

/-- Complete older-bank movement controls the target gap, with a quadratic
saving. An interval cover is sufficient; disjointness and exact hulls are
unnecessary, and representatives may be any times in their intervals. -/
theorem continuationClusters_erosion {A B : Bank}
    (hA : ExactCoreBank K A) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    (hB : ExactCoreBank (K ∪ e.toList.toFinset) B)
    (x : ℕ → ℕ) {L t : ℕ} (ht : t < T) (hx : ∀ u < T, x u < L)
    {ι : Type*} [Fintype ι] (first last rep : ι → ℕ)
    (hrep : ∀ v, first v ≤ rep v ∧ rep v ≤ last v)
    (hlast : ∀ v, last v < T)
    (hcover : ∀ u ∈ continuationSuppliers hA g e t, u ≠ t →
      ∃ v, first v ≤ u ∧ u ≤ last v) :
    let S₀ := rawBankHull B x (clusterRoots t rep)
    let S := rawBankValues (twoExceptionBank A g e) x t
    ∀ (hS₀ : S₀.Nonempty) (hS : S.Nonempty),
    GapErosion.pointArea (range S₀.card) (CyclicSelection.gap L S₀ hS₀) L -
      AnchoredGapErosion.penalty (min (clusterVariation B x first last / L) 1) ≤
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  intro S₀ S hS₀ hS
  have hroots := clusterRoots_lt ht (fun v => (hrep v).2.trans_lt (hlast v))
  have hsource : S ⊆ range L := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    exact mem_range.mpr (hx u ((shadowOrbit_le
      ((twoExceptionBank_exact hA g e horder t).subset hu)).trans_lt ht))
  have hslot (i : Fin B.length) (u : ℕ) : indexed B i u ∈ values B u := by
    rw [← indexed_values]
    exact mem_image_of_mem _ (mem_univ i)
  apply IntervalClusterErosion.area_lower_bound hS₀ (rawBankHull_range hB x hx hroots)
    hS hsource (univ : Finset (ι × Fin B.length))
    (fun vi u => x (indexed B vi.2 u)) (fun vi => first vi.1)
    (fun vi => last vi.1) (fun vi => rep vi.1)
  · intro vi _
    exact hrep vi.1
  · intro vi _ u _ hu
    exact hx _ ((shadowOrbit_le ((hB u).subset (hslot vi.2 u))).trans_lt
      (hu.trans_lt (hlast vi.1)))
  · intro vi _
    exact mem_image.mpr ⟨_, mem_biUnion.mpr ⟨rep vi.1,
      mem_insert_of_mem (mem_image_of_mem rep (mem_univ vi.1)), hslot vi.2 _⟩, rfl⟩
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    rw [continuationSuppliers_exact_bank hA g e hB t] at hu
    obtain ⟨s, hs, hus⟩ := mem_biUnion.mp hu
    by_cases he : s = t
    · subst s
      exact Or.inl (mem_image.mpr ⟨u, mem_biUnion.mpr ⟨t, mem_insert_self _ _, hus⟩, rfl⟩)
    · obtain ⟨v, hv₁, hv₂⟩ := hcover s hs he
      rw [← indexed_values] at hus
      obtain ⟨i, _, hi⟩ := mem_image.mp hus
      exact Or.inr ⟨(v, i), mem_univ _, s, hv₁, hv₂, congrArg x hi⟩
  · simp only [clusterVariation, Fintype.sum_prod_type]
    exact le_rfl

/-- Proposition 3.7(c), strengthened to arbitrary interval covers, arbitrary
exact older banks, and the clipped quadratic erosion penalty. -/
theorem continuationClusters_gap (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    {B : Bank} (hB : ExactCoreBank (retainedCore K M ρ ∪ e.toList.toFinset) B)
    (x : ℕ → ℕ) {L t : ℕ} (ht : t < T) (hx : ∀ u < T, x u < L)
    {ι : Type*} [Fintype ι] (first last rep : ι → ℕ)
    (hrep : ∀ v, first v ≤ rep v ∧ rep v ≤ last v)
    (hlast : ∀ v, last v < T)
    (hcover : ∀ u ∈ continuationSuppliers (coreBank_exact hc hM hρ) g e t, u ≠ t →
      ∃ v, first v ≤ u ∧ u ≤ last v)
    (D : Finset (CoreFamily K)) {r : ℕ} (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ q ∈ univ \ D, ∑ u ∈ q.val.edges,
      dist (x u : ℝ) (x (u + 1) : ℝ)) ≤ α * L) :
    let A := coreBank (ρ := ρ) hc hM
    let S := rawBankValues (twoExceptionBank A g e) x t
    ∀ hS : S.Nonempty,
    max (1 - α) 0 ^ 2 /
      (2 * (2 * (r : ℝ) + 1) * ((2 * (M : ℝ) + 4) * (Fintype.card ι + 1))) -
      AnchoredGapErosion.penalty (min (clusterVariation B x first last / L) 1) ≤
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  intro A S hS
  let S₀ := rawBankHull B x (clusterRoots t rep)
  have hS₀ : S₀.Nonempty := ⟨x t, mem_image.mpr
    ⟨t, mem_biUnion.mpr ⟨t, mem_insert_self _ _, hB.root_mem t⟩, rfl⟩⟩
  have hroots := clusterRoots_lt ht (fun v => (hrep v).2.trans_lt (hlast v))
  have hL : 0 < L := Nat.zero_lt_of_lt (hx t ht)
  have hfinite := olderBank_hull_fractional_bound hc hM hρ e hB x _ hroots
  have hκ : (fractionalCoreCover (phaseSurvivors K M ρ) x S₀).toReal ≤
      (2 * (M : ℝ) + 4) * (Fintype.card ι + 1) :=
    hfinite.2.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast clusterRoots_card t rep) (by positivity))
  have hone := one_le_fractionalCoreCover_toReal (phaseSurvivors K M ρ) x hS₀ hfinite.1
  have hbase := fractional_phase_gap hc D M ρ x hL hD hS₀
    (rawBankHull_range hB x hx hroots) hfinite.1 hV
  have hbase' : max (1 - α) 0 ^ 2 /
      (2 * (2 * (r : ℝ) + 1) * ((2 * (M : ℝ) + 4) * (Fintype.card ι + 1))) ≤
      GapErosion.pointArea (range S₀.card) (CyclicSelection.gap L S₀ hS₀) L := by
    apply le_trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left hκ (by positivity))) hbase
  have herosion := continuationClusters_erosion (coreBank_exact hc hM hρ) g e horder
    hB x ht hx first last rep hrep hlast hcover hS₀ hS
  exact (sub_le_sub_right hbase' _).trans herosion

/-- The original linear movement loss is an immediate corollary of the
stronger quadratic estimate, with exactly the same hypotheses. -/
theorem continuationClusters_gap_linear (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    {B : Bank} (hB : ExactCoreBank (retainedCore K M ρ ∪ e.toList.toFinset) B)
    (x : ℕ → ℕ) {L t : ℕ} (ht : t < T) (hx : ∀ u < T, x u < L)
    {ι : Type*} [Fintype ι] (first last rep : ι → ℕ)
    (hrep : ∀ v, first v ≤ rep v ∧ rep v ≤ last v)
    (hlast : ∀ v, last v < T)
    (hcover : ∀ u ∈ continuationSuppliers (coreBank_exact hc hM hρ) g e t, u ≠ t →
      ∃ v, first v ≤ u ∧ u ≤ last v)
    (D : Finset (CoreFamily K)) {r : ℕ} (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ q ∈ univ \ D, ∑ u ∈ q.val.edges,
      dist (x u : ℝ) (x (u + 1) : ℝ)) ≤ α * L) :
    let S := rawBankValues (twoExceptionBank (coreBank (ρ := ρ) hc hM) g e) x t
    ∀ hS : S.Nonempty,
    max (1 - α) 0 ^ 2 /
      (2 * (2 * (r : ℝ) + 1) * ((2 * (M : ℝ) + 4) * (Fintype.card ι + 1))) -
      clusterVariation B x first last / L ≤
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  intro S hS
  have h := continuationClusters_gap hc hM hρ g e horder hB x ht hx
    first last rep hrep hlast hcover D hD hV hS
  have hp := (AnchoredGapErosion.penalty_le_self
    (min (clusterVariation B x first last / L) 1)).trans (min_le_left _ _)
  linarith

end
end SourceCovers

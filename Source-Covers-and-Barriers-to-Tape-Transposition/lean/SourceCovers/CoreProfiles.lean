import SourceCovers.FamilyAccounting
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-!
# Joint hop and variation profiles of an actual core

One ordering of the complete actual families is used for both profiles.
Only hop counts are sorted. Ties may be resolved arbitrarily, and the
profiles are zero after the last family. Indices are zero-based.
-/

namespace SourceCovers

open Classical Finset BoundedNesting
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- Any fixed hop ordering, with an arbitrary fixed choice among ties. -/
structure SortedCore (K : Finset (ActualFamily xs T)) where
  families : List (ActualFamily xs T)
  nodup : families.Nodup
  complete : families.toFinset = K
  hop_sorted : families.Pairwise (fun G H => H.hops.card ≤ G.hops.card)

theorem exists_sortedCore (K : Finset (ActualFamily xs T)) : Nonempty (SortedCore K) := by
  let cmp := fun G H : ActualFamily xs T => decide (H.hops.card ≤ G.hops.card)
  have hp := List.mergeSort_perm K.toList cmp
  refine ⟨⟨K.toList.mergeSort cmp, hp.nodup_iff.mpr K.nodup_toList, ?_, ?_⟩⟩
  · ext G
    simp only [List.mem_toFinset, hp.mem_iff, mem_toList]
  · simpa only [cmp, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := cmp)
        (fun G H I hGH hHI => by
          simp only [cmp, decide_eq_true_eq] at *
          exact hHI.trans hGH)
        (fun G H => by
          simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
          exact le_total _ _) K.toList

namespace SortedCore

variable {K : Finset (ActualFamily xs T)} (S : SortedCore K)

@[simp]
theorem length_eq_card : S.families.length = K.card := by
  exact (List.toFinset_card_of_nodup S.nodup).symm.trans (congrArg Finset.card S.complete)

@[simp]
theorem mem_families {G : ActualFamily xs T} : G ∈ S.families ↔ G ∈ K := by
  simpa only [S.complete] using (List.mem_toFinset (l := S.families) (a := G)).symm

/-- Normalize any family weight in the same ordering and pad with zero. -/
def profile (w : ActualFamily xs T → ℝ) (L i : ℕ) : ℝ :=
  if hi : i < S.families.length then w S.families[i] / L else 0

def hopProfile (L i : ℕ) : ℝ := S.profile (fun G => G.hops.card) L i

def variationProfile (x : ℕ → ℕ) (L i : ℕ) : ℝ :=
  S.profile (fun G => ∑ e ∈ G.edges, dist (x e : ℝ) (x (e + 1) : ℝ)) L i

theorem profile_eq_zero (w : ActualFamily xs T → ℝ) (L : ℕ) {i : ℕ}
    (hi : K.card ≤ i) : S.profile w L i = 0 := by
  simp only [profile, S.length_eq_card, dite_eq_right (Nat.not_lt.mpr hi)]

theorem profile_nonneg (w : ActualFamily xs T → ℝ)
    (hw : ∀ G ∈ K, 0 ≤ w G) (L i : ℕ) : 0 ≤ S.profile w L i := by
  unfold profile
  split_ifs with hi
  · exact div_nonneg (hw _ (S.mem_families.mp (List.getElem_mem hi))) (Nat.cast_nonneg L)
  · rfl

theorem hopProfile_nonneg (L i : ℕ) : 0 ≤ S.hopProfile L i :=
  S.profile_nonneg _ (fun G _ => Nat.cast_nonneg G.hops.card) L i

theorem variationProfile_nonneg (x : ℕ → ℕ) (L i : ℕ) :
    0 ≤ S.variationProfile x L i :=
  S.profile_nonneg _ (fun _ _ => sum_nonneg fun _ _ => dist_nonneg) L i

theorem hopProfile_pos {L i : ℕ} (hL : 0 < L) (hi : i < K.card) :
    0 < S.hopProfile L i := by
  have hi' : i < S.families.length := by simpa only [S.length_eq_card] using hi
  simp only [hopProfile, profile, dite_eq_left hi']
  apply div_pos _ (by exact_mod_cast hL)
  exact_mod_cast card_pos.mpr (fam_nonempty xs (allHops xs T) (actualOwner xs) S.families[i])

@[simp]
theorem hopProfile_eq_zero (L : ℕ) {i : ℕ} (hi : K.card ≤ i) :
    S.hopProfile L i = 0 := S.profile_eq_zero _ L hi

@[simp]
theorem variationProfile_eq_zero (x : ℕ → ℕ) (L : ℕ) {i : ℕ} (hi : K.card ≤ i) :
    S.variationProfile x L i = 0 := S.profile_eq_zero _ L hi

theorem hopProfile_antitone (L : ℕ) : Antitone (S.hopProfile L) := by
  intro i j hij
  by_cases hj : j < S.families.length
  · have hi : i < S.families.length := hij.trans_lt hj
    simp only [hopProfile, profile, dite_eq_left hi, dite_eq_left hj]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact_mod_cast S.hop_sorted.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
    · rfl
  · rw [hopProfile, profile, dite_eq_right hj]
    exact S.hopProfile_nonneg L i

theorem sum_weights (w : ActualFamily xs T → ℝ) :
    (∑ i : Fin S.families.length, w (S.families.get i)) = ∑ G ∈ K, w G := by
  apply sum_bij (fun i _ => S.families.get i)
  · intro i _
    exact S.mem_families.mp (List.get_mem _ _)
  · intro i _ j _ h
    exact S.nodup.injective_get h
  · intro G hG
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (S.mem_families.mpr hG)
    exact ⟨i, mem_univ _, hi⟩
  · intro i _
    rfl

/-- The full profile sum is exactly the total weight of the actual core. -/
theorem sum_profile_eq (w : ActualFamily xs T → ℝ) (L : ℕ) :
    (∑ i ∈ range K.card, S.profile w L i) = (∑ G ∈ K, w G) / L := by
  rw [← S.length_eq_card, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin S.families.length, w (S.families.get i) / L := by
      apply sum_congr rfl
      intro i _
      simp only [profile, dite_eq_left i.isLt, List.get_eq_getElem]
    _ = _ := by rw [← sum_div, S.sum_weights]

/-- Any finite coordinate set costs no more than the complete actual core. -/
theorem sum_profile_le (w : ActualFamily xs T → ℝ)
    (hw : ∀ G ∈ K, 0 ≤ w G) (L : ℕ) (s : Finset ℕ) :
    (∑ i ∈ s, S.profile w L i) ≤ (∑ G ∈ K, w G) / L := by
  have he : (∑ i ∈ s ∩ range K.card, S.profile w L i) =
      ∑ i ∈ s, S.profile w L i := by
    apply sum_subset inter_subset_left
    intro i hi hin
    apply S.profile_eq_zero
    by_contra h
    exact hin (mem_inter.mpr ⟨hi, mem_range.mpr (by omega)⟩)
  rw [← he, ← S.sum_profile_eq w L]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right
    (fun i _ _ => S.profile_nonneg w hw L i)

theorem sum_hopProfile_le (L : ℕ) (s : Finset ℕ) :
    (∑ i ∈ s, S.hopProfile L i) ≤ ((∑ G ∈ K, G.hops.card : ℕ) : ℝ) / L := by
  simpa only [hopProfile, Nat.cast_sum] using
    S.sum_profile_le (fun G => (G.hops.card : ℝ))
      (fun G _ => Nat.cast_nonneg G.hops.card) L s

theorem sum_variationProfile_le (x : ℕ → ℕ) (L : ℕ) (s : Finset ℕ) :
    (∑ i ∈ s, S.variationProfile x L i) ≤
      (∑ G ∈ K, ∑ e ∈ G.edges, dist (x e : ℝ) (x (e + 1) : ℝ)) / L :=
  S.sum_profile_le _ (fun _ _ => sum_nonneg fun _ _ => dist_nonneg) L s

/-- Prefixes contain whole actual families in the shared hop ordering. -/
def selectedPrefix (J : ℕ) : Finset (ActualFamily xs T) := (S.families.take J).toFinset

theorem selectedPrefix_subset (J : ℕ) : S.selectedPrefix J ⊆ K := by
  intro G hG
  exact S.mem_families.mp (List.mem_of_mem_take (List.mem_toFinset.mp hG))

@[simp]
theorem selectedPrefix_card (J : ℕ) : (S.selectedPrefix J).card = min J K.card := by
  rw [selectedPrefix, List.toFinset_card_of_nodup (S.nodup.sublist (List.take_sublist _ _)),
    List.length_take, S.length_eq_card]

private theorem sum_profile_take (w : ActualFamily xs T → ℝ) (L J : ℕ) :
    (∑ i ∈ range J, S.profile w L i) = ((S.families.map w).take J).sum / L := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih]
    by_cases hJ : J < S.families.length
    · have hmap : J < (S.families.map w).length := by simpa using hJ
      rw [List.sum_take_succ _ _ hmap, add_div]
      simp only [profile, dite_eq_left hJ, List.getElem_map]
    · have hmap : (S.families.map w).length ≤ J := by simp only [List.length_map]; omega
      rw [List.take_of_length_le hmap, List.take_of_length_le (hmap.trans (Nat.le_succ J))]
      simp only [profile, dite_eq_right hJ, add_zero]

/-- Prefix sums refer to these actual families, for any family weight. -/
theorem sum_profile_prefix (w : ActualFamily xs T → ℝ) (L J : ℕ) :
    (∑ i ∈ range J, S.profile w L i) = (∑ G ∈ S.selectedPrefix J, w G) / L := by
  rw [selectedPrefix, List.sum_toFinset _ (S.nodup.sublist (List.take_sublist _ _)), List.map_take]
  exact S.sum_profile_take w L J

/-- Sortedness bounds each omitted coordinate by the total mass divided by
the number of earlier coordinates, counting the coordinate itself. -/
theorem hopProfile_le_mass_div (L J : ℕ) :
    S.hopProfile L J ≤ ((∑ G ∈ K, G.hops.card : ℕ) : ℝ) / L / (J + 1) := by
  have hsum := S.sum_hopProfile_le L (range (J + 1))
  have hbelow : (J + 1 : ℝ) * S.hopProfile L J ≤
      ∑ i ∈ range (J + 1), S.hopProfile L i := by
    calc
      _ = ∑ _i ∈ range (J + 1), S.hopProfile L J := by simp
      _ ≤ _ := sum_le_sum fun i hi => S.hopProfile_antitone L (by have := mem_range.mp hi; omega)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < J + 1)).mpr
  simpa only [mul_comm] using hbelow.trans hsum

/-- Every actual family outside the first `J` has this hop-count bound. -/
theorem omitted_hops_le_total_div {J : ℕ} {G : ActualFamily xs T}
    (hG : G ∈ K) (hout : G ∉ S.selectedPrefix J) :
    (G.hops.card : ℝ) ≤ ((∑ H ∈ K, H.hops.card : ℕ) : ℝ) / (J + 1) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (S.mem_families.mpr hG)
  have hJi : J ≤ i := by
    by_contra h
    apply hout
    exact List.mem_toFinset.mpr (List.mem_take_iff_getElem.mpr
      ⟨i, by omega, heq⟩)
  have hvalue : S.hopProfile 1 i = G.hops.card := by
    simp only [hopProfile, profile, dite_eq_left hi, heq, Nat.cast_one, div_one]
  have h := (S.hopProfile_antitone 1 hJi).trans (S.hopProfile_le_mass_div 1 J)
  simpa only [hvalue, Nat.cast_one, div_one] using h

/-- Q2 family accounting supplies both mass bounds in the same hop ordering.
The raw variation is never independently sorted. -/
theorem profile_mass_bounds (hwalk : ∀ h, IsWalk (xs h)) (hc : HasSpanColoring K 2)
    (x : ℕ → ℕ) {L : ℕ} (hL : 0 < L)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    {c : ℝ} (hruntime : (T : ℝ) ≤ c * L) (s : Finset ℕ) :
    (∑ i ∈ s, S.hopProfile L i) ≤ c ∧
      (∑ i ∈ s, S.variationProfile x L i) ≤ 2 * c := by
  have hacc := q2_accounting hwalk K hc (fun t => (x t : ℝ)) (fun e he => by
    simpa only [Real.dist_eq, abs_sub_comm] using hstep e (mem_range.mp he))
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : ((T - 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T 1
  have htime : ((T - 1 : ℕ) : ℝ) ≤ c * L := hsub.trans hruntime
  constructor
  · apply (S.sum_hopProfile_le L s).trans
    apply (div_le_iff₀ hLR).mpr
    have hhop : ((∑ G ∈ K, G.hops.card : ℕ) : ℝ) ≤ ((T - 1 : ℕ) : ℝ) := by
      exact_mod_cast hacc.1
    exact hhop.trans htime
  · apply (S.sum_variationProfile_le x L s).trans
    apply (div_le_iff₀ hLR).mpr
    have hvariation : (∑ G ∈ K, ∑ e ∈ G.edges,
        dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ 2 * ((T - 1 : ℕ) : ℝ) := by
      simpa only [Real.dist_eq, abs_sub_comm] using hacc.2.1.trans hacc.2.2
    linarith

end SortedCore
end
end SourceCovers

import SourceCovers.AdmissibleGeometry
import SourceCovers.CoreProfiles

set_option autoImplicit false

/-!
# Actual finite prefixes in the paid deficit theorem

Selected, protected and distinguished sets contain the original complete
families in one hop ordering. Their full-span weights are exactly finite
coordinate sums. The protected and distinguished prefixes are independent;
neither is required to contain the other.
-/

namespace SourceCovers

open Classical Finset LeanMachine
open scoped BigOperators
noncomputable section

namespace SortedCore

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K₀ : Finset (ActualFamily xs T)}
    (O : SortedCore K₀)

theorem selectedPrefix_mono {I J : ℕ} (hIJ : I ≤ J) :
    O.selectedPrefix I ⊆ O.selectedPrefix J := by
  intro F hF
  obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hF)
  exact List.mem_toFinset.mpr (List.mem_take_iff_getElem.mpr ⟨i, by omega, heq⟩)

/-- A smaller original prefix viewed as families of the selected core. -/
def subprefix (J I : ℕ) : Finset (CoreFamily (O.selectedPrefix J)) :=
  univ.filter fun F => F.val ∈ O.selectedPrefix I

theorem subprefix_card_le (J I : ℕ) : (O.subprefix J I).card ≤ I := by
  have hcard : (O.subprefix J I).card ≤ (O.selectedPrefix I).card :=
    card_le_card_of_injOn Subtype.val (fun F hF => (mem_filter.mp hF).2)
      (fun _ _ _ _ h => Subtype.ext h)
  exact hcard.trans (by rw [O.selectedPrefix_card]; exact min_le_left _ _)

/-- Subtype conversion keeps the actual complement, for every additive weight. -/
theorem sum_subprefix_compl {A : Type*} [AddCommMonoid A]
    (w : ActualFamily xs T → A) (J I : ℕ) :
    (∑ F ∈ univ \ O.subprefix J I, w F.val) =
      ∑ F ∈ O.selectedPrefix J \ O.selectedPrefix I, w F := by
  apply sum_bij (fun F _ => F.val)
  · intro F hF
    exact mem_sdiff.mpr ⟨F.property, by
      simpa only [subprefix, mem_filter, mem_univ, true_and] using (mem_sdiff.mp hF).2⟩
  · intro F _ H _ h
    exact Subtype.ext h
  · intro F hF
    refine ⟨⟨F, (mem_sdiff.mp hF).1⟩, ?_, rfl⟩
    simpa only [mem_sdiff, subprefix, mem_filter, mem_univ, true_and] using (mem_sdiff.mp hF).2
  · intro F _
    rfl

/-- The zero-based interval `Ico I J` is exactly the family block after the
first `I` and through the first `J`, including zero padding. -/
theorem sum_profile_Ico (w : ActualFamily xs T → ℝ) (L : ℕ)
    {I J : ℕ} (hIJ : I ≤ J) :
    (∑ i ∈ Ico I J, O.profile w L i) =
      (∑ F ∈ O.selectedPrefix J \ O.selectedPrefix I, w F) / L := by
  rw [sum_Ico_eq_sub _ hIJ, O.sum_profile_prefix, O.sum_profile_prefix,
    ← sub_div, sum_sdiff_eq_sub (O.selectedPrefix_mono hIJ)]

theorem sum_subprefix_compl_eq (w : ActualFamily xs T → ℝ) {L I J : ℕ}
    (hL : 0 < L) (hIJ : I ≤ J) :
    (∑ F ∈ univ \ O.subprefix J I, w F.val) =
      (L : ℝ) * ∑ i ∈ Ico I J, O.profile w L i := by
  rw [O.sum_subprefix_compl, O.sum_profile_Ico w L hIJ]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

end SortedCore

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)
    (O : SortedCore G.core)

/-- The original outside bound and the actual omitted-prefix bound account
for every family outside the new selected core and the exceptions. -/
theorem prefix_outside_small {J a : ℕ} (ha0 : G.a0 ≤ a)
    (ha : c * G.inputLength / (J + 1) ≤ (a : ℝ)) :
    ∀ F : ActualFamily G.xs G.T,
      F ∉ O.selectedPrefix J ∪ G.exceptions → F.hops.card ≤ a := by
  have hacc := (q2_accounting G.work_walk G.core G.core_coloring
    (fun s => (G.x s : ℝ)) (fun e he => by
      simpa only [Real.dist_eq, abs_sub_comm] using G.raw_step e (mem_range.mp he))).1
  have htotal : ((∑ F ∈ G.core, F.hops.card : ℕ) : ℝ) ≤ c * G.inputLength := by
    calc
      _ ≤ ((G.T - 1 : ℕ) : ℝ) := by exact_mod_cast hacc
      _ ≤ (G.T : ℝ) := by exact_mod_cast Nat.sub_le G.T 1
      _ ≤ _ := by simpa only [inputLength, Nat.cast_mul] using G.runtime
  intro F hF
  by_cases hcore : F ∈ G.core
  · have hout : F ∉ O.selectedPrefix J := fun h => hF (mem_union_left _ h)
    have h := (O.omitted_hops_le_total_div hcore hout).trans
      ((div_le_div_of_nonneg_right htotal (by positivity)).trans ha)
    exact_mod_cast h
  · apply (G.outside_small F ?_).trans ha0
    intro h
    rcases mem_union.mp h with h | h
    · exact hcore h
    · exact hF (mem_union_right _ h)

/-- Actual complete-bank reciprocal mean, with the original first `J`
families and original first `R` protected ranks. -/
def prefixMeanReciprocal (J R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  meanReciprocalCover (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
    G.exceptions G.x G.t G.d G.b
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)

/-- The same finite mean is genuinely bounded, even when `R > J`. -/
theorem prefixMeanReciprocal_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    1 / (2 * (M : ℝ) + 4) ^ q ≤ G.prefixMeanReciprocal O J R M hM ∧
      G.prefixMeanReciprocal O J R M hM ≤ 1 := by
  have hA := (protected_phase_average (O.selectedPrefix J) (O.subprefix J R)
    (O.subprefix_card_le J R) hRM).1
  have hnonempty : (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).Nonempty :=
    card_pos.mp (lt_of_lt_of_le (Nat.sub_pos_of_lt hRM) hA)
  have h := meanReciprocalCover_bounds
    (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions G.x G.t
    G.hd G.hb G.append_lt _ hnonempty (fun _ hρ => admissiblePhase_lt hρ)
  refine ⟨?_, h.2⟩
  apply le_trans _ h.1
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ _ G.exceptions_card
  have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  linarith

/-- Retain the actual reciprocal-cover credit before any worst-case count.
The protected and distinguished prefixes remain independent. -/
theorem prefix_reciprocal_deficit {K R J M w a : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (ha0 : G.a0 ≤ a) (ha : c * G.inputLength / (J + 1) ≤ (a : ℝ)) :
    G.relativeDeficit ≥
      max (1 - ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1)) * G.prefixMeanReciprocal O J R M hM -
        (2 * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / (G.d * G.inputLength) +
          2 * ((w : ℝ) - 1) / G.inputLength +
          ((G.d : ℝ) * G.b - G.b + 1) / (2 * G.inputLength) +
          β / G.inputLength * (J + q +
            ((G.inputLength : ℝ) * ∑ i ∈ Ico R J, O.hopProfile G.inputLength i) /
              ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / w)) := by
  have hV : (∑ F ∈ univ \ O.subprefix J K, ∑ e ∈ F.val.edges,
      dist (G.x e : ℝ) (G.x (e + 1) : ℝ)) ≤
      (∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) * G.inputLength := by
    rw [O.sum_subprefix_compl_eq
      (fun F => ∑ e ∈ F.edges, dist (G.x e : ℝ) (G.x (e + 1) : ℝ))
      G.inputLength_pos hKJ]
    exact le_of_eq (mul_comm _ _)
  have hτ : ((∑ F ∈ coreNonleaves (O.selectedPrefix J) \ O.subprefix J R,
      F.val.hops.card : ℕ) : ℝ) ≤
      (G.inputLength : ℝ) * ∑ i ∈ Ico R J, O.hopProfile G.inputLength i := by
    have hsum : ((∑ F ∈ coreNonleaves (O.selectedPrefix J) \ O.subprefix J R,
        F.val.hops.card : ℕ) : ℝ) ≤
        ∑ F ∈ univ \ O.subprefix J R, (F.val.hops.card : ℝ) := by
      exact_mod_cast nonleaf_mass_le_total (O.selectedPrefix J) (O.subprefix J R)
    exact hsum.trans_eq (O.sum_subprefix_compl_eq (fun F => (F.hops.card : ℝ))
      G.inputLength_pos hRJ)
  simpa only [relativeDeficit, deficit, inputLength, prefixMeanReciprocal, Nat.cast_mul] using
    reciprocal_cover_paid_deficit (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
      G.exceptions (O.subprefix J R) (O.subprefix J K)
      (by rw [O.selectedPrefix_card]; exact min_le_left _ _) G.exceptions_card
      (O.subprefix_card_le J R) hRM (O.subprefix_card_le J K)
      G.work_walk G.full_coloring (G.prefix_outside_small O ha0 ha)
      G.x G.t G.hd G.hb hw G.append_strict G.append_lt G.raw_range G.raw_step
      G.C G.correct_nonempty G.record G.output G.capacity G.locally_determined G.correct
      (by simpa only [inputLength, Nat.cast_mul] using hV) hτ

/-- The original orbit-count prefix inequality is a direct relaxation. -/
theorem prefix_deficit {K R J M w a : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (ha0 : G.a0 ≤ a) (ha : c * G.inputLength / (J + 1) ≤ (a : ℝ)) :
    G.relativeDeficit ≥
      max (1 - ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4) ^ q) -
        (2 * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / (G.d * G.inputLength) +
          2 * ((w : ℝ) - 1) / G.inputLength +
          ((G.d : ℝ) * G.b - G.b + 1) / (2 * G.inputLength) +
          β / G.inputLength * (J + q +
            ((G.inputLength : ℝ) * ∑ i ∈ Ico R J, O.hopProfile G.inputLength i) /
              ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / w)) := by
  have h := G.prefix_reciprocal_deficit O hKJ hRJ hM hRM hw ha0 ha
  have hlo := (G.prefixMeanReciprocal_bounds O (J := J) hM hRM).1
  have hcredit := mul_le_mul_of_nonneg_left hlo
    (by positivity : 0 ≤ max (1 - ∑ i ∈ Ico K J,
      O.variationProfile G.x G.inputLength i) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)))
  have hfinal := (sub_le_sub_right hcredit _).trans h
  simpa only [div_mul_eq_div_mul_one_div] using hfinal

end AdmissibleGeometry
end
end SourceCovers

import SourceCovers

set_option autoImplicit false

/-!
# The frozen gap-area condition

The paid source-cover inequality `paid_deficit_of_gap_credit` accepts any
credit bounded by the frozen point area of the exact raw bank. Here that
point area itself is the credit. The dimension limit along a joint-profile
subsequence, the prefix limit and the removal of the width error are the
ones used for the reciprocal-cover bound, in the same order.
-/

namespace SourceCovers

open Classical Finset Filter LeanMachine LeanMachine.SourceBank Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators Topology
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- The frozen point area of the complete bank at the first output of a
column. The value zero is used only if the raw set is empty, which does not
happen at legal phases. -/
def phaseGapArea (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b ρ j : ℕ) : ℝ :=
  let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x (columnFirst t (d * b) j)
  if hS : S.Nonempty then
    GapErosion.pointArea (range S.card) (CyclicSelection.gap (d * d * b) S hS) (d * d * b)
  else 0

theorem phaseGapArea_eq (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b j : ℕ) :
    let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x (columnFirst t (d * b) j)
    phaseGapArea hc hM E x t d b ρ j =
      GapErosion.pointArea (range S.card) (CyclicSelection.gap (d * d * b) S
        ⟨_, exactSourceBank_raw_root hc hM hρ E x _⟩) (d * d * b) := by
  intro S
  exact dite_eq_left ⟨_, exactSourceBank_raw_root hc hM hρ E x _⟩

/-- Gaps of a nonempty set of residues sum to the circumference, so the point
area lies in `[0, 1/2]`. -/
theorem pointArea_gap_bounds {L : ℕ} (hL : 0 < L) {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) :
    0 ≤ GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L ∧
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L ≤ 1 / 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : ∑ i ∈ range S.card, (CyclicSelection.gap L S hS i : ℝ) = L := by
    exact_mod_cast CyclicSelection.sum_gap hS hSL
  have hsq : ∑ i ∈ range S.card, (CyclicSelection.gap L S hS i : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ range S.card, (CyclicSelection.gap L S hS i : ℝ) * L := by
        apply sum_le_sum
        intro i hi
        rw [pow_two]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact_mod_cast CyclicSelection.gap_le hS hSL (mem_range.mp hi)
      _ = (L : ℝ) ^ 2 := by rw [← sum_mul, hsum, pow_two]
  unfold GapErosion.pointArea
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    linarith

theorem phaseGapArea_bounds (hc : HasSpanColoring K 2) {M ρ d b j : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hj : j < d) (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b) :
    0 ≤ phaseGapArea hc hM E x t d b ρ j ∧ phaseGapArea hc hM E x t d b ρ j ≤ 1 / 2 := by
  have htime := hn _ ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2)
  have hSL : rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x (columnFirst t (d * b) j) ⊆
      range (d * d * b) := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    apply mem_range.mpr
    apply hx
    have hu' := shadowOrbit_le ((exactSourceBank_exact hc hM hρ E _).subset hu)
    unfold columnFirst at hu'
    omega
  rw [phaseGapArea_eq hc hM hρ E x t d b j]
  exact pointArea_gap_bounds (Nat.mul_pos (Nat.mul_pos hd hd) hb) _ hSL

/-- Mean frozen point area over a set of phases and all columns. -/
def meanGapArea (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ ρ ∈ A, ∑ j ∈ range d, phaseGapArea hc hM E x t d b ρ j) / (A.card * d)

theorem meanGapArea_bounds (hc : HasSpanColoring K 2) {M d b : ℕ}
    (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (A : Finset ℕ) (hA : A.Nonempty) (hAM : ∀ ρ ∈ A, ρ < M) :
    0 ≤ meanGapArea hc hM E x t d b A ∧ meanGapArea hc hM E x t d b A ≤ 1 / 2 := by
  have hpoint : ∀ ρ ∈ A, ∀ j ∈ range d,
      0 ≤ phaseGapArea hc hM E x t d b ρ j ∧ phaseGapArea hc hM E x t d b ρ j ≤ 1 / 2 :=
    fun ρ hρ j hj => phaseGapArea_bounds hc hM (hAM ρ hρ) E x t hd hb (mem_range.mp hj) hn hx
  have hden : (0 : ℝ) < A.card * d := by
    exact mul_pos (by exact_mod_cast card_pos.mpr hA) (by exact_mod_cast hd)
  constructor
  · exact div_nonneg (sum_nonneg fun ρ hρ => sum_nonneg fun j hj => (hpoint ρ hρ j hj).1)
      hden.le
  · apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ ∑ ρ ∈ A, ∑ j ∈ range d, (1 / 2 : ℝ) :=
        sum_le_sum fun ρ hρ => sum_le_sum fun j hj => (hpoint ρ hρ j hj).2
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

variable {Record : Type*} [Fintype Record]

/-- The finite paid deficit with the frozen point area as the credit. -/
theorem gap_area_paid_deficit (hc : HasSpanColoring K 2)
    {M d b w J q R N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    (C : Finset (Fin (d * d * b) → Bool)) (hC : C.Nonempty)
    (record : (Fin (d * d * b) → Bool) → ℕ → Record) (output : ℕ → Record → Bool)
    {β τ : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      meanGapArea hc hM E x t d b (admissiblePhases K P M) -
        (2 * bankCost M q * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((T - 1 : ℕ) : ℝ) / w)) := by
  have h := paid_deficit_of_gap_credit hc hM E P hK hE hP hR hwalk hcolor hsize
    x t hd hb hw ht (fun z hz => by have := hn z hz; omega) hx hstep C hC
    record output hcapacity hlocal hcorrect hτ
    (fun ρ j => phaseGapArea hc hM E x t d b ρ j)
    (fun ρ hρ j _ => (phaseGapArea_eq hc hM (admissiblePhase_lt hρ) E x t d b j).le)
  simpa only [meanGapArea] using h

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q) (O : SortedCore G.core)

/-- Mean frozen point area with the original first `J` families selected and
the original first `R` protected. -/
def prefixMeanGapArea (J R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  meanGapArea (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
    G.exceptions G.x G.t G.d G.b
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)

theorem prefixMeanGapArea_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ G.prefixMeanGapArea O J R M hM ∧ G.prefixMeanGapArea O J R M hM ≤ 1 / 2 := by
  have hA := (protected_phase_average (O.selectedPrefix J) (O.subprefix J R)
    (O.subprefix_card_le J R) hRM).1
  have hnonempty : (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).Nonempty :=
    card_pos.mp (lt_of_lt_of_le (Nat.sub_pos_of_lt hRM) hA)
  exact meanGapArea_bounds (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
    G.exceptions G.x G.t G.hd G.hb G.append_lt G.raw_range _ hnonempty
    (fun _ hρ => admissiblePhase_lt hρ)

/-- The finite prefix inequality, with the same paid error as the
reciprocal-cover form. -/
theorem prefix_gap_area_deficit {R J M w a : ℕ}
    (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (ha0 : G.a0 ≤ a) (ha : c * G.inputLength / (J + 1) ≤ (a : ℝ)) :
    G.relativeDeficit ≥ G.prefixMeanGapArea O J R M hM - G.prefixError O J R M w a := by
  have hτ := G.prefix_nonleaf_mass_le O hRJ
  have h := gap_area_paid_deficit (J := J) (w := w) (a := a)
      (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
      G.exceptions (O.subprefix J R)
      (by rw [O.selectedPrefix_card]; exact min_le_left _ _) G.exceptions_card
      (O.subprefix_card_le J R) hRM
      G.work_walk G.full_coloring (G.prefix_outside_small O ha0 ha)
      G.x G.t G.hd G.hb hw G.append_strict G.append_lt G.raw_range G.raw_step
      G.C G.correct_nonempty G.record G.output G.capacity G.locally_determined G.correct hτ
  simpa only [relativeDeficit, deficit, inputLength, prefixMeanGapArea, prefixError,
    Nat.cast_mul] using h

end AdmissibleGeometry

namespace NearFullSequence.JointProfile

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)

/-- Frozen point-area means along the joint-profile subsequence. -/
def prefixGapArea (J R M : ℕ) (hM : 2 ≤ M) (n : ℕ) : ℝ :=
  (S.geometry (P.subsequence n)).prefixMeanGapArea (S.order (P.subsequence n)) J R M hM

theorem prefixGapArea_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) (n : ℕ) :
    0 ≤ P.prefixGapArea J R M hM n ∧ P.prefixGapArea J R M hM n ≤ 1 / 2 :=
  (S.geometry (P.subsequence n)).prefixMeanGapArea_bounds (S.order (P.subsequence n)) hM hRM

theorem prefixGapArea_limsup_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ limsup (P.prefixGapArea J R M hM) atTop ∧
      limsup (P.prefixGapArea J R M hM) atTop ≤ 1 / 2 := by
  have h := fun n => P.prefixGapArea_bounds (J := J) hM hRM n
  have h1 : ∀ n, P.prefixGapArea J R M hM n ≤ 1 := fun n => (h n).2.trans (by norm_num)
  refine ⟨BoundedLimsup.limsup_nonneg (fun n => (h n).1) h1, ?_⟩
  exact limsup_le_of_le
    (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall fun n => (h n).1))
    (Eventually.of_forall fun n => (h n).2)

/-- The dimension upper limit of the frozen point area at a fixed prefix. -/
theorem prefix_gap_area_limit {R M J : ℕ}
    (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) {lam : ℝ} (hlam : 0 < lam) :
    limsup (P.prefixGapArea J R M hM) atTop ≤
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * (bankCost M q : ℝ) * c ^ 2 / (lam * (J + 1)) := by
  obtain ⟨w, a, F, hdata, hF⟩ := P.prefix_error_limit J R M hlam
  have hpoint : ∀ n, 1 * P.prefixGapArea J R M hM n ≤
      (S.geometry (P.subsequence n)).relativeDeficit + F n := by
    intro n
    obtain ⟨hw, ha0, ha, he⟩ := hdata n
    have hp := (S.geometry (P.subsequence n)).prefix_gap_area_deficit
      (S.order (P.subsequence n)) hRJ hM hRM hw ha0 ha
    change (S.geometry (P.subsequence n)).relativeDeficit ≥
      P.prefixGapArea J R M hM n -
        (S.geometry (P.subsequence n)).prefixError
          (S.order (P.subsequence n)) J R M (w n) (a n) at hp
    linarith
  have hbnd := fun n => P.prefixGapArea_bounds (J := J) hM hRM n
  have h := BoundedLimsup.mul_limsup_le_of_tendsto
    (fun n => (hbnd n).1) (fun n => (hbnd n).2.trans (by norm_num))
    (tendsto_const_nhds (x := (1 : ℝ))) hF (Eventually.of_forall hpoint)
  simpa only [one_mul] using h

/-- Dimension upper limit, followed by prefix upper limit, with fixed modulus. -/
def gapAreaLimit (R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  limsup (fun J => limsup (P.prefixGapArea J R M hM) atTop) atTop

theorem gapAreaLimit_bounds {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ P.gapAreaLimit R M hM ∧ P.gapAreaLimit R M hM ≤ 1 / 2 := by
  have h := fun J => P.prefixGapArea_limsup_bounds (J := J) hM hRM
  have h1 : ∀ J, limsup (P.prefixGapArea J R M hM) atTop ≤ 1 :=
    fun J => (h J).2.trans (by norm_num)
  refine ⟨BoundedLimsup.limsup_nonneg (fun J => (h J).1) h1, ?_⟩
  exact limsup_le_of_le
    (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall fun J => (h J).1))
    (Eventually.of_forall fun J => (h J).2)

/-- **Theorem G.** Along every joint profile of every near-full sequence, the
limiting mean frozen point area is at most the paid nonleaf tail. The cutoff
`R` and the modulus `M` are fixed, and the number of exceptions is arbitrary. -/
theorem necessary_gap_area {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    P.gapAreaLimit R M hM ≤ β * P.hopTail R / ((M - R : ℕ) : ℝ) := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < δ / 2 := by positivity
  let C : ℝ := β * N * (bankCost M q : ℝ) * c ^ 2
  have herror : Tendsto (fun J : ℕ => C / ((δ / 2) * (J + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (C / (δ / 2))).comp
        (tendsto_add_atTop_nat 1)
  have hcost := ((((P.finite_tails_tendsto R).1.const_mul β).div_const
    ((M - R : ℕ) : ℝ)).add_const (2 * (δ / 2))).add herror
  have hbnd := fun J => P.prefixGapArea_limsup_bounds (J := J) hM hRM
  have h := BoundedLimsup.mul_limsup_le_of_tendsto
    (fun J => (hbnd J).1) (fun J => (hbnd J).2.trans (by norm_num))
    (tendsto_const_nhds (x := (1 : ℝ))) hcost
    (eventually_atTop.2 ⟨R, fun J hJ => by
      simpa only [one_mul] using P.prefix_gap_area_limit hJ hM hRM hε⟩)
  simpa only [gapAreaLimit, one_mul, add_zero, show 2 * (δ / 2) = δ by ring] using h

/-- The specialization `M = 2R+2`. -/
theorem necessary_gap_area_default (R : ℕ) :
    P.gapAreaLimit R (2 * R + 2) (by omega) ≤ β * P.hopTail R / (R + 2 : ℝ) := by
  simpa only [show 2 * R + 2 - R = R + 2 by omega, Nat.cast_add, Nat.cast_ofNat] using
    P.necessary_gap_area (R := R) (M := 2 * R + 2) (by omega) (by omega)

end NearFullSequence.JointProfile

end
end SourceCovers

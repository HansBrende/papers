import SourceCovers.TerminalCoreCover
import SourceCovers.PaidSourceCover

set_option autoImplicit false

/-!
# Terminal core counts and reciprocal-cover credit

The actual fractional cover weights are retained through phase and column
averaging. Replacing them by the terminal-orbit count recovers the uniform
corollary without repeating the recovery or payment argument.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators ENNReal
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- The fractional cover weight of the complete bank at the first output
of a column. At legal phases and actual output times it is finite and at least one. -/
def phaseCoreCover (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b ρ j : ℕ) : ℝ :=
  (fractionalCoreCover (phaseSurvivors K M ρ) x
    (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
      (columnFirst t (d * b) j))).toReal

/-- Averaging reciprocals retains the column and phase variation in the
actual cover weights, rather than replacing every weight by its worst bound. -/
def meanReciprocalCover (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ ρ ∈ A, ∑ j ∈ range d, 1 / phaseCoreCover hc hM E x t d b ρ j) / (A.card * d)

theorem meanReciprocalCover_bounds (hc : HasSpanColoring K 2) {M d b : ℕ}
    (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (A : Finset ℕ) (hA : A.Nonempty) (hAM : ∀ ρ ∈ A, ρ < M) :
    1 / (2 * (M : ℝ) + 4) ^ E.card ≤ meanReciprocalCover hc hM E x t d b A ∧
      meanReciprocalCover hc hM E x t d b A ≤ 1 := by
  have hpoint : ∀ ρ ∈ A, ∀ j ∈ range d,
      1 / (2 * (M : ℝ) + 4) ^ E.card ≤ 1 / phaseCoreCover hc hM E x t d b ρ j ∧
        1 / phaseCoreCover hc hM E x t d b ρ j ≤ 1 := by
    intro ρ hρ j hj
    have htime := hn _ ((column_indices hd hb (mem_range.mp hj)).1.trans_lt
      (column_indices hd hb (mem_range.mp hj)).2)
    have hκ := (fractionalCoreCover_exactSourceBank_bounds hc hM (hAM ρ hρ) E x htime).2
    change 1 ≤ phaseCoreCover hc hM E x t d b ρ j ∧
      phaseCoreCover hc hM E x t d b ρ j ≤ ((2 * M + 4) ^ E.card : ℕ) at hκ
    have hu : phaseCoreCover hc hM E x t d b ρ j ≤ (2 * (M : ℝ) + 4) ^ E.card := by
      exact_mod_cast hκ.2
    exact ⟨one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hκ.1) hu,
      by simpa using one_div_le_one_div_of_le zero_lt_one hκ.1⟩
  have hden : (0 : ℝ) < A.card * d := by
    exact mul_pos (by exact_mod_cast card_pos.mpr hA) (by exact_mod_cast hd)
  constructor
  · apply (le_div_iff₀ hden).mpr
    calc
      _ = ∑ ρ ∈ A, ∑ j ∈ range d, 1 / (2 * (M : ℝ) + 4) ^ E.card := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum fun ρ hρ => sum_le_sum fun j hj => (hpoint ρ hρ j hj).1
  · apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ ∑ ρ ∈ A, ∑ j ∈ range d, (1 : ℝ) :=
        sum_le_sum fun ρ hρ => sum_le_sum fun j hj => (hpoint ρ hρ j hj).2
      _ = _ := by simp

/-- Exact complete-bank credit, with no cover-economy premise. -/
theorem phaseCoreCover_gap (hc : HasSpanColoring K 2) {M d b ρ r : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (D : Finset (CoreFamily K)) (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    {j : ℕ} (hj : j < d) :
    let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
      (columnFirst t (d * b) j)
    max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * phaseCoreCover hc hM E x t d b ρ j) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap (d * d * b) S
        ⟨_, exactSourceBank_raw_root hc hM hρ E x _⟩) (d * d * b) := by
  have htime := hn _ ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2)
  apply fractional_phase_gap hc D M ρ x (Nat.mul_pos (Nat.mul_pos hd hd) hb) hD
    ⟨_, exactSourceBank_raw_root hc hM hρ E x _⟩ _
    (fractionalCoreCover_exactSourceBank_bounds hc hM hρ E x htime).1
    (by simpa only [Nat.cast_mul] using hV)
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  apply mem_range.mpr
  apply hx
  have hu' := shadowOrbit_le ((exactSourceBank_exact hc hM hρ E _).subset hu)
  omega

variable {Record : Type*} [Fintype Record]

/-- Stronger finite deficit: retain the mean reciprocal of the actual complete-bank
fractional cover weights. The proof shares all paid recovery with Theorem C. -/
theorem reciprocal_cover_paid_deficit (hc : HasSpanColoring K 2)
    {M d b w J q R r N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P D : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hD : D.card ≤ r) (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    (C : Finset (Fin (d * d * b) → Bool)) (hC : C.Nonempty)
    (record : (Fin (d * d * b) → Bool) → ℕ → Record) (output : ℕ → Record → Bool)
    {β α τ : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1)) *
        meanReciprocalCover hc hM E x t d b (admissiblePhases K P M) -
        (2 * bankCost M q * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((T - 1 : ℕ) : ℝ) / w)) := by
  let c : ℝ := max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1))
  have hcredit : ∀ ρ (hρ : ρ ∈ admissiblePhases K P M), ∀ j < d,
      let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
        (columnFirst t (d * b) j)
      c * (1 / phaseCoreCover hc hM E x t d b ρ j) ≤
        GapErosion.pointArea (range S.card) (CyclicSelection.gap (d * d * b) S
          ⟨_, exactSourceBank_raw_root hc hM (admissiblePhase_lt hρ) E x _⟩)
          (d * d * b) := by
    intro ρ hρ j hj
    simpa only [c, div_mul_eq_div_mul_one_div] using
      phaseCoreCover_gap hc hM (admissiblePhase_lt hρ) E x t hd hb hn hx D hD hV hj
  have h := paid_deficit_of_gap_credit hc hM E P hK hE hP hR hwalk hcolor hsize
    x t hd hb hw ht (fun z hz => by have := hn z hz; omega) hx hstep C hC
    record output hcapacity hlocal hcorrect hτ
    (fun ρ j => c * (1 / phaseCoreCover hc hM E x t d b ρ j)) hcredit
  simpa only [← mul_sum, mul_div_assoc, c, meanReciprocalCover] using h

/-- Counting terminal core orbits is a direct relaxation of reciprocal-cover
credit, using only the exception budget already present in the paid theorem. -/
theorem orbit_count_paid_deficit (hc : HasSpanColoring K 2)
    {M d b w J q R r N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P D : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hD : D.card ≤ r) (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    (C : Finset (Fin (d * d * b) → Bool)) (hC : C.Nonempty)
    (record : (Fin (d * d * b) → Bool) → ℕ → Record) (output : ℕ → Record → Bool)
    {β α τ : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4) ^ q) -
        (2 * bankCost M q * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((T - 1 : ℕ) : ℝ) / w)) := by
  have h := reciprocal_cover_paid_deficit hc hM E P D hK hE hP hR hD
    hwalk hcolor hsize x t hd hb hw ht hn hx hstep C hC record output
    hcapacity hlocal hcorrect hV hτ
  have hA : (admissiblePhases K P M).Nonempty :=
    card_pos.mp (initialPayment_average_of_budgets K E P hK hE hP hR hτ).1
  have hmean := (meanReciprocalCover_bounds hc hM E x t hd hb hn
    (admissiblePhases K P M) hA (fun _ hρ => admissiblePhase_lt hρ)).1
  have hpow : 1 / (2 * (M : ℝ) + 4) ^ q ≤ 1 / (2 * (M : ℝ) + 4) ^ E.card :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith) hE)
  have hfinal := le_trans (sub_le_sub_right (mul_le_mul_of_nonneg_left
    (hpow.trans hmean) (by positivity : 0 ≤ max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1)))) _) h
  simpa only [div_mul_eq_div_mul_one_div] using hfinal

end
end SourceCovers

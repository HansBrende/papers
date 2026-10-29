import SourceCovers.SourceCoverCredit
import SourceCovers.PaidPhaseDeficit
import LeanMachine.PaidAveraging

/-! Complete source-cover credit and the full paid deficit. Each phase uses
its own exact bank and one common paid transcript for every output; only
the resulting signed inequalities are averaged. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Witnesses estimate the complete raw source set of this very phase. -/
abbrev PhaseCoverWitness (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b ρ j : ℕ) :=
  SourceCoverWitness (phaseSurvivors K M ρ) x (d * d * b)
    (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x (columnFirst t (d * b) j))

def phaseCoverCredit {hc : HasSpanColoring K 2} {M : ℕ} {hM : 2 ≤ M}
    {E : Finset (ActualFamily xs T)} {x t : ℕ → ℕ} {d b : ℕ}
    (F : ∀ ρ j, Set (PhaseCoverWitness hc hM E x t d b ρ j))
    (α : ℝ) (r ρ j : ℕ) : ℝ := sourceCoverCredit (F ρ j) α r

/-- Equal weighting of legal phases and all output columns. -/
def meanCoverCredit {hc : HasSpanColoring K 2} {M : ℕ} {hM : 2 ≤ M}
    {E : Finset (ActualFamily xs T)} {x t : ℕ → ℕ} {d b : ℕ}
    (A : Finset ℕ) (F : ∀ ρ j, Set (PhaseCoverWitness hc hM E x t d b ρ j))
    (α : ℝ) (r : ℕ) : ℝ :=
  (∑ ρ ∈ A, ∑ j ∈ range d, phaseCoverCredit F α r ρ j) / (A.card * d)

theorem phaseCoverCredit_bounds (hc : HasSpanColoring K 2) {M d b ρ r : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b)
    (hn : ∀ z < d * d * b, t z ≤ T - 1)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (D : Finset (CoreFamily K)) (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    (F : ∀ ρ j, Set (PhaseCoverWitness hc hM E x t d b ρ j))
    {j : ℕ} (hj : j < d) :
    0 ≤ phaseCoverCredit F α r ρ j ∧
      phaseCoverCredit F α r ρ j ≤
        GapErosion.pointArea
          (range (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
            (columnFirst t (d * b) j)).card)
          (CyclicSelection.gap (d * d * b) _
            ⟨_, exactSourceBank_raw_root hc hM hρ E x (columnFirst t (d * b) j)⟩)
          (d * d * b) ∧
      GapErosion.pointArea
          (range (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
            (columnFirst t (d * b) j)).card)
          (CyclicSelection.gap (d * d * b) _
            ⟨_, exactSourceBank_raw_root hc hM hρ E x (columnFirst t (d * b) j)⟩)
          (d * d * b) ≤ 1 / 2 := by
  apply sourceCoverCredit_bounds hc (phaseSurvivors K M ρ) univ D (subset_univ _) x
    (Nat.mul_pos (Nat.mul_pos hd hd) hb) hD
    ⟨_, exactSourceBank_raw_root hc hM hρ E x _⟩ _
    (by simpa only [Nat.cast_mul] using hV) (F ρ j)
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  apply mem_range.mpr
  apply hx
  have hu' := (exactSourceBank_exact hc hM hρ E _).subset hu
  exact (shadowOrbit_le hu').trans (hn _
    ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2))

variable {Record : Type*} [Fintype Record]

/-- Any lower bounds on the actual raw gaps can supply the geometric credit.
The complete paid inequalities are averaged over the same legal phases. -/
theorem paid_deficit_of_gap_credit (hc : HasSpanColoring K 2)
    {M d b w J q R N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z ≤ T - 1)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    (C : Finset (Fin (d * d * b) → Bool)) (hC : C.Nonempty)
    (record : (Fin (d * d * b) → Bool) → ℕ → Record) (output : ℕ → Record → Bool)
    {β τ : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ)
    (Hcredit : ℕ → ℕ → ℝ)
    (hcredit : ∀ ρ (hρ : ρ ∈ admissiblePhases K P M), ∀ j < d,
      let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
        (columnFirst t (d * b) j)
      Hcredit ρ j ≤ GapErosion.pointArea (range S.card)
        (CyclicSelection.gap (d * d * b) S
          ⟨x (columnFirst t (d * b) j),
            exactSourceBank_raw_root hc hM (admissiblePhase_lt hρ) E x _⟩)
        (d * d * b)) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      (∑ ρ ∈ admissiblePhases K P M, ∑ j ∈ range d, Hcredit ρ j) /
        ((admissiblePhases K P M).card * d) -
        (2 * bankCost M q * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((T - 1 : ℕ) : ℝ) / w)) := by
  let A := admissiblePhases K P M
  let V : ℝ := bankCost M q * ((T - 1 : ℕ) : ℝ)
  let c : ℝ := 2 * V / d + 2 * ((w : ℝ) - 1) + ((d : ℝ) * b - b + 1) / 2 +
    β * ((1 + (N : ℝ) * a) * V / w)
  have hpayment := initialPayment_average_of_budgets K E P hK hE hP hR hτ
  have hA : A.Nonempty := card_pos.mp hpayment.1
  have hpoint : ∀ ρ ∈ A,
      ((d : ℝ) * b * ∑ j ∈ range d, Hcredit ρ j) - c -
        β * (initialPayment K E M ρ).card ≤
      (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 := by
    intro ρ hρ
    have h := phase_paid_deficit hc hM (admissiblePhase_lt hρ) E hwalk hcolor hsize
      hd hb hw hx ht hn hC hcapacity hlocal hcorrect (Hcredit ρ) (hcredit ρ hρ) hE hstep
    convert h using 1
    dsimp [c, V]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  have havg := PaidAveraging.mean_credit_sub_cost_le hA (recordCapacity_nonneg hcapacity)
    hpoint hpayment.2
  have hL : (0 : ℝ) < d * d * b := by positivity
  have hnorm := div_le_div_of_nonneg_right havg hL.le
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hA).ne'
  convert hnorm using 1
  dsimp [c, V]
  rw [← mul_sum]
  field_simp
  ring

/-- Theorem C. All parent, recovery, payment, and cover bounds are derived
from the actual computation and its complete selected families. Runtime need
not be linear; the finite error records the given horizon `T - 1`. -/
theorem complete_cover_paid_deficit (hc : HasSpanColoring K 2)
    {M d b w J q R r N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P D : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hD : D.card ≤ r) (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z ≤ T - 1)
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
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ)
    (F : ∀ ρ j, Set (PhaseCoverWitness hc hM E x t d b ρ j)) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      meanCoverCredit (admissiblePhases K P M) F α r -
        (2 * bankCost M q * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((T - 1 : ℕ) : ℝ) / w)) := by
  exact paid_deficit_of_gap_credit hc hM E P hK hE hP hR hwalk hcolor hsize
    x t hd hb hw ht hn hx hstep C hC record output hcapacity hlocal hcorrect hτ
    (phaseCoverCredit F α r) (fun ρ hρ j hj =>
      (phaseCoverCredit_bounds hc hM (admissiblePhase_lt hρ) E x t hd hb hn hx
        D hD hV F hj).2.1)

end
end SourceCovers

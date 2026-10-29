import SourceCovers.CyclicFreezing
import Transpose.Tape.CEHint

/-!
# From actual paid records to a transpose deficit

The transcript contains exactly the geometry-fixed paid records. Recovery
uses every supplied causal dependency and the root's direct input read.
The grid shift and its cost are obtained from the residual charging theorem.
-/

namespace SourceCovers

open Classical Finset LeanMachine Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

noncomputable section

/-- One common transcript, indexed by the distinct paid times. -/
def paidRecordTuple {Input R : Type*} (C : Finset Input)
    (record : Input → ℕ → R) (Γ : Finset ℕ) : C → Γ → R :=
  fun a u => record a.val u.val

/-- A real upper bound on a finite record's bit capacity is nonnegative. -/
theorem recordCapacity_nonneg {R : Type*} [Fintype R] {β : ℝ}
    (hR : Real.log (Fintype.card R : ℝ) / Real.log 2 ≤ β) : 0 ≤ β :=
  (div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by norm_num))).trans hR

variable {ι R : Type*} [Fintype ι] {d b n w θ : ℕ}
    {C : Finset (Fin (d * d * b) → Bool)}
    {record : (Fin (d * d * b) → Bool) → ℕ → R}
    {output : ℕ → R → Bool} {parents selected : ℕ → Finset ℕ}
    {Γ₀ : Finset ℕ} {Y : ι → ℕ → ℕ} {x t : ℕ → ℕ}

/-- Local causal recovery and actual output correctness give the functional
bank premise with the same paid transcript at every output coordinate. -/
theorem paid_transposeBankRecovers
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hx : ∀ s ≤ n, x s < d * d * b)
    (hread : ∀ s ≤ n, x s ∈ residualBankValues Y s)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun s => {x s})
      n (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ a ∈ C, ∀ z : Fin (d * d * b),
      output (tpos d b z.val) (record a (t (tpos d b z.val))) = a z) :
    TransposeBankRecovers C
      (paidRecordTuple C record
        (residualPayment (residualParents parents selected) n Γ₀ Y w θ)) Y t w θ := by
  intro z a a' hab hraw
  have hr := hn _ (tpos_lt z.isLt)
  have heq : record a.val (t (tpos d b z.val)) =
      record a'.val (t (tpos d b z.val)) := by
    refine paid_residual_source_recovery (w := w) (θ := θ)
      hearlier hselected hx hread hlocal a.property a'.property ?_ hr ?_
    · intro u hu
      exact congrFun hab ⟨u, hu⟩
    · intro q hq
      have h : a.val ⟨q, hq.1⟩ = a'.val ⟨q, hq.1⟩ := hraw hq
      simpa only [zbit, dite_eq_left hq.1] using h
  exact (hcorrect a.val a.property z).symm.trans
    ((congrArg (output (tpos d b z.val)) heq).trans (hcorrect a'.val a'.property z))

/-- An actual residual shift attains the full paid cost and the corresponding
one-phase deficit. The record capacity is real-valued. -/
theorem exists_paidBank_deficit [Nonempty ι] [Fintype R]
    {β H : ℝ} (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hY : ∀ i s, s ≤ n → Y i s < d * d * b)
    (hC : C.Nonempty)
    (hR : Real.log (Fintype.card R : ℝ) / Real.log 2 ≤ β)
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hread : ∀ s ≤ n, x s ∈ residualBankValues Y s)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun s => {x s})
      n (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ a ∈ C, ∀ z : Fin (d * d * b),
      output (tpos d b z.val) (record a (t (tpos d b z.val))) = a z)
    (hH : ∀ e < n,
      ((ResidualGeometry.live (residualParents parents selected) n Γ₀ e).card : ℝ) ≤ H) :
    ∃ θ < w,
      ((residualPayment (residualParents parents selected) n Γ₀ Y w θ).card : ℝ) ≤
        Γ₀.card + (H * ∑ i,
          MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / w ∧
      (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
        (d : ℝ) * b * (∑ j ∈ range d, frozenArea Y t d b j) -
          2 * (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / d -
          2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
          β * (Γ₀.card + (H * ∑ i,
            MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / w) := by
  obtain ⟨θ, hθ, hpay⟩ := exists_residualPayment_le Y hw
    (residualParents_earlier hearlier) hH
  refine ⟨θ, hθ, hpay, ?_⟩
  have hx : ∀ s ≤ n, x s < d * d * b := by
    intro s hs
    obtain ⟨i, _, hi⟩ := mem_image.mp (hread s hs)
    exact hi ▸ hY i s hs
  have hbank := paid_transposeBankRecovers (w := w) (θ := θ)
    hn hearlier hselected hx hread hlocal hcorrect
  have hdef := cyclic_freezing_genie _ β hd hb hw ht hn hY hC hR hbank
  simp only [Fintype.card_coe] at hdef
  exact (sub_le_sub_left
    (mul_le_mul_of_nonneg_left hpay (recordCapacity_nonneg hR)) _).trans hdef

end
end SourceCovers

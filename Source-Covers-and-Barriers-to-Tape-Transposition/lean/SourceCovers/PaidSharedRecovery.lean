import SourceCovers.PaidBankRecovery
import LeanMachine.ShiftedGridUnion

set_option autoImplicit false

/-! A common raw revelation replaces sources after choosing the full-bank
residual shift. Recovery and motion may use different banks. -/

namespace SourceCovers

open Classical Finset LeanMachine TransposeFollowup Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
    {d b w θ : ℕ} {C : Finset (Fin (d * d * b) → Bool)} {Z : C → H}
    {Y : ι → ℕ → ℕ} {D : κ → ℕ → ℕ} {t : ℕ → ℕ}

/-- One fixed raw union works for every actual output root, on the same
correctness set and with the same original transcript. -/
theorem TransposeBankRecovers.reveal_shared (hbank : TransposeBankRecovers C Z Y t w θ)
    (S : Finset ℕ)
    (hcover : ∀ z : Fin (d * d * b),
      residualBankValues Y (t (tpos d b z.val)) ⊆
        residualBankValues D (t (tpos d b z.val)) ∪ S) :
    TransposeBankRecovers C
      (fun a => (Z a, bitView (ShiftedGrid.blockUnion (d * d * b) w θ S) a.val)) D t w θ := by
  intro z a a' hab hraw
  apply hbank z a a' (congrArg Prod.fst hab)
  intro q hq
  obtain ⟨_, i, hi⟩ := hq
  rcases mem_union.mp (hcover z (mem_image_of_mem _ (mem_univ i))) with hD | hS
  · obtain ⟨j, _, hj⟩ := mem_image.mp hD
    exact hraw ⟨q.isLt, j, hj ▸ hi⟩
  · exact (bitView_eq_iff _ _ _).mp (congrArg Prod.snd hab) q
      (ShiftedGrid.mem_blockUnion.mpr ⟨_, hS, hi⟩)

variable {Record : Type*} [Fintype Record] [Nonempty κ]
    {n : ℕ} {record : (Fin (d * d * b) → Bool) → ℕ → Record}
    {output : ℕ → Record → Bool} {parents selected : ℕ → Finset ℕ}
    {Γ₀ : Finset ℕ} {x : ℕ → ℕ} {β load : ℝ}

/-- The stronger paid bound keeps the actual union size and two separate
variation bills. Only the full bank selects the residual shift. -/
theorem exists_paidBank_shared_deficit
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hY : ∀ i s, s ≤ n → Y i s < d * d * b)
    (hD : ∀ i s, s ≤ n → D i s < d * d * b)
    (hC : C.Nonempty)
    (hR : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hread : ∀ s ≤ n, x s ∈ residualBankValues Y s)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun s => {x s})
      n (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ a ∈ C, ∀ z : Fin (d * d * b),
      output (tpos d b z.val) (record a (t (tpos d b z.val))) = a z)
    (hload : ∀ e < n,
      ((ResidualGeometry.live (residualParents parents selected) n Γ₀ e).card : ℝ) ≤ load)
    (S : Finset ℕ)
    (hcover : ∀ z : Fin (d * d * b),
      residualBankValues Y (t (tpos d b z.val)) ⊆
        residualBankValues D (t (tpos d b z.val)) ∪ S) :
    ∃ θ < w,
      ((residualPayment (residualParents parents selected) n Γ₀ Y w θ).card : ℝ) ≤
        Γ₀.card + load * (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / w ∧
      (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
        (d : ℝ) * b * (∑ j ∈ range d, frozenArea D t d b j) -
          2 * (∑ i, MonotonePatches.variation (fun s => (D i s : ℝ)) n) / d -
          2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
          β * (Γ₀.card + load *
            (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / w) -
          (ShiftedGrid.blockUnion (d * d * b) w θ S).card := by
  obtain ⟨θ, hθ, hpay⟩ := exists_residualPayment_le Y hw
    (residualParents_earlier hearlier) hload
  refine ⟨θ, hθ, hpay, ?_⟩
  have hx : ∀ s ≤ n, x s < d * d * b := by
    intro s hs
    obtain ⟨i, _, hi⟩ := mem_image.mp (hread s hs)
    exact hi ▸ hY i s hs
  have hbank := paid_transposeBankRecovers (w := w) (θ := θ)
    hn hearlier hselected hx hread hlocal hcorrect
  have hdef := cyclic_freezing_genie_raw _ β hd hb hw ht hn hD hC hR
    (ShiftedGrid.blockUnion (d * d * b) w θ S) (hbank.reveal_shared S hcover)
  simp only [Fintype.card_coe] at hdef
  have hp := mul_le_mul_of_nonneg_left hpay (recordCapacity_nonneg hR)
  linarith

end
end SourceCovers

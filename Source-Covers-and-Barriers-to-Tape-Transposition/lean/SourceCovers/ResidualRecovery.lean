import LeanMachine.CausalRecovery
import SourceCovers.ResidualPayment

/-!
# Paid residual-source recovery

All dependencies belong to the supplied causal parent relation. Selected
edges preserve bank value sets; every other edge is treated as residual.
One geometry-fixed payment works simultaneously at all output roots.
-/

namespace SourceCovers

open Classical Finset LeanMachine

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Values of a finite raw bank at a time, identifying coincident coordinates. -/
def residualBankValues (Y : ι → ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  univ.image (fun i => Y i t)

/-- The endpoint-clipped union of shifted blocks at a root. -/
def residualBlocks (Y : ι → ℕ → ℕ) (L w θ t : ℕ) : Set ℕ :=
  {z | z < L ∧ ∃ i, ShiftedGrid.label w θ z = ShiftedGrid.label w θ (Y i t)}

theorem residualBlocks_mono_of_values {Y : ι → ℕ → ℕ} {L w θ u v : ℕ}
    (h : residualBankValues Y u ⊆ residualBankValues Y v) :
    residualBlocks Y L w θ u ⊆ residualBlocks Y L w θ v := by
  rintro z ⟨hz, i, hi⟩
  obtain ⟨j, _, hj⟩ := mem_image.mp (h (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
  exact ⟨hz, j, hj ▸ hi⟩

omit [Fintype ι] in
theorem residualBlocks_mono_of_labels {Y : ι → ℕ → ℕ} {L w θ u v : ℕ}
    (h : ∀ i, ShiftedGrid.label w θ (Y i u) = ShiftedGrid.label w θ (Y i v)) :
    residualBlocks Y L w θ u ⊆ residualBlocks Y L w θ v := by
  rintro z ⟨hz, i, hi⟩
  exact ⟨hz, i, hi.trans (h i)⟩

theorem read_mem_residualBlocks {Y : ι → ℕ → ℕ} {x : ℕ → ℕ}
    {L w θ t : ℕ} (hx : x t < L) (hread : x t ∈ residualBankValues Y t) :
    x t ∈ residualBlocks Y L w θ t := by
  obtain ⟨i, _, hi⟩ := mem_image.mp hread
  exact ⟨hx, i, congrArg (ShiftedGrid.label w θ) hi.symm⟩

/-- The complement of the selected edges in the full parent relation. -/
def residualParents (parents selected : ℕ → Finset ℕ) (v : ℕ) : Finset ℕ :=
  parents v \ selected v

omit [Fintype ι] in
theorem residualParents_earlier {parents selected : ℕ → Finset ℕ} {n : ℕ}
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v) :
    ∀ v ≤ n, ∀ u ∈ residualParents parents selected v, u < v :=
  fun v hv u hu => hearlier v hv u (mem_sdiff.mp hu).1

variable {parents selected : ℕ → Finset ℕ} {n L w θ : ℕ} {Γ₀ : Finset ℕ}
    {Y : ι → ℕ → ℕ} {x : ℕ → ℕ}

/-- Every surviving edge preserves containment of complete block unions.
The upper endpoint may be paid; only lower-endpoint payment blocks an edge. -/
theorem residualBlocks_closed
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    {v u : ℕ} (hv : v ≤ n) (hu : u ∈ parents v)
    (hpaid : u ∉ residualPayment (residualParents parents selected) n Γ₀ Y w θ) :
    residualBlocks Y L w θ u ⊆ residualBlocks Y L w θ v := by
  have hΓ : u ∉ Γ₀ := fun h => hpaid (mem_union_left _ h)
  by_cases hs : u ∈ selected v
  · exact residualBlocks_mono_of_values (hselected v hv u hu hs hΓ)
  · have hR : u ∈ residualParents parents selected v := mem_sdiff.mpr ⟨hu, hs⟩
    have hU : u ∈ ResidualGeometry.U (residualParents parents selected) n Γ₀ :=
      ResidualGeometry.mem_U.mpr ⟨hΓ, v, hv, hR⟩
    have hcut : u ∉ residualCut (residualParents parents selected) n Γ₀ Y w θ :=
      fun h => hpaid (mem_union_right _ h)
    have hlu := ResidualGeometry.le_last (residualParents parents selected) n u
    apply residualBlocks_mono_of_labels
    exact fun i => GridPayment.labels_eq_of_not_mem_cut hU hcut
      ((IntervalOscillation.mem_times hlu).mpr ⟨le_rfl, hlu⟩)
      ((IntervalOscillation.mem_times hlu).mpr
        ⟨(hearlier v hv u hu).le, ResidualGeometry.edge_le_last hv hR⟩) i

/-- The complete surviving cone lies in the root's block union. This includes
the root's direct read and unpaid parents even when the root was revealed. -/
theorem paid_residual_sourceCone_subset
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hx : ∀ t ≤ n, x t < L) (hread : ∀ t ≤ n, x t ∈ residualBankValues Y t)
    {root : ℕ} (hr : root ≤ n) :
    CausalRecovery.sourceCone parents (fun t => {x t})
      (residualPayment (residualParents parents selected) n Γ₀ Y w θ) root ⊆
      residualBlocks Y L w θ root := by
  apply CausalRecovery.sourceCone_subset _ hearlier _ _ hr
  · intro t ht z hz
    have hz' : z = x t := hz
    subst z
    exact read_mem_residualBlocks (hx t ht) (hread t ht)
  · intro v hv u hu hpaid
    exact residualBlocks_closed hearlier hselected hv hu hpaid

variable {Input Raw Value : Type*} {C : Set Input}
    {raw : Input → ℕ → Raw} {record : Input → ℕ → Value}

/-- Functional recovery on an arbitrary correctness set. The paid transcript
is fixed before choosing the root; no independence or linearity is assumed. -/
theorem paid_residual_source_recovery
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hx : ∀ t ≤ n, x t < L) (hread : ∀ t ≤ n, x t ∈ residualBankValues Y t)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun t => {x t}) n C raw record)
    {a b : Input} (ha : a ∈ C) (hb : b ∈ C)
    (hpaid : Set.EqOn (record a) (record b)
      (residualPayment (residualParents parents selected) n Γ₀ Y w θ))
    {root : ℕ} (hr : root ≤ n)
    (hraw : Set.EqOn (raw a) (raw b) (residualBlocks Y L w θ root)) :
    record a root = record b root :=
  CausalRecovery.record_eq_of_sourceCone hearlier hlocal ha hb hpaid root hr
    (hraw.mono (paid_residual_sourceCone_subset hearlier hselected hx hread hr))

/-- An actual decoder of the root record from the common paid transcript and
its raw block union. The nonempty record alphabet only fills unused observations. -/
theorem paid_residual_decoder [Nonempty Value]
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hx : ∀ t ≤ n, x t < L) (hread : ∀ t ≤ n, x t ∈ residualBankValues Y t)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun t => {x t}) n C raw record)
    {root : ℕ} (hr : root ≤ n) :
    let Γ : Set ℕ := residualPayment (residualParents parents selected) n Γ₀ Y w θ
    let S := residualBlocks Y L w θ root
    ∃ decode : ((Γ → Value) × (S → Raw)) → Value,
      ∀ a ∈ C, decode (CausalRecovery.observation record raw Γ S a) = record a root := by
  apply CausalRecovery.exists_decoder
  intro a ha b hb hpaid hraw
  exact paid_residual_source_recovery hearlier hselected hx hread hlocal ha hb hpaid hr hraw

/-- Lemma 2.8 in one statement: actual paid lowers, the strengthened cost
chain, and complete recovery at every root using the same payment per shift.
Here `n = T - 1`; the parent relation includes every state and work dependency. -/
theorem paid_residual_recovery [Nonempty Value]
    (hearlier : ∀ v ≤ n, ∀ u ∈ parents v, u < v)
    (hselected : ∀ v ≤ n, ∀ u ∈ parents v, u ∈ selected v → u ∉ Γ₀ →
      residualBankValues Y u ⊆ residualBankValues Y v)
    (hx : ∀ t ≤ n, x t < L) (hread : ∀ t ≤ n, x t ∈ residualBankValues Y t)
    (hlocal : CausalRecovery.LocallyDetermined parents (fun t => {x t}) n C raw record)
    {H : ℝ} (hw : 0 < w)
    (hH : ∀ e < n,
      ((ResidualGeometry.live (residualParents parents selected) n Γ₀ e).card : ℝ) ≤ H) :
    let R := residualParents parents selected
    let cap := ∑ u ∈ ResidualGeometry.U R n Γ₀, ∑ i,
      (min w (IntervalOscillation.oscillation (Y i) u (ResidualGeometry.last R n u)) : ℝ)
    let profile := ∑ e ∈ range n, ((ResidualGeometry.live R n Γ₀ e).card : ℝ) *
      ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ)
    ((∑ θ ∈ range w, ((residualCut R n Γ₀ Y w θ).card : ℝ)) / w ≤ cap / w ∧
      cap / w ≤ residualOscillation R n Γ₀ Y / w ∧
      residualOscillation R n Γ₀ Y / w ≤ profile / w ∧
      profile / w ≤ (H * ∑ i, MonotonePatches.variation (fun t => (Y i t : ℝ)) n) / w) ∧
    (∀ θ u, u ∈ residualCut R n Γ₀ Y w θ → u ∉ Γ₀ ∧ ∃ v ≤ n, u ∈ R v) ∧
    (∀ θ root, root ≤ n →
      CausalRecovery.sourceCone parents (fun t => {x t})
        (residualPayment R n Γ₀ Y w θ) root ⊆ residualBlocks Y L w θ root ∧
      ∃ decode : ((↥(residualPayment R n Γ₀ Y w θ) → Value) ×
          (↥(residualBlocks Y L w θ root) → Raw)) → Value,
        ∀ a ∈ C, decode (CausalRecovery.observation record raw
          (residualPayment R n Γ₀ Y w θ) (residualBlocks Y L w θ root) a) = record a root) := by
  refine ⟨residual_payment_bounds Y hw (residualParents_earlier hearlier) hH,
    fun _ _ hu => residualCut_actual hu, ?_⟩
  intro θ root hr
  exact ⟨paid_residual_sourceCone_subset hearlier hselected hx hread hr,
    paid_residual_decoder hearlier hselected hx hread hlocal hr⟩

end
end SourceCovers

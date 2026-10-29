import LeanMachine.IntervalOscillation

/-! Actual residual lowers, their last successors, and their live-boundary profile.
The horizon `n` is the last time, so the vertices are `0, ..., n`. -/

namespace SourceCovers.ResidualGeometry

open Classical Finset LeanMachine
open scoped BigOperators

/-- Distinct unpaid lower endpoints of actual residual edges. -/
def U (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ) : Finset ℕ :=
  (range (n + 1)).biUnion (fun v => R v \ Γ₀)

def successors (R : ℕ → Finset ℕ) (n u : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun v => u ∈ R v)

/-- With no residual successor, the lifetime ends at its starting time. -/
def last (R : ℕ → Finset ℕ) (n u : ℕ) : ℕ :=
  (insert u (successors R n u)).sup id

theorem mem_U {R : ℕ → Finset ℕ} {n u : ℕ} {Γ₀ : Finset ℕ} :
    u ∈ U R n Γ₀ ↔ u ∉ Γ₀ ∧ ∃ v ≤ n, u ∈ R v := by
  simp only [U, mem_biUnion, mem_range, mem_sdiff]
  constructor
  · rintro ⟨v, hv, hu, hΓ⟩
    exact ⟨hΓ, v, by omega, hu⟩
  · rintro ⟨hΓ, v, hv, hu⟩
    exact ⟨v, by omega, hu, hΓ⟩

theorem mem_successors {R : ℕ → Finset ℕ} {n u v : ℕ} :
    v ∈ successors R n u ↔ v ≤ n ∧ u ∈ R v := by
  simp only [successors, mem_filter, mem_range, Nat.lt_succ_iff]

theorem U_subset_range {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v) : U R n Γ₀ ⊆ range (n + 1) := by
  intro u hu
  obtain ⟨_, v, hv, huv⟩ := mem_U.mp hu
  exact mem_range.mpr (by have := hR v hv u huv; omega)

theorem le_last (R : ℕ → Finset ℕ) (n u : ℕ) : u ≤ last R n u := by
  exact le_sup (f := id) (mem_insert_self u _)

theorem last_le {R : ℕ → Finset ℕ} {n u : ℕ} (hu : u ≤ n) : last R n u ≤ n := by
  apply Finset.sup_le
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact hu
  · exact (mem_successors.mp hv).1

theorem last_le_of_mem_U {R : ℕ → Finset ℕ} {n u : ℕ} {Γ₀ : Finset ℕ}
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v) (hu : u ∈ U R n Γ₀) :
    last R n u ≤ n :=
  last_le (Nat.lt_succ_iff.mp (mem_range.mp (U_subset_range hR hu)))

theorem edge_le_last {R : ℕ → Finset ℕ} {n u v : ℕ} (hv : v ≤ n) (huv : u ∈ R v) :
    v ≤ last R n u := by
  exact le_sup (f := id) (mem_insert_of_mem (mem_successors.mpr ⟨hv, huv⟩))

/-- A straddled lifetime is exactly an unpaid residual lower already born and
still needed by an actual later successor. Causality is unnecessary here. -/
theorem active_iff {R : ℕ → Finset ℕ} {n u e : ℕ} {Γ₀ : Finset ℕ} :
    (u ∈ U R n Γ₀ ∧ u ≤ e ∧ e < last R n u) ↔
      u ∉ Γ₀ ∧ u ≤ e ∧ ∃ v ≤ n, u ∈ R v ∧ e < v := by
  constructor
  · rintro ⟨hu, hue, hel⟩
    obtain ⟨v, hv, hev⟩ := Finset.lt_sup_iff.mp hel
    simp only [id_eq] at hev
    rcases mem_insert.mp hv with rfl | hv
    · exact False.elim (by omega)
    · have hv' := mem_successors.mp hv
      exact ⟨(mem_U.mp hu).1, hue, v, hv'.1, hv'.2, hev⟩
  · rintro ⟨hΓ, hue, v, hv, huv, hev⟩
    exact ⟨mem_U.mpr ⟨hΓ, v, hv, huv⟩, hue, hev.trans_le (edge_le_last hv huv)⟩

def live (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ) (e : ℕ) : Finset ℕ :=
  (U R n Γ₀).filter (fun u => u ≤ e ∧ e < last R n u)

theorem mem_live {R : ℕ → Finset ℕ} {n u e : ℕ} {Γ₀ : Finset ℕ} :
    u ∈ live R n Γ₀ e ↔ u ∉ Γ₀ ∧ u ≤ e ∧ ∃ v ≤ n, u ∈ R v ∧ e < v := by
  rw [live, mem_filter, active_iff]

theorem multiplicity_eq_live_card (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ) (e : ℕ) :
    IntervalOscillation.multiplicity (U R n Γ₀) id (last R n) e = (live R n Γ₀ e).card := rfl

theorem inactive_last_eq {R : ℕ → Finset ℕ} {n u : ℕ} {Γ₀ : Finset ℕ}
    (hΓ : u ∉ Γ₀) (hu : u ∉ U R n Γ₀) : last R n u = u := by
  apply le_antisymm ?_ (le_last R n u)
  apply Finset.sup_le
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact le_rfl
  · have hv' := mem_successors.mp hv
    exact False.elim (hu (mem_U.mpr ⟨hΓ, v, hv'.1, hv'.2⟩))

theorem inactive_oscillation_eq_zero {R : ℕ → Finset ℕ} {n u : ℕ} {Γ₀ : Finset ℕ}
    (hΓ : u ∉ Γ₀) (hu : u ∉ U R n Γ₀) (Y : ℕ → ℕ) :
    IntervalOscillation.oscillation Y u (last R n u) = 0 := by
  rw [inactive_last_eq hΓ hu]
  simp [IntervalOscillation.oscillation, IntervalOscillation.lower,
    IntervalOscillation.upper, IntervalOscillation.times]

/-- Charging every unpaid vertex gives exactly the same oscillation cost as
charging only actual residual lowers. -/
theorem sum_oscillation_eq {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v) (Y : ℕ → ℕ) :
    (∑ u ∈ range (n + 1) \ Γ₀, IntervalOscillation.oscillation Y u (last R n u)) =
      ∑ u ∈ U R n Γ₀, IntervalOscillation.oscillation Y u (last R n u) := by
  symm
  apply sum_subset
  · intro u hu
    exact mem_sdiff.mpr ⟨U_subset_range hR hu, (mem_U.mp hu).1⟩
  · intro u hu hU
    exact inactive_oscillation_eq_zero (mem_sdiff.mp hu).2 hU Y

end SourceCovers.ResidualGeometry

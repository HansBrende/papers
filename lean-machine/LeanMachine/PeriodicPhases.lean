import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Periodic cuts of integer chains and protected finite phase payments. -/

namespace LeanMachine.PeriodicPhases

open Classical Finset

/-- A unit-step chain avoiding one residue lies in a window shorter than a period. -/
theorem unit_chain_window {l : List ℕ} {M ρ : ℕ} (hρ : ρ < M)
    (hc : l.IsChain (fun a b => a ≤ b + 1 ∧ b ≤ a + 1))
    (ha : ∀ a ∈ l, a % M ≠ ρ) :
    ∃ m c, m ≤ c ∧ c < m + M ∧ l.toFinset ⊆ Ico m c := by
  classical
  rcases l with _ | ⟨x, l⟩
  · exact ⟨0, 0, le_rfl, by omega, by simp⟩
  obtain ⟨m, hm, hmin⟩ := (x :: l).toFinset.exists_min_image id
    ⟨x, by simp⟩
  have hρ' : ρ ∈ (Ico m (m + M)).image (· % M) := by
    rw [Nat.image_Ico_mod]; exact mem_range.mpr hρ
  obtain ⟨c, hc', he⟩ := mem_image.mp hρ'
  have hmc := mem_Ico.mp hc'
  have hne : ∀ a ∈ x :: l, a ≠ c := by
    intro a ha' he'; subst a; exact ha c ha' he
  have hiff : (x :: l).IsChain (fun a b => a < c ↔ b < c) :=
    hc.imp_of_mem_imp (by
      intro a b ha' hb' hab
      have := hne a ha'; have := hne b hb'; omega)
  have hprop : ∀ a ∈ x :: l, x < c ↔ a < c :=
    hiff.induction (fun a => x < c ↔ a < c) _
      (fun {_ _} hxy hxa => hxa.trans hxy) (fun _ => Iff.rfl)
  have hml : m < c := by
    have := hne m (List.mem_toFinset.mp hm); omega
  have hxl := (hprop m (List.mem_toFinset.mp hm)).mpr hml
  have hsub : (x :: l).toFinset ⊆ Ico m c := by
    intro a ha'
    exact mem_Ico.mpr ⟨hmin a ha', (hprop a (List.mem_toFinset.mp ha')).mp hxl⟩
  exact ⟨m, c, hmc.1, hmc.2, hsub⟩

/-- The chain need not be monotone or have distinct vertices. -/
theorem unit_chain_card_lt {l : List ℕ} {M ρ : ℕ} (hρ : ρ < M)
    (hc : l.IsChain (fun a b => a ≤ b + 1 ∧ b ≤ a + 1))
    (ha : ∀ a ∈ l, a % M ≠ ρ) : l.toFinset.card < M := by
  obtain ⟨m, c, hmc, hcM, hsub⟩ := unit_chain_window hρ hc ha
  have hcard := card_le_card hsub
  rw [Nat.card_Ico] at hcard
  omega

theorem unit_chain_mod_injective {l : List ℕ} {M ρ : ℕ} (hρ : ρ < M)
    (hc : l.IsChain (fun a b => a ≤ b + 1 ∧ b ≤ a + 1))
    (ha : ∀ a ∈ l, a % M ≠ ρ) : Set.InjOn (· % M) (l.toFinset : Set ℕ) := by
  obtain ⟨m, c, hmc, hcM, hsub⟩ := unit_chain_window hρ hc ha
  intro a ha' b hb' he
  have ha'' := mem_Ico.mp (hsub ha')
  have hb'' := mem_Ico.mp (hsub hb')
  exact Nat.mod_injOn_Ico m M
    (mem_Ico.mpr ⟨ha''.1, ha''.2.trans hcM⟩)
    (mem_Ico.mpr ⟨hb''.1, hb''.2.trans hcM⟩) he

section Payments

variable {A C X : Type*} [DecidableEq A] [DecidableEq C] [DecidableEq X]

/-- Phases not used by any protected member. -/
noncomputable def available (U : Finset C) (P : Finset A) (phase : A → C) : Finset C :=
  U \ P.image phase

/-- Pay the union of all actual items attached to members of this phase. -/
noncomputable def payment (I : Finset A) (phase : A → C) (pay : A → Finset X)
    (c : C) : Finset X := (I.filter (fun a => phase a = c)).biUnion pay

omit [DecidableEq A] in
theorem available_card (U : Finset C) (P : Finset A) (phase : A → C)
    (hP : ∀ a ∈ P, phase a ∈ U) :
    (available U P phase).card = U.card - (P.image phase).card := by
  classical
  apply card_sdiff_of_subset
  simpa only [image_subset_iff] using hP

omit [DecidableEq A] in
theorem protected_not_deleted {U : Finset C} {P : Finset A} {phase : A → C}
    {c : C} (hc : c ∈ available U P phase) {a : A} (ha : a ∈ P) : phase a ≠ c := by
  classical
  intro he
  exact (mem_sdiff.mp hc).2 (he ▸ mem_image_of_mem phase ha)

omit [DecidableEq A] in
/-- Count only members whose phase is actually admissible; shared paid items
can reduce the cost further. No injectivity of the phase or payment maps is assumed. -/
theorem sum_payment_le (I : Finset A) (C₀ : Finset C) (phase : A → C)
    (pay : A → Finset X) :
    (∑ c ∈ C₀, (payment I phase pay c).card) ≤
      ∑ a ∈ I.filter (fun a => phase a ∈ C₀), (pay a).card := by
  classical
  calc
    _ ≤ ∑ c ∈ C₀, ∑ a ∈ I.filter (fun a => phase a = c), (pay a).card :=
      sum_le_sum fun _ _ => card_biUnion_le
    _ = _ := by
      simp only [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      simp only [sum_ite_eq]

/-- Uniform payment averaging over protected phases. The sharper sum above
also omits unprotected members whose phase was forbidden by somebody else. -/
theorem sum_available_payment_le (I P : Finset A) (U : Finset C)
    (phase : A → C) (pay : A → Finset X) :
    (∑ c ∈ available U P phase, (payment I phase pay c).card) ≤
      ∑ a ∈ I \ P, (pay a).card := by
  classical
  refine (sum_payment_le I (available U P phase) phase pay).trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    have h := mem_filter.mp ha
    exact mem_sdiff.mpr ⟨h.1, fun ha' => protected_not_deleted h.2 ha' rfl⟩
  · intros; exact Nat.zero_le _

end Payments

end LeanMachine.PeriodicPhases

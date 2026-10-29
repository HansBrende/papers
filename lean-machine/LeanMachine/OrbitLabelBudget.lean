import LeanMachine.FiniteOrbits

/-! Label counts in a branching root followed by deterministic continuations. -/

namespace LeanMachine.OrbitLabelBudget

open Classical Finset FiniteOrbits

noncomputable section

/-- A changing label consumes one unit of a nonincreasing integer budget. -/
def StepBudget {β : Type*} (s : ℕ → Finset ℕ) (c : ℕ → β) (P : ℕ → ℕ) : Prop :=
  ∀ t, ∀ u ∈ s t, P u ≤ P t ∧ (c u ≠ c t → P u < P t)

theorem image_cloud_card_le_chain {β : Type*} [DecidableEq β]
    {s : ℕ → Finset ℕ} {c : ℕ → β} {P : ℕ → ℕ}
    (hs : DeterministicAfterStep s) (hP : StepBudget s c P)
    (N t : ℕ) (ht : (s t).card ≤ 1) :
    ((cloud s N t).image c).card ≤ P t + 1 := by
  induction N generalizing t with
  | zero => simp [cloud]
  | succ N ih =>
    rcases (s t).eq_empty_or_nonempty with he | ⟨u, hu⟩
    · simp [cloud, he]
    · have he : s t = {u} := by
        ext v
        constructor
        · intro hv
          exact mem_singleton.mpr (card_le_one.mp ht v hv u hu)
        · intro hv
          simpa only [mem_singleton.mp hv] using hu
      simp only [cloud, he, singleton_biUnion, image_insert]
      have hi := ih u (hs t u hu)
      have hp := hP t u hu
      by_cases hc : c u = c t
      · have hm : c t ∈ (cloud s N u).image c :=
          hc ▸ mem_image_of_mem c (mem_cloud_self s N u)
        rw [insert_eq_of_mem hm]
        omega
      · have hb := hp.2 hc
        have hh := card_insert_le (c t) ((cloud s N u).image c)
        omega

/-- Only the root can branch. Each branch contributes at most the root budget
new labels, since their common initial label is counted once. -/
theorem image_cloud_card_le {β : Type*} [DecidableEq β]
    {s : ℕ → Finset ℕ} {c : ℕ → β} {P : ℕ → ℕ}
    (hs : DeterministicAfterStep s) (hP : StepBudget s c P) (N t : ℕ) :
    ((cloud s N t).image c).card ≤ 1 + P t * (s t).card := by
  cases N with
  | zero => simp [cloud]
  | succ N =>
    have hb (u : ℕ) (hu : u ∈ s t) :
        (((cloud s N u).image c).erase (c t)).card ≤ P t := by
      have hi := image_cloud_card_le_chain hs hP N u (hs t u hu)
      have hp := hP t u hu
      by_cases hc : c u = c t
      · have hm : c t ∈ (cloud s N u).image c :=
          hc ▸ mem_image_of_mem c (mem_cloud_self s N u)
        have he := card_erase_add_one hm
        omega
      · have hh := card_erase_le (s := (cloud s N u).image c) (a := c t)
        have hlt := hp.2 hc
        omega
    rw [cloud, image_insert, biUnion_image]
    have he : insert (c t) ((s t).biUnion (fun u => (cloud s N u).image c)) =
        insert (c t) ((s t).biUnion (fun u => ((cloud s N u).image c).erase (c t))) := by
      ext z
      by_cases hz : z = c t <;> simp [mem_biUnion, hz]
    rw [he]
    calc
      _ ≤ 1 + ∑ u ∈ s t, (((cloud s N u).image c).erase (c t)).card := by
        have h₁ := card_insert_le (c t)
          ((s t).biUnion (fun u => ((cloud s N u).image c).erase (c t)))
        have h₂ := card_biUnion_le (s := s t)
          (t := fun u => ((cloud s N u).image c).erase (c t))
        omega
      _ ≤ 1 + ∑ _u ∈ s t, P t := Nat.add_le_add_left (sum_le_sum hb) 1
      _ = _ := by simp [Nat.mul_comm]

theorem mem_cloud_le {s : ℕ → Finset ℕ}
    (hs : ∀ t, ∀ u ∈ s t, u ≤ t) {N t u : ℕ} (hu : u ∈ cloud s N t) : u ≤ t := by
  induction N generalizing t with
  | zero => exact (mem_singleton.mp hu).le
  | succ N ih =>
    rcases mem_insert.mp hu with rfl | hu
    · exact le_rfl
    · obtain ⟨v, hv, hu⟩ := mem_biUnion.mp hu
      exact (ih hu).trans (hs t v hv)

end
end LeanMachine.OrbitLabelBudget

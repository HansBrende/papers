import SourceCovers.SerialCoreCertificates

set_option autoImplicit false

/-! The overlap graph is derived from the original full family spans.
The early component ends in the bridge; the late component does not. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset BoundedNesting
noncomputable section

variable (P : Parameters)

def bankCore (c : Fin 2) (j : Fin P.bankCount) : CoreFamily P.coreFamilies :=
  ⟨P.bankFamily c j, (P.mem_coreFamilies _).mpr (Or.inl ⟨c, j, rfl⟩)⟩

def earlyCore : CoreFamily P.coreFamilies :=
  ⟨P.earlyFamily, (P.mem_coreFamilies _).mpr (Or.inr (Or.inl rfl))⟩

def bridgeCore : CoreFamily P.coreFamilies :=
  ⟨P.bridgeFamily, (P.mem_coreFamilies _).mpr (Or.inr (Or.inr rfl))⟩

theorem core_cases (F : CoreFamily P.coreFamilies) :
    (∃ c : Fin 2, ∃ j : Fin P.bankCount, F = P.bankCore c j) ∨
      F = P.earlyCore ∨ F = P.bridgeCore := by
  rcases (P.mem_coreFamilies F.val).mp F.property with ⟨c, j, he⟩ | he | he
  · exact Or.inl ⟨c, j, Subtype.ext he⟩
  · exact Or.inr (Or.inl (Subtype.ext he))
  · exact Or.inr (Or.inr (Subtype.ext he))

theorem bankCore_injective :
    Function.Injective (fun cj : Fin 2 × Fin P.bankCount => P.bankCore cj.1 cj.2) := by
  intro a b he
  exact P.bankFamily_injective (congrArg Subtype.val he)

theorem bankCore_ne_early (c : Fin 2) (j : Fin P.bankCount) : P.bankCore c j ≠ P.earlyCore := by
  intro he
  have hh := congrArg (fun F : CoreFamily P.coreFamilies => F.val.val.1.val) he
  change (P.bankHeadIndex c j).val = 5 at hh
  have := (P.bankHeadIndex c j).isLt
  omega

theorem bankCore_ne_bridge (c : Fin 2) (j : Fin P.bankCount) : P.bankCore c j ≠ P.bridgeCore := by
  intro he
  have hh := congrArg (fun F : CoreFamily P.coreFamilies => F.val.val.1.val) he
  change (P.bankHeadIndex c j).val = 7 at hh
  have := (P.bankHeadIndex c j).isLt
  omega

theorem width_lt_length : P.width < P.length := by
  have hn := P.bankCount_ge
  have hp := P.width_pos
  dsimp only [length]
  nlinarith

/-- No original core interval crosses the cut separating the two banks. -/
theorem core_span_cut (F : CoreFamily P.coreFamilies) :
    F.val.stop ≤ 9 * P.length ∨ 9 * P.length ≤ F.val.start := by
  rcases P.core_cases F with ⟨c, j, rfl⟩ | rfl | rfl
  · have hb := P.bankFamily_span_bounds c j
    have hw := P.width_lt_length
    fin_cases c
    · left
      change (P.bankFamily _ j).stop ≤ _
      norm_num [bankBase] at hb
      simpa [bankFamily_stop, bankBase] using (show
        4 * P.length + (j.val + 2) * P.width ≤ 9 * P.length by omega)
    · right
      change _ ≤ (P.bankFamily _ j).start
      rw [bankFamily_start]
      change 9 * P.length ≤ 11 * P.length + j.val * P.width
      omega
  · left
    change P.earlyFamily.stop ≤ _
    rw [earlyFamily_stop]
    omega
  · left
    exact P.bridgeFamily_stop_bounds.2.le.trans (by omega)

theorem bankCore_late (c : Fin 2) (j : Fin P.bankCount) :
    9 * P.length ≤ (P.bankCore c j).val.start ↔ c.val = 1 := by
  have hjL := Nat.mul_lt_mul_of_pos_right j.isLt P.width_pos
  change j.val * P.width < P.length at hjL
  have hL := P.length_pos
  fin_cases c
  · change 9 * P.length ≤ (P.bankFamily _ j).start ↔ (0 : ℕ) = 1
    rw [bankFamily_start]
    change 9 * P.length ≤ 4 * P.length + j.val * P.width ↔ (0 : ℕ) = 1
    omega
  · change 9 * P.length ≤ (P.bankFamily _ j).start ↔ (1 : ℕ) = 1
    rw [bankFamily_start]
    change 9 * P.length ≤ 11 * P.length + j.val * P.width ↔ (1 : ℕ) = 1
    omega

theorem adjacent_same_cut {F G : CoreFamily P.coreFamilies}
    (h : (coreModel P.coreFamilies).graph.Adj F G) :
    (9 * P.length ≤ F.val.start ↔ 9 * P.length ≤ G.val.start) := by
  have hF := P.core_span_cut F
  have hG := P.core_span_cut G
  change F ≠ G ∧ F.val.start < G.val.stop ∧ G.val.start < F.val.stop at h
  omega

theorem reachable_same_cut {F G : CoreFamily P.coreFamilies}
    (h : (coreModel P.coreFamilies).graph.Reachable F G) :
    (9 * P.length ≤ F.val.start ↔ 9 * P.length ≤ G.val.start) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (P.adjacent_same_cut h).trans ih

/-- Different copies cannot become connected through any other core family. -/
theorem bankCore_same_copy_of_reachable {c c' : Fin 2} {j j' : Fin P.bankCount}
    (h : (coreModel P.coreFamilies).graph.Reachable (P.bankCore c j) (P.bankCore c' j')) : c = c' := by
  have hh := P.reachable_same_cut h
  rw [bankCore_late, bankCore_late] at hh
  apply Fin.ext
  have := c.isLt
  have := c'.isLt
  omega

theorem bankCore_adj_iff (c c' : Fin 2) (j j' : Fin P.bankCount) :
    (coreModel P.coreFamilies).graph.Adj (P.bankCore c j) (P.bankCore c' j') ↔
      c = c' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by
  constructor
  · intro h
    have hc := P.bankCore_same_copy_of_reachable h.reachable
    subst c'
    refine ⟨rfl, ?_⟩
    change P.bankCore c j ≠ P.bankCore c j' ∧
      (P.bankFamily c j).start < (P.bankFamily c j').stop ∧
      (P.bankFamily c j').start < (P.bankFamily c j).stop at h
    have hne : j.val ≠ j'.val := by
      intro he
      exact h.1 (congrArg (P.bankCore c) (Fin.ext he))
    rw [bankFamily_start, bankFamily_stop, bankFamily_start, bankFamily_stop] at h
    have h₁ : j.val < j'.val + 2 :=
      (Nat.mul_lt_mul_right P.width_pos).mp (Nat.lt_of_add_lt_add_left h.2.1)
    have h₂ : j'.val < j.val + 2 :=
      (Nat.mul_lt_mul_right P.width_pos).mp (Nat.lt_of_add_lt_add_left h.2.2)
    omega
  · rintro ⟨rfl, hj⟩
    change P.bankCore c j ≠ P.bankCore c j' ∧
      (P.bankFamily c j).start < (P.bankFamily c j').stop ∧
      (P.bankFamily c j').start < (P.bankFamily c j).stop
    refine ⟨?_, ?_, ?_⟩
    · intro he
      have hv := congrArg (fun q : Fin 2 × Fin P.bankCount => q.2.val)
        (@bankCore_injective P (c, j) (c, j') he)
      dsimp only at hv
      omega
    · rw [bankFamily_start, bankFamily_stop]
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by omega) P.width_pos) _
    · rw [bankFamily_start, bankFamily_stop]
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by omega) P.width_pos) _

theorem earlyCore_not_adj (F : CoreFamily P.coreFamilies) :
    ¬ (coreModel P.coreFamilies).graph.Adj P.earlyCore F := by
  intro h
  rcases P.core_start_separated F.property with he | hs
  · exact h.ne (Subtype.ext he.symm)
  · change P.earlyCore ≠ F ∧ P.earlyFamily.start < F.val.stop ∧
      F.val.start < P.earlyFamily.stop at h
    rw [earlyFamily_stop] at h
    omega

theorem bankCore_bridge_adj_iff (c : Fin 2) (j : Fin P.bankCount) :
    (coreModel P.coreFamilies).graph.Adj (P.bankCore c j) P.bridgeCore ↔
      c.val = 0 ∧ j.val + 1 = P.bankCount := by
  have hj := j.isLt
  have hB := P.bridgeFamily_stop_bounds
  have hL := P.length_pos
  have hw := P.width_pos
  have hN : P.bankCount * P.width = P.length := rfl
  change (P.bankCore c j ≠ P.bridgeCore ∧
    (P.bankFamily c j).start < P.bridgeFamily.stop ∧
    P.bridgeFamily.start < (P.bankFamily c j).stop) ↔ _
  rw [bankFamily_start, bridgeFamily_start, bankFamily_stop]
  by_cases hc : c.val = 0
  · simp only [bankBase, ite_eq_left hc]
    constructor
    · rintro ⟨_, _, hs⟩
      have hh : P.bankCount < j.val + 2 := (Nat.mul_lt_mul_right hw).mp (by omega)
      exact ⟨hc, by omega⟩
    · rintro ⟨_, he⟩
      have hleft := Nat.mul_lt_mul_of_pos_right hj hw
      have hright := Nat.mul_lt_mul_of_pos_right (show P.bankCount < j.val + 2 by omega) hw
      exact ⟨P.bankCore_ne_bridge _ j, by omega, by omega⟩
  · simp only [bankBase, ite_eq_right hc]
    constructor
    · rintro ⟨_, hs, _⟩
      exact False.elim (by omega)
    · rintro ⟨he, _⟩
      exact False.elim (hc he)

end
end SourceCovers.SerialGeometry.Parameters

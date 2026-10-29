import SourceCovers.SerialFamilies

set_option autoImplicit false

/-! Full-span coloring and exhaustive core/exception partition for the
serial construction. These are the original complete actual families. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset BoundedNesting
noncomputable section

variable (P : Parameters)

def coreFamilies : Finset (ActualFamily P.heads P.horizon) :=
  (univ.image (fun cj : Fin 2 × Fin P.bankCount => P.bankFamily cj.1 cj.2)) ∪
    {P.earlyFamily, P.bridgeFamily}

def exceptionalFamilies : Finset (ActualFamily P.heads P.horizon) := {P.newerFamily, P.olderFamily}

@[simp] theorem mem_coreFamilies (F : ActualFamily P.heads P.horizon) :
    F ∈ P.coreFamilies ↔ (∃ c : Fin 2, ∃ j : Fin P.bankCount, F = P.bankFamily c j) ∨
      F = P.earlyFamily ∨ F = P.bridgeFamily := by
  simp [coreFamilies, Prod.exists, eq_comm, or_assoc, or_left_comm, or_comm]

@[simp] theorem mem_exceptionalFamilies (F : ActualFamily P.heads P.horizon) :
    F ∈ P.exceptionalFamilies ↔ F = P.newerFamily ∨ F = P.olderFamily := by
  simp [exceptionalFamilies]

theorem families_complete : P.coreFamilies ∪ P.exceptionalFamilies = univ := by
  ext F
  simp only [mem_union, mem_coreFamilies, mem_exceptionalFamilies, mem_univ, iff_true]
  rcases P.actualFamily_exhaustive F with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inr (Or.inr h))

theorem core_head_cases {F : ActualFamily P.heads P.horizon} (hF : F ∈ P.coreFamilies) :
    F.val.1.val < 4 ∨ F.val.1.val = 5 ∨ F.val.1.val = 7 := by
  rw [mem_coreFamilies] at hF
  rcases hF with ⟨c, j, rfl⟩ | rfl | rfl
  · exact Or.inl (P.bankHeadIndex c j).isLt
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem exceptional_head_cases {F : ActualFamily P.heads P.horizon}
    (hF : F ∈ P.exceptionalFamilies) : F.val.1.val = 4 ∨ F.val.1.val = 6 := by
  rw [mem_exceptionalFamilies] at hF
  rcases hF with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem core_exceptional_disjoint : Disjoint P.coreFamilies P.exceptionalFamilies := by
  apply Finset.disjoint_left.mpr
  intro F hF hG
  have hc := P.core_head_cases hF
  have he := P.exceptional_head_cases hG
  omega

theorem coreFamilies_card : P.coreFamilies.card = 2 * P.bankCount + 2 := by
  have hne : P.earlyFamily ≠ P.bridgeFamily := by
    intro h
    have he := congrArg (fun F : ActualFamily P.heads P.horizon => F.val.1.val) h
    change (5 : ℕ) = 7 at he
    omega
  have hd : Disjoint (univ.image (fun cj : Fin 2 × Fin P.bankCount => P.bankFamily cj.1 cj.2))
      {P.earlyFamily, P.bridgeFamily} := by
    apply Finset.disjoint_left.mpr
    intro F hF hG
    obtain ⟨⟨c, j⟩, _, rfl⟩ := mem_image.mp hF
    have hh := (P.bankHeadIndex c j).isLt
    rcases mem_insert.mp hG with he | he
    · have ho := congrArg (fun F : ActualFamily P.heads P.horizon => F.val.1.val) he
      change (P.bankHeadIndex c j).val = 5 at ho
      omega
    · have ho := congrArg (fun F : ActualFamily P.heads P.horizon => F.val.1.val) (mem_singleton.mp he)
      change (P.bankHeadIndex c j).val = 7 at ho
      omega
  rw [coreFamilies, card_union_of_disjoint hd, card_image_of_injective _ P.bankFamily_injective]
  simp [hne]

theorem exceptionalFamilies_card : P.exceptionalFamilies.card = 2 := by
  have hne : P.newerFamily ≠ P.olderFamily := by
    intro h
    have he := congrArg (fun F : ActualFamily P.heads P.horizon => F.val.1.val) h
    change (4 : ℕ) = 6 at he
    omega
  simp [exceptionalFamilies, hne]

theorem actualFamilies_card : Fintype.card (ActualFamily P.heads P.horizon) = 2 * P.bankCount + 4 := by
  rw [← card_univ, ← P.families_complete, card_union_of_disjoint P.core_exceptional_disjoint,
    P.coreFamilies_card, P.exceptionalFamilies_card]

private theorem disjoint_of_stop_le {k T : ℕ} {xs : Fin k → ℕ → ℤ}
    (F G : ActualFamily xs T) (h : F.stop ≤ G.start) : Disjoint F.edges G.edges := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have he' := mem_Ico.mp he
  have hf' := mem_Ico.mp hf
  omega

def coreColor (F : ActualFamily P.heads P.horizon) : ℕ := if F.val.2.1 then 0 else 1

@[simp] theorem bankFamily_color (c : Fin 2) (j : Fin P.bankCount) :
    P.coreColor (P.bankFamily c j) = j.val % 2 := by
  change (if decide (j.val % 2 = 0) then 0 else 1) = j.val % 2
  have hm := Nat.mod_lt j.val (by omega : 0 < 2)
  by_cases he : j.val % 2 = 0
  · simp [he]
  · have hh : j.val % 2 = 1 := by omega
    simp [hh]

@[simp] theorem earlyFamily_color : P.coreColor P.earlyFamily = 0 := rfl
@[simp] theorem bridgeFamily_color : P.coreColor P.bridgeFamily = 0 := rfl

theorem bankFamily_span_bounds (c : Fin 2) (j : Fin P.bankCount) :
    P.bankBase c ≤ (P.bankFamily c j).start ∧
      (P.bankFamily c j).stop ≤ P.bankBase c + P.length + P.width := by
  have hm := Nat.mul_le_mul_right P.width (show j.val + 2 ≤ P.bankCount + 1 by have := j.isLt; omega)
  simp only [bankFamily_start, bankFamily_stop]
  dsimp only [length]
  constructor
  · omega
  · nlinarith

theorem banks_disjoint_of_color (c c' : Fin 2) (j j' : Fin P.bankCount)
    (hne : P.bankFamily c j ≠ P.bankFamily c' j')
    (hc : P.coreColor (P.bankFamily c j) = P.coreColor (P.bankFamily c' j')) :
    Disjoint (P.bankFamily c j).edges (P.bankFamily c' j').edges := by
  by_cases he : c = c'
  · subst c'
    have hj : j ≠ j' := fun h => hne (h ▸ rfl)
    have hjv : j.val ≠ j'.val := fun h => hj (Fin.ext h)
    rw [bankFamily_color, bankFamily_color] at hc
    have hs : j.val + 2 ≤ j'.val ∨ j'.val + 2 ≤ j.val := by omega
    rcases hs with hs | hs
    · apply disjoint_of_stop_le
      rw [bankFamily_stop, bankFamily_start]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right P.width hs) _
    · apply Disjoint.symm
      apply disjoint_of_stop_le
      rw [bankFamily_stop, bankFamily_start]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right P.width hs) _
  · have hb := P.bankFamily_span_bounds c j
    have hb' := P.bankFamily_span_bounds c' j'
    have hw : P.width < P.length := by
      have hn := P.bankCount_ge
      have hp := P.width_pos
      dsimp only [length]
      nlinarith
    fin_cases c <;> fin_cases c'
    · exact False.elim (he rfl)
    · apply disjoint_of_stop_le
      simp only [bankFamily_start, bankFamily_stop] at hb hb' ⊢
      norm_num [bankBase] at hb hb' ⊢
      omega
    · apply Disjoint.symm
      apply disjoint_of_stop_le
      simp only [bankFamily_start, bankFamily_stop] at hb hb' ⊢
      norm_num [bankBase] at hb hb' ⊢
      omega
    · exact False.elim (he rfl)

theorem bank_early_disjoint (c : Fin 2) (j : Fin P.bankCount) :
    Disjoint (P.bankFamily c j).edges P.earlyFamily.edges := by
  apply Disjoint.symm
  apply disjoint_of_stop_le
  rw [earlyFamily_stop]
  have hb := (P.bankFamily_span_bounds c j).1
  unfold bankBase at hb
  split_ifs at hb <;> omega

theorem bank_bridge_disjoint_of_color (c : Fin 2) (j : Fin P.bankCount)
    (hc : P.coreColor (P.bankFamily c j) = 0) :
    Disjoint (P.bankFamily c j).edges P.bridgeFamily.edges := by
  rw [bankFamily_color] at hc
  have hm : P.bankCount % 2 = 0 := by unfold bankCount; omega
  have hj : j.val + 2 ≤ P.bankCount := by have := j.isLt; omega
  have hs := Nat.mul_le_mul_right P.width hj
  have hB := P.bridgeFamily_stop_bounds
  fin_cases c
  · apply disjoint_of_stop_le
    rw [bankFamily_stop, bridgeFamily_start]
    change 4 * P.length + (j.val + 2) * P.width ≤ 5 * P.length
    change (j.val + 2) * P.width ≤ P.length at hs
    omega
  · apply Disjoint.symm
    apply disjoint_of_stop_le
    rw [bankFamily_start]
    change P.bridgeFamily.stop ≤ 11 * P.length + j.val * P.width
    omega

theorem early_bridge_disjoint : Disjoint P.earlyFamily.edges P.bridgeFamily.edges := by
  apply disjoint_of_stop_le
  rw [earlyFamily_stop, bridgeFamily_start]
  omega

/-- The manuscript's two colors are the original upper/lower side keys. -/
theorem core_span_coloring : HasSpanColoring P.coreFamilies 2 := by
  refine ⟨P.coreColor, ?_, ?_⟩
  · intro F _
    unfold coreColor
    split <;> omega
  · intro F hF G hG hne hc
    rw [mem_coreFamilies] at hF hG
    rcases hF with ⟨c, j, rfl⟩ | rfl | rfl <;>
      rcases hG with ⟨c', j', rfl⟩ | rfl | rfl
    · exact P.banks_disjoint_of_color c c' j j' hne hc
    · exact P.bank_early_disjoint c j
    · exact P.bank_bridge_disjoint_of_color c j hc
    · exact (P.bank_early_disjoint c' j').symm
    · exact False.elim (hne rfl)
    · exact P.early_bridge_disjoint
    · exact (P.bank_bridge_disjoint_of_color c' j' hc.symm).symm
    · exact P.early_bridge_disjoint.symm
    · exact False.elim (hne rfl)

theorem exceptional_spans_disjoint : Disjoint P.olderFamily.edges P.newerFamily.edges := by
  apply disjoint_of_stop_le
  have ho := P.olderFamily_stop_lt
  rw [newerFamily_start]
  omega

end
end SourceCovers.SerialGeometry.Parameters

import SharedDecoders.CompositionOrbitExchange
import SharedDecoders.UniformSandwich
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-! # A literal one-column patch of a complete permutation -/

namespace SharedDecoders

variable {d : ℕ} {A : Type*} [Zero A]

abbrev ColumnWord (d : ℕ) (A : Type*) := ZMod d → A

def constantColumns (u : ColumnWord d A) : State d A := fun i _ => u i

def puncturedColumns (u : ColumnWord d A) : State d A :=
  fun i c => if c = 0 then 0 else u i

def singletonRest (c : ZMod d) : Bool := decide (c = 0)

theorem one_ne_zero_of_two_le (hd : 2 ≤ d) : (1 : ZMod d) ≠ 0 := by
  intro h
  have hh : d ∣ 1 := (ZMod.natCast_eq_zero_iff 1 d).mp (by simpa using h)
  have := Nat.le_of_dvd (by decide : 0 < 1) hh
  omega

theorem puncturedColumns_injective (hd : 2 ≤ d) :
    Function.Injective (puncturedColumns (d := d) (A := A)) := by
  intro u v h
  funext i
  have := congrArg (fun X => X i 1) h
  simpa [puncturedColumns, one_ne_zero_of_two_le hd] using this

omit [Zero A] in
theorem constantColumns_injective :
    Function.Injective (constantColumns (d := d) (A := A)) := by
  intro u v h
  exact funext fun i => congrArg (fun X => X i 0) h

theorem punctured_constant_disjoint (u v : {u : ColumnWord d A // u ≠ 0}) :
    puncturedColumns u.val ≠ constantColumns v.val := by
  intro h
  apply v.property
  funext i
  have := congrArg (fun X => X i 0) h
  simpa [puncturedColumns, constantColumns] using this.symm

@[simp] theorem puncturedColumns_zero : puncturedColumns (0 : ColumnWord d A) = 0 := by
  funext i c
  simp [puncturedColumns]

@[simp] theorem constantColumns_zero : constantColumns (0 : ColumnWord d A) = 0 := rfl

noncomputable def columnPatch (hd : 2 ≤ d) : Equiv.Perm (State d A) :=
  exchangeEquiv (fun u : {u : ColumnWord d A // u ≠ 0} => puncturedColumns u.val)
    (fun u => constantColumns u.val)
    ((puncturedColumns_injective hd).comp Subtype.val_injective)
    (constantColumns_injective.comp Subtype.val_injective) punctured_constant_disjoint

theorem columnPatch_involutive (hd : 2 ≤ d) :
    Function.Involutive (columnPatch (A := A) hd) :=
  exchangeFamilies_involutive _ _
    ((puncturedColumns_injective hd).comp Subtype.val_injective)
    (constantColumns_injective.comp Subtype.val_injective) punctured_constant_disjoint

theorem columnPatch_nonzero_column (hd : 2 ≤ d) (X : State d A)
    (c : ZMod d) (hc : c ≠ 0) (i : ZMod d) : columnPatch hd X i c = X i c := by
  classical
  let u := fun u : {u : ColumnWord d A // u ≠ 0} => puncturedColumns u.val
  let v := fun u : {u : ColumnWord d A // u ≠ 0} => constantColumns u.val
  change exchangeFamilies u v X i c = X i c
  by_cases hu : ∃ z, u z = X
  · obtain ⟨z, rfl⟩ := hu
    rw [exchangeFamilies_left u v ((puncturedColumns_injective hd).comp Subtype.val_injective)]
    simp [u, v, puncturedColumns, constantColumns, hc]
  · by_cases hv : ∃ z, v z = X
    · obtain ⟨z, rfl⟩ := hv
      rw [exchangeFamilies_right u v
        (constantColumns_injective.comp Subtype.val_injective) punctured_constant_disjoint]
      simp [u, v, puncturedColumns, constantColumns, hc]
    · rw [exchangeFamilies_outside u v X hu hv]

theorem columnPatch_zero (hd : 2 ≤ d) : columnPatch (A := A) hd 0 = 0 := by
  apply exchangeFamilies_outside
  · rintro ⟨u, hu⟩
    apply u.property
    apply puncturedColumns_injective hd
    simpa [puncturedColumns] using hu
  · rintro ⟨u, hu⟩
    apply u.property
    apply constantColumns_injective
    simpa [constantColumns] using hu

theorem columnPatch_punctured (hd : 2 ≤ d) (u : ColumnWord d A) :
    columnPatch hd (puncturedColumns u) = constantColumns u := by
  by_cases hu : u = 0
  · subst u
    simpa [puncturedColumns, constantColumns] using columnPatch_zero (A := A) hd
  · exact exchangeFamilies_left _ _
      ((puncturedColumns_injective hd).comp Subtype.val_injective) ⟨u, hu⟩

theorem columnPatch_classUniform (hd : 2 ≤ d) :
    ClassUniform singletonRest (columnPatch (A := A) hd) := by
  classical
  refine ⟨fun t X i => if t then columnPatch hd X i 0 else X i 0, ?_⟩
  intro X c i
  by_cases hc : c = 0
  · subst c
    simp [singletonRest]
  · simp [singletonRest, hc, columnPatch_nonzero_column hd X c hc i, rot]

/-- An equivariant permutation followed by the patch is a total singleton/rest
map. This is composition of actual total maps, without an extension hypothesis. -/
theorem columnPatch_comp_classUniform (hd : 2 ≤ d)
    (H : State d A → State d A) (hH : Equivariant H) :
    ClassUniform singletonRest (columnPatch hd ∘ H) :=
by
  obtain ⟨f, hf⟩ := columnPatch_classUniform (A := A) hd
  refine ⟨fun t X => f t (H X), ?_⟩
  intro X c i
  simpa only [Function.comp_apply, hH c X] using hf (H X) c i

/-- The patch changes exactly two complete states for each nonzero column
word; this counts whole-state disagreement, not changed output columns. -/
theorem columnPatch_support_card [Fintype A] (hd : 2 ≤ d) :
    Nat.card {X : State d A // columnPatch hd X ≠ X} =
      2 * (Fintype.card A ^ d - 1) := by
  classical
  let : NeZero d := ⟨by omega⟩
  have h := exchangeFamilies_support_card
    (fun u : {u : ColumnWord d A // u ≠ 0} => puncturedColumns u.val)
    (fun u => constantColumns u.val)
    ((puncturedColumns_injective hd).comp Subtype.val_injective)
    (constantColumns_injective.comp Subtype.val_injective) punctured_constant_disjoint
  change Nat.card {X : State d A // columnPatch hd X ≠ X} = _ at h
  rw [Fintype.card_subtype_compl (fun u : ColumnWord d A => u = 0)] at h
  simpa [ColumnWord, Fintype.card_fun, ZMod.card] using h

end SharedDecoders

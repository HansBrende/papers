import SourceCovers.SerialGrid
import SourceCovers.SerialCorePacking

set_option autoImplicit false

/-! The Q nonzero raw targets and the Q seeds which recover them with H. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset LeanMachine
noncomputable section

variable (P : Parameters)

theorem gridFloor_lt (i : Fin P.targets) : i.val * P.length / P.targets < P.length := by
  apply (Nat.div_lt_iff_lt_mul P.targets_pos).mpr
  have := Nat.mul_lt_mul_of_pos_right i.isLt P.length_pos
  nlinarith

theorem gridFloor_large {i : Fin P.targets} (hi : i ≠ 0) :
    256 ≤ i.val * P.length / P.targets := by
  apply (Nat.le_div_iff_mul_le P.targets_pos).mpr
  have hi' : 1 ≤ i.val := Fin.pos_iff_ne_zero.mpr hi
  have hm := Nat.mul_le_mul_right P.length hi'
  exact P.targets_spacing.le.trans (by simpa using hm)

/-- Index zero is the extra strictly clipped source; the other indices
are the surviving physical grid coordinates. -/
def coverTarget (i : Fin P.targets) : ℕ :=
  if i = 0 then P.length - 1 else P.length - i.val * P.length / P.targets

theorem coverTarget_bounds (i : Fin P.targets) :
    0 < P.coverTarget i ∧ P.coverTarget i < P.length := by
  have hL := P.m_lt_length
  have hm := P.hm
  have hf := P.gridFloor_lt i
  by_cases hi : i = 0
  · simp only [coverTarget, ite_eq_left hi]
    omega
  · have hlarge := P.gridFloor_large hi
    simp only [coverTarget, ite_eq_right hi]
    omega

theorem coverTarget_ne_owner (i : Fin P.targets) : P.coverTarget i ≠ P.length - 2 := by
  have hL := P.m_lt_length
  have hm := P.hm
  have hf := P.gridFloor_lt i
  by_cases hi : i = 0
  · simp only [coverTarget, ite_eq_left hi]
    omega
  · have hlarge := P.gridFloor_large hi
    simp only [coverTarget, ite_eq_right hi]
    omega

theorem coverTarget_injective : Function.Injective P.coverTarget := by
  intro i j he
  have hiL := P.gridFloor_lt i
  have hjL := P.gridFloor_lt j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · have hh := P.gridFloor_large hj
    simp only [coverTarget, ite_eq_left hi, ite_eq_right hj] at he
    omega
  · have hh := P.gridFloor_large hi
    simp only [coverTarget, ite_eq_right hi, ite_eq_left hj] at he
    omega
  · apply P.sparseDeparture_strictMono.injective
    simp only [coverTarget, ite_eq_right hi, ite_eq_right hj] at he
    dsimp only [sparseDeparture]
    omega

def coverTargets : Finset ℕ := univ.image P.coverTarget

theorem coverTargets_card : P.coverTargets.card = P.targets := by
  rw [coverTargets, card_image_of_injective _ P.coverTarget_injective]
  exact Fintype.card_fin _

theorem coverTargets_avoid {a : ℕ} (ha : a ∈ P.coverTargets) :
    a ≠ 0 ∧ a ≠ P.length - 2 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact ⟨(P.coverTarget_bounds i).1.ne', P.coverTarget_ne_owner i⟩

def completeRaw : Finset ℕ := insert 0 P.coverTargets

/-- The clipping correction changes the first seed from 2L to 2L+1. -/
def coverSeed (i : Fin P.targets) : ℕ :=
  if i = 0 then 2 * P.length + 1 else P.sparseDeparture i

theorem coverSeed_bounds (i : Fin P.targets) :
    2 * P.length < P.coverSeed i ∧ P.coverSeed i < 3 * P.length := by
  have hL := P.m_lt_length
  have hm := P.hm
  by_cases hi : i = 0
  · simp only [coverSeed, ite_eq_left hi]
    omega
  · have hlo := P.gridFloor_large hi
    have hhi := (P.sparseDeparture_bounds i).2
    simp only [coverSeed, ite_eq_right hi]
    constructor
    · dsimp only [sparseDeparture]
      omega
    · omega

theorem coverSeed_injective : Function.Injective P.coverSeed := by
  intro i j he
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · have hh := P.gridFloor_large hj
    simp only [coverSeed, ite_eq_left hi, ite_eq_right hj, sparseDeparture] at he
    omega
  · have hh := P.gridFloor_large hi
    simp only [coverSeed, ite_eq_right hi, ite_eq_left hj, sparseDeparture] at he
    omega
  · apply P.sparseDeparture_strictMono.injective
    simpa only [coverSeed, ite_eq_right hi, ite_eq_right hj] using he

theorem coverSeed_before_horizon (i : Fin P.targets) : P.coverSeed i < P.horizon := by
  have := (P.coverSeed_bounds i).2
  dsimp only [horizon]
  omega

theorem raw_coverSeed (i : Fin P.targets) : P.raw (P.coverSeed i) = 0 :=
  P.raw_after (by have := (P.coverSeed_bounds i).1; omega)

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
  (head : Fin k) (hx : xs head = NativeExcursion.walk P.early)
  (hT : P.early.arrive 0 < T)

local notation "H" => NativeExcursion.family P.early head hx hT

theorem early_shadow_coverSeed (i : Fin P.targets) :
    (H).shadow (P.coverSeed i) = P.coverTarget i := by
  rw [P.early_shadow_return head hx hT (P.coverSeed_bounds i).1 (P.coverSeed_bounds i).2.le]
  have hL := P.m_lt_length
  have hm := P.hm
  have hf := P.gridFloor_lt i
  by_cases hi : i = 0
  · simp only [coverSeed, coverTarget, ite_eq_left hi]
    omega
  · simp only [coverSeed, coverTarget, ite_eq_right hi, sparseDeparture]
    omega

/-- A seed covers zero and exactly one target in the complete ordinary
core orbit. All later families are permitted, with no coloring requirement. -/
theorem coverSeed_rawOrbit (K : Finset (ActualFamily xs T)) (hH : H ∈ K)
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start) (i : Fin P.targets) :
    P.raw '' shadowOrbit K (P.coverSeed i) = ({0, P.coverTarget i} : Set ℕ) := by
  have hread : P.raw ((H).shadow (P.coverSeed i)) = P.coverTarget i := by
    rw [P.early_shadow_coverSeed head hx hT]
    exact P.raw_initial (P.coverTarget_bounds i).2
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hp := P.early_core_orbit_pair head hx hT K hK (P.coverSeed_bounds i).2.le hu
    rcases Set.mem_insert_iff.mp hp with rfl | he
    · simp [P.raw_coverSeed]
    · rw [Set.mem_singleton_iff.mp he, hread]
      simp
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨P.coverSeed i, mem_shadowOrbit_self _ _, P.raw_coverSeed i⟩
    · refine ⟨(H).shadow (P.coverSeed i), ⟨[H], ?_, rfl⟩, ?_⟩
      · simpa using hH
      · exact hread.trans (Set.mem_singleton_iff.mp ha).symm

end
end SourceCovers.SerialGeometry.Parameters

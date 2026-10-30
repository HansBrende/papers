import GapAreaMemo.Z3DWalks
import GapAreaMemo.StairFamilies

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: its families

Every complete family of the geometry is the upper or lower family of a bank
zigzag on head X or Y, or one of the two exceptions. Bank zigzags occupy
global slots `0, …, 3K-1` in time order (bank C, then B, then A); upper
families of distinct slots, and lower families of distinct slots, have
disjoint spans.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag

variable (P : Index)

theorem heads_X : P.heads 0 = P.walkX := by simp [heads]
theorem heads_Y : P.heads 1 = P.walkY := by simp [heads]
theorem heads_E : P.heads 2 = SourceCovers.NativeExcursion.walk P.eSchedule := by simp [heads]
theorem heads_G : P.heads 3 = SourceCovers.NativeExcursion.walk P.gSchedule := by simp [heads]

theorem segX_last : P.segX (P.nX - 1) = P.segA 1 := by
  have hN := P.NX_pos; have hK := P.K_eq_NX
  unfold nX
  rw [P.segX_A (by omega) (by omega)]
  congr 1; omega

theorem segY_last : P.segY (P.nY - 1) = P.segA 2 := by
  have hN := P.NY_pos; have hK := P.K_eq_NY
  unfold nY
  rw [P.segY_A (by omega) (by omega)]
  congr 1; omega

theorem finishX_lt {j : ℕ} (hj : j < P.nX) : (P.segX j).finish < P.T := by
  have hN := P.NX_pos
  rcases Nat.lt_or_ge (j + 1) P.nX with h | h
  · have h1 := P.finishX_le j
    have h2 := P.startX_strictMono.monotone (show j + 1 ≤ P.nX - 1 by omega)
    have h3 : P.startX (P.nX - 1) < P.T := by
      unfold nX at *
      rw [P.startX_A (by omega) (by omega)]
      have := P.σA_le_OA (k := P.K - 2 * (3 * P.NX - 1 - 2 * P.NX)); have := P.OA_lt_T; omega
    omega
  · rw [show j = P.nX - 1 by omega, P.segX_last, P.segA_one_finish]
    have := P.OA_lt_T; omega

theorem finishY_lt {j : ℕ} (hj : j < P.nY) : (P.segY j).finish < P.T := by
  have hN := P.NY_pos
  rcases Nat.lt_or_ge (j + 1) P.nY with h | h
  · have h1 := P.finishY_le j
    have h2 := P.startY_strictMono.monotone (show j + 1 ≤ P.nY - 1 by omega)
    have h3 : P.startY (P.nY - 1) < P.T := by
      unfold nY at *
      rw [P.startY_A (by omega) (by omega)]
      have := P.σA_le_OA (k := P.K - 1 - 2 * (3 * P.NY - 1 - 2 * P.NY)); have := P.OA_lt_T; omega
    omega
  · rw [show j = P.nY - 1 by omega, P.segY_last, P.segA_two_finish (by have := P.K_eq_NY; omega)]
    have := P.σA_one_lt_OA; have := P.OA_lt_T; omega

/-- Head X as a staircase of zigzag segments. -/
theorem stairX : StairFamilies.Stair P.heads P.T 0 P.segX P.startX P.nX where
  valid := P.validX
  walk_eq := P.heads_X
  finish_le := fun j _ => P.finishX_le j
  finish_lt := fun _ hj => P.finishX_lt hj

/-- Head Y as a staircase of zigzag segments. -/
theorem stairY : StairFamilies.Stair P.heads P.T 1 P.segY P.startY P.nY where
  valid := P.validY
  walk_eq := P.heads_Y
  finish_le := fun j _ => P.finishY_le j
  finish_lt := fun _ hj => P.finishY_lt hj

theorem hg_pos : 0 < P.hg := by
  unfold hg sumA
  have : P.a 1 ≤ ∑ i ∈ Ioc 0 P.K, P.a i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (by simp only [mem_Ioc]; exact ⟨by norm_num, P.K_pos⟩)
  have := P.a_pos 1
  omega

instance hgNeZero : NeZero P.hg := ⟨P.hg_pos.ne'⟩

theorem eArrive_lt : P.eSchedule.arrive 0 < P.T := by
  show P.OB - (0 : Fin P.hg).val < P.T
  have h1 : P.OB < P.OA := by have := P.OB_lt_σA (k := 0); unfold OA; omega
  have := P.OA_lt_T
  simp only [Fin.val_zero, Nat.sub_zero]
  omega

theorem gArrive_lt : P.gSchedule.arrive 0 < P.T := by
  show P.OA - (0 : Fin P.hg).val < P.T
  have := P.OA_lt_T
  simp only [Fin.val_zero, Nat.sub_zero]
  omega

/-- The older exception. -/
noncomputable def eFam : ActualFamily P.heads P.T :=
  SourceCovers.NativeExcursion.family P.eSchedule 2 P.heads_E P.eArrive_lt

/-- The newer exception. -/
noncomputable def gFam : ActualFamily P.heads P.T :=
  SourceCovers.NativeExcursion.family P.gSchedule 3 P.heads_G P.gArrive_lt

/-- The core: all upper and lower families of the bank zigzags. -/
noncomputable def core : Finset (ActualFamily P.heads P.T) :=
  (univ.image (fun j : Fin P.nX => P.stairX.upper j j.isLt)) ∪
  (univ.image (fun j : Fin P.nX => P.stairX.lower j j.isLt)) ∪
  (univ.image (fun j : Fin P.nY => P.stairY.upper j j.isLt)) ∪
  (univ.image (fun j : Fin P.nY => P.stairY.lower j j.isLt))

noncomputable def exceptions : Finset (ActualFamily P.heads P.T) := {P.eFam, P.gFam}

theorem eFam_head : P.eFam.1.1 = 2 := rfl
theorem gFam_head : P.gFam.1.1 = 3 := rfl

theorem mem_core_head {q : ActualFamily P.heads P.T} (hq : q ∈ P.core) :
    q.1.1 = 0 ∨ q.1.1 = 1 := by
  simp only [core, mem_union, mem_image, mem_univ, true_and] at hq
  rcases hq with ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- **Every family is a bank family or an exception.** -/
theorem family_mem (q : ActualFamily P.heads P.T) : q ∈ P.core ∨ q = P.eFam ∨ q = P.gFam := by
  have hh : q.1.1.val < 4 := q.1.1.isLt
  rcases (show q.1.1 = 0 ∨ q.1.1 = 1 ∨ q.1.1 = 2 ∨ q.1.1 = 3 by
    rcases q.1.1 with ⟨v, hv⟩; interval_cases v <;> simp) with h | h | h | h
  · obtain ⟨j, hj, hq | hq⟩ := P.stairX.family_cases q h
    · left; simp only [core, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl ⟨⟨j, hj⟩, hq.symm⟩))
    · left; simp only [core, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr ⟨⟨j, hj⟩, hq.symm⟩))
  · obtain ⟨j, hj, hq | hq⟩ := P.stairY.family_cases q h
    · left; simp only [core, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl (Or.inr ⟨⟨j, hj⟩, hq.symm⟩)
    · left; simp only [core, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨⟨j, hj⟩, hq.symm⟩
  · right; left
    exact SourceCovers.NativeExcursion.family_unique P.eSchedule 2 P.heads_E P.eArrive_lt q h
  · right; right
    exact SourceCovers.NativeExcursion.family_unique P.gSchedule 3 P.heads_G P.gArrive_lt q h

theorem core_disjoint : Disjoint P.core P.exceptions := by
  rw [disjoint_left]
  intro q hq hqe
  have h1 := P.mem_core_head hq
  simp only [exceptions, mem_insert, mem_singleton] at hqe
  rcases hqe with rfl | rfl
  · rw [P.eFam_head] at h1; rcases h1 with h | h <;> exact absurd h (by decide)
  · rw [P.gFam_head] at h1; rcases h1 with h | h <;> exact absurd h (by decide)

theorem exceptions_card : P.exceptions.card ≤ 2 := card_insert_le _ _

theorem outside_none (q : ActualFamily P.heads P.T) (hq : q ∉ P.core ∪ P.exceptions) :
    q.hops.card ≤ 0 := by
  exfalso
  apply hq
  rcases P.family_mem q with h | h | h
  · exact mem_union_left _ h
  · exact mem_union_right _ (by simp [exceptions, h])
  · exact mem_union_right _ (by simp [exceptions, h])

end SourceCovers.Z3D.Index

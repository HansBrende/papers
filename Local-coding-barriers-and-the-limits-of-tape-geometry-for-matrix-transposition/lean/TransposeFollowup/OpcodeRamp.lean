import TransposeFollowup.PageOpcodeWalk

/-! A vertex record controls one seven-phase time block. Its only motion is
in the middle four phases, with the direction specified by its opcode. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def opcodeRampWalk {v k : ℕ} (R offset : ℕ)
    (ops : Fin v → Fin k → PageOpcode) (p : Fin k) (t : ℕ) : ℤ :=
  ∑ u, (ops u p).direction * cappedRamp (4 * R) (offset + 7 * R * u.val + R) t

theorem cappedRamp_record_delta {v : ℕ} (R offset : ℕ) (i j : Fin v)
    (s : ℕ) (hs : s ≤ 7 * R) :
    cappedRamp (4 * R) (offset + 7 * R * j.val + R) (offset + 7 * R * i.val + s) -
      cappedRamp (4 * R) (offset + 7 * R * j.val + R) (offset + 7 * R * i.val) =
      if i = j then cappedRamp (4 * R) R s else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    dsimp [cappedRamp]
    omega
  · rw [ite_eq_right hij]
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · have hm := Nat.mul_le_mul_left (7 * R) (Nat.succ_le_of_lt hlt)
      dsimp [cappedRamp]
      have hb : offset + 7 * R * i.val + s ≤ offset + 7 * R * j.val + R := by
        nlinarith
      omega
    · have hm := Nat.mul_le_mul_left (7 * R) (Nat.succ_le_of_lt hgt)
      have hb : offset + 7 * R * j.val + R + 4 * R ≤ offset + 7 * R * i.val := by
        nlinarith
      dsimp [cappedRamp]
      omega

theorem opcodeRampWalk_record_delta {v k : ℕ} (R offset : ℕ)
    (ops : Fin v → Fin k → PageOpcode) (p : Fin k) (i : Fin v)
    (s : ℕ) (hs : s ≤ 7 * R) :
    opcodeRampWalk R offset ops p (offset + 7 * R * i.val + s) -
      opcodeRampWalk R offset ops p (offset + 7 * R * i.val) =
      (ops i p).direction * cappedRamp (4 * R) R s := by
  classical
  unfold opcodeRampWalk
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, cappedRamp_record_delta R offset i _ s hs, mul_ite, mul_zero]
  simp

theorem opcodeRampWalk_record_end {v k : ℕ} (R offset : ℕ)
    (ops : Fin v → Fin k → PageOpcode) (p : Fin k) (i : Fin v) :
    opcodeRampWalk R offset ops p (offset + 7 * R * i.val + 7 * R) =
      opcodeRampWalk R offset ops p (offset + 7 * R * i.val) +
        (ops i p).direction * (4 * R : ℕ) := by
  have h := opcodeRampWalk_record_delta R offset ops p i (7 * R) le_rfl
  have hr : cappedRamp (4 * R) R (7 * R) = (4 * R : ℕ) := by
    dsimp [cappedRamp]
    omega
  rw [hr] at h
  omega

theorem opcodeRampWalk_before {v k : ℕ} (R offset : ℕ)
    (ops : Fin v → Fin k → PageOpcode) (p : Fin k) {t : ℕ} (ht : t ≤ offset) :
    opcodeRampWalk R offset ops p t = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  have h : cappedRamp (4 * R) (offset + 7 * R * u.val + R) t = 0 := by
    dsimp [cappedRamp]
    omega
  rw [h, mul_zero]

namespace NestedMatchingPages

open Classical

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

theorem walk_eq_opcodeRampWalk (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin k) (t : ℕ) :
    D.walk r K offset hr hK p t = opcodeRampWalk (K * r) offset D.opcode p t := by
  rw [D.walk_eq_opcode_sum]
  simp only [opcodeRampWalk, start, Nat.mul_assoc]

end NestedMatchingPages
end TransposeFollowup

import TransposeFollowup.ScheduledBankRows
import TransposeFollowup.ScheduledMotionError
import TransposeFollowup.ClippedAffineRamps

/-! Uniform geometry for sequential fixed-width row updates. Only their
paid cost and restored head positions are used; their internal motion
and data may be arbitrary. The final bank rewind is included. -/
namespace TransposeFollowup.ScheduledBankRows
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction AffineMotion
set_option autoImplicit false
variable {M : Type*} {W : ℕ} (U : Update M W)

theorem linear_ticks (r D : ℕ) (hc : U.cost+W=D*W) : ticks U r=(D+1)*(r*W) := by
  rw [ticks,hc]
  ring

theorem rows_path_error (r D : ℕ) (hc : U.cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (m : ℕ) (hm : m ≤ r*(U.cost+W)) (t : Fin 2) :
    |(trajectory (rowsSchedule U r) w c m).work.pos t-c.work.pos t-
      (if t=0 then ((m/D : ℕ) : ℤ) else 0)| ≤ (D+1)*W := by
  have hN : 0<U.cost+W := by rw [hc]; exact Nat.mul_pos hD hW
  have h := repeat_block_error (stepSchedule U) (action 0 ⟨none,.stay⟩) (U.cost+W) hN w t
    (if t=0 then (W : ℤ) else 0) (fun d => by
      rw [step_exact,step_position]
      by_cases ht : t=0 <;> simp [ht]) r c m hm
  have he : (m/(D*W))*W+(m/D)%W=m/D := by
    simpa only [Nat.div_div_eq_div_mul] using Nat.div_add_mod' (m/D) W
  have hez : ((m/(D*W) : ℕ) : ℤ)*W+((m/D)%W : ℕ)=(m/D : ℕ) := by exact_mod_cast he
  have hr : (((m/D)%W : ℕ) : ℤ)<W := by exact_mod_cast Nat.mod_lt (m/D) hW
  have hz : (0 : ℤ) ≤ ((m/D)%W : ℕ) := Nat.cast_nonneg _
  change |(trajectory (rowsSchedule U r) w c m).work.pos t-c.work.pos t-
    (m/(U.cost+W) : ℕ)*(if t=0 then (W : ℤ) else 0)| ≤ (U.cost+W : ℕ) at h
  rw [hc,abs_le] at h
  rw [abs_le]
  by_cases ht : t=0 <;> simp only [ht,ite_true,ite_false,mul_zero,Nat.cast_mul] at h ⊢
  · constructor <;> nlinarith
  · constructor <;> nlinarith [Nat.cast_nonneg (α:=ℤ) W]

def path (P D : ℕ) (t : Fin 2) (m : ℕ) : ℤ :=
  if t=0 then ((min (m/D) P : ℕ) : ℤ)-(min (m-D*P) P : ℕ) else 0

theorem path_after (P D : ℕ) (hD : 0<D) (t : Fin 2) (m : ℕ) (hm : (D+1)*P ≤ m) :
    path P D t m=0 := by
  have hd : P ≤ m/D := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith)
  have hr : P ≤ m-D*P := by
    have hm' : D*P+P ≤ m := by nlinarith
    omega
  simp only [path,Nat.min_eq_right hd,Nat.min_eq_right hr,sub_self,ite_self]

theorem path_frozen (P D : ℕ) (hD : 0<D) (t : Fin 2) (m : ℕ) :
    path P D t (min m ((D+1)*P))=path P D t m := by
  by_cases hm : m ≤ (D+1)*P
  · rw [Nat.min_eq_left hm]
  · rw [Nat.min_eq_right (by omega),path_after P D hD t _ le_rfl,path_after P D hD t m (by omega)]

theorem schedule_path_error (r D : ℕ) (hc : U.cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (m : ℕ) (hm : m ≤ ticks U r) (t : Fin 2) :
    |(trajectory (schedule U r) w c m).work.pos t-c.work.pos t-path (r*W) D t m| ≤ (D+1)*W := by
  have h := append_position_error (rowsSchedule U r) (fun _ => action 0 ⟨none,.left⟩)
    (r*(U.cost+W)) (r*W) w t (fun j => if t=0 then ((j/D : ℕ) : ℤ) else 0)
    (fun j => -(if t=0 then (j : ℤ) else 0)) ((D+1)*W) 0 le_rfl (by simp)
    (fun d j hj => rows_path_error U r D hc hD hW w d j hj t)
    (fun d j _ => by
      change |(rewind 0 w d j).work.pos t-d.work.pos t-_| ≤ 0
      rw [rewind_position]
      by_cases ht : t=0 <;> simp [ht]) c m hm
  have he : r*(U.cost+W)=D*(r*W) := by rw [hc]; ring
  have hdiv : min m (r*(U.cost+W))/D=min (m/D) (r*W) := by
    rw [he]
    have hh : Monotone (fun k : ℕ => k/D) := fun _ _ h => Nat.div_le_div_right h
    rw [hh.map_min,Nat.mul_div_cancel_left _ hD]
  have hrew : m-r*(U.cost+W)=min (m-D*(r*W)) (r*W) := by
    unfold ticks at hm
    rw [he] at hm ⊢
    omega
  rw [hdiv,hrew] at h
  by_cases ht : t=0 <;> simpa [schedule,path,ht,sub_eq_add_neg,add_assoc] using h

noncomputable def curve (P D A : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  if t=0 then clippedRamp P A D x-clippedRamp P (A+D*P : ℕ) 1 x else 0

theorem curve_cover (P D A : ℕ) (hD : 0<D) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 9 (curve P D A t) H := by
  change HasAffineIntervalCover 9 (fun x => curve P D A t x) H
  by_cases ht : t=0
  · simp only [curve,ite_eq_left ht]
    exact (clippedRamp_cover hH (by positivity) (by positivity) (by exact_mod_cast hD)).sub
      (clippedRamp_cover hH (by positivity) (by positivity) (by norm_num : (0 : ℝ)<1))
  · simp only [curve,ite_eq_right ht]
    exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

theorem path_curve_error (P D A : ℕ) (t : Fin 2) (x : ℝ) :
    |(path P D t (⌊x⌋₊-A) : ℝ)-curve P D A t x| ≤ 2 := by
  have ha := clippedRamp_sample_error P A D x
  have hb := clippedRamp_sample_error P (A+D*P) 1 x
  simp only [Nat.div_one,Nat.cast_one] at hb
  by_cases ht : t=0
  · simp only [path,curve,ite_eq_left ht,Int.cast_sub,Int.cast_natCast,Nat.sub_sub]
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith
  · simp [path,curve,ht]

theorem schedule_curve_error (r D A : ℕ) (hc : U.cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t : ℝ)-
      c.work.pos t-curve (r*W) D A t x| ≤ (D+1)*W+2 := by
  have h := schedule_path_error U r D hc hD hW w c
    (min (⌊x⌋₊-A) (ticks U r)) (Nat.min_le_right _ _) t
  rw [linear_ticks U r D hc,path_frozen _ _ hD] at h
  have hr : |((trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t : ℝ)-
      c.work.pos t-(path (r*W) D t (⌊x⌋₊-A) : ℝ)| ≤ (D+1)*W := by
    have hh : ((|(trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t-
        c.work.pos t-path (r*W) D t (⌊x⌋₊-A)| : ℤ) : ℝ) ≤ (D+1)*W := by
      rw [linear_ticks U r D hc]
      exact_mod_cast h
    simpa only [Int.cast_abs,Int.cast_sub] using hh
  have ha := path_curve_error (r*W) D A t x
  rw [abs_le] at hr ha ⊢
  constructor <;> linarith

end TransposeFollowup.ScheduledBankRows

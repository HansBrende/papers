import TransposeFollowup.IndexedBankRows
import TransposeFollowup.ScheduledBankRowsMotion

/-! Indexed equal-duration row blocks use the generalized word-block
estimate. Curves, covers and rounding are shared with constant rows. -/
namespace TransposeFollowup.IndexedBankRows
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction AffineMotion
open ScheduledBankRows (Update stepSchedule step_exact step_position)
set_option autoImplicit false
variable {M : Type*} {W : ℕ} (U : ℕ → Update M W)

theorem linear_ticks (r D : ℕ) (hc : ∀ k, (U k).cost+W=D*W) : ticks U r=(D+1)*(r*W) := by
  rw [ticks,rowsTicks_eq U r (D*W) hc]
  ring

theorem rows_path_error (r D : ℕ) (hc : ∀ k, (U k).cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (m : ℕ) (hm : m ≤ rowsTicks U r) (t : Fin 2) :
    |(trajectory (rowsSchedule U r) w c m).work.pos t-c.work.pos t-
      (if t=0 then ((m/D : ℕ) : ℤ) else 0)| ≤ (D+1)*W := by
  have hf : (fun k => (U k).cost+W)=(fun _ => D*W) := funext hc
  have h := word_block_error (fun k => stepSchedule (U k)) (action 0 ⟨none,.stay⟩)
    (D*W) (Nat.mul_pos hD hW) w t (if t=0 then (W : ℤ) else 0)
    (fun k d => by
      rw [← hc k,step_exact,step_position]
      by_cases ht : t=0 <;> simp [ht]) (List.range r) c m
    (by simpa only [List.length_range,rowsTicks_eq U r (D*W) hc] using hm)
  rw [← hf] at h
  change |(trajectory (rowsSchedule U r) w c m).work.pos t-c.work.pos t-
    (m/(D*W) : ℕ)*(if t=0 then (W : ℤ) else 0)| ≤ (D*W : ℕ) at h
  have he : (m/(D*W))*W+(m/D)%W=m/D := by
    simpa only [Nat.div_div_eq_div_mul] using Nat.div_add_mod' (m/D) W
  have hez : ((m/(D*W) : ℕ) : ℤ)*W+((m/D)%W : ℕ)=(m/D : ℕ) := by exact_mod_cast he
  have hr : (((m/D)%W : ℕ) : ℤ)<W := by exact_mod_cast Nat.mod_lt (m/D) hW
  have hz : (0 : ℤ) ≤ ((m/D)%W : ℕ) := Nat.cast_nonneg _
  rw [abs_le] at h
  rw [abs_le]
  by_cases ht : t=0 <;> simp only [ht,ite_true,ite_false,mul_zero,Nat.cast_mul] at h ⊢
  · constructor <;> nlinarith
  · constructor <;> nlinarith [Nat.cast_nonneg (α:=ℤ) W]

theorem schedule_path_error (r D : ℕ) (hc : ∀ k, (U k).cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (m : ℕ) (hm : m ≤ ticks U r) (t : Fin 2) :
    |(trajectory (schedule U r) w c m).work.pos t-c.work.pos t-ScheduledBankRows.path (r*W) D t m| ≤ (D+1)*W := by
  have h := append_position_error (rowsSchedule U r) (fun _ => action 0 ⟨none,.left⟩)
    (rowsTicks U r) (r*W) w t (fun j => if t=0 then ((j/D : ℕ) : ℤ) else 0)
    (fun j => -(if t=0 then (j : ℤ) else 0)) ((D+1)*W) 0 le_rfl (by simp)
    (fun d j hj => rows_path_error U r D hc hD hW w d j hj t)
    (fun d j _ => by
      change |(rewind 0 w d j).work.pos t-d.work.pos t-_| ≤ 0
      rw [rewind_position]
      by_cases ht : t=0 <;> simp [ht]) c m hm
  have he : rowsTicks U r=D*(r*W) := by rw [rowsTicks_eq U r (D*W) hc]; ring
  have hdiv : min m (rowsTicks U r)/D=min (m/D) (r*W) := by
    rw [he]
    have hh : Monotone (fun k : ℕ => k/D) := fun _ _ h => Nat.div_le_div_right h
    rw [hh.map_min,Nat.mul_div_cancel_left _ hD]
  have hrew : m-rowsTicks U r=min (m-D*(r*W)) (r*W) := by
    unfold ticks at hm
    rw [he] at hm ⊢
    omega
  rw [hdiv,hrew] at h
  by_cases ht : t=0 <;> simpa [schedule,ScheduledBankRows.path,ht,sub_eq_add_neg,add_assoc] using h

theorem schedule_curve_error (r D A : ℕ) (hc : ∀ k, (U k).cost+W=D*W) (hD : 0<D) (hW : 0<W)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t : ℝ)-
      c.work.pos t-ScheduledBankRows.curve (r*W) D A t x| ≤ (D+1)*W+2 := by
  have h := schedule_path_error U r D hc hD hW w c
    (min (⌊x⌋₊-A) (ticks U r)) (Nat.min_le_right _ _) t
  rw [linear_ticks U r D hc,ScheduledBankRows.path_frozen _ _ hD] at h
  have hr : |((trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t : ℝ)-
      c.work.pos t-(ScheduledBankRows.path (r*W) D t (⌊x⌋₊-A) : ℝ)| ≤ (D+1)*W := by
    have hh : ((|(trajectory (schedule U r) w c (min (⌊x⌋₊-A) (ticks U r))).work.pos t-
        c.work.pos t-ScheduledBankRows.path (r*W) D t (⌊x⌋₊-A)| : ℤ) : ℝ) ≤ (D+1)*W := by
      rw [linear_ticks U r D hc]
      exact_mod_cast h
    simpa only [Int.cast_abs,Int.cast_sub] using hh
  have ha := ScheduledBankRows.path_curve_error (r*W) D A t x
  rw [abs_le] at hr ha ⊢
  constructor <;> linarith

end TransposeFollowup.IndexedBankRows

import TransposeFollowup.ScheduledWord
import TransposeFollowup.ClippedAffineRamps

/-! Approximate motion composes directly along the paid word schedule.
The suffix starts in the actual prefix state. No exact, input-independent
head path is assumed, including at intermediate stage boundaries. -/
namespace TransposeFollowup.ScheduledWord
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false
variable {O T M : Type*}

noncomputable def approximation (cost : O → ℕ) (q : O → ℕ → T → ℝ → ℝ) :
    List O → ℕ → T → ℝ → ℝ
  | [],_,_,_ => 0
  | op::ops,A,t,x => q op A t x+approximation cost q ops (A+cost op) t x

theorem approximation_cover (cost : O → ℕ) (q : O → ℕ → T → ℝ → ℝ)
    (ops : List O) {J : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (hq : ∀ op ∈ ops, ∀ A t, HasAffineIntervalCover J (q op A t) H)
    (A : ℕ) (t : T) :
    HasAffineIntervalCover (J^ops.length) (approximation cost q ops A t) H := by
  induction ops generalizing A with
  | nil => exact HasAffineIntervalCover.const hH 0
  | cons op ops ih =>
    have h := (hq op List.mem_cons_self A t).add
      (ih (fun a ha => hq a (List.mem_cons_of_mem _ ha)) (A+cost op))
    simpa only [List.length_cons,pow_succ',approximation] using h

theorem approximation_error (cost : O → ℕ) (code : O → ℕ → NativeIO.Program T M)
    (idle : NativeIO.Program T M) (q : O → ℕ → T → ℝ → ℝ)
    (ops : List O) (E : ℝ) (w : List Bool)
    (hq : ∀ op ∈ ops, ∀ A c x t,
      |((trajectory (code op) w c (min (⌊x⌋₊-A) (cost op))).work.pos t : ℝ)-
        c.work.pos t-q op A t x| ≤ E)
    (A : ℕ) (c : NativeIO.Config T M) (x : ℝ) (t : T) :
    |((trajectory (schedule cost code idle ops) w c (min (⌊x⌋₊-A) (ticks cost ops))).work.pos t : ℝ)-
      c.work.pos t-approximation cost q ops A t x| ≤ E*ops.length := by
  induction ops generalizing A c with
  | nil => simp [ticks,trajectory,approximation]
  | cons op ops ih =>
    have hs := hq op List.mem_cons_self A c x t
    have hrest := fun a ha => hq a (List.mem_cons_of_mem _ ha)
    simp only [schedule,ticks,List.map_cons,List.sum_cons,approximation,List.length_cons,Nat.cast_add,Nat.cast_one]
    change |((trajectory (append (code op) (schedule cost code idle ops) (cost op)) w c
      (min (⌊x⌋₊-A) (cost op+ticks cost ops))).work.pos t : ℝ)-c.work.pos t-
      (q op A t x+approximation cost q ops (A+cost op) t x)| ≤ E*((ops.length : ℝ)+1)
    by_cases hn : ⌊x⌋₊-A ≤ cost op
    · have hm : min (⌊x⌋₊-A) (cost op+ticks cost ops)=⌊x⌋₊-A := by omega
      have hz : ⌊x⌋₊-(A+cost op)=0 := by omega
      have ht := ih hrest (A+cost op) c
      rw [hz,Nat.zero_min,trajectory] at ht
      rw [hm,append_prefix _ _ _ _ _ _ hn]
      rw [Nat.min_eq_left hn] at hs
      rw [abs_le] at hs ht ⊢
      constructor <;> linarith
    · have hm : min (⌊x⌋₊-A) (cost op+ticks cost ops)=
          cost op+min (⌊x⌋₊-(A+cost op)) (ticks cost ops) := by omega
      have ht := ih hrest (A+cost op) (trajectory (code op) w c (cost op))
      rw [hm,append_exact]
      rw [Nat.min_eq_right (by omega : cost op ≤ ⌊x⌋₊-A)] at hs
      rw [abs_le] at hs ht ⊢
      constructor <;> linarith

end TransposeFollowup.ScheduledWord

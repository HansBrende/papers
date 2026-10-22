import TransposeFollowup.ScheduledNativeIO

/-! Concatenate public schedules before native compilation. There is no
unpaid linking transition: the global clock already selects each step. -/
namespace TransposeFollowup.ScheduledNativeIO
set_option autoImplicit false
variable {T M : Type*}

def append (σ τ : ℕ → NativeIO.Program T M) (N : ℕ) (i : ℕ) : NativeIO.Program T M :=
  if i < N then σ i else τ (i-N)

theorem append_prefix (σ τ : ℕ → NativeIO.Program T M) (N : ℕ) (w : List Bool)
    (c : NativeIO.Config T M) (n : ℕ) (hn : n ≤ N) :
    trajectory (append σ τ N) w c n=trajectory σ w c n := by
  apply trajectory_congr
  intro i hi
  simp only [append,ite_eq_left (show i<N by omega)]

theorem append_exact (σ τ : ℕ → NativeIO.Program T M) (N n : ℕ) (w : List Bool)
    (c : NativeIO.Config T M) :
    trajectory (append σ τ N) w c (N+n)=trajectory τ w (trajectory σ w c N) n := by
  rw [trajectory_add,append_prefix _ _ _ _ _ _ le_rfl]
  apply trajectory_congr
  intro i _
  simp only [append,ite_eq_right (show ¬N+i<N by omega),Nat.add_sub_cancel_left]

theorem append_active (σ τ : ℕ → NativeIO.Program T M) (N i : ℕ) (c : NativeIO.Config T M)
    (hσ : ∀ j, NativeIO.Active (σ j) c) (hτ : ∀ j, NativeIO.Active (τ j) c) :
    NativeIO.Active (append σ τ N i) c := by
  unfold append
  split_ifs
  · exact hσ _
  · exact hτ _

end TransposeFollowup.ScheduledNativeIO

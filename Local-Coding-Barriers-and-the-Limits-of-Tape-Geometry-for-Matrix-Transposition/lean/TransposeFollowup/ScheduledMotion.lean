import TransposeFollowup.ScheduledSegments

/-! Additive head displacements through paid schedule concatenation.
The proof uses the existing exact trajectory append identities. -/
namespace TransposeFollowup.ScheduledNativeIO
set_option autoImplicit false
variable {T M : Type*}

theorem append_position (σ τ : ℕ → NativeIO.Program T M) (N L : ℕ)
    (w : List Bool) (t : T) (f g : ℕ → ℤ)
    (hσ : ∀ c n, n ≤ N → (trajectory σ w c n).work.pos t=c.work.pos t+f n)
    (hτ : ∀ c n, n ≤ L → (trajectory τ w c n).work.pos t=c.work.pos t+g n)
    (c : NativeIO.Config T M) (n : ℕ) (hn : n ≤ N+L) :
    (trajectory (append σ τ N) w c n).work.pos t=c.work.pos t+(f (min n N)+g (n-N)) := by
  by_cases h : n ≤ N
  · have hz : g 0=0 := by have hh := hτ c 0 (Nat.zero_le _); change c.work.pos t=c.work.pos t+g 0 at hh; omega
    rw [append_prefix _ _ _ _ _ _ h,hσ c n h,Nat.min_eq_left h,Nat.sub_eq_zero_of_le h,hz,add_zero]
  · have hm : n-N ≤ L := by omega
    conv_lhs => rw [show n=N+(n-N) by omega,append_exact]
    rw [hτ _ _ hm,hσ c N le_rfl,Nat.min_eq_right (by omega),add_assoc]

end TransposeFollowup.ScheduledNativeIO

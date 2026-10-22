import TransposeFollowup.ScheduledMotion

/-! Bounded head-path errors compose under the same paid append used for
exact motion. The bounds hold from every initial configuration, so the
suffix may start in a data-dependent state. -/
namespace TransposeFollowup.ScheduledNativeIO
set_option autoImplicit false
variable {T M : Type*}

theorem append_position_error (σ τ : ℕ → NativeIO.Program T M) (N L : ℕ)
    (w : List Bool) (t : T) (f g : ℕ → ℤ) (E F : ℤ) (hF : 0≤F) (hg : g 0=0)
    (hσ : ∀ c n, n≤N → |(trajectory σ w c n).work.pos t-c.work.pos t-f n|≤E)
    (hτ : ∀ c n, n≤L → |(trajectory τ w c n).work.pos t-c.work.pos t-g n|≤F)
    (c : NativeIO.Config T M) (n : ℕ) (hn : n≤N+L) :
    |(trajectory (append σ τ N) w c n).work.pos t-c.work.pos t-
      (f (min n N)+g (n-N))|≤E+F := by
  by_cases h : n≤N
  · rw [append_prefix _ _ _ _ _ _ h,Nat.min_eq_left h,Nat.sub_eq_zero_of_le h,hg,add_zero]
    exact (hσ c n h).trans (by omega)
  · conv_lhs => rw [show n=N+(n-N) by omega,append_exact]
    have ha := hσ c N le_rfl
    have hb := hτ (trajectory σ w c N) (n-N) (by omega)
    have he : min (N+(n-N)) N=N := by omega
    have hf : N+(n-N)-N=n-N := by omega
    rw [he,hf,abs_le]
    rw [abs_le] at ha hb
    constructor <;> omega

end TransposeFollowup.ScheduledNativeIO

import TransposeFollowup.SequentialFiveRun

namespace TransposeFollowup.SequentialFive
set_option autoImplicit false

theorem successful_time_le_halting (M : Transpose.TM) (w : List Bool) (a b : ℕ)
    (ca cb : Transpose.Config M)
    (ha : Transpose.stepN M w a (Transpose.init M)=some ca) (hh : Transpose.step M w ca=none)
    (hb : Transpose.stepN M w b (Transpose.init M)=some cb) : b ≤ a := by
  by_contra h
  have hn : b-a≠0 := by omega
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero hn
  rw [show b=a+(m+1) by omega,stepN_add,ha,Option.bind_some,Transpose.stepN,hh] at hb
  contradiction

end TransposeFollowup.SequentialFive

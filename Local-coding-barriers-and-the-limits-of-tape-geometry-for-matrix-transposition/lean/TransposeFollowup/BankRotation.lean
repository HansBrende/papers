import TransposeFollowup.BankReversal
import TransposeFollowup.ScheduledAdvance

/-! A left rotation of a raw bank: reverse the whole bank, reverse its
first P-R cells, seek to the remaining R cells and reverse them, then
rewind. Every seek, copy and reset is part of the paid schedule. -/
namespace TransposeFollowup.BankRotation
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

def value (P R : ℕ) (x : ℕ → Bool) (j : ℕ) : Bool := x ((j+R)%P)

theorem value_congr {P : ℕ} (hP : 0<P) (R : ℕ) (x y : ℕ → Bool)
    (hxy : ∀ j<P, x j=y j) (j : ℕ) : value P R x j=value P R y j :=
  hxy ((j+R)%P) (Nat.mod_lt _ hP)

def prepared (P R : ℕ) (w : List Bool) (c : State) : State :=
  advance 0 w (BankReversal.result (P-R) w (BankReversal.result P w c)) (P-R)

def result (P R : ℕ) (w : List Bool) (c : State) : State :=
  rewind 0 w (BankReversal.result R w (prepared P R w c)) (P-R)

def ticks (P R : ℕ) : ℕ := BankReversal.ticks P+
  (BankReversal.ticks (P-R)+((P-R)+(BankReversal.ticks R+(P-R))))

def schedule (P R : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (BankReversal.schedule P)
    (append (BankReversal.schedule (P-R))
      (append (fun _ => action 0 ⟨none,.right⟩)
        (append (BankReversal.schedule R) (fun _ => action 0 ⟨none,.left⟩) (BankReversal.ticks R))
        (P-R)) (BankReversal.ticks (P-R))) (BankReversal.ticks P)

theorem schedule_active (P R i : ℕ) (c : State) : NativeIO.Active (schedule P R i) c := by
  unfold schedule
  apply append_active
  · intro j; exact BankReversal.schedule_active _ j c
  · intro _
    apply append_active
    · intro j; exact BankReversal.schedule_active _ j c
    · intro _
      apply append_active
      · intro _; exact ScheduledTapeAction.active _ _ _
      · intro _
        apply append_active
        · intro j; exact BankReversal.schedule_active _ j c
        · intro _; exact ScheduledTapeAction.active _ _ _

theorem schedule_exact (P R : ℕ) (w : List Bool) (c : State) :
    trajectory (schedule P R) w c (ticks P R)=result P R w c := by
  simp only [schedule,ticks,append_exact,BankReversal.schedule_exact]
  rfl

theorem ticks_eq (P R : ℕ) (hR : R≤P) : ticks P R=14*P-2*R+6 := by
  simp only [ticks,BankReversal.ticks_eq]
  omega

theorem ticks_le {P : ℕ} (hP : 0<P) (R : ℕ) (hR : R≤P) : ticks P R≤20*P := by
  rw [ticks_eq P R hR]
  omega

theorem result_spec (P R : ℕ) (hR : R≤P) (w : List Bool) (c : State)
    (hblank : ∀ z, cells c 1 z=.blank) :
    (∀ t, (result P R w c).work.pos t=c.work.pos t) ∧
    (∀ j<P, cells (result P R w c) 0 (c.work.pos 0+j)=
      .data (value P R (fun k => bit (cells c 0 (c.work.pos 0+k))) j)) ∧
    (∀ z, cells (result P R w c) 1 z=.blank) ∧
    (result P R w c).inputPos=c.inputPos ∧ (result P R w c).outRev=c.outRev := by
  have ha := BankReversal.result_spec P w c hblank
  have hb := BankReversal.result_spec (P-R) w (BankReversal.result P w c) ha.2.2.1
  have hpos (t : Fin 2) : (prepared P R w c).work.pos t=c.work.pos t+if t=0 then (P-R : ℕ) else 0 := by
    simp only [prepared,advance_position,hb.1 t,ha.1 t]
  have hcells (t : Fin 2) (z : ℤ) : cells (prepared P R w c) t z=
      cells (BankReversal.result (P-R) w (BankReversal.result P w c)) t z := by
    exact advance_cells 0 w _ (P-R) t z
  have hz : ∀ z, cells (prepared P R w c) 1 z=.blank := fun z => (hcells 1 z).trans (hb.2.2.1 z)
  have hc := BankReversal.result_spec R w (prepared P R w c) hz
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    simp only [result,rewind_position,hc.1 t,hpos t,add_sub_cancel_right]
  · intro j hj
    rw [result,rewind_cells]
    by_cases hjL : j<P-R
    · rw [BankReversal.result_bank_outside R w (prepared P R w c) (c.work.pos 0+j)
        (Or.inl (by rw [hpos 0]; simp only [ite_true]; omega)),hcells]
      have h := hb.2.1 j hjL
      rw [ha.1 0] at h
      rw [h,ha.2.1 (P-R-1-j) (by omega)]
      have he : P-1-(P-R-1-j)=j+R := by omega
      rw [he]
      simp only [value,Nat.mod_eq_of_lt (by omega : j+R<P),bit]
    · have hk : j-(P-R)<R := by omega
      have h := hc.2.1 (j-(P-R)) hk
      have he : (prepared P R w c).work.pos 0+(j-(P-R) : ℕ)=c.work.pos 0+j := by
        rw [hpos 0]; simp only [ite_true]; omega
      rw [he] at h
      rw [h,hcells]
      let m := (P-R)+(R-1-(j-(P-R)))
      have hm : m<P := by dsimp [m]; omega
      have he' : (prepared P R w c).work.pos 0+(R-1-(j-(P-R)) : ℕ)=c.work.pos 0+m := by
        rw [hpos 0]; simp only [ite_true]; dsimp [m]; omega
      rw [he',BankReversal.result_bank_outside (P-R) w (BankReversal.result P w c) (c.work.pos 0+m)
        (Or.inr (by rw [ha.1 0]; dsimp [m]; omega)),ha.2.1 m hm]
      have href : P-1-m=j-(P-R) := by dsimp [m]; omega
      have hmod : (j+R)%P=j-(P-R) := by
        rw [Nat.mod_eq_sub_mod (by omega : P≤j+R),Nat.mod_eq_of_lt (by omega : j+R-P<P)]
        omega
      simp only [value,href,hmod,bit]
  · intro z
    exact (rewind_cells 0 w (BankReversal.result R w (prepared P R w c)) (P-R) 1 z).trans (hc.2.2.1 z)
  · have hd := advance_io 0 w (BankReversal.result (P-R) w (BankReversal.result P w c)) (P-R)
    have he := rewind_io 0 w (BankReversal.result R w (prepared P R w c)) (P-R)
    exact ⟨he.1.trans (hc.2.2.2.1.trans (hd.1.trans (hb.2.2.2.1.trans ha.2.2.2.1))),
      he.2.trans (hc.2.2.2.2.trans (hd.2.trans (hb.2.2.2.2.trans ha.2.2.2.2)))⟩

theorem result_bank_outside (P R : ℕ) (hR : R≤P) (w : List Bool) (c : State)
    (hblank : ∀ z, cells c 1 z=.blank) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+P≤z) :
    cells (result P R w c) 0 z=cells c 0 z := by
  have ha := BankReversal.result_spec P w c hblank
  have hb := BankReversal.result_spec (P-R) w (BankReversal.result P w c) ha.2.2.1
  have hpos : (prepared P R w c).work.pos 0=c.work.pos 0+(P-R : ℕ) := by
    simp only [prepared,advance_position,ite_true,hb.1 0,ha.1 0]
  have hlast : z<(prepared P R w c).work.pos 0 ∨ (prepared P R w c).work.pos 0+R≤z := by
    rw [hpos]; omega
  have hfirst : z<(BankReversal.result P w c).work.pos 0 ∨
      (BankReversal.result P w c).work.pos 0+(P-R : ℕ)≤z := by
    rw [ha.1 0]; omega
  rw [result,rewind_cells,BankReversal.result_bank_outside R w (prepared P R w c) z hlast,
    prepared,advance_cells,BankReversal.result_bank_outside (P-R) w (BankReversal.result P w c) z hfirst,
    BankReversal.result_bank_outside P w c z hz]

end TransposeFollowup.BankRotation

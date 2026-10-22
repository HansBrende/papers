import TransposeFollowup.RawBlockReversal
import TransposeFollowup.ScheduledBankRows

/-! Exact-symbol left rotation on the shared controller. Three existing
block reversals (block width one), two paid seeks and stationary padding
give a fixed 22P-step row update. This preserves trits as well as bits. -/
namespace TransposeFollowup.BankSymbolRotation
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
open SharedBankSymbols
set_option autoImplicit false

def reverse (P : ℕ) (w : List Bool) (c : SharedRowBank.State) : SharedRowBank.State :=
  BankBlockReversal.result read write reset 1 P w c

theorem reverse_exact (P : ℕ) (w : List Bool) (c : SharedRowBank.State) :
    trajectory (RawBlockReversal.schedule 1 P) w c (10*P)=reverse P w c := by
  have h := BankBlockReversal.schedule_exact read write reset 1 P w c
  simpa only [BankBlockReversal.ticks_eq,mul_one,reverse,RawBlockReversal.schedule] using h

theorem reverse_position (P : ℕ) (w : List Bool) (c : SharedRowBank.State) (t : Fin 2) :
    (reverse P w c).work.pos t=c.work.pos t := BankBlockReversal.result_positions _ _ _ _ _ _ _ _

theorem reverse_spec (P : ℕ) (w : List Bool) (c : SharedRowBank.State) (hc : BankWord.symbols.clean c) :
    (∀ j < P, cells (reverse P w c) 0 (c.work.pos 0+j)=cells c 0 (c.work.pos 0+(P-1-j : ℕ))) ∧
    BankWord.symbols.clean (reverse P w c) ∧
    (reverse P w c).inputPos=c.inputPos ∧ (reverse P w c).outRev=c.outRev := by
  have h := BankBlockReversal.represents read write reset write_read 1 P w c hc
  refine ⟨?_,h.2.2⟩
  intro j hj
  simpa only [mul_one,BankWord.symbols,BankWord.input,BankBlockReversal.value,
    BankBlockReversal.index,Nat.div_one,Nat.mod_one,add_zero,id_eq,reverse] using h.2.1 j (by simpa using hj)

theorem reverse_frame (P : ℕ) (w : List Bool) (c : SharedRowBank.State) (z : ℤ)
    (hz : z < c.work.pos 0 ∨ c.work.pos 0+P ≤ z) :
    cells (reverse P w c) 0 z=cells c 0 z :=
  BankBlockReversal.result_bank_outside read write reset 1 P w c z (by simpa using hz)

def prepared (P R : ℕ) (w : List Bool) (c : SharedRowBank.State) : SharedRowBank.State :=
  advance 0 w (reverse (P-R) w (reverse P w c)) (P-R)

def result (P R : ℕ) (w : List Bool) (c : SharedRowBank.State) : SharedRowBank.State :=
  rewind 0 w (reverse R w (prepared P R w c)) (P-R)

def baseTicks (P R : ℕ) : ℕ := 10*P+(10*(P-R)+((P-R)+(10*R+(P-R))))

def baseSchedule (P R : ℕ) : ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  append (RawBlockReversal.schedule 1 P)
    (append (RawBlockReversal.schedule 1 (P-R))
      (append (fun _ => action 0 ⟨none,.right⟩)
        (append (RawBlockReversal.schedule 1 R) (fun _ => action 0 ⟨none,.left⟩) (10*R))
        (P-R)) (10*(P-R))) (10*P)

def idle : NativeIO.Program (Fin 2) SharedRowBank.Mode := fun m => .work (.jump m)

theorem idle_exact (w : List Bool) (c : SharedRowBank.State) (n : ℕ) :
    trajectory (fun _ => idle) w c n=c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory,ih]; rfl

def ticks (P R : ℕ) : ℕ := baseTicks P R+2*R

def schedule (P R : ℕ) : ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  append (baseSchedule P R) (fun _ => idle) (baseTicks P R)

theorem schedule_exact (P R : ℕ) (w : List Bool) (c : SharedRowBank.State) :
    trajectory (schedule P R) w c (ticks P R)=result P R w c := by
  simp only [schedule,ticks,append_exact,idle_exact,baseSchedule,baseTicks,reverse_exact]
  rfl

theorem schedule_active (P R i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule P R i) c := by
  unfold schedule
  apply append_active
  · intro j
    unfold baseSchedule
    apply append_active
    · intro k; exact RawBlockReversal.schedule_active _ _ k c
    · intro k
      apply append_active
      · intro l; exact RawBlockReversal.schedule_active _ _ l c
      · intro l
        apply append_active
        · intro _; exact active _ _ _
        · intro m
          apply append_active
          · intro q; exact RawBlockReversal.schedule_active _ _ q c
          · intro _; exact active _ _ _
  · intro _; simp [idle,NativeIO.Active]

theorem ticks_eq (P R : ℕ) (hR : R ≤ P) : ticks P R=22*P := by
  unfold ticks baseTicks
  omega

theorem result_position (P R : ℕ) (w : List Bool) (c : SharedRowBank.State) (t : Fin 2) :
    (result P R w c).work.pos t=c.work.pos t := by
  simp only [result,prepared,rewind_position,reverse_position,advance_position,add_sub_cancel_right]

def value (P R : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool := x ((j+R)%P)

theorem value_congr (P R : ℕ) : BankWord.Congruent P (value P R) := by
  intro x y hxy j hj
  exact hxy _ (Nat.mod_lt _ (Nat.zero_lt_of_lt hj))

theorem represents (P R : ℕ) (hR : R ≤ P) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c (result P R w c)
      (value P R (BankWord.input BankWord.symbols c)) := by
  have ha := reverse_spec P w c hc
  have hb := reverse_spec (P-R) w (reverse P w c) ha.2.1
  have hp (t : Fin 2) : (prepared P R w c).work.pos t=c.work.pos t+if t=0 then (P-R : ℕ) else 0 := by
    simp only [prepared,advance_position,reverse_position]
  have hcells (t : Fin 2) (z : ℤ) : cells (prepared P R w c) t z=
      cells (reverse (P-R) w (reverse P w c)) t z := advance_cells 0 w _ (P-R) t z
  have hz : BankWord.symbols.clean (prepared P R w c) := by
    intro z
    exact (advance_cells 0 w _ (P-R) 1 z).trans (hb.2.1 z)
  have hd := reverse_spec R w (prepared P R w c) hz
  refine ⟨result_position P R w c,?_,?_,?_⟩
  · intro j hj
    change cells (result P R w c) 0 (c.work.pos 0+j)=cells c 0 (c.work.pos 0+((j+R)%P : ℕ))
    rw [result,rewind_cells]
    by_cases hjL : j < P-R
    · rw [reverse_frame R w (prepared P R w c) _ (Or.inl (by rw [hp 0]; simp only [ite_true]; omega)),
        hcells]
      have h := hb.1 j hjL
      rw [reverse_position] at h
      rw [h,ha.1 (P-R-1-j) (by omega)]
      have he : P-1-(P-R-1-j)=j+R := by omega
      rw [he,Nat.mod_eq_of_lt (by omega : j+R < P)]
    · have hk : j-(P-R) < R := by omega
      have h := hd.1 (j-(P-R)) hk
      have he : (prepared P R w c).work.pos 0+(j-(P-R) : ℕ)=c.work.pos 0+j := by
        rw [hp 0]; simp only [ite_true]; omega
      rw [he] at h
      rw [h,hcells]
      let m := (P-R)+(R-1-(j-(P-R)))
      have hm : m < P := by dsimp [m]; omega
      have he' : (prepared P R w c).work.pos 0+(R-1-(j-(P-R)) : ℕ)=c.work.pos 0+m := by
        rw [hp 0]; simp only [ite_true]; dsimp [m]; omega
      rw [he',reverse_frame (P-R) w (reverse P w c) _ (Or.inr (by
        rw [reverse_position]; dsimp [m]; omega)),ha.1 m hm]
      have href : P-1-m=j-(P-R) := by dsimp [m]; omega
      have hmod : (j+R)%P=j-(P-R) := by
        rw [Nat.mod_eq_sub_mod (by omega : P ≤ j+R),Nat.mod_eq_of_lt (by omega : j+R-P < P)]
        omega
      rw [href,hmod]
  · intro z
    exact (rewind_cells 0 w _ (P-R) 1 z).trans (hd.2.1 z)
  · have hi := advance_io 0 w (reverse (P-R) w (reverse P w c)) (P-R)
    have hr := rewind_io 0 w (reverse R w (prepared P R w c)) (P-R)
    exact ⟨hr.1.trans (hd.2.2.1.trans (hi.1.trans (hb.2.2.1.trans ha.2.2.1))),
      hr.2.trans (hd.2.2.2.trans (hi.2.trans (hb.2.2.2.trans ha.2.2.2)))⟩

theorem result_frame (P R : ℕ) (hR : R ≤ P) (w : List Bool) (c : SharedRowBank.State) (z : ℤ)
    (hz : z < c.work.pos 0 ∨ c.work.pos 0+P ≤ z) :
    cells (result P R w c) 0 z=cells c 0 z := by
  have hp : (prepared P R w c).work.pos 0=c.work.pos 0+(P-R : ℕ) := by
    simp only [prepared,advance_position,ite_true,reverse_position]
  rw [result,rewind_cells,reverse_frame R w (prepared P R w c) z (by rw [hp]; omega),
    prepared,advance_cells,reverse_frame (P-R) w (reverse P w c) z (by rw [reverse_position]; omega),
    reverse_frame P w c z hz]

def update (P R : ℕ) (hR : R ≤ P) : ScheduledBankRows.Update SharedRowBank.Mode P where
  cost := ticks P R
  code := schedule P R
  value := value P R
  congruent := value_congr P R
  active := schedule_active P R
  endpoint := by intro w c t; rw [schedule_exact]; exact result_position P R w c t
  represents := by intro w c hc; rw [schedule_exact]; exact represents P R hR w c hc
  frame := by intro w c z hz; rw [schedule_exact]; exact result_frame P R hR w c z hz

end TransposeFollowup.BankSymbolRotation

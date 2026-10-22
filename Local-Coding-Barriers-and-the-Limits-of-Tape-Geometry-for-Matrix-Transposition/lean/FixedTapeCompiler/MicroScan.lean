import FixedTapeCompiler.MicroCopy

/-! Repeated read/action scans of zero symbols. The target action is fixed
finite control and is executed once per scanned cell, never as a free
iteration. These lemmas also cover a source-only walk by an idle action. -/
namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

def idle : Action := ⟨none,.stay⟩
def emitZero : Action := ⟨some (.data false),.right⟩

def emitBit (bit : Bool) : Action := ⟨some (.data bit),.right⟩

theorem at2_single_source (p : Program T L) (pc next : L) (s t : T) (hs : s ≠ t)
    (a : Action) (hp : p pc = .act (single s a) next)
    (x y : Tape Bool) (bank : T → Tape Bool) :
    step p (focus2 pc s t x y bank) = focus2 next s t (a.apply x) y bank := by
  rw [focus2_swap _ _ _ hs,at_act _ _ _ _ _ hp,focus2_swap _ _ _ hs]

@[simp] theorem idle_apply (t : Tape Bool) : idle.apply t = t := rfl

theorem twins_idle (s t : T) (hs : s ≠ t) (a : Action) :
    twins s t a idle = single s a := by
  funext i
  by_cases ht : i=t
  · subst i; simp [twins,single,Ne.symm hs,idle]
  · simp [twins,single,ht]

theorem iterate_idle (n : ℕ) (word : Tape Bool) : (idle.apply^[n]) word = word := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply,idle_apply] using ih

theorem iterate_emit (n : ℕ) (pre : List (Sym Bool)) :
    (emitZero.apply^[n]) (⟨pre,[]⟩ : Tape Bool) =
      ⟨List.replicate n (.data false)++pre,[]⟩ := by
  induction n generalizing pre with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (emitZero.apply^[n]) (⟨.data false::pre,[]⟩ : Tape Bool) = _
    rw [ih]
    simp [List.replicate_succ',List.append_assoc]

theorem iterate_emit_bit (bit : Bool) (n : ℕ) (pre : List (Sym Bool)) :
    ((emitBit bit).apply^[n]) (⟨pre,[]⟩ : Tape Bool) =
      ⟨List.replicate n (.data bit)++pre,[]⟩ := by
  induction n generalizing pre with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change ((emitBit bit).apply^[n]) (⟨.data bit::pre,[]⟩ : Tape Bool) = _
    rw [ih]
    simp [List.replicate_succ',List.append_assoc]

theorem scan_right (p : Program T L) (s t : T) (hs : s ≠ t)
    (entry body : L) (next : Sym Bool → L) (a : Action)
    (hr : p entry = .read s next) (hz : next (.data false) = body)
    (ha : p body = .act (twins s t ⟨none,.right⟩ a) entry)
    (n : ℕ) (pre rest : List (Sym Bool)) (out : Tape Bool) (bank : T → Tape Bool) :
    run p (2*n)
      (focus2 entry s t ⟨pre,List.replicate n (.data false)++rest⟩ out bank) =
      focus2 entry s t ⟨List.replicate n (.data false)++pre,rest⟩ ((a.apply^[n]) out) bank := by
  induction n generalizing pre out with
  | zero => simp [OperationalTrace.run]
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega,run_add]
    have hh : run p 2
        (focus2 entry s t ⟨pre,List.replicate (n+1) (.data false)++rest⟩ out bank) =
        focus2 entry s t ⟨.data false::pre,List.replicate n (.data false)++rest⟩ (a.apply out) bank := by
      change step p (step p _) = _
      rw [at2_read_source _ _ _ _ hs _ hr]
      simp only [List.replicate_succ,List.cons_append,Tape.read,List.headD_cons,hz]
      rw [at2_act _ _ _ _ _ hs _ _ ha]
      rfl
    rw [hh,ih]
    simp [Function.iterate_succ_apply,List.replicate_succ',List.append_assoc]

theorem scan_left (p : Program T L) (s t : T) (hs : s ≠ t)
    (entry body : L) (next : Sym Bool → L) (a : Action)
    (hr : p entry = .read s next) (hz : next (.data false) = body)
    (ha : p body = .act (twins s t ⟨none,.left⟩ a) entry)
    (n : ℕ) (pre rest : List (Sym Bool)) (out : Tape Bool) (bank : T → Tape Bool) :
    run p (2*n)
      (focus2 entry s t (⟨List.replicate n (.data false)++pre,rest⟩ : Tape Bool).moveLeft out bank) =
      focus2 entry s t (⟨pre,List.replicate n (.data false)++rest⟩ : Tape Bool).moveLeft
        ((a.apply^[n]) out) bank := by
  induction n generalizing rest out with
  | zero => simp [OperationalTrace.run]
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega,run_add]
    have hh : run p 2
        (focus2 entry s t (⟨List.replicate (n+1) (.data false)++pre,rest⟩ : Tape Bool).moveLeft out bank) =
        focus2 entry s t (⟨List.replicate n (.data false)++pre,.data false::rest⟩ : Tape Bool).moveLeft
          (a.apply out) bank := by
      change step p (step p _) = _
      rw [at2_read_source _ _ _ _ hs _ hr]
      simp only [List.replicate_succ,List.cons_append,Tape.moveLeft,Tape.read,List.headD_cons,hz]
      rw [at2_act _ _ _ _ _ hs _ _ ha]
      rfl
    rw [hh,ih]
    simp [Function.iterate_succ_apply,List.replicate_succ',List.append_assoc]

end FixedTapeCompiler.Microcode

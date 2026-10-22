import TransposeFollowup.CoupledRowCell

/-! Repeated paid cells scan two equal-length unmarked fields from right
 to left. The existing scheduled-word compiler supplies their composition. -/
namespace TransposeFollowup.CoupledRowScan
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false
variable {C : Type}

def evaluate (f : (Mode C) → (Mode C)) : C → List (Sym Bool) → List (Sym Bool) →
    C × List (Sym Bool) × List (Sym Bool)
  | c,a::as,b::bs =>
    let u := f (c,a,b)
    let r := evaluate f u.1 as bs
    (r.1,u.2.1::r.2.1,u.2.2::r.2.2)
  | c,_,_ => (c,[],[])

theorem evaluate_lengths (f : (Mode C) → (Mode C)) (c : C) (xs ys : List (Sym Bool))
    (h : xs.length=ys.length) :
    (evaluate f c xs ys).2.1.length=xs.length ∧
      (evaluate f c xs ys).2.2.length=xs.length := by
  induction xs generalizing c ys with
  | nil => simp [evaluate]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have ht := ih (f (c,a,b)).1 ys (by simpa using h)
      simp only [evaluate,List.length_cons,ht.1,ht.2,and_self]

def run (f : (Mode C) → (Mode C)) (n : ℕ) (c : (State C)) : (State C) := (CoupledRowCell.result f)^[n] c

def idle : NativeIO.Program (Fin 2) (Mode C) := fun m => .work (.jump m)

theorem idle_exact (w : List Bool) (c : (State C)) (n : ℕ) :
    trajectory (fun _ => idle) w c n=c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory,ih]; rfl

def schedule (f : (Mode C) → (Mode C)) (n : ℕ) : ℕ → NativeIO.Program (Fin 2) (Mode C) :=
  ScheduledWord.schedule (fun _ : Unit => 4) (fun _ => CoupledRowCell.schedule f) idle
    (List.replicate n ())

theorem schedule_active (f : (Mode C) → (Mode C)) (n i : ℕ) (c : (State C)) :
    NativeIO.Active (schedule f n i) c := by
  apply ScheduledWord.schedule_active
  · simp [idle,NativeIO.Active]
  · intro _ _ j
    exact CoupledRowCell.cell_active f j c

theorem schedule_exact (f : (Mode C) → (Mode C)) (n : ℕ) (w : List Bool) (c : (State C)) :
    trajectory (schedule f n) w c (4*n)=run f n c := by
  have h := ScheduledWord.schedule_exact (fun _ : Unit => 4)
    (fun _ => CoupledRowCell.schedule f) idle (fun _ => CoupledRowCell.result f)
    (List.replicate n ()) w c (fun _ _ d => CoupledRowCell.cell_exact f w d)
  simpa only [schedule,run,ScheduledWord.ticks,List.map_replicate,List.sum_replicate,
    smul_eq_mul,mul_comm,ScheduledWord.transform,List.foldl_const,List.length_replicate] using h

theorem run_pair (f : (Mode C) → (Mode C)) (c : C) (xs ys : List (Sym Bool))
    (h : xs.length=ys.length) (la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    run f xs.length (cfg (c,.blank,.blank) ![⟨xs++la,ra⟩,⟨ys++lb,rb⟩] pos ip out)=
      let r := evaluate f c xs ys
      cfg (r.1,.blank,.blank) ![⟨la,r.2.1.reverse++ra⟩,⟨lb,r.2.2.reverse++rb⟩]
        (fun t => pos t-xs.length) ip out := by
  induction xs generalizing c ys ra rb pos with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp [run,evaluate]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [run,List.length_cons,Function.iterate_succ_apply,List.cons_append]
      rw [CoupledRowCell.result_pair]
      have ht := ih (f (c,a,b)).1 ys (by simpa using h)
        ((f (c,a,b)).2.1::ra) ((f (c,a,b)).2.2::rb) (fun t => pos t-1)
      simpa only [run,evaluate,List.reverse_cons,List.append_assoc,List.singleton_append,
        List.length_cons,Nat.cast_add,Nat.cast_one,sub_sub,add_comm] using ht

end TransposeFollowup.CoupledRowScan

import TransposeFollowup.BufferedRowRule

/-! Repeated raw-row updates use the existing finite-word scheduler.
The rule supplies both the output row and the next retained buffer. The head remains at the end of the bank;
buffer clearing, rewind and raw external IO are separate paid obligations. -/
namespace TransposeFollowup.BufferedRows
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
open CoupledRowCell (Mode State cfg)
open RawRowArithmetic (initial ticks bankOnly)
set_option autoImplicit false
variable {C : Type}

def rowsResult (u : Rule C) (rows : List (List (Sym Bool))) :
    List (Sym Bool) → List (Sym Bool) × List (Sym Bool) :=
  rows.foldr (fun xs go ys =>
    let r := go (u.saved xs ys)
    (u.output xs ys++r.1,r.2)) (fun ys => ([],ys))

def rowsSchedule (u : Rule C) (W r : ℕ) : ℕ → NativeIO.Program (Fin 2) (Mode C) :=
  ScheduledWord.schedule (fun _ : Unit => ticks W) (fun _ => schedule u W)
    CoupledRowScan.idle (List.replicate r ())

theorem rows_active (u : Rule C) (W r i : ℕ) (c : State C) :
    NativeIO.Active (rowsSchedule u W r i) c := by
  apply ScheduledWord.schedule_active
  · simp [CoupledRowScan.idle,NativeIO.Active]
  · intro _ _ j; exact schedule_active u W j c

theorem rows_lengths (u : Rule C) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (ys : List (Sym Bool)) (hy : ys.length=W) :
    (rowsResult u rows ys).1.length=rows.length*W ∧
      (rowsResult u rows ys).2.length=W := by
  induction rows generalizing ys with
  | nil => simp [rowsResult,hy]
  | cons xs rows ih =>
    have hx := hw xs List.mem_cons_self
    have hxy : xs.length=ys.length := hx.trans hy.symm
    have ho : (u.output xs ys).length=W := by
      simp [output_length u xs ys hxy,hx]
    have hs : (u.saved xs ys).length=W := by
      simp [saved_length u xs ys hxy,hx]
    have hi := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) _ hs
    change (u.output xs ys++(rowsResult u rows (u.saved xs ys)).1).length=
      (xs::rows).length*W ∧ (rowsResult u rows (u.saved xs ys)).2.length=W
    simp only [List.length_append,ho,hi.1,hi.2,List.length_cons,Nat.add_mul,Nat.one_mul]
    exact ⟨Nat.add_comm _ _,trivial⟩

theorem rows_exact (u : Rule C) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode C)
    (ys la lb ra rb : List (Sym Bool)) (hy : ys.length=W)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    ∃ m' : Mode C,
      trajectory (rowsSchedule u W rows.length) w
        (initial m rows.flatten ys la lb ra rb pos ip out) (rows.length*ticks W)=
      cfg m' ![⟨(rowsResult u rows ys).1.reverse++la,ra⟩,
        ⟨lb,(rowsResult u rows ys).2++rb⟩]
        (fun t => pos t+if bankOnly t then (rows.length*W : ℕ) else 0) ip out := by
  induction rows generalizing m ys la pos with
  | nil =>
    refine ⟨m,?_⟩
    simp [trajectory,initial,rowsResult]
  | cons xs rows ih =>
    have hx := hw xs List.mem_cons_self
    have hxy : xs.length=ys.length := hx.trans hy.symm
    have hs : (u.saved xs ys).length=W := by
      simp [saved_length u xs ys hxy,hx]
    obtain ⟨m',hi⟩ := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
      (finalCarry u xs ys,.blank,.blank) (u.saved xs ys)
      ((u.output xs ys).reverse++la) hs
      (fun t => pos t+if bankOnly t then (W : ℤ) else 0)
    refine ⟨m',?_⟩
    have ht : (xs::rows).length*ticks W=ticks W+rows.length*ticks W := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
    rw [ht]
    change trajectory (append (schedule u W) (rowsSchedule u W rows.length) (ticks W)) w
      (initial m (xs++rows.flatten) ys la lb ra rb pos ip out) _ = _
    rw [append_exact]
    have he := schedule_exact u m xs ys la lb (rows.flatten++ra) rb hxy pos ip out w
    have hc : initial m (xs++rows.flatten) ys la lb ra rb pos ip out=
        initial m xs ys la lb (rows.flatten++ra) rb pos ip out := by
      simp only [initial,List.append_assoc]
    rw [hc,← hx,he]
    rw [hx]
    have hf : final u xs ys la lb (rows.flatten++ra) rb pos ip out=
        initial (finalCarry u xs ys,.blank,.blank) rows.flatten
          (u.saved xs ys) ((u.output xs ys).reverse++la)
          lb ra rb (fun t => pos t+if bankOnly t then (W : ℤ) else 0) ip out := by
      simp only [final,initial,hx]
    rw [hf,hi]
    change cfg m' _ _ ip out = cfg m' _ _ ip out
    congr 1
    · funext t
      fin_cases t <;> simp [rowsResult,List.reverse_append,List.append_assoc]
    · funext t
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      cases bankOnly t <;> simp
      ring

end TransposeFollowup.BufferedRows

import TransposeFollowup.NativeIOEmbedding
import TransposeFollowup.FiniteProgramEncodingCore
import TransposeFollowup.NativeCountedLoop

/-! A public finite schedule with a fixed finite data mode compiles through
the existing native IO compiler. Each scheduled active instruction costs
exactly one native transition. Only the public clock grows with input size;
the mode contains the explicitly declared finite local data. -/
namespace TransposeFollowup.ScheduledNativeIO
open Classical FixedTapeCompiler
set_option autoImplicit false
variable {T M : Type*}

def trajectory (σ : ℕ → NativeIO.Program T M) (w : List Bool)
    (c : NativeIO.Config T M) : ℕ → NativeIO.Config T M
  | 0 => c
  | n+1 => NativeIO.step (σ n) w (trajectory σ w c n)

theorem trajectory_add (σ : ℕ → NativeIO.Program T M) (w : List Bool)
    (c : NativeIO.Config T M) (n m : ℕ) :
    trajectory σ w c (n+m)=trajectory (fun i => σ (n+i)) w (trajectory σ w c n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change NativeIO.step (σ (n+m)) w (trajectory σ w c (n+m)) =
      NativeIO.step (σ (n+m)) w (trajectory (fun i => σ (n+i)) w (trajectory σ w c n) m)
    rw [ih]

theorem trajectory_congr (σ τ : ℕ → NativeIO.Program T M) (w : List Bool)
    (c : NativeIO.Config T M) (n : ℕ) (h : ∀ i < n, σ i=τ i) :
    trajectory σ w c n=trajectory τ w c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajectory,trajectory,h n (by omega),ih (fun i hi => h i (by omega))]

def lift {N : ℕ} (j : Fin (N+1)) (c : NativeIO.Config T M) :
    NativeIO.Config T (Fin (N+1) × M) :=
  ⟨⟨⟨(j,c.work.core.pc),c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩

noncomputable def program (σ : ℕ → NativeIO.Program T M) (N : ℕ) :
    NativeIO.Program T (Fin (N+1) × M) := fun (j,m) =>
  if h : j.val < N then
    NativeIOEmbedding.instruction (Function.Embedding.refl T)
      (fun m' => (⟨j.val+1,by omega⟩,m')) (σ j.val m)
  else .work .halt

theorem step_lift (σ : ℕ → NativeIO.Program T M) (w : List Bool)
    {N : ℕ} (j : Fin (N+1)) (c : NativeIO.Config T M) (hj : j.val < N)
    (ha : NativeIO.Active (σ j.val) c) :
    NativeIO.step (program σ N) w (lift j c)=
      lift ⟨j.val+1,by omega⟩ (NativeIO.step (σ j.val) w c) := by
  have hid : (Function.Embedding.refl T : T → T)=id := rfl
  cases hi : σ j.val c.work.core.pc with
  | work i =>
    cases i <;> simp_all [NativeIO.Active,NativeIO.step,NativeIO.workProgram,
      NativeMicrocode.step,Microcode.actualStep,NativeIOEmbedding.instruction,
      MicrocodeEmbedding.instruction,lift,program]
  | _ =>
    simp [NativeIO.step,NativeIOEmbedding.instruction,NativeIO.setLabel,lift,program,hj,hi]

theorem active_lift (σ : ℕ → NativeIO.Program T M)
    {N : ℕ} (j : Fin (N+1)) (c : NativeIO.Config T M) (hj : j.val < N)
    (ha : NativeIO.Active (σ j.val) c) : NativeIO.Active (program σ N) (lift j c) := by
  cases hi : σ j.val c.work.core.pc with
  | work i =>
    cases i <;> simp_all [NativeIO.Active,NativeIOEmbedding.instruction,
      MicrocodeEmbedding.instruction,lift,program]
  | _ => simp [NativeIO.Active,NativeIOEmbedding.instruction,lift,program,hj,hi]

theorem trace_prefix (σ : ℕ → NativeIO.Program T M) (w : List Bool)
    {N : ℕ} (c : NativeIO.Config T M)
    (ha : ∀ i < N, NativeIO.Active (σ i) (trajectory σ w c i))
    (n : ℕ) (hn : n ≤ N) :
    OperationalTrace.Trace (NativeIO.step (program σ N) w) (NativeIO.Active (program σ N)) n
      (lift ⟨0,by omega⟩ c) (lift ⟨n,by omega⟩ (trajectory σ w c n)) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    have hn' : n < N := by omega
    have hs := step_lift σ w (N:=N) ⟨n,by omega⟩ (trajectory σ w c n) hn' (ha n hn')
    have ht : OperationalTrace.Trace (NativeIO.step (program σ N) w)
        (NativeIO.Active (program σ N)) 1
        (lift ⟨n,by omega⟩ (trajectory σ w c n))
        (lift ⟨n+1,by omega⟩ (trajectory σ w c (n+1))) := by
      rw [trajectory,← hs]
      exact .cons (active_lift σ _ _ hn' (ha n hn')) (.refl _)
    exact NativeCountedLoop.trace_trans (ih (by omega)) ht

theorem halted_lift (σ : ℕ → NativeIO.Program T M) (N : ℕ) (c : NativeIO.Config T M) :
    ¬NativeIO.Active (program σ N) (lift ⟨N,by omega⟩ c) := by
  simp [NativeIO.Active,lift,program]

theorem native_prefix {N k q : ℕ} (e : NativeMicrocode.Encoding T (Fin (N+1) × M) k q)
    (σ : ℕ → NativeIO.Program T M) (w : List Bool) (c : NativeIO.Config T M)
    (ha : ∀ i < N, NativeIO.Active (σ i) (trajectory σ w c i)) (n : ℕ) (hn : n ≤ N) :
    Transpose.stepN (NativeIO.machine e (program σ N)) w n
      ((lift ⟨0,by omega⟩ c).denote e (program σ N)) =
      some ((lift ⟨n,by omega⟩ (trajectory σ w c n)).denote e (program σ N)) :=
  NativeIO.trace_stepN e (program σ N) w (trace_prefix σ w c ha n hn)

theorem native_run_and_halt {N k q : ℕ} (e : NativeMicrocode.Encoding T (Fin (N+1) × M) k q)
    (σ : ℕ → NativeIO.Program T M) (w : List Bool) (c : NativeIO.Config T M)
    (ha : ∀ i < N, NativeIO.Active (σ i) (trajectory σ w c i)) :
    Transpose.stepN (NativeIO.machine e (program σ N)) w N
      ((lift ⟨0,by omega⟩ c).denote e (program σ N)) =
      some ((lift ⟨N,by omega⟩ (trajectory σ w c N)).denote e (program σ N)) ∧
    Transpose.step (NativeIO.machine e (program σ N)) w
      ((lift ⟨N,by omega⟩ (trajectory σ w c N)).denote e (program σ N))=none :=
  ⟨native_prefix e σ w c ha N le_rfl,
    (NativeIO.step_none_iff e (program σ N) w _).mpr (halted_lift σ N _)⟩

theorem native_state_count [Fintype T] [Fintype M]
    (σ : ℕ → NativeIO.Program T M) (N : ℕ) (m : M) :
    (NativeIO.machine (NativeMicrocode.initialEncoding (T:=T) ((⟨0,by omega⟩,m) : Fin (N+1) × M))
      (program σ N)).q+1=(N+1)*Fintype.card M := by
  change Fintype.card (Fin (N+1) × M)-1+1=(N+1)*Fintype.card M
  simp only [Fintype.card_prod,Fintype.card_fin]
  have hp : 0 < (N+1)*Fintype.card M := Nat.mul_pos (by omega) (Fintype.card_pos_iff.mpr ⟨m⟩)
  omega

end TransposeFollowup.ScheduledNativeIO

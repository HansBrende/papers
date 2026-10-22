import TransposeFollowup.RawSymbolWord
import TransposeFollowup.ScheduledWordApproximation
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Full-word affine approximation on the actual native machine, with
one load/emission shell. Primitive errors accumulate; no exact body path
or intermediate binary projection is introduced. -/
namespace TransposeFollowup.RawSymbolWord
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false
variable {O : Type*}

noncomputable def curve (P : ℕ) (cost : O → ℕ) (q : O → ℕ → Fin 2 → ℝ → ℝ)
    (ops : List O) (t : Fin 2) (x : ℝ) : ℝ :=
  ScheduledWord.approximation cost q ops (4*P) t x+
    RawBankProgram.ioCurve P (ScheduledWord.ticks cost ops) t x

theorem curve_cover (P : ℕ) (cost : O → ℕ) (q : O → ℕ → Fin 2 → ℝ → ℝ)
    (ops : List O) {J : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (hq : ∀ op ∈ ops, ∀ A t, HasAffineIntervalCover J (q op A t) H) (t : Fin 2) :
    HasAffineIntervalCover (J^ops.length*27) (curve P cost q ops t) H :=
  (ScheduledWord.approximation_cover cost q ops hH hq (4*P) t).add
    (RawBankProgram.ioCurve_cover P (ScheduledWord.ticks cost ops) hH t)

theorem curve_error {P : ℕ} {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → CopyMachine.Sym Bool) → ℕ → CopyMachine.Sym Bool}
    (h : Correct P cost code value) (q : O → ℕ → Fin 2 → ℝ → ℝ)
    (ops : List O) (E : ℝ) (w : List Bool)
    (hq : ∀ op ∈ ops, ∀ A c x t,
      |((trajectory (code op) w c (min (⌊x⌋₊-A) (cost op))).work.pos t : ℝ)-
        c.work.pos t-q op A t x| ≤ E) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine P cost code ops) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)).port t) : ℝ)-
      curve P cost q ops t x| ≤ E*ops.length+4 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode P w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode P w).1 t
  have hb := ScheduledWord.approximation_error cost code (ScheduledTapeAction.action 0 ⟨none,.stay⟩)
    q ops E w hq (4*P) c x t
  rw [hpos,Int.cast_zero,sub_zero] at hb
  have hi := RawBankProgram.ioPath_curve_error P (ScheduledWord.ticks cost ops) t x
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)
      (bodySchedule cost code ops)) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)).port t) : ℝ)-
      curve P cost q ops t x| ≤ E*ops.length+4
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode P
    (ScheduledWord.ticks cost ops) (bodySchedule cost code ops) (body_active h ops)]
  simp only [curve,bodySchedule,Int.cast_add]
  rw [abs_le] at hb hi ⊢
  constructor <;> linarith

theorem scaled_approximation {P : ℕ} (hP : 0<P) {cost : O → ℕ}
    {code : O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode}
    {value : O → (ℕ → CopyMachine.Sym Bool) → ℕ → CopyMachine.Sym Bool}
    (h : Correct P cost code value) (q : O → ℕ → Fin 2 → ℝ → ℝ)
    (ops : List O) {J : ℕ} {H E : ℝ} (hH : 0 ≤ H) (w : List Bool)
    (hcover : ∀ op ∈ ops, ∀ A t, HasAffineIntervalCover J (q op A t) (P*H))
    (hq : ∀ op ∈ ops, ∀ A c x t,
      |((trajectory (code op) w c (min (⌊x⌋₊-A) (cost op))).work.pos t : ℝ)-
        c.work.pos t-q op A t x| ≤ E) (t : Fin 2) :
    HasAffineIntervalCover (J^ops.length*27) (fun x => curve P cost q ops t (P*x)/P) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine P cost code ops) w ⌊P*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode P (ScheduledWord.ticks cost ops)).port t) : ℝ)/P-
        curve P cost q ops t (P*x)/P| ≤ (E*ops.length+4)/P := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  refine ⟨(curve_cover P cost q ops (mul_nonneg hp.le hH) hcover t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error h q ops E w hq (P*x) t) hp.le

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (cost : ℕ → O → ℕ)
    (code : ℕ → O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode)
    (ops : ℕ → List O) {C K : ℕ}
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    (hc : ∀ᶠ i in atTop, ∀ op ∈ ops i, cost i op ≤ C*Transpose.inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (Transpose.inputLength (ns i)) (cost i) (code i) (ops i)).q+1) : ℝ)
      /Transpose.inputLength (ns i)) atTop (𝓝 0) := by
  apply RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => ScheduledWord.ticks (cost i) (ops i)) (fun i => bodySchedule (cost i) (code i) (ops i))
    (C:=7+C*K)
  filter_upwards [hK,hc] with i hi hci
  exact (ticks_le (Transpose.inputLength (ns i)) (cost i) (ops i) C hci).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left C hi) 7))

end TransposeFollowup.RawSymbolWord

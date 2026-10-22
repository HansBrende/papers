import TransposeFollowup.RawProgramShell
import TransposeFollowup.LinearStateCount
import TransposeFollowup.RawRowProgram

/-! Reuse the original sublinear state-bit estimate for the shared raw
shell. Only the fixed finite controller size and paid linear runtime
enter; public operation choices may vary arbitrarily with input size. -/
namespace TransposeFollowup.RawProgramShell
open Classical Filter Topology FixedTapeCompiler Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false
variable {F : Type*} [Fintype F]

theorem cellBits_eq (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F)) :
    cellBits (machine f P N σ)=3 := by
  unfold cellBits
  rw [(fixed_resources f P N σ).2.1]
  decide +kernel

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (f : F) {C : ℕ} (N : ℕ → ℕ) (σ : ℕ → ℕ → NativeIO.Program (Fin 2) (Mode F))
    (ht : ∀ᶠ i in atTop, ticks (inputLength (ns i)) (N i)≤C*inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine f (inputLength (ns i)) (N i) (σ i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply state_bits_of_linear_count (c:=(4*Fintype.card F*(C+1) : ℕ)) hns
  filter_upwards [ht,(inputLength_tendsto hns).eventually_ge_atTop 1] with i hi hp
  have hP : 1 ≤ inputLength (ns i) := by exact_mod_cast hp
  have hb : ticks (inputLength (ns i)) (N i)+1≤(C+1)*inputLength (ns i) := by nlinarith
  have hq : (machine f (inputLength (ns i)) (N i) (σ i)).q+1≤
      4*Fintype.card F*(C+1)*inputLength (ns i) := by
    rw [(fixed_resources f (inputLength (ns i)) (N i) (σ i)).2.2]
    calc
      _ ≤ ((C+1)*inputLength (ns i))*(4*Fintype.card F) := Nat.mul_le_mul_right _ hb
      _ = _ := by ring
  exact_mod_cast hq

end TransposeFollowup.RawProgramShell

namespace TransposeFollowup.SharedRowBank
open Classical Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem raw_rule_state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (u : ℕ → BufferedRows.Rule Bool) (W r : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, r i*W i=inputLength (ns i))
    (hW : ∀ᶠ i in atTop, 0<W i) (hr : ∀ᶠ i in atTop, 0<r i) :
    Tendsto (fun i => (Nat.clog 2 ((rawRuleMachine (u i) (W i) (r i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  have ht : ∀ᶠ i in atTop,
      RawProgramShell.ticks (inputLength (ns i)) (RawRowArithmetic.bankTicks (W i) (r i))≤
        17*inputLength (ns i) := by
    filter_upwards [hP,hW,hr] with i hi hwi hri
    rw [← hi]
    exact raw_ticks_linear (W i) (r i) hwi hri
  have h := RawProgramShell.state_bits_vanish hns initialRowMode
    (fun i => RawRowArithmetic.bankTicks (W i) (r i))
    (fun i => ruleSchedule (u i) (W i) (r i)) ht
  apply h.congr'
  filter_upwards [hP] with i hi
  simp only [rawRuleMachine,hi]

theorem raw_state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (sub : ℕ → Bool) (W r : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, r i*W i=inputLength (ns i))
    (hW : ∀ᶠ i in atTop, 0<W i) (hr : ∀ᶠ i in atTop, 0<r i) :
    Tendsto (fun i => (Nat.clog 2 ((rawMachine (sub i) (W i) (r i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) :=
  raw_rule_state_bits_vanish hns (fun i => RawRowArithmetic.rule (sub i)) W r hP hW hr

end TransposeFollowup.SharedRowBank

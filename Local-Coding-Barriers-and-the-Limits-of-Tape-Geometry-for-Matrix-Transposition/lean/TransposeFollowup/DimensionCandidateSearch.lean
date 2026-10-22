import TransposeFollowup.DimensionCandidateData
import FixedTapeCompiler.OperationalTrace

/-! A stopping search for the dimension under the original encoding.
Its transition uses only the measured length and current state. The number
of iterations appears in its proof, not in the search's transition rule.
This module is arithmetic/control specification, not a native time claim. -/
namespace TransposeFollowup.DimensionCandidate
open Transpose FixedTapeCompiler
set_option autoImplicit false

structure State where
  candidate : ℕ
  square : ℕ
  bits : ℕ
  threshold : ℕ
  deriving DecidableEq

def canonical (k : ℕ) : State := ⟨k,k*k,entryBits k,2^entryBits k⟩
def initial : State := ⟨1,1,1,2⟩
def advance (s : State) : State :=
  let grow := s.threshold < s.candidate+1
  ⟨s.candidate+1,s.square+s.candidate+s.candidate+1,
    if grow then s.bits+1 else s.bits,
    if grow then s.threshold+s.threshold else s.threshold⟩
def payload (s : State) : ℕ := s.square*s.bits

theorem initial_eq : initial=canonical 1 := by decide +kernel

theorem advance_at (k : ℕ) (hk : 1 ≤ k) : advance (canonical k)=canonical (k+1) := by
  have hb := entryBits_step k hk
  by_cases h : 2^entryBits k < k+1
  · have hn : ¬k+1 ≤ 2^entryBits k := by omega
    simp only [hn,ite_false] at hb
    simp only [advance,canonical,h,ite_true,hb,pow_succ]
    congr 1 <;> ring
  · have hn : k+1 ≤ 2^entryBits k := by omega
    simp only [hn,ite_true] at hb
    simp only [advance,canonical,h,ite_false,hb]
    congr 1
    ring

theorem payload_at (k : ℕ) : payload (canonical k)=inputLength k := rfl

def step (L : ℕ) (s : State) : State := if payload s < L then advance s else s
def Active (L : ℕ) (s : State) : Prop := payload s < L

theorem step_at {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    step (inputLength n) (canonical k)=canonical (k+1) := by
  have h := length_strictMono hkn
  simp only [step,payload_at,h,ite_true,advance_at k hk]

theorem step_terminal (n : ℕ) : step (inputLength n) (canonical n)=canonical n ∧ ¬Active (inputLength n) (canonical n) := by
  simp [step,Active,payload_at]

theorem search_trace (n k r : ℕ) (hk : 1 ≤ k) (hr : k+r=n) :
    OperationalTrace.Trace (step (inputLength n)) (Active (inputLength n)) r (canonical k) (canonical n) := by
  induction r generalizing k with
  | zero =>
    have he : k=n := by omega
    subst k
    exact .refl _
  | succ r ih =>
    have hkn : k < n := by omega
    apply OperationalTrace.Trace.cons
    · exact length_strictMono hkn
    · rw [step_at hk hkn]
      exact ih (k+1) (by omega) (by omega)

theorem complete_search (n : ℕ) (hn : 1 ≤ n) :
    OperationalTrace.Trace (step (inputLength n)) (Active (inputLength n)) (n-1) initial (canonical n) ∧
    ¬Active (inputLength n) (canonical n) := by
  rw [initial_eq]
  exact ⟨search_trace n 1 (n-1) (by omega) (by omega),(step_terminal n).2⟩

theorem unique_match {k n : ℕ} (h : payload (canonical k)=inputLength n) : k=n :=
  length_strictMono.injective h

theorem threshold_bound (k : ℕ) (hk : 1 ≤ k) : 2^entryBits k ≤ 2*k := by
  by_cases h1 : k=1
  · subst k;decide +kernel
  · have h := Nat.log2_self_le (n:=k-1) (by omega)
    unfold entryBits
    rw [pow_succ]
    omega

theorem dimension_le_length (n : ℕ) (hn : 1 ≤ n) : n ≤ inputLength n := by
  have hb : 1 ≤ entryBits n := by unfold entryBits;omega
  unfold inputLength
  exact (Nat.le_mul_of_pos_right n hn).trans (Nat.le_mul_of_pos_right _ hb)

theorem double_length_fit (L : ℕ) : 2*L+2 < 2^width L := by
  have h := Nat.lt_size_self L
  have hp : 1 ≤ 2^L.size := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have he : 2^width L=16*(2^L.size)*(2^L.size) := by
    rw [show width L=L.size+L.size+4 by unfold width;omega,pow_add,pow_add]
    norm_num
    ring
  rw [he]
  nlinarith

theorem state_fits {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (canonical k).candidate < 2^width (inputLength n) ∧
    (canonical k).square < 2^width (inputLength n) ∧
    (canonical k).bits < 2^width (inputLength n) ∧
    (canonical k).threshold < 2^width (inputLength n) ∧
    payload (canonical k) < 2^width (inputLength n) := by
  have hn : 1 ≤ n := hk.trans hkn
  have hL := dimension_le_length n hn
  have hb := Tape.Impl.entryBits_le_self hk
  have hb1 : 1 ≤ entryBits k := by unfold entryBits;omega
  have hs : k*k ≤ inputLength k := Nat.le_mul_of_pos_right _ hb1
  have hm := length_strictMono.monotone hkn
  have ht := threshold_bound k hk
  have hf := double_length_fit (inputLength n)
  change k < 2^width (inputLength n) ∧ k*k < 2^width (inputLength n) ∧
    entryBits k < 2^width (inputLength n) ∧ 2^entryBits k < 2^width (inputLength n) ∧
    inputLength k < 2^width (inputLength n)
  omega

end TransposeFollowup.DimensionCandidate

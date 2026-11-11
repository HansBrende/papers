import SharedDecoders.CapacityLinearization
import SharedDecoders.CapacityGluing
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Field.ZMod

/-! # Source hypotheses cannot silently be exchanged

The finite binary example has deterministic shared decoding but no linear
shared decoder on the same source. This does not compare maximum capacities.
-/

namespace SharedDecoders.CapacityControls

abbrev Bit := ZMod 2

def generator : State 3 Bit := fun i j => if i = 0 ∧ j ≠ 2 then 1 else 0

def decoder (Y : State 3 Bit) : ZMod 3 → Bit :=
  if Y = generator then generator 0 else 0

theorem decoder_zero (c : ZMod 3) :
    decoder (rot c (0 : State 3 Bit)) = 0 := by
  revert c
  decide

theorem decoder_generator (c : ZMod 3) : decoder (rot c generator) = generator c := by
  revert c
  decide

def source : Submodule Bit (State 3 Bit) := Submodule.span Bit {generator}

theorem source_isSharedCode : IsSharedCode Bit (fun _ : ZMod 3 => ()) source := by
  refine ⟨fun _ => decoder, ?_⟩
  intro X hX c
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hX
  fin_cases a
  · change ((0 : Bit) • generator) c = decoder (rot c ((0 : Bit) • generator))
    simpa only [zero_smul, Pi.zero_apply] using (decoder_zero c).symm
  · change ((1 : Bit) • generator) c = decoder (rot c ((1 : Bit) • generator))
    simpa only [one_smul] using (decoder_generator c).symm

theorem source_not_linear : ¬IsLinearSharedCode (fun _ : ZMod 3 => ()) source := by
  intro h
  have hx : generator ∈ source := Submodule.subset_span (by simp)
  have hdep : generator + rot (1 : ZMod 3) generator + rot (2 * 1 : ZMod 3) generator = 0 := by
    decide
  have hrow := h.triple_rows_zero hx 1 0 hdep rfl rfl
  have hn : generator 0 + generator (0 + 1) + generator (0 + 2 * 1) ≠ 0 := by
    decide
  exact hn hrow

theorem exists_deterministic_not_linear :
    ∃ C : Submodule Bit (State 3 Bit),
      IsSharedCode Bit (fun _ : ZMod 3 => ()) C ∧
      ¬IsLinearSharedCode (fun _ : ZMod 3 => ()) C :=
  ⟨source, source_isSharedCode, source_not_linear⟩

end SharedDecoders.CapacityControls

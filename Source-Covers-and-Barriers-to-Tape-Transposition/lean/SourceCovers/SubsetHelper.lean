import LeanMachine.SubsetPlacement
import SourceCovers.UniformCoordinates
import Mathlib.Data.ZMod.Basic

/-! Exact recovery, helper entropy, fibres, and joint independence for the
repeated subset placement code in Proposition 7.3. Entries are entire
`b`-bit words, not separately sampled or separately decoded bits. -/

namespace SourceCovers.SubsetHelper

open Finset LeanMachine TransposeFollowup
open scoped BigOperators Classical
noncomputable section

abbrev Word (b : ℕ) := Fin b → ZMod 2
abbrev Entry (N k h : ℕ) :=
  SubsetPlacement.Entry (Fin N) k (Fin (N.choose k * h)) (Fin (N * h))
abbrev Packet (N k h : ℕ) :=
  SubsetPlacement.Packet (Fin N) k (Fin (N.choose k * h)) (Fin (N * h))
abbrev Cube (N k h b : ℕ) := Entry N k h → Word b

-- Use the same domain equality instances as the generic finite-map lemmas.
local instance (N k h : ℕ) : DecidableEq (Entry N k h) := Classical.decEq _
local instance (N k h : ℕ) : DecidableEq (Packet N k h) := Classical.decEq _
local instance (b : ℕ) : DecidableEq (Word b) := Classical.decEq _

def side (N k h : ℕ) : ℕ := N * N.choose k * h
def inputBits (N k h b : ℕ) : ℕ := (side N k h) ^ 2 * b
def helperBits (N k h b : ℕ) : ℕ :=
  b * N.choose (k + 1) * (N.choose k * h) * (N * h)

abbrev helper (N k h b : ℕ) : Cube N k h b →+ (Packet N k h → Word b) :=
  SubsetPlacement.code.encode

theorem helper_apply (N k h b : ℕ) (x : Cube N k h b) (p : Packet N k h) :
    helper N k h b x p = ∑ i : p.1.val, x (SubsetPlacement.summand p i) :=
  SubsetPlacement.encode_eq x p

theorem queried_absent (N k h : ℕ) (e : Entry N k h) (he : e.1 ∈ e.2.1.val)
    (p : Packet N k h) : e ∉ SubsetPlacement.code.support p :=
  SubsetPlacement.queried_absent e he p

theorem card_word (b : ℕ) : Fintype.card (Word b) = 2 ^ b := by
  simp [Word, ZMod.card]

theorem card_entry (N k h : ℕ) : Fintype.card (Entry N k h) = (side N k h) ^ 2 := by
  rw [SubsetPlacement.card_entry]
  simp only [Fintype.card_fin, side]
  ring

theorem card_packet (N k h : ℕ) : Fintype.card (Packet N k h) =
    N.choose (k + 1) * (N.choose k * h) * (N * h) := by
  simp [Packet, mul_assoc]

theorem helper_bits_count (N k h b : ℕ) :
    helperBits N k h b = b * Fintype.card (Packet N k h) := by
  rw [card_packet]
  simp only [helperBits, mul_assoc]

theorem input_bits_count (N k h b : ℕ) :
    inputBits N k h b = b * Fintype.card (Entry N k h) := by
  rw [card_entry, inputBits, mul_comm]

theorem helper_bits_le (N k h b : ℕ) : helperBits N k h b ≤ inputBits N k h b := by
  rw [helper_bits_count, input_bits_count]
  exact Nat.mul_le_mul_left b SubsetPlacement.code.card_le

/-- The common helper is uniform on exactly the stated number of bits. -/
theorem helper_uniform (N k h b : ℕ) :
    pushforward (uniformWeight (Cube N k h b)) (helper N k h b) =
      uniformWeight (Packet N k h → Word b) := by
  exact uniform_disjointSums (ι := Entry N k h) (κ := Packet N k h)
    (A := Word b) SubsetPlacement.code

theorem card_helper (N k h b : ℕ) :
    Fintype.card (Packet N k h → Word b) = 2 ^ helperBits N k h b := by
  rw [Fintype.card_fun, card_word, ← pow_mul, helper_bits_count]

theorem helper_entropy (N k h b : ℕ) :
    observationEntropy (uniformWeight (Cube N k h b)) (helper N k h b) / Real.log 2 =
      helperBits N k h b := by
  rw [observationEntropy, helper_uniform, entropy_uniformWeight,
    card_helper, Nat.cast_pow, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact mul_div_cancel_right₀ _ hlog

/-- All helper values occur, with exactly the same full-cube fibre size. -/
theorem helper_fiber (N k h b : ℕ) (y : Packet N k h → Word b) :
    (univ.filter fun x : Cube N k h b => helper N k h b x = y).card =
      2 ^ (inputBits N k h b - helperBits N k h b) := by
  have hf := DisjointSums.fiber_card (ι := Entry N k h) (κ := Packet N k h) (A := Word b)
    (SubsetPlacement.code (α := Fin N) (k := k)
      (U := Fin (N.choose k * h)) (Z := Fin (N * h))) y
  rw [card_word, ← pow_mul] at hf
  rw [input_bits_count, helper_bits_count, ← Nat.mul_sub_left_distrib]
  exact hf

theorem recovery (N k h b : ℕ) (x y : Cube N k h b) (e : Entry N k h)
    (hhelper : helper N k h b x = helper N k h b y)
    (hrows : ∀ f, f.1 ∈ e.2.1.val → x f = y f) : x e = y e :=
  SubsetPlacement.entry_recovery x y e hhelper hrows

/-- Joint observation of the common helper and every other entire entry. -/
def rest (N k h b : ℕ) (e : Entry N k h) (x : Cube N k h b) :=
  (helper N k h b x, fun f : {f : Entry N k h // f ≠ e} => x f)

theorem queried_independent (N k h b : ℕ) (e : Entry N k h)
    (he : e.1 ∈ e.2.1.val) (a : Word b)
    (y : (Packet N k h → Word b) × ({f : Entry N k h // f ≠ e} → Word b)) :
    pushforward (uniformWeight (Cube N k h b)) (fun x => (x e, rest N k h b e x)) (a, y) =
      pushforward (uniformWeight (Cube N k h b)) (fun x => x e) a *
        pushforward (uniformWeight (Cube N k h b)) (rest N k h b e) y := by
  apply uniform_independent_coordinate (ι := Entry N k h) (A := Word b)
  intro x c
  apply Prod.ext
  · exact SubsetPlacement.code.encode_update (SubsetPlacement.queried_absent e he) x c
  · funext f
    exact Function.update_of_ne f.property _ _

/-- Exact helper cost, including all row and column repetitions. -/
theorem helper_bits_formula (N k h b : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    (helperBits N k h b : ℝ) =
      inputBits N k h b * ((N : ℝ) - k) / (N * (k + 1)) := by
  have hc : (N.choose (k + 1) : ℝ) * (k + 1) = N.choose k * ((N : ℝ) - k) := by
    exact_mod_cast Nat.choose_succ_right_eq N k
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (eq_div_iff (by positivity : (N : ℝ) * (k + 1) ≠ 0)).mpr
  simp only [helperBits, inputBits, side, Nat.cast_mul, Nat.cast_pow]
  linear_combination b * N ^ 2 * N.choose k * h ^ 2 * hc

/-- The complete uniform-helper law: output bits, entropy in bits, every
fibre, and the exact cost formula. Zero repetitions or word width are
allowed here; normalized ratios separately require positive input length. -/
theorem helper_law (N k h b : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    pushforward (uniformWeight (Cube N k h b)) (helper N k h b) =
        uniformWeight (Packet N k h → Word b) ∧
    Fintype.card (Packet N k h → Word b) = 2 ^ helperBits N k h b ∧
    observationEntropy (uniformWeight (Cube N k h b)) (helper N k h b) / Real.log 2 =
        helperBits N k h b ∧
    (∀ y : Packet N k h → Word b,
      (univ.filter fun x : Cube N k h b => helper N k h b x = y).card =
        2 ^ (inputBits N k h b - helperBits N k h b)) ∧
    (helperBits N k h b : ℝ) = inputBits N k h b * ((N : ℝ) - k) / (N * (k + 1)) :=
  ⟨helper_uniform N k h b, card_helper N k h b, helper_entropy N k h b,
    helper_fiber N k h b, helper_bits_formula N k h b hN hk⟩

end
end SourceCovers.SubsetHelper

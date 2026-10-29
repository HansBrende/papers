import SourceCovers.CausalNativeNetwork
import LeanMachine.LogarithmicRadius
import Mathlib.Algebra.Order.Floor.Div

/-! Explicit finite estimates for the causal-group obstruction on native tape
diagrams. Entry width is arbitrary; all constants are independent of it. -/

namespace SourceCovers.CausalGroups

open LeanMachine Transpose Transpose.Tape Transpose.Tape.Impl TransposeFollowup Finset
open scoped BigOperators Classical
noncomputable section

variable {k d b r G : ℕ} {c : ℝ}

def nativeBlockSize (G d b : ℕ) : ℕ := (d * b) ⌈/⌉ G

theorem nativeBlockSize_eq : nativeBlockSize G d b = numSlots G (d * b) := rfl

theorem nativeBlockSize_bounds (hd : 0 < d) (hb : 0 < b) (hG : 0 < G) :
    1 ≤ nativeBlockSize G d b ∧ nativeBlockSize G d b ≤ d * b ∧
      d * b ≤ nativeBlockSize G d b * G := by
  have hmul : d * b ≤ nativeBlockSize G d b * G := by
    simpa only [nativeBlockSize, smul_eq_mul, Nat.mul_comm] using
      (le_smul_ceilDiv (b := d * b) hG)
  refine ⟨?_, ?_, hmul⟩
  · by_contra hn
    have : nativeBlockSize G d b = 0 := by omega
    simp only [this, zero_mul] at hmul
    exact (Nat.mul_pos hd hb).not_ge hmul
  · apply (ceilDiv_le_iff_le_mul hG).mpr
    simpa using Nat.mul_le_mul_right (d * b) hG

/-- A slightly relaxed constant avoids rounding losses depending on width. -/
theorem native_nodes_le (D : TSDiagram k) (hd : 0 < d) (hb : 0 < b)
    (hT : (D.T : ℝ) ≤ c * (d * d * b : ℕ)) (hrdb : r ≤ d * b)
    (hrG : d * b ≤ r * G) :
    (D.nodes r : ℝ) ≤ (c + 1) * G * d := by
  have hW : (0 : ℝ) < (d : ℝ) * b := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnr : (D.nodes r : ℝ) * r ≤ (D.T : ℝ) + r := by
    exact_mod_cast (nodes_mul_le (D := D) r).trans (Nat.sub_le _ _)
  have hrdb' : (r : ℝ) ≤ (d : ℝ) * b := by exact_mod_cast hrdb
  have hrG' : (d : ℝ) * b ≤ (r : ℝ) * G := by exact_mod_cast hrG
  have hT' : (D.T : ℝ) ≤ c * ((d : ℝ) * d * b) := by exact_mod_cast hT
  apply (mul_le_mul_iff_of_pos_right hW).mp
  calc
    (D.nodes r : ℝ) * ((d : ℝ) * b) ≤ (D.nodes r : ℝ) * ((r : ℝ) * G) :=
      mul_le_mul_of_nonneg_left hrG' (Nat.cast_nonneg _)
    _ = ((D.nodes r : ℝ) * r) * G := by ring
    _ ≤ ((D.T : ℝ) + r) * G := mul_le_mul_of_nonneg_right hnr (Nat.cast_nonneg _)
    _ ≤ (c * ((d : ℝ) * d * b) + (d : ℝ) * b) * G :=
      mul_le_mul_of_nonneg_right (add_le_add hT' hrdb') (Nat.cast_nonneg _)
    _ ≤ (c * ((d : ℝ) * d * b) + (d : ℝ) * d * b) * G := by
      gcongr
      nlinarith
    _ = _ := by ring

theorem native_capacity_le (D : TSDiagram k) (hd : 0 < d)
    (hT : (D.T : ℝ) ≤ c * (d * d * b : ℕ)) (hrdb : r ≤ d * b)
    (cap : NativeEdge D r → ℝ)
    (hV : ∑ e, cap e ≤ (4 * k * D.nodes r * r * G : ℕ)) :
    ∑ e, cap e ≤ 4 * k * ((c + 1) * G) * (d * d * b : ℕ) := by
  have hnr : (D.nodes r : ℝ) * r ≤ (D.T : ℝ) + r := by
    exact_mod_cast (nodes_mul_le (D := D) r).trans (Nat.sub_le _ _)
  have hrL : (r : ℝ) ≤ (d * d * b : ℕ) := by
    exact_mod_cast hrdb.trans (by nlinarith : d * b ≤ d * d * b)
  have hm := mul_le_mul_of_nonneg_left
    (hnr.trans (add_le_add hT hrL)) (show (0 : ℝ) ≤ 4 * k * G by positivity)
  push_cast at hV
  calc
    ∑ e, cap e ≤ 4 * k * D.nodes r * r * G := hV
    _ ≤ 4 * k * G * (c * (d * d * b : ℕ) + (d * d * b : ℕ)) := by nlinarith [hm]
    _ = _ := by ring

namespace NativeNetwork

universe v
variable {h : ℕ} (D : TSDiagram k) (hD : D.Valid (d * d * b)) (hr : 1 ≤ r)
  (P : ColumnPartition d h) (cap : NativeEdge D r → ℝ) (hcap : ∀ e, 0 ≤ cap e)
local notation "N" => nativeNetwork D hD hr P cap hcap

/-- The finite entropy estimate on the original tape diagram, before choosing
a radius or imposing a runtime bound. -/
theorem entropy_le_native (hb : 0 < b) (hrdb : r ≤ d * b)
    (g : ℕ) (hg : ∀ a, Fintype.card ((N).GroupColumn a) ≤ g)
    {Helper : Type v} (C : Set (Input d b)) (Z : Input d b → Helper)
    (htyp : (N).CausalGroupTyping C Z) (p : C → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (N).conditionalGroupEntropy C Z p ≤
      ((2 * D.nodes r - 1) * b * (2 * k + 3) ^ (ℓ - 1) : ℕ) +
        ((∑ e, cap e) + 2 * (g * d * b : ℕ) * (D.nodes r - 1 : ℕ)) / ℓ := by
  let := (N).groupBit_nonempty hb
  obtain ⟨R, _, _, _, he, hV, hh⟩ := (N).causal_group_routing C Z htyp p hp hp1
  have hshort : ((N).shortBits ℓ).card ≤
      (2 * D.nodes r - 1) * b * (2 * k + 3) ^ (ℓ - 1) :=
    (card_shortBits_le D hD hr P cap hcap hrdb ℓ).trans (min_le_right _ _)
  exact (he.trans (hh ℓ hℓ).1).trans
    (add_le_add (by exact_mod_cast hshort)
      (div_le_div_of_nonneg_right (hV g hg) (Nat.cast_nonneg _)))

/-- Explicit uniform constants for Corollary 8.4. Any block size in the stated
range works; it need not equal the rounded canonical choice. -/
theorem entropy_le_explicit (hd : 0 < d) (hb : 0 < b) (hc : 0 ≤ c)
    (hrdb : r ≤ d * b) (hrG : d * b ≤ r * G)
    (hT : (D.T : ℝ) ≤ c * (d * d * b : ℕ))
    (hV : ∑ e, cap e ≤ (4 * k * D.nodes r * r * G : ℕ))
    (g : ℕ) (hg : ∀ a, Fintype.card ((N).GroupColumn a) ≤ g)
    {Helper : Type v} (C : Set (Input d b)) (Z : Input d b → Helper)
    (htyp : (N).CausalGroupTyping C Z) (p : C → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (hlarge : (2 * k + 3) ^ 4 ≤ d) :
    (N).conditionalGroupEntropy C Z p ≤
      2 * ((c + 1) * G) * (d * d * b : ℕ) / Real.sqrt d +
        4 * Real.log (2 * k + 3) * ((c + 1) * G) * (4 * k + 2 * g) *
          (d * d * b : ℕ) / Real.log d := by
  let A : ℝ := 2 * k + 3
  let K : ℝ := (c + 1) * G
  let L : ℝ := (d * d * b : ℕ)
  have hA : 1 < A := by dsimp [A]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlarge' : A ^ 4 ≤ (d : ℝ) := by dsimp [A]; exact_mod_cast hlarge
  have hd1 : (1 : ℝ) < d := (one_lt_pow₀ hA (by decide : (4 : ℕ) ≠ 0)).trans_le hlarge'
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := Nat.cast_nonneg _
  obtain ⟨ℓ, hℓ, hpow, hrad⟩ := exists_logarithmic_radius hA hlarge'
  have hn := native_nodes_le D hd hb hT hrdb hrG
  have hcapV := native_capacity_le D hd hT hrdb cap hV
  have hm1 : ((D.nodes r - 1 : ℕ) : ℝ) ≤ (D.nodes r : ℝ) := by
    exact_mod_cast Nat.sub_le (D.nodes r) 1
  have hm2 : ((2 * D.nodes r - 1 : ℕ) : ℝ) ≤ 2 * (D.nodes r : ℝ) := by
    exact_mod_cast Nat.sub_le (2 * D.nodes r) 1
  have hexp : A ^ (ℓ - 1) ≤ A ^ ℓ := pow_le_pow_right₀ hA.le (Nat.sub_le _ _)
  have hshort : (((2 * D.nodes r - 1) * b * (2 * k + 3) ^ (ℓ - 1) : ℕ) : ℝ) ≤
      2 * K * L / Real.sqrt d := by
    calc
      _ ≤ 2 * (D.nodes r : ℝ) * b * A ^ ℓ := by
        push_cast
        dsimp [A] at hexp ⊢
        gcongr
      _ ≤ 2 * (K * d) * b * Real.sqrt d := by gcongr
      _ = (2 * K * d * b) * Real.sqrt d := by ring
      _ = _ := by
        apply (eq_div_iff hsqrt.ne').mpr
        calc
          _ = (2 * K * d * b) * (Real.sqrt d * Real.sqrt d) := by ring
          _ = (2 * K * d * b) * d := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
          _ = _ := by dsimp [L]; push_cast; ring
  have hvol : (∑ e, cap e) + 2 * (g * d * b : ℕ) * (D.nodes r - 1 : ℕ) ≤
      K * (4 * k + 2 * g) * L := by
    calc
      _ ≤ 4 * k * K * L + 2 * (g * d * b : ℕ) * (K * d) := by
        apply add_le_add hcapV
        exact mul_le_mul_of_nonneg_left (hm1.trans hn) (by positivity)
      _ = _ := by dsimp [L]; push_cast; ring
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hd1
  have hlogA : 0 < 4 * Real.log A := by positivity [Real.log_pos hA]
  have hden : Real.log (d : ℝ) ≤ (ℓ : ℝ) * (4 * Real.log A) :=
    (div_le_iff₀ hlogA).mp hrad
  have hq : (K * (4 * k + 2 * g) * L) / ℓ ≤
      (4 * Real.log A * (K * (4 * k + 2 * g) * L)) / Real.log d := by
    apply (div_le_div_iff₀ (by exact_mod_cast hℓ) hlog).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hden
      (show 0 ≤ K * (4 * k + 2 * g) * L by positivity)]
  have he := entropy_le_native D hD hr P cap hcap hb hrdb g hg C Z htyp p hp hp1 ℓ hℓ
  refine he.trans ((add_le_add hshort
    ((div_le_div_of_nonneg_right hvol (Nat.cast_nonneg _)).trans hq)).trans_eq ?_)
  dsimp [A, K, L]
  ring

end NativeNetwork
end
end SourceCovers.CausalGroups

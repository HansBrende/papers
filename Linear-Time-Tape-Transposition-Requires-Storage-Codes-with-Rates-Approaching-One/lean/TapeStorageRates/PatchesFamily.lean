import TapeStorageRates.Patches
import TapeStorageRates.Statement

/-!
# Asymptotic coverage by bounded recovery patches

Only a vanishing fraction of short paired distances at the one radius used by
the finite inequality is needed. The scored targets per patch and the patch overlap are bounded while
the family index tends to infinity.
-/

namespace TapeStorageRates

open Finset Filter DirectedRecovery
open scoped Topology

set_option autoImplicit false

/-- The indexed patches, their served targets and their actual recovery
functions, expressed by agreement on codewords. -/
structure RecoveryPatches {V α : Type*} (J : Type*) [Fintype J] [DecidableEq V]
    (N : V → Finset V) (C : Finset (V → α)) (S : Finset V) (w r : ℕ) where
  patch : J → Finset V
  served : J → Finset V
  size_le : ∀ j, (served j).card ≤ w
  overlap_le : ∀ v, (univ.filter fun j => v ∈ patch j).card ≤ r
  covers : ∀ q ∈ S, ∃ j, q ∈ served j
  within : ∀ j, served j ⊆ patch j
  recovers : ∀ j, ∀ q ∈ served j, ∀ x ∈ C, ∀ y ∈ C,
    (∀ u ∈ N q, u ∈ patch j → x u = y u) → x q = y q

/-- On codes over finite alphabets with vanishing short-pair fraction at radius `2*w-1`,
the upper limiting covered fraction is at most twice the overlap times
the upper limiting deficit fraction. -/
theorem patch_coverage_limsup {V J α : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, Nontrivial (α i)] [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (J i)] (N : (i : ℕ) → V i → Finset (V i))
    (C : (i : ℕ) → Finset (V i → α i)) (S : (i : ℕ) → Finset (V i))
    (hne : ∀ i, (C i).Nonempty) (hpos : ∀ i, 0 < Fintype.card (V i))
    (w r : ℕ) (P : ∀ i, RecoveryPatches (J i) (N i) (C i) (S i) w r)
    (hshort : Tendsto (fun i => ((shortPairedCoordinates (N i) (2*w-1)).card : ℝ) /
      Fintype.card (V i)) atTop (𝓝 0)) :
    limsup (fun i => ((S i).card : ℝ) / Fintype.card (V i)) atTop ≤
      2 * r * (1 - liminf (fun i => storageCodeRate (C i)) atTop) := by
  let rate (i : ℕ) := storageCodeRate (C i)
  let k : ℝ := 2 * r
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hlower : IsBoundedUnder (· ≥ ·) atTop rate :=
    isBoundedUnder_of ⟨0, fun i => MergeDepth.storageCodeRate_nonneg (by exact_mod_cast Fintype.one_lt_card (α := α i)) (hne i)⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun i => ((S i).card : ℝ) / Fintype.card (V i)) :=
    isCoboundedUnder_le_of_le atTop (x := (0 : ℝ)) fun _ => by positivity
  change _ ≤ k * (1 - liminf rate atTop)
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le hcob
  let a := ε / (1 + k)
  have ha : 0 < a := div_pos hε (by linarith)
  have haEq : (1 + k) * a = ε := mul_div_cancel₀ ε (by linarith : 1 + k ≠ 0)
  have hrate := eventually_lt_of_lt_liminf (sub_lt_self (liminf rate atTop) ha) hlower
  filter_upwards [hrate, hshort.eventually_lt_const ha] with i hi hbad
  have hn : 0 < (Fintype.card (V i) : ℝ) := by exact_mod_cast hpos i
  have hb := (recovery_patch_coverage (N i) (C i) (hne i) (S i) (P i).patch
    (P i).served w r (P i).size_le (P i).overlap_le (P i).covers (P i).within
    (P i).recovers).2
  have hnrm : ((S i).card : ℝ) / Fintype.card (V i) ≤
      ((shortPairedCoordinates (N i) (2*w-1)).card : ℝ) / Fintype.card (V i) +
        k * (1 - rate i) := by
    apply (div_le_iff₀ hn).mpr
    apply hb.trans
    apply le_of_eq
    dsimp only [k, rate, storageCodeRate]
    field_simp [hn.ne']
  have hh := mul_le_mul_of_nonneg_left hi.le hk
  linarith

/-- The bound for the separated families in the quantitative transfer:
a lower limiting rate of at least `1-a` allows a covered fraction of at
most `2*r*a`. The index type of patches can vary with the code. -/
theorem SeparatedBinaryFamily.patch_coverage_of_rate {Δ : ℕ} (F : SeparatedBinaryFamily Δ)
    {J : ℕ → Type*} [∀ i, Fintype (J i)]
    (S : (i : ℕ) → Finset (Fin (F.length i))) (w r : ℕ) (hw : 0 < w)
    (P : ∀ i, RecoveryPatches (J i) (F.recovery i) (F.code i) (S i) w r)
    {a : ℝ} (ha : 1 - a ≤ liminf (fun i => storageCodeRate (F.code i)) atTop) :
    limsup (fun i => ((S i).card : ℝ) / F.length i) atTop ≤ 2 * r * a := by
  have h := patch_coverage_limsup F.recovery F.code S F.nonempty
    (fun i => by simpa using F.length_pos i) w r P
    (F.hasPairedDistanceSeparation (2*w-1) (by omega))
  simp only [Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end TapeStorageRates

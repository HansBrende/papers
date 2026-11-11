import AdaptiveTransfer.CoreLocalCuts
import AdaptiveTransfer.CoreRecordCounts
import AdaptiveTransfer.LocalMenuCount
import AdaptiveTransfer.GeometryMenuRates

/-! Exact localized native class counting. The message contains only the
original ordinary records, finite local cut records and the original omitted
set's exterior. Imports and chosen roots are not message fields. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations
open scoped BigOperators

namespace CoreReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : CoreReplayClass M P π)
  (c : g.Completion) (N r : ℕ) (hN : (runStarts g.times).card ≤ N)
  (cuts : ∀ X : g.inputs, g.LocalCut X) (hcut : ∀ X, (cuts X).cut.card ≤ r)

noncomputable def localCode (X : g.inputs) :
    (g.Exterior × g.Ordinary) × TotalLocalFragmentRecord M P g.limit N r :=
  ((g.exterior X, g.ordinary X),
    ⟨⟨(cuts X).cut, mem_filter.mpr ⟨mem_powerset.mpr (fun t ht =>
      mem_range.mpr (((cuts X).cut_lt t ht).trans_le (c.finish_le X))), hcut X⟩⟩,
      ((cuts X).observation c N hN).encode⟩)

theorem localCode_injective : Function.Injective (g.localCode c N r hN cuts hcut) := by
  classical
  intro X Y he
  have hc := Sigma.mk.inj_iff.mp (congrArg Prod.snd he)
  apply LocalCut.records_recover c N hN (cuts X) (cuts Y)
    (congrArg Subtype.val hc.1) hc.2 (congrArg (fun v => v.1.2) he)
  intro p hp
  exact congrFun (congrArg (fun v => v.1.1) he) ⟨p, mem_compl.mpr hp⟩

include c hN cuts hcut in
theorem local_bits_card_bound (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    g.inputs.card ≤ 2 ^ (P - g.omitted.card + g.ordinaryBits q a) *
      localCutMenu M.k (q + M.k * a + 2) P g.limit N r := by
  classical
  calc
    g.inputs.card ≤ (Fintype.card g.Exterior * Fintype.card g.Ordinary) *
        Fintype.card (TotalLocalFragmentRecord M P g.limit N r) := by
      simpa only [Fintype.card_coe, Fintype.card_prod] using
        Fintype.card_le_of_injective _ (g.localCode_injective c N r hN cuts hcut)
    _ ≤ (2 ^ (P - g.omitted.card) * 2 ^ g.ordinaryBits q a) *
        localCutMenu M.k (q + M.k * a + 2) P g.limit N r := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul g.exterior_card.le (g.ordinary_card_le q a hq ha)
      · exact totalLocalFragmentRecord_card_le M P g.limit N r q a hq ha
    _ = _ := by rw [pow_add]

include c hN cuts hcut in
/-- The actual snapshot-adjusted saving, with exactly the replacement of the
import menu by the finite localized cut menu. -/
theorem local_saving_card_bound (q a L : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a)
    (hfr : ∀ h, (g.fringe h).card ≤ L) (hwin : 2 * g.radius + 1 ≤ L)
    (saving : ℝ) (hsaving : saving ≤ (g.omitted.card : ℝ) - (a : ℝ) * Fintype.card g.SnapshotDomain) :
    (g.inputs.card : ℝ) ≤
      (2 : ℝ) ^ ((P : ℝ) - saving + (N : ℝ) * q + (a : ℝ) * N * M.k * L) *
      (localCutMenu M.k (q + M.k * a + 2) P g.limit N r : ℕ) := by
  have hh := g.local_bits_card_bound c N r hN cuts hcut q a hq ha
  have hh' : (g.inputs.card : ℝ) ≤
      (2 : ℝ) ^ ((P - g.omitted.card + g.ordinaryBits q a : ℕ) : ℝ) *
        (localCutMenu M.k (q + M.k * a + 2) P g.limit N r : ℕ) := by exact_mod_cast hh
  exact hh'.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (g.saving_exponent_le q a N L hN hfr hwin saving hsaving)) (by positivity))

end CoreReplayClass
end AdaptiveTransfer

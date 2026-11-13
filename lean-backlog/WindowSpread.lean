import WindowWorkCounting
import WindowRowCover
import WindowBudgets

/-!
# Native row spread after an additional cheap cut

The native quantitative target in `StatementsRowSpread.lean` is proved here
from actual unit-speed visits, exact dependency guards and append times.
The stronger result keeps the cost slack, only needs a complete output
prefix, and records that every new cut lies before the horizon.
-/
namespace LeanBacklog.WindowSpread

open Finset BoundedNesting MergeDepth BoundedStackDepth
open WindowGuards WindowConeWindows WindowWorkCounting WindowRows
open WindowRowCover WindowBudgets RowSpread

/-- Full native geometry, with no correctness/obliviousness premise and
no restriction on the initial cut's cost. Only the first `d*d*b` appends
are used, so an exact output length is unnecessary. -/
theorem native_row_spread_prefix {k β D d b : ℕ} {C ε : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hd : 4 ≤ d) (hb : 1 ≤ b)
    (τ : Trace k) (T : ℕ)
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (happ : d * d * b ≤ (appendList τ T).length) (Γ : Finset ℕ)
    (hdepth : ∀ π, IsDepPath τ.work T π → LinNet.GFree Γ π → π.length ≤ D + 1) :
    ∃ (Γ' : Finset ℕ) (E : Finset (Fin d)) (ρ : Fin d → Finset (Fin d)),
      Γ ⊆ Γ' ∧ (Γ' \ Γ) ⊆ range T ∧
      (β * (Γ' \ Γ).card : ℝ) ≤ (63 / 64 : ℝ) * ε * (d * d * b : ℕ) ∧
      (E.card : ℝ) ≤ (21 / 32 : ℝ) * ε * d ∧
      (∀ r, (ρ r).card ≤ rowSpreadWindow k β D C ε) ∧
      ConeRowsExcept (coneSystem τ T Γ' d b) ρ E ∧
      (∀ π, IsDepPath τ.work T π → LinNet.GFree Γ' π → π.length ≤ D + 1) := by
  classical
  let h := d * b
  let N := (T + h - 1) / h
  let M : ℕ := ⌈4 * (k : ℝ) * (k + 1) * β * C / ε⌉₊
  let M' : ℕ := ⌈2 * C / ε⌉₊
  let G := guards τ.work T h (badWindows τ.work T h M)
  let Γ' := Γ ∪ G
  let next := coarseNext τ.work T h M
  let E := badRowSpans (appendTime τ T) d h M'
  let ρ := helperRows τ T d b next D M'
  have hh : 0 < h := Nat.mul_pos (by omega) hb
  have hN : N * (d * b) ≤ T + d * b := by
    have hn := Nat.div_mul_le_self (T + h - 1) h
    dsimp [N, h] at hn ⊢
    omega
  have hΓ : Γ ⊆ Γ' := subset_union_left
  have hG : G ⊆ Γ' := subset_union_right
  have hnew : Γ' \ Γ ⊆ G := by
    intro u hu
    obtain ⟨hu', huΓ⟩ := mem_sdiff.mp hu
    exact (mem_union.mp hu').resolve_left huΓ
  have hcount : (M + 1) * (Γ' \ Γ).card ≤
      3 * k * (k + 1) * (N * (d * b)) :=
    (Nat.mul_le_mul_left _ (card_le_card hnew)).trans
      (mul_card_guards_le τ.work τ.work_isWalk T h M hh)
  have hbill := guarded_cut_budget (β := β) hd hb hC hε hT hN hcount
  have happ' : d * h ≤ (appendList τ T).length := by
    simpa [h, Nat.mul_assoc] using happ
  have hEcount : M' * E.card ≤ N := appendTime_badRowSpans_count τ hh happ' M'
  have hEbill := exceptional_row_budget hd hb hC hε hT hN hEcount
  have hdepth' : ∀ π, IsDepPath τ.work T π → LinNet.GFree Γ' π → π.length ≤ D + 1 :=
    fun π hp hf => hdepth π hp (gfree_mono hΓ hf)
  have hreach : ∀ (t : ℕ) (π : List ℕ),
      IsDepPath τ.work T (t :: π) → LinNet.GFree Γ' (t :: π) →
      (t :: π).getLastD t / h ∈ neighborReach next D (t / h) := by
    intro t π hp hf
    have hdπ : π.length ≤ D := by
      have hlen := hdepth' _ hp hf
      simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen
    exact free_path_last_window_mem_of_length_le τ.work T h M D hh π t hp
      (gfree_mono hG hf) hdπ
  refine ⟨Γ', E, ρ, hΓ, hnew.trans (guards_subset_range _ _ _ _), hbill, hEbill, ?_, ?_, hdepth'⟩
  · intro r
    exact card_helperRows_le τ T next D hh (card_coarseNext_le τ.work T h M) r
  · exact coneRowsExcept_helperRows τ Γ' next hh happ hreach

/-- The exact original quantitative proposition is a direct corollary of
the stronger prefix/slack theorem, with no extra hypotheses. -/
theorem nativeRowSpreadQuantitative : NativeRowSpreadQuantitative := by
  intro k β D C ε _hβ hC hε d hd b hb τ T hT happ Γ hdepth
  obtain ⟨Γ', E, ρ, hΓ, _, hcost, hE, hρ, hcones, _⟩ :=
    native_row_spread_prefix (β := β) hC hε hd hb τ T hT (le_of_eq happ.symm) Γ hdepth
  refine ⟨Γ', E, ρ, hΓ, ?_, ?_, hρ, hcones⟩
  · have hnonneg : 0 ≤ ε * (d * d * b : ℕ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    nlinarith
  · have hnonneg : 0 ≤ ε * (d : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    nlinarith

theorem nativeRowSpreadExtension : NativeRowSpreadExtension :=
  nativeRowSpreadQuantitative.qualitative

#print axioms native_row_spread_prefix
#print axioms nativeRowSpreadQuantitative
#print axioms nativeRowSpreadExtension

end LeanBacklog.WindowSpread

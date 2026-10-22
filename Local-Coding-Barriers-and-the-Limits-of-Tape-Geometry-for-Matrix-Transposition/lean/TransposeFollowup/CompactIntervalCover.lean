import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.Tactic

/-! Finite interval covers of compact real sets with arbitrarily small excess
total length. The outer-measure construction and finite-subcover theorem are
imported from mathlib; no disjoint interval decomposition is needed. -/
namespace TransposeFollowup.AffineMotion
open Classical Set MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem volume_eq_cover_content (E : Set ℝ) :
    volume E = ⨅ (f : ℕ → Set ℝ) (_ : E ⊆ ⋃ n, f n),
      ∑' n, StieltjesFunction.id.length (f n) := by
  rw [Real.volume_eq_stieltjes_id,StieltjesFunction.measure]
  rfl

theorem exists_compact_interval_cover {E : Set ℝ} (hE : IsCompact E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (a b : ℕ → ℝ), E ⊆ ⋃ n ∈ s, Icc (a n) (b n) ∧
      (∑ n ∈ s, ENNReal.ofReal (b n-a n)) ≤ volume E+ENNReal.ofReal ε := by
  have hvol : volume E ≠ ∞ := hE.measure_lt_top.ne
  have hhalf : 0 < ENNReal.ofReal (ε/2) := ENNReal.ofReal_pos.mpr (by positivity)
  have hquarter : 0 < ENNReal.ofReal (ε/4) := ENNReal.ofReal_pos.mpr (by positivity)
  have hlt := ENNReal.lt_add_right hvol hhalf.ne'
  conv_lhs at hlt => rw [volume_eq_cover_content E]
  obtain ⟨f,hf,hcost⟩ := (by simpa only [iInf_lt_iff,exists_prop,StieltjesFunction.id_apply,id] using hlt :
    ∃ f : ℕ → Set ℝ, E ⊆ ⋃ n, f n ∧
      (∑' n, StieltjesFunction.id.length (f n)) < volume E+ENNReal.ofReal (ε/2))
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable hquarter.ne' ℕ
  have hfinite : (∑' n, StieltjesFunction.id.length (f n)) < ∞ :=
    hcost.trans (ENNReal.add_lt_top.mpr ⟨hvol.lt_top,ENNReal.ofReal_lt_top⟩)
  have hinterval (n : ℕ) : ∃ a b : ℝ, f n ⊆ Ioo a (b+δ n) ∧
      ENNReal.ofReal (b+δ n-a) ≤ StieltjesFunction.id.length (f n)+(δ n : ℝ≥0∞)+δ n := by
    have hl : StieltjesFunction.id.length (f n) <
        StieltjesFunction.id.length (f n)+(δ n : ℝ≥0∞) :=
      ENNReal.lt_add_right ((ENNReal.le_tsum n).trans_lt hfinite).ne
        (ENNReal.coe_pos.mpr (hδ n)).ne'
    conv_lhs at hl => rw [StieltjesFunction.length_eq]
    obtain ⟨a,b,hab,hbound⟩ := (by simpa only [iInf_lt_iff,exists_prop,StieltjesFunction.id_apply,id] using hl :
      ∃ a b : ℝ, f n \ botSet ⊆ Ioc a b ∧ ENNReal.ofReal (b-a) <
        StieltjesFunction.id.length (f n)+(δ n : ℝ≥0∞))
    refine ⟨a,b,?_,?_⟩
    · intro x hx
      have hxb := hab ⟨hx,notMem_botSet_of_lt (show x-1 < x by linarith)⟩
      exact ⟨hxb.1,lt_of_le_of_lt hxb.2 (by exact lt_add_of_pos_right b (hδ n))⟩
    · calc
        _ = ENNReal.ofReal ((b-a)+(δ n : ℝ)) := by congr 1; ring
        _ ≤ ENNReal.ofReal (b-a)+ENNReal.ofReal (δ n : ℝ) := ENNReal.ofReal_add_le
        _ ≤ _ := by simpa only [ENNReal.ofReal_coe_nnreal] using add_le_add hbound.le (le_refl (δ n : ℝ≥0∞))
  choose a b hcover hlength using hinterval
  have hEc : E ⊆ ⋃ n, Ioo (a n) (b n+δ n) := hf.trans (Set.iUnion_mono hcover)
  obtain ⟨s,hs⟩ := hE.elim_finite_subcover (fun n => Ioo (a n) (b n+δ n))
    (fun _ => isOpen_Ioo) hEc
  refine ⟨s,a,fun n => b n+δ n,hs.trans ?_,?_⟩
  · exact Set.iUnion₂_mono (fun _ _ => Ioo_subset_Icc_self)
  · calc
      _ ≤ ∑' n, ENNReal.ofReal (b n+δ n-a n) := ENNReal.sum_le_tsum s
      _ ≤ ∑' n, (StieltjesFunction.id.length (f n)+(δ n : ℝ≥0∞)+δ n) :=
        ENNReal.tsum_le_tsum hlength
      _ = (∑' n, StieltjesFunction.id.length (f n))+(∑' n, (δ n : ℝ≥0∞))+
          (∑' n, (δ n : ℝ≥0∞)) := by rw [ENNReal.tsum_add,ENNReal.tsum_add]
      _ ≤ (volume E+ENNReal.ofReal (ε/2))+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) :=
        add_le_add (add_le_add hcost.le hδsum.le) hδsum.le
      _ = _ := by
        rw [add_assoc,add_assoc,← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring

end TransposeFollowup.AffineMotion

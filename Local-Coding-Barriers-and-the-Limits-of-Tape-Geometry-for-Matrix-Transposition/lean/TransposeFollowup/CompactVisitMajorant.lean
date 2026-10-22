import TransposeFollowup.CompactIntervalCover
import Transpose.Tape.MStarAnalysis
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Set.Card.Arithmetic

/-! The original interval indicatrix majorant, localized to compact time
sets by finite interval covers. We import the interval theorem and the
Lipschitz extension theorem instead of reproving either one. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem interval_visit_majorant {K : NNReal} {P : ℝ → ℝ}
    (hP : LipschitzWith K P) (a b : ℝ) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ p, ({x | x ∈ Icc a b ∧ P x=p}.encard : ℝ≥0∞) ≤ F p) ∧
      (∫⁻ p, F p) ≤ K*ENNReal.ofReal (b-a) := by
  have hQ : LipschitzWith K (fun x : ℝ => P (x+a)) := by
    intro x y
    simpa only [edist_add_right] using hP (x+a) (y+a)
  obtain ⟨F,hF,hdom,hint⟩ := Impl.levelSet_encard_majorant (c₀:=b-a) hQ.lipschitzOnWith
  refine ⟨F,hF,?_,hint⟩
  intro p
  have he : {x | x ∈ Icc a b ∧ P x=p}=
      (fun x : ℝ => x+a) '' levelSet (fun x => P (x+a)) (b-a) p := by
    ext x
    constructor
    · rintro ⟨⟨hx1,hx2⟩,hp⟩
      refine ⟨x-a,⟨⟨by linarith,by linarith⟩,?_⟩,by ring⟩
      simpa only [sub_add_cancel] using hp
    · rintro ⟨y,⟨⟨hy1,hy2⟩,hp⟩,rfl⟩
      exact ⟨⟨by linarith,by linarith⟩,hp⟩
  have hi : Function.Injective (fun x : ℝ => x+a) := fun _ _ h => add_right_cancel h
  rw [he,hi.encard_image]
  exact hdom p

theorem compact_visit_majorant {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith 1 P (Icc 0 c₀)) {E : Set ℝ} (hE : IsCompact E)
    (hEI : E ⊆ Icc 0 c₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ p, ({x | x ∈ E ∧ P x=p}.encard : ℝ≥0∞) ≤ F p) ∧
      (∫⁻ p, F p) ≤ volume E+ENNReal.ofReal ε := by
  obtain ⟨g,hg,hPg⟩ := hP.extend_real
  obtain ⟨s,a,b,hcover,hlength⟩ := exists_compact_interval_cover hE hε
  choose F hFm hFd hFi using fun n => interval_visit_majorant hg (a n) (b n)
  refine ⟨fun p => ∑ n ∈ s, F n p,Finset.measurable_sum _ (fun n _ => hFm n),?_,?_⟩
  · intro p
    let V (n : ℕ) := {x | x ∈ Icc (a n) (b n) ∧ g x=p}
    have hsub : {x | x ∈ E ∧ P x=p} ⊆ ⋃ n ∈ s, V n := by
      rintro x ⟨hx,hp⟩
      obtain ⟨n,hn,hxn⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact Set.mem_iUnion₂.mpr ⟨n,hn,hxn,(hPg (hEI hx)).symm.trans hp⟩
    have hc := (Set.encard_mono hsub).trans (s.set_encard_biUnion_le V)
    calc
      _ ≤ ((∑ n ∈ s, (V n).encard : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono hc
      _ = ∑ n ∈ s, ((V n).encard : ℝ≥0∞) := map_sum ENat.toENNRealRingHom _ _
      _ ≤ _ := Finset.sum_le_sum (fun n _ => hFd n p)
  · rw [lintegral_finsetSum _ (fun n _ => hFm n)]
    exact (Finset.sum_le_sum (fun n _ => by simpa only [ENNReal.coe_one,one_mul] using hFi n)).trans hlength

theorem lintegral_compact_visits_le {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith 1 P (Icc 0 c₀)) {E : Set ℝ} (hE : IsCompact E)
    (hEI : E ⊆ Icc 0 c₀) :
    (∫⁻ p, ({x | x ∈ E ∧ P x=p}.encard : ℝ≥0∞)) ≤ volume E := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨F,_,hdom,hint⟩ := compact_visit_majorant hP hE hEI (ε:=(ε : ℝ)) hε
  exact (lintegral_mono hdom).trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hint)

end TransposeFollowup.AffineMotion

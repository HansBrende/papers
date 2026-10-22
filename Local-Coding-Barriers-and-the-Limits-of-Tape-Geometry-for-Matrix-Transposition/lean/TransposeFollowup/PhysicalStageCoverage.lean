import TransposeFollowup.StageRealGeometry
import TransposeFollowup.StageClockAccounting

/-! Physical-time shallow coverage derived from the actual finite stage clock
and child-charge contraction. The stage-key family is finite independently of
execution length; all measure and normalization identities are proved. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem finite_shallow_stage_keys (B J h : ℕ) :
    {p : List (Fin B) × Fin J | p.1.length < h}.Finite := by
  apply ((finite_addresses_lt_depth B h).prod (Set.finite_univ : (Set.univ : Set (Fin J)).Finite)).subset
  intro p hp
  exact ⟨hp,Set.mem_univ _⟩

theorem stage_clock_physical_omission {B J T : ℕ} {V : List (Fin B) → ℝ} {rho a P : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a) (hP : 0 < P)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w) (h : ℕ) :
    volume.real (Ico (0 : ℝ) ((T : ℝ)/P) \
      stageRegion (fun p : List (Fin B) × Fin J => (A p.1 p.2 : ℝ)/P)
        (fun p => (E p.1 p.2 : ℝ)/P) {p | p.1.length < h}) ≤
      (a*V []*rho^h/(1-rho))/P := by
  have hs : ∀ p (t : Fin T), (A p.1 p.2 ≤ t.val ∧ t.val < E p.1 p.2) ↔ label t=p := by
    intro p t
    exact hstage p.1 p.2 t
  rw [stageRegion_scaled_omission_volume label (fun p => A p.1 p.2) (fun p => E p.1 p.2)
    (fun p => hE p.1 p.2) hs _ hP]
  have hb := stage_clock_deep_work_bound hV hr hr1 ha hc label A E hE hstage hbudget h
  simpa only [Set.mem_ofPred_eq,Nat.not_lt] using div_le_div_of_nonneg_right hb hP.le

theorem stage_clock_physical_omission_of_root_bound
    {B J T : ℕ} {V : List (Fin B) → ℝ} {rho a P C : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a) (hP : 0 < P)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w) (hroot : V [] ≤ C*P)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w) (h : ℕ) :
    volume.real (Ico (0 : ℝ) ((T : ℝ)/P) \
      stageRegion (fun p : List (Fin B) × Fin J => (A p.1 p.2 : ℝ)/P)
        (fun p => (E p.1 p.2 : ℝ)/P) {p | p.1.length < h}) ≤
      a*C*rho^h/(1-rho) := by
  have hd : 0 < 1-rho := sub_pos.mpr hr1
  apply (stage_clock_physical_omission hV hr hr1 ha hP hc label A E hE hstage hbudget h).trans
  calc
    (a*V []*rho^h/(1-rho))/P ≤ (a*(C*P)*rho^h/(1-rho))/P := by gcongr
    _ = a*C*rho^h/(1-rho) := by field_simp

end TransposeFollowup.RegularMotion

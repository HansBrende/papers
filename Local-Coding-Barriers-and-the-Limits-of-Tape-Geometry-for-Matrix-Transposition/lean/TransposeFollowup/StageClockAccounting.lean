import TransposeFollowup.ContractingTickBudget

/-! Finite stage clocks: actual integer intervals partition all execution
ticks, yielding own-work costs and shallow-coverage deficits without assuming
the geometric tail estimate. Contiguous calls use the same ownership map. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

theorem finite_addresses_lt_depth (B h : ℕ) :
    {w : List (Fin B) | w.length < h}.Finite := by
  have hf : (⋃ n ∈ (Finset.range h : Set ℕ), Set.range (List.ofFn : (Fin n → Fin B) → List (Fin B))).Finite :=
    (Finset.finite_toSet _).biUnion (fun n _ => Set.finite_range _)
  apply hf.subset
  intro w hw
  exact Set.mem_iUnion.mpr ⟨w.length,Set.mem_iUnion.mpr
    ⟨Finset.mem_range.mpr hw,Set.mem_range.mpr ⟨w.get,List.ofFn_get w⟩⟩⟩

theorem stage_clock_own_ticks {B J T : ℕ}
    (label : Fin T → List (Fin B) × Fin J)
    (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (w : List (Fin B)) :
    (Finset.univ.filter (fun t : Fin T => (label t).1=w)).card=
      ∑ j : Fin J, (E w j-A w j) := by
  rw [Finset.card_eq_sum_card_fiberwise (t:=Finset.univ) (f:=fun t : Fin T => (label t).2)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (Finset.univ.filter (fun t : Fin T => (label t).1=w)).filter
      (fun t => (label t).2=j)=Finset.univ.filter (fun t : Fin T => A w j ≤ t.val ∧ t.val < E w j) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hstage,Prod.ext_iff]
  rw [heq,card_fin_time_interval (hE w j)]

theorem stage_clock_shallow_coverage {B J T h : ℕ}
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (t : Fin T) :
    (∃ w j, w.length < h ∧ A w j ≤ t.val ∧ t.val < E w j) ↔ (label t).1.length < h := by
  constructor
  · rintro ⟨w,j,hw,ht⟩
    rw [(hstage w j t).mp ht]
    exact hw
  · intro ht
    exact ⟨(label t).1,(label t).2,ht,(hstage _ _ t).mpr (Prod.eta _)⟩

theorem stage_clock_deep_work_bound {B J T : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w) (h : ℕ) :
    ((Finset.univ.filter (fun t : Fin T => h ≤ (label t).1.length)).card : ℝ) ≤
      a*V []*rho^h/(1-rho) := by
  apply deep_assigned_tick_bound hV hr hr1 ha hc Finset.univ (fun t => (label t).1) h
  intro w
  rw [stage_clock_own_ticks label A E hE hstage w]
  exact hbudget w

theorem stage_clock_total_time_bound {B J T : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w) :
    (T : ℝ) ≤ a*V []/(1-rho) := by
  simpa using stage_clock_deep_work_bound hV hr hr1 ha hc label A E hE hstage hbudget 0

theorem stage_clock_call_duration_bound {B J T C D : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w)
    (w : List (Fin B)) (hD : D ≤ T)
    (hcall : ∀ t : Fin T, (C ≤ t.val ∧ t.val < D) ↔ w <+: (label t).1) :
    ((D-C : ℕ) : ℝ) ≤ a*V w/(1-rho) := by
  apply contiguous_call_duration_bound hV hr hr1 ha hc (fun t => (label t).1) w hD hcall
  intro u
  rw [stage_clock_own_ticks label A E hE hstage u]
  exact hbudget u

theorem stage_clock_shallow_deficit {B J T : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (label : Fin T → List (Fin B) × Fin J) (A E : List (Fin B) → Fin J → ℕ)
    (hE : ∀ w j, E w j ≤ T)
    (hstage : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j))
    (hbudget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w) (h : ℕ) :
    (T : ℝ)-((Finset.univ.filter (fun t : Fin T =>
      ∃ w j, w.length < h ∧ A w j ≤ t.val ∧ t.val < E w j)).card : ℝ) ≤
      a*V []*rho^h/(1-rho) := by
  have heq : Finset.univ.filter (fun t : Fin T =>
      ∃ w j, w.length < h ∧ A w j ≤ t.val ∧ t.val < E w j)=
      Finset.univ.filter (fun t : Fin T => (label t).1.length < h) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact stage_clock_shallow_coverage label A E hstage t
  rw [heq]
  have hcard := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (p:=fun t : Fin T => (label t).1.length < h)
  simp only [Nat.not_lt,Finset.card_univ,Fintype.card_fin] at hcard
  have hreal : ((Finset.univ.filter (fun t : Fin T => (label t).1.length < h)).card : ℝ)+
      ((Finset.univ.filter (fun t : Fin T => h ≤ (label t).1.length)).card : ℝ)=T := by exact_mod_cast hcard
  have hb := stage_clock_deep_work_bound hV hr hr1 ha hc label A E hE hstage hbudget h
  linarith

end TransposeFollowup.RegularMotion

import TransposeFollowup.LimitingStageCoverage
import Mathlib.Topology.Sequences

/-! A common subsequence for every normalized node volume, stage endpoint and
halting time, with disjoint stage interiors covering almost all execution time.
All compact bounds come from the actual clock and contraction budget. The
subsequence is extracted by mathlib's countable-product compactness theorem. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem exists_stage_clock_limit_cover
    {B J : ℕ} {T : ℕ → ℕ} {P : ℕ → ℝ} {V : ℕ → List (Fin B) → ℝ}
    {rho a C : ℝ}
    (hV : ∀ n w, 0 ≤ V n w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (ha : 0 ≤ a) (hP : ∀ n, 0 < P n)
    (hc : ∀ n w, ∑ b : Fin B, V n (w++[b]) ≤ rho*V n w)
    (hroot : ∀ n, V n [] ≤ C*P n)
    (label : ∀ n, Fin (T n) → List (Fin B) × Fin J)
    (A E : ℕ → List (Fin B) → Fin J → ℕ)
    (hAE : ∀ n w j, A n w j ≤ E n w j) (hE : ∀ n w j, E n w j ≤ T n)
    (hstage : ∀ n w j (t : Fin (T n)),
      (A n w j ≤ t.val ∧ t.val < E n w j) ↔ label n t=(w,j))
    (hbudget : ∀ n w, ((∑ j : Fin J, (E n w j-A n w j) : ℕ) : ℝ) ≤ a*V n w) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (H : ℝ) (l r : List (Fin B) × Fin J → ℝ)
      (v : List (Fin B) → ℝ),
      H ∈ Icc 0 (a*C/(1-rho)) ∧
      (∀ w, v w ∈ Icc 0 (C/(1-rho))) ∧
      Tendsto (fun n => (T (φ n) : ℝ)/P (φ n)) atTop (𝓝 H) ∧
      (∀ p, Tendsto (fun n => (A (φ n) p.1 p.2 : ℝ)/P (φ n)) atTop (𝓝 (l p))) ∧
      (∀ p, Tendsto (fun n => (E (φ n) p.1 p.2 : ℝ)/P (φ n)) atTop (𝓝 (r p))) ∧
      (∀ w, Tendsto (fun n => V (φ n) w/P (φ n)) atTop (𝓝 (v w))) ∧
      (∀ p, 0 ≤ l p ∧ l p ≤ r p ∧ r p ≤ H) ∧
      Pairwise (fun p q => Disjoint (Ico (l p) (r p)) (Ico (l q) (r q))) ∧
      volume (Icc 0 H \ ⋃ p, Ioo (l p) (r p))=0 := by
  have hden : 0 < 1-rho := sub_pos.mpr hr1
  have hvol (n : ℕ) (w : List (Fin B)) : V n w/P n ≤ C/(1-rho) := by
    have hw := sum_deep_charge_le (hV n) hr hr1 (hc n) [] 0 {w} (fun _ _ => Nat.zero_le _)
    simp only [List.nil_append,Finset.sum_singleton,pow_zero,mul_one] at hw
    calc
      V n w/P n ≤ (V n []/(1-rho))/P n := div_le_div_of_nonneg_right hw (hP n).le
      _ ≤ ((C*P n)/(1-rho))/P n :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hroot n) hden.le) (hP n).le
      _ = C/(1-rho) := by field_simp [(hP n).ne']
  have htime (n : ℕ) : (T n : ℝ)/P n ≤ a*C/(1-rho) := by
    have ht := stage_clock_total_time_bound (hV n) hr hr1 ha (hc n)
      (label n) (A n) (E n) (hE n) (hstage n) (hbudget n)
    calc
      (T n : ℝ)/P n ≤ (a*V n []/(1-rho))/P n := div_le_div_of_nonneg_right ht (hP n).le
      _ ≤ (a*(C*P n)/(1-rho))/P n :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hroot n) ha) hden.le) (hP n).le
      _ = a*C/(1-rho) := by field_simp [(hP n).ne']
  let vf (n : ℕ) (w : List (Fin B)) : Icc (0 : ℝ) (C/(1-rho)) :=
    ⟨V n w/P n,div_nonneg (hV n w) (hP n).le,hvol n w⟩
  let lf (n : ℕ) (p : List (Fin B) × Fin J) : Icc (0 : ℝ) (a*C/(1-rho)) :=
    ⟨(A n p.1 p.2 : ℝ)/P n,div_nonneg (Nat.cast_nonneg _) (hP n).le,
      (div_le_div_of_nonneg_right (by exact_mod_cast (hAE n p.1 p.2).trans (hE n p.1 p.2))
        (hP n).le).trans (htime n)⟩
  let rf (n : ℕ) (p : List (Fin B) × Fin J) : Icc (0 : ℝ) (a*C/(1-rho)) :=
    ⟨(E n p.1 p.2 : ℝ)/P n,div_nonneg (Nat.cast_nonneg _) (hP n).le,
      (div_le_div_of_nonneg_right (by exact_mod_cast hE n p.1 p.2) (hP n).le).trans (htime n)⟩
  let tf (n : ℕ) : Icc (0 : ℝ) (a*C/(1-rho)) :=
    ⟨(T n : ℝ)/P n,div_nonneg (Nat.cast_nonneg _) (hP n).le,htime n⟩
  let X := (List (Fin B) → Icc (0 : ℝ) (C/(1-rho))) ×
    ((List (Fin B) × Fin J) → Icc (0 : ℝ) (a*C/(1-rho))) ×
    ((List (Fin B) × Fin J) → Icc (0 : ℝ) (a*C/(1-rho))) × Icc (0 : ℝ) (a*C/(1-rho))
  obtain ⟨e,φ,hφ,he⟩ := CompactSpace.tendsto_subseq (fun n => ((vf n,lf n,rf n,tf n) : X))
  let H : ℝ := e.2.2.2
  let l : List (Fin B) × Fin J → ℝ := fun p => e.2.1 p
  let r : List (Fin B) × Fin J → ℝ := fun p => e.2.2.1 p
  let v : List (Fin B) → ℝ := fun w => e.1 w
  have hH : Tendsto (fun n => (T (φ n) : ℝ)/P (φ n)) atTop (𝓝 H) :=
    (show Continuous (fun z : X => (z.2.2.2 : ℝ)) by dsimp [X]; fun_prop).continuousAt.tendsto.comp he
  have hl (p : List (Fin B) × Fin J) :
      Tendsto (fun n => (A (φ n) p.1 p.2 : ℝ)/P (φ n)) atTop (𝓝 (l p)) :=
    (show Continuous (fun z : X => (z.2.1 p : ℝ)) by dsimp [X]; fun_prop).continuousAt.tendsto.comp he
  have hre (p : List (Fin B) × Fin J) :
      Tendsto (fun n => (E (φ n) p.1 p.2 : ℝ)/P (φ n)) atTop (𝓝 (r p)) :=
    (show Continuous (fun z : X => (z.2.2.1 p : ℝ)) by dsimp [X]; fun_prop).continuousAt.tendsto.comp he
  have hv (w : List (Fin B)) :
      Tendsto (fun n => V (φ n) w/P (φ n)) atTop (𝓝 (v w)) :=
    (show Continuous (fun z : X => (z.1 w : ℝ)) by dsimp [X]; fun_prop).continuousAt.tendsto.comp he
  refine ⟨φ,hφ,H,l,r,v,e.2.2.2.property,(fun w => (e.1 w).property),hH,hl,hre,hv,?_,?_,?_⟩
  · intro p
    refine ⟨(e.2.1 p).property.1,?_,?_⟩
    · exact le_of_tendsto_of_tendsto' (hl p) (hre p) (fun n =>
        div_le_div_of_nonneg_right (by exact_mod_cast hAE (φ n) p.1 p.2) (hP (φ n)).le)
    · exact le_of_tendsto_of_tendsto' (hre p) hH (fun n =>
        div_le_div_of_nonneg_right (by exact_mod_cast hE (φ n) p.1 p.2) (hP (φ n)).le)
  · have hd : Set.univ.PairwiseDisjoint (fun p => Ico (l p) (r p)) := by
      apply stage_intervals_disjoint_of_tendsto (fun p _ => hl p) (fun p _ => hre p)
      apply Eventually.of_forall
      intro n p hp q hq hpq
      exact real_stages_scaled_pairwise_disjoint (hP (φ n)) (label (φ n))
        (fun p => A (φ n) p.1 p.2) (fun p => E (φ n) p.1 p.2)
        (fun p => hE (φ n) p.1 p.2) (fun p t => hstage (φ n) p.1 p.2 t) hpq
    exact fun p q hpq => hd (Set.mem_univ p) (Set.mem_univ q) hpq
  · apply geometric_stage_open_cover hr hr1
    intro h
    exact stage_clock_limit_shallow_omission (fun n => hV (φ n)) hr hr1 ha
      (fun n => hP (φ n)) (fun n => hc (φ n)) (fun n => hroot (φ n))
      (fun n => label (φ n)) (fun n => A (φ n)) (fun n => E (φ n))
      (fun n => hAE (φ n)) (fun n => hE (φ n)) (fun n => hstage (φ n))
      (fun n => hbudget (φ n)) hl hre hH h

theorem stage_duration_limit_bound {J : ℕ} {A E : ℕ → Fin J → ℕ}
    {V P : ℕ → ℝ} {a l r v : ℝ} (hP : ∀ n, 0 < P n)
    (hAE : ∀ n j, A n j ≤ E n j)
    (hbudget : ∀ n, ((∑ j : Fin J, (E n j-A n j) : ℕ) : ℝ) ≤ a*V n)
    (j : Fin J)
    (hl : Tendsto (fun n => (A n j : ℝ)/P n) atTop (𝓝 l))
    (hr : Tendsto (fun n => (E n j : ℝ)/P n) atTop (𝓝 r))
    (hv : Tendsto (fun n => V n/P n) atTop (𝓝 v)) : r-l ≤ a*v := by
  apply le_of_tendsto_of_tendsto' (hr.sub hl) (hv.const_mul a)
  intro n
  have hs : E n j-A n j ≤ ∑ k : Fin J, (E n k-A n k) :=
    Finset.single_le_sum (f:=fun k : Fin J => E n k-A n k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hb : ((E n j-A n j : ℕ) : ℝ) ≤ a*V n :=
    (show ((E n j-A n j : ℕ) : ℝ) ≤ ((∑ k : Fin J, (E n k-A n k) : ℕ) : ℝ)
      by exact_mod_cast hs).trans (hbudget n)
  calc
    (E n j : ℝ)/P n-(A n j : ℝ)/P n = ((E n j-A n j : ℕ) : ℝ)/P n := by
      rw [Nat.cast_sub (hAE n j),sub_div]
    _ ≤ (a*V n)/P n := div_le_div_of_nonneg_right hb (hP n).le
    _ = a*(V n/P n) := by ring

theorem zero_volume_call_duration_tendsto
    {B J : ℕ} {T S D : ℕ → ℕ} {P : ℕ → ℝ} {V : ℕ → List (Fin B) → ℝ}
    {rho a : ℝ} (hV : ∀ n w, 0 ≤ V n w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (ha : 0 ≤ a) (hP : ∀ n, 0 < P n)
    (hc : ∀ n w, ∑ b : Fin B, V n (w++[b]) ≤ rho*V n w)
    (label : ∀ n, Fin (T n) → List (Fin B) × Fin J)
    (A E : ℕ → List (Fin B) → Fin J → ℕ) (hE : ∀ n w j, E n w j ≤ T n)
    (hstage : ∀ n w j (t : Fin (T n)),
      (A n w j ≤ t.val ∧ t.val < E n w j) ↔ label n t=(w,j))
    (hbudget : ∀ n w, ((∑ j : Fin J, (E n w j-A n w j) : ℕ) : ℝ) ≤ a*V n w)
    (w : List (Fin B)) (hD : ∀ n, D n ≤ T n)
    (hcall : ∀ n (t : Fin (T n)), (S n ≤ t.val ∧ t.val < D n) ↔ w <+: (label n t).1)
    (hv : Tendsto (fun n => V n w/P n) atTop (𝓝 0)) :
    Tendsto (fun n => ((D n-S n : ℕ) : ℝ)/P n) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => (a/(1-rho))*(V n w/P n)) atTop (𝓝 0) := by
    simpa using hv.const_mul (a/(1-rho))
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (hP n).le))
    (Eventually.of_forall ?_) hu
  intro n
  have hb := stage_clock_call_duration_bound (hV n) hr hr1 ha (hc n)
    (label n) (A n) (E n) (hE n) (hstage n) (hbudget n) w (hD n) (hcall n)
  calc
    ((D n-S n : ℕ) : ℝ)/P n ≤ (a*V n w/(1-rho))/P n :=
      div_le_div_of_nonneg_right hb (hP n).le
    _ = (a/(1-rho))*(V n w/P n) := by ring

end TransposeFollowup.RegularMotion

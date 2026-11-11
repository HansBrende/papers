import AdaptiveTransfer.ClusterChart
import AdaptiveTransfer.ReplayMetadata

/-! Four bounded integer endpoints encode each protected core and fringe.
Their bounds are derived from a selected live time and actual unit-walk
head positions; no real chart description or endpoint certificate is stored.
-/

namespace AdaptiveTransfer
open Finset LeanMachine.ProtectedIntervals MergeDepth BoundedNesting NativeRelations
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def clusterEndpoints (a b : ℝ) (j : ℕ) : Fin 4 → ℤ :=
  ![⌈a - j⌉, ⌊a + j⌋, ⌈b - j⌉, ⌊b + j⌋]

noncomputable def endpointCore (e : Fin 4 → ℤ) : Finset ℤ := Ioo (e 1) (e 2)
noncomputable def endpointFringe (e : Fin 4 → ℤ) : Finset ℤ :=
  Icc (e 0) (e 1) ∪ Icc (e 2) (e 3)

@[simp] theorem endpointCore_actual (a b : ℝ) (j : ℕ) :
    endpointCore (clusterEndpoints a b j) = core a b j := rfl

@[simp] theorem endpointFringe_actual (a b : ℝ) (j : ℕ) :
    endpointFringe (clusterEndpoints a b j) = fringe a b j := rfl

private theorem abs_floor_le {x : ℝ} {n : ℕ} (hx : |x| ≤ (n : ℝ)) : |⌊x⌋| ≤ (n + 1 : ℕ) := by
  have hh : |((⌊x⌋ : ℤ) : ℝ)| ≤ (n : ℝ) + 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    rw [abs_le]
    constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  exact_mod_cast hh

private theorem abs_ceil_le {x : ℝ} {n : ℕ} (hx : |x| ≤ (n : ℝ)) : |⌈x⌉| ≤ (n + 1 : ℕ) := by
  have hh : |((⌈x⌉ : ℤ) : ℝ)| ≤ (n : ℝ) + 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    rw [abs_le]
    constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]
  exact_mod_cast hh

/-- A single actual selected position controls both chart endpoints. -/
theorem selected_chart_values_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {ell z : ℝ} {u : ℤ} {U W j : ℕ}
    (hu : |u| ≤ (U : ℤ)) (hz : ell ≤ z ∧ z < ell + W)
    (he : |(u : ℝ) - f z| ≤ j) :
    |f ell| ≤ (U : ℝ) + W + j ∧ |f (ell + W)| ≤ (U : ℝ) + W + j := by
  have hu' : |(u : ℝ)| ≤ (U : ℝ) := by exact_mod_cast hu
  have hl := hf.dist_le_mul ell z
  have hr := hf.dist_le_mul (ell + W) z
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl hr
  have hzl : |ell - z| ≤ (W : ℝ) := abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hzr : |ell + W - z| ≤ (W : ℝ) := abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hfl := abs_le.mp (hl.trans hzl)
  have hfr := abs_le.mp (hr.trans hzr)
  have hue := abs_le.mp he
  have huu := abs_le.mp hu'
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hfl.1, hfl.2, hfr.1, hfr.2, hue.1, hue.2, huu.1, huu.2]

theorem selected_chart_endpoints_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {ell z : ℝ} {u : ℤ} {U W j : ℕ}
    (hu : |u| ≤ (U : ℤ)) (hz : ell ≤ z ∧ z < ell + W)
    (he : |(u : ℝ) - f z| ≤ j) (i : Fin 4) :
    |clusterEndpoints (f ell) (f (ell + W)) j i| ≤ (U + W + 2 * j + 1 : ℕ) := by
  obtain ⟨hl, hr⟩ := selected_chart_values_bound hf hu hz he
  have ha : |f ell - j| ≤ (U + W + 2 * j : ℕ) := by
    have hh := abs_le.mp hl
    push_cast
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2, Nat.cast_nonneg (α := ℝ) j]
  have hb : |f ell + j| ≤ (U + W + 2 * j : ℕ) := by
    have hh := abs_le.mp hl
    push_cast
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2, Nat.cast_nonneg (α := ℝ) j]
  have hc : |f (ell + W) - j| ≤ (U + W + 2 * j : ℕ) := by
    have hh := abs_le.mp hr
    push_cast
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2, Nat.cast_nonneg (α := ℝ) j]
  have hd : |f (ell + W) + j| ≤ (U + W + 2 * j : ℕ) := by
    have hh := abs_le.mp hr
    push_cast
    rw [abs_le]
    constructor <;> linarith [hh.1, hh.2, Nat.cast_nonneg (α := ℝ) j]
  fin_cases i
  · exact abs_ceil_le ha
  · exact abs_floor_le hb
  · exact abs_ceil_le hc
  · exact abs_floor_le hd

def clusterEndpointBound (k T W j : ℕ) : ℕ := k * T + W + 2 * j + 2

theorem trace_work_abs_bound {k : ℕ} (τ : Trace k) {t U : ℕ} (ht : t ≤ U) (h : Fin k) :
    |τ.work h t| ≤ (U : ℤ) := by
  have hh := (τ.work_isWalk h).lip (Nat.zero_le t)
  rw [τ.work_zero h] at hh
  rw [abs_le]
  omega

namespace ClusterChart
variable {k L U W j : ℕ} {J : ℝ} {τ : Trace k} (g : ClusterChart τ.work L J)

/-- Endpoint bounds use the native trace's actual head bound at a live
selected time. The finite radius is exactly the manuscript's safe B*. -/
theorem endpoint_bounds {ell : ℤ} {t : ℕ} (ht : t < L) (htU : t ≤ U) (hj : J ≤ j)
    (hz : ell ≤ g.carrier t ∧ g.carrier t < ell + W) (h : g.Heads) (i : Fin 4) :
    |clusterEndpoints (g.map h ell) (g.map h (ell + W)) j i| ≤
      (clusterEndpointBound k U W j : ℤ) := by
  have hu : |clusterOrient (g.signature h.val) (τ.work h.val t)| ≤ (U : ℤ) := by
    simpa only [clusterOrient_abs] using trace_work_abs_bound τ htU h.val
  have hh := selected_chart_endpoints_bound (ell := (ell : ℝ)) (z := (g.carrier t : ℝ))
    (W := W) (j := j) (g.lipschitz h) hu
    (by exact_mod_cast hz) ((g.error t ht h).trans hj) i
  have hk := g.k_pos
  have hn : U + W + 2 * j + 1 ≤ clusterEndpointBound k U W j := by
    unfold clusterEndpointBound
    nlinarith
  exact hh.trans (by exact_mod_cast hn)

end ClusterChart
end AdaptiveTransfer

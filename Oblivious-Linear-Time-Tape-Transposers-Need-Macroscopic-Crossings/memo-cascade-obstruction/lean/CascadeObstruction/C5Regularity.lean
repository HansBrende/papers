import CascadeObstruction.C5ClockPaths
import CascadeObstruction.BlockApproximationPadding

/-! All actual fixed stages of C5 are regular. The finite-block bound may
grow with depth; the existing contracting clock pays the unbounded deep tail.
No limit profile, motion approximation or regularity premise is assumed. -/

namespace CascadeObstruction.C5

open TransposeFollowup.RegularMotion

set_option autoImplicit false

/-- Geometry holds for every sequence of positive widths, not only canonical
ones. Divergence of a selected stage's volume is part of the imported definition. -/
theorem clock_regular {K b : ℕ → ℕ} (hb : ∀ i, 0 < b i) (h : Fin 3) :
    RegularClockHead (fun i => clock (K i) (b i) (hb i))
      (fun i t => position (trace (K i) (b i)) h t) := by
  intro w j
  let J := 4 * 2 ^ w.length + 13
  let p (i : ℕ) : Fin J → Raster.Parameters 18 :=
    paddedBlockParameters (activeStage (K i) (b i) w.length j) h
      (clock_volume_pos (K i) (b i) (hb i) w)
      (activeStage_budget (K i) (b i) (hb i) w j) J
      (activeStage_blocks_bound (K i) (b i) w.length j)
  apply Raster.regular_of_ramp_approximation (C := 2 * (J : ℝ)) (by norm_num) p
  intro i s _hs
  rw [clock_stage_path]
  exact paddedBlockParameters_error (activeStage (K i) (b i) w.length j) h
    (clock_volume_pos (K i) (b i) (hb i) w)
    (activeStage_budget (K i) (b i) (hb i) w j) J
    (activeStage_blocks_bound (K i) (b i) w.length j) s

end CascadeObstruction.C5

import CascadeObstruction.BlockApproximationParameters

/-! Pad a physical block list with zero-duration blocks to obtain one fixed
finite parameter space for a sequence of stages. No execution tick is added. -/

namespace CascadeObstruction.C5

open scoped BigOperators

set_option autoImplicit false

def padBlocks (bs : List Block) (J : ℕ) : List Block :=
  bs ++ List.replicate (J - bs.length) (.straight 0 {})

theorem padBlocks_length (bs : List Block) (J : ℕ) (hJ : bs.length ≤ J) :
    (padBlocks bs J).length = J := by
  simp [padBlocks, hJ]

theorem expand_padBlocks (bs : List Block) (J : ℕ) :
    expand (padBlocks bs J) = expand bs := by
  simp [padBlocks, expand, Block.steps]

theorem blocksDuration_padBlocks (bs : List Block) (J : ℕ) :
    blocksDuration (padBlocks bs J) = blocksDuration bs := by
  rw [← expand_length, expand_padBlocks, expand_length]

noncomputable def paddedBlockParameters (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V)
    (J : ℕ) (hJ : bs.length ≤ J) : Fin J → Raster.Parameters a :=
  fun j => blockParameters (padBlocks bs J) h hV
    (by simpa only [blocksDuration_padBlocks] using hb)
    (finCongr (padBlocks_length bs J hJ).symm j)

theorem paddedBlockParameters_curve (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V)
    (J : ℕ) (hJ : bs.length ≤ J) (s : ℝ) :
    Raster.curve (paddedBlockParameters bs h hV hb J hJ) s =
      Raster.curve (blockParameters (padBlocks bs J) h hV
        (by simpa only [blocksDuration_padBlocks] using hb)) s := by
  unfold Raster.curve paddedBlockParameters
  exact (finCongr (padBlocks_length bs J hJ).symm).sum_comp
    (fun j : Fin (padBlocks bs J).length => Raster.ramp
      (blockParameters (padBlocks bs J) h hV
        (by simpa only [blocksDuration_padBlocks] using hb) j) s)

/-- A fixed `J`-ramp parameterization approximates the exact native tick word
with error `2J/V`; it applies even when the number of actual blocks varies. -/
theorem paddedBlockParameters_error (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V)
    (J : ℕ) (hJ : bs.length ≤ J) (s : ℝ) :
    dist (Raster.curve (paddedBlockParameters bs h hV hb J hJ) s)
      ((position (expand bs) h ⌊V * s⌋₊ : ℝ) / V) ≤ 2 * (J : ℝ) / V := by
  rw [paddedBlockParameters_curve]
  simpa only [expand_padBlocks, padBlocks_length bs J hJ] using
    blockParameters_error (padBlocks bs J) h hV
      (by simpa only [blocksDuration_padBlocks] using hb) s

end CascadeObstruction.C5

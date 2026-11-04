import BoundedStackDepth.CostModel
import BoundedStackDepth.FrameDynamics
import BoundedStackDepth.Decomposition
import BoundedStackDepth.Prominence

/-!
# The data of a hop in a frame system, and the summation of Theorem A

For a frame system `S` (the frames of one class of one walk) and a hop `e = (p, u)` of its walk:
* `bandP`, `bandU`: the bands `β(p)`, `β(u)`;
* `ownerScale`: `σ_τ = band (prom τ)` for the owner `τ` of the hop;
* `homeBand`: the band of `S = max_{c ∈ [p, u]} |x p − home c|`;
* `segScale F s`: the scale of the segment of `F` starting at `s` (the band of the largest distance from
  its home over its own times); `pushMax`: the largest scale of a segment starting in `(p, u]`
  (a frame start or a restart);
* `FrameMicro`: the segment of `u` started at or before `p`.

`Lost h₀ r e`: the hop is neither aligned nor ground at offset `r` (`CostModel.lean`), and `cstar` is its
cost `min(c, σ)`. **The summation of Theorem A** (`sum_card_lost_le_sum_cstar`,
`sum_cstar_le_of_ladders`): if every ladder of a top costs at most `C` times its height, the expected
number of lost upper hops is at most `C · #upper hops / h₀`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable (S : FrameSystem) (h₀ : ℕ)

/-- The band at the start of a hop. -/
noncomputable def bandP (e : ℕ × ℕ) : ℕ := S.beta e.1

/-- The band at the end of a hop. -/
noncomputable def bandU (e : ℕ × ℕ) : ℕ := S.beta e.2

/-- The scale of the owner of a hop: `band (prom τ)`. -/
noncomputable def ownerScale (e : ℕ × ℕ) : ℕ := band (prom S.x S.T (hopOwner S.x e.1 e.2))

/-- The band of the largest distance from the cell of a hop to a home active on it. -/
noncomputable def homeBand (e : ℕ × ℕ) : ℕ :=
  band ((Icc e.1 e.2).sup fun c => (S.x e.1 - S.home c).natAbs)

open Classical in
/-- The scale of the segment of `F` starting at `s`. -/
noncomputable def segScale (F : ℕ × ℕ) (s : ℕ) : ℕ :=
  band (((range S.T).filter fun t => S.Own F t ∧ S.segStart F t = s).sup
    fun t => (S.x t - S.x s).natAbs)

open Classical in
/-- The largest scale of a segment starting in `(p, u]`: at a frame start or a restart. -/
noncomputable def pushMax (e : ℕ × ℕ) : ℕ :=
  (S.frames ×ˢ Ioc e.1 e.2).sup fun Fs =>
    if Fs.2 = Fs.1.1 ∨ S.Restart Fs.1 Fs.2 then segScale S Fs.1 Fs.2 else 0

/-- The hop is frame-micro: the segment of `u` started at or before `p`. -/
def FrameMicro (e : ℕ × ℕ) : Prop := S.segStart (S.inner e.2) e.2 ≤ e.1

noncomputable instance (e : ℕ × ℕ) : Decidable (FrameMicro S e) := by unfold FrameMicro; infer_instance

/-- The hop is lost at offset `r`: neither aligned nor ground. -/
def Lost (r : ℕ) (e : ℕ × ℕ) : Prop :=
  ¬ Aligned h₀ r (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e) (pushMax S e)
      (FrameMicro S e) ∧ ¬ Ground h₀ r (ownerScale S e)

open Classical in
/-- The cost of a hop: `c* = min(c, σ)`. -/
noncomputable def cstar (e : ℕ × ℕ) : ℕ :=
  min (hopCost (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e) (pushMax S e) (FrameMicro S e))
    (ownerScale S e)

open Classical in
/-- **Exchange of sums.** Summed over the offsets, the lost hops of a set number at most the total
cost. -/
theorem sum_card_lost_le_sum_cstar (H : Finset (ℕ × ℕ)) :
    ∑ r ∈ range h₀, (H.filter (Lost S h₀ r)).card ≤ ∑ e ∈ H, cstar S e := by
  calc ∑ r ∈ range h₀, (H.filter (Lost S h₀ r)).card
      = ∑ e ∈ H, ((range h₀).filter (fun r => Lost S h₀ r e)).card := by
        simp only [card_eq_sum_ones, sum_filter]
        exact sum_comm
    _ ≤ ∑ e ∈ H, cstar S e := sum_le_sum fun e _ => by
        unfold cstar
        convert card_lost_le (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e)
          (pushMax S e) (FrameMicro S e) using 3
        exact Iff.rfl

/-- **Grouping by tops.** If the ladder of every top costs at most `C` times its height, the upper hops
cost at most `C` times their number. -/
theorem sum_cstar_le_of_ladders {x : ℕ → ℤ} {T C : ℕ} (f : ℕ × ℕ → ℕ)
    (hper : ∀ τ ∈ tops x T, ∑ e ∈ ladder x T τ, f e ≤ C * height x T τ) :
    ∑ e ∈ upperHops x T, f e ≤ C * (upperHops x T).card := by
  calc ∑ e ∈ upperHops x T, f e
      = ∑ τ ∈ tops x T, ∑ e ∈ ladder x T τ, f e :=
        (sum_fiberwise_of_maps_to (g := fun e : ℕ × ℕ => hopOwner x e.1 e.2)
          (fun _ he => mem_image_of_mem _ he) f).symm
    _ ≤ ∑ τ ∈ tops x T, C * height x T τ := sum_le_sum hper
    _ = C * (upperHops x T).card := by rw [← mul_sum, sum_height_eq]

end BoundedStackDepth

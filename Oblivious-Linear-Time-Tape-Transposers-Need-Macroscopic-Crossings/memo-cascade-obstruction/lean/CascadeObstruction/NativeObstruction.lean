import CascadeObstruction.ClockBudget
import CascadeObstruction.UniformGap
import TransposeFollowup.NativeRegularRecursion

/-! The native obstruction supplied by Paper 2, with a single combined
control-and-correctness-deficit hypothesis.

The actual clock witnesses and their regularity remain explicit hypotheses.
In particular, no theorem here identifies a Rust schedule with a native run.
-/

namespace CascadeObstruction

open Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.RegularMotion TransposeFollowup.AffineMotion

set_option autoImplicit false

/-- No high-rate native family with regular dyadic clocks has vanishing
normalized control bits plus integer correctness deficit.  The clock budget
also supplies the required linear running time. -/
theorem no_vanishing_native_dyadic_cost
    {k G : ℕ} {a : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM}
    (hk : ∀ i, (Ms i).k = k) (hG : ∀ i, cellBits (Ms i) = G)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop,
      2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hcost : Tendsto (fun i =>
      ((Nat.clog 2 ((Ms i).q + 1) : ℝ) + (ms i : ℝ)) /
        inputLength (ns i)) atTop (𝓝 0))
    (ha : 0 ≤ a)
    (hcorrect : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ,
      HaltsAt (Ms i) w T ∧
      (∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse =
          encode (ns i) (entryBits (ns i)) (transpose A)) ∧
      Nonempty (DyadicClock a (inputLength (ns i)) T))
    (hrec : HasRegularRecursiveExecutions 1 2 (1 / 2) a 1 ns Ms Ws hk) :
    False := by
  have hq : Tendsto (fun i =>
      (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => by positivity) _ hcost
    intro i
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity))
      (by positivity)
  have hmL : Tendsto (fun i =>
      (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => by positivity) _ hcost
    intro i
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity))
      (by positivity)
  exact no_native_regular_recursion hns hk hG hq hm hmL
    (by norm_num) (by norm_num) ha hcorrect hrec

/-- A finite correct native instance, together with the actual clock witness
for each correct input.  Stage regularity is a separate, family-level premise. -/
structure NativeDyadicInstance (k G : ℕ) (a : ℝ) (n : ℕ) where
  machine : TM
  tape_count : machine.k = k
  cell_bits : cellBits machine = G
  correctSet : Set (List Bool)
  deficit : ℕ
  count : 2 ^ inputLength n ≤ 2 ^ deficit * correctSet.ncard
  correct : ∀ w ∈ correctSet, ∃ T : ℕ,
    HaltsAt machine w T ∧
    (∃ A : Matrix, w = encode n (entryBits n) A ∧
      (run machine w T).outRev.reverse = encode n (entryBits n) (transpose A)) ∧
    Nonempty (DyadicClock a (inputLength n) T)

/-- Normalized controller bits plus a certified integer correctness deficit. -/
noncomputable def NativeDyadicInstance.cost {k G n : ℕ} {a : ℝ}
    (F : NativeDyadicInstance k G a n) : ℝ :=
  ((Nat.clog 2 (F.machine.q + 1) : ℝ) + (F.deficit : ℝ)) / inputLength n

/-- A class of native instances has an eventual uniform positive cost gap
provided every diverging sequence from the class has regular dyadic clocks.
The object type may encode any additional restrictions of the class. -/
theorem uniform_native_dyadic_gap {k G : ℕ} {a : ℝ} {Obj : ℕ → Type*}
    (family : ∀ n, Obj n → NativeDyadicInstance k G a n) (ha : 0 ≤ a)
    (hregular : ∀ (ns : ℕ → ℕ) (xs : ∀ i, Obj (ns i)),
      Tendsto ns atTop atTop →
      HasRegularRecursiveExecutions 1 2 (1 / 2) a 1 ns
        (fun i => (family (ns i) (xs i)).machine)
        (fun i => (family (ns i) (xs i)).correctSet)
        (fun i => (family (ns i) (xs i)).tape_count)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ x : Obj n, δ ≤ (family n x).cost := by
  apply exists_uniform_positive_gap (fun n x => (family n x).cost)
  · intro n x
    unfold NativeDyadicInstance.cost
    positivity
  · intro ns xs hns hcost
    exact no_vanishing_native_dyadic_cost hns
      (fun i => (family (ns i) (xs i)).tape_count)
      (fun i => (family (ns i) (xs i)).cell_bits)
      (Filter.Eventually.of_forall (fun i => (family (ns i) (xs i)).count))
      hcost ha
      (Filter.Eventually.of_forall (fun i => (family (ns i) (xs i)).correct))
      (hregular ns xs hns)

end CascadeObstruction

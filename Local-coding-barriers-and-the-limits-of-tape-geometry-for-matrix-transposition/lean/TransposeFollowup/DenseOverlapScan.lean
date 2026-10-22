import TransposeFollowup.IntegerOperandSize
import TransposeFollowup.LinearGenerationBudget

/-! An alternative exact row algorithm. Initialize row thresholds once,
then scan all target cells with two additions per advance. The existing
quadratic-logarithmic input budget permits this dense scan. Native signed
comparisons, initialization and output-record assembly remain to be wired. -/

namespace TransposeFollowup

set_option autoImplicit false

def crossingScan (dL dR : ℤ) : ℕ → ℤ × ℤ
  | 0 => (dL, 0)
  | j + 1 => let v := crossingScan dL dR j; (v.1 + dL, v.2 + dR)

theorem crossingScan_eq (dL dR : ℤ) (j : ℕ) :
    crossingScan dL dR j = (((j : ℤ) + 1) * dL, (j : ℤ) * dR) := by
  induction j with
  | zero => simp [crossingScan]
  | succ j ih =>
    simp only [crossingScan, ih, Nat.cast_add, Nat.cast_one]
    congr 1 <;> ring

structure RowCrossingTest where
  sourceOpen : Bool
  lower : ℤ
  upper : ℤ
  deltaLeft : ℤ
  deltaRight : ℤ

def RowCrossingTest.test (r : RowCrossingTest) (v : ℤ × ℤ) : Bool :=
  r.sourceOpen && decide (r.lower < v.1 ∧ v.2 < r.upper)

def RowCrossingTest.scan (r : RowCrossingTest) : ℕ → ℤ × ℤ → List Bool
  | 0, _ => []
  | k + 1, v => r.test v :: r.scan k (v.1 + r.deltaLeft, v.2 + r.deltaRight)

theorem RowCrossingTest.scan_length (r : RowCrossingTest) (k : ℕ) (v : ℤ × ℤ) :
    (r.scan k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [scan, ih]

theorem RowCrossingTest.scan_eq_range (r : RowCrossingTest) (k start : ℕ) :
    r.scan k (crossingScan r.deltaLeft r.deltaRight start) =
      (List.range k).map (fun j => r.test (crossingScan r.deltaLeft r.deltaRight (start + j))) := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    change r.test (crossingScan r.deltaLeft r.deltaRight start) ::
      r.scan k (crossingScan r.deltaLeft r.deltaRight (start + 1)) = _
    rw [ih]
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def,
      Nat.add_comm, Nat.add_left_comm]

theorem dense_scan_budget (A B n : ℕ) (hn : 1 ≤ n) :
    n * (n * (A + B * (n + 1).size)) ≤
      2 * (A + 3 * B) * Transpose.inputLength n := by
  calc
    _ ≤ n * ((n + 1) * (A + B * (n + 1).size)) := by gcongr; omega
    _ ≤ _ := linear_repetition_budget A B n hn

namespace RationalMobius

variable (F : RationalMobius)

def rowCrossingTest {n : ℕ} (i : Fin n) : RowCrossingTest :=
  let l := F.leftPair i
  let r := F.rightPair i
  let L := F.imagePair l
  let R := F.imagePair r
  ⟨decide (l.1 * r.2 < r.1 * l.2), L.1 * (n : ℤ), R.1 * (n : ℤ), L.2, R.2⟩

def denseHit {n : ℕ} (i : Fin n) (j : ℕ) : Bool :=
  let r := F.rowCrossingTest i
  r.test (crossingScan r.deltaLeft r.deltaRight j)

theorem denseHit_eq_integerOverlapTest {n : ℕ} (i j : Fin n) :
    F.denseHit i j.val = F.integerOverlapTest i j := by
  simp [denseHit, rowCrossingTest, RowCrossingTest.test, crossingScan_eq,
    integerOverlapTest]

def denseRow {n : ℕ} (i : Fin n) : List Bool :=
  let r := F.rowCrossingTest i
  r.scan n (r.deltaLeft, 0)

theorem denseRow_eq_range {n : ℕ} (i : Fin n) :
    F.denseRow i = (List.range n).map (F.denseHit i) := by
  change (F.rowCrossingTest i).scan n ((F.rowCrossingTest i).deltaLeft, 0) =
    (List.range n).map (fun j => (F.rowCrossingTest i).test
      (crossingScan (F.rowCrossingTest i).deltaLeft (F.rowCrossingTest i).deltaRight j))
  simpa only [crossingScan, Nat.zero_add] using
    RowCrossingTest.scan_eq_range (F.rowCrossingTest i) n 0

theorem denseRow_length {n : ℕ} (i : Fin n) : (F.denseRow i).length = n :=
  RowCrossingTest.scan_length _ _ _

theorem denseHit_spec {n : ℕ} (i j : Fin n) :
    F.denseHit i j.val = true ↔ F.bounded.Overlap i j := by
  rw [F.denseHit_eq_integerOverlapTest, F.integerOverlapTest_spec]

theorem crossingScan_bits {n : ℕ} (i : Fin n) (j : ℕ) (hj : j ≤ n) :
    let r := F.rowCrossingTest i
    let v := crossingScan r.deltaLeft r.deltaRight j
    v.1.natAbs.size ≤ (F.integerOperandConstant ^ 2).size + 2 * (n + 1).size + 1 ∧
    v.2.natAbs.size ≤ (F.integerOperandConstant ^ 2).size + 2 * (n + 1).size + 1 := by
  have hi := F.endpointImagePairs_bounds i
  have hn := Nat.le_mul_of_pos_left (n + 1) F.integerOperandConstant_pos
  have hJ : (j : ℤ).natAbs ≤ F.integerOperandConstant * (n + 1) := by
    simp only [Int.natAbs_natCast]; omega
  have hJ1 : ((j : ℤ) + 1).natAbs ≤ F.integerOperandConstant * (n + 1) := by omega
  dsimp only
  rw [crossingScan_eq]
  exact ⟨F.integerProduct_bits_le hJ1 hi.2.1, F.integerProduct_bits_le hJ hi.2.2.2⟩

end RationalMobius
end TransposeFollowup

import TransposeFollowup.SignedComponents

/-! A component-level version of the exact row formula. Its arithmetic uses
nonnegative components throughout; neither cancellation nor normalization
is used to shrink operands. This remains a reference circuit: clipping,
word loading, arithmetic calls and the whole row controller must be paid. -/

namespace TransposeFollowup

open SignedComponents
set_option autoImplicit false

structure ComponentRow where
  sourceLeft : Pair
  sourceRight : Pair
  lower : Pair
  upper : Pair
  deltaLeft : Pair
  deltaRight : Pair

def ComponentRow.integerTest (r : ComponentRow) : RowCrossingTest :=
  ⟨r.sourceLeft.less r.sourceRight, r.lower.denote, r.upper.denote,
    r.deltaLeft.denote, r.deltaRight.denote⟩

def ComponentRow.hit (r : ComponentRow) (j : ℕ) : Bool :=
  let v := SignedComponents.scan r.deltaLeft r.deltaRight j
  r.sourceLeft.less r.sourceRight && r.lower.less v.1 && v.2.less r.upper

theorem ComponentRow.hit_spec (r : ComponentRow) (j : ℕ) :
    r.hit j = r.integerTest.test
      (crossingScan r.integerTest.deltaLeft r.integerTest.deltaRight j) := by
  have h := scan_denote r.deltaLeft r.deltaRight j
  apply Bool.eq_iff_iff.mpr
  change (r.sourceLeft.less r.sourceRight &&
    r.lower.less (SignedComponents.scan r.deltaLeft r.deltaRight j).1 &&
    (SignedComponents.scan r.deltaLeft r.deltaRight j).2.less r.upper) = true ↔
    (r.sourceLeft.less r.sourceRight && decide
      (r.lower.denote < (crossingScan r.deltaLeft.denote r.deltaRight.denote j).1 ∧
        (crossingScan r.deltaLeft.denote r.deltaRight.denote j).2 < r.upper.denote)) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq, less_spec]
  rw [← h]
  simp only
  tauto

namespace RationalMobius

variable (F : RationalMobius)

def endpointComponents (x : ℤ × ℤ) : Pair × Pair := (Pair.ofInt x.1, Pair.ofInt x.2)

def imageComponents (x : Pair × Pair) : Pair × Pair :=
  (((Pair.ofInt F.integralA).mul x.1).add ((Pair.ofInt F.integralB).mul x.2),
    ((Pair.ofInt F.integralC).mul x.1).add ((Pair.ofInt F.integralD).mul x.2))

theorem imageComponents_denote (x : Pair × Pair) :
    ((F.imageComponents x).1.denote, (F.imageComponents x).2.denote) =
      F.imagePair (x.1.denote, x.2.denote) := by
  simp only [imageComponents, add_denote, mul_denote, ofInt_denote,
    imagePair, integerNumerator, integerDenominator]

theorem imageComponents_mass (x : Pair × Pair) (H : ℕ)
    (h : x.1.mass ≤ H ∧ x.2.mass ≤ H) :
    (F.imageComponents x).1.mass ≤ F.integerMagnitude * H ∧
    (F.imageComponents x).2.mass ≤ F.integerMagnitude * H := by
  have hn : F.integralA.natAbs + F.integralB.natAbs ≤ F.integerMagnitude := by
    dsimp [integerMagnitude]; omega
  have hd : F.integralC.natAbs + F.integralD.natAbs ≤ F.integerMagnitude := by
    dsimp [integerMagnitude]; omega
  simp only [imageComponents, add_mass, mul_mass, ofInt_mass]
  constructor
  · calc
      _ ≤ F.integralA.natAbs * H + F.integralB.natAbs * H :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h.1) (Nat.mul_le_mul_left _ h.2)
      _ = (F.integralA.natAbs + F.integralB.natAbs) * H := by ring
      _ ≤ _ := Nat.mul_le_mul_right H hn
  · calc
      _ ≤ F.integralC.natAbs * H + F.integralD.natAbs * H :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h.1) (Nat.mul_le_mul_left _ h.2)
      _ = (F.integralC.natAbs + F.integralD.natAbs) * H := by ring
      _ ≤ _ := Nat.mul_le_mul_right H hd

def componentRow {n : ℕ} (i : Fin n) : ComponentRow :=
  let l := endpointComponents (F.leftPair i)
  let r := endpointComponents (F.rightPair i)
  let L := F.imageComponents l
  let R := F.imageComponents r
  ⟨l.1.mul r.2, r.1.mul l.2, L.1.scale n, R.1.scale n, L.2, R.2⟩

theorem componentRow_integerTest {n : ℕ} (i : Fin n) :
    (F.componentRow i).integerTest = F.rowCrossingTest i := by
  have he (x : ℤ × ℤ) :
      (F.imageComponents (endpointComponents x)).1.denote = (F.imagePair x).1 ∧
      (F.imageComponents (endpointComponents x)).2.denote = (F.imagePair x).2 := by
    have h := F.imageComponents_denote (endpointComponents x)
    simp only [endpointComponents, ofInt_denote] at h
    exact Prod.mk.inj h
  have hs : ((Pair.ofInt (F.leftPair i).1).mul (Pair.ofInt (F.rightPair i).2)).less
      ((Pair.ofInt (F.rightPair i).1).mul (Pair.ofInt (F.leftPair i).2)) =
        decide ((F.leftPair i).1 * (F.rightPair i).2 < (F.rightPair i).1 * (F.leftPair i).2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [less_spec, mul_denote, ofInt_denote, decide_eq_true_eq]
  unfold componentRow ComponentRow.integerTest rowCrossingTest
  simp only [endpointComponents, scale_denote]
  rw [hs]
  have hL := he (F.leftPair i)
  have hR := he (F.rightPair i)
  simp only [endpointComponents] at hL hR
  rw [hL.1, hL.2, hR.1, hR.2]
  congr 1 <;> ring

theorem componentRow_hit {n : ℕ} (i : Fin n) (j : ℕ) :
    (F.componentRow i).hit j = F.denseHit i j := by
  rw [ComponentRow.hit_spec, F.componentRow_integerTest]
  rfl

theorem componentRow_overlap {n : ℕ} (i j : Fin n) :
    (F.componentRow i).hit j.val = true ↔ F.bounded.Overlap i j := by
  rw [F.componentRow_hit, F.denseHit_spec]

theorem componentImage_endpoint_bounds {n : ℕ} (i : Fin n) :
    let L := F.imageComponents (endpointComponents (F.leftPair i))
    let R := F.imageComponents (endpointComponents (F.rightPair i))
    L.1.mass ≤ F.integerOperandConstant*(n+1) ∧
    L.2.mass ≤ F.integerOperandConstant*(n+1) ∧
    R.1.mass ≤ F.integerOperandConstant*(n+1) ∧
    R.2.mass ≤ F.integerOperandConstant*(n+1) := by
  have hl := F.imageComponents_mass (endpointComponents (F.leftPair i))
    (F.arithmeticConstant*(n+1)) (by simpa [endpointComponents, ofInt_mass] using F.leftPair_bounds i)
  have hr := F.imageComponents_mass (endpointComponents (F.rightPair i))
    (F.arithmeticConstant*(n+1)) (by simpa [endpointComponents, ofInt_mass] using F.rightPair_bounds i)
  simpa only [integerOperandConstant, Nat.mul_assoc] using ⟨hl.1, hl.2, hr.1, hr.2⟩

/-- Every pair used in the three comparisons has controlled total mass,
including both stored crossing states through the final increment j=n. -/
theorem componentRow_mass_bounds {n : ℕ} (i : Fin n) (j : ℕ) (hj : j ≤ n) :
    let r := F.componentRow i
    let v := SignedComponents.scan r.deltaLeft r.deltaRight j
    ∀ p ∈ [r.sourceLeft, r.sourceRight, r.lower, r.upper, v.1, v.2],
      p.mass ≤ F.integerOperandConstant^2*(n+1)^2 := by
  have he := F.endpointPairs_bounds i
  have hi := F.componentImage_endpoint_bounds i
  have hE := F.integerOperandConstant_pos
  have hscale : n * (F.integerOperandConstant*(n+1)) ≤ F.integerOperandConstant^2*(n+1)^2 := by
    have h1 : n ≤ F.integerOperandConstant*(n+1) := by nlinarith
    calc
      _ ≤ (F.integerOperandConstant*(n+1))*(F.integerOperandConstant*(n+1)) := Nat.mul_le_mul_right _ h1
      _ = _ := by ring
  have hscan := scan_mass_bounds F.integerOperandConstant n j
    (F.componentRow i).deltaLeft (F.componentRow i).deltaRight hj hi.2.1 hi.2.2.2
  have hmore : F.integerOperandConstant*(n+1)^2 ≤ F.integerOperandConstant^2*(n+1)^2 := by
    apply Nat.mul_le_mul_right
    nlinarith
  dsimp only
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [componentRow, endpointComponents, mul_mass, ofInt_mass]
    calc
      _ ≤ (F.integerOperandConstant*(n+1))*(F.integerOperandConstant*(n+1)) := Nat.mul_le_mul he.1 he.2.2.2
      _ = _ := by ring
  · simp only [componentRow, endpointComponents, mul_mass, ofInt_mass]
    calc
      _ ≤ (F.integerOperandConstant*(n+1))*(F.integerOperandConstant*(n+1)) := Nat.mul_le_mul he.2.2.1 he.2.1
      _ = _ := by ring
  · calc
      _ ≤ n*(F.integerOperandConstant*(n+1)) := by
        simpa only [componentRow, scale_mass] using Nat.mul_le_mul_left n hi.1
      _ ≤ _ := hscale
  · calc
      _ ≤ n*(F.integerOperandConstant*(n+1)) := by
        simpa only [componentRow, scale_mass] using Nat.mul_le_mul_left n hi.2.2.1
      _ ≤ _ := hscale
  · exact hscan.1.trans hmore
  · exact hscan.2.trans hmore

/-- Fixed map-dependent constant plus twice the grid-size bit length. -/
def componentWidth (n : ℕ) : ℕ :=
  (F.integerOperandConstant^2).size + 2*(n+1).size + 2

/-- This includes both cross-sums for every comparison needed by the row.
No bound on a canceled signed difference is used in deriving the fit. -/
theorem componentRow_comparison_fit {n : ℕ} (i : Fin n) (j : ℕ) (hj : j ≤ n) :
    let r := F.componentRow i
    let v := SignedComponents.scan r.deltaLeft r.deltaRight j
    let operands := [r.sourceLeft, r.sourceRight, r.lower, r.upper, v.1, v.2]
    ∀ p ∈ operands, ∀ q ∈ operands,
      p.positive + q.negative < 2 ^ F.componentWidth n := by
  have hb := F.componentRow_mass_bounds i j hj
  dsimp only at hb ⊢
  intro p hp q hq
  have hpm := Nat.size_le.mp (natSize_le_poly (hb p hp))
  have hqm := Nat.size_le.mp (natSize_le_poly (hb q hq))
  have hfit := (comparison_fit p q _ hpm hqm).1
  simpa only [componentWidth, Nat.add_assoc] using hfit


end RationalMobius
end TransposeFollowup

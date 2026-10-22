import TransposeFollowup.TreewidthAverage

/-! Constant expected savings force linear average interaction-graph treewidth
in the adaptive original-row model. The proof permits arbitrary nonlinearity,
correlated correct families, helper-dependent strategies, and nontermination
outside the correct family. Graphs and separators depend on the actual leaf. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

section Protocol

variable {n b : ℕ} {H : Type*} [Fintype H]
    (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)

include hrun hcorrect

omit [Nonempty F] in
/-- A family of integral tests, before choosing the common component threshold.
No graph restriction or separator hypothesis remains in this statement. -/
theorem expected_treewidth_test_of_distribution
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) (L : ℕ) :
    ((L : ℝ) + 1) * ((n * n * b : ℕ) -
      (∑ x : F, w x * ((M x.val).length : ℝ)) -
      2 * ((n * n * b : ℕ) - entropy w / Real.log 2) -
      2 * (observationEntropy w (fun x : F => helper x.val) / Real.log 2)) ≤
      (b : ℝ) * n * (n *
        ((∑ x : F, w x *
          (treewidth ((strategy (helper x.val)).interactionGraph [] (M x.val)) : ℝ)) + 1) +
        L * (L + 1)) := by
  let graphs := fun z m => (strategy z).interactionGraph [] m
  let S := fun z m => treewidthLossSeparator b (graphs z m) L
  have hcode := graph_expected_separator_bound_of_distribution F w hw hw1 helper strategy decode M hrun hcorrect S
  have hsep := mean_treewidth_separator_loss w
    hw hw1
    (fun x : F => graphs (helper x.val) (M x.val)) b L
  have hbase : (n * n * b : ℕ) -
      (∑ x : F, w x * ((M x.val).length : ℝ)) -
      2 * ((n * n * b : ℕ) - entropy w / Real.log 2) -
      2 * (observationEntropy w (fun x : F => helper x.val) / Real.log 2) ≤
      ∑ x : F, w x *
        (graphSeparatorLoss b (graphs (helper x.val) (M x.val))
          (S (helper x.val) (M x.val)) : ℝ) := by
    dsimp [graphs] at *
    linarith
  exact (mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ (L : ℝ) + 1)).trans hsep

theorem expected_treewidth_test (L : ℕ) :
    ((L : ℝ) + 1) * ((n * n * b : ℕ) -
      (∑ x : F, uniformWeight F x * ((M x.val).length : ℝ)) -
      2 * ((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) -
      2 * (observationEntropy (uniformWeight F) (fun x : F => helper x.val) / Real.log 2)) ≤
      (b : ℝ) * n * (n *
        ((∑ x : F, uniformWeight F x *
          (treewidth ((strategy (helper x.val)).interactionGraph [] (M x.val)) : ℝ)) + 1) +
        L * (L + 1)) := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    expected_treewidth_test_of_distribution F helper strategy decode M hrun hcorrect
      (uniformWeight F) (uniformWeight_nonneg F) (sum_uniformWeight F) L

omit [Nonempty F] in
/-- For any input law, put P=n²b, D=P-H(X), and η=(D+H(Z))/P. Expected cost at most
(1-ε)P forces E tw(G) ≥ (n/4)(ε-2η)₊²+(ε-2η)₊/2-1. This strengthens the written
188 corollary's coefficient 1/9 and removes its additive 1/n rounding loss.
Queries may depend on arbitrarily many original rows; each support contributes
a clique to the public interaction graph. Coded-workspace access is not assumed. -/
theorem average_treewidth_lower_bound_of_distribution
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) (hn : 0 < n) (hb : 0 < b) (ε : ℝ)
    (hcost : (∑ x : F, w x * ((M x.val).length : ℝ)) ≤
      (1 - ε) * (n * n * b : ℕ)) :
    (∑ x : F, w x *
      (treewidth ((strategy (helper x.val)).interactionGraph [] (M x.val)) : ℝ)) ≥
      (n : ℝ) / 4 * (max (ε - 2 *
        (((n * n * b : ℕ) - entropy w / Real.log 2 +
          observationEntropy w (fun x : F => helper x.val) / Real.log 2) /
            (n * n * b : ℕ))) 0) ^ 2 +
      max (ε - 2 *
        (((n * n * b : ℕ) - entropy w / Real.log 2 +
          observationEntropy w (fun x : F => helper x.val) / Real.log 2) /
            (n * n * b : ℕ))) 0 / 2 - 1 := by
  let P : ℝ := (n * n * b : ℕ)
  let D : ℝ := P - entropy w / Real.log 2
  let HZ : ℝ := observationEntropy w (fun x : F => helper x.val) / Real.log 2
  let cost : ℝ := ∑ x : F, w x * ((M x.val).length : ℝ)
  let E : ℝ := ∑ x : F, w x *
    (treewidth ((strategy (helper x.val)).interactionGraph [] (M x.val)) : ℝ)
  let a : ℝ := ε - 2 * ((D + HZ) / P)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hP : 0 < P := by dsimp [P]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hw x) (Nat.cast_nonneg _)
  have hPa : P * a = ε * P - 2 * D - 2 * HZ := by
    dsimp [a]
    field_simp
    ring
  have hsaving : P * a ≤ P - cost - 2 * D - 2 * HZ := by
    rw [hPa]
    change cost ≤ (1 - ε) * P at hcost
    nlinarith
  have htests (L : ℕ) : (n : ℝ) * ((L : ℝ) + 1) * a ≤
      (n : ℝ) * (E + 1) + L * (L + 1) := by
    have hraw := expected_treewidth_test_of_distribution F helper strategy decode M hrun hcorrect w hw hw1 L
    change ((L : ℝ) + 1) * (P - cost - 2 * D - 2 * HZ) ≤
      (b : ℝ) * n * (n * (E + 1) + L * (L + 1)) at hraw
    have hscaled := (mul_le_mul_of_nonneg_left hsaving
      (by positivity : 0 ≤ (L : ℝ) + 1)).trans hraw
    have hcancel : ((b : ℝ) * n) * ((n : ℝ) * ((L : ℝ) + 1) * a) ≤
        ((b : ℝ) * n) * ((n : ℝ) * (E + 1) + L * (L + 1)) := by
      convert hscaled using 1
      dsimp [P]
      push_cast
      ring
    exact (mul_le_mul_iff_right₀ (mul_pos hbR hnR)).mp hcancel
  have hfinal := quadratic_bound_of_integer_tests (n : ℝ) (E + 1) a hnR
    (by linarith) htests
  change E ≥ (n : ℝ) / 4 * (max a 0) ^ 2 + max a 0 / 2 - 1
  linarith

theorem average_treewidth_lower_bound (hn : 0 < n) (hb : 0 < b) (ε : ℝ)
    (hcost : (∑ x : F, uniformWeight F x * ((M x.val).length : ℝ)) ≤
      (1 - ε) * (n * n * b : ℕ)) :
    (∑ x : F, uniformWeight F x *
      (treewidth ((strategy (helper x.val)).interactionGraph [] (M x.val)) : ℝ)) ≥
      (n : ℝ) / 4 * (max (ε - 2 *
        (((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 +
          observationEntropy (uniformWeight F) (fun x : F => helper x.val) / Real.log 2) /
            (n * n * b : ℕ))) 0) ^ 2 +
      max (ε - 2 *
        (((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 +
          observationEntropy (uniformWeight F) (fun x : F => helper x.val) / Real.log 2) /
            (n * n * b : ℕ))) 0 / 2 - 1 := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    average_treewidth_lower_bound_of_distribution F helper strategy decode M hrun hcorrect
      (uniformWeight F) (uniformWeight_nonneg F) (sum_uniformWeight F) hn hb ε hcost

end Protocol
end TransposeFollowup

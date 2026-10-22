import TransposeFollowup.AdaptiveLeaves

/-! Expected separator bound for finite public original-row protocols.
All comparison budgets and local decoding inequalities are proved from the
protocol. Extending the interface to trees that may diverge off the correct
family still requires the separate finite-truncation construction. -/

namespace TransposeFollowup.RowCode

open scoped BigOperators
open Classical
set_option autoImplicit false

noncomputable def separatorLoss {n b : ℕ} {H κ : Type*} [DecidableEq κ]
    (C : RowCode n b H) (S : H → List Bool → Finset (Fin n))
    (component : H → List Bool → Fin n → κ) (x : FiniteMatrix n b) : ℕ :=
  n * b * (S (C.helper x) (C.transcript x)).card +
    (internalFreeBits (b := b) (S (C.helper x) (C.transcript x))
      (component (C.helper x) (C.transcript x))).card

theorem leafLoss_leafOf {n b : ℕ} {H κ : Type*} [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (x : F) :
    C.leafLoss F S component (C.leafOf F S x) =
      (internalFreeBits (b := b) (S (C.helper x.val) (C.transcript x.val))
        (component (C.helper x.val) (C.transcript x.val))).card := by
  have hm : C.transcript x.val = (C.protocol (C.helper x.val)).run
      (C.leafRepresentative F S (C.leafOf F S x)) :=
    (C.leaf_key_data F S (C.leafOf F S x) x.val rfl).2.1
  change (internalFreeBits (b := b)
    (S (C.helper x.val) ((C.protocol (C.helper x.val)).run (C.leafRepresentative F S (C.leafOf F S x))))
    (component (C.helper x.val) ((C.protocol (C.helper x.val)).run
      (C.leafRepresentative F S (C.leafOf F S x))))).card = _
  rw [← hm]

theorem leaf_charge_loss {n b : ℕ} {H κ : Type*} [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (x : F) :
    (C.leafOf F S x).val.2.length + C.leafLoss F S component (C.leafOf F S x) =
      (C.transcript x.val).length + C.separatorLoss S component x.val := by
  have hlen : (C.leafOf F S x).val.2.length = (C.transcript x.val).length +
      n * b * (S (C.helper x.val) (C.transcript x.val)).card :=
    augmentedTranscript_length (C.protocol (C.helper x.val)) (S (C.helper x.val)) x.val
  rw [hlen, C.leafLoss_leafOf]
  simp only [separatorLoss, Nat.add_assoc]

/-- Expected-cost inequality in natural-log units, directly for the given
correct family and adaptive support-compatible partitions. -/
theorem expected_separator_bound_log_of_distribution {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x)) :
    2 * entropy w ≤ (n * n * b : ℕ) * Real.log 2 +
      2 * observationEntropy w (fun x : F => C.helper x.val) +
      (∑ x : F, w x *
        (((C.transcript x.val).length + C.separatorLoss S component x.val : ℕ) : ℝ)) * Real.log 2 := by
  have h := aggregate_leaf_bounds_of_distribution w hw hw1 (C.leafOf F S) (fun l => l.val.1)
    (n * n * b) (C.leafVolume F S) (fun l => l.val.2.length) (C.leafLoss F S component)
    (fun l _ => C.leafVolume_pos F S l) (C.leaf_log_bound F hc S component hsep)
    (C.leafVolume_budget F S) (C.leafCode_budget F S)
  rw [sum_pushforward_mul] at h
  simp_rw [C.leaf_charge_loss F S component] at h
  have hhelper : (fun l : C.Leaf F S => l.val.1) ∘ C.leafOf F S =
      fun x : F => C.helper x.val := rfl
  rw [hhelper] at h
  exact h

theorem expected_separator_bound_log {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x)) :
    2 * Real.log (F.card : ℝ) ≤ (n * n * b : ℕ) * Real.log 2 +
      2 * observationEntropy (uniformWeight F) (fun x : F => C.helper x.val) +
      (∑ x : F, uniformWeight F x *
        (((C.transcript x.val).length + C.separatorLoss S component x.val : ℕ) : ℝ)) * Real.log 2 := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    C.expected_separator_bound_log_of_distribution F (uniformWeight F)
      (uniformWeight_nonneg F) (sum_uniformWeight F) hc S component hsep

/-- Arbitrary-distribution separator bound: E length >= P - E L - 2D - 2H(Z),
where D=P-H(X) and both entropies are measured in bits under the supplied law. -/
theorem expected_separator_bound_of_distribution {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x)) :
    (∑ x : F, w x * ((C.transcript x.val).length : ℝ)) ≥
      (n * n * b : ℕ) - (∑ x : F, w x * (C.separatorLoss S component x.val : ℝ)) -
      2 * ((n * n * b : ℕ) - entropy w / Real.log 2) -
      2 * (observationEntropy w (fun x : F => C.helper x.val) / Real.log 2) := by
  have h := C.expected_separator_bound_log_of_distribution F w hw hw1 hc S component hsep
  simp_rw [Nat.cast_add, mul_add] at h
  rw [Finset.sum_add_distrib] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hlog).mp
  field_simp
  nlinarith

theorem expected_separator_bound {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x)) :
    (∑ x : F, uniformWeight F x * ((C.transcript x.val).length : ℝ)) ≥
      (n * n * b : ℕ) - (∑ x : F, uniformWeight F x * (C.separatorLoss S component x.val : ℝ)) -
      2 * ((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) -
      2 * (observationEntropy (uniformWeight F) (fun x : F => C.helper x.val) / Real.log 2) := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    C.expected_separator_bound_of_distribution F (uniformWeight F)
      (uniformWeight_nonneg F) (sum_uniformWeight F) hc S component hsep

/-- Worst-case consequence, charging only helper values actually attained
on the correct family. The ambient helper type may be much larger. -/
theorem worst_case_separator_bound {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x))
    (B L g : ℕ) (hB : ∀ x ∈ F, (C.transcript x).length ≤ B)
    (hL : ∀ x ∈ F, C.separatorLoss S component x ≤ L)
    (hg : (F.image C.helper).card ≤ 2 ^ g) :
    (B : ℝ) ≥ (n * n * b : ℕ) - L -
      2 * (((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) + g) := by
  classical
  have h := C.expected_separator_bound F hc S component hsep
  have hBmean : (∑ x : F, uniformWeight F x * ((C.transcript x.val).length : ℝ)) ≤ B := by
    calc
      _ ≤ ∑ x : F, uniformWeight F x * (B : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (uniformWeight_nonneg F x)
        exact_mod_cast hB x.val x.property
      _ = B := by rw [← Finset.sum_mul, sum_uniformWeight, one_mul]
  have hLmean : (∑ x : F, uniformWeight F x * (C.separatorLoss S component x.val : ℝ)) ≤ L := by
    calc
      _ ≤ ∑ x : F, uniformWeight F x * (L : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (uniformWeight_nonneg F x)
        exact_mod_cast hL x.val x.property
      _ = L := by rw [← Finset.sum_mul, sum_uniformWeight, one_mul]
  have hhelper := observationEntropy_le_log_support (uniformWeight F)
    (uniformWeight_nonneg F) (sum_uniformWeight F) (fun x : F => C.helper x.val)
    (F.image C.helper) (fun x => Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)
  have hpos : 0 < ((F.image C.helper).card : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    let x := Classical.arbitrary F
    exact ⟨C.helper x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
  have hlogcard : Real.log ((F.image C.helper).card : ℝ) ≤ (g : ℝ) * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ g) := Real.log_le_log hpos (by exact_mod_cast hg)
      _ = _ := Real.log_pow 2 g
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgH : observationEntropy (uniformWeight F) (fun x : F => C.helper x.val) / Real.log 2 ≤ g := by
    apply (div_le_iff₀ hlog).mpr
    exact hhelper.trans hlogcard
  linarith

end TransposeFollowup.RowCode

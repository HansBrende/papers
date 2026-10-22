import TransposeFollowup.AdaptiveSeparator
import TransposeFollowup.ProtocolTruncation

/-! The expected separator bound without requiring termination off the
correct family. A single finite truncation preserves all its charged runs. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

theorem strategy_expected_separator_bound_of_distribution {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (F : Finset (FiniteMatrix n b))
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (strategy (helper x)).Along
      (PublicProtocol.Separated (S (helper x) (M x)) (component (helper x) (M x))) [] (M x)) :
    (∑ x : F, w x * ((M x.val).length : ℝ)) ≥
      (n * n * b : ℕ) -
      (∑ x : F, w x *
        ((n * b * (S (helper x.val) (M x.val)).card +
          (internalFreeBits (b := b) (S (helper x.val) (M x.val))
            (component (helper x.val) (M x.val))).card : ℕ) : ℝ)) -
      2 * ((n * n * b : ℕ) - entropy w / Real.log 2) -
      2 * (observationEntropy w (fun x : F => helper x.val) / Real.log 2) := by
  obtain ⟨p, hM, hP⟩ := PublicStrategy.finite_family_truncation F helper strategy M hrun
  let C : RowCode n b H := ⟨helper, p, decode⟩
  have htrans : ∀ x ∈ F, C.transcript x = M x := hM
  have hc : C.CorrectOn (F : Set _) := by
    intro x hx j
    change decode (helper x) j (x j) (C.transcript x) = transposed x j
    rw [htrans x hx]
    exact hcorrect x hx j
  have hs : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x) := by
    intro x hx
    rw [htrans x hx]
    exact hP x hx _ (hsep x hx)
  have h := C.expected_separator_bound_of_distribution F w hw hw1 hc S component hs
  have htransF (x : F) : C.transcript x.val = M x.val := htrans x.val x.property
  simpa only [RowCode.separatorLoss, htransF] using h

theorem strategy_expected_separator_bound {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (strategy (helper x)).Along
      (PublicProtocol.Separated (S (helper x) (M x)) (component (helper x) (M x))) [] (M x)) :
    (∑ x : F, uniformWeight F x * ((M x.val).length : ℝ)) ≥
      (n * n * b : ℕ) -
      (∑ x : F, uniformWeight F x *
        ((n * b * (S (helper x.val) (M x.val)).card +
          (internalFreeBits (b := b) (S (helper x.val) (M x.val))
            (component (helper x.val) (M x.val))).card : ℕ) : ℝ)) -
      2 * ((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) -
      2 * (observationEntropy (uniformWeight F) (fun x : F => helper x.val) / Real.log 2) := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    strategy_expected_separator_bound_of_distribution F (uniformWeight F)
      (uniformWeight_nonneg F) (sum_uniformWeight F) helper strategy decode M hrun hcorrect
      S component hsep

/-- Worst-case form for public strategies that may diverge off F. -/
theorem strategy_worst_case_separator_bound {n b : ℕ} {H κ : Type*}
    [Fintype H] [Fintype κ] [DecidableEq κ]
    (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (strategy (helper x)).Along
      (PublicProtocol.Separated (S (helper x) (M x)) (component (helper x) (M x))) [] (M x))
    (B L g : ℕ) (hB : ∀ x ∈ F, (M x).length ≤ B)
    (hL : ∀ x ∈ F, n * b * (S (helper x) (M x)).card +
      (internalFreeBits (b := b) (S (helper x) (M x)) (component (helper x) (M x))).card ≤ L)
    (hg : (F.image helper).card ≤ 2 ^ g) :
    (B : ℝ) ≥ (n * n * b : ℕ) - L -
      2 * (((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) + g) := by
  obtain ⟨p, hM, hP⟩ := PublicStrategy.finite_family_truncation F helper strategy M hrun
  let C : RowCode n b H := ⟨helper, p, decode⟩
  have htrans : ∀ x ∈ F, C.transcript x = M x := hM
  have hc : C.CorrectOn (F : Set _) := by
    intro x hx j
    change decode (helper x) j (x j) (C.transcript x) = transposed x j
    rw [htrans x hx]
    exact hcorrect x hx j
  have hs : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x) := by
    intro x hx
    rw [htrans x hx]
    exact hP x hx _ (hsep x hx)
  apply C.worst_case_separator_bound F hc S component hs B L g _ _ hg
  · intro x hx
    rw [htrans x hx]
    exact hB x hx
  · intro x hx
    unfold RowCode.separatorLoss
    rw [htrans x hx]
    exact hL x hx

end TransposeFollowup

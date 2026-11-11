import SharedDecoders.ResidualRowColumn
import Mathlib.Algebra.Group.TransferInstance

/-! # Sharp helper attainment for arbitrary row-then-column families -/

namespace SharedDecoders.RowColumn

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {G : Type*} [AddCommGroup G]

abbrev PairIndex (d : ℕ) := {z : Sym2 (Fin d) // ¬z.IsDiag}
abbrev PairHelper (d : ℕ) (G : Type*) := PairIndex d → G

def pairIndex (i j : Fin d) (h : i ≠ j) : PairIndex d := ⟨s(i,j), by simpa using h⟩

/-- One oriented difference for each unordered pair of distinct indices. -/
def differenceHelper (X : Mat d G) : PairHelper d G := fun z =>
  Sym2.lift ⟨fun i j => X (min i j) (max i j) - X (max i j) (min i j), by
    intro i j
    dsimp
    rw [min_comm, max_comm]⟩ z.val

@[simp] theorem differenceHelper_pair {i j : Fin d} (hij : i < j) (X : Mat d G) :
    differenceHelper X (pairIndex i j hij.ne) = X i j - X j i := by
  simp only [differenceHelper, pairIndex, Sym2.lift_mk,
    min_eq_left hij.le, max_eq_right hij.le]

def helperColumns (h : PairHelper d G) : Family d G := fun j v i =>
  if hij : i < j then v i - h (pairIndex i j hij.ne)
  else if hji : j < i then v i + h (pairIndex j i hji.ne)
  else v i

/-- Actual complete transpose, using the whole fixed helper to select column maps. -/
theorem difference_helper_correct (X : Mat d G) :
    complete (fun _ => id) (helperColumns (differenceHelper X)) X = fun i j => X j i := by
  funext i j
  change (if hij : i < j then X i j - differenceHelper X (pairIndex i j hij.ne)
    else if hji : j < i then X i j + differenceHelper X (pairIndex j i hji.ne)
    else X i j) = X j i
  split_ifs with hij hji
  · rw [differenceHelper_pair hij]
    abel
  · rw [differenceHelper_pair hji]
    abel
  · have he : i = j := by omega
    subst j
    rfl

def matrixOfHelper (h : PairHelper d G) : Mat d G := fun i j =>
  if hij : i < j then h (pairIndex i j hij.ne) else 0

theorem difference_helper_surjective : Function.Surjective (differenceHelper (d := d) (G := G)) := by
  intro h
  refine ⟨matrixOfHelper h, ?_⟩
  funext z
  obtain ⟨z, hz⟩ := z
  induction z using Sym2.ind with
  | _ i j =>
    have hne : i ≠ j := by simpa using hz
    rcases lt_or_gt_of_ne hne with hij | hji
    · change differenceHelper (matrixOfHelper h) (pairIndex i j hne) = _
      rw [differenceHelper_pair hij]
      simp [matrixOfHelper, hij, not_lt_of_ge hij.le, pairIndex]
    · have he : (⟨s(i,j), hz⟩ : PairIndex d) = pairIndex j i hji.ne := by
        apply Subtype.ext
        exact Sym2.eq_swap
      rw [he, differenceHelper_pair hji]
      simp [matrixOfHelper, hji, not_lt_of_ge hji.le]

theorem difference_helper_range_card [Fintype G] :
    Nat.card (Set.range (differenceHelper (d := d) (G := G))) =
      Fintype.card G ^ (d * (d - 1) / 2) := by
  rw [Set.range_eq_univ.mpr difference_helper_surjective, Nat.card_univ, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, PairIndex, Sym2.card_subtype_not_diag,
    Fintype.card_fin, Nat.choose_two_right]

/-- Every finite nonempty alphabet admits the sharp complete helper construction.
A cyclic group structure is transported internally; the witness is still a
family of ordinary functions on the original alphabet. -/
theorem exists_sharp_helper {A : Type*} [Fintype A] [Nonempty A] :
    ∃ H : Mat d A → PairHelper d A, ∃ C : PairHelper d A → Family d A,
      Function.Surjective H ∧
      Nat.card (Set.range H) = Fintype.card A ^ (d * (d - 1) / 2) ∧
      ∀ X : Mat d A, complete (fun _ => id) (C (H X)) X = fun i j => X j i := by
  classical
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let e : A ≃ ZMod (Fintype.card A) := Fintype.equivOfCardEq (by simp [ZMod.card])
  let : AddCommGroup A := e.addCommGroup
  exact ⟨differenceHelper, helperColumns, difference_helper_surjective,
    difference_helper_range_card, difference_helper_correct⟩

theorem triangular_exponents (d : ℕ) :
    d * d = d * (d - 1) / 2 + d * (d + 1) / 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)
  have h2 : 2 * (d * (d + 1) / 2) = d * (d + 1) := by
    simpa only [Nat.add_sub_cancel, Nat.mul_comm] using
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (d + 1))
  cases d with
  | zero => norm_num
  | succ d =>
    simp only [Nat.succ_sub_one] at h1 h2 ⊢
    nlinarith

/-- Equality in the helper-range counting bound is attained, not just its exponent. -/
theorem helper_bound_attained {A : Type*} [Fintype A] [Nonempty A] :
    ∃ H : Mat d A → PairHelper d A, ∃ C : PairHelper d A → Family d A,
      Nat.card (HelperAgreement H (fun _ _ => id) C) =
        Nat.card (Set.range H) * Fintype.card A ^ (d * (d + 1) / 2) := by
  obtain ⟨H, C, hsurj, hcard, hcorrect⟩ := exists_sharp_helper (d := d) (A := A)
  refine ⟨H, C, ?_⟩
  have hall : HelperAgreement H (fun _ _ => id) C = Set.univ := by
    ext X
    exact iff_true_intro (hcorrect X)
  rw [hall, Nat.card_univ, hcard]
  simp only [Mat, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← pow_mul, ← pow_add]
  rw [triangular_exponents]

end SharedDecoders.RowColumn

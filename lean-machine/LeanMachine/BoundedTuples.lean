import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! Exact finite menus for nonnegative tuples with a bounded total.
The slack coordinate is constructed explicitly; no cardinality certificate
is part of the input. -/

namespace LeanMachine

open scoped BigOperators

/-- Nonnegative integer tuples with a total budget. -/
def BoundedTuple (m T : ℕ) := {f : Fin m → ℕ // ∑ i, f i ≤ T}

/-- Adding the unused budget gives the usual stars-and-bars equivalence. -/
noncomputable def boundedTupleEquivAntidiag (m T : ℕ) :
    BoundedTuple m T ≃ (Finset.univ : Finset (Fin (m + 1))).finsuppAntidiag T where
  toFun f := ⟨Finsupp.equivFunOnFinite.symm
      (Fin.cases (T - ∑ i, f.val i) f.val), by
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · change (∑ i, Fin.cases (T - ∑ j, f.val j) f.val i) = T
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      exact Nat.sub_add_cancel f.prop
    · exact Finset.subset_univ _⟩
  invFun g := ⟨fun i => g.val i.succ, by
    have h := (Finset.mem_finsuppAntidiag.mp g.prop).1
    rw [Fin.sum_univ_succ] at h
    simpa using (Nat.le_add_left (∑ i : Fin m, g.val i.succ) (g.val 0)).trans_eq h⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    simp
  right_inv g := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := (Finset.mem_finsuppAntidiag.mp g.prop).1
      rw [Fin.sum_univ_succ] at h
      change T - (∑ i : Fin m, g.val i.succ) = g.val 0
      omega
    · simp

noncomputable instance (m T : ℕ) : Fintype (BoundedTuple m T) :=
  Fintype.ofEquiv _ (boundedTupleEquivAntidiag m T).symm

theorem boundedTuple_card (m T : ℕ) :
    Fintype.card (BoundedTuple m T) = (T + m).choose m := by
  rw [Fintype.card_congr (boundedTupleEquivAntidiag m T),
    Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h : m + 1 + T - 1 = T + m := by omega
  rw [h]
  exact Nat.choose_symm_add

/-- Chronologically sampled counters, including repeated values. -/
abbrev MonotoneCounters (m P : ℕ) :=
  {f : Fin m → Fin (P + 1) // Monotone f}

noncomputable instance (m P : ℕ) : Fintype (MonotoneCounters m P) :=
  Fintype.ofFinite _

def monotoneCounterMultiset {m P : ℕ} (f : MonotoneCounters m P) :
    Sym (Fin (P + 1)) m :=
  ⟨(List.ofFn f.val : Multiset (Fin (P + 1))), by simp⟩

theorem monotoneCounterMultiset_injective (m P : ℕ) :
    Function.Injective (@monotoneCounterMultiset m P) := by
  intro f g h
  apply Subtype.ext
  apply List.ofFn_injective
  have hperm : List.Perm (List.ofFn f.val) (List.ofFn g.val) :=
    Multiset.coe_eq_coe.mp (congrArg Subtype.val h)
  exact hperm.eq_of_sortedLE f.prop.sortedLE_ofFn g.prop.sortedLE_ofFn

theorem monotoneCounters_card_le (m P : ℕ) :
    Fintype.card (MonotoneCounters m P) ≤ (P + m).choose m := by
  have h := Fintype.card_le_of_injective _ (monotoneCounterMultiset_injective m P)
  rw [Sym.card_sym_eq_choose] at h
  simpa only [Fintype.card_fin, Nat.add_sub_assoc (by omega : 1 ≤ m + 1),
    Nat.add_right_comm P 1 m, Nat.add_sub_cancel] using h

/-- Signed increments with a total absolute-variation budget. -/
def SignedTuple (m T : ℕ) := {f : Fin m → ℤ // ∑ i, (f i).natAbs ≤ T}

def signedTupleEncode {m T : ℕ} (f : SignedTuple m T) :
    (Fin m → Bool) × BoundedTuple m T :=
  (fun i => decide (0 ≤ f.val i), ⟨fun i => (f.val i).natAbs, f.prop⟩)

theorem signedTupleEncode_injective (m T : ℕ) :
    Function.Injective (@signedTupleEncode m T) := by
  intro f g h
  apply Subtype.ext
  funext i
  have hs := congrFun (congrArg Prod.fst h) i
  have ha := congrFun (congrArg (fun v => v.2.val) h) i
  simp only [signedTupleEncode] at hs ha
  have he : 0 ≤ f.val i ↔ 0 ≤ g.val i := by simpa using hs
  rcases Int.natAbs_eq_natAbs_iff.mp ha with hsame | hneg
  · exact hsame
  · by_cases hf : 0 ≤ f.val i
    · have hg := he.mp hf
      omega
    · have hg := mt he.mpr hf
      omega

noncomputable instance (m T : ℕ) : Fintype (SignedTuple m T) :=
  Fintype.ofInjective _ (signedTupleEncode_injective m T)

theorem signedTuple_card_le (m T : ℕ) :
    Fintype.card (SignedTuple m T) ≤ 2 ^ m * (T + m).choose m := by
  have h := Fintype.card_le_of_injective _ (signedTupleEncode_injective m T)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, boundedTuple_card] using h

/-- Positions sampled in chronological order, with the known initial position
included. The bound concerns total variation, not independent coordinates. -/
def SampledPositions (m T : ℕ) :=
  {p : Fin (m + 1) → ℤ // p 0 = 0 ∧
    (∑ i : Fin m, (p i.succ - p i.castSucc).natAbs) ≤ T}

def sampledPositionIncrements {m T : ℕ} (p : SampledPositions m T) :
    SignedTuple m T :=
  ⟨fun i => p.val i.succ - p.val i.castSucc, p.prop.2⟩

theorem sampledPositionIncrements_injective (m T : ℕ) :
    Function.Injective (@sampledPositionIncrements m T) := by
  intro p q h
  apply Subtype.ext
  funext i
  refine Fin.induction ?_ (fun j hj => ?_) i
  · exact p.prop.1.trans q.prop.1.symm
  · have hi := congrFun (congrArg Subtype.val h) j
    change p.val j.succ - p.val j.castSucc =
      q.val j.succ - q.val j.castSucc at hi
    omega

noncomputable instance (m T : ℕ) : Fintype (SampledPositions m T) :=
  Fintype.ofInjective _ (sampledPositionIncrements_injective m T)

theorem sampledPositions_card_le (m T : ℕ) :
    Fintype.card (SampledPositions m T) ≤ 2 ^ m * (T + m).choose m :=
  (Fintype.card_le_of_injective _ (sampledPositionIncrements_injective m T)).trans
    (signedTuple_card_le m T)

theorem sum_monotone_gaps {m : ℕ} (t : Fin (m + 1) → ℕ) (ht : Monotone t) :
    ∑ i : Fin m, (t i.succ - t i.castSucc) = t (Fin.last m) - t 0 := by
  have hz : (∑ i : Fin m, ((t i.succ : ℤ) - t i.castSucc)) =
      (t (Fin.last m) : ℤ) - t 0 := by
    rw [Finset.sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ (fun i : Fin (m + 1) => (t i : ℤ))
    have h₂ := Fin.sum_univ_castSucc (fun i : Fin (m + 1) => (t i : ℤ))
    linarith
  have hstep : ∀ i : Fin m, t i.castSucc ≤ t i.succ :=
    fun i => ht (by simp [Fin.le_iff_val_le_val])
  have hends : t 0 ≤ t (Fin.last m) := ht (Fin.zero_le _)
  have he : ((∑ i : Fin m, (t i.succ - t i.castSucc) : ℕ) : ℤ) =
      ((t (Fin.last m) - t 0 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum, Nat.cast_sub (hstep _), Nat.cast_sub hends] using hz
  exact_mod_cast he

/-- Actual ordered samples of a unit-speed integer path meet the total-variation
menu. The pointwise Lipschitz hypothesis is a property of the path, not a
cardinality or reconstruction premise. -/
def sampleUnitPath {m T : ℕ} (y : ℕ → ℤ)
    (hy : ∀ a b, a ≤ b → (y b - y a).natAbs ≤ b - a)
    (t : Fin (m + 1) → ℕ) (ht : Monotone t)
    (ht0 : t 0 = 0) (hy0 : y 0 = 0) (htT : t (Fin.last m) ≤ T) :
    SampledPositions m T :=
  ⟨fun i => y (t i), by
    constructor
    · simp [ht0, hy0]
    · calc
        (∑ i : Fin m, (y (t i.succ) - y (t i.castSucc)).natAbs) ≤
            ∑ i : Fin m, (t i.succ - t i.castSucc) :=
          Finset.sum_le_sum fun i _ => hy _ _ (ht (by simp [Fin.le_iff_val_le_val]))
        _ = t (Fin.last m) - t 0 := sum_monotone_gaps t ht
        _ ≤ T := (Nat.sub_le _ _).trans htT⟩

end LeanMachine

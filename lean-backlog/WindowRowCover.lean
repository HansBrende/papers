import WindowRows
import WindowGuards
import StatementsRowSpread

/-!
# Covering native cones by reachable input rows

This is the finite union/counting adapter, not the full native row-spread
theorem. Its sole path premise is supplied by a separate concrete guarded
window graph. The input/output geometry is the actual `Trace` geometry.
-/

namespace LeanBacklog.WindowRowCover

open Finset BoundedNesting MergeDepth BoundedStackDepth
open WindowRows WindowGuards RowSpread
open scoped BigOperators

/-- Input row numbers read in any window reachable from one append window. -/
def reachableInputRows {k : ℕ} (τ : Trace k) (L h : ℕ)
    (next : ℕ → Finset ℕ) (D i : ℕ) : Finset ℕ :=
  (neighborReach next D i).biUnion (inputWindowRows τ L h)

/-- All input rows accessible from the complete first-to-last append span
of physical output row `r`. Sparse append times are allowed. -/
def rowSupport {k : ℕ} (τ : Trace k) (T L h : ℕ)
    (next : ℕ → Finset ℕ) (D r : ℕ) : Finset ℕ :=
  (rowWindowSpan (appendTime τ T) h r).biUnion
    (reachableInputRows τ L h next D)

theorem card_reachableInputRows_le {k B : ℕ} (τ : Trace k) (L h : ℕ)
    (next : ℕ → Finset ℕ) (D i : ℕ) (hh : 0 < h)
    (hB : ∀ j, (next j).card ≤ B) :
    (reachableInputRows τ L h next D i).card ≤ 2 * B ^ D := by
  calc
    _ ≤ ∑ j ∈ neighborReach next D i, (inputWindowRows τ L h j).card :=
      card_biUnion_le
    _ ≤ ∑ _j ∈ neighborReach next D i, 2 :=
      sum_le_sum fun j _ => card_inputWindowRows_le_two τ L h j hh
    _ = (neighborReach next D i).card * 2 := by simp
    _ ≤ B ^ D * 2 := Nat.mul_le_mul_right 2 (card_neighborReach_le next hB D i)
    _ = 2 * B ^ D := Nat.mul_comm _ _

theorem card_rowSupport_le {k B : ℕ} (τ : Trace k) (T L h : ℕ)
    (next : ℕ → Finset ℕ) (D r : ℕ) (hh : 0 < h)
    (hB : ∀ j, (next j).card ≤ B) :
    (rowSupport τ T L h next D r).card ≤
      2 * (rowWindowSpan (appendTime τ T) h r).card * B ^ D := by
  calc
    _ ≤ ∑ i ∈ rowWindowSpan (appendTime τ T) h r,
        (reachableInputRows τ L h next D i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ rowWindowSpan (appendTime τ T) h r, 2 * B ^ D :=
      sum_le_sum fun i _ => card_reachableInputRows_le τ L h next D i hh hB
    _ = _ := by simp; ring

theorem card_rowSupport_le_of_not_bad {k d B M : ℕ} (τ : Trace k) (T L h : ℕ)
    (next : ℕ → Finset ℕ) (D : ℕ) (hh : 0 < h)
    (hB : ∀ j, (next j).card ≤ B) {r : Fin d}
    (hr : r ∉ badRowSpans (appendTime τ T) d h M) :
    (rowSupport τ T L h next D r.val).card ≤ 2 * (M + 1) * B ^ D :=
  (card_rowSupport_le τ T L h next D r.val hh hB).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (rowWindowSpan_card_le_of_not_bad hr)))

/-- Discard row numbers outside the requested finite matrix dimension. -/
def finiteRows (d : ℕ) (S : Finset ℕ) : Finset (Fin d) :=
  univ.filter fun r => r.val ∈ S

@[simp] theorem mem_finiteRows {d : ℕ} {S : Finset ℕ} {r : Fin d} :
    r ∈ finiteRows d S ↔ r.val ∈ S := by simp [finiteRows]

theorem card_finiteRows_le (d : ℕ) (S : Finset ℕ) :
    (finiteRows d S).card ≤ S.card := by
  apply card_le_card_of_injOn (fun r : Fin d => r.val)
  · intro r hr
    exact mem_finiteRows.mp hr
  · intro r hr s hs heq
    exact Fin.ext heq

/-- Bad output rows are explicitly assigned no helper rows. Their recovery
is ignored by `ConeRowsExcept`, while this keeps the width bound global. -/
def helperRows {k : ℕ} (τ : Trace k) (T d b : ℕ)
    (next : ℕ → Finset ℕ) (D M : ℕ) (r : Fin d) : Finset (Fin d) :=
  if r ∈ badRowSpans (appendTime τ T) d (d * b) M then ∅ else
    finiteRows d (rowSupport τ T (d * d * b) (d * b) next D r.val)

theorem card_helperRows_le {k d b B M : ℕ} (τ : Trace k) (T : ℕ)
    (next : ℕ → Finset ℕ) (D : ℕ) (hh : 0 < d * b)
    (hB : ∀ j, (next j).card ≤ B) (r : Fin d) :
    (helperRows τ T d b next D M r).card ≤ 2 * (M + 1) * B ^ D := by
  unfold helperRows
  split_ifs with hr
  · simp
  · exact (card_finiteRows_le _ _).trans
      (card_rowSupport_le_of_not_bad τ T (d * d * b) (d * b) next D hh hB hr)

/-- A literal read belongs to the input-row set of its own time window. -/
theorem readPos_row_mem {k L h t : ℕ} (τ : Trace k) (hh : 0 < h) {p : Fin L}
    (hread : readPos τ L t = some p) : p.val / h ∈ inputWindowRows τ L h (t / h) := by
  apply mem_image.mpr
  refine ⟨p, mem_inputWindowPositions.mpr ⟨t, ?_, ?_, hread⟩, rfl⟩
  · simpa [Nat.mul_comm] using Nat.mul_div_le t h
  · have hmod := Nat.mod_lt t hh
    have heq := Nat.mod_add_div t h
    nlinarith

/-- Union membership for a concrete output cone. The hypothesis is the
exact endpoint reachability delivered by the guarded dependency graph.
No full geometric row-spread theorem is assumed in this adapter. -/
theorem cone_row_mem_support {k d b T D : ℕ} (τ : Trace k) (Γ : Finset ℕ)
    (next : ℕ → Finset ℕ) (hh : 0 < d * b)
    (happ : d * d * b ≤ (appendList τ T).length)
    (hreach : ∀ (t : ℕ) (π : List ℕ),
      IsDepPath τ.work T (t :: π) → LinNet.GFree Γ (t :: π) →
      ((t :: π).getLastD t) / (d * b) ∈ neighborReach next D (t / (d * b)))
    {r : Fin d} {ℓ p : Fin (d * d * b)} (hℓ : ℓ.val / (d * b) = r.val)
    (hp : p ∈ coneSystem τ T Γ d b ℓ) :
    p.val / (d * b) ∈ rowSupport τ T (d * d * b) (d * b) next D r.val := by
  simp only [coneSystem, depCone, mem_filter, mem_univ, true_and] at hp
  obtain ⟨π, hpath, hfree, hread⟩ := hp
  have happ' : d * (d * b) ≤ (appendList τ T).length := by
    simpa only [Nat.mul_assoc] using happ
  have hstart := appendTime_mem_rowWindowSpan τ hh happ' r hℓ
  apply mem_biUnion.mpr
  refine ⟨appendTime τ T ℓ.val / (d * b), hstart, mem_biUnion.mpr ?_⟩
  refine ⟨((appendTime τ T ℓ.val :: π).getLastD (appendTime τ T ℓ.val)) / (d * b),
    hreach _ π hpath hfree, ?_⟩
  exact readPos_row_mem τ hh hread

/-- The literal native cone system has the stated row cover outside the
long output spans. The reachability premise must still be established by
the concrete cut/window argument before this is a native theorem. -/
theorem coneRowsExcept_helperRows {k d b T D M : ℕ} (τ : Trace k) (Γ : Finset ℕ)
    (next : ℕ → Finset ℕ) (hh : 0 < d * b)
    (happ : d * d * b ≤ (appendList τ T).length)
    (hreach : ∀ (t : ℕ) (π : List ℕ),
      IsDepPath τ.work T (t :: π) → LinNet.GFree Γ (t :: π) →
      ((t :: π).getLastD t) / (d * b) ∈ neighborReach next D (t / (d * b))) :
    ConeRowsExcept (coneSystem τ T Γ d b) (helperRows τ T d b next D M)
      (badRowSpans (appendTime τ T) d (d * b) M) := by
  intro r hr ℓ hℓ p hp
  have hrow : p.val / (d * b) < d := by
    apply (Nat.div_lt_iff_lt_mul hh).mpr
    simpa only [Nat.mul_assoc] using p.isLt
  refine ⟨⟨p.val / (d * b), hrow⟩, ?_, rfl⟩
  simp only [helperRows, ite_eq_right hr, mem_finiteRows]
  exact cone_row_mem_support τ Γ next hh happ hreach hℓ hp

#print axioms card_rowSupport_le_of_not_bad
#print axioms card_helperRows_le
#print axioms cone_row_mem_support
#print axioms coneRowsExcept_helperRows

end LeanBacklog.WindowRowCover

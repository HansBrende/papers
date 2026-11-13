import BoundedStackDepth.Machines
import MergeDepth.Trimming
import MotionDepthCodes.StorageCode
import DirectedRecovery.StorageCode

/-!
# Row spread and nonlinear whole-row recovery

The native row-spread bridge has a reviewed written proof; here it is only
stated as a proposition, with its Lean proof pending. Uniform whole-row rate
bounds remain open propositions. No new axiom asserts either target. The
finite exceptional-column wrapper, cone comparisons and raw-conditioning
budget are proved below.

From `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/`, check:
`lake env lean ../../lean-backlog/StatementsRowSpread.lean`.
The finite storage-code definition is reused literally; no linearity or
field assumption is added.
-/

namespace LeanBacklog.RowSpread

open Finset BoundedNesting MergeDepth BoundedStackDepth
open scoped BigOperators

universe u

abbrev Entry (d : ℕ) := Fin d × Fin d

/-- Column `q.2` is recovered from every entry of rows `ρ q.2`.
An exceptional column is assigned the full universe of helpers, making its
recovery condition tautological. This is only how exceptions are encoded. -/
def wholeRowHelpers {d : ℕ} (ρ : Fin d → Finset (Fin d))
    (E : Finset (Fin d)) (q : Entry d) : Finset (Entry d) :=
  if q.2 ∈ E then univ else (ρ q.2).product univ

/-- Arbitrary, possibly nonlinear finite-alphabet whole-row recovery.
Each column has ONE common helper-row set for all its entries. -/
def IsWholeRowCodeExcept {d : ℕ} {α : Type u}
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (C : Finset (Entry d → α)) : Prop :=
  MotionDepthCodes.IsStorageCode (wholeRowHelpers ρ E) C

theorem wholeRowCode_iff {d : ℕ} {α : Type u}
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (C : Finset (Entry d → α)) :
    IsWholeRowCodeExcept ρ E C ↔
      ∀ x ∈ C, ∀ y ∈ C, ∀ r ∉ E,
        (∀ s ∈ ρ r, ∀ j, x (s, j) = y (s, j)) →
        ∀ i, x (i, r) = y (i, r) := by
  constructor
  · intro h x hx y hy r hr hxy i
    apply h x hx y hy (i, r)
    intro p hp
    have hp' : p.1 ∈ ρ r := by
      simpa [wholeRowHelpers, hr] using hp
    exact hxy p.1 hp' p.2
  · intro h x hx y hy q hxy
    by_cases hq : q.2 ∈ E
    · exact hxy q (by simp [wholeRowHelpers, hq])
    · exact h x hx y hy q.2 hq (fun s hs j =>
        hxy (s, j) (by simp [wholeRowHelpers, hq, hs])) q.1

theorem wholeRowCode_mono {d : ℕ} {α : Type u}
    {ρ ρ' : Fin d → Finset (Fin d)} {E E' : Finset (Fin d)}
    {C : Finset (Entry d → α)}
    (hC : IsWholeRowCodeExcept ρ E C)
    (hρ : ∀ r, ρ r ⊆ ρ' r) (hE : E ⊆ E') :
    IsWholeRowCodeExcept ρ' E' C := by
  rw [wholeRowCode_iff] at hC ⊢
  intro x hx y hy r hr hxy i
  exact hC x hx y hy r (fun he => hr (hE he))
    (fun s hs j => hxy s (hρ r hs) j) i

/-- A rectangle of rows R and columns J whose columns never read rows R
is an independent coordinate set. Reuse the existing all-alphabet bound;
no entropy, linearity, or positive code-size assumption is needed. -/
theorem wholeRow_rectangle_card_bound {d : ℕ} {α : Type u} [Fintype α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsWholeRowCodeExcept ρ ∅ C) (R J : Finset (Fin d))
    (havoid : ∀ j ∈ J, Disjoint R (ρ j)) :
    C.card ≤ Fintype.card α ^ (d * d - R.card * J.card) := by
  have hI : DirectedRecovery.IsIndependent (wholeRowHelpers ρ ∅) (R.product J) := by
    intro q hq p hp hpI
    have hpρ : p.1 ∈ ρ q.2 := by simpa [wholeRowHelpers] using hp
    exact (disjoint_left.mp (havoid q.2 (mem_product.mp hq).2))
      (mem_product.mp hpI).1 hpρ
  simpa [Entry] using
    DirectedRecovery.storageCode_card_le_of_independent hI hC

/-- Quantitative expansion forced by a lower bound on whole-row code size.
This strengthens the two setwise bounds to any incidence-free rectangle. -/
theorem wholeRow_rectangle_deficit {d : ℕ} {α : Type u} [Fintype α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsWholeRowCodeExcept ρ ∅ C) (R J : Finset (Fin d))
    (havoid : ∀ j ∈ J, Disjoint R (ρ j)) (δ : ℝ)
    (hα : 1 < Fintype.card α)
    (hlower : (Fintype.card α : ℝ) ^ ((1 - δ) * (d : ℝ) ^ 2) ≤ C.card) :
    (R.card : ℝ) * J.card ≤ δ * (d : ℝ) ^ 2 := by
  have hn : R.card * J.card ≤ d * d :=
    Nat.mul_le_mul (by simpa using card_le_univ R) (by simpa using card_le_univ J)
  have hcard := wholeRow_rectangle_card_bound ρ C hC R J havoid
  have hpow : (Fintype.card α : ℝ) ^ ((1 - δ) * (d : ℝ) ^ 2) ≤
      (Fintype.card α : ℝ) ^ ((d * d - R.card * J.card : ℕ) : ℝ) := by
    exact hlower.trans (by exact_mod_cast hcard)
  have he := (Real.rpow_le_rpow_left_iff (by exact_mod_cast hα)).mp hpow
  rw [Nat.cast_sub hn] at he
  simp only [Nat.cast_mul] at he
  nlinarith

/-- Fixing all entries of the exceptional columns makes those columns
constant. Thus a complete-column bound automatically gives its exceptional-
column variant at a cost of at most `|α|^(d*|E|)` fibres. This is finite and
does not require linearity, a nonempty code, or a nontrivial alphabet. -/
theorem exceptional_column_card_bound {d w A : ℕ} {α : Type u} [Fintype α]
    (hbound : ∀ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
      (∀ r, (ρ r).card ≤ w) → IsWholeRowCodeExcept ρ ∅ C → C.card ≤ A)
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (C : Finset (Entry d → α)) (hρ : ∀ r, (ρ r).card ≤ w)
    (hC : IsWholeRowCodeExcept ρ E C) :
    C.card ≤ Fintype.card α ^ (d * E.card) * A := by
  classical
  let restrict : (Entry d → α) → ((Fin d × E) → α) := fun x p => x (p.1, p.2)
  let ρ' : Fin d → Finset (Fin d) := fun r => if r ∈ E then ∅ else ρ r
  have hρ' (r : Fin d) : (ρ' r).card ≤ w := by
    by_cases hr : r ∈ E <;> simp [ρ', hr, hρ r]
  have hfibre (z : (Fin d × E) → α) :
      (C.filter fun x => restrict x = z).card ≤ A := by
    apply hbound ρ' _ hρ'
    rw [wholeRowCode_iff]
    intro x hx y hy r _ hxy i
    obtain ⟨hxC, hxz⟩ := mem_filter.mp hx
    obtain ⟨hyC, hyz⟩ := mem_filter.mp hy
    by_cases hr : r ∈ E
    · exact congrFun (hxz.trans hyz.symm) (i, ⟨r, hr⟩)
    · exact (wholeRowCode_iff ρ E C).mp hC x hxC y hyC r hr
        (fun s hs j => hxy s (by simpa [ρ', hr] using hs) j) i
  have hcount : ∑ z : ((Fin d × E) → α),
      (C.filter fun x => restrict x = z).card = C.card := by
    simpa using sum_card_fiberwise_eq_card_filter C
      (univ : Finset ((Fin d × E) → α)) restrict
  calc
    C.card = ∑ z : ((Fin d × E) → α),
        (C.filter fun x => restrict x = z).card := hcount.symm
    _ ≤ ∑ _z : ((Fin d × E) → α), A := sum_le_sum fun z _ => hfibre z
    _ = Fintype.card α ^ (d * E.card) * A := by simp

/-- Finite all-column target, with a real exponent to avoid rounding the
rate. The alphabet is finite but otherwise arbitrary. -/
def WholeRowCardinalityBound (d w : ℕ) (α : Type u) [Fintype α] (exponent : ℝ) : Prop :=
  ∀ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
    (∀ r, (ρ r).card ≤ w) → IsWholeRowCodeExcept ρ ∅ C →
      (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ exponent

/-- OPEN at the rates of interest: one common limiting upper rate for every
fixed helper window, uniformly over all finite alphabets. Uniformity matters:
the entry alphabet grows with dimension. The threshold may depend on w and
the slack, but not on the alphabet, helper relation or recovery code. -/
def UniformWholeRowRate (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (α : Type u) [Fintype α], 2 ≤ Fintype.card α →
      WholeRowCardinalityBound d w α ((rate + η) * (d : ℝ) ^ 2)

/-- OPEN nonlinear half-rate target, uniform in the finite alphabet. -/
def WholeRowHalfRateAllFiniteAlphabets : Prop :=
  UniformWholeRowRate.{u} (1 / 2)

/-- The narrower alphabet scope needed for canonical binary entry widths.
The alphabet has exactly `2^(entryBits d)` symbols, not `d` symbols in
general. No field or decoder-linearity hypothesis is imposed. -/
def UniformWholeRowRateCanonicalBits (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    WholeRowCardinalityBound d w (Fin (Transpose.entryBits d) → Bool)
      ((rate + η) * (d : ℝ) ^ 2)

/-- OPEN half-rate target at precisely the canonical bit-entry alphabets. -/
def WholeRowHalfRateCanonicalBits : Prop :=
  UniformWholeRowRateCanonicalBits (1 / 2)

/-- The same helper rows must cover every bit cone in an output row. The
output row becomes an INPUT COLUMN after transposing the demand index.
The natural-number quotients avoid hidden positive-width assumptions. -/
def ConeRowsExcept {d b : ℕ}
    (I : Fin (d * d * b) → Finset (Fin (d * d * b)))
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d)) : Prop :=
  ∀ r ∉ E, ∀ ℓ : Fin (d * d * b), ℓ.val / (d * b) = r.val →
    ∀ p ∈ I ℓ, ∃ s ∈ ρ r, p.val / (d * b) = s.val

theorem coneRowsExcept_mono {d b : ℕ}
    {I J : Fin (d * d * b) → Finset (Fin (d * d * b))}
    {ρ : Fin d → Finset (Fin d)} {E : Finset (Fin d)}
    (h : ConeRowsExcept J ρ E) (hIJ : ∀ ℓ, I ℓ ⊆ J ℓ) :
    ConeRowsExcept I ρ E :=
  fun r hr ℓ hℓ p hp => h r hr ℓ hℓ p (hIJ ℓ hp)

/-- Enlarging the revealed set can only shrink cones. `GFree` excludes
the tail, not the root, matching the existing native definitions. -/
theorem coneSystem_antitone {k d b T : ℕ} (τ : Trace k)
    {Γ Γ' : Finset ℕ} (hΓ : Γ ⊆ Γ') (ℓ : Fin (d * d * b)) :
    coneSystem τ T Γ' d b ℓ ⊆ coneSystem τ T Γ d b ℓ := by
  intro p hp
  simp only [coneSystem, depCone, mem_filter, mem_univ, true_and] at hp ⊢
  obtain ⟨π, hπ, hfree, hread⟩ := hp
  exact ⟨π, hπ, gfree_mono hΓ hfree, hread⟩

/-- A dependency path either avoids the new cut or has a suffix starting
at a newly cut step. Conditioning on all OLD raw cones of newly cut steps
therefore transfers an arbitrary recovery code, without invoking correct
machine step-value semantics. This inclusion needs no nesting of the cuts. -/
theorem depCone_change_cut {k L T : ℕ} (xs : Fin k → ℕ → ℤ)
    (rd : ℕ → Option (Fin L)) (Γ Γ' : Finset ℕ) (t : ℕ) :
    depCone xs T rd Γ t ⊆ depCone xs T rd Γ' t ∪
      (Γ' \ Γ).biUnion (fun u => depCone xs T rd Γ u) := by
  classical
  intro p hp
  simp only [depCone, mem_filter, mem_univ, true_and] at hp
  obtain ⟨π, hπ, hfree, hread⟩ := hp
  have aux : ∀ (π : List ℕ) (t : ℕ),
      IsDepPath xs T (t :: π) → LinNet.GFree Γ (t :: π) →
      rd ((t :: π).getLastD t) = some p →
      p ∈ depCone xs T rd Γ' t ∪
        (Γ' \ Γ).biUnion (fun u => depCone xs T rd Γ u) := by
    intro π
    induction π with
    | nil =>
        intro t hπ _ hread
        apply mem_union_left
        simp only [depCone, mem_filter, mem_univ, true_and]
        exact ⟨[], hπ, gfree_singleton _ _, hread⟩
    | cons v π ih =>
        intro t hπ hfree hread
        have htail : IsDepPath xs T (v :: π) := hπ.2
        obtain ⟨hvΓ, hftail⟩ := gfree_cons_cons.mp hfree
        have hrtail : rd ((v :: π).getLastD v) = some p := by
          simpa only [LinNet.getLastD_cons_cons] using hread
        by_cases hvΓ' : v ∈ Γ'
        · apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨v, mem_sdiff.mpr ⟨hvΓ', hvΓ⟩, ?_⟩
          simp only [depCone, mem_filter, mem_univ, true_and]
          exact ⟨π, htail, hftail, hrtail⟩
        · rcases mem_union.mp (ih v htail hftail hrtail) with hpnew | hpcut
          · apply mem_union_left
            simp only [depCone, mem_filter, mem_univ, true_and] at hpnew ⊢
            obtain ⟨σ, hσ, hfσ, hrσ⟩ := hpnew
            refine ⟨v :: σ, ⟨hπ.1, hσ⟩, gfree_cons_cons.mpr ⟨hvΓ', hfσ⟩, ?_⟩
            simpa only [LinNet.getLastD_cons_cons] using hrσ
          · exact mem_union_right _ hpcut
  exact aux π t hπ hfree hread

/-- Native output-root specialization of the raw-cut inclusion. -/
theorem coneSystem_change_cut {k d b T : ℕ} (τ : Trace k)
    (Γ Γ' : Finset ℕ) (ℓ : Fin (d * d * b)) :
    coneSystem τ T Γ d b ℓ ⊆ coneSystem τ T Γ' d b ℓ ∪
      (Γ' \ Γ).biUnion (fun u =>
        depCone τ.work T (readPos τ (d * d * b)) Γ u) :=
  depCone_change_cut τ.work (readPos τ (d * d * b)) Γ Γ' _

/-- The existing finite ball count gives the precise old raw-cone bill
at edge depth D; no walk geometry or correctness assumption is needed. -/
theorem card_depCone_le {k L T D : ℕ} (xs : Fin k → ℕ → ℤ)
    (rd : ℕ → Option (Fin L)) (Γ : Finset ℕ)
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D + 1)
    (t : ℕ) :
    (depCone xs T rd Γ t).card ≤ ∑ j ∈ range (D + 1), (k + 1) ^ j := by
  have hsub : depCone xs T rd Γ t ⊆ stepBall xs T rd D t := by
    intro p hp
    simp only [depCone, mem_filter, mem_univ, true_and] at hp
    obtain ⟨π, hπ, hfree, hread⟩ := hp
    simp only [stepBall, mem_filter, mem_univ, true_and]
    refine ⟨π, hπ, ?_, hread⟩
    have hlen := hdepth _ hπ hfree
    simp only [List.length_cons] at hlen
    omega
  exact (card_le_card hsub).trans (card_stepBall_le xs T rd D t)

theorem card_new_cut_raw_support_le {k L T D : ℕ} (xs : Fin k → ℕ → ℤ)
    (rd : ℕ → Option (Fin L)) (Γ Γ' : Finset ℕ)
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D + 1) :
    ((Γ' \ Γ).biUnion (fun u => depCone xs T rd Γ u)).card ≤
      (Γ' \ Γ).card * ∑ j ∈ range (D + 1), (k + 1) ^ j := by
  calc
    _ ≤ ∑ u ∈ Γ' \ Γ, (depCone xs T rd Γ u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ Γ' \ Γ, ∑ j ∈ range (D + 1), (k + 1) ^ j :=
      sum_le_sum fun u _ => card_depCone_le xs rd Γ hdepth u
    _ = _ := by simp

/-- Finite geometric conclusion at specified dimension and bit width.
`D` counts EDGES, hence the old free paths have at most `D+1` vertices.
No correctness or cheapness of the initial cut is assumed. -/
def NativeRowSpreadAt (k β D w : ℕ) (C ε : ℝ) (d b : ℕ) : Prop :=
  ∀ (τ : Trace k) (T : ℕ),
    (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) →
    (appendList τ T).length = d * d * b →
    ∀ Γ : Finset ℕ,
      (∀ π, IsDepPath τ.work T π → LinNet.GFree Γ π → π.length ≤ D + 1) →
      ∃ (Γ' : Finset ℕ) (E : Finset (Fin d)) (ρ : Fin d → Finset (Fin d)),
        Γ ⊆ Γ' ∧
        (β * (Γ' \ Γ).card : ℝ) ≤ ε * (d * d * b : ℕ) ∧
        (E.card : ℝ) ≤ ε * d ∧
        (∀ r, (ρ r).card ≤ w) ∧
        ConeRowsExcept (coneSystem τ T Γ' d b) ρ E

/-- Explicit width in the reviewed written geometric bridge.
This is a definition of the target constant, not a Lean proof of its validity. -/
noncomputable def rowSpreadWindow (k β D : ℕ) (C ε : ℝ) : ℕ :=
  2 * (⌈2 * C / ε⌉₊ + 1) *
    (⌈4 * (k : ℝ) * (k + 1) * β * C / ε⌉₊ + 2) ^ D

/-- D4 bridge with a reviewed written proof, but no Lean proof here.
The uniform threshold is d>=4 for every positive entry width, including k=0. -/
def NativeRowSpreadQuantitative : Prop :=
  ∀ (k β D : ℕ) (C ε : ℝ), 1 ≤ β → 1 ≤ C → 0 < ε →
    ∀ d ≥ 4, ∀ b, 1 ≤ b →
      NativeRowSpreadAt k β D (rowSpreadWindow k β D C ε) C ε d b

/-- Qualitative statement of the written bridge, not asserted in Lean.
Width and dimension threshold precede dimension, entry width, trace and
the initial cut. -/
def NativeRowSpreadExtension : Prop :=
  ∀ (k β D : ℕ) (C ε : ℝ), 1 ≤ β → 1 ≤ C → 0 < ε →
    ∃ w d₀ : ℕ, ∀ d ≥ d₀, 1 ≤ d → ∀ b, 1 ≤ b →
      NativeRowSpreadAt k β D w C ε d b

/-- Only a logical implication between the two stated propositions. -/
theorem NativeRowSpreadQuantitative.qualitative
    (h : NativeRowSpreadQuantitative) : NativeRowSpreadExtension := by
  intro k β D C ε hβ hC hε
  exact ⟨rowSpreadWindow k β D C ε, 4,
    fun d hd _ b hb => h k β D C ε hβ hC hε d hd b hb⟩

#print axioms wholeRowCode_iff
#print axioms wholeRowCode_mono
#print axioms wholeRow_rectangle_card_bound
#print axioms wholeRow_rectangle_deficit
#print axioms exceptional_column_card_bound
#print axioms coneRowsExcept_mono
#print axioms coneSystem_antitone
#print axioms depCone_change_cut
#print axioms coneSystem_change_cut
#print axioms card_depCone_le
#print axioms card_new_cut_raw_support_le
#print axioms NativeRowSpreadQuantitative.qualitative

end LeanBacklog.RowSpread

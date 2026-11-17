import WallFarCells

/-!
# The bipartite form of the whole-row conjecture

The clean setting: an `n × m` array, a bipartite graph of maximum degree `w` between rows and
columns, every column a function of its neighbouring rows and every row a function of its
neighbouring columns (`IsBipartiteTwoSidedCode`). `BipartiteBoundAt α n m w v` bounds every
such code on every such host by `|α| ^ v`.

Contents.
* The sandwich on a square index set: a bipartite bound at degree `w` gives the normalized
  full-array bound at window `w`, and the normalized bound at window `2 w + 1` gives the
  bipartite bound at degree `w` (`fullArray_is_bipartite`, `bipartite_is_fullArray`).
* `BipartiteCriterion` (the conjecture's quantifiers), `WindowwiseBipartiteCriterion` and
  `BipartiteCommonDeficit`, with `bipartiteCommonDeficit_iff_commonDeficit`.
* The far-cell form at the same size is equivalent pointwise
  (`bipartiteBoundAt_iff_exists_farCellBoundAt`): pinning cells and assuming expansion are free.
* Licences: a larger host keeps the code property; a host with a sparse cut already carries the
  cut's deficit; `bipartiteBoundAt_of_licences` combines both.
* `RefutingFamily` and `conjecture_iff_not_refutingFamily`: exactly what a family of codes must
  achieve to refute the conjecture.
-/

namespace LeanBacklog.WallBipartite

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The bound at one size -/

/-- Every two-sided code on every bipartite host of maximum degree `w` between `n` rows and
`m` columns has at most `|α| ^ v` words. -/
def BipartiteBoundAt (α : Type*) [Fintype α] (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    IsBipartiteTwoSidedCode H_col H_row D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v

/-- A full-array two-sided code is a bipartite two-sided code with both helper maps `ρ`. -/
theorem fullArray_is_bipartite {d : ℕ} {α : Type*} (ρ : Fin d → Finset (Fin d))
    (C : Finset (Entry d → α)) (hC : IsTwoSidedWholeRowCode ρ C) :
    IsBipartiteTwoSidedCode ρ ρ C := by
  obtain ⟨h1, h2⟩ := hC
  rw [wholeRowCode_iff] at h1
  refine ⟨fun x hx y hy a hagree b => ?_, fun x hx y hy b hagree a => h2 x hx y hy b hagree a⟩
  exact h1 x hx y hy a (by simp) (fun i hi j => hagree i hi j) b

/-- A balanced bipartite two-sided code is a full-array two-sided code for the union relation. -/
theorem bipartite_is_fullArray {N : ℕ} {α : Type*} (H_col H_row : Fin N → Finset (Fin N))
    (D : Finset (Fin N × Fin N → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    IsTwoSidedWholeRowCode (fun j => H_col j ∪ H_row j ∪ {j}) D := by
  obtain ⟨h1, h2⟩ := hD
  refine ⟨?_, fun x hx y hy r hagree i => ?_⟩
  · rw [wholeRowCode_iff]
    intro x hx y hy c _ hagree i
    exact h1 x hx y hy c (fun b hb a' => hagree b (by simp [hb]) a') i
  · exact h2 x hx y hy r (fun a ha b' => hagree a (by simp [ha]) b') i

/-- The union relation of a symmetric host of degree at most `w` is a normalized helper relation
of width `2 w + 1`. -/
theorem unionRel_normalized {N w : ℕ} (H_col H_row : Fin N → Finset (Fin N))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b) :
    (∀ r, (H_col r ∪ H_row r ∪ {r}).card ≤ 2 * w + 1) ∧
    (∀ r s, s ∈ H_col r ∪ H_row r ∪ {r} ↔ r ∈ H_col s ∪ H_row s ∪ {s}) ∧
    (∀ r, r ∈ H_col r ∪ H_row r ∪ {r}) := by
  refine ⟨fun r => ?_, fun r s => ?_, fun r => by simp⟩
  · calc (H_col r ∪ H_row r ∪ {r}).card ≤ (H_col r ∪ H_row r).card + ({r} : Finset _).card :=
          card_union_le _ _
      _ ≤ (H_col r).card + (H_row r).card + 1 := by
          rw [card_singleton]; exact Nat.add_le_add_right (card_union_le _ _) 1
      _ ≤ 2 * w + 1 := by have := hcol r; have := hrow r; omega
  · simp only [mem_union, mem_singleton]
    rw [hsym r s, ← hsym s r]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm

/-- **Sandwich, first half.** A bipartite bound at degree `w` on the square `d × d` gives the
normalized full-array bound at window `w`, same alphabet and exponent. -/
theorem normalized_bound_of_bipartiteBoundAt {α : Type*} [Fintype α] {d w : ℕ} {v : ℝ}
    (h : BipartiteBoundAt α d d w v) : NormalizedTwoSidedWholeRowCardinalityBound d w α v := by
  intro ρ C hρ hsym _ hC
  exact h ρ ρ C hρ hρ (fun a b => hsym a b) (fullArray_is_bipartite ρ C hC)

/-- **Sandwich, second half.** The normalized full-array bound at window `2 w + 1` gives the
bipartite bound at degree `w` on the square `N × N`, same alphabet and exponent. -/
theorem bipartiteBoundAt_of_normalized_bound {α : Type*} [Fintype α] {N w : ℕ} {v : ℝ}
    (h : NormalizedTwoSidedWholeRowCardinalityBound N (2 * w + 1) α v) :
    BipartiteBoundAt α N N w v := by
  intro H_col H_row D hcol hrow hsym hD
  obtain ⟨h1, h2, h3⟩ := unionRel_normalized H_col H_row hcol hrow hsym
  exact h (fun j => H_col j ∪ H_row j ∪ {j}) D h1 h2 h3 (bipartite_is_fullArray H_col H_row D hD)

/-- A smaller degree is a weaker requirement. -/
theorem BipartiteBoundAt.mono_w {α : Type*} [Fintype α] {n m w w' : ℕ} {v : ℝ}
    (h : BipartiteBoundAt α n m w v) (hw : w' ≤ w) : BipartiteBoundAt α n m w' v :=
  fun H_col H_row D hcol hrow hsym hD =>
    h H_col H_row D (fun a => (hcol a).trans hw) (fun b => (hrow b).trans hw) hsym hD

/-- A larger exponent is a weaker requirement (nonempty alphabet). -/
theorem BipartiteBoundAt.mono_v {α : Type*} [Fintype α] [Nonempty α] {n m w : ℕ} {v v' : ℝ}
    (h : BipartiteBoundAt α n m w v) (hv : v ≤ v') : BipartiteBoundAt α n m w v' := by
  intro H_col H_row D hcol hrow hsym hD
  have h1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  exact (h H_col H_row D hcol hrow hsym hD).trans (Real.rpow_le_rpow_of_exponent_le h1 hv)

/-! ## The criteria -/

/-- The conjecture with the full-array bound replaced by the bipartite bound on `d × d`. -/
def BipartiteCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      BipartiteBoundAt (Fin (entryBits d) → Bool) d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2) ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ)

/-- **The bipartite criterion implies the conjecture.** -/
theorem conjecture_of_bipartiteCriterion (h : BipartiteCriterion) :
    LeanBacklog.Wall.Conjecture := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hb, hgap⟩ := h k G c hk hG hc d₀
  exact ⟨d, R, θ, δ, hd, hθ, normalized_bound_of_bipartiteBoundAt hb, hgap⟩

/-- The conjecture implies the bipartite criterion at the halved degree budget: the
conjecture's window `W + R + 1` covers bipartite hosts of degree `(W + R) / 2`. -/
theorem bipartiteCriterion_halfWindow_of_conjecture (h : LeanBacklog.Wall.Conjecture) :
    ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
      ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
        BipartiteBoundAt (Fin (entryBits d) → Bool) d d ((endWindow k G θ+R)/2)
          ((1-δ)*(d:ℝ)^2) ∧
        (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
          (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
            δ*(d*d*entryBits d:ℕ) := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hb, hgap⟩ := h k G c hk hG hc d₀
  refine ⟨d, R, θ, δ, hd, hθ, bipartiteBoundAt_of_normalized_bound ?_, hgap⟩
  intro ρ C hρ hsym hrefl hC
  exact hb ρ C (fun r => (hρ r).trans (by omega)) hsym hrefl hC

/-- Uniform rate in the bipartite form, mirroring `UniformNormalizedTwoSidedWholeRowRateCanonicalBits`. -/
def UniformBipartiteRateCanonicalBits (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    BipartiteBoundAt (Fin (entryBits d) → Bool) d d w ((rate + η) * (d : ℝ) ^ 2)

/-- One positive deficit for every degree, in the bipartite form. -/
def BipartiteCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ UniformBipartiteRateCanonicalBits (1 - δ)

/-- The uniform bipartite rate and the uniform normalized two-sided rate are the same
statement, for every rate. -/
theorem uniformBipartiteRate_iff (rate : ℝ) :
    UniformBipartiteRateCanonicalBits rate ↔
      UniformNormalizedTwoSidedWholeRowRateCanonicalBits rate := by
  constructor
  · intro h w η hη
    obtain ⟨d₀, hd₀⟩ := h w η hη
    exact ⟨d₀, fun d hd => normalized_bound_of_bipartiteBoundAt (hd₀ d hd)⟩
  · intro h w η hη
    obtain ⟨d₀, hd₀⟩ := h (2 * w + 1) η hη
    exact ⟨d₀, fun d hd => bipartiteBoundAt_of_normalized_bound (hd₀ d hd)⟩

/-- **The bipartite common deficit is the common deficit.** -/
theorem bipartiteCommonDeficit_iff_commonDeficit :
    BipartiteCommonDeficit ↔ LeanBacklog.Wall.CommonDeficit := by
  unfold BipartiteCommonDeficit LeanBacklog.Wall.CommonDeficit
  rw [commonDeficitCanonicalBits_iff_normalizedTwoSided]
  simp only [uniformBipartiteRate_iff]

theorem conjecture_of_bipartiteCommonDeficit (h : BipartiteCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  LeanBacklog.Wall.of_commonDeficit (bipartiteCommonDeficit_iff_commonDeficit.mp h)

/-- One window per resource triple, cofinally many dimensions, a deficit compared with the
limiting budget. -/
def WindowwiseBipartiteCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        BipartiteBoundAt (Fin (entryBits d) → Bool) d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

/-- **The window-wise criterion implies the bipartite criterion.** -/
theorem bipartiteCriterion_of_windowwise (h : WindowwiseBipartiteCriterion) :
    BipartiteCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨R, θ, δ, hθ, hT, hcof⟩ := h k G c hk hG hc
  obtain ⟨d₁, hd₁⟩ := budget_lt_of_budgetRate_lt hG hθ hT
  obtain ⟨d, hd, hb⟩ := hcof (max (max d₀ 1) d₁)
  exact ⟨d, R, θ, δ, (le_max_left _ _).trans hd, hθ, hb,
    hd₁ d ((le_max_right _ _).trans hd)⟩

theorem conjecture_of_windowwiseBipartiteCriterion (h : WindowwiseBipartiteCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCriterion (bipartiteCriterion_of_windowwise h)

/-! ## The far-cell form at the same size -/

/-- A far-cell bound gives the bipartite bound with the far-cell deficit. -/
theorem bipartiteBoundAt_of_farCellBoundAt {α : Type*} [Fintype α] [Nonempty α]
    {n m w q e : ℕ} {v : ℝ} (h : FarCellBoundAt α n m w q e v) :
    BipartiteBoundAt α n m w ((n * m : ℝ) - farDeficit n m q e v) :=
  fun H_col H_row D hcol hrow hsym hD =>
    bipartite_card_le_of_farCellBoundAt h H_col H_row hcol hrow hsym D hD

/-- A bipartite bound is a far-cell bound with no pinned cells, for every `q`. -/
theorem farCellBoundAt_of_bipartiteBoundAt {α : Type*} [Fintype α] {n m w : ℕ} {v : ℝ}
    (h : BipartiteBoundAt α n m w v) (q : ℕ) : FarCellBoundAt α n m w q 0 v := by
  intro H_col H_row hcol hrow hsym _
  exact ⟨∅, by simp, fun D hD => h H_col H_row D hcol hrow hsym hD.toBipartite⟩

/-- **Pointwise equivalence with the far-cell form**: pinning and expansion are free. -/
theorem bipartiteBoundAt_iff_exists_farCellBoundAt {α : Type*} [Fintype α] [Nonempty α]
    {n m w : ℕ} {Δ : ℝ} (hΔ : Δ ≤ (n * m : ℝ)) :
    BipartiteBoundAt α n m w ((n * m : ℝ) - Δ) ↔
      ∃ (q e : ℕ) (v : ℝ), FarCellBoundAt α n m w q e v ∧ Δ ≤ farDeficit n m q e v := by
  constructor
  · intro h
    refine ⟨1, 0, (n * m : ℝ) - Δ, farCellBoundAt_of_bipartiteBoundAt h 1, ?_⟩
    unfold farDeficit
    apply le_min
    · push_cast; linarith
    · simpa using hΔ
  · rintro ⟨q, e, v, hfar, hle⟩
    exact (bipartiteBoundAt_of_farCellBoundAt hfar).mono_v (by linarith)

/-! ## Licences -/

/-- A code for a host is a code for any host with more helpers. -/
theorem IsBipartiteTwoSidedCode.mono_host {n m : ℕ} {α : Type*}
    {H_col H_col' : Fin m → Finset (Fin n)} {H_row H_row' : Fin n → Finset (Fin m)}
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (hc : ∀ a, H_col a ⊆ H_col' a) (hr : ∀ b, H_row b ⊆ H_row' b) :
    IsBipartiteTwoSidedCode H_col' H_row' D :=
  ⟨fun x hx y hy a hagree => hD.1 x hx y hy a (fun b hb => hagree b (hc a hb)),
    fun x hx y hy b hagree => hD.2 x hx y hy b (fun a ha => hagree a (hr b ha))⟩

/-- No set of columns misses many rows and vice versa: no cut certifies `Δ₀` cells. -/
def NoSparseCut {n m : ℕ} (Δ₀ : ℝ) (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) : Prop :=
  (∀ A₁ : Finset (Fin m), (((n - (A₁.biUnion H_col).card) * A₁.card : ℕ) : ℝ) < Δ₀) ∧
  (∀ B₁ : Finset (Fin n), ((B₁.card * (m - (B₁.biUnion H_row).card) : ℕ) : ℝ) < Δ₀)

/-- A host with a sparse cut forces the cut's deficit on every code. -/
theorem bipartite_card_le_of_sparseCut {n m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    {Δ₀ : ℝ} (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcut : ¬ NoSparseCut Δ₀ H_col H_row)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((n * m : ℝ) - Δ₀) := by
  classical
  have hge1α : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  simp only [NoSparseCut, not_and_or, not_forall, not_lt] at hcut
  rcases hcut with ⟨A₁, hA₁⟩ | ⟨B₁, hB₁⟩
  · have hnat := bipartite_card_le_of_col_subset H_col H_row D hD A₁
    have hle_prod : (n - (A₁.biUnion H_col).card) * A₁.card ≤ n * m :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by simpa using card_le_univ A₁)
    have hcast : (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^
        ((n * m - (n - (A₁.biUnion H_col).card) * A₁.card : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hnat
    apply hcast.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    rw [Nat.cast_sub hle_prod]
    push_cast at hA₁ ⊢
    linarith
  · have hnat := bipartite_card_le_of_row_subset H_col H_row D hD B₁
    have hle_prod : B₁.card * (m - (B₁.biUnion H_row).card) ≤ n * m :=
      Nat.mul_le_mul (by simpa using card_le_univ B₁) (Nat.sub_le _ _)
    have hcast : (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^
        ((n * m - B₁.card * (m - (B₁.biUnion H_row).card) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hnat
    apply hcast.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    rw [Nat.cast_sub hle_prod]
    push_cast at hB₁ ⊢
    linarith

/-- A host with no cut certifying `n m / q²` cells is a `q`-expander (any `q`). -/
theorem isTwoSidedExpander_of_noSparseCut {n m q : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)}
    (h : NoSparseCut ((n * m : ℝ) / (q : ℝ) ^ 2) H_col H_row) :
    IsTwoSidedExpander q H_col H_row := by
  constructor
  · intro A₁ hA₁
    by_contra hlt
    have hb_le : (A₁.biUnion H_col).card ≤ n := by
      simpa using card_le_univ (A₁.biUnion H_col)
    have hkey := div_sq_le_of_nonexpand hb_le hA₁ (not_lt.mp hlt)
    have := h.1 A₁
    linarith
  · intro B₁ hB₁
    by_contra hlt
    have ha_le : (B₁.biUnion H_row).card ≤ m := by
      simpa using card_le_univ (B₁.biUnion H_row)
    have hkey := div_sq_le_of_nonexpand ha_le hB₁ (not_lt.mp hlt)
    have := h.2 B₁
    have hcomm : (m : ℝ) * n = n * m := by ring
    rw [hcomm] at hkey
    have hc2 : (((m - (B₁.biUnion H_row).card) * B₁.card : ℕ) : ℝ) =
        ((B₁.card * (m - (B₁.biUnion H_row).card) : ℕ) : ℝ) := by
      rw [Nat.mul_comm]
    linarith

/-- The licences on one host: if, whenever the host has no sparse cut, some pin set of at most
`e` cells bounds every pinned code by `|α| ^ v`, then every code on the host has at most
`|α| ^ max (v + e) (n m - Δ₀)` words. -/
theorem bipartite_card_le_of_licence_host {α : Type*} [Fintype α] [Nonempty α] {n m e : ℕ}
    {v Δ₀ : ℝ} (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (h : NoSparseCut Δ₀ H_col H_row →
      ∃ E : Finset (Fin n × Fin m), E.card ≤ e ∧
        ∀ D : Finset (Fin n × Fin m → α), IsPinnedBipartiteTwoSidedCode H_col H_row E D →
          (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (max (v + e) ((n * m : ℝ) - Δ₀)) := by
  classical
  have hge1α : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hposα : (0 : ℝ) < Fintype.card α := by linarith
  by_cases hcut : NoSparseCut Δ₀ H_col H_row
  · obtain ⟨E, hEc, hEb⟩ := h hcut
    have hpin := bipartite_card_le_of_pin_set H_col H_row D hD E _ hEb
    rw [← Real.rpow_natCast, ← Real.rpow_add hposα] at hpin
    apply hpin.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have h2 : (E.card : ℝ) ≤ e := by exact_mod_cast hEc
    exact le_trans (by linarith) (le_max_left _ _)
  · exact (bipartite_card_le_of_sparseCut H_col H_row hcut D hD).trans
      (Real.rpow_le_rpow_of_exponent_le hge1α (le_max_right _ _))

/-- **Combined licence theorem.** To prove a bipartite bound, the prover may assume the host has
no sparse cut and may pin a set of at most `e` cells. -/
theorem bipartiteBoundAt_of_licences {α : Type*} [Fintype α] [Nonempty α] {n m w e : ℕ}
    {v Δ₀ : ℝ}
    (h : ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
      (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
      (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) → NoSparseCut Δ₀ H_col H_row →
      ∃ E : Finset (Fin n × Fin m), E.card ≤ e ∧
        ∀ D : Finset (Fin n × Fin m → α), IsPinnedBipartiteTwoSidedCode H_col H_row E D →
          (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v) :
    BipartiteBoundAt α n m w (max (v + e) ((n * m : ℝ) - Δ₀)) :=
  fun H_col H_row D hcol hrow hsym hD =>
    bipartite_card_le_of_licence_host H_col H_row (h H_col H_row hcol hrow hsym) D hD

/-! ## The refutation target -/

/-- A refuting family: for one resource triple and every large `d`, for every `θ > 0` and `R`
there is a normalized two-sided code at window `endWindow k G θ + R + 1` whose deficit, in cells,
is at most the budget divided by the entry width. -/
def RefutingFamily : Prop :=
  ∃ k G c : ℕ, 5 ≤ k ∧ 1 ≤ G ∧ 4 ≤ c ∧ ∃ d₀ : ℕ, ∀ d ≥ max d₀ 1, ∀ (R : ℕ) (θ : ℝ), 0 < θ →
    ∃ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → (Fin (entryBits d) → Bool))),
      (∀ r, (ρ r).card ≤ endWindow k G θ + R + 1) ∧ (∀ r s, s ∈ ρ r ↔ r ∈ ρ s) ∧ (∀ r, r ∈ ρ r) ∧
      IsTwoSidedWholeRowCode ρ C ∧
      (Fintype.card (Fin (entryBits d) → Bool) : ℝ) ^
        ((d:ℝ)^2 - (((2*(adaptiveAllowance k G c*d+cutBudget k G c d θ) : ℕ) : ℝ) +
            ((entryBits d*crossBudget d (endWindow k G θ) R : ℕ) : ℝ)) / (entryBits d : ℝ))
        ≤ (C.card : ℝ)

theorem one_lt_card_bits (d : ℕ) : (1 : ℝ) < (Fintype.card (Fin (entryBits d) → Bool) : ℝ) := by
  have hb : 1 ≤ entryBits d := by unfold entryBits; omega
  have : 1 < Fintype.card (Fin (entryBits d) → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact Nat.one_lt_two_pow (by omega)
  exact_mod_cast this

/-- The dichotomy at one size: either some admissible code reaches `A ^ t` words, or the
normalized bound holds at some exponent `e < t`. -/
theorem exists_code_or_bound {d W : ℕ} {α : Type*} [Fintype α] [Inhabited α]
    (hα : (1 : ℝ) < Fintype.card α) (hW : 1 ≤ W) (t : ℝ) :
    (∃ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
      (∀ r, (ρ r).card ≤ W) ∧ (∀ r s, s ∈ ρ r ↔ r ∈ ρ s) ∧ (∀ r, r ∈ ρ r) ∧
      IsTwoSidedWholeRowCode ρ C ∧ (Fintype.card α : ℝ) ^ t ≤ (C.card : ℝ)) ∨
    ∃ e : ℝ, e < t ∧ NormalizedTwoSidedWholeRowCardinalityBound d W α e := by
  classical
  by_cases hex : ∃ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
      (∀ r, (ρ r).card ≤ W) ∧ (∀ r s, s ∈ ρ r ↔ r ∈ ρ s) ∧ (∀ r, r ∈ ρ r) ∧
      IsTwoSidedWholeRowCode ρ C ∧ (Fintype.card α : ℝ) ^ t ≤ (C.card : ℝ)
  · exact Or.inl hex
  right
  push Not at hex
  set A : ℝ := (Fintype.card α : ℝ) with hAdef
  have hA0 : 0 < A := by linarith
  set T : ℝ := A ^ t with hTdef
  have hT0 : 0 < T := Real.rpow_pos_of_pos hA0 t
  -- the singleton code is admissible
  have hsing : (1 : ℝ) < T := by
    have h := hex (fun r => {r}) {fun _ => default} (fun r => by simp [hW]) (fun r s => by
      simp only [mem_singleton]; exact eq_comm) (fun r => mem_singleton_self r)
      ⟨by rw [wholeRowCode_iff]; intro x hx y hy _ _ _ i; simp at hx hy; rw [hx, hy],
        by intro x hx y hy _ _ i; simp at hx hy; rw [hx, hy]⟩
    simpa using h
  set M : ℕ := ⌈T⌉₊ - 1 with hMdef
  have hceil_lt : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
  have hceil2 : 2 ≤ ⌈T⌉₊ := by
    have : 1 < ⌈T⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hsing)
    omega
  have hM1 : (1 : ℝ) ≤ M := by
    have : 1 ≤ M := by omega
    exact_mod_cast this
  have hMT : (M : ℝ) < T := by
    have hcast : (M : ℝ) = (⌈T⌉₊ : ℝ) - 1 := by
      rw [hMdef, Nat.cast_sub (by omega)]; simp
    linarith
  have hM0 : (0 : ℝ) < M := by linarith
  refine ⟨Real.logb A M, ?_, ?_⟩
  · have hpow : A ^ Real.logb A M = M := Real.rpow_logb hA0 (by linarith) hM0
    rw [← Real.rpow_lt_rpow_left_iff hα, hpow]
    exact hMT
  · intro ρ C hρ hsym hrefl hC
    rw [Real.rpow_logb hA0 (by linarith) hM0]
    have hlt : (C.card : ℝ) < T := hex ρ C hρ hsym hrefl hC
    have hlt' : C.card < ⌈T⌉₊ := by
      have := lt_of_lt_of_le hlt (Nat.le_ceil T)
      exact_mod_cast this
    have : C.card ≤ M := by omega
    exact_mod_cast this

/-- **A refuting family refutes the conjecture.** -/
theorem not_conjecture_of_refutingFamily (hR : RefutingFamily) :
    ¬ LeanBacklog.Wall.Conjecture := by
  intro hC
  obtain ⟨k, G, c, hk, hG, hc, d₀, hfam⟩ := hR
  obtain ⟨d, R, θ, δ, hd, hθ, hb, hgap⟩ := hC k G c hk hG hc d₀
  obtain ⟨ρ, C, hρ, hsym, hrefl, hcode, hT⟩ := hfam d hd R θ hθ
  have hα := one_lt_card_bits d
  have hle := hT.trans (hb ρ C hρ hsym hrefl hcode)
  rw [Real.rpow_le_rpow_left_iff hα] at hle
  have hb1 : (1 : ℝ) ≤ entryBits d := by
    exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
  have hbpos : (0 : ℝ) < entryBits d := by linarith
  set B : ℝ := (((2*(adaptiveAllowance k G c*d+cutBudget k G c d θ) : ℕ) : ℝ) +
            ((entryBits d*crossBudget d (endWindow k G θ) R : ℕ) : ℝ)) with hBdef
  have hgap' : B < δ * ((d:ℝ)^2 * entryBits d) := by
    have : ((d*d*entryBits d : ℕ) : ℝ) = (d:ℝ)^2 * entryBits d := by push_cast; ring
    rw [← this]; exact hgap
  have hdiv : B / (entryBits d : ℝ) * entryBits d = B := div_mul_cancel₀ B hbpos.ne'
  have hle' : δ * (d:ℝ)^2 ≤ B / (entryBits d : ℝ) := by linarith
  have := mul_le_mul_of_nonneg_right hle' hbpos.le
  nlinarith

/-- **The negation of a refuting family is the conjecture.** -/
theorem conjecture_of_not_refutingFamily (hR : ¬ RefutingFamily) :
    LeanBacklog.Wall.Conjecture := by
  intro k G c hk hG hc d₀
  by_contra hneg
  apply hR
  refine ⟨k, G, c, hk, hG, hc, d₀, fun d hd R θ hθ => ?_⟩
  have hα := one_lt_card_bits d
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_max_right _ _).trans hd
  set B : ℝ := (((2*(adaptiveAllowance k G c*d+cutBudget k G c d θ) : ℕ) : ℝ) +
            ((entryBits d*crossBudget d (endWindow k G θ) R : ℕ) : ℝ)) with hBdef
  rcases exists_code_or_bound (d := d) (W := endWindow k G θ + R + 1)
      (α := Fin (entryBits d) → Bool) hα (by omega) ((d:ℝ)^2 - B / (entryBits d : ℝ)) with
    hex | ⟨e, he, hbound⟩
  · exact hex
  · exfalso
    apply hneg
    have hd2 : (0 : ℝ) < (d:ℝ)^2 := by positivity
    refine ⟨d, R, θ, 1 - e / (d:ℝ)^2, hd, hθ, ?_, ?_⟩
    · have heq : (1 - (1 - e / (d:ℝ)^2)) * (d:ℝ)^2 = e := by field_simp; ring
      rw [heq]; exact hbound
    · have hb1 : (1 : ℝ) ≤ entryBits d := by
        exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
      have hbpos : (0 : ℝ) < entryBits d := by linarith
      have hcast : ((d*d*entryBits d : ℕ) : ℝ) = (d:ℝ)^2 * entryBits d := by push_cast; ring
      rw [hcast]
      change B < _
      have hrhs : (1 - e / (d:ℝ)^2) * ((d:ℝ)^2 * entryBits d) = ((d:ℝ)^2 - e) * entryBits d := by
        field_simp
      rw [hrhs]
      have hdiv : B / (entryBits d : ℝ) * entryBits d = B := div_mul_cancel₀ B hbpos.ne'
      have hlt : B / (entryBits d : ℝ) < (d:ℝ)^2 - e := by linarith
      have := mul_lt_mul_of_pos_right hlt hbpos
      linarith

/-- **The conjecture holds exactly when there is no refuting family.** -/
theorem conjecture_iff_not_refutingFamily :
    LeanBacklog.Wall.Conjecture ↔ ¬ RefutingFamily :=
  ⟨fun h hR => not_conjecture_of_refutingFamily hR h, conjecture_of_not_refutingFamily⟩

/-- A bipartite refuting family: square bipartite hosts of degree `w'` with `2 w' + 1` within
the window, and the same cardinality requirement. -/
def BipartiteRefutingFamily : Prop :=
  ∃ k G c : ℕ, 5 ≤ k ∧ 1 ≤ G ∧ 4 ≤ c ∧ ∃ d₀ : ℕ, ∀ d ≥ max d₀ 1, ∀ (R : ℕ) (θ : ℝ), 0 < θ →
    ∃ (w' : ℕ) (H_col H_row : Fin d → Finset (Fin d))
      (D : Finset (Fin d × Fin d → (Fin (entryBits d) → Bool))),
      2 * w' + 1 ≤ endWindow k G θ + R + 1 ∧
      (∀ a, (H_col a).card ≤ w') ∧ (∀ b, (H_row b).card ≤ w') ∧
      (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) ∧ IsBipartiteTwoSidedCode H_col H_row D ∧
      (Fintype.card (Fin (entryBits d) → Bool) : ℝ) ^
        ((d:ℝ)^2 - (((2*(adaptiveAllowance k G c*d+cutBudget k G c d θ) : ℕ) : ℝ) +
            ((entryBits d*crossBudget d (endWindow k G θ) R : ℕ) : ℝ)) / (entryBits d : ℝ))
        ≤ (D.card : ℝ)

theorem refutingFamily_of_bipartite (h : BipartiteRefutingFamily) : RefutingFamily := by
  obtain ⟨k, G, c, hk, hG, hc, d₀, hfam⟩ := h
  refine ⟨k, G, c, hk, hG, hc, d₀, fun d hd R θ hθ => ?_⟩
  obtain ⟨w', H_col, H_row, D, hw, hcol, hrow, hsym, hD, hT⟩ := hfam d hd R θ hθ
  obtain ⟨h1, h2, h3⟩ := unionRel_normalized H_col H_row hcol hrow hsym
  exact ⟨fun j => H_col j ∪ H_row j ∪ {j}, D, fun r => (h1 r).trans hw, h2, h3,
    bipartite_is_fullArray H_col H_row D hD, hT⟩

theorem not_conjecture_of_bipartiteRefutingFamily (h : BipartiteRefutingFamily) :
    ¬ LeanBacklog.Wall.Conjecture :=
  not_conjecture_of_refutingFamily (refutingFamily_of_bipartite h)

#print axioms fullArray_is_bipartite
#print axioms bipartite_is_fullArray
#print axioms normalized_bound_of_bipartiteBoundAt
#print axioms bipartiteBoundAt_of_normalized_bound
#print axioms BipartiteBoundAt.mono_w
#print axioms BipartiteBoundAt.mono_v
#print axioms conjecture_of_bipartiteCriterion
#print axioms bipartiteCriterion_halfWindow_of_conjecture
#print axioms uniformBipartiteRate_iff
#print axioms bipartiteCommonDeficit_iff_commonDeficit
#print axioms conjecture_of_bipartiteCommonDeficit
#print axioms bipartiteCriterion_of_windowwise
#print axioms conjecture_of_windowwiseBipartiteCriterion
#print axioms bipartiteBoundAt_of_farCellBoundAt
#print axioms farCellBoundAt_of_bipartiteBoundAt
#print axioms bipartiteBoundAt_iff_exists_farCellBoundAt
#print axioms IsBipartiteTwoSidedCode.mono_host
#print axioms bipartite_card_le_of_sparseCut
#print axioms isTwoSidedExpander_of_noSparseCut
#print axioms bipartite_card_le_of_licence_host
#print axioms bipartiteBoundAt_of_licences
#print axioms exists_code_or_bound
#print axioms not_conjecture_of_refutingFamily
#print axioms conjecture_of_not_refutingFamily
#print axioms conjecture_iff_not_refutingFamily
#print axioms refutingFamily_of_bipartite
#print axioms not_conjecture_of_bipartiteRefutingFamily

end LeanBacklog.WallBipartite

import WallFarCells
import MotionDepthCodes.StorageCode

/-!
# The Shannon form of the far-cell criteria

A bound on every polymatroid that satisfies the recovery constraints of a pinned bipartite
two-sided code implies the far-cell bound for codes over every finite alphabet: the entropy
function of the uniform law on a code, normalised by `log |α|`, is such a polymatroid.

`IsFarFeasible` lists the constraints, in units of one cell: a polymatroid with
`h {p} ≤ 1`, valid for the column helpers and for the row helpers, where a pinned cell is a
constant and needs no helpers. The threshold `ρ` of the uniform corollary is a free
parameter, measured against all `n m` cells of the quadrant. No value of it is asserted
here, and one half is not singled out: for whole-row codes on the full array, measured
against the far cells alone, one half fails on a finite host (the Clebsch code of
`FarClebsch.lean` has ten free bits on sixteen far cells with every near cell fixed).
That example has zero density and no transfer of it to the class below is claimed.
Whether a threshold below one holds for large `d` at a fixed window is open.
-/

namespace LeanBacklog.WallFarShannon

open Finset LeanBacklog.WallFarCells
open Transpose LeanBacklog.RowSpread LeanBacklog.BlockTCC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Helper cells of the cell `p = (b, a)` for recovering its column from the helper rows of `a`,
with the cells of `E` treated as constants: a pinned cell needs no helpers. -/
def pinnedColHelpers {n m : ℕ} (H_col : Fin m → Finset (Fin n)) (E : Finset (Fin n × Fin m))
    (p : Fin n × Fin m) : Finset (Fin n × Fin m) :=
  if p ∈ E then ∅ else univ.filter fun c => c.1 ∈ H_col p.2 ∧ c ∉ E

/-- Helper cells of the cell `p = (b, a)` for recovering its row from the helper columns of
`b`, with the cells of `E` treated as constants. -/
def pinnedRowHelpers {n m : ℕ} (H_row : Fin n → Finset (Fin m)) (E : Finset (Fin n × Fin m))
    (p : Fin n × Fin m) : Finset (Fin n × Fin m) :=
  if p ∈ E then ∅ else univ.filter fun c => c.2 ∈ H_row p.1 ∧ c ∉ E

/-- Feasible polymatroids, in units of one cell. -/
structure IsFarFeasible {n m : ℕ} (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m))
    (E : Finset (Fin n × Fin m)) (h : Finset (Fin n × Fin m) → ℝ) : Prop where
  poly : MotionDepthCodes.IsPolymatroid h
  cap : ∀ p, h {p} ≤ 1
  col : MotionDepthCodes.IsValid h (pinnedColHelpers H_col E)
  row : MotionDepthCodes.IsValid h (pinnedRowHelpers H_row E)

/-- Sanity: a feasible function vanishes on the pinned cells. -/
theorem isFarFeasible_pinned_zero {n m : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {E : Finset (Fin n × Fin m)}
    {h : Finset (Fin n × Fin m) → ℝ} (hf : IsFarFeasible H_col H_row E h) : h E = 0 := by
  have hsing : ∀ p ∈ E, h {p} = 0 := by
    intro p hp
    have hv := hf.col p
    simp only [pinnedColHelpers, hp, ↓reduceIte] at hv
    rw [← hf.poly.empty, ← hv]
    rfl
  apply le_antisymm
  · calc h E ≤ ∑ p ∈ E, h {p} := hf.poly.le_sum_singleton E
      _ = 0 := sum_eq_zero hsing
  · exact hf.poly.nonneg E

/-- Sanity: the zero function is feasible. -/
theorem isFarFeasible_zero {n m : ℕ} (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) (E : Finset (Fin n × Fin m)) :
    IsFarFeasible H_col H_row E (fun _ => 0) where
  poly := ⟨rfl, fun _ _ _ => le_refl _, fun _ _ => by norm_num⟩
  cap := fun _ => by norm_num
  col := fun _ => rfl
  row := fun _ => rfl

/-- Sanity: every feasible function is at most `n m`. -/
theorem IsFarFeasible.univ_le {n m : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {E : Finset (Fin n × Fin m)}
    {h : Finset (Fin n × Fin m) → ℝ} (hf : IsFarFeasible H_col H_row E h) :
    h univ ≤ ((n * m : ℕ) : ℝ) := by
  calc h univ ≤ ∑ p ∈ (univ : Finset (Fin n × Fin m)), h {p} := hf.poly.le_sum_singleton _
    _ ≤ ∑ _p ∈ (univ : Finset (Fin n × Fin m)), (1 : ℝ) := sum_le_sum fun p _ => hf.cap p
    _ = ((n * m : ℕ) : ℝ) := by simp

/-- A pinned code is recoverable from the pinned column helpers. -/
theorem isRecoverable_col_of_pinned {n m : ℕ} {α : Type*}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {E : Finset (Fin n × Fin m)} {D : Finset (Fin n × Fin m → α)}
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) :
    MotionDepthCodes.IsRecoverable (pinnedColHelpers H_col E)
      (fun x : D => (x : Fin n × Fin m → α)) := by
  intro v ω ω' hagree
  by_cases hv : v ∈ E
  · exact hD.1 ω ω.2 ω' ω'.2 v hv
  · obtain ⟨b, a⟩ := v
    apply hD.2.1 ω ω.2 ω' ω'.2 a ?_ b
    intro b' hb' a' hnot
    apply hagree
    simp [pinnedColHelpers, hv, hb', hnot]

/-- A pinned code is recoverable from the pinned row helpers. -/
theorem isRecoverable_row_of_pinned {n m : ℕ} {α : Type*}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {E : Finset (Fin n × Fin m)} {D : Finset (Fin n × Fin m → α)}
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) :
    MotionDepthCodes.IsRecoverable (pinnedRowHelpers H_row E)
      (fun x : D => (x : Fin n × Fin m → α)) := by
  intro v ω ω' hagree
  by_cases hv : v ∈ E
  · exact hD.1 ω ω.2 ω' ω'.2 v hv
  · obtain ⟨b, a⟩ := v
    apply hD.2.2 ω ω.2 ω' ω'.2 b ?_ a
    intro a' ha' b' hnot
    apply hagree
    simp [pinnedRowHelpers, hv, ha', hnot]

/-- For any law on words recoverable from both pinned helper maps, the entropy function
normalised by `log |α|` is feasible. -/
theorem isFarFeasible_of_recoverable {n m : ℕ} {α : Type*} [Fintype α]
    (hα : 2 ≤ Fintype.card α)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (E : Finset (Fin n × Fin m)) {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → Fin n × Fin m → α)
    (hcol : MotionDepthCodes.IsRecoverable (pinnedColHelpers H_col E) X)
    (hrow : MotionDepthCodes.IsRecoverable (pinnedRowHelpers H_row E) X) :
    IsFarFeasible H_col H_row E
      (fun S => MotionDepthCodes.codeEntropy p X S / Real.log (Fintype.card α)) := by
  have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hL : 0 < Real.log (Fintype.card α) :=
    Real.log_pos (by exact_mod_cast (show 1 < Fintype.card α by omega))
  have hg := MotionDepthCodes.codeEntropy_isPolymatroid p X hp hp1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [hg.empty, zero_div]
  · intro S T hST
    exact div_le_div_of_nonneg_right (hg.mono hST) hL.le
  · intro A B
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (hg.submod A B) hL.le
  · intro q
    exact (div_le_one hL).mpr (MotionDepthCodes.codeEntropy_singleton_le p X hp hp1 q)
  · intro v
    beta_reduce
    rw [MotionDepthCodes.codeEntropy_isValid p X hp hcol v]
  · intro v
    beta_reduce
    rw [MotionDepthCodes.codeEntropy_isValid p X hp hrow v]

/-- The normalised entropy function of the uniform law on a nonempty pinned code over an
alphabet with at least two symbols is feasible. -/
theorem isFarFeasible_normalizedEntropy {n m : ℕ} {α : Type*} [Fintype α]
    (hα : 2 ≤ Fintype.card α)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (E : Finset (Fin n × Fin m)) (D : Finset (Fin n × Fin m → α))
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) (hne : D.Nonempty) :
    IsFarFeasible H_col H_row E (fun S =>
      MotionDepthCodes.codeEntropy (fun _ : D => ((D.card : ℝ))⁻¹)
        (fun x => (x : Fin n × Fin m → α)) S / Real.log (Fintype.card α)) := by
  have hc0 : (0 : ℝ) < D.card := by exact_mod_cast hne.card_pos
  have hp : ∀ ω : D, (0 : ℝ) ≤ (fun _ : D => ((D.card : ℝ))⁻¹) ω :=
    fun _ => inv_nonneg.mpr hc0.le
  have hp1 : ∑ ω : D, (fun _ : D => ((D.card : ℝ))⁻¹) ω = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp
  exact isFarFeasible_of_recoverable hα H_col H_row E _ hp hp1 _
    (isRecoverable_col_of_pinned hD) (isRecoverable_row_of_pinned hD)

/-- **Per-host bridge.** A bound `t` on every feasible polymatroid bounds every pinned code by
`|α| ^ t`, over every nonempty finite alphabet. -/
theorem pinned_card_le_of_polymatroid_bound {n m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (E : Finset (Fin n × Fin m)) (t : ℝ)
    (hbound : ∀ h, IsFarFeasible H_col H_row E h → h univ ≤ t)
    (D : Finset (Fin n × Fin m → α)) (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ t := by
  classical
  have ht : 0 ≤ t := hbound _ (isFarFeasible_zero H_col H_row E)
  have hαpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rcases D.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hαpos.le t
  by_cases hα : 2 ≤ Fintype.card α
  · have hb := hbound _ (isFarFeasible_normalizedEntropy hα H_col H_row E D hD hne)
    rw [MotionDepthCodes.codeEntropy_univ_uniform D hne] at hb
    have hL : 0 < Real.log (Fintype.card α) :=
      Real.log_pos (by exact_mod_cast (show 1 < Fintype.card α by omega))
    have hlog : Real.log D.card ≤ t * Real.log (Fintype.card α) := (div_le_iff₀ hL).mp hb
    have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hne.card_pos
    exact (Real.le_rpow_iff_log_le hDpos hαpos).mpr hlog
  · have h1 : Fintype.card α = 1 := by
      have := Fintype.card_pos (α := α)
      omega
    have hD1 : D.card ≤ 1 := by
      have h := card_le_univ D
      rw [Fintype.card_fun, h1, one_pow] at h
      exact h
    rw [h1, Nat.cast_one, Real.one_rpow]
    exact_mod_cast hD1

/-- The far-cell bound in polymatroid form: the inner statement bounds every feasible
polymatroid; no alphabet is mentioned. -/
def FarPolymatroidBoundAt (n m w q e : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    IsTwoSidedExpander q H_col H_row →
    ∃ E : Finset (Fin n × Fin m), E.card ≤ e ∧
      ∀ h, IsFarFeasible H_col H_row E h → h univ ≤ v

/-- Sanity: the polymatroid bound holds with no pinned cells and exponent `n m`. -/
theorem farPolymatroidBoundAt_trivial (n m w q : ℕ) :
    FarPolymatroidBoundAt n m w q 0 ((n * m : ℕ) : ℝ) := by
  intro H_col H_row _ _ _ _
  exact ⟨∅, by simp, fun h hf => hf.univ_le⟩

/-- **The polymatroid bound implies the far-cell bound** over every nonempty finite alphabet. -/
theorem farCellBoundAt_of_polymatroid {n m w q e : ℕ} {v : ℝ} {α : Type*} [Fintype α]
    [Nonempty α] (h : FarPolymatroidBoundAt n m w q e v) : FarCellBoundAt α n m w q e v := by
  intro H_col H_row hcol hrow hsym hE
  obtain ⟨E, hEc, hb⟩ := h H_col H_row hcol hrow hsym hE
  exact ⟨E, hEc, fun D hD => pinned_card_le_of_polymatroid_bound H_col H_row E v hb D hD⟩

/-- The far-cell criterion with the polymatroid bound in place of the code bound. -/
def FarPolymatroidCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R m q e : ℕ) (θ v : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧ m ≤ d ∧ 1 ≤ q ∧
      FarPolymatroidBoundAt (d - m) m (endWindow k G θ + R + 1) q e v ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          farDeficit (d - m) m q e v * (entryBits d : ℝ)

theorem farCellCriterion_of_polymatroidCriterion (h : FarPolymatroidCriterion) :
    FarCellCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, m, q, e, θ, v, hd, hθ, hm, hq, hfar, hgap⟩ := h k G c hk hG hc d₀
  exact ⟨d, R, m, q, e, θ, v, hd, hθ, hm, hq, farCellBoundAt_of_polymatroid hfar, hgap⟩

theorem conjecture_of_farPolymatroidCriterion (h : FarPolymatroidCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_farCellCriterion (farCellCriterion_of_polymatroidCriterion h)

/-- The uniform polymatroid bound with a free threshold `ρ`. -/
def UniformFarPolymatroidBound (L : ℕ → ℕ) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ w : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (H_col : Fin (d / 2) → Finset (Fin (d - d / 2)))
      (H_row : Fin (d - d / 2) → Finset (Fin (d / 2))),
      (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
      (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) → IsTwoSidedExpander q H_col H_row →
      ∀ h, IsFarFeasible H_col H_row (closeBall H_col H_row (L w)) h →
        h univ ≤ ρ * (((d - d / 2) * (d / 2) : ℕ) : ℝ)

/-- A uniform polymatroid bound below one gives the uniform far-cell deficit `1 - ρ`. -/
theorem uniformFarCellDeficit_of_polymatroid (L : ℕ → ℕ) (q : ℕ) (ρ : ℝ) (hρ : ρ < 1) :
    UniformFarPolymatroidBound L q ρ → UniformFarCellDeficit L q := by
  intro h
  refine ⟨1 - ρ, by linarith, fun w => ?_⟩
  obtain ⟨d₀, hd₀⟩ := h w
  refine ⟨d₀, fun d hd H_col H_row D hcol hrow hsym hE hD => ?_⟩
  have hρ' : (1 - (1 - ρ)) = ρ := by ring
  rw [hρ']
  exact pinned_card_le_of_polymatroid_bound H_col H_row _ _
    (hd₀ d hd H_col H_row hcol hrow hsym hE) D hD

/-- **A uniform polymatroid bound below one implies the conjecture.** -/
theorem conjecture_of_uniformFarPolymatroidBound (L : ℕ → ℕ) (q : ℕ) (hq : 2 ≤ q) (ρ : ℝ)
    (hρ : ρ < 1) : UniformFarPolymatroidBound L q ρ → LeanBacklog.Wall.Conjecture := fun h =>
  conjecture_of_uniformFarCellDeficit L q hq (uniformFarCellDeficit_of_polymatroid L q ρ hρ h)

#print axioms isFarFeasible_pinned_zero
#print axioms isFarFeasible_zero
#print axioms isFarFeasible_normalizedEntropy
#print axioms pinned_card_le_of_polymatroid_bound
#print axioms farPolymatroidBoundAt_trivial
#print axioms farCellBoundAt_of_polymatroid
#print axioms farCellCriterion_of_polymatroidCriterion
#print axioms conjecture_of_farPolymatroidCriterion
#print axioms uniformFarCellDeficit_of_polymatroid
#print axioms conjecture_of_uniformFarPolymatroidBound

end LeanBacklog.WallFarShannon

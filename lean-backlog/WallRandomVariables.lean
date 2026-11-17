import WallBundle

/-!
# The random-variable form of the bundle bound

One random variable `Y · u` per vertex `u` of a bipartite host, under the uniform law on a
finite nonempty set `Ω`. If every vertex is a function of its neighbours and adding a vertex
gains at most `newCells · L` nats, the hypothesis bounds the joint entropy by `v · L`
(`RandomVariableBoundAt`).

* The bundle hypothesis implies this form (`randomVariableBoundAt_of_bundleBoundAt`), so it is
  not stronger than the polymatroid statement.
* It bounds every bipartite two-sided code (`bipartiteBoundAt_of_randomVariableBoundAt`): take
  `Ω` the code with the uniform law, `Y x u` the restriction of the word `x` to the cells of
  `u`, and `L = log |α|`.
* One common deficit for this form implies the conjecture
  (`conjecture_of_randomVariableCommonDeficit`).

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallRandomVariables

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite LeanBacklog.WallBundle

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- Entropy, in nats, of the variables `Y · u`, `u ∈ S`, under the uniform law on the finite
set `Ω`. -/
noncomputable def unifEntropy {Ω β : Type} [Fintype Ω] [Fintype β] {n m : ℕ}
    (Y : Ω → (Fin m ⊕ Fin n) → β) (S : Finset (Fin m ⊕ Fin n)) : ℝ :=
  MotionDepthCodes.codeEntropy (fun _ : Ω => ((Fintype.card Ω : ℝ))⁻¹) Y S

/-- The random-variable form at one size. `Ω` is a finite nonempty set with the uniform law,
`Y` attaches one random variable to each vertex, `L > 0` is the unit of entropy. If every
vertex is a function of its neighbours and adding a vertex gains at most `newCells · L`, the
joint entropy is at most `v · L`. -/
def RandomVariableBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (β : Type) [Fintype β]
      (Y : Ω → (Fin m ⊕ Fin n) → β) (L : ℝ), 0 < L →
      MotionDepthCodes.IsRecoverable (nbrs H_col H_row) Y →
      (∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        unifEntropy Y (insert u K) - unifEntropy Y K ≤ (newCells K u : ℝ) * L) →
      unifEntropy Y univ ≤ v * L

/-- **The random-variable hypothesis.** One deficit `δ` for every degree bound and all large
sizes. -/
def RandomVariableCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    RandomVariableBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-! ## The guard: the bundle bound implies the random-variable bound -/

section Guard

variable {Ω β : Type} [Fintype Ω] [Nonempty Ω] [Fintype β] {n m : ℕ}

omit [Nonempty Ω] in
theorem unif_nonneg : ∀ _ω : Ω, (0 : ℝ) ≤ ((Fintype.card Ω : ℝ))⁻¹ :=
  fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem unif_sum : ∑ _ω : Ω, ((Fintype.card Ω : ℝ))⁻¹ = 1 := by
  have h : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- The normalised entropy of recoverable variables with capped gains is admissible. -/
theorem isBundleAdmissible_unifEntropy (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) (Y : Ω → (Fin m ⊕ Fin n) → β) {L : ℝ} (hL : 0 < L)
    (hrec : MotionDepthCodes.IsRecoverable (nbrs H_col H_row) Y)
    (hcap : ∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
      unifEntropy Y (insert u K) - unifEntropy Y K ≤ (newCells K u : ℝ) * L) :
    IsBundleAdmissible H_col H_row (fun S => unifEntropy Y S / L) := by
  have hp := MotionDepthCodes.codeEntropy_isPolymatroid
    (fun _ : Ω => ((Fintype.card Ω : ℝ))⁻¹) Y unif_nonneg unif_sum
  have hv := MotionDepthCodes.codeEntropy_isValid
    (fun _ : Ω => ((Fintype.card Ω : ℝ))⁻¹) Y unif_nonneg hrec
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show unifEntropy Y ∅ / L = 0
    rw [unifEntropy, hp.empty, zero_div]
  · intro S T hST
    exact div_le_div_of_nonneg_right (hp.mono hST) hL.le
  · intro S T
    show unifEntropy Y (S ∪ T) / L + unifEntropy Y (S ∩ T) / L ≤
      unifEntropy Y S / L + unifEntropy Y T / L
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (hp.submod S T) hL.le
  · intro K u hu
    show unifEntropy Y (insert u K) / L - unifEntropy Y K / L ≤ _
    rw [← sub_div, div_le_iff₀ hL]
    exact hcap K u hu
  · intro u
    show unifEntropy Y (insert u (nbrs H_col H_row u)) / L =
      unifEntropy Y (nbrs H_col H_row u) / L
    rw [unifEntropy, unifEntropy, hv u]

end Guard

/-- **The bundle bound implies the random-variable bound.** -/
theorem randomVariableBoundAt_of_bundleBoundAt {n m w : ℕ} {v : ℝ}
    (h : BundleBoundAt n m w v) : RandomVariableBoundAt n m w v := by
  intro H_col H_row hcol hrow hsym Ω _ _ β _ Y L hL hrec hcap
  have hb : unifEntropy Y univ / L ≤ v := h H_col H_row hcol hrow hsym _
    (isBundleAdmissible_unifEntropy H_col H_row Y hL hrec hcap)
  rwa [div_le_iff₀ hL] at hb

/-! ## The bridge from codes -/

section Bridge

variable {n m : ℕ} {α : Type} [Fintype α]

/-- The restriction of a word to the cells of a vertex. -/
def bundleVar (D : Finset (Fin n × Fin m → α)) (x : D) (u : Fin m ⊕ Fin n) :
    Fin n × Fin m → Option α :=
  MotionDepthCodes.view (cellsOf {u}) (x : Fin n × Fin m → α)

theorem mem_cellsOf_singleton_inl {a : Fin m} {p : Fin n × Fin m} :
    p ∈ cellsOf ({Sum.inl a} : Finset (Fin m ⊕ Fin n)) ↔ p.2 = a := by
  simp [mem_cellsOf]

theorem mem_cellsOf_singleton_inr {b : Fin n} {p : Fin n × Fin m} :
    p ∈ cellsOf ({Sum.inr b} : Finset (Fin m ⊕ Fin n)) ↔ p.1 = b := by
  simp [mem_cellsOf]

theorem mem_cellsOf_iff_exists {S : Finset (Fin m ⊕ Fin n)} {p : Fin n × Fin m} :
    p ∈ cellsOf S ↔ ∃ u ∈ S, p ∈ cellsOf ({u} : Finset (Fin m ⊕ Fin n)) := by
  simp only [mem_cellsOf, mem_singleton]
  constructor
  · rintro (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  · rintro ⟨u, hu, h | h⟩
    · exact Or.inl (h ▸ hu)
    · exact Or.inr (h ▸ hu)

omit [Fintype α] in
/-- Two words of a code that agree on the cells of all neighbours of `u` agree on the cells
of `u`. -/
theorem agree_cellsOf_of_nbrs {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D)
    {x y : Fin n × Fin m → α} (hx : x ∈ D) (hy : y ∈ D) (u : Fin m ⊕ Fin n)
    (h : ∀ u' ∈ nbrs H_col H_row u, ∀ p ∈ cellsOf ({u'} : Finset (Fin m ⊕ Fin n)), x p = y p) :
    ∀ p ∈ cellsOf ({u} : Finset (Fin m ⊕ Fin n)), x p = y p := by
  cases u with
  | inl a =>
    intro p hp
    rw [mem_cellsOf_singleton_inl] at hp
    have := hD.1 x hx y hy a (fun b hb a' => h (Sum.inr b)
      (by simp [nbrs, hb]) (b, a') (by rw [mem_cellsOf_singleton_inr])) p.1
    have hp' : p = (p.1, a) := Prod.ext rfl hp
    rw [hp']
    exact this
  | inr b =>
    intro p hp
    rw [mem_cellsOf_singleton_inr] at hp
    have := hD.2 x hx y hy b (fun a ha b' => h (Sum.inl a)
      (by simp [nbrs, ha]) (b', a) (by rw [mem_cellsOf_singleton_inl])) p.2
    have hp' : p = (b, p.2) := Prod.ext hp rfl
    rw [hp']
    exact this

omit [Fintype α] in
/-- The vertex variables of a code are recoverable from the neighbours. -/
theorem isRecoverable_bundleVar {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    MotionDepthCodes.IsRecoverable (nbrs H_col H_row) (bundleVar D) := by
  intro u x y h
  simp only [bundleVar, MotionDepthCodes.view_eq_iff] at h ⊢
  exact agree_cellsOf_of_nbrs hD x.2 y.2 u h

/-- The entropy of the vertex variables of `S` is the entropy of the cells of `S`. -/
theorem unifEntropy_bundleVar (D : Finset (Fin n × Fin m → α)) (hne : D.Nonempty)
    (S : Finset (Fin m ⊕ Fin n)) :
    unifEntropy (bundleVar D) S =
      MotionDepthCodes.codeEntropy (fun _ : D => ((D.card : ℝ))⁻¹)
        (fun x => (x : Fin n × Fin m → α)) (cellsOf S) := by
  have : Nonempty D := hne.to_subtype
  unfold unifEntropy MotionDepthCodes.codeEntropy
  rw [Fintype.card_coe]
  apply TransposeFollowup.observationEntropy_eq_of_same_fibers _
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  intro x y
  simp only [MotionDepthCodes.view_eq_iff, bundleVar]
  constructor
  · intro h p hp
    obtain ⟨u, hu, hpu⟩ := mem_cellsOf_iff_exists.mp hp
    exact h u hu p hpu
  · intro h u hu p hpu
    exact h p (mem_cellsOf_iff_exists.mpr ⟨u, hu, hpu⟩)

/-- **The random-variable bound bounds every code.** -/
theorem bipartiteBoundAt_of_randomVariableBoundAt {n m w : ℕ} {v : ℝ} [Nonempty α]
    (h : RandomVariableBoundAt n m w v) : BipartiteBoundAt α n m w v := by
  intro H_col H_row D hcol hrow hsym hD
  rcases D.eq_empty_or_nonempty with hDe | hne
  · rw [hDe, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) v
  have hq1 : 1 ≤ Fintype.card α := Fintype.card_pos
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hq | hq
  · -- one symbol: at most one word
    have hq' : Fintype.card α = 1 := by omega
    have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hq'.le
    have hle : D.card ≤ 1 := by
      apply card_le_one.mpr
      intro x _ y _
      funext p
      exact Subsingleton.elim _ _
    rw [hq', Nat.cast_one, Real.one_rpow]
    exact_mod_cast hle
  have : Nonempty D := hne.to_subtype
  have hL : 0 < Real.log (Fintype.card α) :=
    Real.log_pos (by exact_mod_cast (show 1 < Fintype.card α by omega))
  have hadm := isBundleAdmissible_normalizedEntropy hq H_col H_row D hD hne
  have hb := h H_col H_row hcol hrow hsym D (Fin n × Fin m → Option α) (bundleVar D)
    (Real.log (Fintype.card α)) hL (isRecoverable_bundleVar hD) (by
      intro K u hu
      have hc := hadm.cap K u hu
      rw [unifEntropy_bundleVar D hne, unifEntropy_bundleVar D hne]
      rw [← sub_div, div_le_iff₀ hL] at hc
      exact hc)
  rw [unifEntropy_bundleVar D hne, cellsOf_univ,
    MotionDepthCodes.codeEntropy_univ_uniform D hne] at hb
  have hc0 : (0 : ℝ) < D.card := by exact_mod_cast hne.card_pos
  have hα0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [Real.rpow_def_of_pos hα0, ← Real.exp_log hc0]
  exact Real.exp_le_exp.mpr (by linarith)

end Bridge

/-! ## The implications -/

/-- **The bundle hypothesis implies the random-variable hypothesis.** -/
theorem randomVariableCommonDeficit_of_bundle (h : BundleCommonDeficit) :
    RandomVariableCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  exact ⟨n₀, fun n hn => randomVariableBoundAt_of_bundleBoundAt (hn₀ n hn)⟩

/-- **The random-variable hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_randomVariable (h : RandomVariableCommonDeficit) :
    BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨n₀, fun d hd => ?_⟩
  refine (bipartiteBoundAt_of_randomVariableBoundAt (hn₀ d hd)).mono_v ?_
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  nlinarith

theorem commonDeficit_of_randomVariable (h : RandomVariableCommonDeficit) :
    LeanBacklog.Wall.CommonDeficit :=
  bipartiteCommonDeficit_iff_commonDeficit.mp (bipartiteCommonDeficit_of_randomVariable h)

/-- **The random-variable hypothesis implies the conjecture.** -/
theorem conjecture_of_randomVariableCommonDeficit (h : RandomVariableCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_randomVariable h)

/-! ## The window-wise form -/

/-- One window per resource triple, cofinally many dimensions, in random-variable form. -/
def WindowwiseRandomVariableCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        RandomVariableBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

theorem windowwiseBipartite_of_windowwiseRandomVariable
    (h : WindowwiseRandomVariableCriterion) : WindowwiseBipartiteCriterion := by
  intro k G c hk hG hc
  obtain ⟨R, θ, δ, hθ, hT, hcof⟩ := h k G c hk hG hc
  refine ⟨R, θ, δ, hθ, hT, fun d₀ => ?_⟩
  obtain ⟨d, hd, hb⟩ := hcof d₀
  exact ⟨d, hd, bipartiteBoundAt_of_randomVariableBoundAt hb⟩

theorem conjecture_of_windowwiseRandomVariableCriterion
    (h : WindowwiseRandomVariableCriterion) : LeanBacklog.Wall.Conjecture :=
  conjecture_of_windowwiseBipartiteCriterion (windowwiseBipartite_of_windowwiseRandomVariable h)

#print axioms isBundleAdmissible_unifEntropy
#print axioms randomVariableBoundAt_of_bundleBoundAt
#print axioms isRecoverable_bundleVar
#print axioms unifEntropy_bundleVar
#print axioms bipartiteBoundAt_of_randomVariableBoundAt
#print axioms randomVariableCommonDeficit_of_bundle
#print axioms bipartiteCommonDeficit_of_randomVariable
#print axioms commonDeficit_of_randomVariable
#print axioms conjecture_of_randomVariableCommonDeficit
#print axioms windowwiseBipartite_of_windowwiseRandomVariable
#print axioms conjecture_of_windowwiseRandomVariableCriterion

end LeanBacklog.WallRandomVariables

import NativeRelations.CrossingBridge

/-!
# Disjoint Expanding Wave Counting

Proves that `m` pairwise disjoint sets of steps into each of which a set of `α L` outputs has
vertex-cut expansion at least `c` consume at least `m c α L` steps
(`disjointWave_mengerExpansion_counting_le`), bounding the number of expanding waves in any
oblivious linear-time run by `2 C / (c α)` (`obliviousLinTime_expandingWaves_le`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

/-! ## §1. Menger Vertex-Cut Subadditivity & Target-Cardinality Lower Bound -/

section MengerCutAlgebra

/-- The terminal vertex `(t₀ :: π).getLastD d` of any non-empty list `t₀ :: π` belongs to `t₀ :: π`. -/
theorem getLastD_cons_mem {α : Type*} : ∀ (π : List α) (t₀ d : α),
    (t₀ :: π).getLastD d ∈ t₀ :: π
  | [], _, _ => List.mem_cons_self
  | t₁ :: rest, t₀, _ => List.mem_cons_of_mem t₀ (getLastD_cons_mem rest t₁ t₀)

/-- Every target set `Dst` is trivially a Menger vertex cut from `Src` to `Dst`
(witnessed at the path endpoint `(t₀ :: π).getLastD t₀ ∈ Dst`). -/
theorem isMengerVertexCut_dst_self {k T : ℕ} (xs : Fin k → ℕ → ℤ) (Src Dst : Finset ℕ) :
    IsMengerVertexCut xs T Src Dst Dst :=
  fun π t₀ _ _ hlast => ⟨(t₀ :: π).getLastD t₀, getLastD_cons_mem π t₀ t₀, hlast⟩

/-- **Finite-Union Menger Vertex-Cut Subadditivity:** if `B r` cuts `Src → Dst r` for every `r ∈ S`,
then `S.biUnion B` cuts `Src → S.biUnion Dst` (`with cardinality ≤ ∑ r ∈ S, (B r).card`). -/
theorem isMengerVertexCut_biUnion {ι : Type*} [DecidableEq ι] {k T : ℕ} {xs : Fin k → ℕ → ℤ}
    (S : Finset ι) (Src : Finset ℕ) (Dst B : ι → Finset ℕ)
    (h : ∀ r ∈ S, IsMengerVertexCut xs T Src (Dst r) (B r)) :
    IsMengerVertexCut xs T Src (S.biUnion Dst) (S.biUnion B) := by
  intro π t₀ hsrc hdep hlast
  obtain ⟨r, hrS, hd_r⟩ := mem_biUnion.mp hlast
  obtain ⟨v, hv_mem, hv_Br⟩ := h r hrS π t₀ hsrc hdep hd_r
  exact ⟨v, hv_mem, mem_biUnion.mpr ⟨r, hrS, hv_Br⟩⟩

/-- Every Menger expansion lower bound `∀ B, IsMengerVertexCut xs T Src Dst B → lb ≤ B.card`
immediately implies `lb ≤ Dst.card`. -/
theorem card_dst_ge_of_mengerExpansion {k T : ℕ} {xs : Fin k → ℕ → ℤ} {Src Dst : Finset ℕ}
    {lb : ℝ} (hexp : ∀ B : Finset ℕ, IsMengerVertexCut xs T Src Dst B → lb ≤ (B.card : ℝ)) :
    lb ≤ (Dst.card : ℝ) :=
  hexp Dst (isMengerVertexCut_dst_self xs Src Dst)

end MengerCutAlgebra

/-! ## §2. Per-Band Crossing-Lower Sets & Lower-Endpoint Hop Uniqueness -/

section BandCrossingLowers

open scoped Classical

/-- Every revisit hop `IsHop (τ₀.work j) T p u` on a unit-speed walk has excursion `≤ T`. -/
theorem hop_excursion_le_T {k : ℕ} (τ₀ : Trace k) {T : ℕ} (j : Fin k) {p u : ℕ}
    (hhop : IsHop (τ₀.work j) T p u) :
    ∀ t ∈ Ioo p u, |τ₀.work j t - τ₀.work j p| ≤ (T : ℤ) := by
  intro t ht
  obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
  have huT : u < T := hhop.2.1
  have hlip := (τ₀.work_isWalk j).lip (le_of_lt hpt)
  have habs : |τ₀.work j t - τ₀.work j p| ≤ ((t - p : ℕ) : ℤ) :=
    abs_le.mpr ⟨by linarith [hlip.2], hlip.1⟩
  exact habs.trans (Nat.cast_le.mpr (by omega))

end BandCrossingLowers

/-! ## §3. The Disjoint-Band & Disjoint-Wave Counting Lemmas and Scale-Profile Sandwich (Remark 8.3) -/

section DisjointBandCountingLemma

open scoped Classical

/-- **Remark 8.3 (`Padding-Invariant Disjoint Crossing-Wave Counting Lemma`):**
For any `S`-indexed family `M_wave : ι → Finset ℕ` of **pairwise-disjoint** step sets inside `range T`
(in particular, pairwise-disjoint subsets of `crossingLowerEtaSteps τ₀ T W 1 T`), Menger expansion
`≥ c * |V₀|` (`|V₀| ≥ α * L`) into each `M_wave r` forces `S.card * (c * α * L) ≤ T` (with multiplicity
`1` per step rather than `k`). -/
theorem disjointWave_mengerExpansion_counting_le {ι : Type*} [DecidableEq ι] {k T d b : ℕ}
    {c α : ℝ} (τ₀ : Trace k) (hc : 0 ≤ c) (_hα : 0 ≤ α)
    (S : Finset ι) (M_wave : ι → Finset ℕ)
    (hsub : ∀ r ∈ S, M_wave r ⊆ range T)
    (hdisj : (S : Set ι).PairwiseDisjoint M_wave)
    (Src : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hexp : ∀ r ∈ S, ∀ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (M_wave r) B → c * (V₀.card : ℝ) ≤ (B.card : ℝ)) :
    (S.card : ℝ) * (c * α * ((d * d * b : ℕ) : ℝ)) ≤ (T : ℝ) := by
  have hwave_lb : ∀ r ∈ S, c * α * ((d * d * b : ℕ) : ℝ) ≤ ((M_wave r).card : ℝ) := by
    intro r hr
    calc c * α * ((d * d * b : ℕ) : ℝ)
        = c * (α * ((d * d * b : ℕ) : ℝ)) := by ring
      _ ≤ c * (V₀.card : ℝ) := mul_le_mul_of_nonneg_left hV₀ hc
      _ ≤ ((M_wave r).card : ℝ) := card_dst_ge_of_mengerExpansion (hexp r hr)
  have hbi_sub : S.biUnion M_wave ⊆ range T := by
    intro v hv
    obtain ⟨r, hrS, hvr⟩ := mem_biUnion.mp hv
    exact hsub r hrS hvr
  have hsum_nat : ∑ r ∈ S, (M_wave r).card ≤ T := by
    rw [← card_biUnion hdisj]
    simpa [card_range] using card_le_card hbi_sub
  have hsum_real : ∑ r ∈ S, ((M_wave r).card : ℝ) ≤ (T : ℝ) := by
    have hcast : (∑ r ∈ S, (M_wave r).card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsum_nat
    simpa [Nat.cast_sum] using hcast
  calc (S.card : ℝ) * (c * α * ((d * d * b : ℕ) : ℝ))
      = ∑ _r ∈ S, (c * α * ((d * d * b : ℕ) : ℝ)) := by simp
    _ ≤ ∑ r ∈ S, ((M_wave r).card : ℝ) := sum_le_sum hwave_lb
    _ ≤ (T : ℝ) := hsum_real

/-- `O(C / (c * α))` cap on pairwise-disjoint expanding crossing waves for `ObliviousLinTime`. -/
theorem obliviousLinTime_expandingWaves_le {ι : Type*} [DecidableEq ι] {M : TM} {d b T : ℕ}
    {C c α : ℝ} (hd : 1 ≤ d) (hb : 1 ≤ b) (hc : 0 < c) (hα : 0 < α)
    (hobl_lt : ObliviousLinTime M d b C T)
    (S : Finset ι) (M_wave : ι → Finset ℕ)
    (hsub : ∀ r ∈ S, M_wave r ⊆ range T)
    (hdisj : (S : Set ι).PairwiseDisjoint M_wave)
    (Src : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hexp : ∀ r ∈ S, ∀ B : Finset ℕ,
      IsMengerVertexCut (traceAt M (d * d * b)).work T Src (M_wave r) B →
      c * (V₀.card : ℝ) ≤ (B.card : ℝ)) :
    (S.card : ℝ) ≤ 2 * C / (c * α) := by
  have hL1 : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hL_pos : (0 : ℝ) < ((d * d * b : ℕ) : ℝ) := by exact_mod_cast hL1
  have hL_one : (((d * d * b : ℕ) : ℝ) + 1) ≤ 2 * ((d * d * b : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((d * d * b : ℕ) : ℝ) := by exact_mod_cast hL1
    linarith
  have hcnt := disjointWave_mengerExpansion_counting_le (traceAt M (d * d * b)) hc.le hα.le
    S M_wave hsub hdisj Src V₀ hV₀ hexp
  have hC_nn : 0 ≤ C := by
    have hT := hobl_lt.2.1
    have hT_nn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have hden_pos : (0 : ℝ) < ((d * d * b : ℕ) : ℝ) + 1 := by positivity
    nlinarith
  have hT_le : (T : ℝ) ≤ 2 * C * ((d * d * b : ℕ) : ℝ) := by
    have hT := hobl_lt.2.1
    nlinarith
  rw [le_div_iff₀ (mul_pos hc hα)]
  have hmul : ((S.card : ℝ) * (c * α)) * ((d * d * b : ℕ) : ℝ) ≤
      (2 * C) * ((d * d * b : ℕ) : ℝ) := by linarith
  exact le_of_mul_le_mul_right hmul hL_pos

end DisjointBandCountingLemma

end NativeRelations

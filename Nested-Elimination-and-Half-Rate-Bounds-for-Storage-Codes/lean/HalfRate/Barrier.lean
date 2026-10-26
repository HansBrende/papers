import HalfRate.N3

/-!
# The barrier bound

For a triangle-free graph of maximum degree three, let `S` be any vertex set and `I(S)` the
vertices outside `S` all of whose neighbours lie in `S` (the isolated vertices of `G − S`). Then
every valid polymatroid satisfies `h(V) ≤ Σ_{v∈S} h(v) + ½ Σ_{v ∉ S ∪ I(S)} h(v)`, and every
storage code satisfies `2 log|C| ≤ (|V| + |S| − |I(S)|) log|α|`. The proof is the relative
decomposition theorem from the context `S ∪ I(S)`, which `S` closes.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices outside `S` all of whose neighbours lie in `S`: the isolated vertices of
`G − S`. -/
def isolatedOut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ S ∧ nbhd G v ⊆ S)

theorem disjoint_isolatedOut (S : Finset V) : Disjoint S (isolatedOut G S) := by
  rw [Finset.disjoint_left]; intro v hv hv'
  exact (mem_filter.mp hv').2.1 hv

theorem card_sdiff_isolatedOut (S : Finset V) :
    ((univ \ (S ∪ isolatedOut G S)).card : ℝ) =
      Fintype.card V - S.card - (isolatedOut G S).card := by
  rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint (disjoint_isolatedOut S),
    card_univ]
  have : S.card + (isolatedOut G S).card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint (disjoint_isolatedOut S), ← card_univ]
    exact card_le_card (subset_univ _)
  push_cast [Nat.cast_sub this]
  ring

/-- **The barrier inequality.** -/
theorem barrier_ineq (hcf : G.CliqueFree 3) (hdeg : ∀ v, (nbhd G v).card ≤ 3)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (hv : IsValid h (nbhd G)) (S : Finset V) :
    2 * h univ ≤ 2 * ∑ v ∈ S, h {v} + ∑ v ∈ univ \ (S ∪ isolatedOut G S), h {v} := by
  set U := S ∪ isolatedOut G S with hU
  obtain ⟨pcs, hD⟩ := n3_decomp hcf hdeg (univ \ U)
  rw [sdiff_sdiff_right_self, inf_eq_inter, univ_inter] at hD
  have h1 := decomp_ineq hh hv pcs U hD
  have h2 : ∑ v ∈ univ \ U, (h (insert v U) - h U) ≤ ∑ v ∈ univ \ U, h {v} := by
    refine sum_le_sum fun v _ => ?_
    have := hh.union_le {v} U
    rw [singleton_union] at this
    linarith
  have h3 : h U = h S := by
    refine hh.eq_of_closure hv subset_union_left ?_
    intro v hvU hvS
    rcases mem_union.mp hvU with h' | h'
    · exact absurd h' hvS
    · exact (mem_filter.mp h').2.2
  have h4 := hh.le_sum_singleton S
  linarith

/-- **The barrier bound for codes.** Every storage code on a triangle-free graph of maximum
degree three satisfies `2 log|C| ≤ (|V| + |S| − |I(S)|) log|α|` for every vertex set `S`. -/
theorem log_card_le_barrier {α : Type*} [Fintype α] [Nonempty α] (hcf : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) {C : Finset (V → α)} (hC : IsStorageCode (nbhd G) C)
    (S : Finset V) :
    2 * Real.log C.card ≤
      ((Fintype.card V : ℝ) + S.card - (isolatedOut G S).card) * Real.log (Fintype.card α) := by
  have hdeg' : ∀ v, (nbhd G v).card ≤ 3 := fun v => by
    have h := hdeg v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter] at h
    exact h
  have hα : 0 ≤ Real.log (Fintype.card α) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hw : 0 ≤ (Fintype.card V : ℝ) + S.card - (isolatedOut G S).card := by
    have := card_sdiff_isolatedOut (G := G) S
    have : (0 : ℝ) ≤ ((univ \ (S ∪ isolatedOut G S)).card : ℝ) := Nat.cast_nonneg _
    linarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  rcases C.eq_empty_or_nonempty with hCe | hne
  · rw [hCe, card_empty, Nat.cast_zero, Real.log_zero, mul_zero]
    positivity
  · have hc0 : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hp : ∀ ω : C, (0 : ℝ) ≤ (fun _ : C => ((C.card : ℝ))⁻¹) ω :=
      fun _ => inv_nonneg.mpr hc0.le
    have hp1 : ∑ ω : C, (fun _ : C => ((C.card : ℝ))⁻¹) ω = 1 := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      field_simp
    have hX : IsRecoverable (nbhd G) (fun x : C => (x : V → α)) :=
      fun v ω ω' h => hC ω.1 ω.2 ω'.1 ω'.2 v h
    set H := codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x : C => (x : V → α)) with hHdef
    have hH := codeEntropy_isPolymatroid (fun _ : C => ((C.card : ℝ))⁻¹)
      (fun x : C => (x : V → α)) hp hp1
    have hHv := codeEntropy_isValid (fun _ : C => ((C.card : ℝ))⁻¹)
      (fun x : C => (x : V → α)) hp hX
    have hb := barrier_ineq hcf hdeg' hH hHv S
    rw [codeEntropy_univ_uniform C hne, ← hHdef] at hb
    have hsing : ∀ v, H {v} ≤ Real.log (Fintype.card α) := fun v =>
      codeEntropy_singleton_le (fun _ : C => ((C.card : ℝ))⁻¹) (fun x : C => (x : V → α)) hp hp1 v
    have hS : ∑ v ∈ S, H {v} ≤ S.card * Real.log (Fintype.card α) := by
      calc ∑ v ∈ S, H {v} ≤ ∑ _v ∈ S, Real.log (Fintype.card α) := sum_le_sum fun v _ => hsing v
        _ = S.card * Real.log (Fintype.card α) := by rw [sum_const, nsmul_eq_mul]
    have hR : ∑ v ∈ univ \ (S ∪ isolatedOut G S), H {v} ≤
        (univ \ (S ∪ isolatedOut G S)).card * Real.log (Fintype.card α) := by
      calc ∑ v ∈ univ \ (S ∪ isolatedOut G S), H {v}
          ≤ ∑ _v ∈ univ \ (S ∪ isolatedOut G S), Real.log (Fintype.card α) :=
            sum_le_sum fun v _ => hsing v
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    rw [card_sdiff_isolatedOut] at hR
    nlinarith

end HalfRate

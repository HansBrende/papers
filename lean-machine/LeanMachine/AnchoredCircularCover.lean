import LeanMachine.WeightedCircularGap

set_option autoImplicit false

/-!
# Anchored covers on a finite circle

Closed arcs consist of their vertices; their length is paid on outgoing
elementary edges. Two uncovered edges in an old gap cannot be separated by
a new covered vertex, because each covering arc also contains an old anchor.
-/

namespace LeanMachine.AnchoredCircularCover

open Finset CyclicSelection WeightedCircularGap
noncomputable section

variable {κ : Type*}

def coveredEdges (N : ℕ) (I : Finset κ) (start len : κ → ℕ) : Finset ℕ :=
  I.biUnion fun i => arc N (start i) (len i)

def coveredVertices (N : ℕ) (I : Finset κ) (start len : κ → ℕ) : Finset ℕ :=
  I.biUnion fun i => arc N (start i) (len i + 1)

theorem coveredEdges_subset {N : ℕ} (hN : 0 < N) (I : Finset κ) (start len : κ → ℕ) :
    coveredEdges N I start len ⊆ range N := by
  intro e he
  obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
  exact arc_subset hN hei

theorem mem_arc_iff_forward_lt {N a ell z : ℕ}
    (ha : a < N) (hz : z < N) (hell : ell ≤ N) :
    z ∈ arc N a ell ↔ forward N a z < ell := by
  constructor
  · intro hzarc
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hzarc
    have hk' := mem_range.mp hk
    rw [forward_mod_add ha (by omega)]
    exact hk'
  · intro hf
    exact mem_image.mpr ⟨forward N a z, mem_range.mpr hf, mod_add_forward ha hz⟩

theorem mem_closedArc_iff_forward_le {N a ell z : ℕ}
    (ha : a < N) (hz : z < N) (hell : ell ≤ N) :
    z ∈ arc N a (ell + 1) ↔ forward N a z ≤ ell := by
  constructor
  · intro hzarc
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hzarc
    have hk' := mem_range.mp hk
    by_cases hkN : k < N
    · rw [forward_mod_add ha hkN]
      omega
    · have hkN : k = N := by omega
      simp only [hkN, Nat.add_mod_right, Nat.mod_eq_of_lt ha, forward,
        le_refl, ↓reduceIte, Nat.sub_self]
      omega
  · intro hf
    exact mem_image.mpr ⟨forward N a z, mem_range.mpr (by omega), mod_add_forward ha hz⟩

/-- An arc joining a vertex between two edges to a vertex outside them
must cross one of those edges. All positions use the same unrolled cut. -/
theorem arc_crosses_boundary {N c a b z q ell : ℕ}
    (hc : c < N) (hb : b < N) (hq : q < N)
    (haz : a < z) (hzb : z ≤ b) (hqout : q ≤ a ∨ b < q)
    (hzarc : forward N c z ≤ ell) (hqarc : forward N c q ≤ ell) :
    forward N c a < ell ∨ forward N c b < ell := by
  unfold forward at *
  split_ifs at * <;> omega

/-- Express all clockwise coordinates relative to an arbitrary cut. -/
theorem forward_relative {N p a z : ℕ} (hp : p < N) (ha : a < N) (hz : z < N) :
    forward N a z = forward N (forward N p a) (forward N p z) := by
  have h := forward_rotate (L := N) p (forward_lt hp ha) (forward_lt hp hz)
  simpa only [mod_add_forward hp ha, mod_add_forward hp hz] using h

theorem forward_between_iff {N p a b z : ℕ} (hp : p < N) (hb : b < N)
    (hz : z < N) (hab : a ≤ b) :
    (0 < forward N ((p + a) % N) z ∧
      forward N ((p + a) % N) z ≤ forward N ((p + a) % N) ((p + b) % N)) ↔
      a < forward N p z ∧ forward N p z ≤ b := by
  have ha : a < N := by omega
  have hq := forward_lt hp hz
  have hz' := mod_add_forward hp hz
  have hrot := forward_rotate (L := N) p ha hq
  rw [hz'] at hrot
  rw [hrot, forward_rotate p ha hb]
  unfold forward
  split_ifs <;> omega

/-- Inside one old gap, no target vertex can lie strictly after the first
uncovered edge and at or before the second. Singleton and full-circle arcs
are both included. -/
theorem no_target_between {N : ℕ} {S₀ S : Finset ℕ} (hS₀ : S₀.Nonempty)
    (hS₀N : S₀ ⊆ range N) (hSN : S ⊆ range N)
    (I : Finset κ) (start len : κ → ℕ)
    (hstart : ∀ i ∈ I, start i < N) (hlen : ∀ i ∈ I, len i ≤ N)
    (hanchor : ∀ i ∈ I, ∃ q ∈ S₀, q ∈ arc N (start i) (len i + 1))
    (hcover : S ⊆ S₀ ∪ coveredVertices N I start len)
    {i a b : ℕ} (hi : i < S₀.card) (hbg : b < gap N S₀ hS₀ i)
    (haU : (point N S₀ hS₀ i + a) % N ∉ coveredEdges N I start len)
    (hbU : (point N S₀ hS₀ i + b) % N ∉ coveredEdges N I start len) :
    ∀ z ∈ S, ¬(a < forward N (point N S₀ hS₀ i) z ∧
      forward N (point N S₀ hS₀ i) z ≤ b) := by
  intro z hz hbetween
  let p := point N S₀ hS₀ i
  have hp : p < N := mem_range.mp (hS₀N (point_mem hS₀ hi))
  have hgN := gap_le hS₀ hS₀N hi
  have haN : a < N := by omega
  have hbN : b < N := by omega
  have hzN : z < N := mem_range.mp (hSN hz)
  rcases mem_union.mp (hcover hz) with hz₀ | hzU
  · have ho := anchor_offset_zero_or_gap_le hS₀ hS₀N hi hz₀
    omega
  · obtain ⟨c, hc, hzc⟩ := mem_biUnion.mp hzU
    obtain ⟨q, hq, hqc⟩ := hanchor c hc
    have hqN := mem_range.mp (hS₀N hq)
    have hcN := hstart c hc
    have hc' := forward_lt hp hcN
    have hq' := forward_lt hp hqN
    have ho := anchor_offset_zero_or_gap_le hS₀ hS₀N hi hq
    change forward N p q = 0 ∨ gap N S₀ hS₀ i ≤ forward N p q at ho
    have hzc' := (mem_closedArc_iff_forward_le hcN hzN (hlen c hc)).mp hzc
    have hqc' := (mem_closedArc_iff_forward_le hcN hqN (hlen c hc)).mp hqc
    rw [forward_relative hp hcN hzN] at hzc'
    rw [forward_relative hp hcN hqN] at hqc'
    have hcross := arc_crosses_boundary hc' hbN hq' hbetween.1 hbetween.2
      (show forward N p q ≤ a ∨ b < forward N p q by omega) hzc' hqc'
    have hpointN (v : ℕ) : (p + v) % N < N := Nat.mod_lt _ (by omega)
    rcases hcross with ha | hb
    · apply haU
      apply mem_biUnion.mpr
      refine ⟨c, hc, (mem_arc_iff_forward_lt hcN (hpointN a) (hlen c hc)).mpr ?_⟩
      rw [forward_relative hp hcN (hpointN a), forward_mod_add hp haN]
      exact ha
    · apply hbU
      apply mem_biUnion.mpr
      refine ⟨c, hc, (mem_arc_iff_forward_lt hcN (hpointN b) (hlen c hc)).mpr ?_⟩
      rw [forward_relative hp hcN (hpointN b), forward_mod_add hp hbN]
      exact hb

/-- Outside the union of the paid arcs, sharing an old gap implies sharing
a new gap. Old anchors need not belong to the new target. -/
theorem uncovered_pair_labels {N : ℕ} {S₀ S : Finset ℕ}
    (hS₀ : S₀.Nonempty) (hS₀N : S₀ ⊆ range N)
    (hS : S.Nonempty) (hSN : S ⊆ range N)
    (I : Finset κ) (start len : κ → ℕ)
    (hstart : ∀ i ∈ I, start i < N) (hlen : ∀ i ∈ I, len i ≤ N)
    (hanchor : ∀ i ∈ I, ∃ q ∈ S₀, q ∈ arc N (start i) (len i + 1))
    (hcover : S ⊆ S₀ ∪ coveredVertices N I start len) :
    ∀ e ∈ range N \ coveredEdges N I start len,
      ∀ f ∈ range N \ coveredEdges N I start len,
        edgeLabel N S₀ hS₀ e = edgeLabel N S₀ hS₀ f →
          edgeLabel N S hS e = edgeLabel N S hS f := by
  intro e he f hf hlabels
  obtain ⟨heN, heU⟩ := mem_sdiff.mp he
  obtain ⟨hfN, hfU⟩ := mem_sdiff.mp hf
  have heN := mem_range.mp heN
  have hfN := mem_range.mp hfN
  let i := edgeLabel N S₀ hS₀ e
  obtain ⟨hi, hei⟩ := edgeLabel_spec hS₀ hS₀N heN
  change i < S₀.card at hi
  change e ∈ edges N S₀ hS₀ i at hei
  have hfi : f ∈ edges N S₀ hS₀ i :=
    (mem_edges_iff_label hS₀ hS₀N hi).mpr ⟨hfN, hlabels.symm⟩
  obtain ⟨a, ha, hae⟩ := mem_image.mp hei
  obtain ⟨b, hb, hbf⟩ := mem_image.mp hfi
  have ha := mem_range.mp ha
  have hb := mem_range.mp hb
  have hp : point N S₀ hS₀ i < N := mem_range.mp (hS₀N (point_mem hS₀ hi))
  have hgN := gap_le hS₀ hS₀N hi
  have hN : 0 < N := by omega
  have hordered {a b : ℕ} (hab : a ≤ b) (hbg : b < gap N S₀ hS₀ i)
      (haU : (point N S₀ hS₀ i + a) % N ∉ coveredEdges N I start len)
      (hbU : (point N S₀ hS₀ i + b) % N ∉ coveredEdges N I start len) :
      edgeLabel N S hS ((point N S₀ hS₀ i + a) % N) =
        edgeLabel N S hS ((point N S₀ hS₀ i + b) % N) := by
    apply edgeLabel_eq_of_no_target_between hS hSN (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
    intro z hz hbetween
    exact no_target_between hS₀ hS₀N hSN I start len hstart hlen hanchor hcover hi hbg haU hbU z hz
      ((forward_between_iff hp (by omega) (mem_range.mp (hSN hz)) hab).mp hbetween)
  have haU : (point N S₀ hS₀ i + a) % N ∉ coveredEdges N I start len := by
    simpa only [hae] using heU
  have hbU : (point N S₀ hS₀ i + b) % N ∉ coveredEdges N I start len := by
    simpa only [hbf] using hfU
  rw [← hae, ← hbf]
  rcases le_total a b with hab | hba
  · exact hordered hab hb haU hbU
  · exact (hordered hba ha hbU haU).symm

end
end LeanMachine.AnchoredCircularCover

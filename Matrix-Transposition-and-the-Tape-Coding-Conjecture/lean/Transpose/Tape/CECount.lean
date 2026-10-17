import Transpose.Tape.CENet

/-!
# Counting in the block network of a valid diagram

TM-free facts about the block network of a valid `k`-tape diagram (block size `1 ≤ r`):
* `reachable`: the spine connects all nodes.
* `card_nbrs_le`, `card_ball_le`: every node has at most `2k + 2` neighbours, so a ball of radius
  `j` has at most `(2k+3)^j` nodes.
* `card_rowsAt_le`: for `r ≤ n w`, at most `2` rows are attached at a node.
* `outNode_spec` and `card_sink_row_le`: the outputs produced at a node form an interval of length
  `≤ r`, so for `r ≤ n w` at most `2w` bits of one row have their transposed position there;
  `outNode_eq`: the sink of `o` is the slot during which `o` is appended.
* `rowDist_sum_ge`: all but `4 N (2k+3)^j w + u n w` input bits are at distance `≥ j` from their
  sinks.
* `sum_chordTapes_le`, `card_chordEdges_le` and `sum_cap_le`: capacities within the block profile sum
  to at most `4k N r G`.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

section Count

variable {k : ℕ} {D : TSDiagram k} {L r : ℕ}

/-! ### The spine -/

theorem mem_edges_succ {y : ℕ} (hy : y + 1 < D.nodes r) : (y, y + 1) ∈ D.edges r :=
  Finset.mem_union_left _ ((mem_memEdges D).2 ⟨rfl, hy⟩)

theorem spine_up (a : ℕ) : ∀ m, a + m < D.nodes r → a + m ∈ ball (D.edges r) (D.nodes r) a m
  | 0, _ => by simp [ball_zero]
  | m + 1, h => by
    have ih := spine_up a m (by omega)
    have he : (a + m, a + m + 1) ∈ D.edges r := mem_edges_succ (by omega)
    exact mem_ball_succ ih h (Or.inl he)

theorem spine_down {a : ℕ} (ha : a < D.nodes r) :
    ∀ m, m ≤ a → a - m ∈ ball (D.edges r) (D.nodes r) a m
  | 0, _ => by simp [ball_zero]
  | m + 1, h => by
    have ih := spine_down ha m (by omega)
    have he : (a - (m + 1), a - m) ∈ D.edges r := by
      have e : a - m = a - (m + 1) + 1 := by omega
      rw [e]; exact mem_edges_succ (by omega)
    exact mem_ball_succ ih (by omega) (Or.inr he)

/-- The spine connects all nodes. -/
theorem reachable {a s : ℕ} (ha : a < D.nodes r) (hs : s < D.nodes r) :
    ∃ j, s ∈ ball (D.edges r) (D.nodes r) a j := by
  rcases le_or_gt a s with h | h
  · refine ⟨s - a, ?_⟩
    have := spine_up (D := D) (r := r) a (s - a) (by omega)
    rwa [Nat.add_sub_cancel' h] at this
  · refine ⟨a - s, ?_⟩
    have := spine_down (D := D) ha (a - s) (by omega)
    rwa [Nat.sub_sub_self h.le] at this

/-! ### Degrees and balls -/

open Classical in
/-- **Degree bound.** Every node has at most `2k + 2` neighbours: two along the spine, and for each
tape at most one chord out and one chord in. -/
theorem card_nbrs_le (hD : D.Valid L) (hr : 1 ≤ r) (u : ℕ) :
    ((Finset.range (D.nodes r)).filter
      (fun v => (u, v) ∈ D.edges r ∨ (v, u) ∈ D.edges r)).card ≤ 2 * k + 2 := by
  set N := D.nodes r
  set R : Fin k → ℕ → Finset ℤ := fun t => pairRes r (D.work t) D.T with hR
  have hh : ∀ t, UnitSteps (D.work t) := fun t => (hD.1 t).2
  set Out := (Finset.univ : Finset (Fin k)).biUnion
    (fun t => (Finset.range N).filter (fun v => ∃ β, IsChord (R t) β u v))
  set In := (Finset.univ : Finset (Fin k)).biUnion
    (fun t => (Finset.range N).filter (fun v => ∃ β, IsChord (R t) β v u))
  have hsub : (Finset.range N).filter (fun v => (u, v) ∈ D.edges r ∨ (v, u) ∈ D.edges r) ⊆
      ({u - 1, u + 1} ∪ Out) ∪ In := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_range] at hv
    obtain ⟨hvN, hadj⟩ := hv
    rcases hadj with he | he <;> rcases Finset.mem_union.1 he with hm | hc
    · rw [mem_memEdges] at hm
      simp only at hm
      simp [hm.1]
    · rw [mem_chordEdges] at hc
      obtain ⟨-, -, t, β, hch⟩ := hc
      apply Finset.mem_union_left; apply Finset.mem_union_right
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hvN, β, hch⟩⟩
    · rw [mem_memEdges] at hm
      simp only at hm
      have : v = u - 1 := by omega
      simp [this]
    · rw [mem_chordEdges] at hc
      obtain ⟨-, -, t, β, hch⟩ := hc
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hvN, β, hch⟩⟩
  have hOut : Out.card ≤ k := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ t : Fin k, ((Finset.range N).filter (fun v => ∃ β, IsChord (R t) β u v)).card
        ≤ ∑ _t : Fin k, 1 := by
          apply Finset.sum_le_sum
          intro t _
          rw [Finset.card_le_one]
          intro v hv v' hv'
          obtain ⟨β, hβ⟩ := (Finset.mem_filter.1 hv).2
          obtain ⟨β', hβ'⟩ := (Finset.mem_filter.1 hv').2
          exact (pairRes_chord_source_unique (hh t) hr D.T hβ hβ').2
      _ = k := by simp
  have hIn : In.card ≤ k := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ t : Fin k, ((Finset.range N).filter (fun v => ∃ β, IsChord (R t) β v u)).card
        ≤ ∑ _t : Fin k, 1 := by
          apply Finset.sum_le_sum
          intro t _
          rw [Finset.card_le_one]
          intro v hv v' hv'
          obtain ⟨β, hβ⟩ := (Finset.mem_filter.1 hv).2
          obtain ⟨β', hβ'⟩ := (Finset.mem_filter.1 hv').2
          exact (pairRes_chord_target_unique (hh t) hr D.T hβ hβ').2
      _ = k := by simp
  have h2 : ({u - 1, u + 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  calc _ ≤ (({u - 1, u + 1} ∪ Out) ∪ In).card := Finset.card_le_card hsub
    _ ≤ ({u - 1, u + 1} ∪ Out).card + In.card := Finset.card_union_le _ _
    _ ≤ ({u - 1, u + 1} : Finset ℕ).card + Out.card + In.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2 * k + 2 := by omega

open Classical in
/-- A ball of radius `j` has at most `(2k+3)^j` nodes. -/
theorem card_ball_le (hD : D.Valid L) (hr : 1 ≤ r) (a : ℕ) :
    ∀ j, (ball (D.edges r) (D.nodes r) a j).card ≤ (2 * k + 3) ^ j
  | 0 => by simp [ball_zero]
  | j + 1 => by
    rw [ball_succ]
    set B := ball (D.edges r) (D.nodes r) a j
    have hsub : (Finset.range (D.nodes r)).filter
        (fun v => ∃ u ∈ B, (u, v) ∈ D.edges r ∨ (v, u) ∈ D.edges r) ⊆
        B.biUnion (fun u => (Finset.range (D.nodes r)).filter
          (fun v => (u, v) ∈ D.edges r ∨ (v, u) ∈ D.edges r)) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨hvN, u, hu, hadj⟩ := hv
      exact Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_filter.2 ⟨hvN, hadj⟩⟩
    have ih := card_ball_le hD hr a j
    calc (B ∪ _).card ≤ B.card + _ := Finset.card_union_le _ _
      _ ≤ B.card + ∑ u ∈ B, ((Finset.range (D.nodes r)).filter
            (fun v => (u, v) ∈ D.edges r ∨ (v, u) ∈ D.edges r)).card :=
          Nat.add_le_add_left (le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le) _
      _ ≤ B.card + ∑ _u ∈ B, (2 * k + 2) :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun u _ => card_nbrs_le hD hr u)) _
      _ = B.card * (2 * k + 3) := by rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ (2 * k + 3) ^ j * (2 * k + 3) := Nat.mul_le_mul_right _ ih
      _ = (2 * k + 3) ^ (j + 1) := by ring

/-! ### Rows at a node -/

open Classical in
/-- For `r ≤ n w`, at most `2` rows are attached at a node. -/
theorem card_rowsAt_le (hD : D.Valid L) {n w : ℕ} (hrnw : r ≤ n * w) (y : ℕ) :
    (D.rowsAt n w r y).card ≤ 2 := by
  set S := D.rowsAt n w r y with hS
  have hh : UnitSteps D.inp := hD.2.2.1
  by_cases hne : S.Nonempty
  · set m := S.min' hne
    have hsub : S ⊆ {m, m + 1} := by
      intro i hi
      have hmi : m ≤ i := Finset.min'_le _ _ hi
      have hm : m ∈ S := Finset.min'_mem _ _
      simp only [hS, TSDiagram.rowsAt, Finset.mem_filter] at hi hm
      obtain ⟨-, τ, hτ, hi1, hi2⟩ := hi
      obtain ⟨-, τ', hτ', hm1, hm2⟩ := hm
      rw [mem_slotOf] at hτ hτ'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hc
      push Not at hc
      have hfar : m + 2 ≤ i := by omega
      have hd := slot_dist hh hτ'.1 hτ'.2.1 hτ.1 hτ.2.1
      have hprod : (m + 1) * n * w + n * w ≤ i * n * w := by
        have : (m + 2) * n * w ≤ i * n * w :=
          Nat.mul_le_mul_right w (Nat.mul_le_mul_right n hfar)
        have e : (m + 2) * n * w = (m + 1) * n * w + n * w := by ring
        omega
      have hprodZ : (((m + 1) * n * w : ℕ) : ℤ) + ((n * w : ℕ) : ℤ) ≤ ((i * n * w : ℕ) : ℤ) := by
        exact_mod_cast hprod
      have hrZ : (r : ℤ) ≤ ((n * w : ℕ) : ℤ) := by exact_mod_cast hrnw
      have := le_abs_self (D.inp τ - D.inp τ')
      linarith
    calc S.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-! ### Sinks -/

theorem out_mono (hD : D.Valid L) {τ τ' : ℕ} (h : τ ≤ τ') : D.out τ ≤ D.out τ' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact le_trans ih (by rw [← Nat.add_assoc]; exact (hD.2.2.2.2.1 _).1)

theorem out_add_le (hD : D.Valid L) (τ : ℕ) : ∀ j, D.out (τ + j) ≤ D.out τ + j
  | 0 => le_rfl
  | j + 1 => by
    have := (hD.2.2.2.2.1 (τ + j)).2
    have ih := out_add_le hD τ j
    rw [← Nat.add_assoc]; omega

theorem one_le_T (hD : D.Valid L) (hL : 1 ≤ L) : 1 ≤ D.T := by
  by_contra h
  push Not at h
  have h0 := hD.2.2.2.2.2 0 (by omega)
  rw [hD.2.2.2.1] at h0
  omega

theorem T_le_nodes_mul (hr : 1 ≤ r) : D.T ≤ D.nodes r * r := by
  unfold TSDiagram.nodes numSlots
  have h1 := Nat.div_add_mod (D.T + r - 1) r
  have h2 := Nat.mod_lt (D.T + r - 1) (show 0 < r by omega)
  rw [Nat.mul_comm] at h1
  rcases Nat.eq_zero_or_pos D.T with h | h
  · rw [h]; exact Nat.zero_le _
  · omega

theorem nodes_mul_le (r : ℕ) : D.nodes r * r ≤ D.T + r - 1 := by
  unfold TSDiagram.nodes numSlots
  exact Nat.div_mul_le_self _ _

theorem outNode_lt (hD : D.Valid L) (hr : 1 ≤ r) (hL : 1 ≤ L) (o : ℕ) :
    D.outNode r o < D.nodes r := by
  have hT := one_le_T hD hL
  have hN : 1 ≤ D.nodes r := by
    unfold TSDiagram.nodes
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, numSlots_spec hr]; omega
  have : D.outNode r o ≤ D.nodes r - 1 := Nat.findGreatest_le _
  omega

/-- The outputs produced at node `s` form an interval `[out(s r), out(s r) + r)`. -/
theorem outNode_spec (hD : D.Valid L) (hr : 1 ≤ r) {o : ℕ} (ho : o < L) :
    D.out (D.outNode r o * r) ≤ o ∧ o < D.out (D.outNode r o * r) + r := by
  classical
  have hL : 1 ≤ L := by omega
  set s := D.outNode r o with hs
  have hP : D.out (s * r) ≤ o := by
    rw [hs]
    exact Nat.findGreatest_spec (P := fun y => D.out (y * r) ≤ o) (Nat.zero_le _)
      (by rw [Nat.zero_mul, hD.2.2.2.1]; exact Nat.zero_le _)
  refine ⟨hP, ?_⟩
  have hsN := outNode_lt hD hr hL o
  rcases Nat.lt_or_ge (s + 1) (D.nodes r) with h | h
  · -- `s` is not the last node: the next node's first step comes after bit `o`
    have hnot : ¬ D.out ((s + 1) * r) ≤ o :=
      Nat.findGreatest_is_greatest (P := fun y => D.out (y * r) ≤ o) (Nat.lt_succ_self s)
        (by omega)
    have := out_add_le hD (s * r) r
    rw [show s * r + r = (s + 1) * r by ring] at this
    omega
  · -- the last node: bit `o` is produced before `T ≤ (s+1) r`
    have hsT : s * r < D.T := (numSlots_spec hr).1 hsN
    have hTN := T_le_nodes_mul (D := D) hr
    have hout := hD.2.2.2.2.2 D.T le_rfl
    have hle := out_add_le hD (s * r) (D.T - s * r)
    rw [Nat.add_sub_cancel' hsT.le, hout] at hle
    have : D.T - s * r ≤ r := by
      have : D.nodes r = s + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul] at hTN; omega
    omega

/-- The node producing output position `o` is the slot during which `o` is appended. -/
theorem outNode_eq (hD : D.Valid L) {o y : ℕ} (hy : y < D.nodes r) (h1 : D.out (y * r) ≤ o)
    (h2 : o < D.out ((y + 1) * r)) : D.outNode r o = y := by
  classical
  have hle : y ≤ D.outNode r o :=
    Nat.le_findGreatest (P := fun y => D.out (y * r) ≤ o) (by omega) h1
  by_contra hne
  have hlt : y + 1 ≤ D.outNode r o := by omega
  have hP : D.out (D.outNode r o * r) ≤ o :=
    Nat.findGreatest_spec (P := fun y => D.out (y * r) ≤ o) (show y ≤ D.nodes r - 1 by omega) h1
  have := out_mono hD (Nat.mul_le_mul_right r hlt)
  omega

/-- The transposed position of bit `d` lies in the column block `d / w % n`. -/
theorem tpos_div {n w d : ℕ} (hd : d < n * n * w) : tpos n w d / (n * w) = d / w % n := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  have hw : 0 < w := by omega
  have hn : 0 < n := by omega
  rw [hdec, tpos_spec hj ht]
  have h1 : (d / w % n * n + d / w / n) * w + d % w =
      d / w % n * (n * w) + (d / w / n * w + d % w) := by ring
  have h2 : d / w / n * w + d % w < n * w := by
    calc d / w / n * w + d % w < d / w / n * w + w := by omega
      _ = (d / w / n + 1) * w := by ring
      _ ≤ n * w := Nat.mul_le_mul_right _ hi
  rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h2,
    Nat.zero_add]
  have e3 : ((d / w / n * n + d / w % n) * w + d % w) / w % n = d / w % n := by
    rw [Nat.add_comm _ (d % w), Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ht, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  exact e3.symm

open Classical in
/-- For `r ≤ n w`, at most `2 w` bits of one row have their transposed position produced at a given
node: those positions lie in an interval of length `≤ n w`, which meets at most two columns. -/
theorem card_sink_row_le {n w : ℕ} (hD : D.Valid (n * n * w)) (hr : 1 ≤ r) (hrnw : r ≤ n * w)
    (i s : ℕ) :
    ((Finset.range (n * n * w)).filter (fun d => d / (n * w) = i ∧
      D.outNode r (tpos n w d) = s)).card ≤ 2 * w := by
  set q := D.out (s * r) / (n * w) with hq
  have hsub : (Finset.range (n * n * w)).filter (fun d => d / (n * w) = i ∧
      D.outNode r (tpos n w d) = s) ⊆
      (({q, q + 1} : Finset ℕ) ×ˢ Finset.range w).image (fun p => (i * n + p.1) * w + p.2) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdL, hdi, hds⟩ := hd
    obtain ⟨-, hj, ht, hdec⟩ := pos_decomp hdL
    have hnw : 0 < n * w := by
      rcases Nat.eq_zero_or_pos (n * w) with h | h
      · rw [Nat.mul_assoc, h, Nat.mul_zero] at hdL; omega
      · exact h
    have hi : d / w / n = i := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm w n]; exact hdi
    have ho := tpos_lt hdL
    have hspec := outNode_spec hD hr ho
    rw [hds] at hspec
    have hcol := tpos_div hdL
    have h1 : q ≤ d / w % n := by
      rw [← hcol]; exact Nat.div_le_div_right hspec.1
    have h2 : d / w % n ≤ q + 1 := by
      rw [← hcol]
      calc tpos n w d / (n * w) ≤ (D.out (s * r) + n * w) / (n * w) :=
            Nat.div_le_div_right (by omega)
        _ = q + 1 := Nat.add_div_right _ hnw
    rw [Finset.mem_image]
    refine ⟨(d / w % n, d % w), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range]
      refine ⟨?_, ht⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only
      rw [← hi]; exact hdec.symm
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (({q, q + 1} : Finset ℕ) ×ˢ Finset.range w).card := Finset.card_image_le
    _ = ({q, q + 1} : Finset ℕ).card * w := by rw [Finset.card_product, Finset.card_range]
    _ ≤ 2 * w := Nat.mul_le_mul_right _ Finset.card_le_two

/-! ### Distances -/

open Classical in
/-- **Most input bits are far from their sinks.** For every `j`, all but
`4 N (2k+3)^{j-1} w + u n w` of the `L = n² w` input bits are at distance `≥ j` from the sink of their
transposed position (`u` = number of rows with no source node). A bit at distance `< j` has its sink
in a ball of radius `j - 1` around a source node of its row. -/
theorem rowDist_sum_ge {n w : ℕ} (hD : D.Valid (n * n * w)) (hr : 1 ≤ r) (hrnw : r ≤ n * w)
    (j : ℕ) :
    j * (n * n * w) ≤ ∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d +
      j * (4 * D.nodes r * (2 * k + 3) ^ (j - 1) * w +
        ((Finset.range n).filter (fun i => ∀ a < D.nodes r, i ∉ D.rowsAt n w r a)).card *
          (n * w)) := by
  set N := D.nodes r with hN
  set E := D.edges r with hE
  set U := (Finset.range n).filter (fun i => ∀ a < N, i ∉ D.rowsAt n w r a) with hU
  set Unatt := (Finset.range (n * n * w)).filter (fun d => d / (n * w) ∈ U) with hUnatt
  set Near := (Finset.range N).biUnion (fun a => (D.rowsAt n w r a).biUnion (fun i =>
    (ball E N a (j - 1)).biUnion (fun s => (Finset.range (n * n * w)).filter
      (fun d => d / (n * w) = i ∧ D.outNode r (tpos n w d) = s)))) with hNear
  have hcU : Unatt.card = U.card * (n * w) := by
    have := card_filter_row (n * w) n U (Finset.filter_subset _ _)
    rw [show n * (n * w) = n * n * w by ring] at this
    exact this
  have hcN : Near.card ≤ 4 * N * (2 * k + 3) ^ (j - 1) * w := by
    calc Near.card
        ≤ ∑ a ∈ Finset.range N, ∑ i ∈ D.rowsAt n w r a, ∑ s ∈ ball E N a (j - 1), 2 * w := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun a _ => ?_))
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun i _ => ?_))
          exact le_trans Finset.card_biUnion_le
            (Finset.sum_le_sum (fun s _ => card_sink_row_le hD hr hrnw i s))
      _ ≤ ∑ _a ∈ Finset.range N, 2 * ((2 * k + 3) ^ (j - 1) * (2 * w)) := by
          apply Finset.sum_le_sum
          intro a _
          rw [Finset.sum_const, smul_eq_mul]
          calc (D.rowsAt n w r a).card * ∑ _s ∈ ball E N a (j - 1), 2 * w
              = (D.rowsAt n w r a).card * ((ball E N a (j - 1)).card * (2 * w)) := by
                rw [Finset.sum_const, smul_eq_mul]
            _ ≤ 2 * ((2 * k + 3) ^ (j - 1) * (2 * w)) :=
                Nat.mul_le_mul (card_rowsAt_le hD hrnw a)
                  (Nat.mul_le_mul_right _ (card_ball_le hD hr a (j - 1)))
      _ = 4 * N * (2 * k + 3) ^ (j - 1) * w := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  -- each bit outside `Unatt ∪ Near` is at distance `≥ j`
  have hfar : ∀ d ∈ Finset.range (n * n * w),
      j ≤ D.rowDist n w r d + (if d ∈ Unatt ∪ Near then j else 0) := by
    intro d hd
    split_ifs with hbad
    · exact Nat.le_add_left _ _
    rw [Nat.add_zero]
    have hdL := Finset.mem_range.1 hd
    have hL : 1 ≤ n * n * w := by omega
    have hrow : d / (n * w) < n := by
      rw [Nat.div_lt_iff_lt_mul (by
        rcases Nat.eq_zero_or_pos (n * w) with h | h
        · rw [Nat.mul_assoc, h, Nat.mul_zero] at hdL; omega
        · exact h)]
      calc d < n * n * w := hdL
        _ = n * (n * w) := by ring
    have hatt : ∃ a < N, d / (n * w) ∈ D.rowsAt n w r a := by
      by_contra hno
      push Not at hno
      exact hbad (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hd,
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hrow, hno⟩⟩))
    have hne : ((Finset.range N).filter (fun a => d / (n * w) ∈ D.rowsAt n w r a)).Nonempty := by
      obtain ⟨a, ha, hra⟩ := hatt
      exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, hra⟩⟩
    unfold TSDiagram.rowDist
    rw [dite_eq_left hne]
    apply Finset.le_inf'
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    by_contra hlt
    push Not at hlt
    have hsN := outNode_lt hD hr hL (tpos n w d)
    have hball := mem_ball_netDist (reachable (D := D) (r := r) ha.1 hsN)
    have hball' := ball_mono (E := E) (N := N) a (show _ ≤ j - 1 by omega) hball
    apply hbad
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.2 ⟨a, Finset.mem_range.2 ha.1, Finset.mem_biUnion.2 ⟨_, ha.2,
      Finset.mem_biUnion.2 ⟨_, hball', Finset.mem_filter.2 ⟨hd, rfl, rfl⟩⟩⟩⟩
  have hsum := Finset.sum_le_sum hfar
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul] at hsum
  have hbad : (Finset.range (n * n * w) ∩ (Unatt ∪ Near)).card ≤ Near.card + Unatt.card := by
    calc _ ≤ (Unatt ∪ Near).card := Finset.card_le_card Finset.inter_subset_right
      _ ≤ Unatt.card + Near.card := Finset.card_union_le _ _
      _ = Near.card + Unatt.card := Nat.add_comm _ _
  have hfinal : (n * n * w) * j ≤ ∑ d ∈ Finset.range (n * n * w), D.rowDist n w r d +
      (Near.card + Unatt.card) * j :=
    le_trans hsum (Nat.add_le_add_left (Nat.mul_le_mul_right _ hbad) _)
  rw [hcU] at hfinal
  have h2 : (Near.card + U.card * (n * w)) * j ≤
      j * (4 * N * (2 * k + 3) ^ (j - 1) * w + U.card * (n * w)) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hcN _)
  calc j * (n * n * w) = (n * n * w) * j := Nat.mul_comm _ _
    _ ≤ _ := hfinal
    _ ≤ _ := Nat.add_le_add_left h2 _

/-! ### Capacities -/

open Classical in
/-- Every tape has at most one chord into each node, so the chord edges carry at most `k N` tape
chords in all. -/
theorem sum_chordTapes_le (hD : D.Valid L) (hr : 1 ≤ r) :
    ∑ e ∈ D.chordEdges r, D.chordTapes r e ≤ k * D.nodes r := by
  have hh : ∀ t, UnitSteps (D.work t) := fun t => (hD.1 t).2
  have e1 : ∑ e ∈ D.chordEdges r, D.chordTapes r e =
      ∑ t : Fin k, ((D.chordEdges r).filter
        (fun e => ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2)).card := by
    simp only [TSDiagram.chordTapes, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [e1]
  calc ∑ t : Fin k, ((D.chordEdges r).filter
        (fun e => ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2)).card
      ≤ ∑ _t : Fin k, D.nodes r := by
        apply Finset.sum_le_sum
        intro t _
        calc _ ≤ (Finset.range (D.nodes r)).card := by
              apply Finset.card_le_card_of_injOn (fun e => e.2)
              · intro e he
                rw [Finset.mem_coe, Finset.mem_filter] at he
                exact Finset.mem_coe.2 (Finset.mem_range.2 ((mem_chordEdges D).1 he.1).2.1)
              · intro e he e' he' hee
                rw [Finset.mem_coe, Finset.mem_filter] at he he'
                obtain ⟨β, hβ⟩ := he.2
                obtain ⟨β', hβ'⟩ := he'.2
                simp only at hee
                rw [← hee] at hβ'
                have := (pairRes_chord_target_unique (hh t) hr D.T hβ hβ').2
                exact Prod.ext this hee
          _ = D.nodes r := Finset.card_range _
    _ = k * D.nodes r := by simp

open Classical in
/-- The block network of a valid diagram has at most `k N` chord edges. -/
theorem card_chordEdges_le (hD : D.Valid L) (hr : 1 ≤ r) :
    (D.chordEdges r).card ≤ k * D.nodes r := by
  refine le_trans ?_ (sum_chordTapes_le hD hr)
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨-, -, t, β, hch⟩ := (mem_chordEdges D).1 he
  simp only [TSDiagram.chordTapes]
  exact Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, β, hch⟩⟩

theorem card_memEdges_le (r : ℕ) : (D.memEdges r).card ≤ D.nodes r := by
  unfold TSDiagram.memEdges
  exact le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) (by simp))

/-- **Capacities within the block profile sum to `O(N r G)`**: at most `4k N r G` (at most `3k`
resident blocks per memory edge, and `k N` tape chords in all). -/
theorem sum_cap_le_of_pos {n G : ℕ} (hD : D.Valid L) (hr : 1 ≤ blockSize G n) {cap : ℕ × ℕ → ℕ}
    (hcap : D.CapProfile n G cap) :
    ∑ e ∈ D.edges (blockSize G n), cap e ≤
      4 * k * D.nodes (blockSize G n) * (blockSize G n * G) := by
  set r := blockSize G n
  set B := r * G
  have hdisj : Disjoint (D.memEdges r) (D.chordEdges r) :=
    Finset.disjoint_left.2 (fun e hm hc => not_mem_chordEdges_of_mem_memEdges D hm hc)
  rw [TSDiagram.edges, Finset.sum_union hdisj]
  have hres : ∀ y, ∑ t, (pairRes r (D.work t) D.T y).card ≤ 3 * k := by
    intro y
    calc ∑ t, (pairRes r (D.work t) D.T y).card ≤ ∑ _t : Fin k, 3 :=
          Finset.sum_le_sum (fun t _ => (pairRes_admissible (hD.1 t).2 hr D.T).2 y)
      _ = 3 * k := by simp [Nat.mul_comm]
  have h1 : ∑ e ∈ D.memEdges r, cap e ≤ D.nodes r * (3 * k * B) := by
    calc _ ≤ ∑ e ∈ D.memEdges r, (∑ t, (pairRes r (D.work t) D.T e.1).card) * B :=
          Finset.sum_le_sum (fun e he => hcap.1 e he)
      _ ≤ ∑ _e ∈ D.memEdges r, 3 * k * B :=
          Finset.sum_le_sum (fun e _ => Nat.mul_le_mul_right _ (hres e.1))
      _ = (D.memEdges r).card * (3 * k * B) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (card_memEdges_le r)
  have h2 : ∑ e ∈ D.chordEdges r, cap e ≤ k * D.nodes r * B := by
    calc _ ≤ ∑ e ∈ D.chordEdges r, D.chordTapes r e * B :=
          Finset.sum_le_sum (fun e he => hcap.2 e he)
      _ = (∑ e ∈ D.chordEdges r, D.chordTapes r e) * B := by rw [Finset.sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (sum_chordTapes_le hD hr)
  calc _ ≤ D.nodes r * (3 * k * B) + k * D.nodes r * B := Nat.add_le_add h1 h2
    _ = 4 * k * D.nodes r * B := by ring

theorem nodes_zero (D : TSDiagram k) : D.nodes 0 = 0 := by
  simp [TSDiagram.nodes, numSlots]

theorem edges_zero (D : TSDiagram k) : D.edges 0 = ∅ := by
  classical
  unfold TSDiagram.edges TSDiagram.memEdges TSDiagram.chordEdges
  simp [nodes_zero]

/-- **The total capacity** is at most `4 k` blocks per node (also for block size `0`, where there are
no nodes). -/
theorem sum_cap_le {n G : ℕ} (hD : D.Valid L) {cap : ℕ × ℕ → ℕ}
    (hcap : D.CapProfile n G cap) :
    ∑ e ∈ D.edges (blockSize G n), cap e ≤
      4 * k * D.nodes (blockSize G n) * (blockSize G n * G) := by
  rcases Nat.eq_zero_or_pos (blockSize G n) with h0 | hr
  · rw [h0, edges_zero]; simp
  · exact sum_cap_le_of_pos hD hr hcap

end Count

end Transpose.Tape.Impl

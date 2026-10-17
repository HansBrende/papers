import Transpose.Tape.CEProfile

/-!
# The cut-set bound for network codes, and Discrete Isoperimetry for every code-carrying diagram

TM-free. For a causal code solving complete exchange on a set `F` of inputs in the block network of
a diagram, and a set `U` of nodes:
* `cutset_bits_bitwise`: the bits form of the bit-level cut-set bound `cutset_bound_bitwise`
  (`CENet.lean`): the input bits whose row is attached at no node of `U` and whose transposed position
  is decoded at a node of `U` number at most `D + Σ_{e entering U} cap e` when `2^L ≤ 2^D |F|`.
* `cutset_bound`, `cutset_bits`: the entry form. The entries `(i, j)` with row `i` attached at no
  node of `U` and column `j` produced entirely at nodes of `U` give `w |S_U| ≤ |B_U|` cut bits.
* `isoperimetry_code`: summing over the classes of a slot labelling with at most `m` slots per class
  and `M_b` label changes,
  `(n - M_b)(n - 2m) w ≤ (M_b + 1) D + Σ_{e between different labels} cap e`
  when `2^L ≤ 2^D |F|`.

With `traceClass_code` these give the Cut Lemma and Discrete Isoperimetry on trace classes (at
`b = w`, `r = slotLen M n`); here they hold for every code-carrying diagram, so they constrain any
counterexample to `RobustNoCode_TM` (and give Theorem M\* for code-carrying diagrams,
`cutIneq_of_solves`).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

section Cut

variable {k : ℕ} (D : TSDiagram k)

/-- An entry `(i, j)` of a cut has its `w` bits at `(i n + j) w + t`. -/
theorem cut_bits_card {n w : ℕ} (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, p.1 < n ∧ p.2 < n)
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ p ∈ S, ∀ t < w, P ((p.1 * n + p.2) * w + t)) :
    w * S.card ≤ ((Finset.range (n * n * w)).filter P).card := by
  have hinj : Set.InjOn (fun q : (ℕ × ℕ) × ℕ => (q.1.1 * n + q.1.2) * w + q.2)
      ↑(S ×ˢ Finset.range w) := by
    rintro ⟨⟨i, j⟩, t⟩ hq ⟨⟨i', j'⟩, t'⟩ hq' he
    rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_coe, Finset.mem_range] at hq hq'
    have hj : j < n := (hS _ hq.1).2
    have hj' : j' < n := (hS _ hq'.1).2
    have ht : t < w := hq.2
    have ht' : t' < w := hq'.2
    simp only at he
    have hw : 0 < w := by omega
    have hn : 0 < n := by omega
    have e1 : ((i * n + j) * w + t) / w = ((i' * n + j') * w + t') / w := by rw [he]
    have e2 : ((i * n + j) * w + t) % w = ((i' * n + j') * w + t') % w := by rw [he]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ht, Nat.zero_add,
      Nat.add_comm _ t', Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ht', Nat.zero_add] at e1
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht, Nat.add_comm _ t',
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht'] at e2
    have e3 : (i * n + j) / n = (i' * n + j') / n := by rw [e1]
    have e4 : (i * n + j) % n = (i' * n + j') % n := by rw [e1]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add,
      Nat.add_comm _ j', Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj', Nat.zero_add] at e3
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj, Nat.add_comm _ j',
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj'] at e4
    rw [e3, e4, e2]
  calc w * S.card = (S ×ˢ Finset.range w).card := by
        rw [Finset.card_product, Finset.card_range, Nat.mul_comm]
    _ ≤ _ := by
        apply Finset.card_le_card_of_injOn _ _ hinj
        intro q hq
        rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_coe,
          Finset.mem_range] at hq
        have hi : q.1.1 < n := (hS q.1 hq.1).1
        have hj : q.1.2 < n := (hS q.1 hq.1).2
        rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range]
        refine ⟨?_, hP q.1 hq.1 q.2 hq.2⟩
        calc (q.1.1 * n + q.1.2) * w + q.2 < (q.1.1 * n + q.1.2) * w + w := by omega
          _ = (q.1.1 * n + q.1.2 + 1) * w := by ring
          _ ≤ (q.1.1 * n + n) * w := Nat.mul_le_mul_right _ (by omega)
          _ = (q.1.1 + 1) * n * w := by ring
          _ ≤ n * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)

/-- Bit `d` lies in row `d / (n w)` and column `d / w % n`; its transposed position is in the column's
output range. -/
theorem tpos_mem_col {n w d : ℕ} (hd : d < n * n * w) :
    d / w % n * n * w ≤ tpos n w d ∧ tpos n w d < (d / w % n + 1) * n * w := by
  have hnw : 0 < n * w := by
    rcases Nat.eq_zero_or_pos (n * w) with h | h
    · rw [Nat.mul_assoc, h, Nat.mul_zero] at hd; omega
    · exact h
  have hq := tpos_div hd
  have h1 := Nat.div_mul_le_self (tpos n w d) (n * w)
  have h2 := Nat.lt_mul_div_succ (tpos n w d) hnw
  rw [hq] at h1 h2
  constructor
  · calc d / w % n * n * w = d / w % n * (n * w) := by ring
      _ ≤ tpos n w d := h1
  · calc tpos n w d < n * w * (d / w % n + 1) := h2
      _ = (d / w % n + 1) * n * w := by ring

/-- The row and column of the bit `(i n + j) w + t`. -/
theorem pos_row_col {n w i j t : ℕ} (hj : j < n) (ht : t < w) :
    ((i * n + j) * w + t) / (n * w) = i ∧ ((i * n + j) * w + t) / w % n = j := by
  have hw : 0 < w := by omega
  have hn : 0 < n := by omega
  constructor
  · have e : (i * n + j) * w + t = i * (n * w) + (j * w + t) := by ring
    have hlt : j * w + t < n * w := by
      calc j * w + t < j * w + w := by omega
        _ = (j + 1) * w := by ring
        _ ≤ n * w := Nat.mul_le_mul_right _ hj
    rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
      Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ht, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **The cut-set bound, bit level, bits form**: if `2^L ≤ 2^{D_c} |F|`, then
`|B_U| ≤ D_c + Σ_{e entering U} cap e`. -/
theorem cutset_bits_bitwise {n G : ℕ} {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) (U : Set ℕ)
    [DecidablePred (· ∈ U)] :
    ((Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U)).card ≤
      Dc + ∑ e ∈ D.edgesInto (blockSize G n) U, cap e := by
  have h := cutset_bound_bitwise D hsol U
  set B := (Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U) with hB
  have h2 : 2 ^ B.card * F.ncard ≤
      2 ^ (Dc + ∑ e ∈ D.edgesInto (blockSize G n) U, cap e) * F.ncard := by
    calc _ ≤ 2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) := h
      _ ≤ 2 ^ Dc * F.ncard * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) :=
          Nat.mul_le_mul_right _ hco
      _ = _ := by rw [pow_add]; ring
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
    (Nat.le_of_mul_le_mul_right h2 (ncard_pos_of_coentropy hco))

/-- The entries of `S_U` give `w |S_U|` cut bits. -/
theorem entry_cut_le_bitwise {n G : ℕ} (U : Set ℕ) [DecidablePred (· ∈ U)] :
    entryBits n * ((Finset.range n \ D.rowsIn n (entryBits n) (blockSize G n) U) ×ˢ
        D.colsIn n (entryBits n) (blockSize G n) U).card ≤
      ((Finset.range (n * n * entryBits n)).filter (fun d =>
        d / (n * entryBits n) ∉ D.rowsIn n (entryBits n) (blockSize G n) U ∧
        D.outNode (blockSize G n) (tpos n (entryBits n) d) ∈ U)).card := by
  classical
  apply cut_bits_card
  · intro p hp
    rw [Finset.mem_product, Finset.mem_sdiff, Finset.mem_range] at hp
    exact ⟨hp.1.1, Finset.mem_range.1 (Finset.mem_filter.1 hp.2).1⟩
  · intro p hp t ht
    rw [Finset.mem_product, Finset.mem_sdiff, Finset.mem_range] at hp
    have hi : p.1 < n := hp.1.1
    have hj : p.2 < n := Finset.mem_range.1 (Finset.mem_filter.1 hp.2).1
    obtain ⟨hrow, hcol⟩ := pos_row_col (i := p.1) hj ht
    have hd : (p.1 * n + p.2) * entryBits n + t < n * n * entryBits n := by
      calc (p.1 * n + p.2) * entryBits n + t < (p.1 * n + p.2) * entryBits n + entryBits n := by
            omega
        _ = (p.1 * n + p.2 + 1) * entryBits n := by ring
        _ ≤ (p.1 * n + n) * entryBits n := Nat.mul_le_mul_right _ (by omega)
        _ = (p.1 + 1) * n * entryBits n := by ring
        _ ≤ n * n * entryBits n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
    have hm := tpos_mem_col hd
    rw [hcol] at hm
    exact ⟨by rw [hrow]; exact hp.1.2, (Finset.mem_filter.1 hp.2).2 _ hm.1 hm.2⟩

/-- **The cut-set bound** (TM-free; entry form). If a causal code solves complete exchange on `F`
within `cap`, then for every set `U` of nodes, with `S_U` the entries whose row is attached at no node
of `U` and whose column is produced entirely at nodes of `U`,
`2^{w |S_U|} |F| ≤ 2^L · 2^{Σ_{e entering U} cap e}`. A corollary of the bit-level bound
`cutset_bound_bitwise`. -/
theorem cutset_bound {n G : ℕ} {cap : ℕ × ℕ → ℕ} {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode} (hsol : D.Solves n G cap F code) (U : Set ℕ) [DecidablePred (· ∈ U)] :
    2 ^ (entryBits n * ((Finset.range n \ D.rowsIn n (entryBits n) (blockSize G n) U) ×ˢ
        D.colsIn n (entryBits n) (blockSize G n) U).card) * F.ncard ≤
      2 ^ (n * n * entryBits n) * 2 ^ (∑ e ∈ D.edgesInto (blockSize G n) U, cap e) :=
  le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (entry_cut_le_bitwise D U)))
    (cutset_bound_bitwise D hsol U)

/-- **The cut-set bound, bits form**: if `2^L ≤ 2^{D_c} |F|`, then
`w |S_U| ≤ D_c + Σ_{e entering U} cap e`. -/
theorem cutset_bits {n G : ℕ} {cap : ℕ × ℕ → ℕ} {F : Set (Fin (n * n * entryBits n) → Bool)}
    {code : NetCode} (hsol : D.Solves n G cap F code) {Dc : ℕ}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) (U : Set ℕ) [DecidablePred (· ∈ U)] :
    entryBits n * ((Finset.range n \ D.rowsIn n (entryBits n) (blockSize G n) U) ×ˢ
        D.colsIn n (entryBits n) (blockSize G n) U).card ≤
      Dc + ∑ e ∈ D.edgesInto (blockSize G n) U, cap e :=
  le_trans (entry_cut_le_bitwise D U) (cutset_bits_bitwise D hsol hco U)

/-- `outNode` is monotone. -/
theorem outNode_mono {r o o' : ℕ} (h : o ≤ o') : D.outNode r o ≤ D.outNode r o' := by
  classical
  unfold TSDiagram.outNode
  exact Nat.findGreatest_mono_left (fun y hy => le_trans hy h) _

/-- A class of at most `m` nodes has at most `2m` source rows. -/
theorem card_rowsIn_le {L n w r m : ℕ} (hD : D.Valid L) (hrnw : r ≤ n * w) (lab : ℕ → ℕ) (ℓ : ℕ)
    (hm : ((Finset.range (D.nodes r)).filter (fun y => lab y = ℓ)).card ≤ m) :
    (D.rowsIn n w r {y | lab y = ℓ}).card ≤ 2 * m := by
  unfold TSDiagram.rowsIn
  refine le_trans Finset.card_biUnion_le ?_
  calc _ ≤ ∑ _y ∈ (Finset.range (D.nodes r)).filter (· ∈ {y | lab y = ℓ}), 2 :=
        Finset.sum_le_sum (fun y _ => card_rowsAt_le hD hrnw y)
    _ = ((Finset.range (D.nodes r)).filter (fun y => lab y = ℓ)).card * 2 := by
        rw [Finset.sum_const, smul_eq_mul]; rfl
    _ ≤ 2 * m := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hm

/-- **Split columns are at most the label changes.** A column whose outputs are not all produced in
one class of the labelling contains a label change between its first output's node and a later one;
these changes are distinct for distinct columns, since outputs are produced in order. -/
theorem split_cols_le {n r : ℕ} (hD : D.Valid (n * n * entryBits n)) (hr : 1 ≤ r) (lab : ℕ → ℕ) :
    (Finset.range n \ ((Finset.range (D.nodes r)).image lab).biUnion
        (fun ℓ => D.colsIn n (entryBits n) r {y | lab y = ℓ})).card ≤
      labelChanges lab (D.nodes r) := by
  set N := D.nodes r with hN
  set w := entryBits n with hw
  have hw1 : 1 ≤ w := by rw [hw]; unfold entryBits; omega
  -- a label change inside every split column
  have hsplit : ∀ j ∈ Finset.range n \ ((Finset.range N).image lab).biUnion
      (fun ℓ => D.colsIn n w r {y | lab y = ℓ}),
      ∃ τ, D.outNode r (j * n * w) < τ ∧ τ < N ∧
        τ ≤ D.outNode r ((j + 1) * n * w - 1) ∧ lab τ ≠ lab (τ - 1) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    obtain ⟨hjn, hns⟩ := hj
    have hL : 1 ≤ n * n * w := by
      have : 1 ≤ n := by omega
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    set s₀ := D.outNode r (j * n * w) with hs₀
    have hs₀N : s₀ < N := outNode_lt hD hr hL _
    -- some output of the column is produced outside the class of `s₀`
    have hnot : ¬ ∀ o, j * n * w ≤ o → o < (j + 1) * n * w → D.outNode r o ∈ {y | lab y = lab s₀} := by
      intro hall
      apply hns
      refine Finset.mem_biUnion.2 ⟨lab s₀, Finset.mem_image.2 ⟨s₀, Finset.mem_range.2 hs₀N, rfl⟩, ?_⟩
      unfold TSDiagram.colsIn
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hjn, hall⟩
    push Not at hnot
    obtain ⟨o, ho1, ho2, hlab⟩ := hnot
    have hlab' : lab s₀ ≠ lab (D.outNode r o) := fun h => hlab (by simp [h])
    have hle : s₀ ≤ D.outNode r o := outNode_mono D ho1
    have hlt : s₀ < D.outNode r o := lt_of_le_of_ne hle (fun h => hlab' (by rw [h]))
    obtain ⟨τ, h1, h2, h3⟩ := label_change_between lab hlt hlab'
    have hoN : D.outNode r o < N := outNode_lt hD hr hL _
    refine ⟨τ, h1, by omega, le_trans h2 (outNode_mono D (by omega)), h3⟩
  choose! f hf using hsplit
  unfold labelChanges
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    obtain ⟨h1, h2, -, h4⟩ := hf j hj
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range]
    exact ⟨h2, by omega, h4⟩
  · intro j hj j' hj' hjj
    by_contra hne
    have hj1 := (Finset.mem_sdiff.1 hj).1
    have hj1' := (Finset.mem_sdiff.1 hj').1
    -- distinct columns: the earlier one's change comes strictly before the later one's
    have key : ∀ a b, a ∈ Finset.range n \ ((Finset.range N).image lab).biUnion
          (fun ℓ => D.colsIn n w r {y | lab y = ℓ}) →
        b ∈ Finset.range n \ ((Finset.range N).image lab).biUnion
          (fun ℓ => D.colsIn n w r {y | lab y = ℓ}) → a < b → f a < f b := by
      intro a b ha hb hab
      obtain ⟨-, -, ha3, -⟩ := hf a ha
      obtain ⟨hb1, -, -, -⟩ := hf b hb
      have hmono : D.outNode r ((a + 1) * n * w - 1) ≤ D.outNode r (b * n * w) := by
        apply outNode_mono
        have : (a + 1) * n * w ≤ b * n * w :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hab)
        omega
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hjj (ne_of_lt (key j j' hj hj' h))
    · exact absurd hjj.symm (ne_of_lt (key j' j hj' hj h))

/-- The capacities entering the classes of a labelling add up to at most the capacity of the edges
between different labels. -/
theorem sum_edgesInto_le {r : ℕ} (cap : ℕ × ℕ → ℕ) (lab : ℕ → ℕ) (Ls : Finset ℕ) :
    ∑ ℓ ∈ Ls, ∑ e ∈ D.edgesInto r {y | lab y = ℓ}, cap e ≤
      ∑ e ∈ (D.edges r).filter (fun e => lab e.1 ≠ lab e.2), cap e := by
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset
    intro e he
    obtain ⟨ℓ, -, he⟩ := Finset.mem_biUnion.1 he
    unfold TSDiagram.edgesInto at he
    obtain ⟨heE, h1, h2⟩ := Finset.mem_filter.1 he
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact Finset.mem_filter.2 ⟨heE, by rw [h2]; exact h1⟩
  · intro ℓ _ ℓ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    unfold TSDiagram.edgesInto at he he'
    have h1 := (Finset.mem_filter.1 he).2.2
    have h2 := (Finset.mem_filter.1 he').2.2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact hne (h1.symm.trans h2)

open Classical in
/-- **Discrete Isoperimetry for every code-carrying diagram** (TM-free). Let a causal code solve
complete exchange on `F` (with `2^L ≤ 2^{D_c} |F|`) in the block network of a valid diagram, block
size `1 ≤ r ≤ n w`. For a labelling of the slots with at most `m` slots per label and `M_b` label
changes,

  `(n - M_b)(n - 2m) w ≤ (M_b + 1) D_c + Σ_{e between different labels} cap e`. -/
theorem isoperimetry_code {n G : ℕ} (hD : D.Valid (n * n * entryBits n)) (hr : 1 ≤ blockSize G n)
    {cap : ℕ × ℕ → ℕ}
    {F : Set (Fin (n * n * entryBits n) → Bool)} {code : NetCode} (hsol : D.Solves n G cap F code)
    {Dc : ℕ} (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ Dc * F.ncard) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (D.nodes (blockSize G n))).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (D.nodes (blockSize G n))) * (n - 2 * m) * entryBits n ≤
      (labelChanges lab (D.nodes (blockSize G n)) + 1) * Dc +
        ∑ e ∈ (D.edges (blockSize G n)).filter (fun e => lab e.1 ≠ lab e.2), cap e := by
  have hrnw : blockSize G n ≤ n * entryBits n :=
    blockSize_le (Nat.pos_of_ne_zero (by rintro rfl; simp [blockSize] at hr))
  set r := blockSize G n with hrdef
  set N := D.nodes r with hN
  set Mb := labelChanges lab N with hMb
  set Ls := (Finset.range N).image lab with hLs
  -- the per-class cut bounds, summed
  have hsum : entryBits n * ∑ ℓ ∈ Ls, ((Finset.range n \ D.rowsIn n (entryBits n) r {y | lab y = ℓ}) ×ˢ
      D.colsIn n (entryBits n) r {y | lab y = ℓ}).card ≤
      Ls.card * Dc + ∑ e ∈ (D.edges r).filter (fun e => lab e.1 ≠ lab e.2), cap e := by
    rw [Finset.mul_sum]
    calc ∑ ℓ ∈ Ls, entryBits n * ((Finset.range n \ D.rowsIn n (entryBits n) r {y | lab y = ℓ}) ×ˢ
          D.colsIn n (entryBits n) r {y | lab y = ℓ}).card
        ≤ ∑ ℓ ∈ Ls, (Dc + ∑ e ∈ D.edgesInto r {y | lab y = ℓ}, cap e) :=
          Finset.sum_le_sum (fun ℓ _ => cutset_bits D hsol hco _)
      _ = Ls.card * Dc + ∑ ℓ ∈ Ls, ∑ e ∈ D.edgesInto r {y | lab y = ℓ}, cap e := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.add_le_add_left (sum_edgesInto_le D cap lab Ls) _
  -- the cuts are large
  have hcuts : (n - Mb) * (n - 2 * m) ≤
      ∑ ℓ ∈ Ls, ((Finset.range n \ D.rowsIn n (entryBits n) r {y | lab y = ℓ}) ×ˢ
        D.colsIn n (entryBits n) r {y | lab y = ℓ}).card := by
    have hsplit : (Finset.range n \ Ls.biUnion
        (fun ℓ => D.colsIn n (entryBits n) r {y | lab y = ℓ})).card ≤ Mb :=
      split_cols_le D hD hr lab
    have hcov : n - Mb ≤ (Ls.biUnion (fun ℓ => D.colsIn n (entryBits n) r {y | lab y = ℓ})).card := by
      have h1 := Finset.le_card_sdiff (Ls.biUnion (fun ℓ => D.colsIn n (entryBits n) r {y | lab y = ℓ}))
        (Finset.range n)
      rw [Finset.card_range] at h1
      omega
    calc (n - Mb) * (n - 2 * m)
        ≤ (Ls.biUnion (fun ℓ => D.colsIn n (entryBits n) r {y | lab y = ℓ})).card * (n - 2 * m) :=
          Nat.mul_le_mul_right _ hcov
      _ ≤ (∑ ℓ ∈ Ls, (D.colsIn n (entryBits n) r {y | lab y = ℓ}).card) * (n - 2 * m) :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ ℓ ∈ Ls, (D.colsIn n (entryBits n) r {y | lab y = ℓ}).card * (n - 2 * m) :=
          Finset.sum_mul _ _ _
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ℓ _
          rw [Finset.card_product, Nat.mul_comm]
          apply Nat.mul_le_mul_right
          have h1 := Finset.le_card_sdiff (D.rowsIn n (entryBits n) r {y | lab y = ℓ}) (Finset.range n)
          rw [Finset.card_range] at h1
          have h2 := card_rowsIn_le D hD hrnw lab ℓ (hm ℓ)
          omega
  have hLs : Ls.card ≤ Mb + 1 := card_image_lab_le lab N
  calc (n - Mb) * (n - 2 * m) * entryBits n
      ≤ entryBits n * ∑ ℓ ∈ Ls, ((Finset.range n \ D.rowsIn n (entryBits n) r {y | lab y = ℓ}) ×ˢ
          D.colsIn n (entryBits n) r {y | lab y = ℓ}).card := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hcuts
    _ ≤ Ls.card * Dc + ∑ e ∈ (D.edges r).filter (fun e => lab e.1 ≠ lab e.2), cap e := hsum
    _ ≤ (Mb + 1) * Dc + ∑ e ∈ (D.edges r).filter (fun e => lab e.1 ≠ lab e.2), cap e :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hLs) _

end Cut

end Transpose.Tape.Impl

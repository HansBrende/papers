import Transpose.Tape.CECount

/-!
# Attached short-distance count

Lemma 8.3 of *Source Covers and Barriers to Tape Transposition*.
The first paper supplies the block network, row attachments, output nodes,
graph distances, and their three counting estimates. This file exposes the
standalone short-bit bound needed for partial, unequal commodity masses.

The attachment condition is essential: the inherited `rowDist` definition
assigns zero to an unattached row, but those bits must not be counted here.
-/

namespace SourceCovers

open Transpose Transpose.Tape Transpose.Tape.Impl

variable {k : ℕ} {D : TSDiagram k} {d b r ℓ x : ℕ}

open Classical in
/-- Raw bits whose row has an attachment and whose nearest attachment is
at undirected graph distance strictly less than `ℓ` from their output node. -/
noncomputable def attachedShortBits (D : TSDiagram k) (d b r ℓ : ℕ) : Finset ℕ :=
  (Finset.range (d * d * b)).filter fun x =>
    (∃ a < D.nodes r, x / (d * b) ∈ D.rowsAt d b r a) ∧ D.rowDist d b r x < ℓ

/-- Exact bridge from the nearest-attachment definition to a finite ball cover. -/
theorem mem_attachedShortBits_iff (hℓ : 1 ≤ ℓ) :
    x ∈ attachedShortBits D d b r ℓ ↔
      x < d * d * b ∧ ∃ a < D.nodes r,
        x / (d * b) ∈ D.rowsAt d b r a ∧
        D.outNode r (tpos d b x) ∈ ball (D.edges r) (D.nodes r) a (ℓ - 1) := by
  classical
  constructor
  · intro hx
    obtain ⟨hxL, hatt, hdist⟩ := Finset.mem_filter.mp hx
    have hne : ((Finset.range (D.nodes r)).filter
        (fun a => x / (d * b) ∈ D.rowsAt d b r a)).Nonempty := by
      obtain ⟨a, ha, harow⟩ := hatt
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, harow⟩⟩
    unfold TSDiagram.rowDist at hdist
    rw [dite_eq_left hne] at hdist
    obtain ⟨a, ha, hnear⟩ := (Finset.inf'_lt_iff hne).mp hdist
    obtain ⟨haN, harow⟩ := Finset.mem_filter.mp ha
    have hxL' := Finset.mem_range.mp hxL
    have hs : D.outNode r (tpos d b x) < D.nodes r := by
      have ha := Finset.mem_range.mp haN
      have hbound : D.outNode r (tpos d b x) ≤ D.nodes r - 1 := Nat.findGreatest_le _
      omega
    have hb := mem_ball_netDist (reachable (D := D) (r := r)
      (Finset.mem_range.mp haN) hs)
    exact ⟨hxL', a, Finset.mem_range.mp haN, harow,
      ball_mono a (show _ ≤ ℓ - 1 by omega) hb⟩
  · rintro ⟨hxL, a, ha, harow, hball⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hxL, ⟨a, ha, harow⟩, ?_⟩
    have hdist := le_trans (rowDist_le ha harow) (netDist_le_of_mem_ball hball)
    omega

open Classical in
/-- Bits of one raw row whose transposed positions are produced at one block. -/
noncomputable def rowSinkBits (D : TSDiagram k) (d b r i s : ℕ) : Finset ℕ :=
  (Finset.range (d * d * b)).filter fun x =>
    x / (d * b) = i ∧ D.outNode r (tpos d b x) = s

/-- An output interval of length at most one column contains at most `b` bits
of any fixed raw row, even when it straddles a column boundary. -/
theorem card_rowSinkBits_le (hD : D.Valid (d * d * b))
    (hr : 1 ≤ r) (hrdb : r ≤ d * b) (i s : ℕ) :
    (rowSinkBits D d b r i s).card ≤ b := by
  classical
  let S := (Finset.range (d * d * b)).filter (fun x => x / (d * b) = i ∧
    D.outNode r (tpos d b x) = s)
  have hb : 0 < b := by nlinarith
  have repr {x : ℕ} (hx : x ∈ S) :
      x = (i * d + x / b % d) * b + x % b ∧
      tpos d b x = (x / b % d) * (d * b) + i * b + x % b ∧
      D.out (s * r) ≤ tpos d b x ∧ tpos d b x < D.out (s * r) + r := by
    obtain ⟨hxL, hrow, hs⟩ := Finset.mem_filter.mp hx
    have hxL' := Finset.mem_range.mp hxL
    obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hxL'
    have hrow' : x / b / d = i := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm b d]
      exact hrow
    have htp := tpos_spec (i := x / b / d) hj ht
    rw [← hdec, hrow'] at htp
    have ho := outNode_spec hD hr (tpos_lt hxL')
    rw [hs] at ho
    refine ⟨?_, ?_, ho⟩
    · simpa [hrow'] using hdec
    · rw [htp]; ring
  calc S.card ≤ (Finset.range b).card := by
        apply Finset.card_le_card_of_injOn (fun x => x % b)
        · intro x _; exact Finset.mem_range.mpr (Nat.mod_lt _ hb)
        · intro x hx y hy hmod
          change x % b = y % b at hmod
          obtain ⟨hx, htx, hox₁, hox₂⟩ := repr hx
          obtain ⟨hy, hty, hoy₁, hoy₂⟩ := repr hy
          have hcol : x / b % d = y / b % d := by
            rcases lt_trichotomy (x / b % d) (y / b % d) with h | h | h
            · have hm := Nat.mul_le_mul_right (d * b) (Nat.succ_le_iff.mpr h)
              rw [htx] at hox₁ hox₂
              rw [hty] at hoy₁ hoy₂
              nlinarith
            · exact h
            · have hm := Nat.mul_le_mul_right (d * b) (Nat.succ_le_iff.mpr h)
              rw [htx] at hox₁ hox₂
              rw [hty] at hoy₁ hoy₂
              nlinarith
          rw [hx, hy, hcol, hmod]
      _ = b := Finset.card_range b

@[simp] theorem attachedShortBits_zero_radius (D : TSDiagram k) (d b r : ℕ) :
    attachedShortBits D d b r 0 = ∅ := by
  classical
  simp [attachedShortBits]

@[simp] theorem attachedShortBits_zero_block (D : TSDiagram k) (d b ℓ : ℕ) :
    attachedShortBits D d b 0 ℓ = ∅ := by
  classical
  simp [attachedShortBits, TSDiagram.nodes, numSlots]

/-- Counting the actual local contributions needs neither diagram validity nor
restrictions on block length or radius. -/
theorem card_attachedShortBits_le_local (D : TSDiagram k) (d b r ℓ : ℕ) :
    (attachedShortBits D d b r ℓ).card ≤
      ∑ a ∈ Finset.range (D.nodes r), ∑ i ∈ D.rowsAt d b r a,
        ∑ s ∈ ball (D.edges r) (D.nodes r) a (ℓ - 1),
          (rowSinkBits D d b r i s).card := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  let near := (Finset.range (D.nodes r)).biUnion fun a =>
    (D.rowsAt d b r a).biUnion fun i =>
      (ball (D.edges r) (D.nodes r) a (ℓ - 1)).biUnion fun s =>
        rowSinkBits D d b r i s
  have hsub : attachedShortBits D d b r ℓ ⊆ near := by
    intro x hx
    obtain ⟨hxL, a, ha, harow, hball⟩ := (mem_attachedShortBits_iff hℓ).mp hx
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_range.mpr ha,
      Finset.mem_biUnion.mpr ⟨_, harow, Finset.mem_biUnion.mpr
        ⟨_, hball, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxL, rfl, rfl⟩⟩⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun a _ => ?_)
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun i _ => ?_)
  exact Finset.card_biUnion_le

/-- The row/ball profile retains the actual numbers of attachments and ball
vertices. Zero radius and zero block length are allowed. -/
theorem card_attachedShortBits_le_profile (hD : D.Valid (d * d * b))
    (hrdb : r ≤ d * b) :
    (attachedShortBits D d b r ℓ).card ≤ b *
      ∑ a ∈ Finset.range (D.nodes r),
        (D.rowsAt d b r a).card * (ball (D.edges r) (D.nodes r) a (ℓ - 1)).card := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  calc
    (attachedShortBits D d b r ℓ).card ≤
        ∑ a ∈ Finset.range (D.nodes r), ∑ i ∈ D.rowsAt d b r a,
          ∑ s ∈ ball (D.edges r) (D.nodes r) a (ℓ - 1),
            (rowSinkBits D d b r i s).card := card_attachedShortBits_le_local D d b r ℓ
    _ ≤ ∑ a ∈ Finset.range (D.nodes r), ∑ _i ∈ D.rowsAt d b r a,
          ∑ _s ∈ ball (D.edges r) (D.nodes r) a (ℓ - 1), b := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum fun s _ => card_rowSinkBits_le hD hr hrdb i s
    _ = _ := by
      simp only [Finset.sum_const, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _; ring

/-- The initial block can touch only row zero: the input head starts at zero
and has fewer than `r ≤ d*b` steps before that block ends. -/
theorem card_rowsAt_zero_le_one (hD : D.Valid (d * d * b)) (hrdb : r ≤ d * b) :
    (D.rowsAt d b r 0).card ≤ 1 := by
  classical
  have hsub : D.rowsAt d b r 0 ⊆ {0} := by
    intro i hi
    obtain ⟨_, τ, hτ, hlo, _⟩ := Finset.mem_filter.mp hi
    have hτr : τ < r := by simpa using (mem_slotOf.mp hτ).2.1
    have hdist := unitSteps_dist hD.2.2.1 (Nat.zero_le τ)
    simp only [hD.2.1, sub_zero] at hdist
    have hpos := (le_abs_self (D.inp τ)).trans hdist
    have hi0 : i = 0 := by
      by_contra hi0
      have hprod : d * b ≤ i * d * b := by
        have := Nat.mul_le_mul_right (d * b) (show 1 ≤ i by omega)
        nlinarith
      have hprodZ : ((d * b : ℕ) : ℤ) ≤ ((i * d * b : ℕ) : ℤ) := by
        exact_mod_cast hprod
      have hrZ : (r : ℤ) ≤ ((d * b : ℕ) : ℤ) := by exact_mod_cast hrdb
      have hτZ : (τ : ℤ) < r := by exact_mod_cast hτr
      omega
    simpa using hi0
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton 0)

/-- The initial block saves one attachment over the uniform two-per-block count. -/
theorem sum_card_rowsAt_le (hD : D.Valid (d * d * b)) (hrdb : r ≤ d * b) :
    (∑ a ∈ Finset.range (D.nodes r), (D.rowsAt d b r a).card) ≤ 2 * D.nodes r - 1 := by
  classical
  cases hN : D.nodes r with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    have htail : (∑ a ∈ Finset.range m, (D.rowsAt d b r (a + 1)).card) ≤ m * 2 := by
      calc _ ≤ ∑ _a ∈ Finset.range m, 2 :=
            Finset.sum_le_sum fun a _ => card_rowsAt_le hD hrdb (a + 1)
        _ = _ := by simp
    have hhead := card_rowsAt_zero_le_one hD hrdb
    omega

/-- A factor-two improvement, with a further first-block correction, capped by
the total number of bits. Neither radius nor block length needs positivity. -/
theorem card_attachedShortBits_le (hD : D.Valid (d * d * b))
    (hrdb : r ≤ d * b) :
    (attachedShortBits D d b r ℓ).card ≤
      min (d * d * b) ((2 * D.nodes r - 1) * b * (2 * k + 3) ^ (ℓ - 1)) := by
  classical
  apply le_min
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    refine (card_attachedShortBits_le_profile hD hrdb).trans ?_
    calc
      b * (∑ a ∈ Finset.range (D.nodes r),
          (D.rowsAt d b r a).card * (ball (D.edges r) (D.nodes r) a (ℓ - 1)).card) ≤
          b * (∑ a ∈ Finset.range (D.nodes r),
            (D.rowsAt d b r a).card * (2 * k + 3) ^ (ℓ - 1)) := by
        apply Nat.mul_le_mul_left
        exact Finset.sum_le_sum fun a _ =>
          Nat.mul_le_mul_left _ (card_ball_le hD hr a (ℓ - 1))
      _ ≤ b * ((2 * D.nodes r - 1) * (2 * k + 3) ^ (ℓ - 1)) := by
        rw [← Finset.sum_mul]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (sum_card_rowsAt_le hD hrdb))
      _ = _ := by ring

end SourceCovers

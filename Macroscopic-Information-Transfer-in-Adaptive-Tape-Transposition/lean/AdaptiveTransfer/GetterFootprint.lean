import AdaptiveTransfer.GetterGeometry
import AdaptiveTransfer.SlabGeometryAdapters

/-! Actual raw-window unions and their transposed stripe saving. Each
enlarged port interval is counted once for its run, with no bound on the
absolute public origin of the port.
-/

namespace AdaptiveTransfer.Getter
open Finset NativeRelations BoundedNesting MergeDepth Transpose
open scoped BigOperators

def intervalBits (P : ℕ) (lo hi : ℤ) : Finset (Fin P) :=
  univ.filter fun q => lo ≤ (q.val : ℤ) ∧ (q.val : ℤ) ≤ hi

/-- A spatial interval is the literal read set of a public unit-speed walk. -/
theorem intervalBits_eq_inCells (P : ℕ) (lo hi : ℤ) :
    intervalBits P lo hi = inCells P (fun t => lo + (t : ℤ)) (Ico 0 (hi + 1 - lo).toNat) := by
  ext q
  simp only [intervalBits, inCells, mem_filter, mem_univ, true_and, mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨(q.val - lo).toNat, ⟨Nat.zero_le _, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨t, ⟨_, ht⟩, he⟩
    omega

theorem intervalBits_row_bound {d b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) (lo hi : ℤ) :
    d * b * ((intervalBits (d * d * b) lo hi).image (slabRawRow hd hb)).card ≤
      (hi + 1 - lo).toNat + 2 * (d * b) := by
  by_cases hl : lo ≤ hi
  · have hn : 0 < (hi + 1 - lo).toNat := by omega
    have hx : IsWalk (fun t : ℕ => lo + (t : ℤ)) := by
      intro t
      simp only [Nat.cast_add, Nat.cast_one]
      ring_nf
      norm_num
    have hh := card_badRawRows_interval_le hd hb hx hn
    rw [← intervalBits_eq_inCells] at hh
    simp only [Nat.sub_zero] at hh
    have hm := Nat.mul_le_mul_left (d * b) hh
    have hdv := Nat.mul_div_le (hi + 1 - lo).toNat (d * b)
    nlinarith
  · have he : intervalBits (d * d * b) lo hi = ∅ := by
      ext q
      simp only [intervalBits, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      omega
    simp only [he, image_empty, card_empty, mul_zero]
    omega

/-- The length of an enlarged extremum interval is bounded by the actual
number of timestamps in that run plus its two radius margins. -/
theorem enlarged_run_length {x : ℕ → ℤ} (hx : IsWalk x) {C : Finset ℕ} {T R r : ℕ}
    (hCT : ∀ t ∈ C, t < T) (hr : r ∈ runStarts C) :
    (runRawHi x C T r + R + 1 - (runRawLo x C T r - R)).toNat ≤
      (Ico r (runEnd C T r)).card + 2 * R := by
  have he := runEnd_spec hCT hr
  have hne : ((Ico r (runEnd C T r)).image x).Nonempty :=
    ⟨x r, mem_image_of_mem _ (mem_Ico.mpr ⟨le_rfl, he.1⟩)⟩
  have hwalk := walk_image_Ico_eq_Icc hx he.1
  have hcard := card_image_le (f := x) (s := Ico r (runEnd C T r))
  rw [hwalk, Int.card_Icc] at hcard
  have hlohi := min'_le _ _ (max'_mem _ hne)
  simp only [runRawLo, runRawHi, dite_eq_left hne]
  omega

noncomputable def portBits {p : ℕ} (P : ℕ) (xs : Fin p → ℕ → ℤ)
    (C : Finset ℕ) (T R : ℕ) : Finset (Fin P) :=
  (runStarts C).biUnion fun r => univ.biUnion fun j =>
    intervalBits P (runRawLo (xs j) C T r - R) (runRawHi (xs j) C T r + R)

theorem mem_portBits_iff {p P T R : ℕ} {xs : Fin p → ℕ → ℤ} {C : Finset ℕ} {q : Fin P} :
    q ∈ portBits P xs C T R ↔
      (q.val : ℤ) ∈ portExtent C (fun r j => runRawLo (xs j) C T r)
        (fun r j => runRawHi (xs j) C T r) R := by
  simp only [portBits, mem_biUnion, mem_univ, true_and, intervalBits, mem_filter,
    portExtent, Set.mem_ofPred_eq]

/-- Before using a half-input budget, the exact p-port union pays
`p|C|+2pRr` length and at most two boundary rows per spatial interval. -/
theorem portBits_row_bound {d b p T R : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    {xs : Fin p → ℕ → ℤ} (hx : ∀ j, IsWalk (xs j))
    {C : Finset ℕ} (hCT : ∀ t ∈ C, t < T) :
    d * b * ((portBits (d * d * b) xs C T R).image (slabRawRow hd hb)).card ≤
      p * C.card + 2 * p * R * (runStarts C).card +
        2 * (d * b) * p * (runStarts C).card := by
  classical
  let bad (r : ℕ) (j : Fin p) :=
    (intervalBits (d * d * b) (runRawLo (xs j) C T r - R)
      (runRawHi (xs j) C T r + R)).image (slabRawRow hd hb)
  have hsub : (portBits (d * d * b) xs C T R).image (slabRawRow hd hb) ⊆
      (runStarts C).biUnion (fun r => univ.biUnion (bad r)) := by
    intro i hi
    obtain ⟨q, hq, hqi⟩ := mem_image.mp hi
    obtain ⟨r, hr, hq⟩ := mem_biUnion.mp hq
    obtain ⟨j, hj, hq⟩ := mem_biUnion.mp hq
    exact mem_biUnion.mpr ⟨r, hr, mem_biUnion.mpr ⟨j, hj, mem_image.mpr ⟨q, hq, hqi⟩⟩⟩
  have hcounts : C.card = ∑ r ∈ runStarts C, (Ico r (runEnd C T r)).card := by
    conv_lhs => rw [eq_biUnion_runInterval hCT]
    exact card_biUnion (pairwiseDisjoint_runInterval hCT)
  calc
    _ ≤ d * b * ∑ r ∈ runStarts C, ∑ j : Fin p, (bad r j).card := by
      apply Nat.mul_le_mul_left
      exact (card_le_card hsub).trans (card_biUnion_le.trans
        (sum_le_sum fun _ _ => card_biUnion_le))
    _ = ∑ r ∈ runStarts C, ∑ j : Fin p, d * b * (bad r j).card := by simp only [mul_sum]
    _ ≤ ∑ r ∈ runStarts C, ∑ _j : Fin p,
        ((Ico r (runEnd C T r)).card + 2 * R + 2 * (d * b)) := by
      refine sum_le_sum fun r hr => sum_le_sum fun j _ => ?_
      exact (intervalBits_row_bound hd hb _ _).trans
        (Nat.add_le_add_right (enlarged_run_length (hx j) hCT hr) _)
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_add,
        sum_add_distrib, ← mul_sum, ← hcounts]
      ring

/-- Single-row stripe coverage over the actual disjoint chronological runs. -/
theorem output_row_bound {d b T : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    {ot : Fin (d * d * b) → ℕ} (hot : StrictMono ot)
    {C : Finset ℕ} (hCT : ∀ t ∈ C, t < T) (i : Fin d) :
    (outIn ot C).card ≤
      d * (((outIn ot C).image (tposOf d b)).filter fun q => slabRawRow hd hb q = i).card +
        2 * (runStarts C).card * d * b := by
  classical
  let hit (r : ℕ) := (((outIn ot (Ico r (runEnd C T r))).image (tposOf d b)).filter
    fun q => slabRawRow hd hb q = i)
  have hC := eq_biUnion_runInterval hCT
  have hdisj := pairwiseDisjoint_runInterval hCT
  have hout : outIn ot C = (runStarts C).biUnion fun r => outIn ot (Ico r (runEnd C T r)) := by
    ext j
    simp only [outIn, mem_filter, mem_univ, true_and, mem_biUnion]
    conv_lhs => rw [hC]
    exact mem_biUnion
  have hdout : (runStarts C : Set ℕ).PairwiseDisjoint (fun r => outIn ot (Ico r (runEnd C T r))) := by
    intro r hr s hs hne
    exact disjoint_left.mpr fun j hj hj' =>
      disjoint_left.mp (hdisj hr hs hne) (mem_filter.mp hj).2 (mem_filter.mp hj').2
  have hinj : Function.Injective (tposOf d b) := Function.Involutive.injective (tposOf_tposOf d b)
  have hdhit : (runStarts C : Set ℕ).PairwiseDisjoint hit := by
    intro r hr s hs hne
    apply disjoint_left.mpr
    intro q hq hq'
    obtain ⟨j, hj, he⟩ := mem_image.mp (mem_filter.mp hq).1
    obtain ⟨j', hj', he'⟩ := mem_image.mp (mem_filter.mp hq').1
    have hjj := hinj (he.trans he'.symm)
    exact disjoint_left.mp (hdout hr hs hne) hj (hjj ▸ hj')
  have hsub : (runStarts C).biUnion hit ⊆
      ((outIn ot C).image (tposOf d b)).filter fun q => slabRawRow hd hb q = i := by
    intro q hq
    obtain ⟨r, hr, hq⟩ := mem_biUnion.mp hq
    obtain ⟨hj, hi⟩ := mem_filter.mp hq
    obtain ⟨j, hj, he⟩ := mem_image.mp hj
    refine mem_filter.mpr ⟨mem_image.mpr ⟨j, ?_, he⟩, hi⟩
    rw [hout]
    exact mem_biUnion.mpr ⟨r, hr, hj⟩
  have hsum : (∑ r ∈ runStarts C, (hit r).card) ≤
      (((outIn ot C).image (tposOf d b)).filter fun q => slabRawRow hd hb q = i).card := by
    rw [← card_biUnion hdhit]
    exact card_le_card hsub
  calc
    _ = ∑ r ∈ runStarts C, (outIn ot (Ico r (runEnd C T r))).card := by
      rw [hout, card_biUnion hdout]
    _ ≤ ∑ r ∈ runStarts C, (d * (hit r).card + 2 * d * b) :=
      sum_le_sum fun r _ => outIn_interval_le_d_mul_rowHits hd hb hot r _ i
    _ = d * (∑ r ∈ runStarts C, (hit r).card) + 2 * (runStarts C).card * d * b := by
      rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul]
      ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left d hsum) _

noncomputable def omittedPortBits {p d b : ℕ} (xs : Fin p → ℕ → ℤ)
    (ot : Fin (d * d * b) → ℕ) (C : Finset ℕ) (T R : ℕ) : Finset (Fin (d * d * b)) :=
  (outIn ot C).image (tposOf d b) \ portBits (d * d * b) xs C T R

/-- Multiport stripe saving. The two elementary budget premises concern
actual interval length and actual retained timestamps; the final selection
theorem below discharges them from its declared radius and run cap. -/
theorem port_discrepancy {d b p T R : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b)
    {xs : Fin p → ℕ → ℤ} (hx : ∀ j, IsWalk (xs j))
    {ot : Fin (d * d * b) → ℕ} (hot : StrictMono ot)
    {C : Finset ℕ} (hCT : ∀ t ∈ C, t < T)
    (hlen : 2 * (p * C.card + 2 * p * R * (runStarts C).card) ≤ d * d * b)
    (hcap : 4 * p * C.card ≤ d * d * b) :
    (outIn ot C).card ≤ 2 * (omittedPortBits xs ot C T R).card +
      6 * (runStarts C).card * d * b := by
  classical
  let bad := (portBits (d * d * b) xs C T R).image (slabRawRow hd hb)
  let free := (univ : Finset (Fin d)) \ bad
  let hit (i : Fin d) := ((outIn ot C).image (tposOf d b)).filter fun q => slabRawRow hd hb q = i
  let r := (runStarts C).card
  let O := (outIn ot C).card
  have hbad : 2 * bad.card ≤ d + 4 * p * r := by
    have hh := portBits_row_bound hd hb hx hCT (R := R)
    have hh' : (d * b) * (2 * bad.card) ≤ (d * b) * (d + 4 * p * r) := by
      dsimp only [bad, r] at *
      nlinarith
    exact Nat.le_of_mul_le_mul_left hh' (Nat.mul_pos hd hb)
  have hpart : free.card + bad.card = d := by
    simpa only [free, univ_inter, card_fin] using card_sdiff_add_card_inter univ bad
  have hfree : d ≤ 2 * free.card + 4 * p * r := by omega
  have hfree_le : free.card ≤ d := by simpa only [Fintype.card_fin] using card_le_univ free
  have hdisj : (free : Set (Fin d)).PairwiseDisjoint hit := by
    intro i _ j _ hij
    exact disjoint_left.mpr fun q hq hq' => hij ((mem_filter.mp hq).2.symm.trans (mem_filter.mp hq').2)
  have hsub : free.biUnion hit ⊆ omittedPortBits xs ot C T R := by
    intro q hq
    obtain ⟨i, hi, hq⟩ := mem_biUnion.mp hq
    refine mem_sdiff.mpr ⟨(mem_filter.mp hq).1, fun hb' => ?_⟩
    exact (mem_sdiff.mp hi).2 ((mem_filter.mp hq).2 ▸ mem_image_of_mem _ hb')
  have hsum : (∑ i ∈ free, (hit i).card) ≤ (omittedPortBits xs ot C T R).card := by
    rw [← card_biUnion hdisj]
    exact card_le_card hsub
  have hcover : free.card * O ≤ d * (omittedPortBits xs ot C T R).card + 2 * r * d * b * free.card := by
    calc
      free.card * O = ∑ _i ∈ free, O := by simp
      _ ≤ ∑ i ∈ free, (d * (hit i).card + 2 * r * d * b) :=
        sum_le_sum fun i _ => output_row_bound hd hb hot hCT i
      _ = d * (∑ i ∈ free, (hit i).card) + 2 * r * d * b * free.card := by
        rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul]; ring
      _ ≤ _ := by gcongr
  have hO : O ≤ C.card := by
    exact card_le_card_of_injOn ot
      (fun _ hj => (mem_filter.mp hj).2)
      (fun _ _ _ _ he => hot.injective he)
  have hsmall : 4 * p * O ≤ d * d * b := (Nat.mul_le_mul_left (4 * p) hO).trans hcap
  have hmul : d * O ≤ d * (2 * (omittedPortBits xs ot C T R).card + 6 * r * d * b) := by
    have h₁ := Nat.mul_le_mul_right O hfree
    have h₂ := Nat.mul_le_mul_left (2 * r * d * b) hfree_le
    have h₃ := Nat.mul_le_mul_left r hsmall
    nlinarith only [h₁, hcover, h₂, h₃, Nat.zero_le (r * d * d * b)]
  exact Nat.le_of_mul_le_mul_left hmul hd

end AdaptiveTransfer.Getter

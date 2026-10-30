import BoundedNesting.OwnerLoad

/-!
# Skeleton walks

The *skeleton walk* of a walk `x` at scale `w ≥ 1` is `t ↦ ⌊x t / w⌋`: the block of `w` cells that
contains the head. It is again a walk (`isWalk_skel`).

`entries_skel_subset`: an entry of a block by the skeleton walk is an entry of one of the two end
cells of the block by the walk, if the walk starts at cell `0`. So if the walk enters every cell at
most `ℓ` times, its skeleton walk enters every block at most `2ℓ` times (`card_entries_skel_le`).
-/

namespace MergeDepth

open Finset BoundedNesting

/-- The skeleton walk of `x` at scale `w`: the index of the block of `w` cells containing `x t`. -/
def skel (w : ℤ) (x : ℕ → ℤ) : ℕ → ℤ := fun t => x t / w

/-- The block of `a` brackets `a`: `w ⌊a/w⌋ ≤ a < w ⌊a/w⌋ + w`. -/
theorem block_bounds {w : ℤ} (hw : 0 < w) (a : ℤ) : w * (a / w) ≤ a ∧ a < w * (a / w) + w := by
  have h := Int.mul_ediv_add_emod a w
  have h0 := Int.emod_nonneg a hw.ne'
  have h1 := Int.emod_lt_of_pos a hw
  constructor <;> linarith

theorem block_gap {w : ℤ} (hw : 0 < w) {q q' : ℤ} (h : q < q') : w * q + w ≤ w * q' := by
  have : w * (q + 1) ≤ w * q' := mul_le_mul_of_nonneg_left (by omega) hw.le
  linarith

/-- One step of a walk moves its block by at most one. -/
theorem skel_step {w : ℤ} (hw : 0 < w) {a b : ℤ} (h : |b - a| ≤ 1) :
    |b / w - a / w| ≤ 1 := by
  have h1 := abs_le.mp h
  obtain ⟨ha0, ha1⟩ := block_bounds hw a
  obtain ⟨hb0, hb1⟩ := block_bounds hw b
  rw [abs_le]
  constructor
  · by_contra hc
    have := block_gap hw (show b / w + 1 < a / w by omega)
    linarith
  · by_contra hc
    have := block_gap hw (show a / w + 1 < b / w by omega)
    linarith

/-- The skeleton walk of a walk is a walk. -/
theorem isWalk_skel {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) : IsWalk (skel w x) :=
  fun t => skel_step hw (hx t)

/-- When the block changes in one step, the walk moves to an end cell of the new block, which it
did not occupy before. -/
theorem end_cell_of_block_change {w : ℤ} (hw : 0 < w) {a b : ℤ} (h : |b - a| ≤ 1)
    (hne : a / w ≠ b / w) : (b = w * (b / w) ∨ b = w * (b / w) + w - 1) ∧ a ≠ b := by
  have h1 := abs_le.mp h
  obtain ⟨ha0, ha1⟩ := block_bounds hw a
  obtain ⟨hb0, hb1⟩ := block_bounds hw b
  refine ⟨?_, fun hab => hne (by rw [hab])⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := block_gap hw hlt
    left
    linarith
  · have := block_gap hw hgt
    right
    linarith

/-- **Entries of the skeleton walk.** If the walk starts at cell `0`, every entry of block `b` by
its skeleton walk is an entry of one of the end cells `w b` and `w b + w - 1` by the walk. -/
theorem entries_skel_subset {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) (h0 : x 0 = 0)
    (b : ℤ) (T : ℕ) :
    entries (skel w x) b T ⊆ entries x (w * b) T ∪ entries x (w * b + w - 1) T := by
  intro t ht
  obtain ⟨htT, hb, ht0⟩ := mem_filter.mp ht
  simp only [skel] at hb ht0
  rcases ht0 with rfl | hne
  · -- time `0`: the walk is at cell `0 = w ⋅ 0`
    have : b = 0 := by rw [← hb, h0, Int.zero_ediv]
    subst this
    exact mem_union_left _ (mem_filter.mpr ⟨htT, by simp [h0], Or.inl rfl⟩)
  · have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exact absurd hb (by simpa using hne)
      · exact h
    have hstep : |x t - x (t - 1)| ≤ 1 := by
      have := hx (t - 1)
      rwa [Nat.sub_add_cancel ht1] at this
    obtain ⟨hend, hmove⟩ := end_cell_of_block_change hw hstep (by rw [hb]; exact hne)
    rw [hb] at hend
    rcases hend with he | he
    · exact mem_union_left _ (mem_filter.mpr ⟨htT, he, Or.inr (fun h => hmove (h.trans he.symm))⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨htT, he, Or.inr (fun h => hmove (h.trans he.symm))⟩)

/-- **Bounded entry passes to skeleton walks.** If a walk starting at cell `0` enters every cell at
most `ℓ` times, its skeleton walk enters every block at most `2ℓ` times. -/
theorem card_entries_skel_le {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) (h0 : x 0 = 0)
    {ℓ T : ℕ} (hℓ : ∀ c, (entries x c T).card ≤ ℓ) (b : ℤ) :
    (entries (skel w x) b T).card ≤ 2 * ℓ :=
  calc (entries (skel w x) b T).card
      ≤ (entries x (w * b) T ∪ entries x (w * b + w - 1) T).card :=
        card_le_card (entries_skel_subset hw hx h0 b T)
    _ ≤ (entries x (w * b) T).card + (entries x (w * b + w - 1) T).card := card_union_le _ _
    _ ≤ 2 * ℓ := by have := hℓ (w * b); have := hℓ (w * b + w - 1); omega

/-- A walk moves by at most one cell per step: `|x (a + n) - x a| ≤ n`. -/
theorem walk_lip {x : ℕ → ℤ} (hx : IsWalk x) (a : ℕ) : ∀ n : ℕ, |x (a + n) - x a| ≤ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hx (a + n)
    have h2 : x (a + (n + 1)) - x a = (x (a + n + 1) - x (a + n)) + (x (a + n) - x a) := by
      rw [← add_assoc]; ring
    rw [h2]
    push_cast
    exact (abs_add_le _ _).trans (by linarith)

/-- Two positions of a walk differ by at most the time between them. -/
theorem walk_le {x : ℕ → ℤ} (hx : IsWalk x) (t t' : ℕ) : x t' ≤ x t + |(t' : ℤ) - t| := by
  rcases le_total t t' with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    have := abs_le.mp (walk_lip hx t n)
    have : |((t + n : ℕ) : ℤ) - t| = n := by push_cast; simp
    linarith
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    have := abs_le.mp (walk_lip hx t' n)
    have : |((t' : ℕ) : ℤ) - ((t' + n : ℕ) : ℤ)| = n := by push_cast; simp
    linarith

/-- **Lemma 4.2(c): few block changes.** A walk of length `T` that starts at `0` and enters every
cell at most `V` times changes blocks of width `w` at most `2V((T - 1)/w + 2) - 1` times. -/
theorem card_block_changes_le {w : ℕ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) (h0 : x 0 = 0)
    {V T : ℕ} (hT : 1 ≤ T) (hV : ∀ c, (entries x c (T - 1)).card ≤ V) :
    ((Ico 1 T).filter fun t => skel w x t ≠ skel w x (t - 1)).card ≤
      2 * V * ((T - 1) / w + 2) - 1 := by
  classical
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  set s := skel (w : ℤ) x with hs
  -- the blocks met
  set B := (range T).image s
  have h0B : (0 : ℤ) ∈ B := mem_image.mpr ⟨0, mem_range.mpr hT, by simp [hs, skel, h0]⟩
  -- every change is an entry of a met block, other than time `0`
  have hsub : ((Ico 1 T).filter fun t => s t ≠ s (t - 1)) ⊆
      B.biUnion fun b => (entries s b (T - 1)).erase 0 := by
    intro t ht
    obtain ⟨ht1, hne⟩ := mem_filter.mp ht
    obtain ⟨h1, h2⟩ := mem_Ico.mp ht1
    refine mem_biUnion.mpr ⟨s t, mem_image.mpr ⟨t, mem_range.mpr h2, rfl⟩, ?_⟩
    refine mem_erase.mpr ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by omega), rfl, Or.inr ?_⟩⟩
    exact fun h => hne h.symm
  -- each block has at most `2V` entries, and block `0` has the entry at time `0`
  have hblock : ∀ b, (entries s b (T - 1)).card ≤ 2 * V :=
    card_entries_skel_le hw' hx h0 hV
  have hcount : ∑ b ∈ B, ((entries s b (T - 1)).erase 0).card + 1 ≤ 2 * V * B.card := by
    rw [← sum_erase_add _ _ h0B]
    have h00 : 0 ∈ entries s 0 (T - 1) :=
      mem_filter.mpr ⟨by simp, by simp [hs, skel, h0], Or.inl rfl⟩
    have e0 : ((entries s 0 (T - 1)).erase 0).card + 1 = (entries s 0 (T - 1)).card :=
      card_erase_add_one h00
    have hrest : ∑ b ∈ B.erase 0, ((entries s b (T - 1)).erase 0).card ≤ ∑ _b ∈ B.erase 0, 2 * V :=
      sum_le_sum fun b _ => (card_erase_le).trans (hblock b)
    rw [sum_const, smul_eq_mul, card_erase_of_mem h0B] at hrest
    have hB : 1 ≤ B.card := card_pos.mpr ⟨0, h0B⟩
    have := hblock 0
    calc ∑ b ∈ B.erase 0, ((entries s b (T - 1)).erase 0).card +
          ((entries s 0 (T - 1)).erase 0).card + 1
        ≤ (B.card - 1) * (2 * V) + 2 * V := by omega
      _ = 2 * V * B.card := by
          obtain ⟨n, hn⟩ : ∃ n, B.card = n + 1 := ⟨B.card - 1, by omega⟩
          rw [hn]; simp; ring
  -- the met blocks lie in an interval of at most `(T - 1)/w + 2` blocks
  have hBcard : B.card ≤ (T - 1) / w + 2 := by
    obtain ⟨t₀, ht₀, hmin⟩ := exists_min_image (range T) x ⟨0, mem_range.mpr hT⟩
    set a := x t₀
    have hrange : ∀ t ∈ range T, a ≤ x t ∧ x t ≤ a + ((T - 1 : ℕ) : ℤ) := by
      intro t ht
      refine ⟨hmin t ht, ?_⟩
      have := walk_le hx t₀ t
      have hlt := mem_range.mp ht
      have hlt0 := mem_range.mp ht₀
      have : |(t : ℤ) - t₀| ≤ ((T - 1 : ℕ) : ℤ) := by
        rw [abs_le]; push_cast [Nat.cast_sub hT]; constructor <;> omega
      linarith
    have hBsub : B ⊆ Icc (a / w) ((a + ((T - 1 : ℕ) : ℤ)) / w) := by
      intro b hb
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hb
      obtain ⟨h1, h2⟩ := hrange t ht
      exact mem_Icc.mpr ⟨Int.ediv_le_ediv hw' h1, Int.ediv_le_ediv hw' h2⟩
    refine (card_le_card hBsub).trans ?_
    rw [Int.card_Icc, Int.toNat_le]
    -- `(a + N)/w ≤ a/w + N/w + 1`
    obtain ⟨ha0, ha1⟩ := block_bounds hw' a
    obtain ⟨hb0, hb1⟩ := block_bounds hw' (a + ((T - 1 : ℕ) : ℤ))
    obtain ⟨hn0, hn1⟩ := block_bounds hw' ((T - 1 : ℕ) : ℤ)
    have hdiv : (a + ((T - 1 : ℕ) : ℤ)) / w ≤ a / w + ((T - 1 : ℕ) : ℤ) / w + 1 := by
      by_contra hc
      push Not at hc
      have := block_gap hw' (show a / w + ((T - 1 : ℕ) : ℤ) / w + 1 < (a + ((T - 1 : ℕ) : ℤ)) / w by
        omega)
      nlinarith
    rw [Nat.cast_add, Int.natCast_div]
    push_cast
    linarith
  calc ((Ico 1 T).filter fun t => s t ≠ s (t - 1)).card
      ≤ (B.biUnion fun b => (entries s b (T - 1)).erase 0).card := card_le_card hsub
    _ ≤ ∑ b ∈ B, ((entries s b (T - 1)).erase 0).card := card_biUnion_le
    _ ≤ 2 * V * B.card - 1 := by omega
    _ ≤ 2 * V * ((T - 1) / w + 2) - 1 := by
        have := Nat.mul_le_mul_left (2 * V) hBcard
        omega

end MergeDepth

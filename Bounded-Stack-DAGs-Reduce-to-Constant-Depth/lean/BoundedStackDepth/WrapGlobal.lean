import BoundedStackDepth.Global
import BoundedStackDepth.Wrap
import BoundedStackDepth.Accounting

/-!
# WRAP for the composed label

* `card_wrap_le_sum`: for one hop, the digit offsets that wrap a digit of a group in `B` number at most
  `K^{P−1}` times the sum over `B` of the counter increases (one union bound, `card_wrap_offsets_le`).
* `turnCount_sub`, `segEventCount_sub`: a counter increase from `p` to `u` counts the events in `(p, u]`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

/-- **Wraps of one hop.** The offset vectors wrapping the digit of some group of `B ⊆ O` number at most
`Σ_{g ∈ B} (c' g − c g) K^{P−1}`. -/
theorem card_wrap_le_sum {K P : ℕ} (hK : 0 < K) (O B : Finset ℕ) (c c' : ℕ → ℕ)
    (hcc : ∀ g ∈ B, c g ≤ c' g) :
    ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
      ∃ g ∈ B, ∃ i : Fin P, topRank O g = i ∧ (c g + ω i) / K ≠ (c' g + ω i) / K).card ≤
      ∑ g ∈ B, (c' g - c g) * K ^ (P - 1) := by
  classical
  calc _ ≤ (B.biUnion fun g => (Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
          ∃ i : Fin P, topRank O g = i ∧ (c g + ω i) / K ≠ (c' g + ω i) / K).card := by
        refine card_le_card fun ω hω => ?_
        obtain ⟨hmem, g, hg, i, hi, hw⟩ := mem_filter.mp hω
        exact mem_biUnion.mpr ⟨g, hg, mem_filter.mpr ⟨hmem, i, hi, hw⟩⟩
    _ ≤ ∑ g ∈ B, ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
          ∃ i : Fin P, topRank O g = i ∧ (c g + ω i) / K ≠ (c' g + ω i) / K).card := card_biUnion_le
    _ ≤ ∑ g ∈ B, (c' g - c g) * K ^ (P - 1) := sum_le_sum fun g hg => by
        by_cases hP : topRank O g < P
        · have : ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
              ∃ i : Fin P, topRank O g = i ∧ (c g + ω i) / K ≠ (c' g + ω i) / K) =
              (Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
                (c g + ω ⟨topRank O g, hP⟩) / K ≠ (c' g + ω ⟨topRank O g, hP⟩) / K := by
            refine filter_congr fun ω _ => ⟨fun ⟨i, hi, hw⟩ => ?_, fun hw => ⟨_, rfl, hw⟩⟩
            have : i = ⟨topRank O g, hP⟩ := Fin.ext hi.symm
            subst this
            exact hw
          rw [this]
          exact card_wrap_offsets_le hK _ (hcc g hg)
        · have : ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
              ∃ i : Fin P, topRank O g = i ∧ (c g + ω i) / K ≠ (c' g + ω i) / K) = ∅ :=
            filter_eq_empty_iff.mpr fun ω _ ⟨i, hi, _⟩ => hP (hi ▸ i.isLt)
          rw [this, card_empty]
          exact Nat.zero_le _

variable {S : FrameSystem}

/-- The turning points of a frame system's walk. -/
noncomputable def turnsOf (S : FrameSystem) : Finset ℕ := (range S.T).filter fun s => 1 ≤ prom S.x S.T s

/-- A turning-point counter increase counts the turning points in `(p, u]`. -/
theorem turnCount_sub {θ p u : ℕ} (hpu : p ≤ u) :
    turnCount S θ u - turnCount S θ p =
      ((turnsOf S).filter fun s => p < s ∧ s ≤ u ∧ θ ≤ band (prom S.x S.T s)).card := by
  classical
  have hsplit : (range S.T).filter (fun s => s ≤ u ∧ 1 ≤ prom S.x S.T s ∧ θ ≤ band (prom S.x S.T s)) =
      (range S.T).filter (fun s => s ≤ p ∧ 1 ≤ prom S.x S.T s ∧ θ ≤ band (prom S.x S.T s)) ∪
        (turnsOf S).filter fun s => p < s ∧ s ≤ u ∧ θ ≤ band (prom S.x S.T s) := by
    ext s
    simp only [turnsOf, mem_union, mem_filter]
    constructor
    · rintro ⟨hs, h1, h2, h3⟩
      by_cases hsp : s ≤ p
      · exact Or.inl ⟨hs, hsp, h2, h3⟩
      · exact Or.inr ⟨⟨hs, h2⟩, by omega, h1, h3⟩
    · rintro (⟨hs, h1, h2, h3⟩ | ⟨⟨hs, h2⟩, h0, h1, h3⟩)
      · exact ⟨hs, h1.trans hpu, h2, h3⟩
      · exact ⟨hs, h1, h2, h3⟩
  have hdisj : Disjoint ((range S.T).filter
      (fun s => s ≤ p ∧ 1 ≤ prom S.x S.T s ∧ θ ≤ band (prom S.x S.T s)))
      ((turnsOf S).filter fun s => p < s ∧ s ≤ u ∧ θ ≤ band (prom S.x S.T s)) := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    have := (mem_filter.mp h1).2.1
    have := (mem_filter.mp h2).2.1
    omega
  unfold turnCount
  rw [hsplit, card_union_of_disjoint hdisj]
  omega

/-- A segment-start counter increase counts the segment starts in `(p, u]`. -/
theorem segEventCount_sub {θ p u : ℕ} (hpu : p ≤ u) :
    segEventCount S θ u - segEventCount S θ p =
      ((segStarts S).filter fun Fs => p < Fs.2 ∧ Fs.2 ≤ u ∧ θ ≤ segScale S Fs.1 Fs.2).card := by
  classical
  have hsplit : (segStarts S).filter (fun Fs => Fs.2 ≤ u ∧ θ ≤ segScale S Fs.1 Fs.2) =
      (segStarts S).filter (fun Fs => Fs.2 ≤ p ∧ θ ≤ segScale S Fs.1 Fs.2) ∪
        (segStarts S).filter fun Fs => p < Fs.2 ∧ Fs.2 ≤ u ∧ θ ≤ segScale S Fs.1 Fs.2 := by
    ext Fs
    simp only [mem_union, mem_filter]
    constructor
    · rintro ⟨hs, h1, h3⟩
      by_cases hsp : Fs.2 ≤ p
      · exact Or.inl ⟨hs, hsp, h3⟩
      · exact Or.inr ⟨hs, by omega, h1, h3⟩
    · rintro (⟨hs, h1, h3⟩ | ⟨hs, h0, h1, h3⟩)
      · exact ⟨hs, h1.trans hpu, h3⟩
      · exact ⟨hs, h1, h3⟩
  have hdisj : Disjoint ((segStarts S).filter (fun Fs => Fs.2 ≤ p ∧ θ ≤ segScale S Fs.1 Fs.2))
      ((segStarts S).filter fun Fs => p < Fs.2 ∧ Fs.2 ≤ u ∧ θ ≤ segScale S Fs.1 Fs.2) :=
    disjoint_filter.mpr fun Fs _ h1 h2 => by omega
  unfold segEventCount
  rw [hsplit, card_union_of_disjoint hdisj]
  omega

theorem flr_mono {h₀ r a b : ℕ} (h : a ≤ b) : flr h₀ r a ≤ flr h₀ r b :=
  Nat.sub_le_sub_right (Nat.mul_le_mul_left _ h) _

open Classical in
/-- **The counting fact for kept hops.** At most `10 · 2^{θ(g+1)}` upper hops that are not lost at offset
`r`, with deciding group at most `g`, span a time `c`. -/
theorem card_kept_spanning_le (hx : IsWalk S.x) {h₀ r : ℕ} (hr : r < h₀) (c g : ℕ) :
    ((upperHops S.x S.T).filter fun e => ¬ Lost S h₀ r e ∧ e.1 < c ∧ c ≤ e.2 ∧
      decGroup S h₀ r e ≤ g).card ≤ 10 * 2 ^ flr h₀ r (g + 1) := by
  have hal := card_aligned_spanning_lt S h₀ r c (flr h₀ r (g + 1))
  have hgr := card_ground_spanning_lt S hx (r := r) (by omega) c (flr h₀ r (g + 1)) (flr_mono (by omega))
  calc _ ≤ ((hops S.x S.T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧
          Aligned h₀ r (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e) (pushMax S e)
            (FrameMicro S e) ∧ flr h₀ r (grp h₀ r (bandU S e) + 1) ≤ flr h₀ r (g + 1)) ∪
        (upperHops S.x S.T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧
          Ground h₀ r (ownerScale S e))).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨heU, hnl, h1, h2, hd⟩ := mem_filter.mp he
        by_cases hA : Aligned h₀ r (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e)
            (pushMax S e) (FrameMicro S e)
        · refine mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp heU).1, h1, h2, hA, flr_mono ?_⟩)
          unfold decGroup at hd
          simp only [hA, ↓reduceIte] at hd
          omega
        · have hG : Ground h₀ r (ownerScale S e) := by
            unfold Lost at hnl
            push Not at hnl
            exact hnl hA
          exact mem_union_right _ (mem_filter.mpr ⟨heU, h1, h2, hG⟩)
    _ ≤ _ := card_union_le _ _
    _ ≤ 10 * 2 ^ flr h₀ r (g + 1) := by
        have : 2 * 2 ^ (flr h₀ r (g + 1) + 2) = 8 * 2 ^ flr h₀ r (g + 1) := by ring
        omega

/-- The geometric sum of the floors above the groups reached by a scale. -/
theorem sum_ten_two_pow_flr_le {h₀ r : ℕ} (hr : r < h₀) (s : ℕ) :
    ∑ g ∈ range (grp h₀ r s + 1), 10 * 2 ^ flr h₀ r (g + 1) ≤ 20 * 2 ^ h₀ * 2 ^ s := by
  have hh : 0 < h₀ := by omega
  rw [← mul_sum]
  have h1 := sum_two_pow_flr_succ_le hr (grp h₀ r s)
  have h2 := flr_grp_succ_le (h₀ := h₀) r s
  have key : ∑ g ∈ range (grp h₀ r s + 1), 2 ^ flr h₀ r (g + 1) ≤ 2 * (2 ^ h₀ * 2 ^ s) :=
    calc _ ≤ 2 ^ (flr h₀ r (grp h₀ r s + 1) + 1) := h1.le
      _ ≤ 2 ^ (s + h₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * (2 ^ h₀ * 2 ^ s) := by ring
  calc 10 * ∑ g ∈ range (grp h₀ r s + 1), 2 ^ flr h₀ r (g + 1) ≤ 10 * (2 * (2 ^ h₀ * 2 ^ s)) :=
        Nat.mul_le_mul_left _ key
    _ = 20 * 2 ^ h₀ * 2 ^ s := by ring

open Classical in
/-- **WRAP, one event family.** For the hops of a frame system that are not lost at offset `r`, each
summing over a set of groups at least its deciding group, the events of one family in the hop with scale
`≥ θ(g)` total at most `Σ_a 20 · 2^{σ a + h₀}`. -/
theorem sum_kept_family_le (hx : IsWalk S.x) {h₀ r : ℕ} (hr : r < h₀) {α : Type*} (A : Finset α)
    (τ σ : α → ℕ) (B : ℕ × ℕ → Finset ℕ) (hB : ∀ e, ∀ g ∈ B e, decGroup S h₀ r e ≤ g) :
    ∑ e ∈ (upperHops S.x S.T).filter (fun e => ¬ Lost S h₀ r e), ∑ g ∈ B e,
        (A.filter fun a => e.1 < τ a ∧ τ a ≤ e.2 ∧ flr h₀ r g ≤ σ a).card ≤
      ∑ a ∈ A, 20 * 2 ^ h₀ * 2 ^ σ a := by
  have hh : 0 < h₀ := by omega
  set H := (upperHops S.x S.T).filter (fun e => ¬ Lost S h₀ r e) with hH
  have step1 := sum_hops_events_le A τ σ H (fun e => e.1) (fun e => e.2) (decGroup S h₀ r) B
    (flr h₀ r) (grp h₀ r) hB fun g s h => (flr_le_iff hh r g s).mp h
  have step2 : ∀ a ∈ A, ∀ g ∈ range (grp h₀ r (σ a) + 1),
      (H.filter fun e => e.1 < τ a ∧ τ a ≤ e.2 ∧ decGroup S h₀ r e ≤ g).card ≤
        10 * 2 ^ flr h₀ r (g + 1) := fun a _ g _ => by
    refine (card_le_card fun e he => ?_).trans (card_kept_spanning_le hx hr (τ a) g)
    obtain ⟨heH, h⟩ := mem_filter.mp he
    obtain ⟨heU, hnl⟩ := mem_filter.mp heH
    exact mem_filter.mpr ⟨heU, hnl, h⟩
  calc _ ≤ _ := step1
    _ ≤ ∑ a ∈ A, ∑ g ∈ range (grp h₀ r (σ a) + 1), 10 * 2 ^ flr h₀ r (g + 1) :=
        sum_le_sum fun a ha => sum_le_sum fun g hg => step2 a ha g hg
    _ ≤ ∑ a ∈ A, 20 * 2 ^ h₀ * 2 ^ σ a := sum_le_sum fun a _ => sum_ten_two_pow_flr_le hr _

end BoundedStackDepth

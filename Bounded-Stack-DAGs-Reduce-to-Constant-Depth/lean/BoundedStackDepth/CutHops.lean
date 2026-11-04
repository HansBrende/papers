import BoundedStackDepth.Truncation
import BoundedStackDepth.Exposure
import BoundedStackDepth.EventWeight
import BoundedStackDepth.LadderBands

/-!
# The violated hops of the label

Fix a head `v` with frame system `S v = headFrames v`, its upper hops `H_v`, an offset `r < h₀`, digit
offsets `ω` and bits `ξ`. Write `d e = decGroup (S v) r e` for the deciding group of a hop, `O` for the
shown sets and `cnt g t` for the global counter of group `g`. An *event* at `r` is a pair `(w, (t, g))`
with `(t, g)` a rise or a last-stint end of a head `w` (`rises`, `lastStints`).

**Decomposition** (`card_violated_le_cut`). A violated upper hop of `v` is
* lost (`lostSet`: neither aligned nor ground), or
* truncated (`truncSet`: `d` has rank at least `P` at `p`), or
* *charged* (`chargedSet`): an event lies in `(p, u]` at a group `≥ d + 1` (`Charged`), or
* exposed (`exposedSet`): not charged, and the shown sets above `d` differ at `p` and `u`, or
* WRAP (`wrapSet`): a digit of a shown group `g ≥ d` wraps,

by the cut classification `trunc_or_above_or_wrap_head`.

* **Charged** (`card_chargedSet_le`): every charged hop spans the time of an event `(w, (t, g))` with
  `d + 1 ≤ g`; per event, the counting fact `card_kept_spanning_le` (group `g − 1`) bounds the hops by
  `10 · 2^{θ(g)}`.
* **Exposed hops** (`sum_card_exposedSet_le`): without an event in `(p, u]` above `d`, every head's view above `d`
  is the same at `p` and `u` (`views_eq_of_no_event`: `view_interval` with Lemma W2,
  `popsAtZero_headFrames`). An aligned hop has `d` as a seed at both ends, and exposure
  (`card_exposed_le`) bounds the bit vectors by `2n Q^{|ι|−1}`; a non-aligned hop has `d = 0`, every
  candidate at `0` is displayed (`Disp.zero`), and the shown sets above `0` agree (`shown_above_eq`).
* **WRAP** (`sum_card_wrapSet_le`): per hop, `card_wrap_le_sum` with the shown groups `≥ d`; a counter
  increase is at most the sum over heads of the turning points and segment starts in `(p, u]`
  (`globalCount_sub_le_events`, from `turnCount_sub` and `segEventCount_sub`), and
  `sum_kept_family_le` sums each family over the hops.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

/-- **Double counting.** Summing the sizes of subsets of `H` is summing, over `H`, the number of
indices whose subset contains the element. -/
theorem sum_card_eq_sum_card_filter {α β : Type*} [DecidableEq β] (A : Finset α) (H : Finset β)
    (s : α → Finset β) (hs : ∀ a ∈ A, s a ⊆ H) :
    ∑ a ∈ A, (s a).card = ∑ b ∈ H, (A.filter fun a => b ∈ s a).card := by
  calc ∑ a ∈ A, (s a).card = ∑ a ∈ A, ∑ b ∈ H, if b ∈ s a then 1 else 0 :=
        sum_congr rfl fun a ha => card_eq_sum_ite (hs a ha)
    _ = ∑ b ∈ H, ∑ a ∈ A, if b ∈ s a then 1 else 0 := sum_comm
    _ = ∑ b ∈ H, (A.filter fun a => b ∈ s a).card :=
        sum_congr rfl fun b _ => (card_filter _ _).symm

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} (T : ℕ) (hx : ∀ i, IsWalk (xs i))

/-- **Lemma W2 for the heads.** Every nonempty non-root frame of a head ends at band `0`. -/
theorem popsAtZero_headFrames (v : Fin (k * 2)) : (headFrames T hx v).PopsAtZero := by
  intro F hF hne hlt
  have hF' : F ∈ insert (0, T) (suspendFrames (headWalk xs v) T) := hF
  rcases mem_insert.mp hF' with h | h
  · exact absurd h hne
  · exact beta_last_eq_zero (isWalk_headWalk hx v) h hlt

variable (h₀ : ℕ) {Q : ℕ} [NeZero Q]

/-- A hop `e` of head `v` is *charged* at offset `r`: an event of some head (a rise or a last-stint end)
lies in `(p, u]` at a group `≥ d + 1`. -/
def Charged (v : Fin (k * 2)) (r : ℕ) (e : ℕ × ℕ) : Prop :=
  ∃ w, ∃ tg ∈ rises (headFrames T hx w) h₀ r T ∪ lastStints (headFrames T hx w) h₀ r T,
    e.1 < tg.1 ∧ tg.1 ≤ e.2 ∧ decGroup (headFrames T hx v) h₀ r e + 1 ≤ tg.2

open Classical in
/-- The lost upper hops of head `v` at offset `r`. -/
noncomputable def lostSet (v : Fin (k * 2)) (r : ℕ) : Finset (ℕ × ℕ) :=
  (upperHops (headWalk xs v) T).filter (Lost (headFrames T hx v) h₀ r)

/-- The truncated upper hops of head `v`: the deciding group has rank at least `P` at the start. -/
noncomputable def truncSet (P : ℕ) (v : Fin (k * 2)) (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    Finset (ℕ × ℕ) :=
  (upperHops (headWalk xs v) T).filter fun e =>
    P ≤ topRank (shown T hx h₀ r ξ e.1) (decGroup (headFrames T hx v) h₀ r e)

open Classical in
/-- The charged upper hops of head `v` that are not lost. -/
noncomputable def chargedSet (v : Fin (k * 2)) (r : ℕ) : Finset (ℕ × ℕ) :=
  (upperHops (headWalk xs v) T).filter fun e =>
    ¬ Lost (headFrames T hx v) h₀ r e ∧ Charged T hx h₀ v r e

open Classical in
/-- Exposed: the upper hops of head `v`, neither lost nor charged, whose shown sets above the deciding
group differ at the two ends. -/
noncomputable def exposedSet (v : Fin (k * 2)) (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    Finset (ℕ × ℕ) :=
  (upperHops (headWalk xs v) T).filter fun e =>
    ¬ Lost (headFrames T hx v) h₀ r e ∧ ¬ Charged T hx h₀ v r e ∧
      (shown T hx h₀ r ξ e.1).filter (decGroup (headFrames T hx v) h₀ r e < ·) ≠
        (shown T hx h₀ r ξ e.2).filter (decGroup (headFrames T hx v) h₀ r e < ·)

open Classical in
/-- WRAP: the upper hops of head `v`, not lost, that wrap the digit of a shown group at least the
deciding group. -/
noncomputable def wrapSet (K P : ℕ) (v : Fin (k * 2)) (r : ℕ) (ω : Fin P → ℕ)
    (ξ : EntryIdx (headFrames T hx) → Fin Q) : Finset (ℕ × ℕ) :=
  (upperHops (headWalk xs v) T).filter fun e =>
    ¬ Lost (headFrames T hx v) h₀ r e ∧
      ∃ g ∈ shown T hx h₀ r ξ e.1, decGroup (headFrames T hx v) h₀ r e ≤ g ∧ ∃ i : Fin P,
        topRank (shown T hx h₀ r ξ e.1) g = i ∧
          (globalCount T hx (flr h₀ r g) e.1 + ω i) / K ≠ (globalCount T hx (flr h₀ r g) e.2 + ω i) / K

variable {T h₀}

/-! ### The decomposition -/

/-- **The decomposition of the violated hops.** The violated upper hops of a head number at most its
lost, truncated, charged, exposed and WRAP hops. -/
theorem card_violated_le_cut {K P : ℕ} (hK : 0 < K) (v : Fin (k * 2)) (r : ℕ) (ω : Fin P → ℕ)
    (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    ((upperHops (headWalk xs v) T).filter fun e =>
      labelOf T hx h₀ K P r ω ξ e.2 ≤ labelOf T hx h₀ K P r ω ξ e.1).card ≤
      (lostSet T hx h₀ v r).card + (truncSet T hx h₀ P v r ξ).card + (chargedSet T hx h₀ v r).card +
        (exposedSet T hx h₀ v r ξ).card + (wrapSet T hx h₀ K P v r ω ξ).card := by
  classical
  calc _ ≤ (lostSet T hx h₀ v r ∪ truncSet T hx h₀ P v r ξ ∪ chargedSet T hx h₀ v r ∪
        exposedSet T hx h₀ v r ξ ∪ wrapSet T hx h₀ K P v r ω ξ).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨heU, hviol⟩ := mem_filter.mp he
        simp only [mem_union]
        by_cases hL : Lost (headFrames T hx v) h₀ r e
        · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨heU, hL⟩))))
        rcases trunc_or_above_or_wrap_head hx hK v r ω ξ heU hviol with h | h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨heU, h⟩))))
        · by_cases hC : Charged T hx h₀ v r e
          · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨heU, hL, hC⟩)))
          · exact Or.inl (Or.inr (mem_filter.mpr ⟨heU, hL, hC, h⟩))
        · exact Or.inr (mem_filter.mpr ⟨heU, hL, h⟩)
    _ ≤ _ := by
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact card_union_le _ _

/-- The truncated hops are counted by the bad times (`card_trunc_le_bad`). -/
theorem card_truncSet_le_bad (P : ℕ) (v : Fin (k * 2)) (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    (truncSet T hx h₀ P v r ξ).card ≤ (badTimes hx (h₀ := h₀) P r ξ).card :=
  card_trunc_le_bad hx v P r ξ

/-! ### Charged hops -/

/-- **Charged hops.** The charged hops of a head number at most `10 · 2^{θ(g)}` per event `(w, (t, g))`. -/
theorem card_chargedSet_le {r : ℕ} (hr : r < h₀) (v : Fin (k * 2)) :
    (chargedSet T hx h₀ v r).card ≤
      ∑ w, ∑ tg ∈ rises (headFrames T hx w) h₀ r T ∪ lastStints (headFrames T hx w) h₀ r T,
        10 * 2 ^ flr h₀ r tg.2 := by
  classical
  -- the hops of `v` charged to an event at `tg`
  let F : ℕ × ℕ → Finset (ℕ × ℕ) := fun tg => (upperHops (headWalk xs v) T).filter fun e =>
    ¬ Lost (headFrames T hx v) h₀ r e ∧ e.1 < tg.1 ∧ tg.1 ≤ e.2 ∧
      decGroup (headFrames T hx v) h₀ r e + 1 ≤ tg.2
  have hF : ∀ tg : ℕ × ℕ, (F tg).card ≤ 10 * 2 ^ flr h₀ r tg.2 := by
    intro tg
    rcases Nat.eq_zero_or_pos tg.2 with h0 | hpos
    · have hemp : F tg = ∅ := filter_eq_empty_iff.mpr fun e _ h => by omega
      rw [hemp, card_empty]
      exact Nat.zero_le _
    · have h := card_kept_spanning_le (S := headFrames T hx v) (isWalk_headWalk hx v) hr tg.1 (tg.2 - 1)
      rw [show tg.2 - 1 + 1 = tg.2 by omega] at h
      refine le_trans (card_le_card fun e he => ?_) h
      obtain ⟨heU, hnl, h1, h2, hd⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨heU, hnl, h1, h2, by omega⟩
  calc (chargedSet T hx h₀ v r).card
      ≤ (univ.biUnion fun w => (rises (headFrames T hx w) h₀ r T ∪
          lastStints (headFrames T hx w) h₀ r T).biUnion F).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨heU, hnl, w, tg, htg, h1, h2, hd⟩ := mem_filter.mp he
        exact mem_biUnion.mpr ⟨w, mem_univ _, mem_biUnion.mpr ⟨tg, htg,
          mem_filter.mpr ⟨heU, hnl, h1, h2, hd⟩⟩⟩
    _ ≤ ∑ w, ((rises (headFrames T hx w) h₀ r T ∪
          lastStints (headFrames T hx w) h₀ r T).biUnion F).card := card_biUnion_le
    _ ≤ ∑ w, ∑ tg ∈ rises (headFrames T hx w) h₀ r T ∪ lastStints (headFrames T hx w) h₀ r T,
          (F tg).card := sum_le_sum fun w _ => card_biUnion_le
    _ ≤ _ := sum_le_sum fun w _ => sum_le_sum fun tg _ => hF tg

/-! ### Exposed hops -/

/-- **No event, equal views.** If no event of any head at offset `r` lies in `(p, u]` at a group `≥ d + 1`,
every head's view above `d` is the same at `p` and at `u` (`view_interval`, with Lemma W2). Events at
groups `≥ T` do not exist (`lt_of_rise`, `lt_of_lastStint`). -/
theorem views_eq_of_no_event {r : ℕ} (hr : r < h₀) {p u d : ℕ} (hpu : p ≤ u) (huT : u < T)
    (hno : ∀ w, ∀ tg ∈ rises (headFrames T hx w) h₀ r T ∪ lastStints (headFrames T hx w) h₀ r T,
      ¬ (p < tg.1 ∧ tg.1 ≤ u ∧ d + 1 ≤ tg.2)) (w : Fin (k * 2)) :
    (headFrames T hx w).headAbove h₀ r d p = (headFrames T hx w).headAbove h₀ r d u ∧
      (headFrames T hx w).headVisible h₀ r d p = (headFrames T hx w).headVisible h₀ r d u := by
  classical
  refine view_interval hr (popsAtZero_headFrames T hx w) hpu huT d
    fun t h1 h2 g hg => ⟨fun hR => ?_, fun hL => ?_⟩
  · have htT : t < (headFrames T hx w).T := show t < T by omega
    have hgT : g < T := lt_of_rise (S := headFrames T hx w) (isWalk_headWalk hx w) hr htT hR
    refine hno w (t, g) (mem_union_left _ ?_) ⟨h1, h2, hg⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr htT, mem_range.mpr hgT⟩, hR⟩
  · have htT : t < (headFrames T hx w).T := show t < T by omega
    have hgT : g < T := lt_of_lastStint (S := headFrames T hx w) (isWalk_headWalk hx w) hr htT hL
    refine hno w (t, g) (mem_union_right _ ?_) ⟨h1, h2, hg⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr htT, mem_range.mpr hgT⟩, by omega, hL⟩

/-- **Exposed hops, one hop.** At most `2n Q^{|ι|−1}` bit vectors put a given upper hop of a head in `exposedSet`. -/
theorem card_exposed_hop_le {r : ℕ} (hr : r < h₀) (v : Fin (k * 2)) {e : ℕ × ℕ}
    (he : e ∈ upperHops (headWalk xs v) T) :
    (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q => e ∈ exposedSet T hx h₀ v r ξ).card ≤
      2 * (k * 2) * Q ^ (Fintype.card (EntryIdx (headFrames T hx)) - 1) := by
  classical
  -- a lost or charged hop is never in `exposedSet`
  by_cases hLC : ¬ Lost (headFrames T hx v) h₀ r e ∧ ¬ Charged T hx h₀ v r e
  swap
  · have hemp : (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
        e ∈ exposedSet T hx h₀ v r ξ) = ∅ :=
      filter_eq_empty_iff.mpr fun ξ _ hξ => hLC ⟨(mem_filter.mp hξ).2.1, (mem_filter.mp hξ).2.2.1⟩
    rw [hemp, card_empty]
    exact Nat.zero_le _
  obtain ⟨-, hC⟩ := hLC
  have hh := isHop_of_mem_upperHops he
  have hpu : e.1 ≤ e.2 := by have := hh.1; omega
  have huT : e.2 < T := hh.2.1
  -- without an event above `d` in `(p, u]`, all views above `d` agree at `p` and `u`
  have hv := views_eq_of_no_event hx hr hpu huT (d := decGroup (headFrames T hx v) h₀ r e)
    fun w tg htg h => hC ⟨w, tg, htg, h⟩
  by_cases hal : Aligned h₀ r (bandP (headFrames T hx v) e) (bandU (headFrames T hx v) e)
      (ownerScale (headFrames T hx v) e) (homeBand (headFrames T hx v) e)
      (pushMax (headFrames T hx v) e) (FrameMicro (headFrames T hx v) e)
  · -- aligned: `d` is the band group of `v` at both ends, a seed; exposure
    have hd : decGroup (headFrames T hx v) h₀ r e = grp h₀ r (bandU (headFrames T hx v) e) := by
      unfold decGroup
      rw [ite_eq_left hal]
    have hdp : decGroup (headFrames T hx v) h₀ r e ∈ seeds (headFrames T hx) h₀ r e.1 :=
      mem_image.mpr ⟨v, mem_univ _, hal.1.trans hd.symm⟩
    have hdu : decGroup (headFrames T hx v) h₀ r e ∈ seeds (headFrames T hx) h₀ r e.2 :=
      mem_image.mpr ⟨v, mem_univ _, hd.symm⟩
    refine le_trans (card_le_card fun ξ hξ => ?_)
      (card_exposed_le (headFrames T hx) h₀ r (Q := Q) hdp hdu hv)
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_filter.mp hξ).2).2.2.2⟩
  · -- not aligned: `d = 0`, and every candidate at `0` is displayed
    have hd0 : decGroup (headFrames T hx v) h₀ r e = 0 := by
      unfold decGroup
      rw [ite_eq_right hal]
    rw [hd0] at hv
    have hemp : (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
        e ∈ exposedSet T hx h₀ v r ξ) = ∅ := by
      refine filter_eq_empty_iff.mpr fun ξ _ hξ => ?_
      have hne := (mem_filter.mp hξ).2.2.2
      rw [hd0] at hne
      obtain ⟨hX, hV⟩ := views_eq (headFrames T hx) h₀ r (fun e => ξ e ≠ 0) hv
      refine hne ?_
      unfold shown
      exact shown_above_eq (fun e' h1 _ => Disp.zero (Nat.le_zero.mp h1))
        (fun e' h1 _ => Disp.zero (Nat.le_zero.mp h1)) hX hV
    rw [hemp, card_empty]
    exact Nat.zero_le _

/-- **Exposed hops.** Summed over the bit vectors, the exposed hops of a head number at most
`2n Q^{|ι|−1}` per upper hop. -/
theorem sum_card_exposedSet_le {r : ℕ} (hr : r < h₀) (v : Fin (k * 2)) :
    ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, (exposedSet T hx h₀ v r ξ).card ≤
      (upperHops (headWalk xs v) T).card *
        (2 * (k * 2) * Q ^ (Fintype.card (EntryIdx (headFrames T hx)) - 1)) := by
  classical
  calc ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, (exposedSet T hx h₀ v r ξ).card
      = ∑ e ∈ upperHops (headWalk xs v) T, (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
          e ∈ exposedSet T hx h₀ v r ξ).card :=
        sum_card_eq_sum_card_filter _ _ _ fun ξ _ => filter_subset _ _
    _ ≤ ∑ _e ∈ upperHops (headWalk xs v) T,
          2 * (k * 2) * Q ^ (Fintype.card (EntryIdx (headFrames T hx)) - 1) :=
        sum_le_sum fun e he => card_exposed_hop_le hx hr v he
    _ = _ := by rw [sum_const, smul_eq_mul]

/-! ### WRAP -/

/-- A global counter increase is at most the number of turning points and segment starts of all heads
in `(p, u]` of scale at least `θ`. -/
theorem globalCount_sub_le_events {θ p u : ℕ} (hpu : p ≤ u) :
    globalCount T hx θ u - globalCount T hx θ p ≤
      ∑ w, (((turnsOf (headFrames T hx w)).filter fun s =>
          p < s ∧ s ≤ u ∧ θ ≤ band (prom (headFrames T hx w).x (headFrames T hx w).T s)).card +
        ((segStarts (headFrames T hx w)).filter fun Fs =>
          p < Fs.2 ∧ Fs.2 ≤ u ∧ θ ≤ segScale (headFrames T hx w) Fs.1 Fs.2).card) := by
  unfold globalCount
  rw [tsub_le_iff_right, ← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  have h1 := turnCount_sub (S := headFrames T hx w) (θ := θ) hpu
  have h2 := segEventCount_sub (S := headFrames T hx w) (θ := θ) hpu
  have h3 := turnCount_mono (S := headFrames T hx w) (θ := θ) hpu
  have h4 := segEventCount_mono (S := headFrames T hx w) (θ := θ) hpu
  unfold eventCount
  omega

/-- **WRAP, one hop.** The digit offsets putting an upper hop in `wrapSet` number at most `K^{P−1}` times
the counter increases of the shown groups `≥ d` (`card_wrap_le_sum`). -/
theorem card_wrap_hop_le {K P : ℕ} (hK : 0 < K) (v : Fin (k * 2)) (r : ℕ)
    (ξ : EntryIdx (headFrames T hx) → Fin Q) {e : ℕ × ℕ} (he : e ∈ upperHops (headWalk xs v) T) :
    ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω =>
      e ∈ wrapSet T hx h₀ K P v r ω ξ).card ≤
      ∑ g ∈ (shown T hx h₀ r ξ e.1).filter (decGroup (headFrames T hx v) h₀ r e ≤ ·),
        (globalCount T hx (flr h₀ r g) e.2 - globalCount T hx (flr h₀ r g) e.1) * K ^ (P - 1) := by
  classical
  have hh := isHop_of_mem_upperHops he
  have hpu : e.1 ≤ e.2 := by have := hh.1; omega
  refine le_trans (card_le_card fun ω hω => ?_) (card_wrap_le_sum hK (shown T hx h₀ r ξ e.1)
    ((shown T hx h₀ r ξ e.1).filter (decGroup (headFrames T hx v) h₀ r e ≤ ·))
    (fun g => globalCount T hx (flr h₀ r g) e.1) (fun g => globalCount T hx (flr h₀ r g) e.2)
    fun g _ => globalCount_mono T hx hpu)
  obtain ⟨hmem, hw⟩ := mem_filter.mp hω
  obtain ⟨-, -, g, hg, hdg, i, hi, hwr⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨hmem, g, mem_filter.mpr ⟨hg, hdg⟩, i, hi, hwr⟩

/-- **WRAP.** Summed over the digit offsets, the WRAP hops of a head number at most `K^{P−1}` times the
weight `20 · 2^{h₀} · 2^{scale}` of the turning points and segment starts of all heads. -/
theorem sum_card_wrapSet_le {K P : ℕ} (hK : 0 < K) {r : ℕ} (hr : r < h₀) (v : Fin (k * 2))
    (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), (wrapSet T hx h₀ K P v r ω ξ).card ≤
      K ^ (P - 1) * ∑ w, (∑ s ∈ turnsOf (headFrames T hx w),
          20 * 2 ^ h₀ * 2 ^ band (prom (headFrames T hx w).x (headFrames T hx w).T s) +
        ∑ Fs ∈ segStarts (headFrames T hx w),
          20 * 2 ^ h₀ * 2 ^ segScale (headFrames T hx w) Fs.1 Fs.2) := by
  classical
  -- the upper hops of `v` that are not lost, and the groups each one sums over
  let H' : Finset (ℕ × ℕ) :=
    (upperHops (headWalk xs v) T).filter fun e => ¬ Lost (headFrames T hx v) h₀ r e
  let B : ℕ × ℕ → Finset ℕ := fun e =>
    (shown T hx h₀ r ξ e.1).filter (decGroup (headFrames T hx v) h₀ r e ≤ ·)
  -- the turning points and segment starts of head `w` in a hop, at the scale of group `g`
  let X : Fin (k * 2) → ℕ × ℕ → ℕ → ℕ := fun w e g =>
    ((turnsOf (headFrames T hx w)).filter fun s =>
      e.1 < s ∧ s ≤ e.2 ∧ flr h₀ r g ≤ band (prom (headFrames T hx w).x (headFrames T hx w).T s)).card
  let Y : Fin (k * 2) → ℕ × ℕ → ℕ → ℕ := fun w e g =>
    ((segStarts (headFrames T hx w)).filter fun Fs =>
      e.1 < Fs.2 ∧ Fs.2 ≤ e.2 ∧ flr h₀ r g ≤ segScale (headFrames T hx w) Fs.1 Fs.2).card
  have hB : ∀ e, ∀ g ∈ B e, decGroup (headFrames T hx v) h₀ r e ≤ g := fun e g hg =>
    (mem_filter.mp hg).2
  have hX : ∀ w, ∑ e ∈ H', ∑ g ∈ B e, X w e g ≤ ∑ s ∈ turnsOf (headFrames T hx w),
      20 * 2 ^ h₀ * 2 ^ band (prom (headFrames T hx w).x (headFrames T hx w).T s) := fun w =>
    sum_kept_family_le (S := headFrames T hx v) (isWalk_headWalk hx v) hr
      (turnsOf (headFrames T hx w)) (fun s => s)
      (fun s => band (prom (headFrames T hx w).x (headFrames T hx w).T s)) B hB
  have hY : ∀ w, ∑ e ∈ H', ∑ g ∈ B e, Y w e g ≤ ∑ Fs ∈ segStarts (headFrames T hx w),
      20 * 2 ^ h₀ * 2 ^ segScale (headFrames T hx w) Fs.1 Fs.2 := fun w =>
    sum_kept_family_le (S := headFrames T hx v) (isWalk_headWalk hx v) hr
      (segStarts (headFrames T hx w)) (fun Fs => Fs.2)
      (fun Fs => segScale (headFrames T hx w) Fs.1 Fs.2) B hB
  have hswap : ∑ e ∈ H', ∑ g ∈ B e, ∑ w, (X w e g + Y w e g) =
      ∑ w, (∑ e ∈ H', ∑ g ∈ B e, X w e g + ∑ e ∈ H', ∑ g ∈ B e, Y w e g) := by
    calc ∑ e ∈ H', ∑ g ∈ B e, ∑ w, (X w e g + Y w e g)
        = ∑ e ∈ H', ∑ w, ∑ g ∈ B e, (X w e g + Y w e g) := sum_congr rfl fun e _ => sum_comm
      _ = ∑ w, ∑ e ∈ H', ∑ g ∈ B e, (X w e g + Y w e g) := sum_comm
      _ = ∑ w, (∑ e ∈ H', ∑ g ∈ B e, X w e g + ∑ e ∈ H', ∑ g ∈ B e, Y w e g) :=
          sum_congr rfl fun w _ => by
            rw [← sum_add_distrib]
            exact sum_congr rfl fun e _ => sum_add_distrib
  calc ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), (wrapSet T hx h₀ K P v r ω ξ).card
      = ∑ e ∈ upperHops (headWalk xs v) T, ((Fintype.piFinset fun _ : Fin P => range K).filter
          fun ω => e ∈ wrapSet T hx h₀ K P v r ω ξ).card :=
        sum_card_eq_sum_card_filter _ _ _ fun ω _ => filter_subset _ _
    _ ≤ ∑ e ∈ H', ((Fintype.piFinset fun _ : Fin P => range K).filter
          fun ω => e ∈ wrapSet T hx h₀ K P v r ω ξ).card := by
        refine sum_le_sum_of_ne_zero fun e he hne => mem_filter.mpr ⟨he, fun hL => hne ?_⟩
        exact card_eq_zero.mpr (filter_eq_empty_iff.mpr fun ω _ hω => (mem_filter.mp hω).2.1 hL)
    _ ≤ ∑ e ∈ H', ∑ g ∈ B e,
          (globalCount T hx (flr h₀ r g) e.2 - globalCount T hx (flr h₀ r g) e.1) * K ^ (P - 1) :=
        sum_le_sum fun e he => card_wrap_hop_le hx hK v r ξ (mem_filter.mp he).1
    _ ≤ ∑ e ∈ H', ∑ g ∈ B e, (∑ w, (X w e g + Y w e g)) * K ^ (P - 1) := by
        refine sum_le_sum fun e he => sum_le_sum fun g _ => Nat.mul_le_mul_right _ ?_
        have := (isHop_of_mem_upperHops (mem_filter.mp he).1).1
        exact globalCount_sub_le_events hx (by omega)
    _ = K ^ (P - 1) * ∑ e ∈ H', ∑ g ∈ B e, ∑ w, (X w e g + Y w e g) := by
        rw [mul_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun g _ => mul_comm _ _
    _ = K ^ (P - 1) * ∑ w, (∑ e ∈ H', ∑ g ∈ B e, X w e g + ∑ e ∈ H', ∑ g ∈ B e, Y w e g) := by
        rw [hswap]
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum fun w _ => Nat.add_le_add (hX w) (hY w))

end BoundedStackDepth

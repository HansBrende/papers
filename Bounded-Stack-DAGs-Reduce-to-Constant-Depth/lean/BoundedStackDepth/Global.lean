import BoundedStackDepth.Composition
import BoundedStackDepth.Events
import BoundedStackDepth.Excursions
import BoundedStackDepth.Label

/-!
# The global construction for `k` walks

* **Heads.** The `2k` virtual heads are the pairs (walk, class), indexed by `Fin (k * 2)` through
  `finProdFinEquiv`: class U (`j = 0`) sees the walk upright, class L (`j = 1`) reflected (the earlier
  paper's `sw`). Head `v` has the frame system `headFrames v` (Theorem A's frames of its walk).
* **Events and counters.** `globalCount θ t` counts the events of all heads up to `t` of scale `≥ θ`
  (each walk's turning points are counted once per class).
* **The display.** `shown r ξ t` is the shown set of the composed display at offset `r` and bits `ξ`.
* **The label.** `labelOf r ω ξ t`: the label of the shown set with the global counters and digit
  offsets `ω`; it takes fewer than `K ^ P` values (`labelOf_lt`).
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)

/-- The walk and class of a head. -/
def headOf (v : Fin (k * 2)) : Fin k × Fin 2 := finProdFinEquiv.symm v

/-- The walk seen by a head: upright for class U (`j = 0`), reflected for class L. -/
def headWalk (v : Fin (k * 2)) : ℕ → ℤ := sw xs (headOf v).1 (decide ((headOf v).2 = 0))

theorem isWalk_headWalk {xs : Fin k → ℕ → ℤ} (hx : ∀ i, IsWalk (xs i)) (v : Fin (k * 2)) :
    IsWalk (headWalk xs v) :=
  isWalk_sw hx _ _

theorem headOf_mk (i : Fin k) (j : Fin 2) : headOf (finProdFinEquiv (i, j)) = (i, j) := by
  simp [headOf]

/-- The class-U head of walk `i` sees the walk upright. -/
theorem headWalk_up (i : Fin k) : headWalk xs (finProdFinEquiv (i, 0)) = xs i := by
  funext t; simp [headWalk, headOf_mk, sw]

/-- The class-L head of walk `i` sees the walk reflected. -/
theorem headWalk_down (i : Fin k) : headWalk xs (finProdFinEquiv (i, 1)) = fun t => -xs i t := by
  funext t; simp [headWalk, headOf_mk, sw]

/-- Every hop of walk `i` is an upper hop of one of its two heads. -/
theorem hops_subset_heads (i : Fin k) :
    hops (xs i) T ⊆ upperHops (headWalk xs (finProdFinEquiv (i, 0))) T ∪
      upperHops (headWalk xs (finProdFinEquiv (i, 1))) T := by
  rw [headWalk_up, headWalk_down, upperHops_neg, upperHops_union_lowerHops]

/-- The violated hop pairs of a label number at most the violated upper hops of all heads. -/
theorem card_violated_le_heads (Ψ : ℕ → ℕ) :
    (violatedOf Ψ (hopPairs (allHops xs T))).card ≤
      ∑ v, ((upperHops (headWalk xs v) T).filter fun e => Ψ e.2 ≤ Ψ e.1).card := by
  refine (card_le_card fun e he => ?_).trans card_biUnion_le
  obtain ⟨heH, hviol⟩ := mem_filter.mp he
  obtain ⟨η, hη, rfl⟩ := mem_image.mp heH
  have hmem : (η.2.1, η.2.2) ∈ hops (xs η.1) T := mem_hops.mpr (mem_allHops.mp hη)
  rcases mem_union.mp (hops_subset_heads xs T η.1 hmem) with h | h
  · exact mem_biUnion.mpr ⟨_, mem_univ _, mem_filter.mpr ⟨h, hviol⟩⟩
  · exact mem_biUnion.mpr ⟨_, mem_univ _, mem_filter.mpr ⟨h, hviol⟩⟩

variable {xs} (hx : ∀ i, IsWalk (xs i))

/-- The frame system of a head. -/
noncomputable def headFrames (v : Fin (k * 2)) : FrameSystem :=
  upperFrames (headWalk xs v) T (isWalk_headWalk hx v)

/-- The events of all heads up to `t` of scale `≥ θ`. -/
noncomputable def globalCount (θ t : ℕ) : ℕ := ∑ v, eventCount (headFrames T hx v) θ t

theorem globalCount_mono {θ t t' : ℕ} (h : t ≤ t') :
    globalCount T hx θ t ≤ globalCount T hx θ t' :=
  sum_le_sum fun _ _ => eventCount_mono h

/-- The counter of one head is part of the global counter, so a strict increase passes on. -/
theorem globalCount_lt_of_head (v : Fin (k * 2)) {θ t t' : ℕ} (h : t ≤ t')
    (hlt : eventCount (headFrames T hx v) θ t < eventCount (headFrames T hx v) θ t') :
    globalCount T hx θ t < globalCount T hx θ t' :=
  sum_lt_sum (fun _ _ => eventCount_mono h) ⟨v, mem_univ _, hlt⟩

variable (h₀ : ℕ) {Q : ℕ} [NeZero Q]

/-- The shown set at `t`, for offset `r` and bits `ξ`. -/
noncomputable def shown (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) (t : ℕ) : Finset ℕ :=
  shownSet (dispBot (headFrames T hx) h₀ r t) (dispTop (headFrames T hx) h₀ r) (fun e => ξ e ≠ 0)
    (seeds (headFrames T hx) h₀ r t)

/-- **The label** for offset `r`, digit offsets `ω` and bits `ξ`. -/
noncomputable def labelOf (K P r : ℕ) (ω : Fin P → ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) (t : ℕ) :
    ℕ :=
  label K P (shown T hx h₀ r ξ) (fun g t => globalCount T hx (flr h₀ r g) t) ω t

theorem labelOf_lt {K P r : ℕ} (hK : 0 < K) (ω : Fin P → ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q)
    (t : ℕ) : labelOf T hx h₀ K P r ω ξ t < K ^ P :=
  label_lt hK t

end BoundedStackDepth

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} (hx : ∀ i, IsWalk (xs i)) {h₀ : ℕ} {Q : ℕ} [NeZero Q]

/-- The band group of a head is shown. -/
theorem headGroup_mem_shown (v : Fin (k * 2)) (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q)
    (t : ℕ) : (headFrames T hx v).headGroup h₀ r t ∈ shown T hx h₀ r ξ t :=
  mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ v)))

theorem zero_mem_shown (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) (t : ℕ) :
    0 ∈ shown T hx h₀ r ξ t :=
  mem_insert_self _ _

/-- The deciding group of an upper hop of a head is shown at both ends. -/
theorem decGroup_mem_shown (v : Fin (k * 2)) (r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q)
    (e : ℕ × ℕ) :
    decGroup (headFrames T hx v) h₀ r e ∈ shown T hx h₀ r ξ e.1 ∧
      decGroup (headFrames T hx v) h₀ r e ∈ shown T hx h₀ r ξ e.2 := by
  unfold decGroup
  split_ifs with hal
  · refine ⟨?_, headGroup_mem_shown hx v r ξ e.2⟩
    rw [← hal.1]
    exact headGroup_mem_shown hx v r ξ e.1
  · exact ⟨zero_mem_shown hx r ξ _, zero_mem_shown hx r ξ _⟩

/-- **The cut classification of the hops of a head.** A violated upper hop of a head is truncated,
changes the shown set above its deciding group `d`, or wraps a digit of rank at most that of `d`. -/
theorem trunc_or_above_or_wrap_head {K P : ℕ} (hK : 0 < K) (v : Fin (k * 2)) (r : ℕ)
    (ω : Fin P → ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) {e : ℕ × ℕ}
    (he : e ∈ upperHops (headWalk xs v) T)
    (hviol : labelOf T hx h₀ K P r ω ξ e.2 ≤ labelOf T hx h₀ K P r ω ξ e.1) :
    let d := decGroup (headFrames T hx v) h₀ r e
    let O := shown T hx h₀ r ξ
    let cnt := fun g t => globalCount T hx (flr h₀ r g) t
    P ≤ topRank (O e.1) d ∨ (O e.1).filter (d < ·) ≠ (O e.2).filter (d < ·) ∨
      ∃ g ∈ O e.1, d ≤ g ∧ ∃ i : Fin P, topRank (O e.1) g = i ∧
        (cnt g e.1 + ω i) / K ≠ (cnt g e.2 + ω i) / K := by
  obtain ⟨hh, hu⟩ := (mem_upperHops (isWalk_headWalk hx v)).mp he
  obtain ⟨hdp, hdu⟩ := decGroup_mem_shown hx v r ξ e
  have hpu : e.1 ≤ e.2 := by have := hh.1; omega
  refine trunc_or_above_or_wrap hK hdp hdu (fun g _ _ => globalCount_mono T hx hpu) ?_ hviol
  exact globalCount_lt_of_head T hx v hpu (eventCount_lt_decGroup (S := headFrames T hx v) hh hu)

end BoundedStackDepth

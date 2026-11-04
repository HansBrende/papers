import BoundedStackDepth.HopData

/-!
# Events, counters and validity

The *events* of one walk with one frame system `S` are
* its turning points: times `s < T` with `prom ≥ 1`, of scale `band (prom s)` (`turnCount`);
* the segment starts of `S`: a frame start, or a restart, of scale `segScale` (`segEventCount`).

`eventCount S θ t` counts the events up to `t` of scale `≥ θ`; it is monotone in `t` (`eventCount_mono`).

**Validity** (`eventCount_lt_decGroup`): every upper hop strictly increases the counter of its deciding
group `d` (the group of `β(u)` if aligned, `0` otherwise) between `p` and `u`. Eventfulness provides the
event: the segment start of `u` inside `(p, u]`, the owner (a turning point of scale `σ`), or a segment
start of scale `pushMax`; with `d = 0` the owner always serves. (The paper states this for kept hops; it
holds for all.)
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable (S : FrameSystem)

/-- The turning points up to `t` of scale `≥ θ`. -/
noncomputable def turnCount (θ t : ℕ) : ℕ :=
  ((range S.T).filter fun s => s ≤ t ∧ 1 ≤ prom S.x S.T s ∧ θ ≤ band (prom S.x S.T s)).card

open Classical in
/-- The segment starts of `S`: a frame and a time that is its start or a restart. -/
noncomputable def segStarts : Finset ((ℕ × ℕ) × ℕ) :=
  (S.frames ×ˢ range S.T).filter fun Fs => Fs.2 = Fs.1.1 ∨ S.Restart Fs.1 Fs.2

open Classical in
/-- The segment starts up to `t` of scale `≥ θ`. -/
noncomputable def segEventCount (θ t : ℕ) : ℕ :=
  ((segStarts S).filter fun Fs => Fs.2 ≤ t ∧ θ ≤ segScale S Fs.1 Fs.2).card

/-- The events up to `t` of scale `≥ θ`. -/
noncomputable def eventCount (θ t : ℕ) : ℕ := turnCount S θ t + segEventCount S θ t

variable {S}

theorem turnCount_mono {θ t t' : ℕ} (h : t ≤ t') : turnCount S θ t ≤ turnCount S θ t' :=
  card_le_card (monotone_filter_right _ fun _ _ hs => ⟨hs.1.trans h, hs.2⟩)

theorem segEventCount_mono {θ t t' : ℕ} (h : t ≤ t') : segEventCount S θ t ≤ segEventCount S θ t' := by
  classical
  exact card_le_card (monotone_filter_right _ fun _ _ hs => ⟨hs.1.trans h, hs.2⟩)

theorem eventCount_mono {θ t t' : ℕ} (h : t ≤ t') : eventCount S θ t ≤ eventCount S θ t' :=
  Nat.add_le_add (turnCount_mono h) (segEventCount_mono h)

/-- A turning point in `(p, u]` of scale `≥ θ` increases the counter. -/
theorem turnCount_lt {θ p u s : ℕ} (hs : s < S.T) (hp : p < s) (hu : s ≤ u) (h1 : 1 ≤ prom S.x S.T s)
    (hθ : θ ≤ band (prom S.x S.T s)) : turnCount S θ p < turnCount S θ u := by
  refine card_lt_card ⟨monotone_filter_right _ fun _ _ h => ⟨h.1.trans (by omega), h.2⟩, fun hsub => ?_⟩
  have := (mem_filter.mp (hsub (mem_filter.mpr ⟨mem_range.mpr hs, hu, h1, hθ⟩))).2.1
  omega

/-- A segment start in `(p, u]` of scale `≥ θ` increases the counter. -/
theorem segEventCount_lt {θ p u : ℕ} {F : ℕ × ℕ} {s : ℕ} (hF : F ∈ S.frames) (hs : s < S.T)
    (hst : s = F.1 ∨ S.Restart F s) (hp : p < s) (hu : s ≤ u) (hθ : θ ≤ segScale S F s) :
    segEventCount S θ p < segEventCount S θ u := by
  classical
  refine card_lt_card ⟨monotone_filter_right _ fun _ _ h => ⟨h.1.trans (by omega), h.2⟩, fun hsub => ?_⟩
  have hmem : (F, s) ∈ segStarts S := mem_filter.mpr ⟨mem_product.mpr ⟨hF, mem_range.mpr hs⟩, hst⟩
  have := (mem_filter.mp (hsub (mem_filter.mpr ⟨hmem, hu, hθ⟩))).2.1
  omega

/-- Times in the current segment have the same segment start. -/
theorem segStart_eq_of_mem {F : ℕ × ℕ} {t t' : ℕ} (h1 : S.segStart F t ≤ t') (h2 : t' ≤ t) :
    S.segStart F t' = S.segStart F t := by
  refine segStart_eq ?_ h1 fun s' hs' hlt hle hown' =>
    not_restart_of_segStart_lt hlt (hle.trans h2) hs' hown'
  rcases segStart_mem (S := S) F t with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, h.2.1, h.2.2.2⟩

/-- The band at `t` is at most the scale of its segment. -/
theorem beta_le_segScale {t : ℕ} (ht : t < S.T) :
    S.beta t ≤ segScale S (S.inner t) (S.segStart (S.inner t) t) := by
  classical
  unfold beta segScale
  refine band_mono (runMax_le fun t' hown' h1 h2 => ?_)
  exact le_sup (f := fun t₁ => (S.x t₁ - S.x (S.segStart (S.inner t) t)).natAbs)
    (mem_filter.mpr ⟨mem_range.mpr (by omega), hown', segStart_eq_of_mem h1 h2⟩)

variable (S) (h₀ : ℕ)

open Classical in
/-- The deciding group of a hop at offset `r`: the group of `β(u)` if the hop is aligned, `0` otherwise. -/
noncomputable def decGroup (r : ℕ) (e : ℕ × ℕ) : ℕ :=
  if Aligned h₀ r (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e) (pushMax S e) (FrameMicro S e)
  then grp h₀ r (bandU S e) else 0

variable {S h₀}

/-- The owner of an upper hop is a turning point in `(p, u)` with `prom ≥ 1`. -/
theorem owner_turn {e : ℕ × ℕ} (he : IsHop S.x S.T e.1 e.2) (hu : IsUpperHop S.x e.1 e.2) :
    e.1 < hopOwner S.x e.1 e.2 ∧ hopOwner S.x e.1 e.2 < e.2 ∧ 1 ≤ prom S.x S.T (hopOwner S.x e.1 e.2) := by
  have ho := isOwner_hopOwner_of_upper hu
  have h1 := sub_le_prom hu ho he.2.1
  have h2 := hu.above _ ho.gt ho.lt
  exact ⟨ho.gt, ho.lt, by omega⟩

open Classical in
/-- **Validity.** Every upper hop strictly increases the counter of its deciding group from
`p` to `u` (for a hop that is not aligned the deciding group is `0`, and its owner is an event). -/
theorem eventCount_lt_decGroup {r : ℕ} {e : ℕ × ℕ} (he : IsHop S.x S.T e.1 e.2)
    (hu : IsUpperHop S.x e.1 e.2) :
    eventCount S (flr h₀ r (decGroup S h₀ r e)) e.1 < eventCount S (flr h₀ r (decGroup S h₀ r e)) e.2 := by
  obtain ⟨hτ1, hτ2, hprom⟩ := owner_turn he hu
  have huT : e.2 < S.T := he.2.1
  -- an event at the owner
  have howner : ∀ θ, θ ≤ ownerScale S e → eventCount S θ e.1 < eventCount S θ e.2 := fun θ hθ =>
    Nat.add_lt_add_of_lt_of_le (turnCount_lt (by omega) hτ1 hτ2.le hprom hθ) (segEventCount_mono (by omega))
  -- an event at a segment start
  have hseg : ∀ θ (F : ℕ × ℕ) (s : ℕ), F ∈ S.frames → (s = F.1 ∨ S.Restart F s) → e.1 < s → s ≤ e.2 →
      θ ≤ segScale S F s → eventCount S θ e.1 < eventCount S θ e.2 := fun θ F s hF hst hp hs hθ =>
    Nat.add_lt_add_of_le_of_lt (turnCount_mono (by omega))
      (segEventCount_lt hF (by omega) hst hp hs hθ)
  unfold decGroup
  split_ifs with hal
  · obtain ⟨-, -, hev⟩ := hal
    rcases hev with hfm | hσ | hpm
    · -- the segment of `u` starts in `(p, u]`
      have hown := own_inner (S := S) huT
      unfold FrameMicro at hfm
      set F := S.inner e.2
      set s := S.segStart F e.2
      have hps : e.1 < s := by omega
      have hst : s = F.1 ∨ S.Restart F s := by
        rcases segStart_mem (S := S) F e.2 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, h.2.1, h.2.2.2⟩
      refine hseg _ F s hown.1 hst hps (segStart_le hown.2.1.1) ?_
      exact (flr_grp_le h₀ r _).trans (beta_le_segScale huT)
    · exact howner _ hσ
    · rcases Nat.eq_zero_or_pos (flr h₀ r (grp h₀ r (bandU S e))) with h0 | hpos
      · rw [h0]; exact howner 0 (Nat.zero_le _)
      · -- a segment start of scale `pushMax` in `(p, u]`
        have hne : (S.frames ×ˢ Ioc e.1 e.2).Nonempty := by
          by_contra hemp
          rw [not_nonempty_iff_eq_empty] at hemp
          unfold pushMax at hpm
          simp [hemp] at hpm
          omega
        obtain ⟨Fs, hFs, hmax⟩ := exists_mem_eq_sup _ hne fun Fs =>
          if Fs.2 = Fs.1.1 ∨ S.Restart Fs.1 Fs.2 then segScale S Fs.1 Fs.2 else 0
        unfold pushMax at hpm
        rw [hmax] at hpm
        obtain ⟨hF, hI⟩ := mem_product.mp hFs
        obtain ⟨h1, h2⟩ := mem_Ioc.mp hI
        split_ifs at hpm with hc
        · exact hseg _ Fs.1 Fs.2 hF hc h1 h2 hpm
        · omega
  · rw [show flr h₀ r 0 = 0 by simp [flr]]
    exact howner 0 (Nat.zero_le _)

end BoundedStackDepth

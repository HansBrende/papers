import SharedDecoders.CapacityRunsShifts

/-! Actual isolated-row counts for the scalar-closure refinement. -/

namespace SharedDecoders

open Finset CapacityRuns
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {κ : Type*}

def IsIsolated (p : ZMod d → κ) (Δ : Finset (ZMod d)) (x : ZMod d) : Prop :=
  ∀ y, Link p Δ x y → y = x

noncomputable def isolatedCount (p : ZMod d → κ) (Δ : Finset (ZMod d)) : ℕ :=
  Fintype.card {x // IsIsolated p Δ x}

omit [NeZero d] in
theorem link_symm {p : ZMod d → κ} {Δ : Finset (ZMod d)} {x y : ZMod d}
    (h : Link p Δ x y) : Link p Δ y x := by
  obtain ⟨hp, u, hu, v, hv, he⟩ := h
  exact ⟨hp.symm, v, hv, u, hu, he.symm⟩

omit [NeZero d] in
theorem radius_link {p : ZMod d → κ} {Δ : Finset (ZMod d)} {s : ZMod d} {r : ℕ}
    (hcover : CoversRadius Δ s r) (x : ZMod d) {j : ℕ} (hj : j ≤ r)
    (hp : p (x + j • s) = p x) : Link p Δ x (x + j • s) := by
  obtain ⟨u, hu, v, hv, he⟩ := hcover j hj
  refine ⟨hp.symm, u, hu, v, hv, ?_⟩
  rw [he]
  abel

theorem isolatedCount_le_card (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    isolatedCount p Δ ≤ d := by
  simpa only [isolatedCount, ZMod.card] using
    (Fintype.card_subtype_le (IsIsolated p Δ))

omit [NeZero d] in
theorem isolated_prefix_start {p : ZMod d → Bool} {Δ : Finset (ZMod d)}
    {s x : ZMod d} {r : ℕ} (hr : 0 < r) (horder : r < addOrderOf s)
    (hcover : CoversRadius Δ s r) (hx : IsIsolated p Δ x) :
    Start p s r (x + s) := by
  have hne (j : ℕ) (hj : 0 < j) (hjr : j ≤ r) : p (x + j • s) ≠ p x := by
    intro he
    have heq := hx (x + j • s) (radius_link hcover x hjr he)
    have hz : j • s = 0 • s := by simpa using heq
    have hh := nsmul_injOn_Iio_addOrderOf (by omega : j < addOrderOf s)
      (by omega : 0 < addOrderOf s) hz
    omega
  have hfirst : p (x + s) ≠ p x := by simpa using hne 1 (by omega) (by omega)
  refine ⟨by simpa using hfirst.symm, ?_⟩
  intro j hj
  have he : x + s + j • s = x + (j + 1) • s := by rw [add_nsmul, one_nsmul]; abel
  rw [he]
  have hnext := hne (j + 1) (by omega) (by omega)
  cases h₀ : p x <;> cases h₁ : p (x + s) <;>
    cases h₂ : p (x + (j + 1) • s) <;> simp_all

theorem isolatedCount_le_runs_of_long_orbit (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (r : ℕ) (hr : 0 < r)
    (horder : r < addOrderOf s) (hcover : CoversRadius Δ s r) :
    isolatedCount p Δ ≤ runCount p s r := by
  let mark : {x // IsIsolated p Δ x} → {x // Start p s r x} := fun x =>
    ⟨x.1 + s, isolated_prefix_start hr horder hcover x.2⟩
  exact Fintype.card_le_of_injective mark (fun x y h =>
    Subtype.ext (add_right_cancel (congrArg Subtype.val h)))

theorem isolatedCount_le_two_orbits_of_short (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (r : ℕ)
    (horder : addOrderOf s ≤ r) (hcover : CoversRadius Δ s r) :
    isolatedCount p Δ ≤ 2 * Nat.gcd d s.val := by
  let mark : {x // IsIsolated p Δ x} → TranslationOrbit s × Bool :=
    fun x => (orbitOf s x.1, p x.1)
  have hinj : Function.Injective mark := by
    intro x y h
    have hpair : orbitOf s x.1 = orbitOf s y.1 ∧ p x.1 = p y.1 := by
      simpa only [mark, Prod.mk.injEq] using h
    have ho := hpair.1
    have hp := hpair.2
    wlog hle : (indexOf s x.1).val ≤ (indexOf s y.1).val generalizing x y
    · exact (this h.symm ⟨ho.symm, hp.symm⟩ ho.symm hp.symm (by omega)).symm
    let i := (indexOf s x.1).val
    let j := (indexOf s y.1).val
    have he : x.1 + (j - i) • s = y.1 := by
      rw [← walk_index s x.1, ← walk_add, Nat.add_sub_of_le hle, ho]
      exact walk_index s y.1
    have hj : j - i ≤ r := by have := (indexOf s y.1).isLt; omega
    have hl := radius_link hcover x.1 hj (by rw [he]; exact hp.symm)
    rw [he] at hl
    exact Subtype.ext (x.2 y.1 hl).symm
  have hh := Fintype.card_le_of_injective mark hinj
  simpa only [isolatedCount, Fintype.card_prod, Fintype.card_bool,
    translationOrbit_card, mul_comm] using hh

/-- Radius `r` isolates can be charged to following long runs, unless the whole
translation orbit is short, when at most one vertex of each colour is isolated. -/
theorem isolatedCount_le_runs_add_two_gcd (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (r : ℕ) (hr : 0 < r)
    (hcover : CoversRadius Δ s r) :
    isolatedCount p Δ ≤ runCount p s r + 2 * Nat.gcd d s.val := by
  by_cases hn : r < addOrderOf s
  · exact (isolatedCount_le_runs_of_long_orbit p Δ s r hr hn hcover).trans (by omega)
  · exact (isolatedCount_le_two_orbits_of_short p Δ s r (by omega) hcover).trans (by omega)

theorem isolatedCount_add_run_two_le (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (hcover : CoversRadius Δ s 1) :
    isolatedCount p Δ + runCount p s 2 ≤ changeCount p s + Nat.gcd d s.val := by
  classical
  by_cases hs : s = 0
  · subst s
    simpa [runCount, changeCount, Start, Nat.gcd_zero_right] using isolatedCount_le_card p Δ
  let A := univ.filter (Start p s 1)
  let B := univ.filter (Start p s 2)
  have hBA : B ⊆ A := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.1, prefix_one p s x⟩
  have hsub : univ.filter (IsIsolated p Δ) ⊆ A \ B := by
    intro x hx
    have hi := (mem_filter.mp hx).2
    have hn : p (x + s) ≠ p x := by
      intro he
      have hh := hi (x + s) (by simpa only [one_nsmul] using
        (radius_link hcover x (by omega : 1 ≤ 1) (by simpa using he)))
      exact hs (by simpa using hh)
    have hp : p (x - s) ≠ p x := by
      intro he
      have hl := radius_link hcover (x - s) (by omega : 1 ≤ 1) (by simpa using he.symm)
      have hh := hi (x - s) (link_symm (by simpa using hl))
      exact hs (by simpa using hh)
    have hstart : Start p s 1 x := ⟨hp, prefix_one p s x⟩
    have hnot : ¬Start p s 2 x := fun h => hn ((prefix_two_iff p s x).mp h.2)
    simp only [mem_sdiff, A, B, mem_filter, mem_univ, true_and]
    exact ⟨hstart, hnot⟩
  have hc := Finset.card_le_card hsub
  have he := Finset.card_sdiff_add_card_eq_card hBA
  have ha : A.card = changeCount p s := by
    rw [← runCount_one]
    simp only [A, runCount, Fintype.card_subtype]
  have hb : B.card = runCount p s 2 := by simp only [B, runCount, Fintype.card_subtype]
  have hi : (univ.filter (IsIsolated p Δ)).card = isolatedCount p Δ := by
    simp only [isolatedCount, Fintype.card_subtype]
  rw [ha, hb] at he
  rw [hi] at hc
  omega

theorem isolatedCount_first_shift (p : ZMod d → Bool) (s : ZMod d) :
    2 * isolatedCount p (extendShifts {0} s) + changeCount p (2 • s) ≤
      2 * changeCount p s + 2 * Nat.gcd d s.val := by
  have h := isolatedCount_add_run_two_le p _ s (first_shift_covers s)
  rw [changeCount_double]
  omega

theorem isolatedCount_second_shift (p : ZMod d → Bool) (s : ZMod d) :
    isolatedCount p (extendShifts (extendShifts {0} s) (3 • s)) ≤
      runCount p s 4 + 2 * Nat.gcd d s.val :=
  isolatedCount_le_runs_add_two_gcd p _ s 4 (by omega) (second_shift_covers s)

end SharedDecoders

import SharedDecoders.CapacityRunsOrbits

/-!
# Components of a same-colour finite-radius graph

Choose the least orbit index occurring in each component. If that index is at
least the radius, the preceding radius cells have the opposite colour. The
remaining representatives inject into one colour label per translation orbit.
This works even when a run crosses the chosen coordinate origin.
-/

namespace SharedDecoders.CapacityRuns

open Finset
attribute [local instance] Classical.propDecidable

variable {G C : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C]

structure MinimalRepresentatives (s : G) (f : G → C) where
  point : C → G
  value : ∀ c, f (point c) = c
  minimal : ∀ c x, f x = c → (indexOf s (point c)).val ≤ (indexOf s x).val

noncomputable def minimalRepresentatives (s : G) (f : G → C)
    (hf : Function.Surjective f) : MinimalRepresentatives s f := by
  classical
  have hex (c : C) : ∃ x, f x = c ∧
      ∀ y, f y = c → (indexOf s x).val ≤ (indexOf s y).val := by
    obtain ⟨z, hz⟩ := hf c
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image
      (univ.filter (fun y => f y = c)) (fun y => (indexOf s y).val)
      ⟨z, by simp [hz]⟩
    refine ⟨x, (mem_filter.mp hx).2, ?_⟩
    intro y hy
    exact hmin y (by simp [hy])
  exact {
    point := fun c => (hex c).choose
    value := fun c => (hex c).choose_spec.1
    minimal := fun c => (hex c).choose_spec.2 }

variable {s : G} {p : G → Bool} {r : ℕ} {f : G → C}

/-- Every same-colour forward jump of at most `r` stays in the same component. -/
def RespectsRadius (p : G → Bool) (s : G) (r : ℕ) (f : G → C) : Prop :=
  ∀ x j, j ≤ r → p (x + j • s) = p x → f (x + j • s) = f x

omit [DecidableEq G] [Fintype C] in
theorem earlier_ne (R : MinimalRepresentatives s f) (hc : RespectsRadius p s r f)
    (c : C) {j : ℕ} (hj : j < (indexOf s (R.point c)).val)
    (hnear : (indexOf s (R.point c)).val - j ≤ r) :
    p (walk s (orbitOf s (R.point c)) j) ≠ p (R.point c) := by
  intro he
  let a := (indexOf s (R.point c)).val
  let o := orbitOf s (R.point c)
  have hjn : j < addOrderOf s := lt_trans hj (indexOf s (R.point c)).isLt
  have hwalk : walk s o j + (a - j) • s = R.point c := by
    rw [← walk_add, Nat.add_sub_of_le (by omega : j ≤ a)]
    exact walk_index s (R.point c)
  have hv : f (walk s o j) = c := by
    have hh := hc (walk s o j) (a - j) hnear
      (by rw [hwalk]; exact he.symm)
    rw [hwalk, R.value] at hh
    exact hh.symm
  have hm := R.minimal c (walk s o j) hv
  have hi : (indexOf s (walk s o j)).val = j :=
    congrArg Fin.val (indexOf_walk s o ⟨j, hjn⟩)
  rw [hi] at hm
  omega

omit [DecidableEq G] [Fintype C] in
theorem representative_end (R : MinimalRepresentatives s f)
    (hc : RespectsRadius p s r f) (hr : 0 < r) (c : C)
    (ha : r ≤ (indexOf s (R.point c)).val) :
    End p s r (R.point c - r • s) := by
  let a := (indexOf s (R.point c)).val
  let o := orbitOf s (R.point c)
  have hz : R.point c - r • s = walk s o (a - r) := by
    have hw := walk_index s (R.point c)
    have hn : a - r + r = a := by omega
    have he := walk_add s o (a - r) r
    rw [hn, hw] at he
    exact (eq_sub_iff_add_eq).2 he.symm |>.symm
  have hbase : p (walk s o (a - r)) ≠ p (R.point c) :=
    earlier_ne R hc c (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hz, ← walk_add]
    have hjne : p (walk s o (a - r + j)) ≠ p (R.point c) :=
      earlier_ne R hc c (by omega) (by omega)
    cases hp : p (R.point c) <;> cases hb : p (walk s o (a - r)) <;>
      cases hx : p (walk s o (a - r + j)) <;> simp_all
  · simpa only [sub_add_cancel] using (by rw [hz]; exact hbase.symm :
      p (R.point c) ≠ p (R.point c - r • s))

omit [DecidableEq G] [Fintype C] in
theorem small_same_orbit_value (hc : RespectsRadius p s r f) {x y : G}
    (hx : (indexOf s x).val < r) (hy : (indexOf s y).val < r)
    (ho : orbitOf s x = orbitOf s y) (hp : p x = p y) : f x = f y := by
  wlog hle : (indexOf s x).val ≤ (indexOf s y).val generalizing x y
  · exact (this hy hx ho.symm hp.symm (by omega)).symm
  let i := (indexOf s x).val
  let j := (indexOf s y).val
  have he : x + (j - i) • s = y := by
    rw [← walk_index s x, ← walk_add, Nat.add_sub_of_le hle, ho]
    exact walk_index s y
  have hh := hc x (j - i) (by omega) (by rw [he]; exact hp.symm)
  simpa only [he] using hh.symm

omit [DecidableEq G] in
/-- A finite-radius same-colour quotient has at most one component per long
opposite-colour run, plus two baseline components per translation orbit. -/
theorem card_le_ends_add_two_orbits (p : G → Bool) (s : G) (r : ℕ)
    (hr : 0 < r) (f : G → C) (hf : Function.Surjective f)
    (hc : RespectsRadius p s r f) :
    Fintype.card C ≤ Fintype.card {x // End p s r x} +
      2 * Fintype.card (TranslationOrbit s) := by
  classical
  let R := minimalRepresentatives s f hf
  let mark : C → {x // End p s r x} ⊕ (TranslationOrbit s × Bool) := fun c =>
    if h : r ≤ (indexOf s (R.point c)).val then
      Sum.inl ⟨R.point c - r • s, representative_end R hc hr c h⟩
    else Sum.inr (orbitOf s (R.point c), p (R.point c))
  have hinj : Function.Injective mark := by
    intro c e h
    by_cases h₁ : r ≤ (indexOf s (R.point c)).val <;>
      by_cases h₂ : r ≤ (indexOf s (R.point e)).val
    · simp only [mark, dite_eq_left h₁, dite_eq_left h₂, Sum.inl.injEq, Subtype.mk.injEq] at h
      have he : R.point c = R.point e := sub_left_inj.mp h
      simpa only [R.value] using congrArg f he
    · simp only [mark, dite_eq_left h₁, dite_eq_right h₂, Sum.inl_ne_inr] at h
    · simp only [mark, dite_eq_right h₁, dite_eq_left h₂, Sum.inr_ne_inl] at h
    · simp only [mark, dite_eq_right h₁, dite_eq_right h₂, Sum.inr.injEq, Prod.mk.injEq] at h
      have hv := small_same_orbit_value hc (by omega) (by omega) h.1 h.2
      simpa only [R.value] using hv
  have hh := Fintype.card_le_of_injective mark hinj
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, mul_comm] using hh

omit [DecidableEq G] in
/-- At radius one there is only one uncharged index in each orbit. -/
theorem card_le_changes_add_orbits (p : G → Bool) (s : G)
    (f : G → C) (hf : Function.Surjective f)
    (hc : RespectsRadius p s 1 f) :
    Fintype.card C ≤ changeCount p s + Fintype.card (TranslationOrbit s) := by
  classical
  let R := minimalRepresentatives s f hf
  let mark : C → {x // End p s 1 x} ⊕ TranslationOrbit s := fun c =>
    if h : 1 ≤ (indexOf s (R.point c)).val then
      Sum.inl ⟨R.point c - 1 • s, representative_end R hc (by omega) c h⟩
    else Sum.inr (orbitOf s (R.point c))
  have hinj : Function.Injective mark := by
    intro c e h
    by_cases h₁ : 1 ≤ (indexOf s (R.point c)).val <;>
      by_cases h₂ : 1 ≤ (indexOf s (R.point e)).val
    · simp only [mark, dite_eq_left h₁, dite_eq_left h₂, Sum.inl.injEq, Subtype.mk.injEq] at h
      have he : R.point c = R.point e := sub_left_inj.mp h
      simpa only [R.value] using congrArg f he
    · simp only [mark, dite_eq_left h₁, dite_eq_right h₂, Sum.inl_ne_inr] at h
    · simp only [mark, dite_eq_right h₁, dite_eq_left h₂, Sum.inr_ne_inl] at h
    · simp only [mark, dite_eq_right h₁, dite_eq_right h₂, Sum.inr.injEq] at h
      have hi : (indexOf s (R.point c)).val = (indexOf s (R.point e)).val := by omega
      have he : R.point c = R.point e := by
        rw [← walk_index s (R.point c), ← walk_index s (R.point e), h, hi]
      simpa only [R.value] using congrArg f he
  have hh := Fintype.card_le_of_injective mark hinj
  have hend : Fintype.card {x // End p s 1 x} = changeCount p s := by
    unfold changeCount
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl G) (fun x => by simp [End, prefix_one])
  simpa only [Fintype.card_sum, hend] using hh

end SharedDecoders.CapacityRuns

namespace SharedDecoders

open CapacityRuns
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- The differences of the actual translate set cover all forward jumps to `r`. -/
def CoversRadius (Δ : Finset (ZMod d)) (s : ZMod d) (r : ℕ) : Prop :=
  ∀ j ≤ r, ∃ u ∈ Δ, ∃ v ∈ Δ, u = j • s + v

omit [NeZero d] in
theorem quotient_respectsRadius (p : ZMod d → Bool) (Δ : Finset (ZMod d))
    (s : ZMod d) (r : ℕ) (hcover : CoversRadius Δ s r) :
    RespectsRadius p s r (Quotient.mk (Relation.EqvGen.setoid (Link p Δ))) := by
  intro x j hj hp
  obtain ⟨u, hu, v, hv, he⟩ := hcover j hj
  apply Quotient.sound
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨hp.symm, u, hu, v, hv, ?_⟩
  rw [he]
  abel

theorem componentCount_le_runs_add_two_gcd (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (r : ℕ) (hr : 2 ≤ r)
    (hcover : CoversRadius Δ s r) :
    componentCount p Δ ≤ runCount p s r + 2 * Nat.gcd d s.val := by
  have hh := card_le_ends_add_two_orbits p s r (by omega)
    (Quotient.mk (Relation.EqvGen.setoid (Link p Δ))) Quotient.mk_surjective
    (quotient_respectsRadius p Δ s r hcover)
  simpa only [componentCount, end_card_eq_runCount p s hr, translationOrbit_card] using hh

theorem componentCount_le_changes_add_gcd (p : ZMod d → Bool)
    (Δ : Finset (ZMod d)) (s : ZMod d) (hcover : CoversRadius Δ s 1) :
    componentCount p Δ ≤ changeCount p s + Nat.gcd d s.val := by
  have hh := card_le_changes_add_orbits p s
    (Quotient.mk (Relation.EqvGen.setoid (Link p Δ))) Quotient.mk_surjective
    (quotient_respectsRadius p Δ s 1 hcover)
  simpa only [componentCount, translationOrbit_card] using hh

end SharedDecoders

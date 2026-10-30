import GapAreaMemo.CoreWords

set_option autoImplicit false

/-!
# Orbits with a newer exception and a terminal older exception

Adding one family `g` to a family set: every new orbit point is reached by
one nonidentity action of `g` from the old orbit, followed by old families
only, since `g` cannot act again below its owner. Adding a family `e` whose
lower region no other family acts on: every new point is a single landing of
`e`. If the raw path is monotone on the lower region of `e`, raw values of
landings are antitone in the landing time.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

theorem shadowOrbit_step {F : Finset (ActualFamily xs T)} {s v : ℕ}
    (hv : v ∈ shadowOrbit F s) {q : ActualFamily xs T} (hq : q ∈ F) :
    q.shadow v ∈ shadowOrbit F s := by
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨w ++ [q], ?_, Funnel.shadowEndpoint_concat w q s⟩
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hw a h
  · simp only [List.mem_singleton] at h
    exact h ▸ hq

/-- Closure induction over orbit points. -/
theorem shadowOrbit_induction {F : Finset (ActualFamily xs T)} {s : ℕ} {P : ℕ → Prop}
    (h0 : P s) (hstep : ∀ v ∈ shadowOrbit F s, P v → ∀ q ∈ F, P (q.shadow v)) :
    ∀ v ∈ shadowOrbit F s, P v := by
  rintro v ⟨w, hw, rfl⟩
  induction w using List.reverseRecOn with
  | nil => exact h0
  | append_singleton w q ih =>
    rw [Funnel.shadowEndpoint_concat]
    have hw' : ∀ a ∈ w, a ∈ F := fun a ha => hw a (List.mem_append_left _ ha)
    exact hstep _ ⟨w, hw', rfl⟩ (ih hw') q (hw q (by simp))

theorem shadow_eq_self_of_le_owner (q : ActualFamily xs T) {t : ℕ} (ht : t ≤ q.owner) :
    q.shadow t = t := by
  by_contra h
  have := (q.shadow_ne_self_iff t).mp h
  omega

/-- Every orbit point is the root or lies in the lower region of a family of the set. -/
theorem shadowOrbit_root_or_lower {F : Finset (ActualFamily xs T)} {s : ℕ} :
    ∀ v ∈ shadowOrbit F s, v = s ∨ ∃ q ∈ F, q.start < v ∧ v ≤ q.owner := by
  refine shadowOrbit_induction (P := fun v => v = s ∨ ∃ q ∈ F, q.start < v ∧ v ≤ q.owner)
    (Or.inl rfl) ?_
  intro v _ hv q hq
  by_cases ha : q.shadow v = v
  · rw [ha]; exact hv
  · have hb := q.shadow_active_bounds ((q.shadow_ne_self_iff v).mp ha)
    exact Or.inr ⟨q, hq, hb.1, hb.2.1⟩

/-- **A newer exception acts at most once.** -/
theorem shadowOrbit_insert_newer (F : Finset (ActualFamily xs T)) (g : ActualFamily xs T)
    (s : ℕ) :
    ∀ v ∈ shadowOrbit (F ∪ {g}) s, v ∈ shadowOrbit F s ∨
      ∃ u ∈ shadowOrbit F s, g.shadow u ≠ u ∧ v ∈ shadowOrbit F (g.shadow u) := by
  refine shadowOrbit_induction (P := fun v => v ∈ shadowOrbit F s ∨
      ∃ u ∈ shadowOrbit F s, g.shadow u ≠ u ∧ v ∈ shadowOrbit F (g.shadow u))
    (Or.inl (mem_shadowOrbit_self F s)) ?_
  intro v _ hv q hq
  rcases mem_union.mp hq with hqF | hqg
  · rcases hv with hv | ⟨u, hu, hgu, hv⟩
    · exact Or.inl (shadowOrbit_step hv hqF)
    · exact Or.inr ⟨u, hu, hgu, shadowOrbit_step hv hqF⟩
  · rw [mem_singleton.mp hqg]
    rcases hv with hv | ⟨u, hu, hgu, hv⟩
    · by_cases hg : g.shadow v = v
      · rw [hg]; exact Or.inl hv
      · exact Or.inr ⟨v, hv, hg, mem_shadowOrbit_self F _⟩
    · have hb := g.shadow_active_bounds ((g.shadow_ne_self_iff u).mp hgu)
      have hle := shadowOrbit_le hv
      rw [shadow_eq_self_of_le_owner g (hle.trans hb.2.1)]
      exact Or.inr ⟨u, hu, hgu, hv⟩

/-- **A terminal older exception lands once.** No family of the set acts on
the lower region of `e`. -/
theorem shadowOrbit_insert_terminal (F : Finset (ActualFamily xs T)) (e : ActualFamily xs T)
    (s : ℕ) (hterm : ∀ q ∈ F, ∀ t, e.start < t → t ≤ e.owner → q.shadow t = t) :
    ∀ v ∈ shadowOrbit (F ∪ {e}) s, v ∈ shadowOrbit F s ∨
      ∃ u ∈ shadowOrbit F s, e.shadow u ≠ u ∧ v = e.shadow u := by
  refine shadowOrbit_induction (P := fun v => v ∈ shadowOrbit F s ∨
      ∃ u ∈ shadowOrbit F s, e.shadow u ≠ u ∧ v = e.shadow u)
    (Or.inl (mem_shadowOrbit_self F s)) ?_
  intro v _ hv q hq
  rcases hv with hv | ⟨u, hu, heu, rfl⟩
  · rcases mem_union.mp hq with hqF | hqe
    · exact Or.inl (shadowOrbit_step hv hqF)
    · rw [mem_singleton.mp hqe]
      by_cases he : e.shadow v = v
      · rw [he]; exact Or.inl hv
      · exact Or.inr ⟨v, hv, he, rfl⟩
  · have hb := e.shadow_active_bounds ((e.shadow_ne_self_iff u).mp heu)
    rcases mem_union.mp hq with hqF | hqe
    · rw [hterm q hqF _ hb.1 hb.2.1]
      exact Or.inr ⟨u, hu, heu, rfl⟩
    · rw [mem_singleton.mp hqe, shadow_eq_self_of_le_owner e hb.2.1]
      exact Or.inr ⟨u, hu, heu, rfl⟩

/-- Raw values of landings are antitone in the landing time. -/
theorem raw_landing_antitone (e : ActualFamily xs T) (x : ℕ → ℕ)
    (hx : MonotoneOn x (Set.Ioc e.start e.owner)) {u u' : ℕ}
    (hu : e.owner < u ∧ u ≤ e.stop) (hu' : e.owner < u' ∧ u' ≤ e.stop) (h : u ≤ u') :
    x (e.shadow u') ≤ x (e.shadow u) := by
  have e1 : e.shadow u = e.clipped u := e.shadowAction.apply_eq hu
  have e2 : e.shadow u' = e.clipped u' := e.shadowAction.apply_eq hu'
  rw [e1, e2]
  exact hx ⟨(e.clipped_bounds u').1, (e.clipped_bounds u').2⟩
    ⟨(e.clipped_bounds u).1, (e.clipped_bounds u).2⟩ (e.clipped_antitone h)

end
end SourceCovers

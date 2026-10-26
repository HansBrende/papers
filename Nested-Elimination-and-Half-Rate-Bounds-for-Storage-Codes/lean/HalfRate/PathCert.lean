import HalfRate.Circulant

/-!
# Lemma S: chorded digon paths

Let `f 0 ↔ f 1 ↔ ⋯ ↔ f (L-1)` be a path of reciprocated arcs inside a block, and let every other
internal arc (a chord) skip at least two positions, with at most one chord into and one chord out
of every vertex. Eliminating along the path, the later in-neighbours of `f j` are `f (j+1)` and
the source `f u` of a chord `f u → f j` with `u > j`. Link `u` with `j + 1` for every such
downward chord: each position has at most one link from above and one from below, links drop by
at least two, so the classes are chains in which consecutive positions never meet
(`pathRoot_succ_ne`). The classes are the records (`elimOn_path`).
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] {N : V → Finset V} {L : ℕ}

/-- A downward chord `f u → f v` with `v + 3 ≤ u`. -/
def DownChord (N : V → Finset V) (f : Fin L → V) (u v : ℕ) : Prop :=
  ∃ (hu : u < L) (hv : v < L), v + 3 ≤ u ∧ f ⟨u, hu⟩ ∈ N (f ⟨v, hv⟩)

open Classical in
/-- The bottom of the chain of downward links through `u`. -/
noncomputable def pathRoot (N : V → Finset V) (f : Fin L → V) (u : ℕ) : ℕ :=
  if h : ∃ v, DownChord N f u v then pathRoot N f (Classical.choose h + 1) else u
termination_by u
decreasing_by
  obtain ⟨_, _, h3, _⟩ := Classical.choose_spec h
  omega

omit [DecidableEq V] in
theorem pathRoot_le (f : Fin L → V) : ∀ u, pathRoot N f u ≤ u := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    rw [pathRoot]
    split_ifs with h
    · obtain ⟨_, _, h3, _⟩ := Classical.choose_spec h
      exact (ih _ (by omega)).trans (by omega)
    · exact le_rfl

omit [DecidableEq V] in
theorem pathRoot_of_not (f : Fin L → V) {u : ℕ} (h : ¬ ∃ v, DownChord N f u v) :
    pathRoot N f u = u := by
  rw [pathRoot]; simp only [h, ↓reduceDIte]

omit [DecidableEq V] in
/-- With at most one chord out of every vertex, the link of `u` is determined by its chord. -/
theorem pathRoot_of_down (f : Fin L → V)
    (hout : ∀ u v v', DownChord N f u v → DownChord N f u v' → v = v') {u v : ℕ}
    (h : DownChord N f u v) : pathRoot N f u = pathRoot N f (v + 1) := by
  have hex : ∃ v, DownChord N f u v := ⟨v, h⟩
  rw [pathRoot]; simp only [hex, ↓reduceDIte]
  rw [hout u _ v (Classical.choose_spec hex) h]

/-- `x` lies strictly below `y` on the chain of downward links. -/
inductive Desc (N : V → Finset V) (f : Fin L → V) : ℕ → ℕ → Prop
  | step {y v : ℕ} : DownChord N f y v → Desc N f (v + 1) y
  | trans {x y v : ℕ} : DownChord N f y v → Desc N f x (v + 1) → Desc N f x y

omit [DecidableEq V] in
theorem Desc.le {f : Fin L → V} {x y : ℕ} (h : Desc N f x y) : x + 2 ≤ y := by
  induction h with
  | step hc => obtain ⟨_, _, h3, _⟩ := hc; omega
  | trans hc _ ih => obtain ⟨_, _, h3, _⟩ := hc; omega

omit [DecidableEq V] in
/-- Links from above are unique: a chain through `x` cannot reach the link target `v + 1` of a
chord `f y → f v` with `x < y`. -/
theorem Desc.not_up {f : Fin L → V}
    (hin : ∀ u u' v, DownChord N f u v → DownChord N f u' v → u = u') {a x : ℕ}
    (h : Desc N f a x) : ∀ y v, a = v + 1 → DownChord N f y v → x < y → False := by
  induction h with
  | step hc =>
    intro y v hav hyv hxy
    rename_i y' v'
    have : v' = v := by omega
    subst this
    have := hin _ _ _ hc hyv
    omega
  | trans hc hd ih =>
    intro y v hav hyv hxy
    have := hd.le
    obtain ⟨_, _, h3, _⟩ := hc
    exact ih y v hav hyv (by omega)

omit [DecidableEq V] in
/-- Positions with the same root: the lower one lies on the chain of the upper one. -/
theorem desc_of_pathRoot_eq (f : Fin L → V)
    (hin : ∀ u u' v, DownChord N f u v → DownChord N f u' v → u = u')
    (hout : ∀ u v v', DownChord N f u v → DownChord N f u v' → v = v') :
    ∀ y x, x < y → pathRoot N f x = pathRoot N f y → Desc N f x y := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro x hxy he
    by_cases hd : ∃ v, DownChord N f y v
    · obtain ⟨v, hv⟩ := hd
      have hw : pathRoot N f y = pathRoot N f (v + 1) := pathRoot_of_down f hout hv
      obtain ⟨_, _, h3, _⟩ := id hv
      rcases lt_trichotomy x (v + 1) with hlt | heq | hgt
      · exact Desc.trans hv (ih (v + 1) (by omega) x hlt (he.trans hw))
      · rw [heq]; exact Desc.step hv
      · exfalso
        have hdesc := ih x hxy (v + 1) hgt (hw.symm.trans he.symm)
        exact hdesc.not_up hin y v rfl hv hxy
    · rw [pathRoot_of_not f hd] at he
      have := pathRoot_le (N := N) f x
      omega

omit [DecidableEq V] in
/-- **Consecutive positions have different roots.** -/
theorem pathRoot_succ_ne (f : Fin L → V)
    (hin : ∀ u u' v, DownChord N f u v → DownChord N f u' v → u = u')
    (hout : ∀ u v v', DownChord N f u v → DownChord N f u v' → v = v') (j : ℕ) :
    pathRoot N f j ≠ pathRoot N f (j + 1) := by
  intro he
  have := (desc_of_pathRoot_eq f hin hout (j + 1) j (by omega) he).le
  omega

/-- **Lemma S.** Along a path `f 0, …, f (L-1)` whose internal arcs join consecutive positions or
are chords skipping at least two positions, with at most one chord into and one chord out of every
vertex, the relation induced on the path has an elimination certificate: eliminate along the path
with the classes of the downward links as records. -/
theorem elimOn_path (hL : 0 < L) (f : Fin L → V) (hf : Function.Injective f)
    (hpar : ∀ i j (hi : i < L) (hj : j < L), f ⟨i, hi⟩ ∈ N (f ⟨j, hj⟩) →
      j = i + 1 ∨ i = j + 1 ∨ i + 3 ≤ j ∨ j + 3 ≤ i)
    (hin : ∀ u u' v, DownChord N f u v → DownChord N f u' v → u = u')
    (hout : ∀ u v v', DownChord N f u v → DownChord N f u v' → v = v') :
    Nonempty (ElimOn N (univ.image f)) := by
  let col : ℕ → Fin (L + 1) := fun p => ⟨pathRoot N f p % (L + 1), Nat.mod_lt _ (by omega)⟩
  let bcol : ℕ → Fin (L + 1) := fun p => if p + 1 < L then col (p + 1) else ⟨L, by omega⟩
  have hcolv : ∀ p, p < L → (col p).val = pathRoot N f p := fun p hp =>
    Nat.mod_eq_of_lt (by have := pathRoot_le (N := N) f p; omega)
  refine elimOn_ofFn hL f hf col bcol ?_ ?_
  · intro j hj he
    by_cases h : j + 1 < L
    · have he' : col j = col (j + 1) := by simpa [bcol, h] using he
      have := congrArg Fin.val he'
      rw [hcolv j hj, hcolv (j + 1) h] at this
      exact pathRoot_succ_ne f hin hout j this
    · have he' : col j = ⟨L, by omega⟩ := by simpa [bcol, h] using he
      have := congrArg Fin.val he'
      rw [hcolv j hj] at this
      have := pathRoot_le (N := N) f j
      simp at *; omega
  · intro i j hi hj h
    rcases hpar i j hi hj h with e | e | e | e
    · left; omega
    · right
      subst e
      simp [bcol, hi]
    · left; omega
    · right
      have hdc : DownChord N f i j := ⟨hi, hj, e, h⟩
      have hj1 : j + 1 < L := by omega
      simp only [bcol, hj1, ↓reduceIte]
      apply Fin.ext
      rw [hcolv i hi, hcolv (j + 1) hj1]
      exact pathRoot_of_down f hout hdc

section Kinds

variable [Fintype V]

/-- Blocks of the second kind: a path `f 0 ↔ f 1 ↔ ⋯ ↔ f (L-1)` of reciprocated arcs whose other
internal arcs (chords, joining positions at distance at least two) number at most one into and at
most one out of every vertex, with no transitive triangle inside. -/
structure ChordedPath (N : V → Finset V) (K : Finset V) where
  L : ℕ
  pos : 0 < L
  f : Fin L → V
  inj : Function.Injective f
  image : univ.image f = K
  digon : ∀ i (hi : i + 1 < L),
    f ⟨i, by omega⟩ ∈ N (f ⟨i + 1, hi⟩) ∧ f ⟨i + 1, hi⟩ ∈ N (f ⟨i, by omega⟩)
  chordIn : ∀ u u' v (hu : u < L) (hu' : u' < L) (hv : v < L),
    f ⟨u, hu⟩ ∈ N (f ⟨v, hv⟩) → f ⟨u', hu'⟩ ∈ N (f ⟨v, hv⟩) →
    (u + 2 ≤ v ∨ v + 2 ≤ u) → (u' + 2 ≤ v ∨ v + 2 ≤ u') → u = u'
  chordOut : ∀ u v v' (hu : u < L) (hv : v < L) (hv' : v' < L),
    f ⟨u, hu⟩ ∈ N (f ⟨v, hv⟩) → f ⟨u, hu⟩ ∈ N (f ⟨v', hv'⟩) →
    (u + 2 ≤ v ∨ v + 2 ≤ u) → (u + 2 ≤ v' ∨ v' + 2 ≤ u) → v = v'
  tt : TTFreeOn N K

omit [Fintype V] in
/-- A chorded path has an elimination certificate (Lemma S): chords cannot skip a single vertex,
since with the reciprocated arcs around it they would close a transitive triangle. -/
theorem ChordedPath.elimOn (hloop : ∀ v, v ∉ N v) {K : Finset V} (c : ChordedPath N K) :
    Nonempty (ElimOn N K) := by
  rw [← c.image]
  have hmem : ∀ i, c.f i ∈ K := fun i => by
    have h := mem_image_of_mem c.f (mem_univ i)
    rwa [c.image] at h
  have hne : ∀ a b (ha : a < c.L) (hb : b < c.L), a ≠ b → c.f ⟨a, ha⟩ ≠ c.f ⟨b, hb⟩ :=
    fun a b ha hb hab e => hab (congrArg Fin.val (c.inj e))
  refine elimOn_path c.pos c.f c.inj ?_ ?_ ?_
  · intro i j hi hj h
    by_contra hcon
    simp only [not_or] at hcon
    rcases (show i = j ∨ j = i + 2 ∨ i = j + 2 by omega) with e | e | e
    · subst e; exact hloop _ h
    · subst e
      have d := c.digon i (by omega)
      have d' := c.digon (i + 1) hj
      exact c.tt _ (hmem _) _ (hmem _) _ (hmem _) (hne _ _ _ _ (by omega))
        (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega)) d.1 d'.1 h
    · subst e
      have d := c.digon j (by omega)
      have d' := c.digon (j + 1) hi
      exact c.tt _ (hmem _) _ (hmem _) _ (hmem _) (hne _ _ _ _ (by omega))
        (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega)) d'.2 d.2 h
  · rintro u u' v ⟨hu, hv, h3, h⟩ ⟨hu', hv', h3', h'⟩
    exact c.chordIn u u' v hu hu' hv h h' (Or.inr (by omega)) (Or.inr (by omega))
  · rintro u v v' ⟨hu, hv, h3, h⟩ ⟨hu', hv', h3', h'⟩
    exact c.chordOut u v v' hu hv hv' h h' (Or.inr (by omega)) (Or.inr (by omega))

/-- **Theorem PC, block form.** Let the blocks be the fibres of `κ`. Suppose every vertex has at
most one in-neighbour outside its block, every vertex is an in-neighbour of at most one vertex of
each other block, and every block is chordless subcubic, a chorded path, or has an elimination
certificate of its induced relation. Then every valid polymatroid satisfies
`2 h(V) ≤ Σ_v h({v})`. Out-degrees are unbounded. -/
theorem rateBound_pc {ι : Type*} [Fintype ι] [DecidableEq ι] (hloop : ∀ v, v ∉ N v)
    (κ : V → ι)
    (h1 : ∀ v, ∀ u ∈ N v, ∀ u' ∈ N v, κ u ≠ κ v → κ u' ≠ κ v → u = u')
    (h2 : ∀ w v v', κ v = κ v' → κ w ≠ κ v → w ∈ N v → w ∈ N v' → v = v')
    (hK : ∀ i, ChordlessSubcubic N (univ.filter (κ · = i)) ∨
      Nonempty (ChordedPath N (univ.filter (κ · = i))) ∨
      Nonempty (ElimOn N (univ.filter (κ · = i)))) :
    RateBound N (1 / 2) := by
  refine rateBound_pc_ac hloop κ h1 h2 fun i => ?_
  rcases hK i with h | hc | h
  · exact Or.inl h
  · obtain ⟨c⟩ := hc
    exact Or.inr (c.elimOn hloop)
  · exact Or.inr h

end Kinds

end HalfRate

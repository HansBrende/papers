import MergeDepth.Lineage

/-!
# Formations and merges (Lemma 3.11)

A *copy* is a vertex with exactly one out-edge and no input mark; every other vertex is a
*formation*. Following the out-edges of copies leads to the *transport root* of a vertex
(`troot`), a formation. A formation is *deep* (`DeepFormation`) if it is the tail of a deep edge or
its transport tree contains a deep edge, that is, the out-edge of a copy with that transport root.

`dm_le_countP_deepFormation` is Lemma 3.11: for a lineage assignment whose lineage edges are
out-edges and in which every copy is a continuation, every path has at most as many deep merges as
deep formations. The proof walks along the path with a credit: a deep lineage edge out of a
formation credits that formation, and one out of a copy credits the next formation on the path,
whose transport tree contains it; a deep merge of type β uses the credit of its stretch.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {F : Type*} [Field F] {L m : ℕ}

/-- A copy: exactly one out-edge and no input mark. -/
def IsCopy (net : LinNet F L m) (u : ℕ) : Prop := (net.out u).card = 1 ∧ net.rd u = none

open Classical in
/-- The forest of copy edges: a copy points along its out-edge. -/
noncomputable def copyForest (net : LinNet F L m) : Forest where
  nxt u := if h : IsCopy net u then some ((net.out u).min' (card_pos.mp (by rw [h.1]; omega)))
    else none
  nxt_lt u v hv := by
    split_ifs at hv with h
    · cases hv
      exact net.out_lt u _ (min'_mem _ _)

/-- The root of a forest: follow its edges to a vertex without one. -/
def root (lin : Forest) (u : ℕ) : ℕ :=
  match _h : lin.nxt u with
  | none => u
  | some v => root lin v
termination_by u
decreasing_by exact lin.nxt_lt u v _h

theorem root_of_none {lin : Forest} {u : ℕ} (h : lin.nxt u = none) : root lin u = u := by
  rw [root]
  split
  · rfl
  · rename_i v h'
    rw [h] at h'
    exact absurd h' (by simp)

theorem root_of_some {lin : Forest} {u v : ℕ} (h : lin.nxt u = some v) :
    root lin u = root lin v := by
  rw [root]
  split
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)
  · rename_i v' h'
    rw [h] at h'
    cases h'
    rfl

theorem copyForest_nxt_of_copy {net : LinNet F L m} {u v : ℕ} (hc : IsCopy net u)
    (hv : v ∈ net.out u) : (copyForest net).nxt u = some v := by
  classical
  obtain ⟨w, hw⟩ := card_eq_one.mp hc.1
  rw [hw, mem_singleton] at hv
  subst hv
  simp only [copyForest, hc, ↓reduceDIte, Option.some.injEq]
  have h2 : ∀ (s : Finset ℕ) (hs : s.Nonempty), s = {v} → s.min' hs = v := by
    rintro s hs rfl
    simp
  exact h2 _ _ hw

theorem copyForest_nxt_none {net : LinNet F L m} {u : ℕ} (hc : ¬ IsCopy net u) :
    (copyForest net).nxt u = none := by
  classical
  simp [copyForest, hc]

theorem isCopy_of_copyForest {net : LinNet F L m} {u v : ℕ} (h : (copyForest net).nxt u = some v) :
    IsCopy net u ∧ net.out u = {v} := by
  classical
  by_cases hc : IsCopy net u
  · refine ⟨hc, ?_⟩
    obtain ⟨w, hw⟩ := card_eq_one.mp hc.1
    have := copyForest_nxt_of_copy hc (show w ∈ net.out u by rw [hw]; exact mem_singleton_self w)
    rw [h] at this
    cases this
    exact hw
  · rw [copyForest_nxt_none hc] at h
    exact absurd h (by simp)

/-- A deep formation: a formation that is the tail of a deep edge, or whose transport tree contains
a deep edge. -/
def DeepFormation (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) (u : ℕ) : Prop :=
  ¬ IsCopy net u ∧ ((∃ v ∈ net.out u, Rr u v) ∨
    ∃ x v, (copyForest net).nxt x = some v ∧ Rr x v ∧ root (copyForest net) x = u)

/-- **Lemma 3.11, with a credit.** Along a path, the deep merges number at most the deep formations
plus the credit `c`; the credit or a deep copy edge of the current transport tree pays for an open
stretch with a deep edge. -/
theorem dm_le_countP_aux (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr]
    [DecidablePred (DeepFormation net Rr)] (lin : Forest)
    (hlin : ∀ u v, lin.nxt u = some v → v ∈ net.out u)
    (hcopy : ∀ u, IsCopy net u → lin.nxt u ≠ none) :
    ∀ (π : List ℕ) (t : ℕ) (f : Bool) (c : ℕ), π ∈ net.paths t →
      (f = true → 1 ≤ c ∨ ∃ x v, (copyForest net).nxt x = some v ∧ Rr x v ∧
        root (copyForest net) x = root (copyForest net) t) →
      dm lin Rr f π ≤ π.countP (DeepFormation net Rr) + c
  | [], _, _, _, _, _ => by simp [dm]
  | [u], t, f, c, h, hinv => by
    have hu := head_eq_of_mem_paths h
    subst hu
    simp only [dm]
    split_ifs with hm
    · obtain ⟨hnone, hf⟩ := hm
      rcases hinv hf with hc | ⟨x, v, hx, hR, hroot⟩
      · omega
      · have hnc : ¬ IsCopy net u := fun hc => hcopy u hc hnone
        have hroot' : root (copyForest net) u = u := root_of_none (copyForest_nxt_none hnc)
        have hdf : DeepFormation net Rr u := ⟨hnc, Or.inr ⟨x, v, hx, hR, hroot.trans hroot'⟩⟩
        simp [hdf]
    · omega
  | u :: v :: π, t, f, c, h, hinv => by
    have hu := head_eq_of_mem_paths h
    subst hu
    obtain ⟨hv, hπ⟩ := cons_cons_mem_paths.mp h
    have hcount : (u :: v :: π).countP (DeepFormation net Rr) =
        (v :: π).countP (DeepFormation net Rr) + (if DeepFormation net Rr u then 1 else 0) := by
      rw [List.countP_cons]
      simp
    cases hn : lin.nxt u with
    | none =>
      -- a merge node: a formation, deep if it pays
      have hnc : ¬ IsCopy net u := fun hc => hcopy u hc hn
      have hroot' : root (copyForest net) u = u := root_of_none (copyForest_nxt_none hnc)
      have ih := dm_le_countP_aux net Rr lin hlin hcopy (v :: π) v false 0 hπ (by simp)
      simp only [dm, hn, ↓reduceIte]
      rw [hcount]
      by_cases hpay : Rr u v ∨ f = true
      · have hdf_or : DeepFormation net Rr u ∨ 1 ≤ c := by
          rcases hpay with hR | hf
          · exact Or.inl ⟨hnc, Or.inl ⟨v, hv, hR⟩⟩
          · rcases hinv hf with hc | ⟨x, w, hx, hR, hroot⟩
            · exact Or.inr hc
            · exact Or.inl ⟨hnc, Or.inr ⟨x, w, hx, hR, hroot.trans hroot'⟩⟩
        simp only [hpay, ↓reduceIte]
        rcases hdf_or with hdf | hc
        · simp only [hdf, ↓reduceIte]; omega
        · split_ifs <;> omega
      · simp only [hpay, ↓reduceIte]
        omega
    | some v₀ =>
      by_cases hvv : v = v₀
      · subst hvv
        -- the lineage edge: credit a deep formation, or carry the deep copy edge along
        by_cases hc : IsCopy net u
        · have hcf : (copyForest net).nxt u = some v := copyForest_nxt_of_copy hc hv
          have hdf : ¬ DeepFormation net Rr u := fun h => h.1 hc
          have ih := dm_le_countP_aux net Rr lin hlin hcopy (v :: π) v (f || decide (Rr u v)) c hπ
            (by
              intro hf'
              by_cases hR : Rr u v
              · exact Or.inr ⟨u, v, hcf, hR, root_of_some hcf⟩
              · have hf : f = true := by simpa [hR] using hf'
                rcases hinv hf with hc' | ⟨x, w, hx, hR', hroot⟩
                · exact Or.inl hc'
                · exact Or.inr ⟨x, w, hx, hR', hroot.trans (root_of_some hcf)⟩)
          simp only [dm, hn, reduceCtorEq, ↓reduceIte]
          rw [hcount]
          simp only [hdf, ↓reduceIte, add_zero]
          omega
        · have hroot' : root (copyForest net) u = u := root_of_none (copyForest_nxt_none hc)
          set c' := c + (if DeepFormation net Rr u then 1 else 0)
          have ih := dm_le_countP_aux net Rr lin hlin hcopy (v :: π) v (f || decide (Rr u v)) c' hπ
            (by
              intro hf'
              left
              by_cases hR : Rr u v
              · have hdf : DeepFormation net Rr u := ⟨hc, Or.inl ⟨v, hv, hR⟩⟩
                simp [c', hdf]
              · have hf : f = true := by simpa [hR] using hf'
                rcases hinv hf with hc' | ⟨x, w, hx, hR', hroot⟩
                · omega
                · have hdf : DeepFormation net Rr u := ⟨hc, Or.inr ⟨x, w, hx, hR', hroot.trans hroot'⟩⟩
                  simp [c', hdf])
          simp only [dm, hn, reduceCtorEq, ↓reduceIte]
          rw [hcount]
          omega
      · -- a side edge: the stretch ends without a merge
        have ih := dm_le_countP_aux net Rr lin hlin hcopy (v :: π) v false 0 hπ (by simp)
        have hne : ¬ (some v₀ = some v) := fun h => hvv (Option.some.inj h).symm
        simp only [dm, hn, reduceCtorEq, ↓reduceIte, hne]
        rw [hcount]
        omega

/-- **Lemma 3.11.** For a lineage assignment whose lineage edges are out-edges and in which every
copy is a continuation, every path has at most as many deep merges as deep formations. -/
theorem dm_le_countP_deepFormation (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr]
    [DecidablePred (DeepFormation net Rr)] (lin : Forest)
    (hlin : ∀ u v, lin.nxt u = some v → v ∈ net.out u)
    (hcopy : ∀ u, IsCopy net u → lin.nxt u ≠ none) {π : List ℕ} {t : ℕ}
    (h : π ∈ net.paths t) : dm lin Rr false π ≤ π.countP (DeepFormation net Rr) := by
  simpa using dm_le_countP_aux net Rr lin hlin hcopy π t false 0 h (by simp)

end MergeDepth

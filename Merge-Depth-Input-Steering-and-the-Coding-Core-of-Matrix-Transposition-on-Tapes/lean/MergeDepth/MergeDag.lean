import MergeDepth.Charging

/-!
# The merge DAG (Definition 3.20, Proposition 3.21)

Fix a network, a deep-edge relation, a lineage assignment, a revealed set `Γ` (the cold genie and
the checkpoints of Lemma 3.10) and a set `O` of output vertices. The merge DAG has an edge `f → f'`
whenever `f` and `f'` are consecutive deep merges (`dmList`) of a `Γ`-free path from a vertex of `O`
(`MEdge`), and a vertex is initial if it is the first deep merge of such a path (`MInit`).

`dm_le_of_cut`: if `Z` meets every path of the merge DAG with `s + 1` vertices whose first vertex is
initial, then every `(Γ ∪ Z)`-free path from a vertex of `O` outside `Z` has at most `s` deep merges.
`length_le_of_cut` combines it with the per-path bound of Lemma 3.10: such a path has fewer than
`(s + 1) τ D` edges.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {F : Type*} [Field F] {L m : ℕ}

section MergeDag

variable (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (lin : Forest)
  (Γ O : Finset ℕ)

/-- An edge of the merge DAG: consecutive deep merges of a `Γ`-free path from an output vertex. -/
def MEdge (a b : ℕ) : Prop :=
  ∃ u ∈ O, ∃ π ∈ net.paths u, LinNet.GFree Γ π ∧
    ∃ l₁ l₂, dmList lin Rr false π = l₁ ++ a :: b :: l₂

/-- An initial vertex of the merge DAG: the first deep merge of such a path. -/
def MInit (a : ℕ) : Prop :=
  ∃ u ∈ O, ∃ π ∈ net.paths u, LinNet.GFree Γ π ∧ (dmList lin Rr false π).head? = some a

/-- `Z` meets every path of the merge DAG with `s + 1` vertices whose first vertex is initial. -/
def MCut (Z : Finset ℕ) (s : ℕ) : Prop :=
  ∀ l : List ℕ, l.length = s + 1 → (∀ a, l.head? = some a → MInit net Rr lin Γ O a) →
    List.IsChain (MEdge net Rr lin Γ O) l → ∃ z ∈ l, z ∈ Z

/-- **The cut bounds deep merges.** -/
theorem dm_le_of_cut {Z : Finset ℕ} {s : ℕ} (hZ : MCut net Rr lin Γ O Z s) {u : ℕ} (hu : u ∈ O)
    (huZ : u ∉ Z) {π : List ℕ} (hπ : π ∈ net.paths u) (hfree : LinNet.GFree (Γ ∪ Z) π) :
    dm lin Rr false π ≤ s := by
  by_contra hlt
  push Not at hlt
  have hΓ : LinNet.GFree Γ π := gfree_mono subset_union_left hfree
  set dl := dmList lin Rr false π
  have hlen : s + 1 ≤ dl.length := by rw [length_dmList]; omega
  set l := dl.take (s + 1)
  have hl : l.length = s + 1 := by simp [l, List.length_take, hlen]
  -- the first `s + 1` deep merges form a path of the merge DAG from an initial vertex
  have hhead : l.head? = dl.head? := by simp [l, List.head?_take]
  have hinit : ∀ a, l.head? = some a → MInit net Rr lin Γ O a := by
    intro a ha
    refine ⟨u, hu, π, hπ, hΓ, ?_⟩
    rw [← ha, hhead]
  have hchain : List.IsChain (MEdge net Rr lin Γ O) dl :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mpr fun a b l₁ l₂ he =>
      ⟨u, hu, π, hπ, hΓ, l₁, l₂, he⟩
  obtain ⟨z, hz, hzZ⟩ := hZ l hl hinit (hchain.take _)
  -- `z` is a vertex of `π` other than its first, hence not in `Z`
  have hzπ : z ∈ π := mem_of_mem_dmList lin Rr false π z (List.mem_of_mem_take hz)
  obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
  have hzu : z ≠ u := fun h => huZ (h ▸ hzZ)
  have hz' : z ∈ π' := by
    rcases List.mem_cons.mp hzπ with h | h
    · exact absurd h hzu
    · exact h
  exact hfree z hz' (mem_union_right _ hzZ)

/-- **Proposition 3.21, the paths.** For a set `Q` with the covering property and a cut `Z` of the
merge DAG relative to `Γ₀ ∪ Q`, every `(Γ₀ ∪ Q ∪ Z)`-free path from an output vertex outside `Z` has
at most `(s + 1) τ D` vertices. -/
theorem length_le_of_cut (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree Γ₀ (u :: v' :: π) → rCount Rr (u :: v' :: π) = 0)
    (M : Finset ℕ) (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) {τ : ℕ} (hτ : 1 ≤ τ)
    (Q : Finset ℕ)
    (hcov : ∀ u ρ, IsChain lin (u :: ρ) → (∀ v ∈ ρ, v ∉ Q) → crossed M (u :: ρ) < τ)
    {Z : Finset ℕ} {s : ℕ} (hZ : MCut net Rr lin (Γ₀ ∪ Q) O Z s) {u : ℕ} (hu : u ∈ O)
    (huZ : u ∉ Z) {π : List ℕ} (hπ : π ∈ net.paths u) (hfree : LinNet.GFree (Γ₀ ∪ Q ∪ Z) π) :
    π.length ≤ (s + 1) * τ * D := by
  have hdm := dm_le_of_cut net Rr lin (Γ₀ ∪ Q) O hZ hu huZ hπ hfree
  have h := length_le_of_cov net Rr lin Γ₀ D hcold hside M hM hτ Q hcov hπ
    (gfree_mono subset_union_left hfree)
  calc π.length ≤ (dm lin Rr false π + 1) * τ * D := h
    _ ≤ (s + 1) * τ * D := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

end MergeDag

open Matrix Module BoundedNesting.LinNet in
open Classical in
/-- **Proposition 3.21(a).** For a set `Q` with the covering property and a cut `Z` of the merge DAG
(built from paths that start at the output vertices outside `Γ₀ ∪ Q`), a transposing linear network has `P_tpos = R + S` with `rank R ≤ rank(E_{Γ₀}) + m |Q| + m |Z|` and
row `ℓ` of `S` supported in the balls of radius `(s + 1) τ D` around the output vertices of `ℓ`
outside `Γ₀ ∪ Q ∪ Z`. -/
theorem merge_reduction (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (lin : Forest)
    (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree Γ₀ (u :: v' :: π) → rCount Rr (u :: v' :: π) = 0)
    (M : Finset ℕ) (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) {τ : ℕ} (hτ : 1 ≤ τ)
    (Q : Finset ℕ)
    (hcov : ∀ u ρ, IsChain lin (u :: ρ) → (∀ v ∈ ρ, v ∉ Q) → crossed M (u :: ρ) < τ)
    (O : Finset ℕ) {Z : Finset ℕ} {s : ℕ} (hZ : MCut net Rr lin (Γ₀ ∪ Q) O Z s)
    (tout : Fin L → Finset ℕ) (htout : ∀ ℓ, ∀ u ∈ tout ℓ, u ∉ Γ₀ ∪ Q → u ∈ O)
    (φ : Fin L → ℕ → Fin m → F)
    (φc : Fin L → F) (tpos : Fin L → Fin L)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val w u = w (tpos ℓ)) :
    ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
      R.rank ≤ finrank F (LinearMap.range (revealed net Γ₀)) + m * Q.card + m * Z.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ∃ u ∈ tout ℓ, u ∉ Γ₀ ∪ Q ∪ Z ∧
        j ∈ net.reach ∅ ((s + 1) * τ * D) u := by
  obtain ⟨R, hP, hrank⟩ := rigidity_core_rev net tout φ φc tpos (Γ₀ ∪ Q ∪ Z) htrans
  refine ⟨R, _, hP, ?_, fun ℓ j hS => ?_⟩
  · calc R.rank ≤ finrank F (LinearMap.range (revealed net (Γ₀ ∪ Q ∪ Z))) := hrank
      _ ≤ finrank F (LinearMap.range (revealed net (Γ₀ ∪ Q))) +
            finrank F (LinearMap.range (revealed net Z)) := finrank_revealed_union_le net _ _
      _ ≤ (finrank F (LinearMap.range (revealed net Γ₀)) +
            finrank F (LinearMap.range (revealed net Q))) + m * Z.card :=
          Nat.add_le_add (finrank_revealed_union_le net _ _) (finrank_revealed_le net Z)
      _ ≤ finrank F (LinearMap.range (revealed net Γ₀)) + m * Q.card + m * Z.card := by
          have := finrank_revealed_le net Q
          omega
  · by_contra hno
    push Not at hno
    apply hS
    simp only [Matrix.of_apply]
    refine sum_eq_zero fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
    have huZ : u ∉ Z := fun h => hu2 (mem_union_right _ h)
    have hshort : ∀ π, π ∈ net.paths u → LinNet.GFree (Γ₀ ∪ Q ∪ Z) π →
        π.length ≤ (s + 1) * τ * D + 1 := fun π hπ hfree =>
      (length_le_of_cut net Rr lin O Γ₀ D hcold hside M hM hτ Q hcov hZ
        (htout ℓ u hu1 fun h => hu2 (mem_union_left _ h)) huZ hπ hfree).trans (Nat.le_succ _)
    by_cases hj : j ∈ net.reach (Γ₀ ∪ Q ∪ Z) ((s + 1) * τ * D) u
    · exact absurd (net.reach_subset _ _ _ hj) (hno u hu1 hu2)
    · rw [C_eq_zero_of_short net _ _ u hshort j hj]
      simp

end MergeDepth

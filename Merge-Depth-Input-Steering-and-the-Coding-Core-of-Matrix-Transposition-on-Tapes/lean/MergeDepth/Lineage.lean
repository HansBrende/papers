import MergeDepth.Paths
import MergeDepth.Covering

/-!
# Lineages and deep merges: paths that avoid the checkpoints are short

A linear network (one coordinate per vertex, in the application) carries a *lineage assignment*
`lin`: some vertices `u` designate one out-edge `u → lin u`, their *lineage edge*, and are called
*continuations*; the others are *merge nodes*. The hypothesis `hside` says that a continuation's
other out-edges are dead: no `Γ₀`-free path that leaves `u` through another out-edge contains a deep
edge (an edge of `Rr`).

A merge node `u_i` of a path is a *deep merge* of the path if the path leaves it along a deep edge
(type α), or reaches it through a deep lineage edge followed only by lineage edges (type β).
`dm lin Rr false π` counts the deep merges of `π`; the flag records whether the path arrived at its
current vertex through a stretch of lineage edges containing a deep one.

`paths_short`: let every `Γ₀`-free path without deep edges have at most `D` vertices, let `M`
contain the tails of the deep lineage edges and let `τ ≥ 1`. Then there is a set `Q` of checkpoints
with `τ |Q| ≤ |M|` such that every `(Γ₀ ∪ Q)`-free path from a vertex `t`, all of whose `Γ₀`-free
paths have at most `s` deep merges, has at most `(s + 1) τ D` vertices.

The proof (`rCount_add_le`) walks along the path carrying the current lineage stretch: by the
covering lemma a stretch whose vertices after the first avoid `Q` crosses fewer than `τ` deep
edges; a stretch that crosses one ends at a deep merge (type β), at a dead side edge, or at the end
of the path; and a deep edge out of a merge node is a deep merge (type α). So a path with `s'` deep
merges has at most `(s' + 1) τ - 1` deep edges, and the cold-depth bound (`length_le_of_cold`)
turns `ρ` deep edges into at most `(ρ + 1) D` vertices.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {F : Type*} [Field F] {L m : ℕ}

/-- **Deep merges.** `dm lin Rr f π` counts the merge nodes of `π` that the path leaves along a deep
edge (type α) or reaches through a stretch of lineage edges containing a deep one (type β); the
flag `f` says whether the path arrives at its first vertex through such a stretch. -/
def dm (lin : Forest) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] : Bool → List ℕ → ℕ
  | _, [] => 0
  | f, [u] => if lin.nxt u = none ∧ f = true then 1 else 0
  | f, u :: v :: π =>
    if lin.nxt u = none then (if Rr u v ∨ f = true then 1 else 0) + dm lin Rr false (v :: π)
    else if lin.nxt u = some v then dm lin Rr (f || decide (Rr u v)) (v :: π)
    else dm lin Rr false (v :: π)

/-! ### Appending to a chain -/

theorem isChain_append (lin : Forest) {v : ℕ} :
    ∀ (σ : List ℕ) (hσ : σ ≠ []), IsChain lin σ → lin.nxt (σ.getLast hσ) = some v →
      IsChain lin (σ ++ [v])
  | [], h, _, _ => absurd rfl h
  | [u], _, _, h => by simpa [IsChain] using h
  | u :: w :: σ, _, hc, h => by
    obtain ⟨huw, hc'⟩ := hc
    have := isChain_append lin (w :: σ) (by simp) hc' (by simpa using h)
    exact ⟨huw, this⟩

theorem crossed_append (M : Finset ℕ) {v : ℕ} :
    ∀ (σ : List ℕ) (hσ : σ ≠ []),
      crossed M (σ ++ [v]) = crossed M σ + (if σ.getLast hσ ∈ M then 1 else 0)
  | [], h => absurd rfl h
  | [u], _ => by
    show (if u ∈ M then 1 else 0) + 0 = 0 + (if u ∈ M then 1 else 0)
    omega
  | u :: w :: σ, _ => by
    have ih := crossed_append M (v := v) (w :: σ) (by simp)
    rw [List.getLast_cons_cons]
    show (if u ∈ M then 1 else 0) + crossed M ((w :: σ) ++ [v]) =
      (if u ∈ M then 1 else 0) + crossed M (w :: σ) + _
    rw [ih]
    ring

theorem rCount_append (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] {v : ℕ} :
    ∀ (σ : List ℕ) (hσ : σ ≠ []),
      rCount Rr (σ ++ [v]) = rCount Rr σ + (if Rr (σ.getLast hσ) v then 1 else 0)
  | [], h => absurd rfl h
  | [u], _ => by
    show (if Rr u v then 1 else 0) + 0 = 0 + (if Rr u v then 1 else 0)
    omega
  | u :: w :: σ, _ => by
    have ih := rCount_append Rr (v := v) (w :: σ) (by simp)
    rw [List.getLast_cons_cons]
    show (if Rr u w then 1 else 0) + rCount Rr ((w :: σ) ++ [v]) =
      (if Rr u w then 1 else 0) + rCount Rr (w :: σ) + _
    rw [ih]
    ring

/-- On a chain, the deep edges are deep lineage edges, whose tails lie in `M`. -/
theorem rCount_le_crossed (lin : Forest) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (M : Finset ℕ)
    (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) :
    ∀ σ : List ℕ, IsChain lin σ → rCount Rr σ ≤ crossed M σ
  | [], _ => le_rfl
  | [_], _ => le_rfl
  | u :: w :: σ, hc => by
    obtain ⟨huw, hc'⟩ := hc
    have ih := rCount_le_crossed lin Rr M hM (w :: σ) hc'
    simp only [rCount, crossed]
    have : (if Rr u w then 1 else 0) ≤ (if u ∈ M then 1 else 0) := by
      by_cases hR : Rr u w
      · simp [hR, hM u w huw hR]
      · simp [hR]
    omega

/-! ### Deep edges on paths that avoid the checkpoints -/

/-- **Deep edges and deep merges.** Carry the current lineage stretch `σ`, a chain ending at the
first vertex of `π` whose vertices after the first avoid `Q`. Then the deep edges of `π` and `σ`
together number at most `τ - 1 + τ` times the deep merges of `π`. -/
theorem rCount_add_le (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (lin : Forest)
    (Γ₀ : Finset ℕ)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree Γ₀ (u :: v' :: π) → rCount Rr (u :: v' :: π) = 0)
    (M : Finset ℕ) (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) {τ : ℕ} (Q : Finset ℕ)
    (hcov : ∀ u ρ, IsChain lin (u :: ρ) → (∀ v ∈ ρ, v ∉ Q) → crossed M (u :: ρ) < τ) :
    ∀ (π : List ℕ) (t : ℕ) (σ : List ℕ) (hσ : σ ≠ []), π ∈ net.paths t →
      LinNet.GFree (Γ₀ ∪ Q) π → IsChain lin σ → σ.getLast hσ = t → (∀ v ∈ σ.tail, v ∉ Q) →
      rCount Rr π + rCount Rr σ ≤ (τ - 1) + τ * dm lin Rr (decide (0 < rCount Rr σ)) π := by
  -- the current stretch crosses fewer than `τ` deep edges
  have hstretch : ∀ (σ : List ℕ), σ ≠ [] → IsChain lin σ → (∀ v ∈ σ.tail, v ∉ Q) →
      rCount Rr σ < τ := by
    intro σ hσ hc hQ
    obtain ⟨a, ρ, rfl⟩ := List.exists_cons_of_ne_nil hσ
    exact (rCount_le_crossed lin Rr M hM _ hc).trans_lt (hcov a ρ hc (by simpa using hQ))
  intro π
  induction π with
  | nil =>
    intro t σ hσ h
    obtain ⟨π', hπ'⟩ := net.mem_paths_head h
    simp at hπ'
  | cons u π ih =>
    intro t σ hσ h hfree hc hlast hQ
    have hu := head_eq_of_mem_paths h
    subst hu
    have hσlt := hstretch σ hσ hc hQ
    cases π with
    | nil =>
      simp only [rCount, zero_add]
      omega
    | cons v π =>
      obtain ⟨hv, hπ⟩ := cons_cons_mem_paths.mp h
      obtain ⟨hvΓ, hfree'⟩ := gfree_cons_cons.mp hfree
      have hvQ : v ∉ Q := fun hq => hvΓ (mem_union_right _ hq)
      cases hn : lin.nxt u with
      | none =>
        -- a merge node: the stretch restarts at `v`
        have ihv := ih v [v] (by simp) hπ hfree' trivial rfl (by simp)
        simp only [rCount, add_zero, lt_irrefl, decide_false] at ihv
        simp only [dm, rCount, hn, ↓reduceIte]
        by_cases hR : Rr u v
        · simp only [hR, ↓reduceIte, true_or]
          nlinarith
        · by_cases hf : 0 < rCount Rr σ
          · simp only [hR, hf, decide_true, or_true, ↓reduceIte]
            nlinarith
          · simp only [hR, hf, decide_false, Bool.false_eq_true, or_self, ↓reduceIte, zero_add]
            omega
      | some v₀ =>
        by_cases hvv : v = v₀
        · -- the lineage edge: the stretch grows by `v`
          subst hvv
          have hσ' : σ ++ [v] ≠ [] := by simp
          have hc' := isChain_append lin σ hσ hc (by rw [hlast]; exact hn)
          have hR' := rCount_append Rr (v := v) σ hσ
          rw [hlast] at hR'
          have ihv := ih v (σ ++ [v]) hσ' hπ hfree' hc' (by simp) (by
            intro x hx
            obtain ⟨a, ρ, rfl⟩ := List.exists_cons_of_ne_nil hσ
            simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hQ x (by simpa using hx)
            · exact hvQ)
          have hflag : decide (0 < rCount Rr (σ ++ [v])) =
              (decide (0 < rCount Rr σ) || decide (Rr u v)) := by
            rw [hR']
            by_cases hR : Rr u v <;> by_cases hf : 0 < rCount Rr σ <;> simp [hR, hf]
          rw [hflag, hR'] at ihv
          have hne : lin.nxt u ≠ none := by rw [hn]; simp
          simp only [dm, rCount, hn, ↓reduceIte, reduceCtorEq]
          omega
        · -- a side edge: no deep edge follows
          have h0 := hside u v₀ v π hn hvv h (gfree_mono subset_union_left hfree)
          rw [h0, zero_add]
          omega

/-! ### Paths avoiding the checkpoints are short -/

/-- **Short paths.** Let every `Γ₀`-free path without deep edges have at most `D` vertices, let the
other out-edges of continuations be dead, let `M` contain the tails of the deep lineage edges, and
let `τ ≥ 1`. There is a set `Q` with `τ |Q| ≤ |M|` such that, for every vertex `t` whose `Γ₀`-free
paths have at most `s` deep merges, every `(Γ₀ ∪ Q)`-free path from `t` has at most `(s + 1) τ D`
vertices. -/
theorem paths_short (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (lin : Forest)
    (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree Γ₀ (u :: v' :: π) → rCount Rr (u :: v' :: π) = 0)
    (M : Finset ℕ) (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ M.card ∧
      ∀ (t s : ℕ), (∀ π, π ∈ net.paths t → LinNet.GFree Γ₀ π → dm lin Rr false π ≤ s) →
        ∀ π, π ∈ net.paths t → LinNet.GFree (Γ₀ ∪ Q) π → π.length ≤ (s + 1) * τ * D := by
  obtain ⟨Q, -, hQ, hcov⟩ := covering lin M hτ
  refine ⟨Q, hQ, fun t s hround π hπ hfree => ?_⟩
  have h1 := rCount_add_le net Rr lin Γ₀ hside M hM Q hcov π t [t] (by simp) hπ hfree trivial rfl
    (by simp)
  simp only [rCount, add_zero, lt_irrefl, decide_false] at h1
  have h3 := hround π hπ (gfree_mono subset_union_left hfree)
  have h4 := length_le_of_cold net Rr Γ₀ D hcold hπ (gfree_mono subset_union_left hfree)
  have h6 : τ * dm lin Rr false π ≤ τ * s := Nat.mul_le_mul_left _ h3
  have h5 : rCount Rr π + 1 ≤ (s + 1) * τ := by
    have : (s + 1) * τ = τ + τ * s := by ring
    omega
  calc π.length ≤ (rCount Rr π + 1) * D := h4
    _ ≤ (s + 1) * τ * D := Nat.mul_le_mul_right _ h5

end MergeDepth

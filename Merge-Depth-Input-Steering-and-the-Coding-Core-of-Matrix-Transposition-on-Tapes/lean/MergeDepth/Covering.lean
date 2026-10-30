import Mathlib

/-!
# The covering lemma

A *lineage forest* on `ℕ` is given by a partial parent map `nxt : ℕ → Option ℕ` with
`nxt u = some v → v < u`: every node has at most one out-edge, towards an earlier node. Some of its
edges are *marked*: the tails of the marked edges form a finite set `M`.

`covering`: for every `τ ≥ 1` there is a set `Q` of heads of marked edges with `τ |Q| ≤ |M|` such
that every chain `u₀ → u₁ → ⋯ → u_n` of the forest whose nodes after the first avoid `Q` crosses
fewer than `τ` marked edges.

The proof sorts the heads of marked edges by their marked height modulo `τ`: the marked height
`ht u` is the number of marked edges on the walk from `u` to its root. Along a marked edge the
height drops by one, so `τ` marked edges on one chain have heads in all `τ` residue classes; `Q` is
the smallest class.
-/

namespace MergeDepth

open Finset

section Covering

/-- A lineage forest on `ℕ`: every node has at most one parent, at an earlier node. -/
structure Forest where
  nxt : ℕ → Option ℕ
  nxt_lt : ∀ u v, nxt u = some v → v < u

variable (F : Forest) (M : Finset ℕ)

/-- A list is a *chain* of the forest if each node is followed by its parent. -/
def IsChain : List ℕ → Prop
  | [] => True
  | [_] => True
  | u :: v :: π => F.nxt u = some v ∧ IsChain (v :: π)

/-- The number of marked edges crossed by a chain: the nodes other than the last that lie in `M`. -/
def crossed : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | u :: v :: π => (if u ∈ M then 1 else 0) + crossed (v :: π)

/-- The marked height of a node: the number of marked edges on the walk to its root. -/
def ht (u : ℕ) : ℕ :=
  match h : F.nxt u with
  | none => 0
  | some v => (if u ∈ M then 1 else 0) + ht v
termination_by u
decreasing_by exact F.nxt_lt u v h

theorem ht_of_some {u v : ℕ} (h : F.nxt u = some v) :
    ht F M u = (if u ∈ M then 1 else 0) + ht F M v := by
  rw [ht]
  split
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)
  · rename_i v' h'
    rw [h] at h'
    cases h'
    rfl

/-- The heads of the marked edges. -/
def heads : Finset ℕ := M.biUnion fun u => (F.nxt u).toFinset

theorem card_heads_le : (heads F M).card ≤ M.card := by
  unfold heads
  refine (card_biUnion_le).trans ?_
  calc ∑ u ∈ M, (F.nxt u).toFinset.card ≤ ∑ _u ∈ M, 1 := by
        refine sum_le_sum fun u _ => ?_
        cases F.nxt u <;> simp
    _ = M.card := by simp

/-- The heads of marked edges whose marked height is `j` modulo `τ`. -/
def headClass (τ j : ℕ) : Finset ℕ :=
  (heads F M).filter fun v => ht F M v % τ = j

/-- The classes partition the heads, so the smallest has at most `|M| / τ` elements. -/
theorem exists_small_class {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ j < τ, τ * (headClass F M τ j).card ≤ M.card := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : ∑ j ∈ range τ, (headClass F M τ j).card = (heads F M).card := by
    unfold headClass
    rw [← card_biUnion]
    · congr 1
      ext v
      simp only [mem_biUnion, mem_range, mem_filter]
      constructor
      · rintro ⟨j, -, hv, -⟩
        exact hv
      · intro hv
        exact ⟨_, Nat.mod_lt _ (by omega), hv, rfl⟩
    · intro i _ j _ hij
      refine disjoint_left.mpr fun v hv hv' => hij ?_
      exact (mem_filter.mp hv).2.symm.trans (mem_filter.mp hv').2
  have hlt : τ * M.card < τ * (heads F M).card := by
    calc τ * M.card = ∑ _j ∈ range τ, M.card := by simp
      _ < ∑ j ∈ range τ, τ * (headClass F M τ j).card := by
          refine sum_lt_sum_of_nonempty ⟨0, by simp; omega⟩ fun j hj => hcon j (mem_range.mp hj)
      _ = τ * (heads F M).card := by rw [← mul_sum, hsum]
  have := card_heads_le F M
  have : M.card < (heads F M).card := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- Along a chain, the marked height of the first node is that of the last plus the number of
marked edges crossed. -/
theorem ht_chain : ∀ (π : List ℕ) (u : ℕ), IsChain F (u :: π) →
    ht F M u = crossed M (u :: π) + ht F M ((u :: π).getLast (by simp))
  | [], u, _ => by simp [crossed]
  | v :: π, u, h => by
    obtain ⟨huv, hπ⟩ := h
    rw [ht_of_some F M huv, ht_chain π v hπ]
    simp only [crossed, List.getLast_cons_cons]
    ring

/-- Along a chain, every value `h` with `ht(last) ≤ h < ht(first)` is the marked height of the head
of a marked edge of the chain, met after the first node. -/
theorem exists_head_of_height : ∀ (π : List ℕ) (u : ℕ), IsChain F (u :: π) →
    ∀ h, ht F M ((u :: π).getLast (by simp)) ≤ h → h < ht F M u →
      ∃ v ∈ π, v ∈ heads F M ∧ ht F M v = h
  | [], u, _, h, h1, h2 => by simp at h1; omega
  | v :: π, u, hc, h, h1, h2 => by
    obtain ⟨huv, hπ⟩ := hc
    rw [ht_of_some F M huv] at h2
    simp only [List.getLast_cons_cons] at h1
    by_cases hlt : h < ht F M v
    · obtain ⟨x, hx, hxh, hxe⟩ := exists_head_of_height π v hπ h h1 hlt
      exact ⟨x, List.mem_cons_of_mem _ hx, hxh, hxe⟩
    · have hu : u ∈ M := by
        by_contra hu
        simp [hu] at h2
        omega
      have hv : ht F M v = h := by simp [hu] at h2; omega
      refine ⟨v, List.mem_cons_self .., ?_, hv⟩
      exact mem_biUnion.mpr ⟨u, hu, by simp [huv]⟩

/-- **The covering lemma.** For `τ ≥ 1` there is a set `Q` of heads of marked edges with
`τ |Q| ≤ |M|` such that every chain whose nodes after the first avoid `Q` crosses fewer than `τ`
marked edges. -/
theorem covering {τ : ℕ} (hτ : 1 ≤ τ) :
    ∃ Q : Finset ℕ, Q ⊆ heads F M ∧ τ * Q.card ≤ M.card ∧
      ∀ (u : ℕ) (π : List ℕ), IsChain F (u :: π) → (∀ v ∈ π, v ∉ Q) →
        crossed M (u :: π) < τ := by
  obtain ⟨j, hj, hcard⟩ := exists_small_class F M hτ
  refine ⟨headClass F M τ j, filter_subset _ _, hcard, fun u π hc hQ => ?_⟩
  by_contra hge
  push Not at hge
  have hht := ht_chain F M π u hc
  set a := ht F M ((u :: π).getLast (by simp))
  -- the heights `a, a + 1, …, a + τ - 1` are all heights of heads met after `u`
  -- one of them is `j` modulo `τ`
  set h := a + (j + τ - a % τ) % τ with hh
  have hlo : a ≤ h := Nat.le_add_right _ _
  have hhi : h < ht F M u := by
    have : (j + τ - a % τ) % τ < τ := Nat.mod_lt _ (by omega)
    omega
  have hmod : h % τ = j := by
    have ha := Nat.mod_lt a (show 0 < τ by omega)
    have e : a % τ + (j + τ - a % τ) = j + τ := by omega
    rw [hh, Nat.add_mod_mod, ← Nat.mod_add_mod, e, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  obtain ⟨v, hv, hvh, hve⟩ := exists_head_of_height F M π u hc h hlo hhi
  exact hQ v hv (mem_filter.mpr ⟨hvh, by rw [hve, hmod]⟩)

end Covering

end MergeDepth

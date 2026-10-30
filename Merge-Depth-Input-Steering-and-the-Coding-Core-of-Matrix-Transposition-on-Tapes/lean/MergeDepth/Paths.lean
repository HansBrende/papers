import BoundedNesting.Rigidity

/-!
# Paths of a linear network, edge counts and cold depth

Paths of a linear network are the lists `paths t` of the eighth paper's library: `t = t₀ → t₁ → ⋯`
along out-edges. This file adds the cons characterisation of paths and of `Γ`-freeness, the number
`rCount Rr π` of edges of a path in a relation `Rr` (the deep hops, in the application), and the
**cold-depth bound** `length_le_of_cold`: if every `Γ₀`-free path without `Rr`-edges has at most `D`
vertices, every `Γ₀`-free path with `ρ` such edges has at most `(ρ + 1) D` vertices.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {F : Type*} [Field F] {L m : ℕ}

theorem singleton_mem_paths (net : LinNet F L m) (t : ℕ) : [t] ∈ net.paths t := by
  rw [LinNet.paths_eq]
  exact mem_insert_self _ _

theorem head_eq_of_mem_paths {net : LinNet F L m} {t u : ℕ} {π : List ℕ}
    (h : (u :: π) ∈ net.paths t) : u = t := by
  obtain ⟨π', hπ'⟩ := net.mem_paths_head h
  exact (List.cons.inj hπ').1

theorem cons_cons_mem_paths {net : LinNet F L m} {t s : ℕ} {π : List ℕ} :
    (t :: s :: π) ∈ net.paths t ↔ s ∈ net.out t ∧ (s :: π) ∈ net.paths s := by
  constructor
  · intro h
    rw [LinNet.paths_eq] at h
    rcases mem_insert.mp h with h | h
    · simp at h
    · obtain ⟨s', hs', himg⟩ := mem_biUnion.mp h
      obtain ⟨ρ, hρ, he⟩ := mem_image.mp himg
      obtain ⟨ρ', rfl⟩ := net.mem_paths_head hρ
      simp only [List.cons.injEq, true_and] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hs', hρ⟩
  · rintro ⟨hs, hπ⟩
    rw [LinNet.paths_eq]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨s, hs, mem_image.mpr ⟨_, hπ, rfl⟩⟩)

theorem gfree_singleton (Γ : Finset ℕ) (t : ℕ) : LinNet.GFree Γ [t] := fun v hv => by simp at hv

theorem gfree_cons_cons {Γ : Finset ℕ} {t s : ℕ} {π : List ℕ} :
    LinNet.GFree Γ (t :: s :: π) ↔ s ∉ Γ ∧ LinNet.GFree Γ (s :: π) := by
  simp only [LinNet.GFree, List.tail_cons, List.mem_cons]
  constructor
  · intro h
    exact ⟨h s (Or.inl rfl), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hs, h⟩ v (rfl | hv)
    · exact hs
    · exact h v hv

theorem gfree_mono {Γ Γ' : Finset ℕ} (hΓ : Γ ⊆ Γ') {π : List ℕ} (h : LinNet.GFree Γ' π) :
    LinNet.GFree Γ π :=
  fun v hv hvΓ => h v hv (hΓ hvΓ)

/-- The number of edges of a path in the relation `Rr`. -/
def rCount (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | u :: v :: π => (if Rr u v then 1 else 0) + rCount Rr (v :: π)

/-- The cold-depth bound with a prefix of `a` edges already used. -/
theorem length_le_of_cold_aux (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr]
    (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D) :
    ∀ (π : List ℕ) (t a : ℕ), π ∈ net.paths t → LinNet.GFree Γ₀ π →
      (∀ ρ, ρ ∈ net.paths t → LinNet.GFree Γ₀ ρ → rCount Rr ρ = 0 → a + ρ.length ≤ D) →
      a + π.length ≤ (rCount Rr π + 1) * D
  | [], t, a, h, _, _ => by
    obtain ⟨π', hπ'⟩ := net.mem_paths_head h
    simp at hπ'
  | [u], t, a, h, _, hpre => by
    have := hpre [u] h (gfree_singleton _ _) rfl
    simpa [rCount] using this
  | u :: s :: π, t, a, h, hfree, hpre => by
    have hu := head_eq_of_mem_paths h
    subst hu
    obtain ⟨hs, hπ⟩ := cons_cons_mem_paths.mp h
    obtain ⟨hsΓ, hfree'⟩ := gfree_cons_cons.mp hfree
    by_cases hR : Rr u s
    · -- an `Rr`-edge: the prefix ends here and a new one starts at `s`
      have h1 := hpre [u] (singleton_mem_paths _ _) (gfree_singleton _ _) rfl
      have h2 := length_le_of_cold_aux net Rr Γ₀ D hcold (s :: π) s 0 hπ hfree'
        (fun ρ hρ hρf hρR => by simpa using hcold s ρ hρ hρf hρR)
      simp only [rCount, hR, ↓reduceIte, List.length_cons] at h1 h2 ⊢
      nlinarith
    · -- no `Rr`-edge: the prefix grows by one edge
      have h2 := length_le_of_cold_aux net Rr Γ₀ D hcold (s :: π) s (a + 1) hπ hfree'
        (fun ρ hρ hρf hρR => by
          obtain ⟨ρ', rfl⟩ := net.mem_paths_head hρ
          have := hpre (u :: s :: ρ') (cons_cons_mem_paths.mpr ⟨hs, hρ⟩)
            (gfree_cons_cons.mpr ⟨hsΓ, hρf⟩) (by simp [rCount, hR, hρR])
          simp only [List.length_cons] at this ⊢
          omega)
      simp only [rCount, hR, ↓reduceIte, zero_add, List.length_cons] at h2 ⊢
      omega

/-- **Cold depth.** If every `Γ₀`-free path without `Rr`-edges has at most `D` vertices, every
`Γ₀`-free path with `ρ` such edges has at most `(ρ + 1) D` vertices. -/
theorem length_le_of_cold (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr]
    (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D)
    {t : ℕ} {π : List ℕ} (h : π ∈ net.paths t) (hfree : LinNet.GFree Γ₀ π) :
    π.length ≤ (rCount Rr π + 1) * D := by
  simpa using length_le_of_cold_aux net Rr Γ₀ D hcold π t 0 h hfree
    (fun ρ hρ hρf hρR => by simpa using hcold t ρ hρ hρf hρR)

end MergeDepth

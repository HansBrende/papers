import MergeDepth.Charging

/-!
# Lemma 3.3(a) without a length bound

The vertices decrease along every path of a linear network, so a path from `t` has at most `t + 1`
vertices (`length_le_of_mem_paths`). Hence the cone set `I_Γ(u)` of all positions read at the ends
of `Γ`-free paths from `u` (`coneI`) is a ball set of finite radius, and the path sums vanish
outside it (`C_eq_zero_of_not_mem_coneI`). `expansion_cone` is Lemma 3.3(a) as stated: `P_tpos = R + S`
with `rank R ≤ rank(E_Γ) + |X|`, row `ℓ` of `S` zero for `ℓ ∈ X` and otherwise supported in the
union of the cone sets of the unrevealed output vertices of `ℓ`, with no common length bound.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m : ℕ}

/-- **Paths are short.** A path from `t` has at most `t + 1` vertices. -/
theorem length_le_of_mem_paths (net : LinNet F L m) :
    ∀ t π, π ∈ net.paths t → π.length ≤ t + 1 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro π hπ
    obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
    cases π' with
    | nil => simp
    | cons s ρ =>
      obtain ⟨hs, hρ⟩ := cons_cons_mem_paths.mp hπ
      have := ih s (net.out_lt t s hs) _ hρ
      have hst := net.out_lt t s hs
      simp only [List.length_cons] at this ⊢
      omega

open Classical in
/-- The cone set `I_Γ(u)`: the positions read at the ends of the `Γ`-free paths from `u`. -/
noncomputable def coneI (net : LinNet F L m) (Γ : Finset ℕ) (u : ℕ) : Finset (Fin L) :=
  univ.filter fun j => ∃ π ∈ net.paths u, LinNet.GFree Γ π ∧ net.rd (π.getLastD u) = some j

theorem reach_subset_coneI (net : LinNet F L m) (Γ : Finset ℕ) (D u : ℕ) :
    net.reach Γ D u ⊆ coneI net Γ u := by
  classical
  intro j hj
  simp only [LinNet.reach, coneI, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, hfree, -, hrd⟩ := hj
  exact ⟨π, hπ, hfree, hrd⟩

theorem coneI_subset_reach (net : LinNet F L m) (Γ : Finset ℕ) {D u : ℕ} (hD : u ≤ D) :
    coneI net Γ u ⊆ net.reach Γ D u := by
  classical
  intro j hj
  simp only [LinNet.reach, coneI, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, hfree, hrd⟩ := hj
  exact ⟨π, hπ, hfree, (length_le_of_mem_paths net u π hπ).trans (by omega), hrd⟩

/-- The path sums vanish outside the cone set. -/
theorem C_eq_zero_of_not_mem_coneI (net : LinNet F L m) (Γ : Finset ℕ) (u : ℕ) (j : Fin L)
    (hj : j ∉ coneI net Γ u) : net.C Γ u j = 0 :=
  C_eq_zero_of_short net Γ u u (fun π hπ _ => length_le_of_mem_paths net u π hπ) j
    fun h => hj (reach_subset_coneI net Γ u u h)

open Classical in
/-- **Lemma 3.3(a).** For a transposing linear network, `P_tpos = R + S` with
`rank R ≤ rank(E_Γ) + |X|`, where row `ℓ` of `S` is zero for `ℓ ∈ X` and is otherwise supported in
the union of the cone sets `I_Γ(u)` of the output vertices `u ∉ Γ` of `ℓ`. -/
theorem expansion_cone (net : LinNet F L m) (tout : Fin L → Finset ℕ)
    (φ : Fin L → ℕ → Fin m → F) (φc : Fin L → F) (tpos : Fin L → Fin L) (Γ : Finset ℕ)
    (X : Finset (Fin L))
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val w u = w (tpos ℓ)) :
    ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
      R.rank ≤ finrank F (LinearMap.range (revealed net Γ)) + X.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ℓ ∉ X ∧ ∃ u ∈ tout ℓ, u ∉ Γ ∧ j ∈ coneI net Γ u := by
  obtain ⟨R₀, hP, hR₀⟩ := rigidity_core_rev net tout φ φc tpos Γ htrans
  set S₀ : Matrix (Fin L) (Fin L) F :=
    Matrix.of (fun ℓ j => ∑ u ∈ (tout ℓ).filter (· ∉ Γ), φ ℓ u ⬝ᵥ net.C Γ u j)
  let S : Matrix (Fin L) (Fin L) F := Matrix.of fun ℓ j => if ℓ ∈ X then 0 else S₀ ℓ j
  let Δ : Matrix (Fin L) (Fin L) F := Matrix.of fun ℓ j => if ℓ ∈ X then S₀ ℓ j else 0
  refine ⟨R₀ + Δ, S, ?_, ?_, ?_⟩
  · rw [hP]
    ext ℓ j
    simp only [Matrix.add_apply, S, Δ, Matrix.of_apply]
    split_ifs <;> ring
  · calc (R₀ + Δ).rank ≤ R₀.rank + Δ.rank := rank_add_le' _ _
      _ ≤ _ := Nat.add_le_add hR₀ (rank_le_card_rows Δ X fun ℓ j h => by
          by_contra hX
          simp [Δ, hX] at h)
  · intro ℓ j hS
    have hX : ℓ ∉ X := fun hX => hS (by simp [S, hX])
    refine ⟨hX, ?_⟩
    by_contra hj
    push Not at hj
    apply hS
    simp only [S, Matrix.of_apply, hX, ↓reduceIte, S₀]
    refine Finset.sum_eq_zero fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
    rw [C_eq_zero_of_not_mem_coneI net Γ u j (hj u hu1 hu2)]
    simp

end MergeDepth

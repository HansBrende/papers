import TransposeFollowup.MonotoneOverlapGraph

/-! Counting the outside boundary from expansion on both bipartite sides.
For classes of even size2h, (1+epsilon)-neighbor expansion up to h yields
ordinary vertex expansion epsilon/2 on sets of size at most2h. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

noncomputable def bipartiteRight {n : ℕ} (edges : Finset (Fin n × Fin n))
    (A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ i ∈ A, (i, j) ∈ edges)

noncomputable def bipartiteLeft {n : ℕ} (edges : Finset (Fin n × Fin n))
    (B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ j ∈ B, (i, j) ∈ edges)

theorem mem_bipartiteRight {n : ℕ} (edges : Finset (Fin n × Fin n))
    (A : Finset (Fin n)) (j : Fin n) :
    j ∈ bipartiteRight edges A ↔ ∃ i ∈ A, (i, j) ∈ edges := by simp [bipartiteRight]

theorem mem_bipartiteLeft {n : ℕ} (edges : Finset (Fin n × Fin n))
    (B : Finset (Fin n)) (i : Fin n) :
    i ∈ bipartiteLeft edges B ↔ ∃ j ∈ B, (i, j) ∈ edges := by simp [bipartiteLeft]

theorem bipartiteRight_mono {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Monotone (bipartiteRight edges) := by
  intro A B hAB j hj
  obtain ⟨i, hi, he⟩ := (mem_bipartiteRight edges A j).mp hj
  exact (mem_bipartiteRight edges B j).mpr ⟨i, hAB hi, he⟩

theorem bipartiteLeft_mono {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Monotone (bipartiteLeft edges) := by
  intro A B hAB i hi
  obtain ⟨j, hj, he⟩ := (mem_bipartiteLeft edges A i).mp hi
  exact (mem_bipartiteLeft edges B i).mpr ⟨j, hAB hj, he⟩

theorem large_side_boundary {V W : Type*} [DecidableEq V] [DecidableEq W]
    (N : Finset V → Finset W) (hmono : Monotone N) (h : ℕ) (eps : ℝ)
    (hexp : ∀ A, A.card ≤ h → (1 + eps) * A.card ≤ (N A).card)
    (A : Finset V) (B : Finset W) (hA : h ≤ A.card) (hB : B.card ≤ h) :
    eps * h ≤ ((N A \ B).card : ℝ) := by
  obtain ⟨C, hCA, hC⟩ := Finset.exists_subset_card_eq hA
  have he := hexp C (by omega)
  have hm : ((N C).card : ℝ) ≤ (N A).card := by
    exact_mod_cast Finset.card_le_card (hmono hCA)
  have hd : ((N A).card : ℝ) ≤ (N A \ B).card + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := N A) (t := B))
  have hb : (B.card : ℝ) ≤ h := by exact_mod_cast hB
  rw [hC] at he
  nlinarith

theorem two_sided_expansion_count {n h : ℕ} (edges : Finset (Fin n × Fin n))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hR : ∀ A : Finset (Fin n), A.card ≤ h →
      (1 + eps) * A.card ≤ (bipartiteRight edges A).card)
    (hL : ∀ B : Finset (Fin n), B.card ≤ h →
      (1 + eps) * B.card ≤ (bipartiteLeft edges B).card)
    (A B : Finset (Fin n)) (hab : A.card + B.card ≤ 2 * h) :
    eps / 2 * (A.card + B.card : ℕ) ≤
      ((bipartiteRight edges A \ B).card : ℝ) + (bipartiteLeft edges B \ A).card := by
  have htotal : (A.card : ℝ) + B.card ≤ 2 * h := by exact_mod_cast hab
  have hscale := mul_le_mul_of_nonneg_left htotal heps
  have hX : (0 : ℝ) ≤ (bipartiteRight edges A \ B).card := Nat.cast_nonneg _
  have hY : (0 : ℝ) ≤ (bipartiteLeft edges B \ A).card := Nat.cast_nonneg _
  push_cast
  by_cases ha : A.card ≤ h
  · by_cases hb : B.card ≤ h
    · have heA := hR A ha
      have heB := hL B hb
      have hdA : ((bipartiteRight edges A).card : ℝ) ≤
          (bipartiteRight edges A \ B).card + (B.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := bipartiteRight edges A) (t := B))
      have hdB : ((bipartiteLeft edges B).card : ℝ) ≤
          (bipartiteLeft edges B \ A).card + (A.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := bipartiteLeft edges B) (t := A))
      have hp : 0 ≤ eps * ((A.card : ℝ) + B.card) := mul_nonneg heps (by positivity)
      nlinarith
    · have hb := large_side_boundary (bipartiteLeft edges) (bipartiteLeft_mono edges)
        h eps hL B A (by omega) ha
      nlinarith
  · have ha := large_side_boundary (bipartiteRight edges) (bipartiteRight_mono edges)
      h eps hR A B (by omega) (by omega)
    nlinarith

end TransposeFollowup

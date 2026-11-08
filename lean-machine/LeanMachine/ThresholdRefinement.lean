import Mathlib

/-! # Common refinement of finite threshold sets

A finite threshold set `S_ref ⊆ [0, T]` containing `0` and `T` with `|S_ref| ≤ N_cells + 1`
partitions `[0, T)` into at most `N_cells` elementary half-open intervals `[a, b)` free of interior
thresholds. On each elementary interval every threshold predicate `t < s` (`min T s ∈ S_ref`) is
constant, and by pigeonhole some interval captures at least `|Q| / N_cells` elements of any finite
set `Q` mapped into `[0, T)`.
-/

namespace LeanMachine.ThresholdRefinement

open Finset
set_option autoImplicit false

/-- Strictly increasing enumeration of any `Finset ℕ` of cardinality `n`. -/
theorem exists_strictMono_equiv_of_finset :
    ∀ (n : ℕ) (s : Finset ℕ), s.card = n →
      ∃ f : Fin n → ℕ, StrictMono f ∧ (∀ i, f i ∈ s) ∧ (∀ x ∈ s, ∃ i, f i = x)
  | 0, s, hs => by
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun x hx => ?_⟩
    have := card_eq_zero.mp hs
    subst this
    exact absurd hx (notMem_empty x)
  | n + 1, s, hs => by
    have hne : s.Nonempty := card_pos.mp (by omega)
    let m := s.min' hne
    have hm : m ∈ s := s.min'_mem hne
    let s' := s.erase m
    have hs' : s'.card = n := by rw [card_erase_of_mem hm, hs]; omega
    obtain ⟨f', hf'_mono, hf'_mem, hf'_surj⟩ := exists_strictMono_equiv_of_finset n s' hs'
    let f : Fin (n + 1) → ℕ := Fin.cons m f'
    have hlt_m : ∀ j : Fin n, m < f' j := by
      intro j
      have hj_s' := hf'_mem j
      have hj_ne : f' j ≠ m := (mem_erase.mp hj_s').1
      have hj_le : m ≤ f' j := s.min'_le (f' j) (mem_erase.mp hj_s').2
      omega
    refine ⟨f, ?_, ?_, ?_⟩
    · intro a b hab
      refine Fin.cases ?_ (fun a' => ?_) a hab
      · intro hab0
        refine Fin.cases ?_ (fun b' _ => hlt_m b') b hab0
        intro h00; exact absurd h00 (lt_irrefl _)
      · intro hab_s
        refine Fin.cases ?_ (fun b' hab' => hf'_mono (Fin.succ_lt_succ_iff.mp hab')) b hab_s
        intro hs0; exact absurd hs0 (Nat.not_lt_zero _)
    · intro i
      exact Fin.cases hm (fun j => (mem_erase.mp (hf'_mem j)).2) i
    · intro x hx
      rcases eq_or_ne x m with rfl | hne_x
      · exact ⟨0, rfl⟩
      · obtain ⟨j, rfl⟩ := hf'_surj x (mem_erase.mpr ⟨hne_x, hx⟩)
        exact ⟨j.succ, rfl⟩

/-- Pigeonhole selection of one elementary interval `[a_*, b_*)` of the common refinement of
`S_ref ⊆ [0, T]`, on which every clamped threshold comparison `u < s` is constant. -/
theorem exists_refinement_cell {α : Type*} [DecidableEq α] {T N_cells : ℕ}
    (hT : 1 ≤ T) (S_ref : Finset ℕ) (h0_ref : 0 ∈ S_ref) (hT_ref : T ∈ S_ref)
    (hS_le_T : ∀ x ∈ S_ref, x ≤ T) (hS_card : S_ref.card ≤ N_cells + 1)
    (Q : Finset α) (u : α → ℕ) (hu_lt_T : ∀ q ∈ Q, u q < T) :
    ∃ (a_star b_star : ℕ),
      a_star < b_star ∧ b_star ≤ T ∧
      a_star ∈ S_ref ∧ b_star ∈ S_ref ∧
      (∀ x ∈ S_ref, ¬ (a_star < x ∧ x < b_star)) ∧
      Q.card ≤ N_cells * (Q.filter fun q => u q ∈ Ico a_star b_star).card ∧
      (∀ {u₁ u₂ : ℕ}, u₁ ∈ Ico a_star b_star → u₂ ∈ Ico a_star b_star →
        ∀ s : ℕ, min T s ∈ S_ref → (u₁ < s ↔ u₂ < s)) := by
  have hS_ge2 : 2 ≤ S_ref.card := by
    have hsub : ({0, T} : Finset ℕ) ⊆ S_ref :=
      insert_subset h0_ref (singleton_subset_iff.mpr hT_ref)
    have hc2 : ({0, T} : Finset ℕ).card = 2 := card_pair (by omega)
    exact hc2 ▸ card_le_card hsub
  let M_ref := S_ref.card - 1
  have hM_pos : 1 ≤ M_ref := by omega
  have hM_le_N : M_ref ≤ N_cells := by omega
  have hS_eq : S_ref.card = M_ref + 1 := by omega
  obtain ⟨f_ref, hf_mono, hf_mem, hf_surj⟩ := exists_strictMono_equiv_of_finset (M_ref + 1) S_ref hS_eq
  have hf0 : f_ref ⟨0, by omega⟩ = 0 := by
    obtain ⟨i, hi⟩ := hf_surj 0 h0_ref
    rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
    · have : i = ⟨0, by omega⟩ := Fin.ext h0; rwa [this] at hi
    · exfalso; have := hf_mono (show (⟨0, by omega⟩ : Fin (M_ref + 1)) < i from hpos); omega
  have hfM : f_ref ⟨M_ref, by omega⟩ = T := by
    obtain ⟨i, hi⟩ := hf_surj T hT_ref
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with heq | hlt
    · have : i = ⟨M_ref, by omega⟩ := Fin.ext heq; rwa [this] at hi
    · exfalso
      have hlt_f := hf_mono (show i < (⟨M_ref, by omega⟩ : Fin (M_ref + 1)) from hlt)
      have hle_T := hS_le_T _ (hf_mem ⟨M_ref, by omega⟩)
      omega
  have hno_inner : ∀ (r : Fin M_ref) (x : ℕ), x ∈ S_ref →
      ¬ (f_ref ⟨r.1, by omega⟩ < x ∧ x < f_ref ⟨r.1 + 1, by omega⟩) := by
    intro r x hx ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ := hf_surj x hx
    have hi1 : r.1 < i.1 := by
      by_contra hle; push Not at hle
      have := hf_mono.monotone (show i ≤ ⟨r.1, by omega⟩ from hle); omega
    have hi2 : i.1 < r.1 + 1 := by
      by_contra hge; push Not at hge
      have := hf_mono.monotone (show (⟨r.1 + 1, by omega⟩ : Fin (M_ref + 1)) ≤ i from hge); omega
    omega
  let CellOf : Fin M_ref → Finset α := fun r =>
    Q.filter fun q => u q ∈ Ico (f_ref ⟨r.1, by omega⟩) (f_ref ⟨r.1 + 1, by omega⟩)
  have hQ_cov : Q ⊆ (univ : Finset (Fin M_ref)).biUnion CellOf := by
    intro q hq
    have huT : u q < T := hu_lt_T q hq
    let I_le := (univ : Finset (Fin (M_ref + 1))).filter fun i => f_ref i ≤ u q
    have hne_le : I_le.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
    let i_max := I_le.max' hne_le
    have hi_le : f_ref i_max ≤ u q := (mem_filter.mp (I_le.max'_mem hne_le)).2
    have hi_lt : i_max.1 < M_ref := by
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ i_max.2) with heq | hlt
      · exfalso; have : i_max = ⟨M_ref, by omega⟩ := Fin.ext heq; rw [this, hfM] at hi_le; omega
      · exact hlt
    have hu_lt_next : u q < f_ref ⟨i_max.1 + 1, by omega⟩ := by
      by_contra hge; push Not at hge
      have hmem_s : (⟨i_max.1 + 1, by omega⟩ : Fin (M_ref + 1)) ∈ I_le :=
        mem_filter.mpr ⟨mem_univ _, hge⟩
      have hle_max : i_max.1 + 1 ≤ i_max.1 := I_le.le_max' _ hmem_s
      omega
    exact mem_biUnion.mpr ⟨⟨i_max.1, hi_lt⟩, mem_univ _,
      mem_filter.mpr ⟨hq, mem_Ico.mpr ⟨hi_le, hu_lt_next⟩⟩⟩
  have hsum_cells : Q.card ≤ ∑ r : Fin M_ref, (CellOf r).card :=
    (card_le_card hQ_cov).trans card_biUnion_le
  have hne_M : (univ : Finset (Fin M_ref)).Nonempty := ⟨⟨0, hM_pos⟩, mem_univ _⟩
  obtain ⟨r_star, _, hmax_cell⟩ := exists_max_image (univ : Finset (Fin M_ref))
    (fun r => (CellOf r).card) hne_M
  have hQ_le_max : Q.card ≤ M_ref * (CellOf r_star).card := by
    calc Q.card
        ≤ ∑ r : Fin M_ref, (CellOf r).card := hsum_cells
      _ ≤ ∑ _r : Fin M_ref, (CellOf r_star).card := sum_le_sum fun r _ => hmax_cell r (mem_univ r)
      _ = M_ref * (CellOf r_star).card := by simp
  let a_star := f_ref ⟨r_star.1, by omega⟩
  let b_star := f_ref ⟨r_star.1 + 1, by omega⟩
  have hab_lt : a_star < b_star :=
    hf_mono (show (⟨r_star.1, by omega⟩ : Fin (M_ref + 1)) < ⟨r_star.1 + 1, by omega⟩ by simp)
  have hb_le_T : b_star ≤ T := hS_le_T _ (hf_mem ⟨r_star.1 + 1, by omega⟩)
  refine ⟨a_star, b_star, hab_lt, hb_le_T,
    hf_mem ⟨r_star.1, by omega⟩, hf_mem ⟨r_star.1 + 1, by omega⟩,
    hno_inner r_star,
    hQ_le_max.trans (Nat.mul_le_mul_right _ hM_le_N), ?_⟩
  intro u₁ u₂ hu₁ hu₂ s hs_ref
  obtain ⟨h1a, h1b⟩ := mem_Ico.mp hu₁
  obtain ⟨h2a, h2b⟩ := mem_Ico.mp hu₂
  let y := min T s
  have hy_no := hno_inner r_star y hs_ref
  have hu₁_y : u₁ < s ↔ u₁ < y := by dsimp [y]; omega
  have hu₂_y : u₂ < s ↔ u₂ < y := by dsimp [y]; omega
  rw [hu₁_y, hu₂_y]
  change ¬ (a_star < y ∧ y < b_star) at hy_no
  omega

end LeanMachine.ThresholdRefinement

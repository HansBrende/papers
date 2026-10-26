import BoundedNesting.MSum

/-!
# Theorem M: averaging over the residue and the offsets

`sum_offsets_cut_le`: at one residue `ρ`, `K` times the total size of the cuts over all offsets is at most
`K^(2q)` times an explicit bound (`q ≥ 1`), which collects the cost of the edges at line times, of the
descents, of the chords (the exchange lemmas (X1)–(X3)) and of the hops of the bounded walks ((X4),
(X5)).

`sum_cut_le`: summed over the residues `ρ < W q`, where a cell is a level-`i` line for `W q / W i`
residues (`sum_rho_lineT`).
-/

namespace BoundedNesting

open Finset

/-! ### Lines over the residues -/

/-- The residues `ρ < M` congruent to `a < w` modulo `w ∣ M` number `M / w`. -/
theorem card_residue {w M a : ℕ} (hw : 0 < w) (ha : a < w) (hM : w ∣ M) :
    ((range M).filter fun ρ => ρ % w = a).card = M / w := by
  have e : (range M).filter (fun ρ => ρ % w = a) = (range (M / w)).image (fun m => a + w * m) := by
    ext ρ
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨ρ / w, (Nat.div_lt_iff_lt_mul hw).mpr (by rwa [Nat.div_mul_cancel hM]), ?_⟩
      rw [← h2]
      exact Nat.mod_add_div ρ w
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]⟩
      obtain ⟨c, rfl⟩ := hM
      rw [Nat.mul_div_cancel_left _ hw] at hm
      nlinarith
  rw [e, card_image_of_injective _ (fun m m' h => Nat.eq_of_mul_eq_mul_left hw
    (Nat.add_left_cancel h)), card_range]

section Lines

variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {T : ℕ}

theorem lineAt_iff_mod (hW : ∀ i, 2 ≤ W i) {ρ i : ℕ} {c : ℤ} :
    LineAt W ρ i c ↔ ρ % W i = (c % (W i : ℤ)).toNat := by
  unfold LineAt IsLine res
  have h0 : 0 ≤ c % (W i : ℤ) := Int.emod_nonneg _ (by have := hW i; omega)
  constructor
  · intro h
    rw [h]
    exact (Int.toNat_natCast _).symm
  · intro h
    rw [h, Int.toNat_of_nonneg h0]

/-- A cell is a level-`i` line for `M / W i` of the residues `ρ < M`. -/
theorem card_rho_lineAt (hW : ∀ i, 2 ≤ W i) {i M : ℕ} (hM : W i ∣ M) (c : ℤ) :
    ((range M).filter fun ρ => LineAt W ρ i c).card = M / W i := by
  have hw : 0 < W i := by have := hW i; omega
  rw [filter_congr (fun ρ _ => lineAt_iff_mod hW)]
  refine card_residue hw ?_ hM
  have h0 : 0 ≤ c % (W i : ℤ) := Int.emod_nonneg _ (by omega)
  exact (Int.toNat_lt h0).mpr (Int.emod_lt_of_pos _ (by omega))

/-- **Averaging the lines.** Over the residues `ρ < M`, the level-`i` line times number `T (M / W i)`
in all. -/
theorem sum_rho_lineT (hW : ∀ i, 2 ≤ W i) {i M : ℕ} (hM : W i ∣ M) :
    ∑ ρ ∈ range M, (lineT x0 W ρ T i).card = T * (M / W i) := by
  unfold lineT
  rw [sum_card_filter_comm (range M) (range T) (fun ρ t => LineAt W ρ i (x0 t)),
    sum_congr rfl fun t _ => card_rho_lineAt hW hM (x0 t), sum_const, card_range, smul_eq_mul]

theorem Zt_eq_lineT {ρ : ℕ} : Zt x0 W ρ T = lineT x0 W ρ T 0 := rfl

theorem card_incT_zero {ρ : ℕ} : (incT x0 W ρ T 0).card = T := by
  simp [incT]

/-- At positive levels, the increment times follow line times. -/
theorem card_incT_le {ρ i : ℕ} (hi : i ≠ 0) : (incT x0 W ρ T i).card ≤ (lineT x0 W ρ T i).card := by
  unfold incT
  simp only [hi, ↓reduceIte]
  refine card_le_card_of_injOn (fun s => s - 1) (fun s hs => ?_) (fun s hs s' hs' h => ?_)
  · obtain ⟨h1, -, h3⟩ := mem_filter.mp (Finset.mem_coe.mp hs)
    exact Finset.mem_coe.mpr
      (mem_filter.mpr ⟨mem_range.mpr (show s - 1 < T by have := mem_range.mp h1; omega), h3⟩)
  · obtain ⟨-, h2, -⟩ := mem_filter.mp (Finset.mem_coe.mp hs)
    obtain ⟨-, h2', -⟩ := mem_filter.mp (Finset.mem_coe.mp hs')
    simp only at h
    omega

end Lines

/-! ### The cost at one residue -/

section PerResidue

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ} {K₀ K : ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

include hW hdiv in
/-- The growth of the counters of one level along the chords of that level. -/
theorem sum_chord_level_le (i : ℕ) (ρ : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T ∧ P e),
      (lcnt x0 W ρ i e.2 - lcnt x0 W ρ i e.1) ≤ (W i - 1) * (incT x0 W ρ T i).card := by
  refine le_trans (sum_le_sum_of_subset fun e he => ?_) (sum_chord_growth_le hW hdiv i)
  obtain ⟨h1, h2, -⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨h1, h2⟩

open Classical in
include hx0 hW hdiv in
/-- **The cost at one residue**, summed over the offsets and multiplied by `K` (for `q ≥ 1`). -/
theorem sum_offsets_cut_le (hq : 1 ≤ q) (hK₀ : 0 < K₀) (hK : 0 < K) (hA : A.Valid T)
    (hβ : StrictMono β) {k h : ℕ} (win : ι → Fin q) (hwin1 : ∀ F, β (win F) ≤ lam (A.d F))
    (hwin2 : ∀ F, lam (A.d F) ≤ β (win F) + h)
    (hdegA : ∀ t, ((A.H.image fun η => η.2).filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 * k)
    (ρ : ℕ) :
    K * ∑ ω ∈ offsets K₀ K q, ((cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card) ≤
      K ^ q * K ^ q * (K * K₀ * (4 + 2 * k) * (Zt x0 W ρ T).card + K * T +
        K₀ * ∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card + K * (W 0 - 1) * T +
        K₀ * ∑ j : Fin q, (W (j.val + 1) - 1) * (lineT x0 W ρ T (j.val + 1)).card +
        K₀ * ∑ j : Fin q, (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card +
        K * K₀ * N * ∑ j : Fin q, (lineT x0 W ρ T (j.val + 1)).card * 2 ^ (β j + h + 1) +
        K₀ * N * 2 ^ (h + 2) * ∑ F, A.d F) := by
  have hPQ : K ^ q = K * K ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  -- the cut at each offset
  have hZ : ∀ ω ∈ offsets K₀ K q,
      (cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card ≤
        (4 + 2 * k) * (Zt x0 W ρ T).card +
        ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
          mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)).card +
        ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
          mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1).card +
        (A.H.filter fun η => η.2.1 ∉ Zt x0 W ρ T ∧ η.2.2 ∉ Zt x0 W ρ T ∧
          mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.2 ≤
            mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.1).card := by
    intro ω _
    have h1 := card_cut_le (x0 := x0) (W := W) (ρ := ρ) (A := A) (T := T) (β := β) (K₀ := K₀)
      (K := K) ω
    have h2 := card_ZS_le (x0 := x0) (W := W) (ρ := ρ) (T := T)
    have h3 := card_ZH_le (x0 := x0) (W := W) (ρ := ρ) (A := A) (T := T) hdegA
    nlinarith
  -- the chords
  have hC := sum_chord_le (A := A) (β := β) hx0 hW hdiv (ρ := ρ) (T := T) hK₀ hK
  have hC0 := sum_chord_level_le (x0 := x0) (T := T) hW hdiv 0 ρ
    (fun e => chordLevel x0 W ρ q e.1 e.2 = 0)
  rw [card_incT_zero] at hC0
  have hCd : ∀ j : Fin q, ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T ∧
      chordLevel x0 W ρ q e.1 e.2 = j.val + 1),
      (lcnt x0 W ρ (j.val + 1) e.2 - lcnt x0 W ρ (j.val + 1) e.1) ≤
        (W (j.val + 1) - 1) * (lineT x0 W ρ T (j.val + 1)).card := fun j =>
    (sum_chord_level_le (x0 := x0) (T := T) hW hdiv (j.val + 1) ρ
      (fun e => chordLevel x0 W ρ q e.1 e.2 = j.val + 1)).trans
      (Nat.mul_le_mul_left _ (card_incT_le (Nat.succ_ne_zero _)))
  have hCe : ∀ j : Fin q, ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T ∧
      chordLevel x0 W ρ q e.1 e.2 < j.val + 1), (nev A β j e.2 - nev A β j e.1) ≤
        (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card := fun j =>
    sum_chord_events_le (ρ := ρ) (T := T) hx0 hW hdiv j
  -- the hops of the bounded walks
  have hH := sum_ahop_le (K₀ := K₀) hx0 hW hdiv (ρ := ρ) hK hA win hwin1
  have hLV := card_lineVisit_le (x0 := x0) (W := W) (ρ := ρ) hA win hwin2
  have hAE := sum_ahop_events_le hA hβ win hwin2
  have hD := sum_desc_le (A := A) (β := β) hx0 hW hdiv (ρ := ρ) (T := T) hK₀ hK
  rw [card_offsets] at hH
  calc K * ∑ ω ∈ offsets K₀ K q, ((cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card)
      ≤ K * (K₀ * (K ^ q * K ^ q) * ((4 + 2 * k) * (Zt x0 W ρ T).card) +
          (T * (K ^ q * K ^ q) + (∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card) *
            (K₀ * (K ^ q * K ^ (q - 1)))) +
          ((K ^ q * K ^ q) * ((W 0 - 1) * T) +
            (K₀ * (K ^ (q - 1) * K ^ q)) *
              ∑ j : Fin q, (W (j.val + 1) - 1) * (lineT x0 W ρ T (j.val + 1)).card +
            (K₀ * (K ^ q * K ^ (q - 1))) *
              ∑ j : Fin q, (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card) +
          (K₀ * (K ^ q * K ^ q) *
              (N * ∑ j : Fin q, (lineT x0 W ρ T (j.val + 1)).card * 2 ^ (β j + h + 1)) +
            (K₀ * (K ^ q * K ^ (q - 1))) * (N * 2 ^ (h + 2) * ∑ F, A.d F))) := by
        refine Nat.mul_le_mul_left _ ?_
        refine (sum_le_sum hZ).trans ?_
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, card_offsets, smul_eq_mul]
        refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl ?_) ?_) ?_
        · rw [sum_mul]
          exact hD
        · refine hC.trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hC0) ?_) ?_)
          · rw [mul_sum]
            exact sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hCd j)
          · rw [mul_sum]
            exact sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hCe j)
        · refine hH.trans (Nat.add_le_add (Nat.mul_le_mul_left _ (hLV.trans ?_)) ?_)
          · rw [mul_sum]
            refine sum_le_sum fun j _ => ?_
            calc (lineT x0 W ρ T (j.val + 1)).card * (N * (2 ^ (β j + h + 1) - 1))
                ≤ (lineT x0 W ρ T (j.val + 1)).card * (N * 2 ^ (β j + h + 1)) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
              _ = N * ((lineT x0 W ρ T (j.val + 1)).card * 2 ^ (β j + h + 1)) := by ring
          · rw [← mul_sum]
            exact Nat.mul_le_mul_left _ hAE
    _ = _ := by
        rw [hPQ]
        ring

end PerResidue

/-! ### Summing over the residues -/

/-- The bound of `sum_cut_le`, as a function of the parameters and of the sums `Sev` (events),
`SWev` (events weighted by widths), `SL` (line visits weighted by overlaps) and `SD` (heights). -/
def costB (K K₀ k T Wq W0 q N h Sev SWev SL SD : ℕ) : ℕ :=
  K * K₀ * (4 + 2 * k) * (T * (Wq / W0)) + Wq * (K * T) + Wq * (K₀ * Sev) + Wq * (K * (W0 - 1) * T) +
    K₀ * (q * (T * Wq)) + Wq * (K₀ * SWev) + K * K₀ * N * (T * SL) + Wq * (K₀ * N * 2 ^ (h + 2) * SD)

section AllResidues

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ} {K₀ K : ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

open Classical in
include hx0 hW hdiv in
/-- **The total cost** over all residues `ρ < W q` and offsets, multiplied by `K` (for `q ≥ 1`). -/
theorem sum_cut_le (hq : 1 ≤ q) (hK₀ : 0 < K₀) (hK : 0 < K) (hA : A.Valid T)
    (hβ : StrictMono β) {k h : ℕ} (win : ι → Fin q) (hwin1 : ∀ F, β (win F) ≤ lam (A.d F))
    (hwin2 : ∀ F, lam (A.d F) ≤ β (win F) + h)
    (hdegA : ∀ t, ((A.H.image fun η => η.2).filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 * k) :
    K * ∑ ρ ∈ range (W q), ∑ ω ∈ offsets K₀ K q,
        ((cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card) ≤
      K ^ q * K ^ q * costB K K₀ k T (W q) (W 0) q N h
        (∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card)
        (∑ j : Fin q, (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card)
        (∑ j : Fin q, W q / W (j.val + 1) * 2 ^ (β j + h + 1)) (∑ F, A.d F) := by
  have hdq : ∀ j : Fin q, W (j.val + 1) ∣ W q := fun j => hdiv _ _ (by omega)
  rw [mul_sum]
  refine (sum_le_sum fun ρ _ =>
    sum_offsets_cut_le hx0 hW hdiv hq hK₀ hK hA hβ win hwin1 hwin2 hdegA ρ).trans ?_
  rw [← mul_sum]
  refine Nat.mul_le_mul_left _ ?_
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul]
  have e1 : ∑ ρ ∈ range (W q), K * K₀ * (4 + 2 * k) * (Zt x0 W ρ T).card =
      K * K₀ * (4 + 2 * k) * (T * (W q / W 0)) := by
    rw [← mul_sum]
    exact congrArg _ (sum_rho_lineT hW (hdiv 0 q (Nat.zero_le _)))
  have e2 : ∑ ρ ∈ range (W q), K₀ * ∑ j : Fin q, (W (j.val + 1) - 1) * (lineT x0 W ρ T (j.val + 1)).card ≤
      K₀ * (q * (T * W q)) := by
    rw [← mul_sum, sum_comm]
    refine Nat.mul_le_mul_left _ ?_
    calc ∑ j : Fin q, ∑ ρ ∈ range (W q), (W (j.val + 1) - 1) * (lineT x0 W ρ T (j.val + 1)).card
        = ∑ j : Fin q, (W (j.val + 1) - 1) * (T * (W q / W (j.val + 1))) := by
          refine sum_congr rfl fun j _ => ?_
          rw [← mul_sum, sum_rho_lineT hW (hdq j)]
      _ ≤ ∑ _j : Fin q, T * W q := by
          refine sum_le_sum fun j _ => ?_
          have h1 : (W (j.val + 1) - 1) * (W q / W (j.val + 1)) ≤ W q :=
            calc (W (j.val + 1) - 1) * (W q / W (j.val + 1)) ≤ W (j.val + 1) * (W q / W (j.val + 1)) :=
                  Nat.mul_le_mul_right _ (Nat.sub_le _ _)
              _ = W q := Nat.mul_div_cancel' (hdq j)
          calc (W (j.val + 1) - 1) * (T * (W q / W (j.val + 1)))
              = T * ((W (j.val + 1) - 1) * (W q / W (j.val + 1))) := by ring
            _ ≤ T * W q := Nat.mul_le_mul_left _ h1
      _ = q * (T * W q) := by simp
  have e3 : ∑ ρ ∈ range (W q), K * K₀ * N *
      ∑ j : Fin q, (lineT x0 W ρ T (j.val + 1)).card * 2 ^ (β j + h + 1) =
      K * K₀ * N * ∑ j : Fin q, T * (W q / W (j.val + 1)) * 2 ^ (β j + h + 1) := by
    rw [← mul_sum, sum_comm]
    refine congrArg _ (sum_congr rfl fun j _ => ?_)
    rw [← sum_mul, sum_rho_lineT hW (hdq j)]
  have e4 : ∑ j : Fin q, T * (W q / W (j.val + 1)) * 2 ^ (β j + h + 1) =
      T * ∑ j : Fin q, W q / W (j.val + 1) * 2 ^ (β j + h + 1) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  unfold costB
  rw [e1, e3, e4]
  omega

end AllResidues

end BoundedNesting

import HalfRate.Decomposition

/-! Recovery defects in the existing piece decomposition. Exact recovery is
not assumed. Repeated elimination-list entries incur no additional charge. -/

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [DecidableEq V]

/-- The conditional increment of one coordinate. -/
def increment (h : Finset V → ℝ) (S : Finset V) (v : V) : ℝ :=
  h (insert v S) - h S

theorem increment_nonneg {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (S : Finset V) (v : V) : 0 ≤ increment h S v :=
  sub_nonneg.mpr (hh.mono (subset_insert v S))

theorem increment_antitone {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {A B : Finset V} (hAB : A ⊆ B) (v : V) :
    increment h B v ≤ increment h A v := by
  have hs := hh.submod (insert v A) B
  rw [insert_union, union_eq_right.mpr hAB] at hs
  have hm := hh.mono (subset_inter (subset_insert v A) hAB)
  unfold increment
  linarith

theorem increment_le_singleton {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (S : Finset V) (v : V) : increment h S v ≤ h {v} := by
  simpa [increment, hh.empty] using increment_antitone hh (empty_subset S) v

@[simp] theorem increment_of_mem (h : Finset V → ℝ) {S : Finset V} {v : V}
    (hv : v ∈ S) : increment h S v = 0 := by simp [increment, hv]

theorem increment_contr (h : Finset V → ℝ) (U S : Finset V) (v : V) :
    increment (contr h U) S v = increment h (S ∪ U) v := by
  simp only [increment, contr, insert_union]
  ring

/-- Recovery uncertainty after the prescribed parents and the current context. -/
def residual (h : Finset V → ℝ) (N : V → Finset V) (U : Finset V) (v : V) : ℝ :=
  increment h (N v ∪ U) v

theorem residual_nonneg {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (N : V → Finset V) (U : Finset V) (v : V) : 0 ≤ residual h N U v :=
  increment_nonneg hh _ _

theorem residual_antitone {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (N : V → Finset V) {U U' : Finset V} (hU : U ⊆ U') (v : V) :
    residual h N U' v ≤ residual h N U v :=
  increment_antitone hh (union_subset_union (subset_refl _) hU) v

theorem increment_contr_le_residual {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {N : V → Finset V} {U Q : Finset V} {v : V} (hN : N v ⊆ U ∪ Q) :
    increment (contr h U) Q v ≤ residual h N U v := by
  rw [increment_contr]
  apply increment_antitone hh
  rw [union_comm Q U]
  exact union_subset hN subset_union_left

/-- The usual charged-step identity, with its recovery defect retained. -/
theorem defect_eq_mi_add_increment (g : Finset V → ℝ)
    (S R : Finset V) (v w : V) :
    defect g S R v = mi g w (insert v (S ∪ R)) - mi g w (S ∪ R) +
      increment g (insert w (S ∪ R)) v := by
  simp only [defect, mi, increment, insert_comm w v]
  ring

private theorem unrevealed_sum_cons (ε : V → ℝ) (S : Finset V) (v : V) (l : List V) :
    (∑ x ∈ (v :: l).toFinset \ S, ε x) =
      (if v ∈ S then 0 else ε v) + ∑ x ∈ l.toFinset \ insert v S, ε x := by
  by_cases hv : v ∈ S
  · have he : (v :: l).toFinset \ S = l.toFinset \ insert v S := by
      ext x
      simp only [List.toFinset_cons, mem_sdiff, mem_insert]
      have hxv : x = v → x ∈ S := fun hx => hx ▸ hv
      tauto
    rw [he, ite_eq_left hv, zero_add]
  · have he : (v :: l).toFinset \ S = insert v (l.toFinset \ insert v S) := by
      ext x
      simp only [List.toFinset_cons, mem_sdiff, mem_insert]
      by_cases hx : x = v <;> simp_all
    rw [he, sum_insert (by simp), ite_eq_right hv]

section Charges

variable {ι : Type*}

/-- The old structural charging predicate suffices without any validity
hypothesis. Every still-unrevealed coordinate pays its residual at most once. -/
theorem totalDefect_le_residual {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (N : V → Finset V) (U : Finset V) (P : ι → Finset V) (b : V → ι)
    (par : V → Option V) (H W : Finset V) (hPH : ∀ i, P i ⊆ H) :
    ∀ (l : List V) (S : Finset V) (L : V → Finset V),
      S ⊆ H → (∀ v ∈ l, v ∈ H) → (∀ w, L w ⊆ H) →
      RelCharged N U P b par W S L l →
      totalDefect (contr h U) P b S l ≤
        (∑ w ∈ W, (mi (contr h U) w H - mi (contr h U) w (L w))) +
        ∑ v ∈ l.toFinset \ S, residual h N U v := by
  intro l
  induction l with
  | nil =>
    intro S L _ _ hL _
    simp only [totalDefect, List.toFinset_nil, empty_sdiff, sum_empty, add_zero]
    exact sum_nonneg fun w _ =>
      sub_nonneg.mpr (mi_mono (contr_isPolymatroid hh U) w (hL w))
  | cons v l ih =>
    intro S L hSH hlH hL hch
    have hg := contr_isPolymatroid hh U
    have hvH := hlH v List.mem_cons_self
    have hlH' : ∀ u ∈ l, u ∈ H := fun u hu => hlH u (List.mem_cons_of_mem v hu)
    have hSH' : insert v S ⊆ H := insert_subset hvH hSH
    have hQH : insert v (S ∪ P (b v)) ⊆ H :=
      insert_subset hvH (union_subset hSH (hPH (b v)))
    rw [unrevealed_sum_cons]
    simp only [totalDefect]
    cases hp : par v with
    | none =>
      simp only [RelCharged, hp] at hch
      obtain ⟨hN, hrest⟩ := hch
      have hd : defect (contr h U) S (P (b v)) v ≤
          if v ∈ S then 0 else residual h N U v := by
        change increment (contr h U) (S ∪ P (b v)) v ≤ _
        split_ifs with hv
        · simp [mem_union_left _ hv]
        · exact increment_contr_le_residual hh hN
      have hih := ih (insert v S) L hSH' hlH' hL hrest
      linarith
    | some w =>
      simp only [RelCharged, hp] at hch
      obtain ⟨hwW, hN, hLw, hrest⟩ := hch
      let Q := S ∪ P (b v)
      have hL' : ∀ u, Function.update L w (insert v Q) u ⊆ H := by
        intro u
        by_cases hu : u = w
        · subst u; simpa using hQH
        · simpa [Function.update_of_ne hu] using hL u
      have hih := ih (insert v S) _ hSH' hlH' hL' hrest
      have hd := defect_eq_mi_add_increment (contr h U) S (P (b v)) v w
      have hr : increment (contr h U) (insert w Q) v ≤
          if v ∈ S then 0 else residual h N U v := by
        split_ifs with hv
        · exact le_of_eq (increment_of_mem _ (mem_insert_of_mem (mem_union_left _ hv)))
        · exact increment_contr_le_residual hh hN
      have hupd :
          (∑ u ∈ W, (mi (contr h U) u H -
            mi (contr h U) u (Function.update L w (insert v Q) u))) =
          (∑ u ∈ W, (mi (contr h U) u H - mi (contr h U) u (L u))) +
            mi (contr h U) w (L w) - mi (contr h U) w (insert v Q) := by
        rw [← add_sum_erase _ _ hwW, ← add_sum_erase _ _ hwW]
        have he :
            (∑ u ∈ W.erase w, (mi (contr h U) u H -
              mi (contr h U) u (Function.update L w (insert v Q) u))) =
            ∑ u ∈ W.erase w, (mi (contr h U) u H - mi (contr h U) u (L u)) := by
          apply sum_congr rfl
          intro u hu
          rw [Function.update_of_ne (ne_of_mem_erase hu)]
        rw [he, Function.update_self]
        ring
      rw [hupd] at hih
      have hm := mi_mono hg w hLw
      change defect (contr h U) S (P (b v)) v =
        mi (contr h U) w (insert v Q) - mi (contr h U) w Q +
          increment (contr h U) (insert w Q) v at hd
      linarith

end Charges

section Decomposition

variable [Fintype V]

theorem piece_ineq_residual {N : V → Finset V} {U H : Finset V}
    (c : PieceCert N U H) {h : Finset V → ℝ} (hh : IsPolymatroid h) :
    2 * contr h U H ≤ (∑ v ∈ H, contr h U {v}) +
      (∑ w ∈ univ \ (U ∪ H), mi (contr h U) w H) +
      ∑ v ∈ H, residual h N U v := by
  have hg := contr_isPolymatroid hh U
  have hPH : ∀ i, c.P i ⊆ H := fun i =>
    (subset_biUnion_of_mem c.P (mem_univ i)).trans c.cover.le
  have h0 := elim_defect hg c.P c.a c.b H hPH c.l ∅ (empty_subset H)
    (by simpa using c.hl) c.own c.ab
  have h1 := totalDefect_le_residual hh N U c.P c.b c.par H
    (univ \ (U ∪ H)) hPH c.l ∅ (fun _ => ∅) (empty_subset H)
    (fun v hv => by rw [← c.hl]; exact List.mem_toFinset.mpr hv)
    (fun _ => empty_subset H) c.charged
  simp only [empty_union, hg.empty, mul_zero, add_zero, mi_empty hg, sub_zero,
    c.hl, sdiff_empty] at h0 h1
  have hsub : ∑ i, contr h U (c.P i) ≤ ∑ v ∈ H, contr h U {v} := by
    calc ∑ i, contr h U (c.P i) ≤ ∑ i, ∑ v ∈ c.P i, contr h U {v} :=
          sum_le_sum fun i _ => hg.le_sum_singleton (c.P i)
      _ = ∑ v ∈ (univ : Finset (Fin c.m)).biUnion c.P, contr h U {v} := by
          rw [sum_biUnion]
          intro i _ j _ hij
          exact c.disj i j hij
      _ = ∑ v ∈ H, contr h U {v} := by rw [c.cover]
  linarith

/-- Retain each piece's actual prior context in the uncertainty charge. -/
def decompositionResidual (h : Finset V → ℝ) (N : V → Finset V) :
    Finset V → List (Finset V) → ℝ
  | _, [] => 0
  | U, H :: rest => (∑ v ∈ H, residual h N U v) + decompositionResidual h N (U ∪ H) rest

private theorem sum_remaining (f : V → ℝ) {U H : Finset V} (hdisj : Disjoint U H) :
    (∑ v ∈ univ \ U, f v) = (∑ v ∈ H, f v) + ∑ v ∈ univ \ (U ∪ H), f v := by
  have hs : univ \ U = H ∪ (univ \ (U ∪ H)) := by
    ext x
    simp only [mem_sdiff, mem_univ, true_and, mem_union]
    have hd : x ∈ U → x ∉ H := fun hU hH => disjoint_left.mp hdisj hU hH
    tauto
  rw [hs, sum_union]
  rw [disjoint_left]
  intro x hx hx'
  exact (mem_sdiff.mp hx').2 (mem_union_right _ hx)

/-- Soft decomposition, with the stronger piece-by-piece conditioning. -/
theorem decomp_ineq_residual {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) : ∀ (pcs : List (Finset V)) (U : Finset V),
      Decomp N U pcs →
      2 * (h univ - h U) ≤ (∑ v ∈ univ \ U, increment h U v) +
        decompositionResidual h N U pcs := by
  intro pcs
  induction pcs with
  | nil => intro U hU; simp only [Decomp] at hU; subst U; simp [decompositionResidual]
  | cons H rest ih =>
    intro U hD
    obtain ⟨hdisj, ⟨c⟩, hrest⟩ := hD
    have hp := piece_ineq_residual c hh
    have hi := ih (U ∪ H) hrest
    have hid : ∀ w, increment h (U ∪ H) w =
        contr h U {w} - mi (contr h U) w H := by
      intro w
      simp only [increment, mi, contr, singleton_union, insert_union, union_comm H U]
      ring
    rw [sum_congr rfl (fun w _ => hid w), sum_sub_distrib] at hi
    rw [sum_remaining (increment h U) hdisj]
    simp only [decompositionResidual, increment]
    simp only [contr, union_comm H U, singleton_union] at hp hi
    linarith

theorem decompositionResidual_le {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) : ∀ (pcs : List (Finset V)) (U : Finset V),
      Decomp N U pcs → decompositionResidual h N U pcs ≤
        ∑ v ∈ univ \ U, residual h N U v := by
  intro pcs
  induction pcs with
  | nil => intro U hU; simp only [Decomp] at hU; subst U; simp [decompositionResidual]
  | cons H rest ih =>
    intro U hD
    obtain ⟨hd, _, hr⟩ := hD
    rw [decompositionResidual, sum_remaining (residual h N U) hd]
    apply add_le_add le_rfl
    exact (ih _ hr).trans (sum_le_sum fun v _ => residual_antitone hh N subset_union_left v)

/-- Arbitrary polymatroids, arbitrary initial context, no recovery equalities. -/
theorem decomp_ineq_soft {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) {pcs : List (Finset V)} {U : Finset V}
    (hD : Decomp N U pcs) :
    2 * (h univ - h U) ≤ (∑ v ∈ univ \ U, increment h U v) +
      ∑ v ∈ univ \ U, residual h N U v :=
  (decomp_ineq_residual hh pcs U hD).trans
    (add_le_add le_rfl (decompositionResidual_le hh pcs U hD))

/-- The unconditioned soft half-rate inequality. -/
theorem soft_half {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) {pcs : List (Finset V)} (hD : Decomp N ∅ pcs) :
    2 * h univ ≤ (∑ v, h {v}) + ∑ v, increment h (N v) v := by
  simpa [increment, residual, hh.empty] using decomp_ineq_soft hh hD

/-- The original exact theorem follows directly from the soft theorem. -/
theorem exact_half {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h N)
    {pcs : List (Finset V)} (hD : Decomp N ∅ pcs) :
    2 * h univ ≤ ∑ v, h {v} := by
  have hr : ∀ v, increment h (N v) v = 0 := fun v => by
    rw [increment, hv v, sub_self]
  simpa only [hr, sum_const_zero, add_zero] using soft_half hh hD

/-- The original relative decomposition theorem, directly from the soft bound. -/
theorem exact_decomp {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h N)
    {pcs : List (Finset V)} {U : Finset V} (hD : Decomp N U pcs) :
    2 * (h univ - h U) ≤ ∑ v ∈ univ \ U, contr h U {v} := by
  have hr : ∀ v, residual h N U v = 0 := by
    intro v
    apply le_antisymm _ (residual_nonneg hh N U v)
    have hi := increment_antitone hh (subset_union_left : N v ⊆ N v ∪ U) v
    simpa only [residual, increment, hv v, sub_self] using hi
  have hs := decomp_ineq_soft hh hD
  simpa only [hr, sum_const_zero, add_zero, increment, contr, singleton_union] using hs

theorem exact_rateBound {N : V → Finset V} {pcs : List (Finset V)}
    (hD : Decomp N ∅ pcs) : RateBound N (1 / 2) := by
  intro h hh hv
  have hs := exact_half hh hv hD
  linarith

theorem exact_card_sq {α : Type*} [Fintype α] [Nonempty α]
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (exact_rateBound hD) hC

end Decomposition

end SoftRecovery

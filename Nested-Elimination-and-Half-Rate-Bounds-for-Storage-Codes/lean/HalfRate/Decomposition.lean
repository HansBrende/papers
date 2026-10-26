import HalfRate.NestedElimination
import MotionDepthCodes.RateHalf

/-!
# The decomposition theorem (Theorem D, the master theorem)

If the vertex set of a recovery relation `N` has an ordered decomposition into pieces, each
carrying a relative elimination certificate (Lemma E) in the relation left after contracting
the earlier pieces, then every valid polymatroid satisfies `2 h(V) ≤ Σ_v h({v})`, i.e.
`RateBound N (1/2)` in the sense of the series' fourth paper; hence every storage code has
`|C|² ≤ |α|^|V|` (Theorem D of the paper).
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V]

section Contraction

/-- Contraction by `U`: `g_U(X) = g(X ∪ U) - g(U)`. -/
def contr (g : Finset V → ℝ) (U X : Finset V) : ℝ := g (X ∪ U) - g U

theorem contr_isPolymatroid {g : Finset V → ℝ} (hg : IsPolymatroid g) (U : Finset V) :
    IsPolymatroid (contr g U) where
  empty := by simp [contr]
  mono := fun X Y hXY => by
    have := hg.mono (union_subset_union hXY (subset_refl U))
    simp only [contr]; linarith
  submod := fun A B => by
    have h := hg.submod (A ∪ U) (B ∪ U)
    have e1 : (A ∪ U) ∪ (B ∪ U) = (A ∪ B) ∪ U := by ext x; simp only [mem_union]; tauto
    have e2 : (A ∪ U) ∩ (B ∪ U) = (A ∩ B) ∪ U := by
      ext x; simp only [mem_union, mem_inter]; tauto
    rw [e1, e2] at h
    simp only [contr]; linarith

/-- A dependence of `v` on `X ∪ U` in `g` is a dependence on `X` in the contraction. -/
theorem contr_insert_eq {g : Finset V → ℝ} (hg : IsPolymatroid g) {N : V → Finset V}
    (hv : IsValid g N) {U X : Finset V} {v : V} (hN : N v ⊆ U ∪ X) :
    contr g U (insert v X) = contr g U X := by
  have h := hg.insert_eq_of_subset (A := N v) (B := X ∪ U) (v := v)
    (by rw [union_comm]; exact hN) (hv v)
  simp only [contr, insert_union, h]

end Contraction

section Pieces

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relation-level charging conditions for a piece in context `U`. -/
def RelCharged (N : V → Finset V) (U : Finset V) (P : ι → Finset V) (b : V → ι)
    (par : V → Option V) (W : Finset V) : Finset V → (V → Finset V) → List V → Prop
  | _, _, [] => True
  | S, L, v :: l =>
      match par v with
      | none => N v ⊆ U ∪ (S ∪ P (b v)) ∧ RelCharged N U P b par W (insert v S) L l
      | some w => w ∈ W ∧ N v ⊆ U ∪ insert w (S ∪ P (b v)) ∧ L w ⊆ S ∪ P (b v) ∧
          RelCharged N U P b par W (insert v S) (Function.update L w (insert v (S ∪ P (b v)))) l

omit [Fintype ι] [DecidableEq ι] in
theorem RelCharged.charged {h : Finset V → ℝ} (hh : IsPolymatroid h) {N : V → Finset V}
    (hv : IsValid h N) (U : Finset V) (P : ι → Finset V) (b : V → ι) (par : V → Option V)
    (W : Finset V) : ∀ (l : List V) (S : Finset V) (L : V → Finset V),
      RelCharged N U P b par W S L l → Charged (contr h U) P b par W S L l := by
  intro l
  induction l with
  | nil => intro _ _ _; trivial
  | cons v l ih =>
    intro S L hrc
    cases hp : par v with
    | none =>
      simp only [RelCharged, hp] at hrc
      obtain ⟨hN, hrest⟩ := hrc
      simp only [Charged, hp]
      exact ⟨contr_insert_eq hh hv hN, ih _ _ hrest⟩
    | some w =>
      simp only [RelCharged, hp] at hrc
      obtain ⟨hwW, hN, hLw, hrest⟩ := hrc
      simp only [Charged, hp]
      exact ⟨hwW, contr_insert_eq hh hv hN, hLw, ih _ _ hrest⟩

end Pieces

section Decomposition

variable [Fintype V]

/-- A piece certificate for `H` in context `U`: records partitioning `H`, an elimination
list, own and supplying records, optional outside parents, and the charging conditions. -/
structure PieceCert (N : V → Finset V) (U H : Finset V) where
  m : ℕ
  P : Fin m → Finset V
  disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  cover : (univ : Finset (Fin m)).biUnion P = H
  l : List V
  hl : l.toFinset = H
  a : V → Fin m
  b : V → Fin m
  par : V → Option V
  own : ∀ v ∈ l, v ∈ P (a v)
  ab : ∀ v ∈ l, a v ≠ b v
  charged : RelCharged N U P b par (univ \ (U ∪ H)) ∅ (fun _ => ∅) l

/-- The piece inequality: Lemma E in the contraction by the context, plus subadditivity. -/
theorem PieceCert.ineq {N : V → Finset V} {U H : Finset V} (c : PieceCert N U H)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (hv : IsValid h N) :
    2 * contr h U H ≤ ∑ v ∈ H, contr h U {v} + ∑ w ∈ univ \ (U ∪ H), mi (contr h U) w H := by
  have hg := contr_isPolymatroid hh U
  have hPH : ∀ i, c.P i ⊆ H := fun i =>
    (subset_biUnion_of_mem c.P (mem_univ i)).trans c.cover.le
  have hE := nested_elimination hg c.P c.a c.b c.par H (univ \ (U ∪ H)) hPH c.l c.hl c.own c.ab
    (RelCharged.charged hh hv U c.P c.b c.par _ c.l ∅ _ c.charged)
  have hsub : ∑ i, contr h U (c.P i) ≤ ∑ v ∈ H, contr h U {v} := by
    calc ∑ i, contr h U (c.P i) ≤ ∑ i, ∑ v ∈ c.P i, contr h U {v} :=
          sum_le_sum fun i _ => hg.le_sum_singleton (c.P i)
      _ = ∑ v ∈ (univ : Finset (Fin c.m)).biUnion c.P, contr h U {v} := by
          rw [sum_biUnion]; intro i _ j _ hij; exact c.disj i j hij
      _ = ∑ v ∈ H, contr h U {v} := by rw [c.cover]
  linarith

/-- An ordered decomposition of the vertices outside `U` into certified pieces. -/
def Decomp (N : V → Finset V) : Finset V → List (Finset V) → Prop
  | U, [] => U = univ
  | U, H :: rest => Disjoint U H ∧ Nonempty (PieceCert N U H) ∧ Decomp N (U ∪ H) rest

/-- The relative form of the decomposition theorem. -/
theorem decomp_ineq {N : V → Finset V} {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h N) : ∀ (pcs : List (Finset V)) (U : Finset V), Decomp N U pcs →
      2 * (h univ - h U) ≤ ∑ v ∈ univ \ U, (h (insert v U) - h U) := by
  intro pcs
  induction pcs with
  | nil => intro U hU; simp only [Decomp] at hU; subst hU; simp
  | cons H rest ih =>
    intro U hD
    simp only [Decomp] at hD
    obtain ⟨hdisj, ⟨c⟩, hrest⟩ := hD
    have hpiece := c.ineq hh hv
    have hih := ih (U ∪ H) hrest
    -- per-vertex identity for the outside vertices
    have hid : ∀ w, h (insert w (U ∪ H)) - h (U ∪ H) =
        contr h U {w} - mi (contr h U) w H := by
      intro w
      have e1 : insert w H ∪ U = insert w (U ∪ H) := by
        ext x; simp only [mem_union, mem_insert]; tauto
      have e2 : H ∪ U = U ∪ H := union_comm H U
      simp only [mi, contr, e1, e2, singleton_union]; ring
    rw [sum_congr rfl (fun w _ => hid w), sum_sub_distrib] at hih
    -- split univ \ U into H and the rest
    have hsplit : univ \ U = H ∪ (univ \ (U ∪ H)) := by
      ext x; simp only [mem_sdiff, mem_univ, true_and, mem_union]
      constructor
      · intro hx; by_cases hxH : x ∈ H
        · exact Or.inl hxH
        · exact Or.inr (by tauto)
      · rintro (hx | hx)
        · exact fun hxU => disjoint_left.mp hdisj hxU hx
        · tauto
    have hdisj2 : Disjoint H (univ \ (U ∪ H)) := by
      rw [disjoint_left]; intro x hx hx'
      simp only [mem_sdiff, mem_union] at hx'; exact hx'.2 (Or.inr hx)
    have hsum : ∑ v ∈ univ \ U, (h (insert v U) - h U) =
        ∑ v ∈ H, contr h U {v} + ∑ v ∈ univ \ (U ∪ H), contr h U {v} := by
      rw [hsplit, sum_union hdisj2]
      simp only [contr, singleton_union]
    rw [hsum]
    have hcontrH : contr h U H = h (U ∪ H) - h U := by simp only [contr, union_comm]
    rw [hcontrH] at hpiece
    linarith

/-- **The decomposition (master) theorem.** -/
theorem rateBound_of_decomp {N : V → Finset V} {pcs : List (Finset V)}
    (hD : Decomp N ∅ pcs) : RateBound N (1 / 2) := by
  intro h hh hv
  have := decomp_ineq hh hv pcs ∅ hD
  simp only [hh.empty, sub_zero, sdiff_empty, insert_empty_eq] at this
  linarith

/-- Every storage code on a relation with a certified decomposition has `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_of_decomp {α : Type*} [Fintype α] [Nonempty α] {N : V → Finset V}
    {pcs : List (Finset V)} (hD : Decomp N ∅ pcs) {C : Finset (V → α)}
    (hC : IsStorageCode N C) : C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_of_decomp hD) hC

end Decomposition

end HalfRate

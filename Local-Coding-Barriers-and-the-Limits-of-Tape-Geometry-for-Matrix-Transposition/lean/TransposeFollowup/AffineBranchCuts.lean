import TransposeFollowup.AffineHeightPairs
import TransposeFollowup.ConsecutiveDeletion

/-! Actual finite affine branch families admit arbitrarily small retained
crossing integral, simultaneously for finitely many paths. We overcount by
all ordered branch pairs; no first-return selection or successor-domain
measurability theorem is needed. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

noncomputable def inverseVisit (a : ℝˣ) (b p : ℝ) : ℝ :=
  (a : ℝ)⁻¹*p-b/(a : ℝ)

theorem inverseVisit_eq {a : ℝˣ} {b p x : ℝ} (h : (a : ℝ)*x+b=p) :
    inverseVisit a b p=x := by
  dsimp [inverseVisit]
  rw [← h]
  field_simp
  ring

theorem retained_pairs_card_le {ι : Type*} [Fintype ι]
    (P : ℝ → ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) (J : ι → Set ℝ) (u : ι → ℝ)
    (hu : ∀ i x, x ∈ J i → P x=p → u i=x) :
    ({q ∈ crossPairs P ∅ β c₀ p | q.1 ∈ ⋃ i, J i ∧ q.2 ∈ ⋃ i, J i}.ncard : ℝ≥0∞) ≤
      ∑ ij : ι × ι, if u ij.1 ∈ J ij.1 ∧ u ij.2 ∈ J ij.2 ∧ β (u ij.1) ≠ β (u ij.2)
        then (1 : ℝ≥0∞) else 0 := by
  let A := Finset.univ.filter (fun ij : ι × ι =>
    u ij.1 ∈ J ij.1 ∧ u ij.2 ∈ J ij.2 ∧ β (u ij.1) ≠ β (u ij.2))
  let f (ij : ι × ι) := (u ij.1,u ij.2)
  have hsub : {q ∈ crossPairs P ∅ β c₀ p | q.1 ∈ ⋃ i, J i ∧ q.2 ∈ ⋃ i, J i} ⊆
      f '' (A : Set (ι × ι)) := by
    rintro q ⟨hq,h1,h2⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h1
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h2
    have hei := hu i q.1 hi hq.1.1.2
    have hej := hu j q.2 hj hq.1.2.1.2
    refine ⟨(i,j),?_,Prod.ext hei hej⟩
    simp only [A,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,hei,hej]
    exact ⟨hi,hj,hq.2.2.2⟩
  have hn := (Set.ncard_le_ncard hsub (A.finite_toSet.image f)).trans
    (Set.ncard_image_le (s:=(A : Set (ι × ι))) (f:=f) A.finite_toSet)
  rw [Set.ncard_coe_finset] at hn
  have he : (A.card : ℝ≥0∞)=
      ∑ ij : ι × ι, if u ij.1 ∈ J ij.1 ∧ u ij.2 ∈ J ij.2 ∧ β (u ij.1) ≠ β (u ij.2)
        then (1 : ℝ≥0∞) else 0 := by
    simp [A,Finset.sum_boole]
  rw [← he]
  exact_mod_cast hn

theorem exists_finite_branch_small_cut {τ ι : Type*} [Fintype τ] [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (P : τ → ℝ → ℝ)
    (a : τ → ι → ℝˣ) (b : τ → ι → ℝ) (J : τ → ι → Set ℝ)
    (hJm : ∀ t i, MeasurableSet (J t i))
    (hJi : ∀ t i, J t i ⊆ Icc 0 c₀)
    (hP : ∀ t i x, x ∈ J t i → P t x=(a t i : ℝ)*x+b t i)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}.ncard : ℝ≥0∞)) < ENNReal.ofReal ε := by
  let u (t : τ) (i : ι) (p : ℝ) := inverseVisit (a t i) (b t i) p
  have hum (t : τ) (i : ι) : Measurable (u t i) := by dsimp [u,inverseVisit]; fun_prop
  let D (q : τ × (ι × ι)) : Set ℝ := {p | u q.1 q.2.1 p ∈ J q.1 q.2.1 ∧
    u q.1 q.2.2 p ∈ J q.1 q.2.2}
  have hDm (q : τ × (ι × ι)) : MeasurableSet (D q) :=
    ((hJm q.1 q.2.1).preimage (hum _ _)).inter ((hJm q.1 q.2.2).preimage (hum _ _))
  obtain ⟨β,hβ,hpc,hm,hcut⟩ := exists_small_height_pair_cut hc
    (fun q : τ × (ι × ι) => (a q.1 q.2.1)⁻¹)
    (fun q : τ × (ι × ι) => (a q.1 q.2.2)⁻¹)
    (fun q => -(b q.1 q.2.1)/(a q.1 q.2.1 : ℝ))
    (fun q => -(b q.1 q.2.2)/(a q.1 q.2.2 : ℝ)) D
    (fun q p hp => by
      simpa only [Units.val_inv_eq_inv_val,neg_div,sub_eq_add_neg,u,inverseVisit] using
        And.intro (hJi _ _ hp.1) (hJi _ _ hp.2)) hθ hε
  refine ⟨β,hβ,hpc,hm,lt_of_le_of_lt ?_ hcut⟩
  simp only [Fintype.sum_prod_type,Units.val_inv_eq_inv_val,neg_div,← sub_eq_add_neg]
  apply Finset.sum_le_sum
  intro t _
  let E (ij : ι × ι) := {p | p ∈ D (t,ij) ∧ β (u t ij.1 p) ≠ β (u t ij.2 p)}
  have hEm (ij : ι × ι) : MeasurableSet (E ij) := (hDm (t,ij)).inter
    (measurableSet_eq_fun (hβ.comp (hum _ _)) (hβ.comp (hum _ _))).compl
  have hi : (∫⁻ p, ∑ ij : ι × ι, (E ij).indicator (fun _ => (1 : ℝ≥0∞)) p)=
      ∑ ij : ι × ι, volume (E ij) := by
    rw [lintegral_finsetSum _ (fun ij _ => measurable_const.indicator (hEm ij))]
    simp only [lintegral_indicator_const (hEm _) 1,one_mul]
  calc
    _ ≤ ∫⁻ p, ∑ ij : ι × ι, (E ij).indicator (fun _ => (1 : ℝ≥0∞)) p := by
      apply lintegral_mono
      intro p
      have hh := retained_pairs_card_le (P t) β c₀ p (J t) (fun i => u t i p)
        (fun i x hx hp => inverseVisit_eq ((hP t i x hx).symm.trans hp))
      simpa only [E,D,Set.indicator_apply,Set.mem_ofPred_eq,and_assoc] using hh
    _ = ∑ ij : ι × ι, volume (E ij) := hi
    _ = _ := by simp only [Fintype.sum_prod_type,E,D,u,inverseVisit]

/-- Constant branches are retained in time. Only their finitely many height
values are discarded, which is legitimate for the height integral. -/
theorem exists_finite_affine_branch_small_cut {τ ι : Type*} [Fintype τ] [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (P : τ → ℝ → ℝ)
    (a b : τ → ι → ℝ) (J : τ → ι → Set ℝ)
    (hJm : ∀ t i, MeasurableSet (J t i))
    (hJi : ∀ t i, J t i ⊆ Icc 0 c₀)
    (hP : ∀ t i x, x ∈ J t i → P t x=a t i*x+b t i)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}.ncard : ℝ≥0∞)) < ENNReal.ofReal ε := by
  let A (t : τ) (i : ι) : ℝˣ := if h : a t i=0 then 1 else Units.mk0 (a t i) h
  let J' (t : τ) (i : ι) : Set ℝ := if a t i=0 then ∅ else J t i
  have hmem (t : τ) (i : ι) (x : ℝ) : x ∈ J' t i ↔ a t i ≠ 0 ∧ x ∈ J t i := by
    dsimp [J']
    split_ifs <;> simp_all
  have hAm (t : τ) (i : ι) : MeasurableSet (J' t i) := by
    dsimp [J']
    split_ifs
    · exact MeasurableSet.empty
    · exact hJm t i
  have hAi (t : τ) (i : ι) : J' t i ⊆ Icc 0 c₀ :=
    fun x hx => hJi t i ((hmem t i x).mp hx).2
  have hAP (t : τ) (i : ι) (x : ℝ) (hx : x ∈ J' t i) :
      P t x=(A t i : ℝ)*x+b t i := by
    have hx' := (hmem t i x).mp hx
    simpa only [A,dite_eq_right hx'.1,Units.val_mk0] using hP t i x hx'.2
  obtain ⟨β,hβ,hpc,hm,hcut⟩ := exists_finite_branch_small_cut hc P A b J' hAm hAi hAP hθ hε
  refine ⟨β,hβ,hpc,hm,?_⟩
  have heq : (∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}.ncard : ℝ≥0∞))=
      ∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J' t i ∧ q.2 ∈ ⋃ i, J' t i}.ncard : ℝ≥0∞) := by
    apply Finset.sum_congr rfl
    intro t _
    apply lintegral_congr_ae
    filter_upwards [(Set.finite_range (fun i : ι => b t i)).countable.ae_notMem volume] with p hp
    have hvisit (x : ℝ) (hx : x ∈ levelSet (P t) c₀ p) :
        (x ∈ ⋃ i, J t i) ↔ (x ∈ ⋃ i, J' t i) := by
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        have hne : a t i ≠ 0 := by
          intro ha
          have hb : b t i=p := by simpa only [ha,zero_mul,zero_add] using (hP t i x hi).symm.trans hx.2
          exact hp ⟨i,hb⟩
        exact ⟨i,(hmem t i x).mpr ⟨hne,hi⟩⟩
      · rintro ⟨i,hi⟩
        exact ⟨i,((hmem t i x).mp hi).2⟩
    have hsets : {q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}=
        {q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J' t i ∧ q.2 ∈ ⋃ i, J' t i} := by
      ext q
      constructor
      · rintro ⟨hq,h1,h2⟩
        exact ⟨hq,(hvisit q.1 hq.1.1).mp h1,(hvisit q.2 hq.1.2.1).mp h2⟩
      · rintro ⟨hq,h1,h2⟩
        exact ⟨hq,(hvisit q.1 hq.1.1).mpr h1,(hvisit q.2 hq.1.2.1).mpr h2⟩
    rw [hsets]
  exact heq.trans_lt hcut

end TransposeFollowup.AffineMotion

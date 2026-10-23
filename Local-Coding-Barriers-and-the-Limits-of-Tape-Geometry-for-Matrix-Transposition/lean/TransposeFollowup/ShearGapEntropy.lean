import TransposeFollowup.ExpanderShearRank
import TransposeFollowup.EntropyFibers
import TransposeFollowup.ConditionalObservation
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Coset.Basic

/-! Finite linear fibers give conditional entropy lower bounds for row cuts.
All entropies are natural-log entropies of arbitrary finite input laws. -/

namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- A linear observation has no fiber larger than its kernel. -/
theorem fiberCard_linear_le_ker {K V U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup U] [Module K U] (f : V →ₗ[K] U) (u : U) :
    fiberCard f u ≤ Fintype.card (LinearMap.ker f) := by
  by_cases h : ∃ v, f v = u
  · obtain ⟨v, rfl⟩ := h
    rw [fiberCard, ← Fintype.card_subtype]
    let g : {x // f x = f v} → LinearMap.ker f :=
      fun x => ⟨x.val - v, by simp [LinearMap.mem_ker, map_sub, x.property]⟩
    apply Fintype.card_le_of_injective g
    intro x y h
    apply Subtype.ext
    exact sub_left_inj.mp (congrArg Subtype.val h)
  · have he : (Finset.univ.filter (fun v => f v = u)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact h ⟨v, (Finset.mem_filter.mp hv).2⟩
    simp [fiberCard, he]

/-- The finite-field cardinality formula for a matrix kernel. -/
theorem card_matrix_ker {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β Bit) :
    Fintype.card (LinearMap.ker M.mulVecLin) = 2 ^ (Fintype.card β - M.rank) := by
  rw [Module.card_eq_pow_finrank (K := Bit) (V := LinearMap.ker M.mulVecLin)]
  have hr : Module.finrank Bit (LinearMap.range M.mulVecLin) = M.rank := by
    rw [Matrix.range_mulVecLin, Matrix.rank_eq_finrank_span_cols]
  have hk := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hr, Module.finrank_fintype_fun_eq_card] at hk
  have he : Module.finrank Bit (LinearMap.ker M.mulVecLin) =
      Fintype.card β - M.rank := by omega
  simp [Bit, ZMod.card, he]

/-- Entrywise application of a row matrix, retaining each bit lane. -/
def rowMap {α : Type*} [Fintype α] (M : Matrix α α Bit) {W : ℕ}
    (x : α → Fin W → Bit) : α → Fin W → Bit :=
  fun j w => M.mulVec (fun i => x i w) j

def rowView {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) {W : ℕ} (x : α → Fin W → Bit) : I → Fin W → Bit :=
  fun i w => x i w

/-- A vector vanishing on the selected input rows is acted on by the
complementary matrix block on selected output rows. -/
theorem cross_mulVec_of_zero {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α Bit) (I J : Finset α) (x : α → Bit)
    (hx : ∀ i ∈ I, x i = 0) (j : J) :
    (crossMatrix M J I).mulVec (fun i => x i) j = M.mulVec x j := by
  simp only [Matrix.mulVec, dotProduct, crossMatrix, Matrix.submatrix_apply]
  calc
    (∑ i : (↑(Iᶜ) : Finset α), M j i * x i) = ∑ i ∈ Iᶜ, M j i * x i :=
      Finset.sum_coe_sort Iᶜ (fun i => M j i * x i)
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have him : i ∈ I := by simpa using hi
      simp [hx i him]

/-- Jointly record selected output and input rows. -/
def jointView {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α Bit) (I J : Finset α) {W : ℕ}
    (x : α → Fin W → Bit) := (rowView J (rowMap M x), rowView I x)

/-- Differences of two inputs with equal observations lie in one copy of the
cross-block kernel per bit lane. -/
def fiberToKernels {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α Bit) (I J : Finset α) {W : ℕ} (x₀ : α → Fin W → Bit)
    (x : {x // jointView M I J x = jointView M I J x₀}) :
    Fin W → LinearMap.ker (crossMatrix M J I).mulVecLin := by
  intro w
  refine ⟨(fun i => x.val i w - x₀ i w), ?_⟩
  apply LinearMap.mem_ker.mpr
  funext j
  change (crossMatrix M J I).mulVec (fun i => x.val i w - x₀ i w) j = 0
  rw [cross_mulVec_of_zero M I J (fun i => x.val i w - x₀ i w)]
  · change M.mulVec ((fun i => x.val i w) - (fun i => x₀ i w)) j = 0
    rw [Matrix.mulVec_sub]
    have h := congrFun (congrFun (congrArg Prod.fst x.property) j) w
    exact sub_eq_zero.mpr h
  · intro i hi
    exact sub_eq_zero.mpr (congrFun (congrFun (congrArg Prod.snd x.property) ⟨i, hi⟩) w)

theorem fiberToKernels_injective {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α Bit) (I J : Finset α) {W : ℕ} (x₀ : α → Fin W → Bit) :
    Function.Injective (fiberToKernels M I J x₀) := by
  intro x y h
  apply Subtype.ext
  funext i w
  by_cases hi : i ∈ I
  · have hx := congrFun (congrFun (congrArg Prod.snd x.property) ⟨i, hi⟩) w
    have hy := congrFun (congrFun (congrArg Prod.snd y.property) ⟨i, hi⟩) w
    exact hx.trans hy.symm
  · have hic : i ∈ Iᶜ := Finset.mem_compl.mpr hi
    have hz := congrFun (congrArg Subtype.val (congrFun h w)) ⟨i, hic⟩
    exact sub_left_inj.mp hz

theorem jointView_fiberCard_le {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α Bit) (I J : Finset α) (W : ℕ)
    (a : (J → Fin W → Bit) × (I → Fin W → Bit)) :
    fiberCard (jointView M I J) a ≤
      2 ^ ((Iᶜ.card - (crossMatrix M J I).rank) * W) := by
  by_cases h : ∃ x, jointView M I J x = a
  · obtain ⟨x₀, rfl⟩ := h
    rw [fiberCard, ← Fintype.card_subtype]
    calc
      _ ≤ Fintype.card (Fin W → LinearMap.ker (crossMatrix M J I).mulVecLin) :=
        Fintype.card_le_of_injective _ (fiberToKernels_injective M I J x₀)
      _ = _ := by
        rw [Fintype.card_fun, Fintype.card_fin]
        have hc := card_matrix_ker (crossMatrix M J I)
        have hpow := congrArg (fun n => n ^ W) hc
        rw [Fintype.card_coe, ← pow_mul] at hpow
        exact hpow
  · have he : (Finset.univ.filter (fun x => jointView M I J x = a)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, (Finset.mem_filter.mp hx).2⟩
    have hz : fiberCard (jointView (W := W) M I J) a = 0 := by
      unfold fiberCard
      apply Finset.card_eq_zero.mpr
      convert he using 1
      congr 1
    rw [hz]
    exact Nat.zero_le _

/-- Equal-size input/output row cuts have conditional entropy at least their
cross-block rank per lane, minus the entropy deficit of the complete input. -/
theorem conditional_rowView_ge_cross_rank {Ω α : Type*}
    [Fintype Ω] [Fintype α] [DecidableEq α]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (M : Matrix α α Bit) (I J : Finset α) (hIJ : I.card = J.card)
    (W : ℕ) (X : Ω → α → Fin W → Bit) :
    ((crossMatrix M J I).rank * W : ℕ) * Real.log 2 -
        ((Fintype.card α * W : ℕ) * Real.log 2 - observationEntropy p X) ≤
      conditionalObservationEntropy p (fun ω => rowView I (X ω))
        (fun ω => rowView J (rowMap M (X ω))) := by
  let e := (Iᶜ.card - (crossMatrix M J I).rank) * W
  have hcap : ∀ a, (fiberCard (jointView (W := W) M I J) a : ℝ) ≤ (2 : ℝ) ^ e := by
    intro a
    exact_mod_cast jointView_fiberCard_le M I J W a
  have hjoint := entropy_le_observation_add_log_fiber_bound
    (pushforward p X) (pushforward_nonneg p hp X) (jointView M I J)
    ((2 : ℝ) ^ e) (pow_pos (by norm_num) _) hcap
  rw [sum_pushforward, hp1, one_mul, Real.log_pow] at hjoint
  have hcomp : observationEntropy (pushforward p X) (jointView M I J) =
      observationEntropy p (fun ω => jointView M I J (X ω)) := by
    unfold observationEntropy
    rw [pushforward_comp]
    rfl
  rw [hcomp] at hjoint
  change observationEntropy p X ≤ _ at hjoint
  have hout : observationEntropy p (fun ω => rowView J (rowMap M (X ω))) ≤
      (J.card * W : ℕ) * Real.log 2 := by
    have hh := entropy_le_log_card
      (pushforward p (fun ω => rowView J (rowMap M (X ω))))
      (pushforward_nonneg p hp _) (by rw [sum_pushforward, hp1])
    simpa only [observationEntropy, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Bit, ZMod.card, ← pow_mul, Nat.cast_pow,
      Nat.cast_ofNat, Real.log_pow, Nat.cast_mul, mul_comm] using hh
  have hr : (crossMatrix M J I).rank ≤ Iᶜ.card := by
    simpa only [Fintype.card_coe] using (crossMatrix M J I).rank_le_card_width
  have hn : J.card * W + e + (crossMatrix M J I).rank * W = Fintype.card α * W := by
    dsimp [e]
    rw [← Nat.add_mul, ← Nat.add_mul]
    congr 1
    have hc := Finset.card_compl_add_card I
    omega
  have he : ((J.card * W : ℕ) : ℝ) + (e : ℝ) +
      (((crossMatrix M J I).rank * W : ℕ) : ℝ) = (Fintype.card α * W : ℕ) := by
    exact_mod_cast hn
  unfold conditionalObservationEntropy
  change _ ≤ observationEntropy p (fun ω => jointView M I J (X ω)) - _
  have he' := congrArg (fun t : ℝ => t * Real.log 2) he
  nlinarith only [hjoint, hout, he']

end TransposeFollowup.ExpanderShear

import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Real-capacity flows on finite directed multigraphs. Edges retain their
identities, including parallel edges. No rationality or acyclicity premise. -/

namespace LeanMachine.FiniteFlow

open Finset
open scoped BigOperators Classical
noncomputable section

/-- An inward-pointing scalar direction admits a positive step in a closed
interval, including at either endpoint. -/
theorem scalar_box_step {c f h : ℝ} (hf : 0 ≤ f) (hfc : f ≤ c)
    (hzero : f = 0 → 0 ≤ h) (hcap : f = c → h ≤ 0) :
    ∃ δ > 0, ∀ t, 0 ≤ t → t ≤ δ → 0 ≤ f + t * h ∧ f + t * h ≤ c := by
  rcases lt_trichotomy 0 h with hh | hh | hh
  · have hslack : 0 < c - f := by
      have : f ≠ c := fun he => (not_le_of_gt hh) (hcap he)
      exact sub_pos.mpr (lt_of_le_of_ne hfc this)
    refine ⟨(c - f) / h, div_pos hslack hh, fun t ht htd => ?_⟩
    have := (le_div_iff₀ hh).mp htd
    exact ⟨add_nonneg hf (mul_nonneg ht hh.le), by linarith⟩
  · refine ⟨1, zero_lt_one, fun t _ _ => ?_⟩
    simpa only [← hh, mul_zero, add_zero] using And.intro hf hfc
  · have hfp : 0 < f := by
      have : f ≠ 0 := fun he => (not_le_of_gt hh) (hzero he)
      exact lt_of_le_of_ne hf (Ne.symm this)
    refine ⟨f / (-h), div_pos hfp (neg_pos.mpr hh), fun t ht htd => ?_⟩
    have := (le_div_iff₀ (neg_pos.mpr hh)).mp htd
    have := mul_nonpos_of_nonneg_of_nonpos ht hh.le
    constructor <;> nlinarith

/-- A single positive step works for all coordinates of a finite box. -/
theorem finite_box_step {Edge : Type*} [Fintype Edge] (c f h : Edge → ℝ)
    (hf : ∀ e, 0 ≤ f e) (hfc : ∀ e, f e ≤ c e)
    (hzero : ∀ e, f e = 0 → 0 ≤ h e) (hcap : ∀ e, f e = c e → h e ≤ 0) :
    ∃ δ > 0, ∀ e, 0 ≤ f e + δ * h e ∧ f e + δ * h e ≤ c e := by
  choose δ hδ hstep using fun e => scalar_box_step (hf e) (hfc e) (hzero e) (hcap e)
  cases isEmpty_or_nonempty Edge with
  | inl he => exact ⟨1, zero_lt_one, fun e => isEmptyElim e⟩
  | inr he =>
    let m := univ.inf' univ_nonempty δ
    have hm : 0 < m := (lt_inf'_iff _).mpr (fun e _ => hδ e)
    exact ⟨m, hm, fun e => hstep e m hm.le (inf'_le δ (mem_univ e))⟩

structure Network (Vertex Edge : Type*) where
  source : Edge → Vertex
  target : Edge → Vertex
  capacity : Edge → ℝ
  capacity_nonneg : ∀ e, 0 ≤ capacity e

namespace Network

variable {Vertex Edge : Type*} [Fintype Edge]
variable (G : Network Vertex Edge)

def incidence (e : Edge) (v : Vertex) : ℝ :=
  (if G.source e = v then 1 else 0) - (if G.target e = v then 1 else 0)

def divergence (f : Edge → ℝ) (v : Vertex) : ℝ := ∑ e, G.incidence e v * f e

@[simp] theorem divergence_zero (v : Vertex) : G.divergence 0 v = 0 := by
  simp [divergence]

theorem divergence_add (f g : Edge → ℝ) (v : Vertex) :
    G.divergence (f + g) v = G.divergence f v + G.divergence g v := by
  simp [divergence, mul_add, sum_add_distrib]

theorem divergence_smul (r : ℝ) (f : Edge → ℝ) (v : Vertex) :
    G.divergence (r • f) v = r * G.divergence f v := by
  simp [divergence, mul_sum, mul_left_comm]

theorem continuous_divergence (v : Vertex) : Continuous (fun f => G.divergence f v) := by
  unfold divergence
  fun_prop

/-- Nonnegative edge flow, capacity bounds, and conservation away from
the source and sink. Both incoming source edges and outgoing sink edges
are allowed; the flow value is net source divergence. -/
def Feasible (s t : Vertex) (f : Edge → ℝ) : Prop :=
  f ∈ Set.Icc 0 G.capacity ∧ ∀ v, v ≠ s → v ≠ t → G.divergence f v = 0

theorem feasible_zero (s t : Vertex) : G.Feasible s t 0 := by
  exact ⟨⟨le_rfl, G.capacity_nonneg⟩, fun v _ _ => G.divergence_zero v⟩

theorem feasible_smul {s t : Vertex} {f : Edge → ℝ} (hf : G.Feasible s t f)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : G.Feasible s t (r • f) := by
  refine ⟨⟨fun e => mul_nonneg hr (hf.1.1 e), fun e => ?_⟩, fun v hs ht => ?_⟩
  · exact (mul_le_of_le_one_left (hf.1.1 e) hr1).trans (hf.1.2 e)
  · rw [G.divergence_smul, hf.2 v hs ht, mul_zero]

theorem compact_feasible (s t : Vertex) : IsCompact {f | G.Feasible s t f} := by
  have hc : IsClosed {f | ∀ v, v ≠ s → v ≠ t → G.divergence f v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (G.continuous_divergence v) continuous_const
  exact isCompact_Icc.inter_right hc

theorem exists_maximum (s t : Vertex) :
    ∃ f, G.Feasible s t f ∧ ∀ g, G.Feasible s t g →
      G.divergence g s ≤ G.divergence f s := by
  exact (G.compact_feasible s t).exists_isMaxOn ⟨0, G.feasible_zero s t⟩
    (G.continuous_divergence s).continuousOn

/-- Directions may decrease saturated edges and increase zero edges,
but cannot cross either active bound. -/
def Admissible (f h : Edge → ℝ) : Prop :=
  ∀ e, (f e = 0 → 0 ≤ h e) ∧ (f e = G.capacity e → h e ≤ 0)

omit [Fintype Edge] in
theorem admissible_zero (f : Edge → ℝ) : G.Admissible f 0 :=
  fun _ => ⟨fun _ => le_rfl, fun _ => le_rfl⟩

omit [Fintype Edge] in
theorem admissible_add {f h k : Edge → ℝ}
    (hh : G.Admissible f h) (hk : G.Admissible f k) : G.Admissible f (h + k) :=
  fun e => ⟨fun he => add_nonneg ((hh e).1 he) ((hk e).1 he),
    fun he => add_nonpos ((hh e).2 he) ((hk e).2 he)⟩

theorem admissible_step {s t : Vertex} {f h : Edge → ℝ}
    (hf : G.Feasible s t f) (hh : G.Admissible f h) :
    ∃ δ : ℝ, 0 < δ ∧ f + δ • h ∈ Set.Icc 0 G.capacity := by
  obtain ⟨δ, hp, hδ⟩ := finite_box_step G.capacity f h hf.1.1 hf.1.2
    (fun e => (hh e).1) (fun e => (hh e).2)
  exact ⟨δ, hp, fun e => (hδ e).1, fun e => (hδ e).2⟩

def unit (e : Edge) : Edge → ℝ := fun k => if k = e then 1 else 0

theorem divergence_unit (e : Edge) (v : Vertex) :
    G.divergence (unit e) v = G.incidence e v := by
  simp [divergence, unit, mul_ite]

theorem divergence_neg (f : Edge → ℝ) (v : Vertex) :
    G.divergence (-f) v = -G.divergence f v := by
  simp [divergence, sum_neg_distrib]

omit [Fintype Edge] in
theorem admissible_unit {f : Edge → ℝ} (e : Edge) (he : f e < G.capacity e) :
    G.Admissible f (unit e) := by
  intro k
  by_cases hk : k = e
  · subst k
    simp only [unit]
    exact ⟨fun _ => zero_le_one, fun hc => False.elim ((ne_of_lt he) hc)⟩
  · simp [unit, hk]

omit [Fintype Edge] in
theorem admissible_neg_unit {f : Edge → ℝ} (e : Edge) (he : 0 < f e) :
    G.Admissible f (-unit e) := by
  intro k
  by_cases hk : k = e
  · subst k
    simp only [Pi.neg_apply, unit]
    exact ⟨fun hz => False.elim ((ne_of_gt he) hz), fun _ => by norm_num⟩
  · simp [unit, hk]

/-- A residual step either increases an unsaturated edge or decreases a
positive edge. Parallel and oppositely directed arcs remain distinct. -/
def Residual (f : Edge → ℝ) (u v : Vertex) : Prop :=
  ∃ e, (G.source e = u ∧ G.target e = v ∧ f e < G.capacity e) ∨
    (G.target e = u ∧ G.source e = v ∧ 0 < f e)

theorem residual_direction {f : Edge → ℝ} {u v : Vertex} (hr : G.Residual f u v) :
    ∃ h, G.Admissible f h ∧ ∀ w,
      G.divergence h w = (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  obtain ⟨e, ⟨hs, ht, he⟩ | ⟨ht, hs, he⟩⟩ := hr
  · refine ⟨unit e, G.admissible_unit e he, fun w => ?_⟩
    simp only [G.divergence_unit, incidence, hs, ht, eq_comm]
  · refine ⟨-unit e, G.admissible_neg_unit e he, fun w => ?_⟩
    rw [G.divergence_neg, G.divergence_unit]
    simp only [incidence, hs, ht, eq_comm]
    ring

/-- Residual walks give admissible directions by addition. Telescoping
divergences remove internal vertices; repeated arcs require no path erasure. -/
theorem reachable_direction {f : Edge → ℝ} {u v : Vertex}
    (hr : Relation.ReflTransGen (G.Residual f) u v) :
    ∃ h, G.Admissible f h ∧ ∀ w,
      G.divergence h w = (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  induction hr with
  | refl => exact ⟨0, G.admissible_zero f, fun w => by simp⟩
  | tail _ step ih =>
    obtain ⟨h, hh, hd⟩ := ih
    obtain ⟨k, hk, kd⟩ := G.residual_direction step
    refine ⟨h + k, G.admissible_add hh hk, fun w => ?_⟩
    rw [G.divergence_add, hd, kd]
    ring

theorem maximum_no_residual {s t : Vertex} (hst : s ≠ t) {f : Edge → ℝ}
    (hf : G.Feasible s t f)
    (hm : ∀ g, G.Feasible s t g → G.divergence g s ≤ G.divergence f s) :
    ¬ Relation.ReflTransGen (G.Residual f) s t := by
  intro hr
  obtain ⟨h, hh, hd⟩ := G.reachable_direction hr
  obtain ⟨δ, hp, hbox⟩ := G.admissible_step hf hh
  have hg : G.Feasible s t (f + δ • h) := by
    refine ⟨hbox, fun v hs ht => ?_⟩
    rw [G.divergence_add, G.divergence_smul, hf.2 v hs ht, hd]
    simp [hs, ht]
  have he := hm _ hg
  rw [G.divergence_add, G.divergence_smul, hd] at he
  simp [hst] at he
  linarith

def crossingSum (f : Edge → ℝ) (U : Set Vertex) : ℝ :=
  ∑ e, if G.source e ∈ U ∧ G.target e ∉ U then f e else 0

def cutCapacity (U : Set Vertex) : ℝ := G.crossingSum G.capacity U

variable [Fintype Vertex]

/-- Summed divergence equals outgoing flow minus incoming flow. Every
physical edge appears once, irrespective of parallel arcs or loops. -/
theorem sum_divergence (f : Edge → ℝ) (U : Set Vertex) :
    ∑ v ∈ U.toFinset, G.divergence f v = G.crossingSum f U - G.crossingSum f Uᶜ := by
  calc
    _ = ∑ e, ∑ v ∈ U.toFinset, G.incidence e v * f e := by
      unfold divergence
      rw [sum_comm]
    _ = ∑ e, ((if G.source e ∈ U then f e else 0) -
        (if G.target e ∈ U then f e else 0)) := by
      apply sum_congr rfl
      intro e _
      simp [incidence, sub_mul, sum_sub_distrib, ite_mul, eq_comm]
    _ = _ := by
      unfold crossingSum
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      by_cases hs : G.source e ∈ U <;> by_cases ht : G.target e ∈ U <;> simp [hs, ht]

theorem value_eq_net_cut {s t : Vertex} {f : Edge → ℝ} (hf : G.Feasible s t f)
    {U : Set Vertex} (hs : s ∈ U) (ht : t ∉ U) :
    G.divergence f s = G.crossingSum f U - G.crossingSum f Uᶜ := by
  rw [← G.sum_divergence]
  symm
  apply sum_eq_single s
  · intro v hv hvs
    exact hf.2 v hvs (fun hvt => ht (hvt ▸ Set.mem_toFinset.mp hv))
  · exact fun h => (h (Set.mem_toFinset.mpr hs)).elim

/-- Weak duality: every feasible flow value is at most every separating
cut capacity. Incoming edges across the cut cannot improve that bound. -/
theorem value_le_cut {s t : Vertex} {f : Edge → ℝ} (hf : G.Feasible s t f)
    {U : Set Vertex} (hs : s ∈ U) (ht : t ∉ U) :
    G.divergence f s ≤ G.cutCapacity U := by
  have ho : G.crossingSum f U ≤ G.cutCapacity U := by
    apply sum_le_sum
    intro e _
    split_ifs <;> [exact hf.1.2 e; exact le_rfl]
  have hi : 0 ≤ G.crossingSum f Uᶜ := by
    apply sum_nonneg
    intro e _
    split_ifs <;> [exact hf.1.1 e; exact le_rfl]
  rw [G.value_eq_net_cut hf hs ht]
  linarith

/-- Max-flow/min-cut for finite directed multigraphs with arbitrary
nonnegative real capacities. Together with `value_le_cut`, equality
certifies both maximal flow and minimal separating cut. -/
theorem max_flow_min_cut (s t : Vertex) (hst : s ≠ t) :
    ∃ f U, G.Feasible s t f ∧ s ∈ U ∧ t ∉ U ∧ G.divergence f s = G.cutCapacity U := by
  obtain ⟨f, hf, hm⟩ := G.exists_maximum s t
  let U : Set Vertex := {v | Relation.ReflTransGen (G.Residual f) s v}
  have hs : s ∈ U := Relation.ReflTransGen.refl
  have ht : t ∉ U := G.maximum_no_residual hst hf hm
  have ho : G.crossingSum f U = G.cutCapacity U := by
    apply sum_congr rfl
    intro e _
    split_ifs with he
    · apply le_antisymm (hf.1.2 e)
      by_contra hc
      exact he.2 (he.1.tail ⟨e, Or.inl ⟨rfl, rfl, lt_of_not_ge hc⟩⟩)
    · rfl
  have hi : G.crossingSum f Uᶜ = 0 := by
    apply sum_eq_zero
    intro e _
    split_ifs with he
    · apply le_antisymm ?_ (hf.1.1 e)
      by_contra hc
      have hr : G.target e ∈ U := by simpa using he.2
      exact he.1 (hr.tail ⟨e, Or.inr ⟨rfl, rfl, lt_of_not_ge hc⟩⟩)
    · rfl
  refine ⟨f, U, hf, hs, ht, ?_⟩
  rw [G.value_eq_net_cut hf hs ht, ho, hi, sub_zero]

/-- A nonnegative real demand below every cut is attained exactly,
by scaling the maximum flow if necessary. -/
theorem exists_flow_of_cut_bound (s t : Vertex) (hst : s ≠ t) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ U, s ∈ U → t ∉ U → R ≤ G.cutCapacity U) :
    ∃ f, G.Feasible s t f ∧ G.divergence f s = R := by
  by_cases hz : R = 0
  · exact ⟨0, G.feasible_zero s t, by simp [hz]⟩
  obtain ⟨f, U, hf, hs, ht, he⟩ := G.max_flow_min_cut s t hst
  have hle : R ≤ G.divergence f s := he ▸ hcut U hs ht
  have hp : 0 < G.divergence f s := (lt_of_le_of_ne hR (Ne.symm hz)).trans_le hle
  refine ⟨(R / G.divergence f s) • f,
    G.feasible_smul hf (div_nonneg hR hp.le) ((div_le_one hp).mpr hle), ?_⟩
  rw [G.divergence_smul, div_mul_cancel₀ _ hp.ne']

end Network
end
end LeanMachine.FiniteFlow

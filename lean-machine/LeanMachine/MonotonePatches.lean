import LeanMachine.FiniteIncidence
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Variation under monotone patches of the identity

Count threshold crossings once, then reuse the count for every metric-valued
path. A monotone patch on an order-connected domain has at most one downward
crossing of each threshold, hence at most three crossings in total.
-/

namespace LeanMachine.MonotonePatches

open Classical Finset
open scoped BigOperators

/-- Either orientation of weak monotonicity on a domain. -/
def SignedMonotoneOn (f : ℕ → ℕ) (D : Set ℕ) : Prop :=
  MonotoneOn f D ∨ AntitoneOn f D

/-- Total variation of a finite path, with `n` elementary edges. -/
def variation {X : Type*} [PseudoMetricSpace X] (Y : ℕ → X) (n : ℕ) : ℝ :=
  ∑ e ∈ range n, dist (Y e) (Y (e + 1))

/-- Threshold edges traversed by a jump. -/
def jumpEdges (a b : ℕ) : Finset ℕ := Ico (min a b) (max a b)

theorem mem_jumpEdges {a b z : ℕ} :
    z ∈ jumpEdges a b ↔ (a ≤ z ∧ z < b) ∨ (b ≤ z ∧ z < a) := by
  simp only [jumpEdges, mem_Ico]
  omega

/-- Exact crossing multiplicity of a time map. -/
def crossings (f : ℕ → ℕ) (n z : ℕ) : ℕ :=
  ((range n).filter (fun e => z ∈ jumpEdges (f e) (f (e + 1)))).card

def downcrossings (f : ℕ → ℕ) (n z : ℕ) : ℕ :=
  ((range n).filter (fun e => f (e + 1) ≤ z ∧ z < f e)).card

/-- Upward crossings exceed downward crossings by at most one. -/
theorem crossings_le_twice_down_add_one (f : ℕ → ℕ) (n z : ℕ) :
    crossings f n z ≤ 2 * downcrossings f n z + 1 := by
  let b : ℕ → ℝ := fun t => if z < f t then 1 else 0
  have he (e : ℕ) :
      (if z ∈ jumpEdges (f e) (f (e + 1)) then (1 : ℝ) else 0) =
        2 * (if f (e + 1) ≤ z ∧ z < f e then 1 else 0) + b (e + 1) - b e := by
    simp only [mem_jumpEdges, b]
    split_ifs <;> norm_num <;> omega
  have hs := Finset.sum_congr (s₁ := range n) rfl (fun e _ => he e)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at hs
  have ht : (∑ e ∈ range n, b (e + 1)) - ∑ e ∈ range n, b e = b n - b 0 := by
    rw [← sum_sub_distrib, sum_range_sub]
  have hc : (crossings f n z : ℝ) =
      2 * downcrossings f n z + b n - b 0 := by
    simp only [crossings, downcrossings, ← sum_boole] at *
    linarith
  have hb0 : 0 ≤ b 0 := by dsimp [b]; split_ifs <;> norm_num
  have hbn : b n ≤ 1 := by dsimp [b]; split_ifs <;> norm_num
  have : (crossings f n z : ℝ) ≤ 2 * downcrossings f n z + 1 := by linarith
  exact_mod_cast this

/-- One monotone patch of the identity cannot cross a threshold down twice. -/
theorem downcrossings_le_one {f : ℕ → ℕ} {D : Set ℕ}
    (hD : D.OrdConnected) (hf : SignedMonotoneOn f D)
    (hid : ∀ t ∉ D, f t = t) (n z : ℕ) : downcrossings f n z ≤ 1 := by
  have no_two {e j : ℕ} (hej : e < j)
      (he : f (e + 1) ≤ z ∧ z < f e) (hj : f (j + 1) ≤ z ∧ z < f j) : False := by
    have hleft : e ∈ D ∨ e + 1 ∈ D := by
      by_contra h
      push Not at h
      have := hid e h.1
      have := hid (e + 1) h.2
      omega
    have hright : j ∈ D ∨ j + 1 ∈ D := by
      by_contra h
      push Not at h
      have := hid j h.1
      have := hid (j + 1) h.2
      omega
    have hm : e + 1 ∈ D ∧ j ∈ D := by
      rcases hleft with hl | hl <;> rcases hright with hr | hr
      · exact ⟨hD.out hl hr ⟨by omega, by omega⟩, hr⟩
      · exact ⟨hD.out hl hr ⟨by omega, by omega⟩, hD.out hl hr ⟨by omega, by omega⟩⟩
      · exact ⟨hl, hr⟩
      · exact ⟨hl, hD.out hl hr ⟨by omega, by omega⟩⟩
    rcases hf with hf | hf
    · have heD : e ∉ D := fun h => by have := hf h hm.1 (by omega); omega
      have hjD : j + 1 ∉ D := fun h => by have := hf hm.2 h (by omega); omega
      have := hid e heD
      have := hid (j + 1) hjD
      omega
    · have := hf hm.1 hm.2 (by omega)
      omega
  apply Finset.card_le_one.mpr
  intro e he j hj
  have he' := (mem_filter.mp he).2
  have hj' := (mem_filter.mp hj).2
  rcases lt_trichotomy e j with h | h | h
  · exact False.elim (no_two h he' hj')
  · exact h
  · exact False.elim (no_two h hj' he')

theorem crossings_le_three {f : ℕ → ℕ} {D : Set ℕ}
    (hD : D.OrdConnected) (hf : SignedMonotoneOn f D)
    (hid : ∀ t ∉ D, f t = t) (n z : ℕ) : crossings f n z ≤ 3 := by
  have := downcrossings_le_one hD hf hid n z
  have := crossings_le_twice_down_add_one f n z
  omega

/-- Keep exact crossing multiplicities before applying any uniform bound. -/
theorem variation_comp_le_crossings {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (f : ℕ → ℕ) (n N : ℕ) (hf : ∀ t ≤ n, f t ≤ N) :
    variation (Y ∘ f) n ≤
      ∑ z ∈ range N, (crossings f n z : ℝ) * dist (Y z) (Y (z + 1)) := by
  calc
    _ ≤ ∑ e ∈ range n, ∑ z ∈ jumpEdges (f e) (f (e + 1)), dist (Y z) (Y (z + 1)) := by
      apply sum_le_sum
      intro e _
      rcases le_total (f e) (f (e + 1)) with h | h
      · simpa only [Function.comp_apply, jumpEdges, min_eq_left h, max_eq_right h] using
          dist_le_Ico_sum_dist Y h
      · simpa only [Function.comp_apply, jumpEdges, min_eq_right h, max_eq_left h,
          dist_comm (Y (f e))] using dist_le_Ico_sum_dist Y h
    _ = _ := by
      simpa only [crossings, jumpEdges, mem_Ico, nsmul_eq_mul] using
        FiniteIncidence.sum_eq_sum_multiplicity (range n) (range N)
          (fun e => jumpEdges (f e) (f (e + 1))) (fun z => dist (Y z) (Y (z + 1)))
          (by
            intro e he z hz
            have he' := mem_range.mp he
            have h0 := hf e (by omega)
            have h1 := hf (e + 1) (by omega)
            have := mem_jumpEdges.mp hz
            exact mem_range.mpr (by omega))

theorem variation_comp_le {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (f : ℕ → ℕ) (n N C : ℕ) (hf : ∀ t ≤ n, f t ≤ N)
    (hC : ∀ z < N, crossings f n z ≤ C) :
    variation (Y ∘ f) n ≤ C * variation Y N := by
  calc
    _ ≤ _ := variation_comp_le_crossings Y f n N hf
    _ ≤ ∑ z ∈ range N, (C : ℝ) * dist (Y z) (Y (z + 1)) :=
      sum_le_sum fun z hz => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hC z (mem_range.mp hz)) dist_nonneg
    _ = _ := by rw [← mul_sum]; rfl

/-- No regression assumption is needed: only preservation of the finite time range. -/
theorem variation_patch_le_three {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) {f : ℕ → ℕ} {D : Set ℕ} (n : ℕ)
    (hD : D.OrdConnected) (hf : SignedMonotoneOn f D)
    (hid : ∀ t ∉ D, f t = t) (hb : ∀ t ≤ n, f t ≤ n) :
    variation (Y ∘ f) n ≤ 3 * variation Y n :=
  variation_comp_le Y f n n 3 hb (fun z _ => crossings_le_three hD hf hid n z)

/-- An action is active on an interval, monotone there in either direction,
and strictly decreases time when active. Its inactive behavior is identity. -/
structure Action where
  domain : Set ℕ
  map : ℕ → ℕ
  connected : domain.OrdConnected
  monotone : SignedMonotoneOn map domain
  decreases : ∀ t ∈ domain, map t < t

namespace Action

noncomputable def apply (a : Action) (t : ℕ) : ℕ := if t ∈ a.domain then a.map t else t

theorem apply_eq (a : Action) {t : ℕ} (ht : t ∈ a.domain) : a.apply t = a.map t := by
  simp [apply, ht]

theorem apply_eq_self (a : Action) {t : ℕ} (ht : t ∉ a.domain) : a.apply t = t := by
  simp [apply, ht]

theorem apply_ne_self_iff (a : Action) (t : ℕ) : a.apply t ≠ t ↔ t ∈ a.domain := by
  by_cases h : t ∈ a.domain
  · simp [apply, h, (a.decreases t h).ne]
  · simp [apply, h]

theorem apply_le (a : Action) (t : ℕ) : a.apply t ≤ t := by
  by_cases h : t ∈ a.domain
  · rw [a.apply_eq h]; exact (a.decreases t h).le
  · rw [a.apply_eq_self h]

theorem apply_monotone (a : Action) : SignedMonotoneOn a.apply a.domain := by
  rcases a.monotone with hm | hm
  · exact Or.inl fun _ hx _ hy h => by simpa only [a.apply_eq hx, a.apply_eq hy] using hm hx hy h
  · exact Or.inr fun _ hx _ hy h => by simpa only [a.apply_eq hx, a.apply_eq hy] using hm hx hy h

/-- Execution in list order, including identity actions at inactive arguments. -/
noncomputable def endpoint : List Action → ℕ → ℕ
  | [], t => t
  | a :: w, t => endpoint w (a.apply t)

/-- Exactly the starting times for which every action is nonidentity. -/
def success : List Action → Set ℕ
  | [] => Set.univ
  | a :: w => a.domain ∩ a.apply ⁻¹' success w

theorem success_cons_iff (a : Action) (w : List Action) (t : ℕ) :
    t ∈ success (a :: w) ↔ a.apply t ≠ t ∧ a.apply t ∈ success w := by
  simp only [success, Set.mem_inter_iff, Set.mem_preimage, a.apply_ne_self_iff]

theorem endpoint_le (w : List Action) (t : ℕ) : endpoint w t ≤ t := by
  induction w generalizing t with
  | nil => exact le_rfl
  | cons a w ih => exact (ih _).trans (a.apply_le t)

/-- Success is order-connected, and its endpoint map has a single orientation. -/
theorem success_structure (w : List Action) :
    (success w).OrdConnected ∧ SignedMonotoneOn (endpoint w) (success w) := by
  induction w with
  | nil => exact ⟨Set.ordConnected_univ, Or.inl (monotone_id.monotoneOn _)⟩
  | cons a w ih =>
    have hc : (success (a :: w)).OrdConnected := by
      rcases a.apply_monotone with hm | hm
      · obtain ⟨U, hU, he⟩ := ih.1.preimage_monotoneOn hm
        change (a.domain ∩ a.apply ⁻¹' success w).OrdConnected
        rw [he]
        exact a.connected.inter hU
      · obtain ⟨U, hU, he⟩ := ih.1.preimage_antitoneOn hm
        change (a.domain ∩ a.apply ⁻¹' success w).OrdConnected
        rw [he]
        exact a.connected.inter hU
    refine ⟨hc, ?_⟩
    rcases a.apply_monotone with ha | ha <;> rcases ih.2 with hw | hw
    · exact Or.inl fun _ hx _ hy h => hw hx.2 hy.2 (ha hx.1 hy.1 h)
    · exact Or.inr fun _ hx _ hy h => hw hx.2 hy.2 (ha hx.1 hy.1 h)
    · exact Or.inr fun _ hx _ hy h => hw hy.2 hx.2 (ha hx.1 hy.1 h)
    · exact Or.inl fun _ hx _ hy h => hw hy.2 hx.2 (ha hx.1 hy.1 h)

/-- Run the word on its success interval and use identity elsewhere. -/
noncomputable def successfulMap (w : List Action) (t : ℕ) : ℕ :=
  if t ∈ success w then endpoint w t else t

theorem endpoint_append (v w : List Action) (t : ℕ) :
    endpoint (v ++ w) t = endpoint w (endpoint v t) := by
  induction v generalizing t with
  | nil => rfl
  | cons a v ih => exact ih _

theorem success_append (v w : List Action) (t : ℕ) :
    t ∈ success (v ++ w) ↔ t ∈ success v ∧ endpoint v t ∈ success w := by
  induction v generalizing t with
  | nil => simp [success, endpoint]
  | cons a v ih => simp [success, endpoint, ih, and_assoc]

/-- The successful nonempty word as one action. Empty words use the empty
domain, giving the identity map without pretending that identity is strict. -/
noncomputable def successfulAction (w : List Action) : Action where
  domain := if w = [] then ∅ else success w
  map := endpoint w
  connected := by split_ifs; exact Set.ordConnected_empty; exact (success_structure w).1
  monotone := by
    split_ifs
    · exact Or.inl (fun _ h => False.elim h)
    · exact (success_structure w).2
  decreases := by
    intro t ht
    cases w with
    | nil => simp at ht
    | cons a w =>
      have ha : t ∈ a.domain := by simpa [success] using ht.1
      exact (endpoint_le w (a.apply t)).trans_lt (by rw [a.apply_eq ha]; exact a.decreases t ha)

theorem successfulAction_apply (w : List Action) : (successfulAction w).apply = successfulMap w := by
  funext t
  cases w with
  | nil => simp [successfulAction, apply, successfulMap, success, endpoint]
  | cons a w => simp [successfulAction, apply, successfulMap]

theorem variation_successfulMap {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (w : List Action) (n : ℕ) :
    variation (Y ∘ successfulMap w) n ≤ 3 * variation Y n := by
  obtain ⟨hc, hm⟩ := success_structure w
  apply variation_patch_le_three Y n hc
  · rcases hm with hm | hm
    · exact Or.inl fun _ hx _ hy h => by simpa only [successfulMap, ite_eq_left hx, ite_eq_left hy] using hm hx hy h
    · exact Or.inr fun _ hx _ hy h => by simpa only [successfulMap, ite_eq_left hx, ite_eq_left hy] using hm hx hy h
  · intro t ht; simp [successfulMap, ht]
  · intro t ht
    by_cases h : t ∈ success w
    · simpa only [successfulMap, ite_eq_left h] using (endpoint_le w t).trans ht
    · simp only [successfulMap, ite_eq_right h]; exact ht

end Action

/-- A patch is supported in a half-open span and keeps its images in that span. -/
structure Patch where
  left : ℕ
  right : ℕ
  action : Action
  domain_subset : action.domain ⊆ Set.Ioc left right
  mapsTo : Set.MapsTo action.map action.domain (Set.Ioc left right)

namespace Patch

def edges (p : Patch) : Finset ℕ := Ico p.left p.right

theorem apply_eq_self (p : Patch) {t : ℕ} (ht : t ∉ Set.Ioc p.left p.right) :
    p.action.apply t = t := p.action.apply_eq_self (fun h => ht (p.domain_subset h))

theorem apply_mem (p : Patch) {t : ℕ} (ht : t ∈ Set.Ioc p.left p.right) :
    p.action.apply t ∈ Set.Ioc p.left p.right := by
  by_cases h : t ∈ p.action.domain
  · rw [p.action.apply_eq h]; exact p.mapsTo h
  · rw [p.action.apply_eq_self h]; exact ht

/-- A threshold outside a patch's span is unaffected. -/
theorem threshold_iff (p : Patch) {z : ℕ} (hz : z ∉ p.edges) (t : ℕ) :
    z < p.action.apply t ↔ z < t := by
  by_cases h : t ∈ Set.Ioc p.left p.right
  · have hi := p.apply_mem h
    simp only [edges, mem_Ico] at hz
    simp only [Set.mem_Ioc] at h hi
    omega
  · rw [p.apply_eq_self h]

variable {ι : Type*} (I : Finset ι) (P : ι → Patch)

/-- Full spans are disjoint; sharing one excluded lower endpoint is harmless. -/
def Separated : Prop := ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i).edges (P j).edges

theorem Separated.unique_time (hsep : Separated I P) {t : ℕ}
    {a b : ι} (ha : a ∈ I) (hb : b ∈ I)
    (hta : t ∈ Set.Ioc (P a).left (P a).right)
    (htb : t ∈ Set.Ioc (P b).left (P b).right) : a = b := by
  by_contra h
  have hd := disjoint_left.mp (hsep a ha b hb h)
  have he (p : Patch) (hp : t ∈ Set.Ioc p.left p.right) : t - 1 ∈ p.edges := by
    simp only [edges, mem_Ico, Set.mem_Ioc] at *
    omega
  exact hd (he _ hta) (he _ htb)

/-- Apply the unique span's action, or identity outside all spans. -/
noncomputable def pack (t : ℕ) : ℕ :=
  if h : ∃ i ∈ I, t ∈ Set.Ioc (P i).left (P i).right then
    (P h.choose).action.apply t else t

theorem pack_eq_on (hsep : Separated I P) {i : ι} (hi : i ∈ I) {t : ℕ}
    (ht : t ∈ Set.Ioc (P i).left (P i).right) : pack I P t = (P i).action.apply t := by
  have h : ∃ j ∈ I, t ∈ Set.Ioc (P j).left (P j).right := ⟨i, hi, ht⟩
  rw [pack, dite_eq_left h]
  have he := Separated.unique_time I P hsep h.choose_spec.1 hi h.choose_spec.2 ht
  rw [he]

theorem pack_cases (t : ℕ) : pack I P t = t ∨
    ∃ i ∈ I, t ∈ Set.Ioc (P i).left (P i).right ∧ pack I P t = (P i).action.apply t := by
  unfold pack
  split_ifs with h
  · exact Or.inr ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩
  · exact Or.inl rfl

theorem pack_le (t : ℕ) : pack I P t ≤ t := by
  rcases pack_cases I P t with h | ⟨i, _, _, h⟩
  · exact h.le
  · rw [h]; exact (P i).action.apply_le t

theorem pack_threshold (hsep : Separated I P) {i : ι} (hi : i ∈ I) {z : ℕ}
    (hz : z ∈ (P i).edges) (t : ℕ) :
    z < pack I P t ↔ z < (P i).action.apply t := by
  by_cases ht : t ∈ Set.Ioc (P i).left (P i).right
  · rw [pack_eq_on I P hsep hi ht]
  rw [(P i).apply_eq_self ht]
  rcases pack_cases I P t with h | ⟨j, hj, htj, h⟩
  · rw [h]
  · have hji : j ≠ i := by rintro rfl; exact ht htj
    have hzj : z ∉ (P j).edges := fun hzj =>
      disjoint_left.mp (hsep j hj i hi hji) hzj hz
    rw [h]
    exact (P j).threshold_iff hzj t

theorem pack_threshold_outside {z : ℕ} (hz : ∀ i ∈ I, z ∉ (P i).edges) (t : ℕ) :
    z < pack I P t ↔ z < t := by
  rcases pack_cases I P t with h | ⟨i, hi, _, h⟩
  · rw [h]
  · rw [h]; exact (P i).threshold_iff (hz i hi) t

end Patch

theorem crossings_congr {f g : ℕ → ℕ} (n z : ℕ)
    (h : ∀ t, z < f t ↔ z < g t) : crossings f n z = crossings g n z := by
  unfold crossings
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro e _
  simp only [mem_jumpEdges, ← not_lt]
  rw [h e, h (e + 1)]

/-- Packing arbitrarily many disjoint patches still costs only a factor of three. -/
theorem variation_pack {X ι : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (I : Finset ι) (P : ι → Patch) (hsep : Patch.Separated I P) (n : ℕ) :
    variation (Y ∘ Patch.pack I P) n ≤ 3 * variation Y n := by
  apply variation_comp_le Y _ n n 3 (fun t ht => (Patch.pack_le I P t).trans ht)
  intro z _
  by_cases hz : ∃ i ∈ I, z ∈ (P i).edges
  · obtain ⟨i, hi, hz⟩ := hz
    rw [crossings_congr n z (Patch.pack_threshold I P hsep hi hz)]
    exact crossings_le_three (P i).action.connected (P i).action.apply_monotone
      (fun _ h => (P i).action.apply_eq_self h) n z
  · have hz' : ∀ i ∈ I, z ∉ (P i).edges := by simpa using hz
    rw [crossings_congr (g := id) n z (Patch.pack_threshold_outside I P hz')]
    exact crossings_le_three Set.ordConnected_univ (Or.inl (monotone_id.monotoneOn _))
      (fun _ _ => rfl) n z

/-- The factor three is attained by a single regressive interval patch. -/
theorem exists_sharp_patch : ∃ p : Patch, ∃ Y : ℕ → ℝ,
    variation Y 5 = 1 ∧ variation (Y ∘ p.action.apply) 5 = 3 := by
  let a : Action := {
    domain := Set.Ioc 2 4
    map := fun _ => 1
    connected := Set.ordConnected_Ioc
    monotone := Or.inr (fun _ _ _ _ _ => le_rfl)
    decreases := fun _ h => by have := h.1; omega }
  let p : Patch := {
    left := 0
    right := 4
    action := a
    domain_subset := fun _ h => ⟨by have := h.1; omega, h.2⟩
    mapsTo := fun _ _ => by norm_num [a] }
  refine ⟨p, (fun t => if 2 ≤ t then 1 else 0), ?_⟩
  norm_num [p, a, Action.apply, variation, sum_range_succ, Real.dist_eq, Function.comp_def]

end LeanMachine.MonotonePatches

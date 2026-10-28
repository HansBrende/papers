import LeanMachine.FiniteOrbits

/-! Finite lists of time maps, their summed variation, and ordered insertions.
The bounds apply to every pseudometric-valued path, including paths with
repeated values. Lists retain multiplicity, so coincident slots are charged. -/

namespace LeanMachine.SourceBank

open Classical Finset MonotonePatches

noncomputable section

abbrev Bank := List (ℕ → ℕ)

def values (B : Bank) (t : ℕ) : Finset ℕ := (B.map (fun a => a t)).toFinset

def cost {X : Type*} [PseudoMetricSpace X] (B : Bank) (Y : ℕ → X) (n : ℕ) : ℝ :=
  (B.map (fun a => variation (Y ∘ a) n)).sum

/-- A uniform bound, before choosing the path or its horizon. -/
def Bounded (B : Bank) (C : ℝ) : Prop :=
  ∀ {X : Type} [PseudoMetricSpace X] (Y : ℕ → X) (n : ℕ), cost B Y n ≤ C * variation Y n

theorem mem_values {B : Bank} {t u : ℕ} :
    u ∈ values B t ↔ ∃ a ∈ B, a t = u := by simp [values, eq_comm]

theorem cost_append {X : Type*} [PseudoMetricSpace X] (B D : Bank) (Y : ℕ → X) (n : ℕ) :
    cost (B ++ D) Y n = cost B Y n + cost D Y n := by simp [cost]

theorem bounded_append {B D : Bank} {C E : ℝ} (hB : Bounded B C) (hD : Bounded D E) :
    Bounded (B ++ D) (C + E) := by
  intro X _ Y n
  rw [cost_append, add_mul]
  exact add_le_add (hB Y n) (hD Y n)

theorem bounded_identity : Bounded [id] 1 := by
  intro X _ Y n
  simp [cost]

theorem bounded_mono {B : Bank} {C D : ℝ} (hB : Bounded B C) (hCD : C ≤ D) :
    Bounded B D := by
  intro X _ Y n
  exact (hB Y n).trans (mul_le_mul_of_nonneg_right hCD
    (Finset.sum_nonneg (fun _ _ => dist_nonneg)))

/-- Specialization to a unit-speed path on a finite horizon. -/
theorem Bounded.unit_variation {B : Bank} {C : ℝ} (hB : Bounded B C) (hC : 0 ≤ C)
    {X : Type} [PseudoMetricSpace X] (Y : ℕ → X) (n : ℕ)
    (hY : ∀ e < n, dist (Y e) (Y (e + 1)) ≤ 1) : cost B Y n ≤ C * n := by
  have hv : variation Y n ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _e ∈ range n, (1 : ℝ) := sum_le_sum (fun e he => hY e (mem_range.mp he))
      _ = _ := by simp
  exact (hB Y n).trans (mul_le_mul_of_nonneg_left hv hC)

/-- Compose every outer slot with every inner slot. -/
def compose (D B : Bank) : Bank := D.flatMap (fun b => B.map (fun a => b ∘ a))

theorem compose_length (D B : Bank) : (compose D B).length = D.length * B.length := by
  induction D with
  | nil => simp [compose]
  | cons b D ih => simp [compose, Nat.add_mul, Nat.add_comm]

theorem mem_compose {D B : Bank} {f : ℕ → ℕ} :
    f ∈ compose D B ↔ ∃ b ∈ D, ∃ a ∈ B, b ∘ a = f := by simp [compose]

theorem bounded_compose {B D : Bank} {C E : ℝ}
    (hB : Bounded B C) (hD : Bounded D E) (hC : 0 ≤ C) :
    Bounded (compose D B) (C * E) := by
  intro X _ Y n
  have h : cost (compose D B) Y n ≤ C * cost D Y n := by
    clear hD E
    induction D with
    | nil => simp [compose, cost]
    | cons b D ih =>
      change cost ((B.map (fun a => b ∘ a)) ++ compose D B) Y n ≤ _
      rw [cost_append]
      have hb := hB (Y ∘ b) n
      simpa only [cost, List.map_map, Function.comp_def, List.map_cons,
        List.sum_cons, mul_add] using add_le_add hb ih
  exact h.trans ((mul_le_mul_of_nonneg_left (hD Y n) hC).trans_eq (mul_assoc ..).symm)

theorem bounded_action (f : Action) : Bounded [f.apply] 3 := by
  intro X _ Y n
  simpa only [cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
    variation_patch_le_three Y n f.connected f.apply_monotone
      (fun _ ht => f.apply_eq_self ht) (fun t ht => (f.apply_le t).trans ht)

/-- All ordered subsequences of exceptions, with a core slot before, between
and after them. The list order of exceptions is their execution order. -/
def ordered (B : Bank) : List Action → Bank
  | [] => B
  | f :: fs => ordered B fs ++ compose (ordered B fs) (compose [f.apply] B)

theorem ordered_length (B : Bank) (fs : List Action) :
    (ordered B fs).length = B.length * (1 + B.length) ^ fs.length := by
  induction fs with
  | nil => simp [ordered]
  | cons f fs ih =>
    simp only [ordered, List.length_append, compose_length, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.one_mul, ih, pow_succ]
    ring

theorem bounded_ordered {B : Bank} {C : ℝ} (hB : Bounded B C) (hC : 0 ≤ C)
    (fs : List Action) : Bounded (ordered B fs) (C * (1 + 3 * C) ^ fs.length) := by
  induction fs with
  | nil =>
    intro X _ Y n
    simpa only [ordered, List.length_nil, pow_zero, mul_one] using hB Y n
  | cons f fs ih =>
    have hinner : Bounded (compose [f.apply] B) (C * 3) :=
      bounded_compose hB (bounded_action f) hC
    have hterm : Bounded (compose (ordered B fs) (compose [f.apply] B))
        ((C * 3) * (C * (1 + 3 * C) ^ fs.length)) :=
      bounded_compose hinner ih (mul_nonneg hC (by norm_num))
    intro X _ Y n
    have h := bounded_append ih hterm Y n
    have he : C * (1 + 3 * C) ^ (fs.length + 1) =
        C * (1 + 3 * C) ^ fs.length + (C * 3) * (C * (1 + 3 * C) ^ fs.length) := by
      rw [pow_succ]; ring
    simpa only [ordered, List.length_cons, he] using h

end
end LeanMachine.SourceBank

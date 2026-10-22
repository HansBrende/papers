import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! Geometric charge decay on fixed-branching address trees. The finite-tuple
enumeration and all infinite-sum infrastructure are imported from mathlib. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

noncomputable def levelCharge {B : ℕ} (V : List (Fin B) → ℝ)
    (w : List (Fin B)) (n : ℕ) : ℝ := ∑ u : Fin n → Fin B, V (w++List.ofFn u)

theorem levelCharge_zero {B : ℕ} (V : List (Fin B) → ℝ) (w : List (Fin B)) :
    levelCharge V w 0=V w := by simp [levelCharge]

theorem levelCharge_succ {B : ℕ} (V : List (Fin B) → ℝ) (w : List (Fin B)) (n : ℕ) :
    levelCharge V w (n+1)=∑ b : Fin B, levelCharge V (w++[b]) n := by
  unfold levelCharge
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin B)).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem levelCharge_nonneg {B : ℕ} {V : List (Fin B) → ℝ} (hV : ∀ w, 0 ≤ V w)
    (w : List (Fin B)) (n : ℕ) : 0 ≤ levelCharge V w n :=
  Finset.sum_nonneg fun _ _ => hV _

theorem levelCharge_le {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hr : 0 ≤ rho) (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (w : List (Fin B)) (n : ℕ) : levelCharge V w n ≤ V w*rho^n := by
  induction n generalizing w with
  | zero => simp [levelCharge_zero]
  | succ n ih =>
    rw [levelCharge_succ]
    calc
      _ ≤ ∑ b : Fin B, V (w++[b])*rho^n := Finset.sum_le_sum fun _ _ => ih _
      _ = (∑ b : Fin B, V (w++[b]))*rho^n := (Finset.sum_mul _ _ _).symm
      _ ≤ (rho*V w)*rho^n := mul_le_mul_of_nonneg_right (hc w) (pow_nonneg hr _)
      _ = V w*rho^(n+1) := by rw [pow_succ]; ring

theorem summable_levelCharge {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w) (w : List (Fin B)) :
    Summable (levelCharge V w) := by
  exact Summable.of_nonneg_of_le (levelCharge_nonneg hV w) (levelCharge_le hr hc w)
    ((summable_geometric_of_lt_one hr hr1).mul_left (V w))

theorem summable_descendant_charge {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w) (w : List (Fin B)) :
    Summable (fun u : List (Fin B) => V (w++u)) := by
  have hs : Summable (fun u : Σ n, Fin n → Fin B => V (w++List.ofFn u.2)) := by
    apply (summable_sigma_of_nonneg (fun u => hV _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
    simp only [tsum_fintype]
    exact summable_levelCharge hV hr hr1 hc w
  exact (List.equivSigmaTuple.symm.summable_iff).mp hs

theorem tsum_deep_charge_eq_levels {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w) (w : List (Fin B)) (h : ℕ) :
    (∑' u : List (Fin B), if h ≤ u.length then V (w++u) else 0)=
      ∑' n : ℕ, if h ≤ n then levelCharge V w n else 0 := by
  let W : List (Fin B) → ℝ := fun u => if h ≤ u.length then V (w++u) else 0
  have hs : Summable W := by
    exact ((summable_descendant_charge hV hr hr1 hc w).indicator {u | h ≤ u.length}).congr
      (fun u => by simp [W,Set.indicator])
  have hsig := List.equivSigmaTuple.symm.summable_iff.mpr hs
  change (∑' u, W u)=_
  rw [← List.equivSigmaTuple.symm.tsum_eq W]
  have hsigsum := hsig.tsum_sigma
  simp only [Function.comp_def] at hsigsum
  rw [hsigsum]
  apply tsum_congr
  intro n
  simp only [W,List.equivSigmaTuple_symm_apply,List.length_ofFn,tsum_fintype]
  by_cases hn : h ≤ n <;> simp [hn,levelCharge]

theorem tsum_deep_charge_le {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w) (w : List (Fin B)) (h : ℕ) :
    (∑' u : List (Fin B), if h ≤ u.length then V (w++u) else 0) ≤
      V w*rho^h/(1-rho) := by
  rw [tsum_deep_charge_eq_levels hV hr hr1 hc w h]
  have hm : Summable (fun n => if h ≤ n then levelCharge V w n else 0) := by
    exact ((summable_levelCharge hV hr hr1 hc w).indicator {n | h ≤ n}).congr
      (fun n => by simp [Set.indicator])
  have hzero : (∑ n ∈ Finset.range h, if h ≤ n then levelCharge V w n else 0)=0 :=
    Finset.sum_eq_zero fun n hn => ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hn))
  have hshift := hm.sum_add_tsum_nat_add h
  simp only [hzero,zero_add,show ∀ n, h ≤ n+h by omega,ite_true] at hshift
  rw [← hshift]
  have hs := (summable_nat_add_iff h).mpr (summable_levelCharge hV hr hr1 hc w)
  have hg := (summable_geometric_of_lt_one hr hr1).mul_left (V w*rho^h)
  calc
    _ ≤ ∑' n : ℕ, (V w*rho^h)*rho^n := hs.tsum_le_tsum (fun n => by
      calc
        _ ≤ V w*rho^(n+h) := levelCharge_le hr hc w (n+h)
        _ = (V w*rho^h)*rho^n := by rw [pow_add]; ring) hg
    _ = V w*rho^h/(1-rho) := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr1,div_eq_mul_inv]

theorem sum_deep_charge_le {B : ℕ} {V : List (Fin B) → ℝ} {rho : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (w : List (Fin B)) (h : ℕ) (S : Finset (List (Fin B))) (hS : ∀ u ∈ S, h ≤ u.length) :
    (∑ u ∈ S, V (w++u)) ≤ V w*rho^h/(1-rho) := by
  have hs : Summable (fun u : List (Fin B) => if h ≤ u.length then V (w++u) else 0) := by
    exact ((summable_descendant_charge hV hr hr1 hc w).indicator {u | h ≤ u.length}).congr
      (fun u => by simp [Set.indicator])
  calc
    _ = ∑ u ∈ S, if h ≤ u.length then V (w++u) else 0 :=
      Finset.sum_congr rfl fun u hu => (ite_eq_left (hS u hu)).symm
    _ ≤ ∑' u : List (Fin B), if h ≤ u.length then V (w++u) else 0 :=
      hs.sum_le_tsum S (fun u _ => by split_ifs <;> first | exact hV _ | rfl)
    _ ≤ V w*rho^h/(1-rho) := tsum_deep_charge_le hV hr hr1 hc w h

end TransposeFollowup.RegularMotion

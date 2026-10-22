import TransposeFollowup.ContractingTreeCharge
import Mathlib.Data.List.Infix

/-! Converting the charge decay into bounds on actual assigned ticks. Every
tick in the finite execution set has one owner; no type of work is omitted. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

theorem assigned_tick_bound {ι : Type*} {B : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (S : Finset ι) (owner : ι → List (Fin B)) (h : ℕ)
    (hbudget : ∀ w, ((S.filter (fun t => owner t=w)).card : ℝ) ≤ a*V w)
    (hdepth : ∀ t ∈ S, h ≤ (owner t).length) :
    (S.card : ℝ) ≤ a*V []*rho^h/(1-rho) := by
  rw [Finset.card_eq_sum_card_image owner S,Nat.cast_sum]
  calc
    _ ≤ ∑ w ∈ S.image owner, a*V w := Finset.sum_le_sum fun w _ => hbudget w
    _ = a*(∑ w ∈ S.image owner, V w) := (Finset.mul_sum _ _ _).symm
    _ ≤ a*(V []*rho^h/(1-rho)) := mul_le_mul_of_nonneg_left
      (by
        have hb := sum_deep_charge_le hV hr hr1 hc [] h (S.image owner)
          (fun w hw => by obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hw; exact hdepth t ht)
        simpa only [List.nil_append] using hb) ha
    _ = a*V []*rho^h/(1-rho) := by ring

theorem deep_assigned_tick_bound {ι : Type*} {B : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (S : Finset ι) (owner : ι → List (Fin B)) (h : ℕ)
    (hbudget : ∀ w, ((S.filter (fun t => owner t=w)).card : ℝ) ≤ a*V w) :
    ((S.filter (fun t => h ≤ (owner t).length)).card : ℝ) ≤ a*V []*rho^h/(1-rho) := by
  apply assigned_tick_bound hV hr hr1 ha hc _ owner h
  · intro w
    apply le_trans _ (hbudget w)
    exact_mod_cast Finset.card_le_card (show
      ((S.filter (fun t => h ≤ (owner t).length)).filter (fun t => owner t=w)) ⊆
      S.filter (fun t => owner t=w) from fun t ht => by
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_filter.mp ht).2⟩)
  · intro t ht
    exact (Finset.mem_filter.mp ht).2

theorem subtree_assigned_tick_bound {ι : Type*} {B : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (S : Finset ι) (owner : ι → List (Fin B)) (w : List (Fin B))
    (hbudget : ∀ u, ((S.filter (fun t => owner t=u)).card : ℝ) ≤ a*V u) :
    ((S.filter (fun t => w <+: owner t)).card : ℝ) ≤ a*V w/(1-rho) := by
  let S' := S.filter (fun t => w <+: owner t)
  have hfiber (u : List (Fin B)) :
      S'.filter (fun t => (owner t).drop w.length=u)=S.filter (fun t => owner t=w++u) := by
    ext t
    constructor
    · intro ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht,hp⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨ht,(List.prefix_append_drop hp).trans (congrArg (w++·) he)⟩
    · intro ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨ht,⟨u,he.symm⟩⟩,?_⟩
      rw [he,List.drop_left]
  have hc' : ∀ u, ∑ b : Fin B, V (w++(u++[b])) ≤ rho*V (w++u) := by
    intro u
    simpa only [List.append_assoc] using hc (w++u)
  have hb : ∀ u, ((S'.filter (fun t => (owner t).drop w.length=u)).card : ℝ) ≤ a*V (w++u) := by
    intro u
    rw [hfiber]
    exact hbudget (w++u)
  have h := assigned_tick_bound (V:=fun u => V (w++u)) (fun u => hV _) hr hr1 ha hc'
    S' (fun t => (owner t).drop w.length) 0 hb (fun _ _ => Nat.zero_le _)
  simpa only [List.append_nil,pow_zero,mul_one,S'] using h

theorem card_fin_time_interval {T A E : ℕ} (hE : E ≤ T) :
    (Finset.univ.filter (fun t : Fin T => A ≤ t.val ∧ t.val < E)).card=E-A := by
  rw [← Nat.card_Ico A E]
  apply Finset.card_bij (fun t _ => t.val)
  · intro t ht
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp ht).2
  · intro t ht u hu he
    exact Fin.ext he
  · intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact ⟨⟨n,hn'.2.trans_le hE⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn'⟩,rfl⟩

theorem contiguous_call_duration_bound {B T A E : ℕ} {V : List (Fin B) → ℝ} {rho a : ℝ}
    (hV : ∀ w, 0 ≤ V w) (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hc : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w)
    (owner : Fin T → List (Fin B)) (w : List (Fin B)) (hE : E ≤ T)
    (hcall : ∀ t : Fin T, (A ≤ t.val ∧ t.val < E) ↔ w <+: owner t)
    (hbudget : ∀ u, ((Finset.univ.filter (fun t => owner t=u)).card : ℝ) ≤ a*V u) :
    ((E-A : ℕ) : ℝ) ≤ a*V w/(1-rho) := by
  have heq : Finset.univ.filter (fun t : Fin T => w <+: owner t)=
      Finset.univ.filter (fun t : Fin T => A ≤ t.val ∧ t.val < E) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (hcall t).symm
  have h := subtree_assigned_tick_bound hV hr hr1 ha hc Finset.univ owner w hbudget
  rwa [heq,card_fin_time_interval hE] at h

end TransposeFollowup.RegularMotion

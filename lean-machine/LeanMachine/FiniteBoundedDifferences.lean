import LeanMachine.FiniteUniformProbability

/-! # Bounded differences for the actual finite uniform product

Conditioning is expressed by exact finite product averages. At each step
the conditional mean has range length at most the coordinate bound. Applying
Hoeffding to that mean and inducting on the remaining coordinates gives the
sharp bounded-differences constant without martingale certificates.
-/

namespace LeanMachine.FiniteProbability

open scoped BigOperators

variable {I κ : Type*}

def BoundedChanges (f : (I → κ) → ℝ) (c : I → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j=y j) → |f x-f y|≤c i

variable [Fintype κ] [Nonempty κ]

omit [Fintype κ] [Nonempty κ] in
theorem boundedChanges_cons_tail {n : ℕ} {f : (Fin (n+1) → κ) → ℝ}
    {c : Fin (n+1) → ℝ} (hf : BoundedChanges f c) (a : κ) :
    BoundedChanges (fun y : Fin n → κ => f (Fin.cons a y)) (fun i => c i.succ) := by
  intro i x y hxy
  apply hf i.succ (Fin.cons a x) (Fin.cons a y)
  intro j hj
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    exact hxy j (fun he => hj (congrArg Fin.succ he))

omit [Fintype κ] [Nonempty κ] in
theorem boundedChanges_cons_head {n : ℕ} {f : (Fin (n+1) → κ) → ℝ}
    {c : Fin (n+1) → ℝ} (hf : BoundedChanges f c) (a a' : κ) (y : Fin n → κ) :
    |f (Fin.cons a y)-f (Fin.cons a' y)|≤c 0 := by
  apply hf 0 (Fin.cons a y) (Fin.cons a' y)
  intro j hj
  induction j using Fin.cases with
  | zero => exact (hj rfl).elim
  | succ _ => rfl

theorem avg_exp_boundedChanges_fin (n : ℕ) (f : (Fin n → κ) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0≤c i) (hf : BoundedChanges f c) (t : ℝ) :
    avg (fun x => Real.exp (t*(f x-avg f))) ≤
      Real.exp ((∑ i, (c i)^2)*t^2/8) := by
  induction n with
  | zero =>
    have he (x : Fin 0 → κ) : f x=avg f := by
      have hh : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
      rw [hh,avg_const]
    simp_rw [he,sub_self,mul_zero,Real.exp_zero]
    simp [avg_const]
  | succ n ih =>
    let g : κ → ℝ := fun a => avg (fun y : Fin n → κ => f (Fin.cons a y))
    have hmean : avg f=avg g := avg_cons f
    have hg : ∀ a a', |g a-g a'|≤c 0 := by
      intro a a'
      apply abs_le.mpr
      have hh : ∀ y : Fin n → κ, |f (Fin.cons a y)-f (Fin.cons a' y)|≤c 0 :=
        fun y => boundedChanges_cons_head hf a a' y
      have hlo := le_avg (fun y => (abs_le.mp (hh y)).1)
      have hhi := avg_le (fun y => (abs_le.mp (hh y)).2)
      rw [avg_sub] at hlo hhi
      exact ⟨hlo,hhi⟩
    have hhead := avg_exp_centered_le g (c 0) (hc 0) hg t
    have htail (a : κ) := ih (fun y => f (Fin.cons a y)) (fun i => c i.succ)
      (fun i => hc i.succ) (boundedChanges_cons_tail hf a)
    rw [avg_cons, hmean]
    change avg (fun a : κ => avg (fun y : Fin n → κ =>
      Real.exp (t*(f (Fin.cons a y)-avg g)))) ≤ _
    calc
      _ = avg (fun a => Real.exp (t*(g a-avg g))*
          avg (fun y : Fin n → κ => Real.exp (t*(f (Fin.cons a y)-g a)))) := by
        congr 1
        funext a
        rw [← avg_const_mul]
        congr 1
        funext y
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ avg (fun a => Real.exp (t*(g a-avg g))*
          Real.exp ((∑ i : Fin n, (c i.succ)^2)*t^2/8)) := by
        apply avg_mono
        intro a
        exact mul_le_mul_of_nonneg_left (htail a) (Real.exp_pos _).le
      _ = avg (fun a => Real.exp (t*(g a-avg g)))*
          Real.exp ((∑ i : Fin n, (c i.succ)^2)*t^2/8) := avg_mul_const _ _
      _ ≤ Real.exp ((c 0)^2*t^2/8)*
          Real.exp ((∑ i : Fin n, (c i.succ)^2)*t^2/8) :=
        mul_le_mul_of_nonneg_right hhead (Real.exp_pos _).le
      _ = Real.exp ((∑ i : Fin (n+1), (c i)^2)*t^2/8) := by
        rw [← Real.exp_add,Fin.sum_univ_succ]
        congr 1
        ring

theorem avg_exp_boundedChanges [Fintype I] [DecidableEq I] (f : (I → κ) → ℝ)
    (c : I → ℝ) (hc : ∀ i, 0≤c i) (hf : BoundedChanges f c) (t : ℝ) :
    avg (fun x => Real.exp (t*(f x-avg f))) ≤
      Real.exp ((∑ i, (c i)^2)*t^2/8) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E : (Fin (Fintype.card I) → κ) ≃ (I → κ) :=
    { toFun x i := x (e.symm i)
      invFun x i := x (e i)
      left_inv x := by funext i; simp
      right_inv x := by funext i; simp }
  have hb : BoundedChanges (fun x => f (E x)) (fun i => c (e i)) := by
    intro i x y hxy
    apply hf (e i) (E x) (E y)
    intro j hj
    apply hxy (e.symm j)
    intro he
    apply hj
    rw [← e.apply_symm_apply j, he]
  have hh := avg_exp_boundedChanges_fin (Fintype.card I) (fun x => f (E x))
    (fun i => c (e i)) (fun i => hc (e i)) hb t
  have hm := avg_equiv E f
  rw [hm] at hh
  rw [avg_equiv E (fun x => Real.exp (t*(f x-avg f)))] at hh
  have hs : (∑ i : Fin (Fintype.card I), (c (e i))^2) = ∑ i : I, (c i)^2 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rwa [hs] at hh

theorem prob_upper_of_mgf {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (V : ℝ) (hV : 0≤V)
    (hmgf : ∀ t : ℝ, avg (fun x => Real.exp (t*(f x-avg f))) ≤ Real.exp (V*t^2/8))
    (u : ℝ) (hu : 0≤u) :
    prob (fun x => avg f+u≤f x) ≤ Real.exp (-2*u^2/V) := by
  classical
  by_cases hV0 : V=0
  · simpa only [hV0, div_zero, Real.exp_zero] using prob_le_one (fun x => avg f+u≤f x)
  have hVp : 0<V := lt_of_le_of_ne hV (Ne.symm hV0)
  let t := 4*u/V
  have ht : 0≤t := by dsimp [t]; positivity
  have hp : prob (fun x => avg f+u≤f x) ≤
      Real.exp (-t*u)*avg (fun x => Real.exp (t*(f x-avg f))) := by
    rw [← avg_const_mul]
    apply avg_mono
    intro x
    by_cases hx : avg f+u≤f x
    · rw [ite_eq_left hx, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hh := mul_nonneg ht (show 0≤f x-avg f-u by linarith)
      nlinarith only [hh]
    · rw [ite_eq_right hx]
      positivity
  calc
    _ ≤ Real.exp (-t*u)*avg (fun x => Real.exp (t*(f x-avg f))) := hp
    _ ≤ Real.exp (-t*u)*Real.exp (V*t^2/8) :=
      mul_le_mul_of_nonneg_left (hmgf t) (Real.exp_pos _).le
    _ = Real.exp (-2*u^2/V) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

/-- The exact upper-tail McDiarmid bound for independent uniform labels. -/
theorem boundedDifferences_upper [Fintype I] [DecidableEq I] (f : (I → κ) → ℝ)
    (c : I → ℝ) (hc : ∀ i, 0≤c i) (hf : BoundedChanges f c)
    (u : ℝ) (hu : 0≤u) :
    prob (fun x => avg f+u≤f x) ≤ Real.exp (-2*u^2/(∑ i, (c i)^2)) :=
  prob_upper_of_mgf f _ (Finset.sum_nonneg (fun _i _ => sq_nonneg _))
    (avg_exp_boundedChanges f c hc hf) u hu

/-- The lower tail uses the same actual product law and the same constant. -/
theorem boundedDifferences_lower [Fintype I] [DecidableEq I] (f : (I → κ) → ℝ)
    (c : I → ℝ) (hc : ∀ i, 0≤c i) (hf : BoundedChanges f c)
    (u : ℝ) (hu : 0≤u) :
    prob (fun x => f x≤avg f-u) ≤ Real.exp (-2*u^2/(∑ i, (c i)^2)) := by
  have hn : BoundedChanges (fun x => -f x) c := by
    intro i x y hxy
    simpa only [neg_sub_neg,abs_sub_comm] using hf i x y hxy
  have hh := boundedDifferences_upper (fun x => -f x) c hc hn u hu
  rw [avg_neg] at hh
  have he : (fun x => -avg f+u≤ -f x) = (fun x => f x≤avg f-u) := by
    funext x
    apply propext
    constructor <;> intro h <;> linarith
  rwa [he] at hh

end LeanMachine.FiniteProbability

namespace LeanMachine.FiniteProbability

open scoped BigOperators

theorem BoundedChanges.add {I κ : Type*} {f g : (I → κ) → ℝ} {c e : I → ℝ}
    (hf : BoundedChanges f c) (hg : BoundedChanges g e) :
    BoundedChanges (fun x => f x+g x) (fun i => c i+e i) := by
  intro i x y hxy
  have heq : f x+g x-(f y+g y)=(f x-f y)+(g x-g y) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hf i x y hxy) (hg i x y hxy))

theorem BoundedChanges.const_mul {I κ : Type*} {f : (I → κ) → ℝ} {c : I → ℝ}
    (hf : BoundedChanges f c) (a : ℝ) (ha : 0≤a) :
    BoundedChanges (fun x => a*f x) (fun i => a*c i) := by
  intro i x y hxy
  rw [← mul_sub,abs_mul,abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (hf i x y hxy) ha

/-- Finite weighted sums preserve the actual coordinate-change bounds. -/
theorem BoundedChanges.finset_sum {I κ J : Type*} (S : Finset J)
    (f : J → (I → κ) → ℝ) (c : J → I → ℝ)
    (hf : ∀ j∈S, BoundedChanges (f j) (c j)) :
    BoundedChanges (fun x => ∑ j∈S, f j x) (fun i => ∑ j∈S, c j i) := by
  intro i x y hxy
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j hj => hf j hj i x y hxy))

theorem BoundedChanges.div_const {I κ : Type*} {f : (I → κ) → ℝ} {c : I → ℝ}
    (hf : BoundedChanges f c) (a : ℝ) (ha : 0≤a) :
    BoundedChanges (fun x => f x/a) (fun i => c i/a) := by
  simpa only [div_eq_mul_inv,mul_comm,mul_one] using hf.const_mul (1/a) (by positivity)

end LeanMachine.FiniteProbability

import Transpose.Tape.PlainRobust.CESelect

/-!
# Bounded-degree constraints: plain ⟹ no code on the zero set of a low-degree function

The **discrete derivative** of `f : (Fin L → Bool) → Bool` along `u` is `x ↦ f x ⊕ f (x ⊕ u)`;
`deriv f us` iterates it along a list of directions. `f` has **degree `≤ D`** (`DegLE f D`) if every
derivative of order `D + 1` vanishes (over `F₂` this is the usual degree bound).

* `deriv_const`: a derivative of top order is constant.
* `deriv_true_cover`: if `deriv f us x = true` and `us ≠ []`, some translate of `x` by a sum of a
  sub-list of `us` lies in the zero set of `f` (the `2^{|us|}` values have odd parity, so they are
  not all `true`).
* `zeroSet_cover`: hence the zero set of a function of degree `≤ D` that is not identically `true`
  is covered by `2^D` fixed translates of itself.

With selection among `2^D` shifted codes (`noCode_hintConst_of_noCode`), `NoCode_TM` rules out
codes on every set containing such a zero set (`noCode_lowDegree_of_noCode`). This covers, for
example, `Σ_{i<j} ⟨x_ij, x_ji⟩ = 0` and every quadratic constraint.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

section Degree

variable {L : ℕ}

/-- The discrete derivative of `f` along the directions `us`. -/
def deriv (f : (Fin L → Bool) → Bool) : List (Fin L → Bool) → (Fin L → Bool) → Bool
  | [] => f
  | u :: us => fun x => xor (deriv f us x) (deriv f us (xorVec x u))

/-- `f` has degree at most `D` over `F₂`: every derivative of order `D + 1` vanishes. -/
def DegLE (f : (Fin L → Bool) → Bool) (D : ℕ) : Prop :=
  ∀ us : List (Fin L → Bool), us.length = D + 1 → ∀ x, deriv f us x = false

/-- The sum of the directions selected by the binary digits of `m`. -/
def maskSum : List (Fin L → Bool) → ℕ → (Fin L → Bool)
  | [], _ => fun _ => false
  | u :: us, m => if m % 2 = 1 then xorVec u (maskSum us (m / 2)) else maskSum us (m / 2)

theorem xorVec_assoc' (x u v : Fin L → Bool) : xorVec x (xorVec u v) = xorVec (xorVec x u) v := by
  funext d; simp only [xorVec]; cases x d <;> cases u d <;> cases v d <;> rfl

/-- **A top-order derivative is constant.** -/
theorem deriv_const {f : (Fin L → Bool) → Bool} {D : ℕ} (hf : DegLE f D)
    (us : List (Fin L → Bool)) (hus : us.length = D) (x y : Fin L → Bool) :
    deriv f us x = deriv f us y := by
  have h := hf (xorVec x y :: us) (by simp [hus]) x
  simp only [deriv] at h
  have e : xorVec x (xorVec x y) = y := xorVec_xorVec_left x y
  rw [e] at h
  cases hx : deriv f us x <;> cases hy : deriv f us y <;> simp_all

/-- **A nonzero derivative of positive order finds a zero of `f` in the cube.** -/
theorem deriv_true_cover (f : (Fin L → Bool) → Bool) :
    ∀ (us : List (Fin L → Bool)) (x : Fin L → Bool), us ≠ [] → deriv f us x = true →
      ∃ m < 2 ^ us.length, f (xorVec x (maskSum us m)) = false := by
  intro us
  induction us with
  | nil => intro x h; exact absurd rfl h
  | cons u us ih =>
    intro x _ hd
    simp only [deriv] at hd
    by_cases hnil : us = []
    · -- one direction: `f x ⊕ f (x ⊕ u) = true`
      subst hnil
      simp only [deriv] at hd
      cases hfx : f x
      · refine ⟨0, by simp, ?_⟩
        have e : xorVec x (maskSum [u] 0) = x := by
          funext d; simp [maskSum, xorVec]
        rw [e]; exact hfx
      · refine ⟨1, by simp, ?_⟩
        have e : xorVec x (maskSum [u] 1) = xorVec x u := by
          funext d; simp [maskSum, xorVec]
        rw [e]
        rw [hfx] at hd
        cases hfu : f (xorVec x u) <;> simp_all
    · have hne : us ≠ [] := hnil
      cases hd1 : deriv f us x
      · -- the other term is `true`
        rw [hd1] at hd
        have hd2 : deriv f us (xorVec x u) = true := by simpa using hd
        obtain ⟨m, hm, hfm⟩ := ih (xorVec x u) hne hd2
        refine ⟨2 * m + 1, by simp only [List.length_cons, pow_succ]; omega, ?_⟩
        have e : maskSum (u :: us) (2 * m + 1) = xorVec u (maskSum us m) := by
          simp only [maskSum]
          rw [ite_eq_left (by omega), show (2 * m + 1) / 2 = m by omega]
        rw [e, xorVec_assoc']
        exact hfm
      · obtain ⟨m, hm, hfm⟩ := ih x hne hd1
        refine ⟨2 * m, by simp only [List.length_cons, pow_succ]; omega, ?_⟩
        have e : maskSum (u :: us) (2 * m) = maskSum us m := by
          simp only [maskSum]
          rw [ite_eq_right (by omega), show 2 * m / 2 = m by omega]
        rw [e]
        exact hfm

/-- **The zero set of a low-degree function is covered by `2^D` translates.** If `f` has degree
`≤ D` and is not identically `true`, there are directions `us` (`|us| ≤ D`) such that every input
has a translate by some `maskSum us m`, `m < 2^D`, in the zero set of `f`. -/
theorem zeroSet_cover {f : (Fin L → Bool) → Bool} {D : ℕ} (hf : DegLE f D)
    (hz : ∃ x, f x = false) :
    ∃ us : List (Fin L → Bool), ∀ x, ∃ m < 2 ^ D, f (xorVec x (maskSum us m)) = false := by
  classical
  by_cases hzero : ∀ x, f x = false
  · refine ⟨[], fun x => ⟨0, Nat.two_pow_pos _, hzero _⟩⟩
  push Not at hzero
  obtain ⟨x₀, hx₀⟩ := hzero
  have hx₀' : f x₀ = true := by simpa using hx₀
  -- the largest order `≤ D` with a nonzero derivative
  set P : ℕ → Prop := fun j => ∃ us : List (Fin L → Bool), us.length = j ∧ ∃ x, deriv f us x = true
    with hPdef
  set D' := Nat.findGreatest P D with hD'
  have hP0 : P 0 := ⟨[], rfl, x₀, hx₀'⟩
  have hPD' : P D' := Nat.findGreatest_spec (P := P) (Nat.zero_le D) hP0
  have hD'le : D' ≤ D := Nat.findGreatest_le D
  have hdeg : DegLE f D' := by
    intro us hus x
    by_cases hlt : D' + 1 ≤ D
    · by_contra hne
      have hP : P (D' + 1) := ⟨us, hus, x, by simpa using hne⟩
      have := Nat.le_findGreatest hlt hP
      omega
    · have : D' = D := by omega
      rw [this] at hus
      exact hf us hus x
  obtain ⟨us, hus, x₁, hx₁⟩ := hPD'
  have hconst : ∀ y, deriv f us y = true := fun y => by
    rw [deriv_const hdeg us hus y x₁]; exact hx₁
  rcases Nat.eq_zero_or_pos D' with h0 | hpos
  · -- order `0`: `f` itself is constant `true`, a contradiction
    rw [h0] at hus
    have hnil : us = [] := List.eq_nil_of_length_eq_zero hus
    obtain ⟨z, hzf⟩ := hz
    have := hconst z
    rw [hnil] at this
    simp only [deriv] at this
    rw [hzf] at this
    exact absurd this (by simp)
  · refine ⟨us, fun x => ?_⟩
    have hne : us ≠ [] := by
      intro h; rw [h] at hus; simp at hus; omega
    obtain ⟨m, hm, hfm⟩ := deriv_true_cover f us x hne (hconst x)
    refine ⟨m, lt_of_lt_of_le hm ?_, hfm⟩
    rw [hus]
    exact Nat.pow_le_pow_right (by norm_num) hD'le

/-! ### Degree bounds for concrete functions -/

instance xorCommutative : Std.Commutative xor := ⟨Bool.xor_comm⟩
instance xorAssociative : Std.Associative xor := ⟨Bool.xor_assoc⟩

theorem deriv_xor (f g : (Fin L → Bool) → Bool) :
    ∀ (us : List (Fin L → Bool)) (x : Fin L → Bool),
      deriv (fun y => xor (f y) (g y)) us x = xor (deriv f us x) (deriv g us x) := by
  intro us
  induction us with
  | nil => intro x; rfl
  | cons u us ih =>
    intro x
    simp only [deriv]
    rw [ih, ih]
    cases deriv f us x <;> cases deriv g us x <;> cases deriv f us (xorVec x u) <;>
      cases deriv g us (xorVec x u) <;> rfl

theorem deriv_append (f : (Fin L → Bool) → Bool) (us₂ : List (Fin L → Bool)) :
    ∀ us₁ : List (Fin L → Bool), deriv f (us₁ ++ us₂) = deriv (deriv f us₂) us₁ := by
  intro us₁
  induction us₁ with
  | nil => rfl
  | cons u us₁ ih =>
    funext x
    simp only [List.cons_append, deriv, ih]

theorem deriv_false : ∀ (us : List (Fin L → Bool)) (x : Fin L → Bool),
    deriv (fun _ => false) us x = false := by
  intro us
  induction us with
  | nil => intro x; rfl
  | cons u us ih => intro x; simp only [deriv, ih]; rfl

theorem degLE_mono {f : (Fin L → Bool) → Bool} {D D' : ℕ} (hf : DegLE f D) (hDD : D ≤ D') :
    DegLE f D' := by
  intro us hus x
  have hsplit : us = us.take (D' - D) ++ us.drop (D' - D) := (List.take_append_drop _ _).symm
  have hlen : (us.drop (D' - D)).length = D + 1 := by simp [List.length_drop, hus]; omega
  have hz : deriv f (us.drop (D' - D)) = fun _ => false := funext (hf _ hlen)
  rw [hsplit, deriv_append, hz]
  exact deriv_false _ x

theorem degLE_xor {f g : (Fin L → Bool) → Bool} {D : ℕ} (hf : DegLE f D) (hg : DegLE g D) :
    DegLE (fun y => xor (f y) (g y)) D := by
  intro us hus x
  rw [deriv_xor, hf us hus x, hg us hus x]
  rfl

/-- The product of two input bits has degree `≤ 2`. -/
theorem degLE_and (a b : Fin L) : DegLE (fun x => x a && x b) 2 := by
  intro us hus x
  match us, hus with
  | [u, v, t], _ =>
    simp only [deriv, xorVec]
    cases x a <;> cases x b <;> cases u a <;> cases u b <;> cases v a <;> cases v b <;>
      cases t a <;> cases t b <;> rfl

/-- **A quadratic form over `F₂`** (`x ↦ ⊕_{(p, q) ∈ Q} x_p x_q`) has degree `≤ 2`. -/
theorem degLE_quadForm (Q : Finset (Fin L × Fin L)) :
    DegLE (fun x => Q.fold xor false (fun pq => x pq.1 && x pq.2)) 2 := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro us _ x
    simp only [Finset.fold_empty]
    exact deriv_false us x
  | insert pq Q hpq ih =>
    have e : (fun x : Fin L → Bool => (insert pq Q).fold xor false (fun pq => x pq.1 && x pq.2)) =
        fun x => xor (x pq.1 && x pq.2) (Q.fold xor false (fun pq => x pq.1 && x pq.2)) := by
      funext x; rw [Finset.fold_insert hpq]
    rw [e]
    exact degLE_xor (degLE_and pq.1 pq.2) ih

/-- The zero input is a zero of every quadratic form. -/
theorem quadForm_zero (Q : Finset (Fin L × Fin L)) :
    Q.fold xor false (fun pq => (fun _ : Fin L => false) pq.1 && (fun _ : Fin L => false) pq.2) =
      false := by
  classical
  induction Q using Finset.induction_on with
  | empty => rfl
  | insert pq Q hpq ih => rw [Finset.fold_insert hpq, ih]; rfl

end Degree

/-- **Plain ⟹ no code on any set containing the zero set of a bounded-degree function.** Under
`NoCode_TM`, for every constant `D` and all large `n`: no code solves complete exchange at the
profile capacities on a set `F` containing `{x | f x = false}`, for any `f` of degree `≤ D` over
`F₂` that is not identically `true`. (The zero set is covered by `2^D` translates; the `2^D`
shifted codes are the candidates of a selection.) -/
theorem noCode_lowDegree_of_noCode (h : NoCode_TM) (k G c D : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (Dg : TSDiagram k), Dg.Valid (n * n * entryBits n) → Dg.T ≤ c * (n * n * entryBits n) →
      ∀ (f : (Fin (n * n * entryBits n) → Bool) → Bool), DegLE f D → (∃ x, f x = false) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), {x | f x = false} ⊆ F →
      ∀ code : NetCode, ¬ Dg.Solves n G (Dg.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_hintConst_of_noCode h D k G c hG
  refine ⟨n₀, fun n hn Dg hDg hT f hf hz F hF code hsol => ?_⟩
  obtain ⟨us, hcov⟩ := zeroSet_cover hf hz
  refine hn₀ n hn Dg hDg hT (fun x => Classical.choose (hcov x))
    (fun m => shiftCode Dg n (entryBits n) (blockSize G n) code (maskSum us m))
    (fun x => (Classical.choose_spec (hcov x)).1) (fun x => ?_)
  have hx := (Classical.choose_spec (hcov x)).2
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact solves_shiftCode Dg hsol _ y (hF hx)

/-- **Plain ⟹ no code on the zero set of a quadratic form.** Under `NoCode_TM`, for all constants and
all large `n`: no code solves complete exchange at the profile capacities on a set containing
`{x | ⊕_{(p, q) ∈ Q} x_p x_q = 0}`, for any set `Q` of pairs of input positions. For example, with
`Q` the pairs of equal bits of transposed entries `(i, j)`, `(j, i)`, `i < j`, this is the set
`Σ_{i<j} ⟨x_ij, x_ji⟩ = 0`. -/
theorem noCode_quadForm_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (Dg : TSDiagram k), Dg.Valid (n * n * entryBits n) → Dg.T ≤ c * (n * n * entryBits n) →
      ∀ (Q : Finset (Fin (n * n * entryBits n) × Fin (n * n * entryBits n)))
        (F : Set (Fin (n * n * entryBits n) → Bool)),
        {x | Q.fold xor false (fun pq => x pq.1 && x pq.2) = false} ⊆ F →
      ∀ code : NetCode, ¬ Dg.Solves n G (Dg.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_lowDegree_of_noCode h k G c 2 hG
  refine ⟨n₀, fun n hn Dg hDg hT Q F hF code => ?_⟩
  exact hn₀ n hn Dg hDg hT _ (degLE_quadForm Q) ⟨fun _ => false, quadForm_zero Q⟩ F hF code

end Transpose.Tape.Impl

import SharedDecoders.Model
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

/-! # Distinct final classes along the orbits of a commuting input shift -/

namespace SharedDecoders

variable {d : ℕ} {A κ : Type*} [Nontrivial A]

/-- A covariance relation forces distinct receiver classes across its input
shift. The output shift may be different, and no field or linearity is needed. -/
theorem covariance_no_class_collision
    {p : ZMod d → κ} {K : State d A → State d A}
    (hK : ClassUniform p K) (hKs : Function.Surjective K)
    {s t : ZMod d} (hcov : ∀ X, K (rot s X) = rowRot t (K X))
    {c e : ZMod d} (hp : p c = p e) (he : e - c = s) : c = e := by
  classical
  by_contra hce
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  let Y : State d A := fun _ j => if j = c then a else b
  obtain ⟨X, hX⟩ := hKs Y
  have h := hK.columns_of_same_class hp X 0
  rw [he, hcov, hX] at h
  have hba : b = a := by simpa [rowRot, Y, Ne.symm hce] using h
  exact hab hba.symm

omit [Nontrivial A] in
theorem covariance_nsmul {K : State d A → State d A} {s t : ZMod d}
    (h : ∀ X, K (rot s X) = rowRot t (K X)) (n : ℕ) (X : State d A) :
    K (rot (n • s) X) = rowRot (n • t) (K X) := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← rot_rot, ih, h, rowRot_rowRot, succ_nsmul]

omit [Nontrivial A] in
/-- Exact complete factorization transports a commutation of the first map
to a covariance of the final map. Surjectivity is stated explicitly here. -/
theorem covariance_of_exact_factorization
    {A₀ K : State d A → State d A} {s : ZMod d}
    (hAs : Function.Surjective A₀)
    (hA : ∀ X, A₀ (rot s X) = rot s (A₀ X))
    (hexact : ∀ X, K (A₀ X) = swap X) (Y : State d A) :
    K (rot s Y) = rowRot s (K Y) := by
  obtain ⟨X, rfl⟩ := hAs Y
  rw [← hA, hexact, hexact, swap_rot]

/-- Each natural orbit of a covariance shift has pairwise distinct labels. -/
theorem orbit_classes_injective
    {p : ZMod d → κ} {K : State d A → State d A}
    (hK : ClassUniform p K) (hKs : Function.Surjective K)
    {s t : ZMod d} (hcov : ∀ X, K (rot s X) = rowRot t (K X))
    (c : ZMod d) :
    Function.Injective (fun n : Fin (addOrderOf s) => p (c + (n.val • s))) := by
  intro m n hmn
  have hmn' : c + (m.val • s) = c + (n.val • s) := by
    by_cases hle : m.val ≤ n.val
    · apply covariance_no_class_collision hK hKs (covariance_nsmul hcov (n.val - m.val)) hmn
      rw [add_sub_add_left_eq_sub, sub_nsmul s hle, sub_eq_add_neg]
    · have hle' : n.val ≤ m.val := Nat.le_of_not_ge hle
      symm
      apply covariance_no_class_collision hK hKs (covariance_nsmul hcov (m.val - n.val)) hmn.symm
      rw [add_sub_add_left_eq_sub, sub_nsmul s hle', sub_eq_add_neg]
  apply Fin.ext
  exact (nsmul_injOn_Iio_addOrderOf (x := s) m.isLt n.isLt)
    (add_left_cancel hmn')

/-- Cardinal form of the orbit theorem: at least the order of the input shift
many receiver labels are necessary. Unused labels only weaken this inequality. -/
theorem class_count_ge_order [Fintype κ]
    {p : ZMod d → κ} {K : State d A → State d A}
    (hK : ClassUniform p K) (hKs : Function.Surjective K)
    {s t : ZMod d} (hcov : ∀ X, K (rot s X) = rowRot t (K X)) :
    addOrderOf s ≤ Fintype.card κ := by
  simpa using Fintype.card_le_of_injective _ (orbit_classes_injective hK hKs hcov 0)

/-- Distinct receivers in one class have disjoint covariance orbits. -/
theorem class_orbit_embedding
    {p : ZMod d → κ} {K : State d A → State d A}
    (hK : ClassUniform p K) (hKs : Function.Surjective K)
    {s t : ZMod d} (hcov : ∀ X, K (rot s X) = rowRot t (K X)) (j : κ) :
    Function.Injective (fun z : {c : ZMod d // p c = j} × Fin (addOrderOf s) =>
      z.1.val + z.2.val • s) := by
  rintro ⟨⟨c, hc⟩, m⟩ ⟨⟨e, he⟩, n⟩ h
  have hce : c = e := by
    have hp : p c = p e := hc.trans he.symm
    by_cases hle : n.val ≤ m.val
    · apply covariance_no_class_collision hK hKs
        (covariance_nsmul hcov (m.val - n.val)) hp
      rw [sub_nsmul s hle]
      change c + m.val • s = e + n.val • s at h
      simp only [← sub_eq_add_neg]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using h.symm)
    · have hle' : m.val ≤ n.val := Nat.le_of_not_ge hle
      symm
      apply covariance_no_class_collision hK hKs
        (covariance_nsmul hcov (n.val - m.val)) hp.symm
      rw [sub_nsmul s hle']
      change c + m.val • s = e + n.val • s at h
      simp only [← sub_eq_add_neg]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using h)
  subst e
  have hmn : m = n := Fin.ext <|
    nsmul_injOn_Iio_addOrderOf (x := s) m.isLt n.isLt (add_left_cancel h)
  subst n
  rfl

/-- The class-size bound is stronger than only counting the number of classes:
each class uses at most one representative of each shift orbit. -/
theorem class_size_mul_order_le [NeZero d]
    {p : ZMod d → κ} {K : State d A → State d A}
    (hK : ClassUniform p K) (hKs : Function.Surjective K)
    {s t : ZMod d} (hcov : ∀ X, K (rot s X) = rowRot t (K X)) (j : κ) :
    Nat.card {c : ZMod d // p c = j} * addOrderOf s ≤ d := by
  classical
  let _ := Fintype.ofFinite {c : ZMod d // p c = j}
  simpa [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective _ (class_orbit_embedding hK hKs hcov j)

/-- For a finite complete state space, exactness supplies both surjectivities.
This is the numeric subgroup bound, with arbitrary deterministic factors. -/
theorem exact_periodic_first_class_bound [Finite A] [NeZero d] [Fintype κ]
    {p : ZMod d → κ} {A₀ K : State d A → State d A} (r : ℕ)
    (hK : ClassUniform p K)
    (hA : ∀ X, A₀ (rot (r : ZMod d) X) = rot (r : ZMod d) (A₀ X))
    (hexact : ∀ X, K (A₀ X) = swap X) :
    d / Nat.gcd d r ≤ Fintype.card κ := by
  have hAi : Function.Injective A₀ := by
    intro X Y h
    apply swapEquiv.injective
    change swap X = swap Y
    simpa only [hexact] using congrArg K h
  have hAs := Finite.surjective_of_injective hAi
  have hKs : Function.Surjective K := by
    intro Y
    refine ⟨A₀ (swap Y), ?_⟩
    rw [hexact, swap_swap]
  have hc := class_count_ge_order hK hKs (covariance_of_exact_factorization hAs hA hexact)
  rwa [ZMod.addOrderOf_coe r (NeZero.ne d)] at hc

/-- The corresponding bound on every individual class. -/
theorem exact_periodic_first_class_size_bound [Finite A] [NeZero d]
    {p : ZMod d → κ} {A₀ K : State d A → State d A} (r : ℕ)
    (hK : ClassUniform p K)
    (hA : ∀ X, A₀ (rot (r : ZMod d) X) = rot (r : ZMod d) (A₀ X))
    (hexact : ∀ X, K (A₀ X) = swap X) (j : κ) :
    Nat.card {c : ZMod d // p c = j} ≤ Nat.gcd d r := by
  have hAi : Function.Injective A₀ := by
    intro X Y h
    apply swapEquiv.injective
    change swap X = swap Y
    simpa only [hexact] using congrArg K h
  have hAs := Finite.surjective_of_injective hAi
  have hKs : Function.Surjective K := by
    intro Y
    refine ⟨A₀ (swap Y), ?_⟩
    rw [hexact, swap_swap]
  have hc := class_size_mul_order_le hK hKs
    (covariance_of_exact_factorization hAs hA hexact) j
  rw [ZMod.addOrderOf_coe r (NeZero.ne d)] at hc
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hg : 0 < Nat.gcd d r := Nat.gcd_pos_of_pos_left r hd
  have hh : 0 < d / Nat.gcd d r := Nat.div_pos (Nat.gcd_le_left r hd) hg
  have he := Nat.div_mul_cancel (Nat.gcd_dvd_left d r)
  nlinarith

end SharedDecoders

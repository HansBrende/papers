import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Uniform finite orders: each member of a nonempty set is first equally often.
The proof double-counts minima and uses a swap bijection, without factorials. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

abbrev BinOrder (J : Type*) [Fintype J] := J ≃ Fin (Fintype.card J)

def OwnFirst {J : Type*} [Fintype J] (r : J) (A : Finset J) (e : BinOrder J) : Prop :=
  ∀ a ∈ A, e r < e a

private def IsFirst {J : Type*} [Fintype J] (S : Finset J) (r : J)
    (e : BinOrder J) : Prop := ∀ a ∈ S, e r ≤ e a

private noncomputable def firstCount {J : Type*} [Fintype J] (S : Finset J) (r : J) : ℕ :=
  ∑ e : BinOrder J, if IsFirst S r e then 1 else 0

private theorem swap_mem {J : Type*} [Fintype J] (S : Finset J) {r s a : J}
    (hr : r ∈ S) (hs : s ∈ S) (ha : a ∈ S) : Equiv.swap r s a ∈ S := by
  by_cases har : a = r
  · subst a; simpa using hs
  by_cases has : a = s
  · subst a; simpa using hr
  simpa [Equiv.swap_apply_of_ne_of_ne har has] using ha

private theorem firstCount_eq {J : Type*} [Fintype J] (S : Finset J) {r s : J}
    (hr : r ∈ S) (hs : s ∈ S) : firstCount S r = firstCount S s := by
  let f : BinOrder J ≃ BinOrder J :=
    Equiv.equivCongr (Equiv.swap r s) (Equiv.refl _)
  apply Fintype.sum_equiv f
  intro e
  have he : IsFirst S r e ↔ IsFirst S s (f e) := by
    constructor
    · intro h a ha
      simpa [f] using h (Equiv.swap r s a) (swap_mem S hr hs ha)
    · intro h a ha
      simpa [f] using h (Equiv.swap r s a) (swap_mem S hr hs ha)
  simp only [he]

private theorem first_sum {J : Type*} [Fintype J] (S : Finset J) (hne : S.Nonempty)
    (e : BinOrder J) : (∑ r ∈ S, if IsFirst S r e then (1 : ℕ) else 0) = 1 := by
  obtain ⟨r,hr,hmin⟩ := S.exists_min_image e hne
  have hfilter : S.filter (fun a => IsFirst S a e) = {r} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨ha,hfirst⟩
      exact e.injective (le_antisymm (hfirst r hr) (hmin a ha))
    · intro ha
      subst a
      exact ⟨hr,hmin⟩
  simpa using congrArg Finset.card hfilter

/-- Exact integer count of orders that put a specified member first. -/
theorem ownFirst_mass {J : Type*} [Fintype J] (r : J) (A : Finset J)
    (hr : r ∉ A) :
    (A.card + 1) * (∑ e : BinOrder J, if OwnFirst r A e then 1 else 0) =
      Fintype.card (BinOrder J) := by
  let S := insert r A
  have hrs : r ∈ S := Finset.mem_insert_self _ _
  have he (e : BinOrder J) : IsFirst S r e ↔ OwnFirst r A e := by
    constructor
    · intro h a ha
      exact lt_of_le_of_ne (h a (Finset.mem_insert_of_mem ha))
        (fun heq => hr ((e.injective heq) ▸ ha))
    · intro h a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_rfl
      · exact le_of_lt (h a ha)
  have hc : S.card * firstCount S r = Fintype.card (BinOrder J) := by
    calc
      _ = ∑ a ∈ S, firstCount S a := by
        symm
        calc
          _ = ∑ _a ∈ S, firstCount S r :=
            Finset.sum_congr rfl (fun a ha => firstCount_eq S ha hrs)
          _ = _ := by simp
      _ = ∑ e : BinOrder J, ∑ a ∈ S, if IsFirst S a e then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ _e : BinOrder J, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro e _
        exact first_sum S ⟨r,hrs⟩ e
      _ = _ := by simp
  simpa [S, firstCount, he, hr] using hc

end BitWord

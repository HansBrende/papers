import BitWord.HelperOrderingMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat

/-! Acyclic demand selection by one shared public source-bin order. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

noncomputable def orderSelected {V J : Type*} {N : ℕ} [Fintype V]
    (F : Finset V) (bin : V → J) (ancestors : V → Finset J) (rank : J → Fin N) : Finset V :=
  F.filter (fun v => ∀ a ∈ ancestors v, rank (bin v) < rank a)

@[simp] theorem mem_orderSelected {V J : Type*} {N : ℕ} [Fintype V]
    (F : Finset V) (bin : V → J) (ancestors : V → Finset J) (rank : J → Fin N) (v : V) :
    v ∈ orderSelected F bin ancestors rank ↔ v ∈ F ∧ ∀ a ∈ ancestors v, rank (bin v) < rank a := by
  simp [orderSelected]

/-- Averaging acyclic selections loses only the number of named ancestor bins
plus one. The single order is shared by all demands. -/
theorem far_card_le_of_orderSelected_card_le {V J : Type*} [Fintype V] [Fintype J]
    (F : Finset V) (bin : V → J) (ancestors : V → Finset J) (D h : ℕ)
    (hfar : ∀ v ∈ F, bin v ∉ ancestors v)
    (hdegree : ∀ v ∈ F, (ancestors v).card ≤ D)
    (hselected : ∀ e : BinOrder J, (orderSelected F bin ancestors e).card ≤ h) :
    F.card ≤ (D+1)*h := by
  let K := Fintype.card (BinOrder J)
  have hK : 0 < K := Fintype.card_pos_iff.mpr ⟨Fintype.equivFin J⟩
  have hcount : (∑ v ∈ F, ∑ e : BinOrder J, if OwnFirst (bin v) (ancestors v) e then 1 else 0) =
      ∑ e : BinOrder J, (orderSelected F bin ancestors e).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have he : F.filter (fun v => OwnFirst (bin v) (ancestors v) e) =
        orderSelected F bin ancestors e := by
      ext v
      rw [Finset.mem_filter, mem_orderSelected]
      rfl
    simpa only [he, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun v => OwnFirst (bin v) (ancestors v) e) F)
  have htotal : F.card * K ≤ ((D+1)*h) * K := by
    calc
      _ = ∑ _v ∈ F, K := by simp
      _ ≤ ∑ v ∈ F, (D+1) * (∑ e : BinOrder J,
          if OwnFirst (bin v) (ancestors v) e then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        change Fintype.card (BinOrder J) ≤ _
        rw [← ownFirst_mass (bin v) (ancestors v) (hfar v hv)]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (hdegree v hv) 1)
      _ = (D+1) * ∑ e : BinOrder J, (orderSelected F bin ancestors e).card := by
        rw [← Finset.mul_sum, hcount]
      _ ≤ (D+1) * (K*h) := by
        apply Nat.mul_le_mul_left
        simpa [K] using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hselected e)
      _ = _ := by ac_rfl
  exact le_of_mul_le_mul_right htotal hK

end BitWord

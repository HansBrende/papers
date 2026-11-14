import LeanMachine.DisjointSumsWeighted
import Mathlib.Data.Fintype.EquivFin

/-! # Involution pairs as weighted parity blocks

Choose the smaller endpoint in a finite enumeration. Its weight is +1,
its mate's weight is -1, and fixed coordinates remain free. The resulting
kernel is exactly the subgroup of orbit-constant functions.
-/

namespace LeanMachine.InvolutionSums

open Finset
open scoped BigOperators
noncomputable section

variable {V A : Type*} [Fintype V]

/-- One oriented endpoint of every nontrivial orbit. -/
def representatives (m : V → V) : Finset V := by
  classical
  exact univ.filter (fun v => Fintype.equivFin V v < Fintype.equivFin V (m v))

private theorem mem_representatives (m : V → V) (v : V) :
    v ∈ representatives m ↔ Fintype.equivFin V v < Fintype.equivFin V (m v) := by
  classical
  simp [representatives]

private theorem chosen_ne (m : V → V) {v : V} (hv : v ∈ representatives m) :
    m v ≠ v := by
  intro he
  have hh := (mem_representatives m v).mp hv
  rw [he] at hh
  exact lt_irrefl _ hh

private theorem mate_not_chosen (m : V → V) (hm : Function.Involutive m)
    {v : V} (hv : v ∈ representatives m) : m v ∉ representatives m := by
  rw [mem_representatives, hm v]
  exact not_lt_of_gt ((mem_representatives m v).mp hv)

private theorem choose_or_mate (m : V → V) (hm : Function.Involutive m)
    {v : V} (hv : m v ≠ v) : v ∈ representatives m ∨ m v ∈ representatives m := by
  rw [mem_representatives, mem_representatives, hm v]
  exact lt_or_gt_of_ne (fun h => hv ((Fintype.equivFin V).injective h.symm))

/-- Nontrivial pairs, oriented by `representatives`, are disjoint sum blocks. -/
def blocks (m : V → V) (hm : Function.Involutive m) :
    DisjointSums V (representatives m) := by
  classical
  refine ⟨fun v => {v.val, m v.val}, fun v => ⟨v.val, by simp⟩, ?_⟩
  intro v w hne
  rw [disjoint_left]
  intro x hx hy
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hh | hh
  · exact hne (Subtype.ext hh)
  · exact mate_not_chosen m hm w.property (hh ▸ v.property)
  · exact mate_not_chosen m hm v.property (hh.symm ▸ w.property)
  · exact hne (Subtype.ext (hm.injective hh))

/-- Signs realize a pair difference as a weighted sum, also in characteristic two. -/
def weights [AddCommGroup A] (m : V → V) (v : V) : A ≃+ A := by
  classical
  exact if v ∈ representatives m then AddEquiv.refl A else AddEquiv.neg A

/-- The weighted block value is the oriented difference. -/
theorem encode_apply [AddCommGroup A] (m : V → V) (hm : Function.Involutive m)
    (x : V → A) (v : representatives m) :
    (blocks m hm).weightedEncode (weights m) x v = x v - x (m v) := by
  classical
  simp [DisjointSums.weightedEncode_apply, DisjointSums.encode_apply, blocks,
    weights, v.property, mate_not_chosen m hm v.property,
    Ne.symm (chosen_ne m v.property), sub_eq_add_neg]

/-- Independent shifts constant on every orbit, including the fixed points. -/
def orbitConstant [AddCommGroup A] (m : V → V) : AddSubgroup (V → A) where
  carrier := {x | ∀ v, x (m v) = x v}
  zero_mem' := by simp
  add_mem' hx hy := by intro v; simp [hx v, hy v]
  neg_mem' hx := by intro v; simp [hx v]

/-- The involution-shift subgroup is exactly a weighted disjoint-sum kernel. -/
theorem kernel_eq [AddCommGroup A] (m : V → V) (hm : Function.Involutive m) :
    ((blocks m hm).weightedEncode (weights m) (A := A)).ker = orbitConstant m := by
  classical
  ext x
  change (blocks m hm).weightedEncode (weights m) x = 0 ↔ ∀ v, x (m v) = x v
  constructor
  · intro hx v
    by_cases hv : m v = v
    · rw [hv]
    · rcases choose_or_mate m hm hv with hc | hc
      · have he := congrFun hx ⟨v, hc⟩
        exact (sub_eq_zero.mp (by simpa only [encode_apply, Pi.zero_apply] using he)).symm
      · have he := congrFun hx ⟨m v, hc⟩
        simpa only [encode_apply, hm v, Pi.zero_apply, sub_eq_zero] using he
  · intro hx
    ext v
    simp only [encode_apply, Pi.zero_apply, hx v, sub_self]

/-- Two vertices per nontrivial pair, plus the fixed vertices, exhaust the type. -/
theorem card_partition (m : V → V) (hm : Function.Involutive m) :
    2 * (representatives m).card + Nat.card {v // m v = v} = Fintype.card V := by
  classical
  have hd : Disjoint (representatives m) ((representatives m).image m) := by
    rw [disjoint_left]
    rintro v hv hmv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hmv
    exact mate_not_chosen m hm hu hv
  have hu : representatives m ∪ (representatives m).image m =
      univ.filter (fun v => m v ≠ v) := by
    ext v
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro (h | ⟨u, hu, rfl⟩)
      · exact chosen_ne m h
      · rw [hm u]
        exact Ne.symm (chosen_ne m hu)
    · intro h
      rcases choose_or_mate m hm h with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨m v, hc, hm v⟩
  have hc := congrArg Finset.card hu
  rw [card_union_of_disjoint hd, card_image_of_injective _ hm.injective] at hc
  have hp := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => m v = v)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [card_univ] at hp
  simp only [ne_eq] at hc
  omega

/-- Exact number of independent orbit-constant shifts over a finite alphabet. -/
theorem card_orbitConstant [AddCommGroup A] [Fintype A]
    (m : V → V) (hm : Function.Involutive m) :
    Nat.card (orbitConstant (A := A) m) =
      Fintype.card A ^ ((Fintype.card V + Nat.card {v // m v = v}) / 2) := by
  classical
  have h := (blocks m hm).card_weighted_kernel (weights (A := A) m)
  have hc := card_partition m hm
  calc
    Nat.card (orbitConstant (A := A) m) =
        Fintype.card A ^ (Fintype.card V - (representatives m).card) := by
      simpa only [kernel_eq, Fintype.card_coe] using h
    _ = _ := by congr 1; omega

/-- Selected oriented differences. -/
def differenceRecord [AddCommGroup A] (m : V → V)
    (T : Set (representatives m)) (x : V → A) : T → A :=
  fun k => x k.val.val - x (m k.val.val)

private theorem record_eq [AddCommGroup A] (m : V → V) (hm : Function.Involutive m)
    (T : Set (representatives m)) :
    (blocks m hm).weightedSyndromeRecord (weights (A := A) m) T =
      differenceRecord m T := by
  funext x k
  exact encode_apply m hm x k.val

/-- The full-invariance pairing quotient identity, with arbitrary recovery views.
No omitted-pair or geometric incidence hypothesis is silently added. -/
theorem card_eq_orbitConstant_mul_record [AddCommGroup A]
    (m : V → V) (hm : Function.Involutive m) (C : Set (V → A))
    (hstable : ∀ x ∈ C, ∀ z ∈ orbitConstant m, x + z ∈ C)
    (H : V → Set V) (T : Set (representatives m))
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i p, (↑((blocks m hm).support p) : Set V) ⊆ H i → p ∈ T)
    (hincident : ∀ p, (∀ i ∈ (blocks m hm).support p, i ∈ H i) → p ∈ T) :
    Nat.card C = Nat.card (orbitConstant (A := A) m) *
      Nat.card (differenceRecord m T '' C) := by
  have hs : ∀ x ∈ C, ∀ z : V → A,
      (blocks m hm).weightedEncode (weights m) z = 0 → x + z ∈ C := by
    intro x hx z hz
    apply hstable x hx z
    rw [← kernel_eq m hm]
    exact hz
  simpa only [kernel_eq, record_eq] using
    (blocks m hm).card_eq_weighted_kernel_mul_record_image_of_recovery
      (weights m) C hs H T hrecover hinternal hincident

/-- Finite pairing bound with the selected-record cardinality made explicit. -/
theorem card_le_pow [AddCommGroup A] [Fintype A]
    (m : V → V) (hm : Function.Involutive m) (C : Set (V → A))
    (hstable : ∀ x ∈ C, ∀ z ∈ orbitConstant m, x + z ∈ C)
    (H : V → Set V) (T : Set (representatives m))
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i p, (↑((blocks m hm).support p) : Set V) ⊆ H i → p ∈ T)
    (hincident : ∀ p, (∀ i ∈ (blocks m hm).support p, i ∈ H i) → p ∈ T) :
    Nat.card C ≤ Fintype.card A ^
      ((Fintype.card V + Nat.card {v // m v = v}) / 2 + Nat.card T) := by
  classical
  rw [card_eq_orbitConstant_mul_record m hm C hstable H T hrecover hinternal hincident,
    card_orbitConstant m hm, pow_add]
  apply Nat.mul_le_mul_left
  have h := Nat.card_le_card_of_injective
    (Subtype.val : (differenceRecord m T '' C) → (T → A)) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun] using h

end
end LeanMachine.InvolutionSums

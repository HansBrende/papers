import TransposeFollowup.RecodedXor
import TransposeFollowup.GraphNearCount

/-! A globally bijective stored bank with explicit inverse row dependencies.
Forward dependencies may be global and nonlinear. This is an information
interface; no cost for evaluating either direction is asserted. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

structure InverseRowBank (d b : ℕ) where
  recode : FiniteMatrix d b ≃ (MatrixBit d b → Bool)
  support : Fin d → Finset (Fin d)
  inverse_local : ∀ (y y' : MatrixBit d b → Bool) (i : Fin d),
    (∀ u ∈ support i, ∀ j t, y (u, (j, t)) = y' (u, (j, t))) →
      recode.symm y i = recode.symm y' i

namespace InverseRowBank

variable {d b : ℕ} (A : InverseRowBank d b)

theorem row_eq_of_recode_eq (x x' : FiniteMatrix d b) (i : Fin d)
    (h : ∀ u ∈ A.support i, ∀ j t,
      A.recode x (u, (j, t)) = A.recode x' (u, (j, t))) : x i = x' i := by
  simpa only [Equiv.symm_apply_apply] using A.inverse_local (A.recode x) (A.recode x') i h

theorem support_nonempty (hd : 0 < d) (hb : 0 < b) (i : Fin d) :
    (A.support i).Nonempty := by
  by_contra h
  have hempty : A.support i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have he := A.row_eq_of_recode_eq (fun _ _ _ => false) (fun _ _ _ => true) i
    (by simp [hempty])
  have hf := congrFun (congrFun he ⟨0, hd⟩) ⟨0, hb⟩
  exact Bool.false_ne_true hf

/-- Independent arbitrary row bijections are the width-one special case. -/
def ofRowwise (R : (i : Fin d) → Row d b ≃ Row d b) : InverseRowBank d b where
  recode := rowRecodingEquiv R
  support i := {i}
  inverse_local y y' i h := by
    change (R i).symm (fun j t => y (i, (j, t))) =
      (R i).symm (fun j t => y' (i, (j, t)))
    congr 1
    funext j t
    exact h i (Finset.mem_singleton_self i) j t

@[simp] theorem ofRowwise_support (R : (i : Fin d) → Row d b ≃ Row d b) (i : Fin d) :
    (ofRowwise R).support i = {i} := rfl

end InverseRowBank

/-- Nearness pulled back through declared inverse dependencies. -/
def InverseSupportNear {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell : ℕ) (i j : Fin d) : Prop :=
  ∃ u ∈ S i, ∃ v ∈ S j, GraphNear G ell u v

theorem graphNear_symm {V : Type*} {G : SimpleGraph V} {ell : ℕ} {i j : V}
    (h : GraphNear G ell i j) : GraphNear G ell j i := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

theorem inverseSupportNear_symm {d : ℕ} {S : Fin d → Finset (Fin d)}
    {G : SimpleGraph (Fin d)} {ell : ℕ} {i j : Fin d}
    (h : InverseSupportNear S G ell i j) : InverseSupportNear S G ell j i := by
  obtain ⟨u, hu, v, hv, hnear⟩ := h
  exact ⟨v, hv, u, hu, graphNear_symm hnear⟩

def inverseSupportGraph {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell : ℕ) : SimpleGraph (Fin d) where
  Adj i j := i ≠ j ∧ InverseSupportNear S G ell i j
  symm := ⟨fun _ _ h => ⟨h.1.symm, inverseSupportNear_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def inverseSupportVertices {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell : ℕ) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (InverseSupportNear S G ell i)

theorem inverseSupportVertices_eq_union {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell : ℕ) (i : Fin d) :
    inverseSupportVertices S G ell i =
      (S i).biUnion (fun u => (nearVertices G ell u).biUnion
        (fun v => Finset.univ.filter (fun j => v ∈ S j))) := by
  ext j
  simp only [inverseSupportVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, mem_nearVertices, InverseSupportNear]
  constructor
  · rintro ⟨u, hu, v, hv, hnear⟩
    exact ⟨u, hu, v, hnear, hv⟩
  · rintro ⟨u, hu, v, hnear, hv⟩
    exact ⟨u, hu, v, hv, hnear⟩

theorem inverseSupportVertices_card_le {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell c e nu : ℕ)
    (hwidth : ∀ i, (S i).card ≤ c)
    (hreuse : ∀ v, (Finset.univ.filter (fun j => v ∈ S j)).card ≤ e)
    (hballs : ∀ u, (nearVertices G ell u).card ≤ nu) (i : Fin d) :
    (inverseSupportVertices S G ell i).card ≤ c * nu * e := by
  rw [inverseSupportVertices_eq_union]
  calc
    _ ≤ ∑ u ∈ S i, ((nearVertices G ell u).biUnion
        (fun v => Finset.univ.filter (fun j => v ∈ S j))).card := Finset.card_biUnion_le
    _ ≤ ∑ u ∈ S i, (nearVertices G ell u).card * e := by
      apply Finset.sum_le_sum
      intro u _
      calc
        _ ≤ ∑ v ∈ nearVertices G ell u, (Finset.univ.filter (fun j => v ∈ S j)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ nearVertices G ell u, e := Finset.sum_le_sum (fun v _ => hreuse v)
        _ = _ := by simp
    _ ≤ ∑ _u ∈ S i, nu * e :=
      Finset.sum_le_sum (fun u _ => Nat.mul_le_mul_right e (hballs u))
    _ = (S i).card * (nu * e) := by simp
    _ ≤ c * (nu * e) := Nat.mul_le_mul_right _ (hwidth i)
    _ = _ := by ring

theorem mem_inverseSupportVertices_self {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) {ell : ℕ} (hell : 0 < ell) (i : Fin d)
    (hi : (S i).Nonempty) : i ∈ inverseSupportVertices S G ell i := by
  obtain ⟨u, hu⟩ := hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, u, hu, .nil, hell⟩

theorem inverseSupportGraph_degree_add_one_le {d : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell c e nu : ℕ)
    [DecidableRel (inverseSupportGraph S G ell).Adj]
    (hell : 0 < ell) (hne : ∀ i, (S i).Nonempty)
    (hwidth : ∀ i, (S i).card ≤ c)
    (hreuse : ∀ v, (Finset.univ.filter (fun j => v ∈ S j)).card ≤ e)
    (hballs : ∀ u, (nearVertices G ell u).card ≤ nu) (i : Fin d) :
    (inverseSupportGraph S G ell).degree i + 1 ≤ c * nu * e := by
  have he : (inverseSupportGraph S G ell).neighborFinset i =
      (inverseSupportVertices S G ell i).erase i := by
    ext j
    rw [(inverseSupportGraph S G ell).mem_neighborFinset]
    change (i ≠ j ∧ InverseSupportNear S G ell i j) ↔ _
    simp only [
      Finset.mem_erase, inverseSupportVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he,
    Finset.card_erase_add_one (mem_inverseSupportVertices_self S G hell i (hne i))]
  exact inverseSupportVertices_card_le S G ell c e nu hwidth hreuse hballs i

/-- Raw coordinates covered by a diagonal or an inverse-support conflict. -/
noncomputable def inverseNearBits {d b : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell : ℕ) : Finset (MatrixBit d b) :=
  Finset.univ.filter (fun v => v.1 = v.2.1 ∨ InverseSupportNear S G ell v.1 v.2.1)

theorem inverseNearBits_card_le {d b : ℕ} (S : Fin d → Finset (Fin d))
    (G : SimpleGraph (Fin d)) (ell c e nu : ℕ)
    (hell : 0 < ell) (hne : ∀ i, (S i).Nonempty)
    (hwidth : ∀ i, (S i).card ≤ c)
    (hreuse : ∀ v, (Finset.univ.filter (fun j => v ∈ S j)).card ≤ e)
    (hballs : ∀ u, (nearVertices G ell u).card ≤ nu) :
    (inverseNearBits (b := b) S G ell).card ≤ d * (c * nu * e) * b := by
  have he : (inverseNearBits (b := b) S G ell).card =
      ∑ i : Fin d, (inverseSupportVertices S G ell i).card * b := by
    let E : inverseNearBits (b := b) S G ell ≃
        Σ i : Fin d, (inverseSupportVertices S G ell i) × Fin b :=
      { toFun := fun v => ⟨v.val.1, ⟨⟨v.val.2.1, by
          rcases (Finset.mem_filter.mp v.property).2 with hv | hv
          · rw [← hv]
            exact mem_inverseSupportVertices_self S G hell v.val.1 (hne _)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩, v.val.2.2⟩⟩
        invFun := fun v => ⟨(v.1, (v.2.1.val, v.2.2)),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Or.inr (Finset.mem_filter.mp v.2.1.property).2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin] using Fintype.card_congr E
  rw [he]
  calc
    _ ≤ ∑ _i : Fin d, (c * nu * e) * b := Finset.sum_le_sum
      (fun i _ => Nat.mul_le_mul_right b
        (inverseSupportVertices_card_le S G ell c e nu hwidth hreuse hballs i))
    _ = _ := by simp [Nat.mul_assoc]

end TransposeFollowup

import SharedDecoders.CapacitySetConsistency
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Exact cyclic capacity of arbitrary correctness sets

All views and demanded rows below are the actual maps in `Model`. Stabilizers,
covariance cosets and the attaining set are constructed, rather than supplied as
certificates. The alphabet need not carry algebraic structure.
-/

namespace SharedDecoders.SetCapacity

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {A : Type*}

/-- Column rotation, used only as a local action instance in this development. -/
@[instance_reducible] def rotationAction : AddAction (ZMod d) (State d A) where
  vadd := rot
  zero_vadd := rot_zero
  add_vadd s t X := (rot_rot s t X).symm

attribute [local instance] rotationAction

/-- The actual column stabilizer. -/
def H (X : State d A) : AddSubgroup (ZMod d) := AddAction.stabilizer (ZMod d) X

@[simp] theorem mem_H (X : State d A) (s : ZMod d) : s ∈ H X ↔ rot s X = X := Iff.rfl

/-- Row covariance, with the same shift on the row index and row word. -/
def K (X : State d A) : AddSubgroup (ZMod d) where
  carrier := {s | ∀ c j, X (c + s) j = X c (j + s)}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht c j
    calc
      X (c + (s + t)) j = X ((c + s) + t) j := by rw [add_assoc]
      _ = X (c + s) (j + t) := ht _ _
      _ = X c (j + (s + t)) := by rw [hs]; congr 1; abel
  neg_mem' := by
    intro s hs c j
    have hh := hs (c - s) (j - s)
    simpa [sub_eq_add_neg, add_assoc] using hh.symm

@[simp] theorem mem_K (X : State d A) (s : ZMod d) :
    s ∈ K X ↔ ∀ c j, X (c + s) j = X c (j + s) := Iff.rfl

def Eligible (X : State d A) : Prop := H X ≤ K X

theorem H_rot (t : ZMod d) (X : State d A) : H (rot t X) = H X := by
  ext s
  simp only [mem_H]
  constructor <;> intro h
  · have h' := congrArg (rot (-t)) h
    simpa [rot_rot, add_assoc, add_comm, add_left_comm] using h'
  · calc
      rot s (rot t X) = rot t (rot s X) := by rw [rot_rot, rot_rot, add_comm s t]
      _ = rot t X := congrArg (rot t) h

theorem K_rot (t : ZMod d) (X : State d A) : K (rot t X) = K X := by
  ext s
  simp only [mem_K, rot_apply]
  constructor <;> intro h c j
  · have he : (j - t + s) + t = j + s := by abel
    simpa only [sub_add_cancel, he] using h c (j - t)
  · simpa [add_assoc, add_comm t s] using h c (j + t)

@[simp] theorem eligible_rot (t : ZMod d) (X : State d A) :
    Eligible (rot t X) ↔ Eligible X := by simp [Eligible, H_rot, K_rot]

theorem rot_eq_iff_sub_mem_H (X : State d A) (s t : ZMod d) :
    rot s X = rot t X ↔ s - t ∈ H X := by
  constructor
  · intro h
    have hh := congrArg (rot (-t)) h
    simpa [rot_rot, sub_eq_add_neg, add_comm] using hh
  · intro h
    have hh := congrArg (rot t) (mem_H X (s - t) |>.mp h)
    simpa [rot_rot, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh

/-- Actual pairwise consistency, including every possible colliding receiver. -/
def Compatible (X Y : State d A) : Prop :=
  ∀ c e, rot c X = rot e Y → X c = Y e

theorem eligible_iff_self_compatible (X : State d A) :
    Eligible X ↔ Compatible X X := by
  constructor
  · intro h c e he
    have hs : c - e ∈ K X := h ((rot_eq_iff_sub_mem_H X c e).mp he)
    have hh : c - e ∈ H X := (rot_eq_iff_sub_mem_H X c e).mp he
    funext j
    calc
      X c j = X (e + (c - e)) j := by congr 2; abel
      _ = X e (j + (c - e)) := hs e j
      _ = X e j := congrFun (congrFun ((mem_H X _).mp hh) e) j
  · intro h s hs c j
    have hs := (mem_H X s).mp hs
    have he : rot (c + s) X = rot c X := by
      rw [← rot_rot, hs]
    have hr := congrFun (h (c + s) c he) j
    exact hr.trans (congrFun (congrFun hs c) j).symm

theorem compatible_symm {X Y : State d A} (h : Compatible X Y) : Compatible Y X :=
  fun c e he => (h e c he.symm).symm

/-- In an eligible orbit, two words are compatible exactly in one covariance coset. -/
theorem compatible_rot_iff (X : State d A) (hX : Eligible X) (t : ZMod d) :
    Compatible X (rot t X) ↔ t ∈ K X := by
  constructor
  · intro h c j
    have hv : rot (c + t) X = rot c (rot t X) := (rot_rot c t X).symm
    exact congrFun (h (c + t) c hv) j
  · intro ht c e he
    have hs : c - (e + t) ∈ H X :=
      (rot_eq_iff_sub_mem_H X c (e + t)).mp (by simpa only [rot_rot] using he)
    have hk := (K X).add_mem (hX hs) ht
    have hc : c - (e + t) + t = c - e := by abel
    rw [hc] at hk
    funext j
    calc
      X c j = X e (j + (c - e)) := by
        simpa [add_sub_cancel_left] using hk e j
      _ = X e (j + t) := by
        have hh := congrFun (congrFun ((mem_H X _).mp hs) e) (j + t)
        have he : (j + t) + (c - (e + t)) = j + (c - e) := by abel
        simpa only [rot_apply, he] using hh
      _ = rot t X e j := rfl

/-- Validity means one total, deterministic decoder for the complete correctness set. -/
def IsCode (C : Set (State d A)) : Prop :=
  ∃ f : State d A → (ZMod d → A), ∀ X ∈ C, ∀ c, f (rot c X) = X c

theorem IsCode.eligible {C : Set (State d A)} (hC : IsCode C)
    {X : State d A} (hX : X ∈ C) : Eligible X := by
  apply (eligible_iff_self_compatible X).mpr
  obtain ⟨f, hf⟩ := hC
  intro c e he
  rw [← hf X hX c, ← hf X hX e, he]

theorem IsCode.compatible {C : Set (State d A)} (hC : IsCode C)
    {X Y : State d A} (hX : X ∈ C) (hY : Y ∈ C) : Compatible X Y := by
  obtain ⟨f, hf⟩ := hC
  intro c e he
  rw [← hf X hX c, ← hf Y hY e, he]

/-- The full covariance coset based at a matrix. -/
def Cluster (X : State d A) : Set (State d A) := AddAction.orbit (K X) X

@[simp] theorem mem_cluster (X Y : State d A) :
    Y ∈ Cluster X ↔ ∃ s ∈ K X, rot s X = Y := by
  change (∃ s : K X, rot s.val X = Y) ↔ _
  simp

theorem cluster_consistent {X : State d A} (hX : Eligible X)
    {Y Z : State d A} (hY : Y ∈ Cluster X) (hZ : Z ∈ Cluster X) : Compatible Y Z := by
  obtain ⟨a, ha, rfl⟩ := (mem_cluster X Y).mp hY
  obtain ⟨b, hb, rfl⟩ := (mem_cluster X Z).mp hZ
  have h := (compatible_rot_iff (rot a X) ((eligible_rot a X).mpr hX) (b - a)).mpr
    (by rw [K_rot]; exact (K X).sub_mem hb ha)
  have he : rot (b - a) (rot a X) = rot b X := by
    rw [rot_rot, sub_add_cancel]
  rwa [he] at h

theorem cluster_isCode [Nonempty A] {X : State d A} (hX : Eligible X) :
    IsCode (Cluster X) :=
  (exists_cyclic_set_decoder_iff _).mpr (fun _ hY _ hZ => cluster_consistent hX hY hZ)

/-- Column-rotation orbits, with an actual representative chosen from each orbit. -/
abbrev Orbit (d : ℕ) (A : Type*) := AddAction.orbitRel.Quotient (ZMod d) (State d A)

def orbitOf (X : State d A) : Orbit d A := Quotient.mk'' X

@[simp] theorem orbitOf_rot (s : ZMod d) (X : State d A) :
    orbitOf (rot s X) = orbitOf X :=
  Quotient.sound' (AddAction.mem_orbit X s)

theorem orbitOf_eq_iff (X Y : State d A) :
    orbitOf X = orbitOf Y ↔ ∃ s, rot s Y = X := Quotient.eq''

@[simp] theorem orbitOf_out (o : Orbit d A) : orbitOf o.out = o := Quotient.out_eq' o

theorem orbit_invariants {X Y : State d A} (h : orbitOf X = orbitOf Y) :
    H X = H Y ∧ K X = K Y := by
  obtain ⟨s, rfl⟩ := (orbitOf_eq_iff X Y).mp h
  exact ⟨H_rot s Y, K_rot s Y⟩

theorem eligible_of_orbit {X Y : State d A} (h : orbitOf X = orbitOf Y) :
    Eligible X ↔ Eligible Y := by
  obtain ⟨hH, hK⟩ := orbit_invariants h
  simp only [Eligible, hH, hK]

/-- The selected entire covariance coset in an eligible rotation orbit. -/
def Chosen : Set (State d A) :=
  {X | Eligible (orbitOf X).out ∧ X ∈ Cluster (orbitOf X).out}

theorem chosen_isCode [Nonempty A] : IsCode (Chosen (d := d) (A := A)) := by
  apply (exists_cyclic_set_decoder_iff _).mpr
  intro X hX Y hY c e he
  have ho : orbitOf X = orbitOf Y := by
    calc
      orbitOf X = orbitOf (rot c X) := (orbitOf_rot c X).symm
      _ = orbitOf (rot e Y) := congrArg orbitOf he
      _ = orbitOf Y := orbitOf_rot e Y
  have hy : Y ∈ Cluster (orbitOf X).out := by rw [ho]; exact hY.2
  exact cluster_consistent hX.1 hX.2 hy c e he

section Finite
variable [NeZero d] [Fintype A]

noncomputable instance orbitFintype : Fintype (Orbit d A) := Fintype.ofFinite _

/-- The stabilizer of the restricted covariance action is the actual column
stabilizer, using eligibility to embed it into the covariance subgroup. -/
def clusterStabilizerEquiv (X : State d A) (hX : Eligible X) :
    AddAction.stabilizer (K X) X ≃ H X where
  toFun s := ⟨s.val.val, s.property⟩
  invFun s := ⟨⟨s.val, hX s.property⟩, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cluster_card_mul_H (X : State d A) (hX : Eligible X) :
    Nat.card (Cluster X) * Nat.card (H X) = Nat.card (K X) := by
  have hh := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup (K X) X
  rw [Fintype.card_congr (clusterStabilizerEquiv X hX)] at hh
  simpa only [Nat.card_eq_fintype_card, Cluster] using hh

theorem cluster_card (X : State d A) (hX : Eligible X) :
    Nat.card (Cluster X) = Nat.card (K X) / Nat.card (H X) := by
  rw [← cluster_card_mul_H X hX, Nat.mul_div_cancel _ (Nat.card_pos (α := H X))]

/-- The orbit contribution is a proved count of the entire chosen coset. -/
noncomputable def orbitCapacity (o : Orbit d A) : ℕ :=
  if Eligible o.out then Nat.card (Cluster o.out) else 0

noncomputable def capacity : ℕ := ∑ o : Orbit d A, orbitCapacity o

noncomputable def chosenEquiv : Chosen (d := d) (A := A) ≃
    Σ o : {o : Orbit d A // Eligible o.out}, Cluster o.val.out where
  toFun X := ⟨⟨orbitOf X.val, X.property.1⟩, ⟨X.val, X.property.2⟩⟩
  invFun p := ⟨p.2.val, by
    have ho : orbitOf p.2.val = p.1.val := by
      obtain ⟨s, hs, he⟩ := (mem_cluster _ _).mp p.2.property
      rw [← he, orbitOf_rot, orbitOf_out]
    change Eligible (orbitOf p.2.val).out ∧ p.2.val ∈ Cluster (orbitOf p.2.val).out
    rw [ho]
    exact ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv p := by
    have ho : orbitOf p.2.val = p.1.val := by
      obtain ⟨s, hs, he⟩ := (mem_cluster _ _).mp p.2.property
      rw [← he, orbitOf_rot, orbitOf_out]
    apply Sigma.ext (Subtype.ext ho)
    apply (Subtype.heq_iff_coe_eq (fun Y => by
      change Y ∈ Cluster (orbitOf p.2.val).out ↔ Y ∈ Cluster p.1.val.out
      rw [ho])).mpr
    rfl

theorem chosen_card : Nat.card (Chosen (d := d) (A := A)) = capacity (d := d) (A := A) := by
  classical
  rw [Nat.card_congr chosenEquiv, Nat.card_sigma]
  unfold capacity orbitCapacity
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype
    (Finset.univ.filter (fun o : Orbit d A => Eligible o.out))
    (by intro o; simp) (fun o => Nat.card (Cluster o.out))).symm

/-- Every valid set meets each rotation orbit in at most one covariance coset. -/
theorem IsCode.fiber_card_le {C : Set (State d A)} (hC : IsCode C) (o : Orbit d A) :
    Nat.card {X : C // orbitOf X.val = o} ≤ orbitCapacity o := by
  classical
  by_cases hn : Nonempty {X : C // orbitOf X.val = o}
  · obtain ⟨x⟩ := hn
    have hx := hC.eligible x.val.property
    have hxo : orbitOf x.val.val = orbitOf o.out := x.property.trans (orbitOf_out o).symm
    have ho := (eligible_of_orbit hxo).mp hx
    let f : {X : C // orbitOf X.val = o} → Cluster x.val.val := fun y =>
      ⟨y.val.val, by
        have hxy : orbitOf y.val.val = orbitOf x.val.val := y.property.trans x.property.symm
        obtain ⟨s, hs⟩ := (orbitOf_eq_iff _ _).mp hxy
        refine (mem_cluster _ _).mpr ⟨s, ?_, hs⟩
        exact (compatible_rot_iff _ hx s).mp (by
          rw [hs]
          exact hC.compatible x.val.property y.val.property)⟩
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Cluster x.val.val => z.val) h
    have hle := Nat.card_le_card_of_injective f hf
    have hinv := orbit_invariants hxo
    calc
      Nat.card {X : C // orbitOf X.val = o} ≤ Nat.card (Cluster x.val.val) := hle
      _ = Nat.card (Cluster o.out) := by
        rw [cluster_card _ hx, cluster_card _ ho, hinv.1, hinv.2]
      _ = orbitCapacity o := by simp [orbitCapacity, ho]
  · have : IsEmpty {X : C // orbitOf X.val = o} := not_nonempty_iff.mp hn
    simp

theorem IsCode.card_le {C : Set (State d A)} (hC : IsCode C) :
    Nat.card C ≤ capacity (d := d) (A := A) := by
  have hc := Nat.card_congr (Equiv.sigmaFiberEquiv (fun X : C => orbitOf X.val))
  rw [Nat.card_sigma] at hc
  calc
    Nat.card C = ∑ o : Orbit d A, Nat.card {X : C // orbitOf X.val = o} := hc.symm
    _ ≤ capacity (d := d) (A := A) := Finset.sum_le_sum (fun o _ => hC.fiber_card_le o)

/-- The actual maximum, with one total decoder attaining all eligible orbits. -/
theorem exact_capacity [Nonempty A] :
    (∃ C : Set (State d A), IsCode C ∧ Nat.card C = capacity (d := d) (A := A)) ∧
    (∀ C : Set (State d A), IsCode C → Nat.card C ≤ capacity (d := d) (A := A)) :=
  ⟨⟨Chosen, chosen_isCode, chosen_card⟩, fun _ h => h.card_le⟩

theorem capacity_orbit_formula :
    capacity (d := d) (A := A) =
      ∑ o : Orbit d A, if Eligible o.out then Nat.card (K o.out) / Nat.card (H o.out) else 0 := by
  unfold capacity orbitCapacity
  apply Finset.sum_congr rfl
  intro o _
  split_ifs with ho
  · exact cluster_card _ ho
  · rfl

/-- The quotient fibre is the actual column-rotation orbit of its representative. -/
def orbitFiberEquiv (o : Orbit d A) :
    {X : State d A // orbitOf X = o} ≃ AddAction.orbit (ZMod d) o.out where
  toFun X := ⟨X.val, (orbitOf_eq_iff _ _).mp (X.property.trans (orbitOf_out o).symm)⟩
  invFun X := ⟨X.val, ((orbitOf_eq_iff _ _).mpr X.property).trans (orbitOf_out o)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orbit_card_mul_H (o : Orbit d A) :
    Nat.card {X : State d A // orbitOf X = o} * Nat.card (H o.out) = d := by
  rw [Nat.card_congr (orbitFiberEquiv o)]
  have hh := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup (ZMod d) o.out
  simpa only [Nat.card_eq_fintype_card, H, ZMod.card] using hh

noncomputable def weight (X : State d A) : ℕ := if Eligible X then Nat.card (K X) else 0

omit [NeZero d] [Fintype A] in
theorem weight_of_orbit {X Y : State d A} (h : orbitOf X = orbitOf Y) :
    weight X = weight Y := by
  have hi := orbit_invariants h
  simp only [weight, eligible_of_orbit h, hi.2]

theorem weighted_sum_by_orbits :
    (∑ X : State d A, weight X) =
      ∑ o : Orbit d A, Nat.card {X : State d A // orbitOf X = o} * weight o.out := by
  classical
  rw [← (Equiv.sigmaFiberEquiv (orbitOf (d := d) (A := A))).sum_comp weight,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  calc
    (∑ x : {X : State d A // orbitOf X = o},
        weight ((Equiv.sigmaFiberEquiv orbitOf) ⟨o, x⟩)) =
      ∑ _x : {X : State d A // orbitOf X = o}, weight o.out := by
        apply Finset.sum_congr rfl
        intro x _
        exact weight_of_orbit (x.property.trans (orbitOf_out o).symm)
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- Exact weighted formula, with no rounding loss or orbit-count hypothesis. -/
theorem capacity_weighted_formula :
    d * capacity (d := d) (A := A) = ∑ X : State d A, weight X := by
  rw [weighted_sum_by_orbits]
  unfold capacity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : Eligible o.out
  · simp only [orbitCapacity, weight, ite_eq_left ho]
    have h1 := orbit_card_mul_H (A := A) o
    have h2 := cluster_card_mul_H o.out ho
    calc
      d * Nat.card (Cluster o.out) =
          (Nat.card {X : State d A // orbitOf X = o} * Nat.card (H o.out)) *
            Nat.card (Cluster o.out) := by rw [h1]
      _ = Nat.card {X : State d A // orbitOf X = o} * Nat.card (K o.out) := by
        rw [← h2]
        ring
  · simp [orbitCapacity, weight, ho]

theorem capacity_average_formula :
    capacity (d := d) (A := A) = (∑ X : State d A, weight X) / d := by
  rw [← capacity_weighted_formula, Nat.mul_div_cancel_left _ (NeZero.pos d)]

theorem capacity_le_card_state : capacity (d := d) (A := A) ≤ Nat.card (State d A) := by
  rw [← chosen_card]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem capacity_eq_card_of_univCode (h : IsCode (Set.univ : Set (State d A))) :
    capacity (d := d) (A := A) = Nat.card (State d A) := by
  apply Nat.le_antisymm capacity_le_card_state
  simpa using h.card_le

theorem capacity_one_dimension : capacity (d := 1) (A := A) = Fintype.card A := by
  have hh : IsCode (Set.univ : Set (State 1 A)) := by
    refine ⟨fun X => X 0, ?_⟩
    intro X _ c
    have hc : c = 0 := Subsingleton.elim _ _
    simp [hc]
  rw [capacity_eq_card_of_univCode hh]
  simp [State, Nat.card_eq_fintype_card]

theorem capacity_one_symbol [Subsingleton A] [Nonempty A] :
    capacity (d := d) (A := A) = 1 := by
  have hh : IsCode (Set.univ : Set (State d A)) := by
    refine ⟨fun _ => Classical.choice inferInstance, ?_⟩
    intro _ _ _
    exact Subsingleton.elim _ _
  rw [capacity_eq_card_of_univCode hh, Nat.card_unique]

end Finite
end SharedDecoders.SetCapacity

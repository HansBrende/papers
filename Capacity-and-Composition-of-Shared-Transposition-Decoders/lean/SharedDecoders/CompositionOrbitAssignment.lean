import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Exact assignment of whole source orbits to cyclic target orbits

Orbit maps are constructed from the actual actions and stabilizers. Uniform
fibre sizes are derived by transport and finite counting.
-/

namespace SharedDecoders.OrbitAssignment

open MulAction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {G C X Y : Type*} [Group G] [Group C] [MulAction G X] [MulAction C Y]

def Intertwines (θ : G →* C) (f : X → Y) : Prop := ∀ g x, f (g • x) = θ g • f x

abbrev Orbits (G X : Type*) [Group G] [MulAction G X] := orbitRel.Quotient G X

def orbitOf (G : Type*) [Group G] {X : Type*} [MulAction G X] (x : X) : Orbits G X :=
  Quotient.mk'' x

@[simp] theorem orbitOf_smul (g : G) (x : X) : orbitOf G (g • x) = orbitOf G x :=
  Quotient.sound' (mem_orbit x g)

@[simp] theorem orbitOf_out (o : Orbits G X) : orbitOf G o.out = o := Quotient.out_eq' o

theorem orbitOf_eq_iff (x z : X) : orbitOf G x = orbitOf G z ↔ x ∈ orbit G z := Quotient.eq''

theorem mem_out_orbit (x : X) : x ∈ orbit G (orbitOf G x).out :=
  (orbitOf_eq_iff _ _).mp (orbitOf_out (orbitOf G x)).symm

theorem orbitOf_eq_of_mem {o : Orbits G X} {x : X} (hx : x ∈ orbit G o.out) : orbitOf G x = o :=
  ((orbitOf_eq_iff _ _).mpr hx).trans (orbitOf_out o)

theorem orbit_card_eq {x z : X} (h : orbitOf G x = orbitOf G z) :
    Nat.card (orbit G x) = Nat.card (orbit G z) :=
  congrArg (fun s : Set X => Nat.card s) (orbit_eq_iff.mpr ((orbitOf_eq_iff _ _).mp h))

/-- Stabilizer inclusion is forced by actual equivariance. -/
theorem stabilizer_map_le (θ : G →* C) {f : X → Y} (hf : Intertwines θ f) (x : X) :
    (stabilizer G x).map θ ≤ stabilizer C (f x) := by
  rintro c ⟨g, hg, rfl⟩
  change θ g • f x = f x
  rw [← hf, hg]

theorem orbit_value_wellDefined (θ : G →* C) (x : X) (z : Y)
    (hs : (stabilizer G x).map θ ≤ stabilizer C z) {g h : G}
    (he : g • x = h • x) : θ g • z = θ h • z := by
  have hm : h⁻¹ * g ∈ stabilizer G x := by
    change (h⁻¹ * g) • x = x
    rw [mul_smul, he, inv_smul_smul]
  have hz : θ (h⁻¹ * g) • z = z := hs ⟨h⁻¹ * g, hm, rfl⟩
  have hh := congrArg (fun y : Y => θ h • y) hz
  simpa only [map_mul, map_inv, ← mul_smul, mul_inv_cancel_left] using hh

/-- The actual orbit map `g*x ↦ θ(g)*z`, with well-definedness proved above. -/
noncomputable def orbitMap (θ : G →* C) (x : X) (z : Y)
    (_hs : (stabilizer G x).map θ ≤ stabilizer C z) (u : orbit G x) : Y :=
  θ (Classical.choose u.property) • z

theorem orbitMap_translate (θ : G →* C) (x : X) (z : Y)
    (hs : (stabilizer G x).map θ ≤ stabilizer C z) (g : G) :
    orbitMap θ x z hs ⟨g • x, mem_orbit x g⟩ = θ g • z :=
  orbit_value_wellDefined θ x z hs (Classical.choose_spec (mem_orbit x g))

theorem orbitMap_intertwines (θ : G →* C) (x : X) (z : Y)
    (hs : (stabilizer G x).map θ ≤ stabilizer C z) :
    Intertwines θ (orbitMap θ x z hs) := by
  intro g u
  obtain ⟨h, hh⟩ := u.property
  have hu : u = ⟨h • x, mem_orbit x h⟩ := Subtype.ext hh.symm
  subst u
  have he : g • (⟨h • x, mem_orbit x h⟩ : orbit G x) =
      ⟨(g * h) • x, mem_orbit x (g * h)⟩ := Subtype.ext (mul_smul g h x).symm
  rw [he, orbitMap_translate, orbitMap_translate, map_mul, mul_smul]

theorem orbitMap_mem (θ : G →* C) (x : X) (z : Y)
    (hs : (stabilizer G x).map θ ≤ stabilizer C z) (u : orbit G x) :
    orbitMap θ x z hs u ∈ orbit C z := ⟨θ (Classical.choose u.property), rfl⟩

/-- Exact local existence criterion, with an actual orbit map in the reverse direction. -/
theorem orbit_map_exists_iff (θ : G →* C) (x : X) (z : Y) :
    (∃ f : orbit G x → Y, Intertwines θ f ∧ f ⟨x, mem_orbit_self x⟩ = z) ↔
      (stabilizer G x).map θ ≤ stabilizer C z := by
  constructor
  · rintro ⟨f, hf, hz⟩ c ⟨g, hg, rfl⟩
    change θ g • z = z
    rw [← hz, ← hf]
    congr 1
    exact Subtype.ext hg
  · intro hs
    refine ⟨orbitMap θ x z hs, orbitMap_intertwines θ x z hs, ?_⟩
    have h := orbitMap_translate θ x z hs 1
    simpa only [one_smul, map_one] using h

/-- Every group element transports the actual fibres by a bijection. -/
def fiberTransport (θ : G →* C) (f : X → Y) (hf : Intertwines θ f) (g : G) (y : Y) :
    {x : X // f x = y} ≃ {x : X // f x = θ g • y} where
  toFun x := ⟨g • x.val, by rw [hf, x.property]⟩
  invFun x := ⟨g⁻¹ • x.val, by rw [hf, map_inv, x.property, inv_smul_smul]⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

/-- A transitive target has exactly uniform fibres under any actual intertwiner
through a surjective phase homomorphism. -/
theorem transitive_fiber_card [Fintype X] [Fintype Y] [IsPretransitive C Y]
    (θ : G →* C) (hθ : Function.Surjective θ) (f : X → Y) (hf : Intertwines θ f) (y : Y) :
    Nat.card {x : X // f x = y} = Nat.card X / Nat.card Y := by
  classical
  have hcard (z : Y) : Nat.card {x : X // f x = z} = Nat.card {x : X // f x = y} := by
    obtain ⟨c, rfl⟩ := exists_smul_eq C y z
    obtain ⟨g, rfl⟩ := hθ c
    exact (Nat.card_congr (fiberTransport θ f hf g y)).symm
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at he
  simp_rw [hcard] at he
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at he
  have : Nonempty Y := ⟨y⟩
  rw [← he, Nat.mul_div_cancel_left _ (Nat.card_pos (α := Y))]

/-- Restriction of an actual equivariant map to one actual source and target orbit. -/
def restrictOrbit (θ : G →* C) (f : X → Y) (hf : Intertwines θ f) (x : X) :
    orbit G x → orbit C (f x) := fun u => ⟨f u.val, by
      obtain ⟨g, hg⟩ := u.property
      rw [← hg, hf]
      exact mem_orbit (f x) (θ g)⟩

theorem restrictOrbit_intertwines (θ : G →* C) (f : X → Y) (hf : Intertwines θ f) (x : X) :
    Intertwines θ (restrictOrbit θ f hf x) :=
  fun g u => Subtype.ext (hf g u.val)

theorem orbitMap_onto (θ : G →* C) (hθ : Function.Surjective θ) (x : X) (z : Y)
    (hs : (stabilizer G x).map θ ≤ stabilizer C z) {y : Y} (hy : y ∈ orbit C z) :
    ∃ u : orbit G x, orbitMap θ x z hs u = y := by
  obtain ⟨c, rfl⟩ := hy
  obtain ⟨g, rfl⟩ := hθ c
  exact ⟨⟨g • x, mem_orbit x g⟩, orbitMap_translate θ x z hs g⟩

section Finite
variable [Fintype X] [Fintype Y]

noncomputable instance orbitsFintype : Fintype (Orbits G X) := Fintype.ofFinite _

noncomputable def orbitCard (o : Orbits G X) : ℕ := Nat.card (orbit G o.out)

noncomputable def assignmentOf (f : X → Y) (o : Orbits G X) : Orbits C Y := orbitOf C (f o.out)

/-- The exact contribution from one whole source orbit to any target point. -/
theorem orbit_fiber_card (θ : G →* C) (hθ : Function.Surjective θ)
    (f : X → Y) (hf : Intertwines θ f) (o : Orbits G X) (y : Y) :
    Nat.card {u : orbit G o.out // f u.val = y} =
      if assignmentOf (C := C) f o = orbitOf C y then
        orbitCard o / orbitCard (orbitOf C y) else 0 := by
  classical
  by_cases hy : assignmentOf (C := C) f o = orbitOf C y
  · rw [ite_eq_left hy]
    have hym : y ∈ orbit C (f o.out) := (orbitOf_eq_iff _ _).mp hy.symm
    let z : orbit C (f o.out) := ⟨y, hym⟩
    have e : {u : orbit G o.out // restrictOrbit θ f hf o.out u = z} ≃
        {u : orbit G o.out // f u.val = y} :=
      Equiv.subtypeEquivRight (fun _ => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
    have hc := transitive_fiber_card θ hθ (restrictOrbit θ f hf o.out)
      (restrictOrbit_intertwines θ f hf o.out) z
    rw [Nat.card_congr e] at hc
    have hcard := orbit_card_eq (G := C) ((orbitOf_out (orbitOf C y)).trans hy.symm)
    simpa only [orbitCard, hcard] using hc
  · rw [ite_eq_right hy]
    have : IsEmpty {u : orbit G o.out // f u.val = y} := ⟨by
      intro u
      have hu : orbitOf C (f u.val.val) = orbitOf C (f o.out) := by
        obtain ⟨g, hg⟩ := u.val.property
        rw [← hg, hf, orbitOf_smul]
      exact hy (hu.symm.trans (congrArg (orbitOf C) u.property))⟩
    simp

omit [Fintype Y] in
/-- Partition an actual output fibre by its complete source orbits. -/
theorem fiber_card_sum_orbits (f : X → Y) (y : Y) :
    Nat.card {x : X // f x = y} =
      ∑ o : Orbits G X, Nat.card {u : orbit G o.out // f u.val = y} := by
  classical
  let p : {x : X // f x = y} → Orbits G X := fun x => orbitOf G x.val
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv p)
  rw [Nat.card_sigma] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro o _
  let e : {u : {x : X // f x = y} // p u = o} ≃
      {u : orbit G o.out // f u.val = y} := {
    toFun := fun u => ⟨⟨u.val.val, (orbitOf_eq_iff _ _).mp
      (u.property.trans (orbitOf_out o).symm)⟩, u.val.property⟩
    invFun := fun u => ⟨⟨u.val.val, u.property⟩, orbitOf_eq_of_mem u.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- Balance is exactly the sum of actual whole-orbit contributions. -/
theorem balanced_iff_orbit_sums (θ : G →* C) (hθ : Function.Surjective θ)
    (f : X → Y) (hf : Intertwines θ f) (F : ℕ) :
    (∀ y : Y, Nat.card {x : X // f x = y} = F) ↔
      (∀ D : Orbits C Y, (∑ o : Orbits G X,
        if assignmentOf (C := C) f o = D then orbitCard o / orbitCard D else 0) = F) := by
  have hsum (y : Y) : Nat.card {x : X // f x = y} =
      ∑ o : Orbits G X, if assignmentOf (C := C) f o = orbitOf C y then
        orbitCard o / orbitCard (orbitOf C y) else 0 := by
    rw [fiber_card_sum_orbits (G := G)]
    apply Finset.sum_congr rfl
    intro o _
    exact orbit_fiber_card θ hθ f hf o y
  constructor
  · intro hb D
    have hh := (hsum D.out).symm.trans (hb D.out)
    simpa only [orbitOf_out] using hh
  · intro hb y
    exact (hsum y).trans (hb (orbitOf C y))

def Allowed (θ : G →* C) (o : Orbits G X) (D : Orbits C Y) : Prop :=
  (stabilizer G o.out).map θ ≤ stabilizer C D.out

/-- One representative and its allowed target produce a total map on all source states. -/
noncomputable def fromAssignment (θ : G →* C) (a : Orbits G X → Orbits C Y)
    (ha : ∀ o, Allowed θ o (a o)) (x : X) : Y :=
  orbitMap θ (orbitOf G x).out (a (orbitOf G x)).out (ha (orbitOf G x)) ⟨x, mem_out_orbit x⟩

omit [Fintype X] [Fintype Y] in
theorem fromAssignment_eq (θ : G →* C) (a : Orbits G X → Orbits C Y)
    (ha : ∀ o, Allowed θ o (a o)) (o : Orbits G X) (x : X) (hx : orbitOf G x = o) :
    fromAssignment θ a ha x = orbitMap θ o.out (a o).out (ha o)
      ⟨x, (orbitOf_eq_iff _ _).mp (hx.trans (orbitOf_out o).symm)⟩ := by
  subst o
  rfl

omit [Fintype X] [Fintype Y] in
theorem fromAssignment_intertwines (θ : G →* C) (a : Orbits G X → Orbits C Y)
    (ha : ∀ o, Allowed θ o (a o)) : Intertwines θ (fromAssignment θ a ha) := by
  intro g x
  rw [fromAssignment_eq θ a ha (orbitOf G x) (g • x) (orbitOf_smul g x),
    fromAssignment_eq θ a ha (orbitOf G x) x rfl]
  exact orbitMap_intertwines θ (orbitOf G x).out (a (orbitOf G x)).out
    (ha (orbitOf G x)) g ⟨x, mem_out_orbit x⟩

omit [Fintype X] [Fintype Y] in
theorem assignmentOf_fromAssignment (θ : G →* C) (a : Orbits G X → Orbits C Y)
    (ha : ∀ o, Allowed θ o (a o)) :
    assignmentOf (G := G) (C := C) (fromAssignment θ a ha) = a := by
  funext o
  unfold assignmentOf fromAssignment
  simp only [orbitOf_out]
  exact orbitOf_eq_of_mem (orbitMap_mem θ _ _ _ _)

section Cyclic
variable [IsCyclic C]

omit [Fintype Y] in
theorem stabilizer_eq_of_orbit {y z : Y} (h : orbitOf C y = orbitOf C z) :
    stabilizer C y = stabilizer C z := by
  obtain ⟨c, rfl⟩ := (orbitOf_eq_iff _ _).mp h
  let : CommGroup C := IsCyclic.commGroup
  exact stabilizer_smul_eq_right c z

omit [Fintype X] in
/-- The phase stabilizer, and hence its index, is independent of the chosen
representative of a source orbit. -/
theorem phase_stabilizer_smul (θ : G →* C) (g : G) (x : X) :
    (stabilizer G (g • x)).map θ = (stabilizer G x).map θ := by
  let : CommGroup C := IsCyclic.commGroup
  rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply, mul_assoc]

omit [Fintype X] in
theorem phase_stabilizer_of_orbit (θ : G →* C) {x z : X} (h : orbitOf G x = orbitOf G z) :
    (stabilizer G x).map θ = (stabilizer G z).map θ := by
  obtain ⟨g, rfl⟩ := (orbitOf_eq_iff _ _).mp h
  exact phase_stabilizer_smul θ g z

omit [Fintype X] [Fintype Y] in
theorem assignmentOf_allowed (θ : G →* C) (f : X → Y) (hf : Intertwines θ f)
    (o : Orbits G X) : Allowed θ o (assignmentOf (C := C) f o) := by
  have hs := stabilizer_map_le θ hf o.out
  have he := stabilizer_eq_of_orbit (orbitOf_out (assignmentOf (C := C) f o))
  change stabilizer C (assignmentOf (C := C) f o).out = stabilizer C (f o.out) at he
  change _ ≤ stabilizer C (assignmentOf (C := C) f o).out
  rw [he]
  exact hs

omit [Fintype X] [Fintype Y] in
/-- In the actual finite cyclic phase group, the stabilizer condition is precisely
 the index divisor in the manuscript. -/
theorem allowed_iff_divides (θ : G →* C) (o : Orbits G X) (D : Orbits C Y) :
    Allowed θ o D ↔ orbitCard D ∣ ((stabilizer G o.out).map θ).index := by
  rw [Allowed, IsCyclic.subgroup_le_iff_index_dvd, index_stabilizer]
  rfl

/-- Exact whole-orbit assignment criterion, with existence in both directions.
No orbit map, constant-fibre certificate, or fractional orbit splitting is assumed. -/
theorem balanced_map_iff_orbit_assignment (θ : G →* C) (hθ : Function.Surjective θ) (F : ℕ) :
    (∃ f : X → Y, Intertwines θ f ∧ ∀ y, Nat.card {x : X // f x = y} = F) ↔
      (∃ a : Orbits G X → Orbits C Y,
        (∀ o, orbitCard (a o) ∣ ((stabilizer G o.out).map θ).index) ∧
        ∀ D : Orbits C Y, (∑ o : Orbits G X,
          if a o = D then orbitCard o / orbitCard D else 0) = F) := by
  constructor
  · rintro ⟨f, hf, hb⟩
    refine ⟨assignmentOf (C := C) f, ?_, (balanced_iff_orbit_sums θ hθ f hf F).mp hb⟩
    intro o
    exact (allowed_iff_divides θ o _).mp (assignmentOf_allowed θ f hf o)
  · rintro ⟨a, ha, hsum⟩
    have hs : ∀ o, Allowed θ o (a o) := fun o => (allowed_iff_divides θ o (a o)).mpr (ha o)
    refine ⟨fromAssignment θ a hs, fromAssignment_intertwines θ a hs, ?_⟩
    apply (balanced_iff_orbit_sums θ hθ _ (fromAssignment_intertwines θ a hs) F).mpr
    rw [assignmentOf_fromAssignment]
    exact hsum

end Cyclic

/-- The manuscript's explicit cyclic phase group `ℤ/dℤ`; multiplicative notation
is only the standard wrapper allowing a homomorphism from an arbitrary group. -/
theorem cyclic_balanced_map_iff_orbit_assignment {d : ℕ} [NeZero d]
    [MulAction (Multiplicative (ZMod d)) Y]
    (θ : G →* Multiplicative (ZMod d)) (hθ : Function.Surjective θ) (F : ℕ) :
    (∃ f : X → Y, Intertwines θ f ∧ ∀ y, Nat.card {x : X // f x = y} = F) ↔
      (∃ a : Orbits G X → Orbits (Multiplicative (ZMod d)) Y,
        (∀ o, orbitCard (a o) ∣ ((stabilizer G o.out).map θ).index) ∧
        ∀ D : Orbits (Multiplicative (ZMod d)) Y, (∑ o : Orbits G X,
          if a o = D then orbitCard o / orbitCard D else 0) = F) :=
  balanced_map_iff_orbit_assignment θ hθ F

end Finite
end SharedDecoders.OrbitAssignment

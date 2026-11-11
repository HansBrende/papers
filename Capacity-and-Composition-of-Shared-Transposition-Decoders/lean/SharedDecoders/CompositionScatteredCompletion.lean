import SharedDecoders.CompositionScatteredSource

/-! # A total first factor for the scattered binary source -/

namespace SharedDecoders

open CapacityIntervals

variable {d : ℕ} [NeZero d] {A : Type*} [Zero A]

omit [NeZero d] in
private theorem punctured_zero_column_iff (u : {u : ColumnWord d A // u ≠ 0})
    (s c : ZMod d) : (fun i => rot s (puncturedColumns u.val) i c) = 0 ↔ c+s=0 := by
  constructor
  · intro h
    by_contra hc
    apply u.property
    simpa only [rot_apply, puncturedColumns, hc, ite_false] using h
  · intro h
    funext i
    simp [rot, puncturedColumns, h]

omit [NeZero d] in
theorem punctured_orbit_injective (hd : 2 ≤ d) :
    Function.Injective (fun su : ZMod d × {u : ColumnWord d A // u ≠ 0} =>
      rot su.1 (puncturedColumns su.2.val)) := by
  rintro ⟨s,u⟩ ⟨t,v⟩ h
  have hh := congrArg (fun X => fun i => X i (-s)) h
  have hz : (fun i => rot s (puncturedColumns u.val) i (-s)) = 0 :=
    (punctured_zero_column_iff u s (-s)).mpr (neg_add_cancel s)
  have ht := (punctured_zero_column_iff v t (-s)).mp (hh.symm.trans hz)
  have hst : s=t := by linear_combination -ht
  subst t
  have huv := puncturedColumns_injective hd ((rotEquiv s).injective h)
  exact Prod.ext rfl (Subtype.ext huv)

variable {b : ℕ}

noncomputable def scatteredEquivariantCompletion (hd : 2 ≤ d) :
    Equiv.Perm (State d (Fin b → Bit)) :=
  exchangeEquiv
    (fun su : ZMod d × {u : ColumnWord d (Fin b → Bit) // u ≠ 0} =>
      rot su.1 (scatteredSourceMap su.2.val))
    (fun su => rot su.1 (puncturedColumns su.2.val))
    (scattered_orbit_injective hd) (punctured_orbit_injective hd)
    (fun su tv => scattered_punctured_orbits_disjoint hd su.1 tv.1 su.2 tv.2)

theorem scatteredCompletion_equivariant (hd : 2 ≤ d) :
    Equivariant (scatteredEquivariantCompletion (b := b) hd) := by
  intro s X
  apply exchangeFamilies_commutes _ _ (scattered_orbit_injective hd)
    (punctured_orbit_injective hd)
    (fun su tv => scattered_punctured_orbits_disjoint hd su.1 tv.1 su.2 tv.2)
    (rotEquiv s) (Equiv.prodCongr (Equiv.addLeft s) (Equiv.refl _))
  · intro su
    exact (rot_rot s su.1 _).symm
  · intro su
    exact (rot_rot s su.1 _).symm

theorem scatteredCompletion_zero (hd : 2 ≤ d) :
    scatteredEquivariantCompletion (b := b) hd 0 = 0 := by
  apply exchangeFamilies_outside
  · rintro ⟨⟨s,u⟩, hu⟩
    apply u.property
    have hz : rot s (scatteredSourceMap u.val) = rot s (scatteredSourceMap 0) := by
      simpa only [map_zero, show rot s (0 : State d (Fin b → Bit)) = 0 from rfl] using hu
    exact scatteredSourceMap_injective ((rotEquiv s).injective hz)
  · rintro ⟨⟨s,u⟩, hu⟩
    apply u.property
    have hz : rot s (puncturedColumns u.val) = rot s (puncturedColumns 0) := by
      simpa only [puncturedColumns_zero, show rot s (0 : State d (Fin b → Bit)) = 0 from rfl] using hu
    exact puncturedColumns_injective hd ((rotEquiv s).injective hz)

theorem scatteredCompletion_source (hd : 2 ≤ d) (u : ColumnWord d (Fin b → Bit)) :
    scatteredEquivariantCompletion hd (scatteredSourceMap u) = puncturedColumns u := by
  by_cases hu : u=0
  · subst u
    simpa only [map_zero, puncturedColumns_zero] using scatteredCompletion_zero (b := b) hd
  · have h := exchangeFamilies_left
      (fun su : ZMod d × {u : ColumnWord d (Fin b → Bit) // u ≠ 0} =>
        rot su.1 (scatteredSourceMap su.2.val))
      (fun su => rot su.1 (puncturedColumns su.2.val))
      (scattered_orbit_injective hd) (0, ⟨u,hu⟩)
    change exchangeFamilies _ _ _ = _
    simpa only [rot_zero] using h

noncomputable def scatteredFirstFactor (hd : 2 ≤ d) :
    Equiv.Perm (State d (Fin b → Bit)) :=
  columnPatch hd * scatteredEquivariantCompletion hd

theorem scatteredFirstFactor_classUniform (hd : 2 ≤ d) :
    ClassUniform singletonRest (scatteredFirstFactor (b := b) hd) :=
  columnPatch_comp_classUniform hd _ (scatteredCompletion_equivariant hd)

theorem scatteredFirstFactor_source (hd : 2 ≤ d) (u : ColumnWord d (Fin b → Bit)) :
    scatteredFirstFactor hd (scatteredSourceMap u) = constantColumns u := by
  change columnPatch hd (scatteredEquivariantCompletion hd (scatteredSourceMap u)) = _
  rw [scatteredCompletion_source, columnPatch_punctured]

omit [NeZero d] [Zero A] in
theorem fixed_columns_iff_constant (X : State d A) :
    (∀ s, rot s X = X) ↔ ∃ u, X = constantColumns u := by
  constructor
  · intro h
    refine ⟨fun i => X i 0, ?_⟩
    funext i c
    simpa only [rot_apply, zero_add, constantColumns] using congrArg (fun Y => Y i 0) (h c)
  · rintro ⟨u,rfl⟩ s
    rfl

/-- The complete first factor has precisely the scattered source as the
preimage of the fixed-column subspace. -/
theorem scatteredFirstFactor_fixed_preimage (hd : 2 ≤ d)
    (X : State d (Fin b → Bit)) :
    (∀ s, rot s (scatteredFirstFactor hd X) = scatteredFirstFactor hd X) ↔
      X ∈ scatteredSource := by
  rw [fixed_columns_iff_constant]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, (scatteredFirstFactor hd).injective ?_⟩
    rw [scatteredFirstFactor_source, hu]
  · rintro ⟨u,rfl⟩
    exact ⟨u, scatteredFirstFactor_source hd u⟩

/-- One equivariant class cannot carry even this scattered source injectively
into the fixed-column space. -/
theorem scattered_one_class_impossible [NeZero b] (hd : 2 ≤ d)
    (K : State d (Fin b → Bit) → State d (Fin b → Bit))
    (hK : Equivariant K) (hKi : Function.Injective K)
    (hfix : ∀ u : ColumnWord d (Fin b → Bit), ∀ s,
      rot s (K (scatteredSourceMap u)) = K (scatteredSourceMap u)) : False := by
  obtain ⟨u, hu⟩ := exists_ne (0 : ColumnWord d (Fin b → Bit))
  have h := hKi ((hK 1 (scatteredSourceMap u)).trans (hfix u 1))
  have he : rot 1 (scatteredSourceMap u) = rot 0 (scatteredSourceMap u) := by
    simpa only [rot_zero] using h
  have hh := scattered_orbit_injective hd
    (a₁ := (1, ⟨u,hu⟩)) (a₂ := (0, ⟨u,hu⟩)) he
  exact one_ne_zero_of_two_le hd (congrArg Prod.fst hh)

end SharedDecoders

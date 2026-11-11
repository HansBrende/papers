import SharedDecoders.CapacityIntervalsField
import SharedDecoders.CompositionSparsePatch

/-! # A scattered normal-basis source and its literal orbit embeddings -/

namespace SharedDecoders

open Module
open CapacityIntervals

variable {d b : ℕ} [NeZero d]

noncomputable def scatteredFieldMap :
    ColumnWord d (Fin b → Bit) →ₗ[Bit] (ZMod d → Fin b → Extension d) where
  toFun u i l := if i = 0 then rowEncode d (fun j => u j l)
    else normalElement d * rowEncode d (fun j => u j l)
  map_add' u v := by
    funext i l
    have he := (rowEncode d).map_add (fun j => u j l) (fun j => v j l)
    change (if i=0 then rowEncode d (fun j => u j l + v j l)
      else normalElement d * rowEncode d (fun j => u j l + v j l)) = _
    simp only [Pi.add_apply]
    split_ifs
    · exact he
    · exact (congrArg (normalElement d * ·) he).trans (mul_add _ _ _)
  map_smul' a u := by
    funext i l
    have he := (rowEncode d).map_smul a (fun j => u j l)
    change (if i=0 then rowEncode d (fun j => a • u j l)
      else normalElement d * rowEncode d (fun j => a • u j l)) = _
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · exact he
    · exact (congrArg (normalElement d * ·) he).trans (mul_smul_comm _ _ _)

noncomputable def scatteredSourceMap :
    ColumnWord d (Fin b → Bit) →ₗ[Bit] State d (Fin b → Bit) :=
  (fieldEncode d).symm.toLinearMap.comp scatteredFieldMap

noncomputable def scatteredSource : Submodule Bit (State d (Fin b → Bit)) :=
  (scatteredSourceMap (d := d) (b := b)).range

@[simp] theorem fieldEncode_scattered (u : ColumnWord d (Fin b → Bit)) :
    fieldEncode d (scatteredSourceMap u) = scatteredFieldMap u :=
  (fieldEncode d).apply_symm_apply _

@[simp] theorem scatteredSourceMap_first (u : ColumnWord d (Fin b → Bit)) :
    scatteredSourceMap u 0 = u := by
  funext j l
  change (rowEncode d).symm (scatteredFieldMap u 0 l) j = u j l
  simp [scatteredFieldMap]

theorem scatteredSourceMap_injective :
    Function.Injective (scatteredSourceMap (d := d) (b := b)) := by
  intro u v h
  simpa only [scatteredSourceMap_first] using congrArg (fun X => X 0) h

theorem scatteredSource_finrank :
    finrank Bit (scatteredSource (d := d) (b := b)) = d * b := by
  rw [scatteredSource, LinearMap.finrank_range_of_inj scatteredSourceMap_injective]
  simp [Module.finrank_pi_fintype, ZMod.card]

omit [NeZero d] in
private theorem normalElement_ne_zero' : normalElement d ≠ 0 :=
  (IsGalois.normalBasis Bit (Extension d)).ne_zero 1

private theorem phase_normal_ne_one (hd : 2 ≤ d) (s : ZMod d) :
    phase d s (normalElement d) ≠ 1 := by
  intro h
  have hβ : normalElement d = 1 := (phase d s).injective (h.trans (map_one _).symm)
  have h10 : (1 : ZMod d) = 0 := phase_normal_injective d (by simp [hβ])
  exact one_ne_zero_of_two_le hd h10

/-- No nonzero source state has two identical rotated representations. -/
theorem scattered_orbit_injective (hd : 2 ≤ d) :
    Function.Injective (fun su : ZMod d × {u : ColumnWord d (Fin b → Bit) // u ≠ 0} =>
      rot su.1 (scatteredSourceMap su.2.val)) := by
  rintro ⟨s,u⟩ ⟨t,v⟩ h
  have hst : s = t := by
    by_contra hst
    have hu0 : u.val = 0 := by
      funext j l
      have hfirst := congrArg (fun X => fieldEncode d X 0 l) h
      have hsecond := congrArg (fun X => fieldEncode d X 1 l) h
      simp only [fieldEncode_rot, fieldEncode_scattered, scatteredFieldMap,
        LinearMap.coe_mk, AddHom.coe_mk, ite_true, ite_eq_right (one_ne_zero_of_two_le hd),
        map_mul] at hfirst hsecond
      have hcoeff : phase d s (normalElement d) - phase d t (normalElement d) ≠ 0 :=
        sub_ne_zero.mpr (fun he => hst (phase_normal_injective d he))
      rw [hfirst] at hsecond
      have he : (phase d s (normalElement d) - phase d t (normalElement d)) *
          phase d t (rowEncode d (fun j => v.val j l)) = 0 := by
        rw [sub_mul]
        exact sub_eq_zero.mpr hsecond
      have hz := (mul_eq_zero.mp he).resolve_left hcoeff
      have hu := (phase d s).injective (hfirst.trans (hz.trans (map_zero _).symm))
      have hu' := (rowEncode d).injective (hu.trans (map_zero _).symm)
      exact congrFun hu' j
    exact u.property hu0
  subst t
  have huv := scatteredSourceMap_injective ((rotEquiv s).injective h)
  exact Prod.ext rfl (Subtype.ext huv)

private theorem bit_eq_one_of_ne_zero {x : Bit} (hx : x ≠ 0) : x = 1 := by
  exact (by decide +kernel : ∀ x : Bit, x ≠ 0 → x = 1) x hx

/-- The source orbits and punctured-column orbits are disjoint. This supplies
the missing compatibility for a literal equivariant exchange. -/
theorem scattered_punctured_orbits_disjoint (hd : 2 ≤ d)
    (s t : ZMod d) (u v : {u : ColumnWord d (Fin b → Bit) // u ≠ 0}) :
    rot s (scatteredSourceMap u.val) ≠ rot t (puncturedColumns v.val) := by
  intro h
  have hu : ∃ l, rowEncode d (fun j => u.val j l) ≠ 0 := by
    by_contra! hn
    apply u.property
    funext j l
    exact congrFun ((rowEncode d).injective ((hn l).trans (map_zero _).symm)) j
  obtain ⟨l, hl⟩ := hu
  have h0 := congrArg (fun X => fieldEncode d X 0 l) h
  have h1 := congrArg (fun X => fieldEncode d X 1 l) h
  simp only [fieldEncode_rot, fieldEncode_scattered, scatteredFieldMap,
    LinearMap.coe_mk, AddHom.coe_mk, ite_true, ite_eq_right (one_ne_zero_of_two_le hd),
    map_mul] at h0 h1
  have hv0 : v.val 0 l ≠ 0 := by
    intro hz
    have hh : fieldEncode d (puncturedColumns v.val) 0 l = 0 := by
      change rowEncode d (fun j => (if j = 0 then 0 else v.val _) l) = 0
      rw [← (rowEncode d).map_zero]
      apply congrArg (rowEncode d)
      funext j
      split_ifs <;> simp [hz]
    rw [hh, map_zero] at h0
    exact hl ((phase d s).injective (h0.trans (map_zero _).symm))
  have hv1 : v.val 1 l ≠ 0 := by
    intro hz
    have hh : fieldEncode d (puncturedColumns v.val) 1 l = 0 := by
      change rowEncode d (fun j => (if j = 0 then 0 else v.val _) l) = 0
      rw [← (rowEncode d).map_zero]
      apply congrArg (rowEncode d)
      funext j
      split_ifs <;> simp [hz]
    rw [hh, map_zero] at h1
    have ha : phase d s (normalElement d) ≠ 0 :=
      (map_ne_zero_iff (phase d s) (phase d s).injective).mpr normalElement_ne_zero'
    have hb : phase d s (rowEncode d (fun j => u.val j l)) ≠ 0 :=
      (map_ne_zero_iff (phase d s) (phase d s).injective).mpr hl
    exact (mul_ne_zero ha hb) h1
  have hh : fieldEncode d (puncturedColumns v.val) 0 l =
      fieldEncode d (puncturedColumns v.val) 1 l := by
    apply congrArg (rowEncode d)
    funext j
    change (if j=0 then 0 else v.val 0) l = (if j=0 then 0 else v.val 1) l
    split_ifs <;> simp [bit_eq_one_of_ne_zero hv0, bit_eq_one_of_ne_zero hv1]
  rw [← hh, ← h0] at h1
  have hnonzero : phase d s (rowEncode d (fun j => u.val j l)) ≠ 0 :=
    (map_ne_zero_iff (phase d s) (phase d s).injective).mpr hl
  exact phase_normal_ne_one hd s (mul_right_cancel₀ hnonzero (h1.trans (one_mul _).symm))

end SharedDecoders

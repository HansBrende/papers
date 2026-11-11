import SharedDecoders.CapacityRuns
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A finite coordinate on each translation orbit, including one-point orbits. -/

namespace SharedDecoders.CapacityRuns

open AddSubgroup
attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev TranslationOrbit (s : G) := G ⧸ zmultiples s

noncomputable instance (s : G) : Fintype (TranslationOrbit s) := Fintype.ofFinite _

noncomputable def walk (s : G) (o : TranslationOrbit s) (j : ℕ) : G :=
  o.out + j • s

omit [Fintype G] in
theorem walk_orbit (s : G) (o : TranslationOrbit s) (j : ℕ) :
    (↑(walk s o j) : TranslationOrbit s) = o := by
  calc
    (↑(walk s o j) : TranslationOrbit s) = (o.out : TranslationOrbit s) := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change (o.out + j • s) - o.out ∈ zmultiples s
      simp only [add_sub_cancel_left]
      exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples s) j
    _ = o := Quotient.out_eq' o

omit [Fintype G] in
theorem walk_add (s : G) (o : TranslationOrbit s) (i j : ℕ) :
    walk s o (i + j) = walk s o i + j • s := by
  simp [walk, add_nsmul, add_assoc]

omit [Fintype G] in
theorem walk_injective (s : G) (o : TranslationOrbit s) :
    Function.Injective (fun j : Fin (addOrderOf s) => walk s o j.val) := by
  intro i j h
  apply Fin.ext
  apply nsmul_injOn_Iio_addOrderOf i.isLt j.isLt
  exact add_left_cancel h

/-- The orbit coordinate is defined by actual translation from a representative. -/
noncomputable def orbitCoordinates (s : G) :
    (TranslationOrbit s × Fin (addOrderOf s)) ≃ G :=
  Equiv.ofBijective (fun z => walk s z.1 z.2.val) (by
    constructor
    · rintro ⟨o, i⟩ ⟨p, j⟩ h
      have ho : o = p := by
        calc
          o = (↑(walk s o i.val) : TranslationOrbit s) := (walk_orbit s o i.val).symm
          _ = (↑(walk s p j.val) : TranslationOrbit s) := congrArg _ h
          _ = p := walk_orbit s p j.val
      subst p
      have hi := walk_injective s o h
      simp only [Prod.mk.injEq, true_and]
      exact hi
    · intro x
      let o : TranslationOrbit s := x
      have hm : x - o.out ∈ zmultiples s := by
        apply QuotientAddGroup.eq_iff_sub_mem.mp
        exact (Quotient.out_eq' o).symm
      obtain ⟨j, hj⟩ := (finEquivZMultiples (isOfFinAddOrder_of_finite s)).surjective
        ⟨x - o.out, hm⟩
      refine ⟨(o, j), ?_⟩
      have he := congrArg Subtype.val hj
      change j.val • s = x - o.out at he
      simp only [walk, he, add_sub_cancel])

@[simp] theorem orbitCoordinates_apply (s : G)
    (z : TranslationOrbit s × Fin (addOrderOf s)) :
    orbitCoordinates s z = walk s z.1 z.2.val := rfl

noncomputable def orbitOf (s x : G) : TranslationOrbit s := (orbitCoordinates s).symm x |>.1

noncomputable def indexOf (s x : G) : Fin (addOrderOf s) := (orbitCoordinates s).symm x |>.2

theorem walk_index (s x : G) : walk s (orbitOf s x) (indexOf s x).val = x :=
  (orbitCoordinates s).apply_symm_apply x

@[simp] theorem orbitOf_walk (s : G) (o : TranslationOrbit s) (j : Fin (addOrderOf s)) :
    orbitOf s (walk s o j.val) = o :=
  congrArg Prod.fst ((orbitCoordinates s).symm_apply_apply (o, j))

@[simp] theorem indexOf_walk (s : G) (o : TranslationOrbit s) (j : Fin (addOrderOf s)) :
    indexOf s (walk s o j.val) = j :=
  congrArg Prod.snd ((orbitCoordinates s).symm_apply_apply (o, j))

theorem translationOrbit_card {d : ℕ} [NeZero d] (s : ZMod d) :
    Fintype.card (TranslationOrbit s) = Nat.gcd d s.val := by
  have htop : zmultiples (1 : ZMod d) = ⊤ := by
    apply top_unique
    intro x _
    exact ⟨(x.val : ℤ), by simp⟩
  have hh := AddSubgroup.index_zmultiples_zsmul htop (s.val : ℤ)
  have hs : (s.val : ℤ) • (1 : ZMod d) = s := by simp
  rw [hs, ZMod.addOrderOf_one, Int.gcd_natCast_natCast,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card] at hh
  simpa only [Nat.gcd_comm] using hh

end SharedDecoders.CapacityRuns

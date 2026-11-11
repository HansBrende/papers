import SharedDecoders.CapacityRetention
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import LeanMachine.PermutationFixedSpace

/-! # Exact dimensions of a symmetric space and its cyclic translate

The two symmetries form a dihedral permutation action. Burnside's formula
counts its fixed coordinate functions in every characteristic.
-/

namespace SharedDecoders.RetentionOrbit

variable {d : ℕ} [NeZero d]

def act (s : ZMod d) : DihedralGroup d → (ZMod d × ZMod d) → (ZMod d × ZMod d)
  | .r a, (i, j) => (i + a * s, j - a * s)
  | .sr a, (i, j) => (j - a * s, i + a * s)

@[instance_reducible] def action (s : ZMod d) : MulAction (DihedralGroup d) (ZMod d × ZMod d) where
  smul := act s
  one_smul := by
    intro p
    change act s (.r 0) p = p
    cases p
    simp [act]
  mul_smul := by
    intro g h p
    change act s (g * h) p = act s g (act s h p)
    cases g <;> cases h <;> cases p <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, act] <;>
      ext <;> ring

def reflectionFixedEquiv (s a : ZMod d) :
    {p : ZMod d × ZMod d // act s (.sr a) p = p} ≃ ZMod d where
  toFun p := p.val.1
  invFun i := ⟨(i, i + a * s), by simp [act]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd p.property
      exact h
  right_inv _ := rfl

omit [NeZero d] in
theorem card_reflection_fixed (s a : ZMod d) :
    Nat.card {p : ZMod d × ZMod d // act s (.sr a) p = p} = d := by
  rw [Nat.card_congr (reflectionFixedEquiv s a), Nat.card_zmod]

theorem card_rotation_fixed (s a : ZMod d) :
    Nat.card {p : ZMod d × ZMod d // act s (.r a) p = p} =
      if a * s = 0 then d * d else 0 := by
  classical
  by_cases h : a * s = 0
  · simp [act, h, Nat.card_eq_fintype_card]
  · let _ : IsEmpty {p : ZMod d × ZMod d // act s (.r a) p = p} :=
      ⟨fun p => h (by simpa [act] using congrArg Prod.fst p.property)⟩
    simp [h, Nat.card_eq_fintype_card]

theorem card_zero_multiples (s : ZMod d) :
    Nat.card {a : ZMod d // a * s = 0} = Nat.gcd d s.val := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod d) s.val
  have he : {a : ZMod d // a * s = 0} ≃
      (nsmulAddMonoidHom s.val : ZMod d →+ ZMod d).ker :=
    Equiv.subtypeEquivRight (fun a => by simp [nsmul_eq_mul, mul_comm])
  rw [Nat.card_congr he, h, Nat.card_zmod]

theorem sum_fixed_counts (s : ZMod d) :
    (∑ g : DihedralGroup d, Nat.card {p : ZMod d × ZMod d // act s g p = p}) =
      d * d * (Nat.gcd d s.val + 1) := by
  classical
  have he := Equiv.sum_comp (DihedralGroup.equivSum.symm :
    (ZMod d ⊕ ZMod d) ≃ DihedralGroup d)
    (fun g => Nat.card {p : ZMod d × ZMod d // act s g p = p})
  rw [← he, Fintype.sum_sum_type]
  change (∑ a : ZMod d, Nat.card {p : ZMod d × ZMod d // act s (.r a) p = p}) +
    (∑ a : ZMod d, Nat.card {p : ZMod d × ZMod d // act s (.sr a) p = p}) = _
  simp only [card_rotation_fixed, card_reflection_fixed]
  have hc : (Finset.univ.filter (fun a : ZMod d => a * s = 0)).card = Nat.gcd d s.val := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using card_zero_multiples s
  rw [← Finset.sum_filter]
  simp [hc]
  ring

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

def pairedSymmetric (s : ZMod d) : Submodule F (State d A) :=
  symmetricSpace ⊓ symmetricSpace.map (rotLinear F s)

theorem paired_translation {s : ZMod d} {X : State d A}
    (hX : X ∈ pairedSymmetric (F := F) s) (a i j : ZMod d) :
    X (i + a * s) (j - a * s) = X i j := by
  obtain ⟨hsym, Y, hY, hXY⟩ := hX
  have hstep (i j : ZMod d) : X (i + s) (j - s) = X i j := by
    have he : X (i + s) (j - s) = X j i := by
      rw [← hXY]
      change Y (i + s) (j - s + s) = Y j (i + s)
      rw [sub_add_cancel, hY (i + s) j]
    exact he.trans (hsym j i)
  have hn (n : ℕ) : ∀ i j, X (i + n • s) (j - n • s) = X i j := by
    induction n with
    | zero => intro i j; simp
    | succ n ih =>
        intro i j
        have hh := (hstep (i + n • s) (j - n • s)).trans (ih i j)
        simpa only [add_nsmul, one_nsmul, add_assoc, sub_add_eq_sub_sub] using hh
  simpa [nsmul_eq_mul] using hn a.val i j

noncomputable def pairedEquiv (s : ZMod d) :
    let _ := action s
    pairedSymmetric (F := F) (A := A) s ≃ₗ[F]
      LeanMachine.PermutationFixedSpace.invariants (F := F) (A := A)
        (G := DihedralGroup d) (Y := ZMod d × ZMod d) := by
  let _ := action s
  refine
    { toFun := fun X => ⟨fun p => X.val p.1 p.2, ?_⟩
      invFun := fun f => ⟨fun i j => f.val (i, j), ?_⟩
      left_inv := fun _ => by apply Subtype.ext; rfl
      right_inv := fun _ => by apply Subtype.ext; funext p; cases p; rfl
      map_add' := fun _ _ => by apply Subtype.ext; rfl
      map_smul' := fun _ _ => by apply Subtype.ext; rfl }
  · intro g p
    cases p with
    | mk i j =>
      cases g with
      | r a => exact paired_translation X.property a i j
      | sr a =>
          exact (X.property.1 (j - a * s) (i + a * s)).trans
            (paired_translation X.property a i j)
  · refine ⟨?_, ?_⟩
    · intro i j
      have h := f.property (.sr 0) (i, j)
      change f.val (act s (.sr 0) (i, j)) = f.val (i, j) at h
      simpa [act] using h.symm
    · refine ⟨rot (-s) (fun i j => f.val (i, j)), ?_, ?_⟩
      · intro i j
        have h := f.property (.sr (-1)) (i, j - s)
        change f.val (act s (.sr (-1)) (i, j - s)) = f.val (i, j - s) at h
        simpa [act, rot, sub_eq_add_neg] using h.symm
      · exact rot_rot_neg s (fun i j => f.val (i, j))

theorem twice_finrank_pairedSymmetric [FiniteDimensional F A] (s : ZMod d) :
    2 * Module.finrank F (pairedSymmetric (F := F) (A := A) s) =
      d * (Nat.gcd d s.val + 1) * Module.finrank F A := by
  let _ := action s
  have h := LeanMachine.PermutationFixedSpace.card_mul_finrank_invariants
    (F := F) (A := A) (G := DihedralGroup d) (Y := ZMod d × ZMod d)
  rw [← (pairedEquiv (F := F) (A := A) s).finrank_eq, DihedralGroup.card] at h
  change (2 * d) * Module.finrank F (pairedSymmetric (F := F) (A := A) s) =
    (∑ g : DihedralGroup d, Nat.card {p : ZMod d × ZMod d // act s g p = p}) *
      Module.finrank F A at h
  rw [sum_fixed_counts] at h
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos d)
  nlinarith

end SharedDecoders.RetentionOrbit

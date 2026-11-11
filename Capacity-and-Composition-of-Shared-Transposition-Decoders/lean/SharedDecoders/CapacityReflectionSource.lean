import SharedDecoders.CapacityGluing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! # The literal reflection source at every lane width

Rows vanish at zero and agree at opposite positions.  For odd prime side
length, two distinct rotated views meet only at zero, so the source admits
one deterministic shared decoder. No Fourier or extension field is needed
for this construction statement.
-/

namespace SharedDecoders.CapacityReflection

open Module

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

def rowSpace (d : ℕ) : Submodule F (ZMod d → A) where
  carrier := {x | x 0=0 ∧ ∀ j, x (-j)=x j}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp [hx.1,hy.1], fun j => congrArg₂ (·+·) (hx.2 j) (hy.2 j)⟩
  smul_mem' := by
    intro a x hx
    exact ⟨by simp [hx.1], fun j => congrArg (a • ·) (hx.2 j)⟩

instance oddNeZero (m : ℕ) : NeZero (2*m+1) := ⟨by omega⟩

private theorem pair_min_pos {m : ℕ} (j : ZMod (2*m+1)) (hj : j≠0) :
    0<min j.val (-j).val := by
  exact lt_min (ZMod.val_pos.mpr hj) (ZMod.val_pos.mpr (neg_ne_zero.mpr hj))

private theorem pair_min_le {m : ℕ} (j : ZMod (2*m+1)) (hj : j≠0) :
    min j.val (-j).val≤m := by
  let : NeZero j := ⟨hj⟩
  have hn := ZMod.val_neg_of_ne_zero j
  have hv := ZMod.val_lt j
  omega

def pairRep {m : ℕ} (j : ZMod (2*m+1)) (hj : j≠0) : Fin m :=
  ⟨min j.val (-j).val-1, by have := pair_min_pos j hj; have := pair_min_le j hj; omega⟩

theorem pairRep_neg {m : ℕ} (j : ZMod (2*m+1)) (hj : j≠0) :
    pairRep (-j) (neg_ne_zero.mpr hj) = pairRep j hj := by
  apply Fin.ext
  simp [pairRep, min_comm]

theorem positiveIndex_ne_zero {m : ℕ} (i : Fin m) :
    ((i.val+1 : ℕ) : ZMod (2*m+1))≠0 := by
  intro hz
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem pairRep_positiveIndex {m : ℕ} (i : Fin m) :
    pairRep ((i.val+1 : ℕ) : ZMod (2*m+1)) (positiveIndex_ne_zero i)=i := by
  let j : ZMod (2*m+1) := ((i.val+1 : ℕ) : ZMod (2*m+1))
  have hj : j≠0 := positiveIndex_ne_zero i
  let : NeZero j := ⟨hj⟩
  have hv : j.val=i.val+1 := ZMod.val_natCast_of_lt (by omega)
  have hn := ZMod.val_neg_of_ne_zero j
  apply Fin.ext
  change min j.val (-j).val-1=i.val
  rw [hv] at hn ⊢
  omega

noncomputable def rowEquiv (m : ℕ) : rowSpace (F := F) (A := A) (2*m+1) ≃ₗ[F] (Fin m → A) where
  toFun x i := x.1 ((i.val+1 : ℕ) : ZMod (2*m+1))
  invFun y := ⟨fun j => if h : j=0 then 0 else y (pairRep j h), by
    constructor
    · simp
    · intro j
      by_cases hj : j=0
      · simp [hj]
      · simp only [dite_eq_right hj, dite_eq_right (neg_ne_zero.mpr hj)]
        congr 1
        exact pairRep_neg j hj⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hj : j=0
    · simp [hj,x.2.1]
    · simp only [dite_eq_right hj]
      change x.1 (((pairRep j hj).val+1 : ℕ) : ZMod (2*m+1))=x.1 j
      have hp := pair_min_pos j hj
      by_cases hle : j.val≤(-j).val
      · have he : (pairRep j hj).val+1=j.val := by simp only [pairRep, min_eq_left hle]; omega
        rw [he,ZMod.natCast_zmod_val]
      · have he : (pairRep j hj).val+1=(-j).val := by
          simp only [pairRep, min_eq_right (le_of_not_ge hle)]; omega
        rw [he,ZMod.natCast_zmod_val]
        exact x.2.2 j
  right_inv y := by
    funext i
    simp only [dite_eq_right (positiveIndex_ne_zero i), pairRep_positiveIndex]
  map_add' x y := rfl
  map_smul' a x := rfl

theorem finrank_rowSpace [FiniteDimensional F A] (m : ℕ) :
    finrank F (rowSpace (F := F) (A := A) (2*m+1))=m*finrank F A := by
  rw [(rowEquiv (F := F) (A := A) m).finrank_eq]
  simp [Module.finrank_pi_fintype]

def source (d : ℕ) : Submodule F (State d A) where
  carrier := {X | ∀ c, X c ∈ rowSpace (F := F) d}
  zero_mem' := by intro c; exact (rowSpace d).zero_mem
  add_mem' := by intro X Y hX hY c; exact (rowSpace d).add_mem (hX c) (hY c)
  smul_mem' := by intro a X hX c; exact (rowSpace d).smul_mem a (hX c)

def sourceEquiv (d : ℕ) : source (F := F) (A := A) d ≃ₗ[F]
    (ZMod d → rowSpace (F := F) (A := A) d) where
  toFun X c := ⟨X.1 c,X.2 c⟩
  invFun Y := ⟨fun c => (Y c).1,fun c => (Y c).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_source [FiniteDimensional F A] (m : ℕ) :
    finrank F (source (F := F) (A := A) (2*m+1))=(2*m+1)*m*finrank F A := by
  rw [(sourceEquiv (F := F) (A := A) (2*m+1)).finrank_eq]
  simp [Module.finrank_pi_fintype, ZMod.card, finrank_rowSpace, mul_assoc]

theorem constant_of_period {d : ℕ} [Fact d.Prime] {B : Type*}
    (f : ZMod d → B) (s : ZMod d) (hs : s≠0) (hper : ∀ j, f (j+s)=f j)
    (j k : ZMod d) : f j=f k := by
  have hn : ∀ n : ℕ, ∀ j, f (j+n • s)=f j := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih => intro j; rw [succ_nsmul, ← add_assoc, hper, ih]
  have hh := hn ((j-k)/s).val k
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hs,
    add_sub_cancel] at hh
  exact hh

theorem rotated_rows_eq_zero {d : ℕ} [Fact d.Prime] (hd : 2<d)
    (x y : ZMod d → A) (hx : x∈rowSpace (F := F) d) (hy : y∈rowSpace (F := F) d)
    (c e : ZMod d) (hce : c≠e) (heq : (fun j => x (j+c))=(fun j => y (j+e))) :
    (fun j => x (j+c))=0 := by
  let z : ZMod d → A := fun j => x (j+c)
  have hc : ∀ j, z (-j-2*c)=z j := by
    intro j
    change x (-j-2*c+c)=x (j+c)
    rw [show -j-2*c+c=-(j+c) by ring]
    exact hx.2 _
  have he : ∀ j, z (-j-2*e)=z j := by
    intro j
    change x (-j-2*e+c)=x (j+c)
    rw [congrFun heq (-j-2*e),congrFun heq j]
    rw [show -j-2*e+e=-(j+e) by ring]
    exact hy.2 _
  have hp : ∀ j, z (j+2*(e-c))=z j := by
    intro j
    have hh := (hc (-j-2*e)).trans (he j)
    convert hh using 1
    congr 1
    ring
  have htwo : (2 : ZMod d)≠0 := by
    intro hh
    have hv := congrArg ZMod.val hh
    have hv2 : (2 : ZMod d).val=2 := by simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt hd
    rw [hv2, ZMod.val_zero] at hv
    omega
  have hs : 2*(e-c)≠0 := mul_ne_zero htwo (sub_ne_zero.mpr hce.symm)
  funext j
  have hz : z (-c)=0 := by simpa [z] using hx.1
  exact (constant_of_period z _ hs hp j (-c)).trans hz

theorem source_disjoint_views {d : ℕ} [Fact d.Prime] (hd : 2<d)
    (c e : ZMod d) (hce : c≠e) :
    Disjoint ((source (F := F) (A := A) d).map (rotLinear F c))
      ((source (F := F) (A := A) d).map (rotLinear F e)) := by
  rw [Submodule.disjoint_def]
  rintro X ⟨Y,hY,rfl⟩ ⟨Z,hZ,hYZ⟩
  funext i j
  exact congrFun (rotated_rows_eq_zero hd (Y i) (Z i) (hY i) (hZ i) c e hce
    (congrFun hYZ.symm i)) j

theorem source_shared {d : ℕ} [Fact d.Prime] (hd : 2<d)
    {κ : Type*} (p : ZMod d → κ) : IsSharedCode F p (source (F := F) (A := A) d) :=
  IsSharedCode.of_disjoint_views (source_disjoint_views hd)

end SharedDecoders.CapacityReflection

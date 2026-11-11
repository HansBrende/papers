import SharedDecoders.Model
import SharedDecoders.PeriodTransport
import SharedDecoders.CompositionBalance
import Mathlib.Data.Fintype.BigOperators

/-!
# The complete-map inputs to the balance obstruction

Balanced decoder fibers are derived from a bijective complete map. Covariance
is derived from its actual intertwining identity. Neither property is inferred
from correctness on a proper subspace or from surjectivity of a local rule.
-/

namespace SharedDecoders

variable {d : ℕ} {A κ I B : Type*}

theorem coordinate_fiber_card [Fintype I] [Fintype B] (i : I) (z : B) :
    Nat.card {f : I → B // f i = z} = Fintype.card B ^ (Fintype.card I - 1) := by
  classical
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset B) i
      (Finset.mem_univ z)

theorem column_fiber_card [Fintype A] [NeZero d] (c : ZMod d) (z : ZMod d → A) :
    Nat.card {X : State d A // (fun i => X i c) = z} =
      (Fintype.card A ^ d) ^ (d - 1) := by
  have he := Nat.card_congr (swapEquiv.subtypeEquiv
    (p := fun X : State d A => (fun i => X i c) = z)
    (q := fun X : State d A => X c = z) (fun _ => Iff.rfl))
  rw [he, coordinate_fiber_card]
  simp [ZMod.card]

/-- Every decoder used by a bijective complete map is surjective. -/
theorem complete_decoder_surjective
    (p : ZMod d → κ) (K : State d A → State d A)
    (f : κ → State d A → (ZMod d → A))
    (hf : ∀ X c i, K X i c = f (p c) (rot c X) i)
    (hK : Function.Surjective K) (c : ZMod d) :
    Function.Surjective (f (p c)) := by
  intro z
  obtain ⟨X, hX⟩ := hK (fun i _ => z i)
  refine ⟨rot c X, ?_⟩
  funext i
  rw [← hf]
  exact congrFun (congrFun hX i) c

/-- Exact balanced fiber size of an actual complete-map decoder. -/
theorem complete_decoder_fiber_card [Fintype A] [NeZero d]
    (p : ZMod d → κ) (K : State d A → State d A)
    (f : κ → State d A → (ZMod d → A))
    (hf : ∀ X c i, K X i c = f (p c) (rot c X) i)
    (hK : Function.Bijective K) (c : ZMod d) (z : ZMod d → A) :
    Nat.card {X : State d A // f (p c) X = z} =
      (Fintype.card A ^ d) ^ (d - 1) := by
  classical
  let E : State d A ≃ State d A := (rotEquiv (-c)).trans (Equiv.ofBijective K hK)
  have hE (X : State d A) : (fun i => E X i c) = f (p c) X := by
    funext i
    change K (rot (-c) X) i c = f (p c) X i
    rw [hf, rot_rot_neg]
  have he := Nat.card_congr (E.subtypeEquiv
    (p := fun X => f (p c) X = z)
    (q := fun X => (fun i => X i c) = z) (fun X => by rw [hE]))
  exact he.trans (column_fiber_card c z)

/-- Full-domain intertwining gives covariance of the actual decoder at every
receiver. The `+c` conjugation sign is explicit. -/
theorem complete_decoder_covariance
    (p : ZMod d → κ) (K Q : State d A → State d A)
    (f : κ → State d A → (ZMod d → A))
    (hf : ∀ X c i, K X i c = f (p c) (rot c X) i)
    (hQ : ∀ X, K (Q X) = rowRot 1 (K X)) (c : ZMod d) (Y : State d A) :
    f (p c) (rot c (Q (rot (-c) Y))) = fun i => f (p c) Y (i + 1) := by
  funext i
  have h := congrFun (congrFun (hQ (rot (-c) Y)) i) c
  change K (Q (rot (-c) Y)) i c = K (rot (-c) Y) (i + 1) c at h
  simpa only [hf, rot_rot_neg] using h

/-- Cyclic rotations act faithfully on the complete column-word alphabet. -/
instance columnWordRotation : MulAction (Multiplicative (ZMod d)) (ZMod d → A) where
  smul s z := fun i => z (i + s.toAdd)
  one_smul z := by
    funext i
    change z (i + 0) = z i
    rw [add_zero]
  mul_smul s t z := by
    funext i
    change z (i + (s.toAdd + t.toAdd)) = z ((i + s.toAdd) + t.toAdd)
    rw [add_assoc]

instance columnWordRotation_faithful [Nontrivial A] :
    FaithfulSMul (Multiplicative (ZMod d)) (ZMod d → A) where
  eq_of_smul_eq_smul := by
    classical
    intro s t h
    change s.toAdd = t.toAdd
    by_contra hne
    obtain ⟨a, b, hab⟩ := exists_pair_ne A
    let z : ZMod d → A := fun i => if i = s.toAdd then a else b
    have he := congrFun (h z) 0
    change z (0 + s.toAdd) = z (0 + t.toAdd) at he
    have : a = b := by simpa [z, Ne.symm hne] using he
    exact hab this

end SharedDecoders

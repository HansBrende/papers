import TapeStorageRates.PaidInputsSuccess
import TapeStorageRates.FrozenPackets
import TapeStorageRates.NativeSchedule
import Mathlib.Data.Nat.Log

/-!
# Paying for a common packet schedule

At one public horizon the compiler records a fixed-length list of carries and
flush flags, padding after halt. Its alphabet and the coefficient of the number
of batches are independent of the packet size. Counting is on the attained
descriptors of the actual successful payload slice.
-/

namespace TapeStorageRates.PaidClasses

open Finset Filter PaidInputs
open scoped Topology

set_option autoImplicit false

open Classical in
/-- Finite output of a deadline-bounded packet compiler. The relation between
the attained descriptor's population and the frozen class is explicit. -/
def Compiles (M : Transpose.TM) (c : ℝ) (s β J : ℕ) (C : ℝ) : Prop :=
  ∀ d a r : ℕ, 0 < a → r < s →
  ∀ z : Raw d r,
    let F := payloadFibre (a := a) (s := s) (successfulInputsAt M c d (a*s+r)) z
    ∃ R : ℕ, R ≤ J*(d*d*a+1) ∧
      ∃ σ : Payload d a s → Fin R → Native.Descriptor M.k,
      ∀ y ∈ F.image σ, ∃ W : PacketClass M.k s β d a,
        (W.time : ℝ) ≤ C*((d*d*a : ℕ) + 1) ∧ (F.filter fun x => σ x = y) ⊆ W.words

/-- Integer bits per packet sufficient to fix the complete padded descriptor
class, uniformly in the packet size and native control width. -/
def descriptorBill (k J : ℕ) : ℕ := Nat.clog 2 (2*3^(k+1)) * (2*J)

/-- Bound the number of schedules actually attained by the specified successful
payloads. Neither the code nor the descriptor need be injective. -/
theorem attained_support_le {X : Type*} {k R n J : ℕ} (F : Finset X)
    (σ : X → Fin R → Native.Descriptor k) (hn : 0 < n) (hR : R ≤ J*(n+1)) :
    (F.image σ).card ≤ 2^(descriptorBill k J*n) := by
  classical
  let b := Nat.clog 2 (2*3^(k+1))
  have ha : 2*3^(k+1) ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hr : R ≤ 2*J*n := hR.trans (by nlinarith [Nat.mul_le_mul_left J (by omega : n+1 ≤ n+n)])
  calc
    (F.image σ).card ≤ Fintype.card (Fin R → Native.Descriptor k) := card_le_univ _
    _ = (2*3^(k+1))^R := by rw [Fintype.card_fun,Fintype.card_fin,Native.card_descriptor]
    _ ≤ (2^b)^R := Nat.pow_le_pow_left ha _
    _ = 2^(b*R) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      simpa [descriptorBill,b,Nat.mul_assoc] using Nat.mul_le_mul_left b hr)

/-- One attained common descriptor has a genuine frozen packet class paying
only the schedule bill beyond whatever was lost on the raw-input slice. -/
theorem exists_paid_class {M : Transpose.TM} {c C : ℝ} {s β J d a r : ℕ}
    (hc : Compiles M c s β J C) (hd : 0 < d) (ha : 0 < a) (hr : r < s) (z : Raw d r)
    (hne : (payloadFibre (a := a) (s := s) (successfulInputsAt M c d (a*s+r)) z).Nonempty) :
    ∃ W : PacketClass M.k s β d a, (W.time : ℝ) ≤ C*((d*d*a : ℕ) + 1) ∧
      (payloadFibre (a := a) (s := s) (successfulInputsAt M c d (a*s+r)) z).card ≤
        2^(descriptorBill M.k J*(d*d*a))*W.words.card := by
  classical
  let F := payloadFibre (a := a) (s := s) (successfulInputsAt M c d (a*s+r)) z
  obtain ⟨R,hR,σ,hσ⟩ := hc d a r ha hr z
  obtain ⟨y,hy,hpop⟩ := exists_large_observation_fibre hne σ
  obtain ⟨W,hT,hW⟩ := hσ y hy
  have hn : 0 < d*d*a := by positivity
  exact ⟨W,hT,hpop.trans (Nat.mul_le_mul (attained_support_le F σ hn hR) (card_le_card hW))⟩

end TapeStorageRates.PaidClasses

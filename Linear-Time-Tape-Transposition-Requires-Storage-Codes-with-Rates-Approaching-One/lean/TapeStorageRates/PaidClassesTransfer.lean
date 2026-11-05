import TapeStorageRates.PaidClasses
import TapeStorageRates.PaidInputsLimits

/-! # Paid packet populations on arbitrary cofinally growing widths -/

namespace TapeStorageRates.PaidClasses

open Finset Filter PaidInputs DirectedRecovery
open scoped Topology

set_option autoImplicit false

/-- A raw input deficit of E bits per complete packet survives fixing one tail and then
costs exactly E extra bits per packet in the schedule budget. -/
theorem hasPacketClasses_of_paid_widths {M : Transpose.TM} {c C : ℝ} {s β J : ℕ} (hs : 0 < s)
    (hc : Compiles M c s β J C) (E : ℕ)
    (hM : ∀ n, ∃ d ≥ n, ∃ b ≥ s, (successfulInputsAt M c d b).Nonempty ∧
      ((d*d*b : ℕ) : ℝ) - Real.logb 2 (successfulInputsAt M c d b).card ≤ (E*(d*d*(b/s)) : ℕ)) :
    HasPacketClasses M.k s β (descriptorBill M.k J + E) C := by
  intro d₀
  obtain ⟨d,hd,b,hb,hG,hraw⟩ := hM (max d₀ 1)
  let a := b/s
  let r := b%s
  let n := d*d*a
  have ha : 0 < a := Nat.div_pos hb hs
  have hwidth : a*s+r = b := Nat.div_add_mod' _ _
  let G := successfulInputsAt M c d (a*s+r)
  have hG' : G.Nonempty := by dsimp only [G]; rw [hwidth]; exact hG
  obtain ⟨z,hz,hdef⟩ := exists_payload_deficit_le (a := a) (s := s) (r := r) G hG'
  obtain ⟨W,hT,hword⟩ := exists_paid_class hc (by omega : 0<d) ha (Nat.mod_lt _ hs) z hz
  let F := payloadFibre (a := a) (s := s) G z
  have hF : 0 < (F.card : ℝ) := by exact_mod_cast hz.card_pos
  have hbits : ((n*s : ℕ):ℝ) - Real.logb 2 F.card ≤ (E*n : ℕ) :=
    hdef.trans (by dsimp only [G]; rw [hwidth]; exact hraw)
  have hpow : (2:ℝ)^((s*n : ℕ):ℝ) ≤ (2:ℝ)^((E*n : ℕ)+Real.logb 2 F.card) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mpr (by
      rw [Nat.mul_comm s n]; linarith only [hbits])
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_logb (by norm_num) (by norm_num) hF] at hpow
  have hpay : 2^(s*n) ≤ 2^(E*n)*F.card := by exact_mod_cast hpow
  refine ⟨d,(le_max_left _ _).trans hd,a,ha,W,hT,?_⟩
  calc
    _ ≤ 2^(E*n) * (2^(descriptorBill M.k J*n)*W.words.card) :=
      hpay.trans (Nat.mul_le_mul_left _ hword)
    _ = _ := by rw [← Nat.mul_assoc, ← pow_add]; congr 2; ring

/-- Full success at arbitrarily large canonical dimensions pays no raw deficit. -/
theorem hasPacketClasses_of_full {M : Transpose.TM} {c C : ℝ} {s β J : ℕ} (hs : 0 < s)
    (hc : Compiles M c s β J C)
    (hM : ∀ d₀, ∃ d ≥ d₀, MergeDepth.TransposesAt M d c) :
    HasPacketClasses M.k s β (descriptorBill M.k J) C := by
  apply hasPacketClasses_of_paid_widths hs hc 0
  intro n
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (tendsto_entryBits.eventually_ge_atTop s)
  obtain ⟨d,hd,h⟩ := hM (max d₀ n)
  refine ⟨d,(le_max_right _ _).trans hd,_,hd₀ _ ((le_max_left _ _).trans hd),?_⟩
  rw [successfulInputsAt_eq_univ h]
  simp [Raw,Real.logb_pow]

/-- Near-full success at jointly growing dimensions and widths pays at most one
extra bit per packet. This also applies when the successful widths are noncanonical. -/
theorem hasPacketClasses_of_growing_widths {M : Transpose.TM} {c C : ℝ} {s β J : ℕ} (hs : 0 < s)
    (hc : Compiles M c s β J C) (hM : GrowingWidthSuccess M c) :
    HasPacketClasses M.k s β (descriptorBill M.k J + 1) C := by
  apply hasPacketClasses_of_paid_widths hs hc 1
  intro n
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  obtain ⟨d,hd,b,hb,hG,hρ⟩ := hM (max n s) (1/(2*s)) (by positivity)
  refine ⟨d,(le_max_left _ _).trans hd,b,(le_max_right _ _).trans hb,hG,?_⟩
  let L := d*d*b
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega : 0<d) (by omega)) (by omega : 0<b)
  have hrate : (1-1/(2*(s:ℝ)))*L ≤ Real.logb 2 (successfulInputsAt M c d b).card :=
    (le_div_iff₀ hL).mp (by simpa only [storageCodeRate,Raw,Fintype.card_fin,Fintype.card_bool,
      Nat.cast_ofNat,L] using hρ)
  have ha : 0 < b/s := Nat.div_pos (by omega) hs
  have hrem : b%s ≤ (b/s)*s := (Nat.mod_lt _ hs).le.trans (Nat.le_mul_of_pos_left s ha)
  have hw := Nat.div_add_mod' b s
  have hsz : L ≤ 2*(d*d*(b/s))*s := by
    dsimp [L]
    nlinarith only [Nat.mul_le_mul_left (d*d) hrem,congrArg (d*d*·) hw]
  have hp : (L:ℝ)/(2*s) ≤ (d*d*(b/s) : ℕ) :=
    (div_le_iff₀ (by positivity)).mpr (by exact_mod_cast (by nlinarith only [hsz] : L ≤ d*d*(b/s)*(2*s)))
  rw [sub_mul,one_mul,one_div_mul_eq_div] at hrate
  simpa only [one_mul] using (by linarith only [hrate,hp] :
    (L:ℝ)-Real.logb 2 (successfulInputsAt M c d b).card ≤ (d*d*(b/s) : ℕ))

end TapeStorageRates.PaidClasses

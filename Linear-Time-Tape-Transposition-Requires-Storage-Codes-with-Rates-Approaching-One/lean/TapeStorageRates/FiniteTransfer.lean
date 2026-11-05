import TapeStorageRates.FrozenPackets
import TapeStorageRates.PacketExpansion

/-! # A finite binary code from one causal packet schedule -/

namespace TapeStorageRates

open Finset DirectedRecovery MergeDepth BoundedNesting MotionDepthCodes

set_option autoImplicit false

/-- The maximum number of input packets in a depth-D cone. -/
def packetFan (k D : ℕ) : ℕ := ∑ h ∈ range (D + 1), (k + 1) ^ h

/-- Paper 11's explicit short-pair constant at packet scale one. -/
noncomputable def shortPairCost (k B θ r : ℕ) (c : ℝ) : ℝ :=
  pathPackingConstant r (max B θ)
    (fun j => 2 * j * c * B * (k + 2) * ((k + 2 : ℕ) + 1) + 3)

/-- Convert the separate spatial and distance trim bounds into one loss on the
original coordinates. Both native bit cuts and packet cuts use this count. -/
theorem packet_trim_retention {k d b θ r B : ℕ} {c : ℝ}
    {Q : Finset (Fin (d*d*b))} {U : Finset Q}
    (hheavy : Qᶜ.card * (θ+1) ≤ B*(d*d*b))
    (hshort : (Uᶜ.card : ℝ) ≤ pathPackingConstant r (max B θ)
      (fun j => 2*j*c*B*(k+2)*((k+2 : ℕ)+1)+3) * ((d : ℝ)^2*b / Real.logb 2 d)) :
    ((d*d*b : ℕ) : ℝ) ≤ U.card + (B : ℝ)*(d*d*b : ℕ)/(θ+1) +
      shortPairCost k B θ r c * ((d*d*b : ℕ) / Real.logb 2 d) := by
  have hQ := card_add_card_compl Q
  have hU := card_add_card_compl U
  simp only [Fintype.card_fin, Fintype.card_coe] at hQ hU
  have heq : (Qᶜ.card : ℝ) + Uᶜ.card + U.card = (d*d*b : ℕ) := by
    exact_mod_cast (by omega : Qᶜ.card + Uᶜ.card + U.card = d*d*b)
  have heavy : (Qᶜ.card : ℝ) ≤ (B : ℝ)*(d*d*b : ℕ)/(θ+1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < θ+1)).mpr
    exact_mod_cast hheavy
  have short : (Uᶜ.card : ℝ) ≤ shortPairCost k B θ r c * ((d*d*b : ℕ) / Real.logb 2 d) := by
    simpa only [shortPairCost, pow_two, Nat.cast_mul] using hshort
  linarith

/-- Any loss strictly above the heavy-degree fraction pays for all short pairs once
the logarithm y of the dimension is sufficiently large. -/
theorem retained_fraction_of_trim {θ : ℕ} {B L m K y loss : ℝ}
    (hL : 0 ≤ L) (hy : 0 < y) (hsmall : K ≤ (loss - B/((θ:ℝ)+1))*y)
    (htrim : L ≤ m + B*L/((θ:ℝ)+1) + K*(L/y)) :
    (1-loss)*L ≤ m := by
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hy).mpr hsmall) hL
  rw [show B*L/((θ:ℝ)+1) = (B/((θ:ℝ)+1))*L by ring,
    show K*(L/y) = (K/y)*L by ring] at htrim
  linarith only [htrim, h]

open Classical in
/-- Choosing a genie, trimming both kinds of bad coordinates, fixing their joint values, and
expanding packets give an actual binary code. Time is measured in packets. The input set
can be any nonempty set of correctly computed words on a common schedule. -/
theorem finite_packet_code {k d b T s β : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {Bval : Type*} [Fintype Bval] (hβ : 1 ≤ β) (hwidth : Fintype.card Bval ≤ 2 ^ β)
    {S : Finset (Fin (d*d*b) → Fin s → Bool)} (hne : S.Nonempty)
    (z : Tp k → ℕ → ℤ) (hz : ∀ j, IsWalk (z j))
    {val : (Fin (d*d*b) → Fin s → Bool) → ℕ → Bval} (hloc : PacketLocal z T S val)
    (ot : ℕ → ℕ)
    (hot : ∀ q : Fin (d*d*b), ot (tpos d b q) < T ∧ (tpos d b q : ℤ) = z (some none) (ot (tpos d b q)))
    (houtput : ∀ x ∈ S, ∀ y ∈ S, ∀ q : Fin (d*d*b),
      val x (ot (tpos d b q)) = val y (ot (tpos d b q)) → x q = y q)
    {c : ℝ} (hc : 1 ≤ c) (htime : (T : ℝ) ≤ c * (d*d*b + 1))
    (θ r : ℕ) :
    let n := d*d*b
    let B := packetFan k (BoundedStackDepth.genieDepth k β c 1)
    ∃ (m : ℕ) (R : Fin (m*s) → Finset (Fin (m*s))) (C : Finset (Fin (m*s) → Bool)),
      m ≤ n ∧ (n : ℝ) ≤ m + (B : ℝ) * n / (θ + 1) + shortPairCost k B θ r c * (n / Real.logb 2 d) ∧
      C.Nonempty ∧ IsStorageCode R C ∧
      S.card ≤ 2 ^ (n + s * (n - m)) * C.card ∧
      (∀ v, (pairedIncidenceGraph R).degree v ≤ s * max B θ) ∧
      ∀ q, ¬ (pairedIncidenceGraph R).edist (Sum.inl q) (Sum.inr q) ≤ r := by
  intro n B
  have hn : 1 ≤ n := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  obtain ⟨Γ, F, _, hFne, hF, hg, hcard, hdepth⟩ := hloc.paid_cone_code hne hβ hwidth hn hc
    (show (0 : ℝ) < 1 by norm_num) (by simpa only [Nat.cast_mul] using htime) (fun j => hz (some (some j))) ot (tpos d b)
    (fun q => (hot q).1) houtput
  obtain ⟨Q, U, hheavy, hshort, hdeg, hfar⟩ := packet_schedule_trim hd hb z hz Γ ot
    (fun π hp hf => (hdepth π hp hf).trans (Nat.le_succ _)) hot (zero_le_one.trans hc) htime θ r
  obtain ⟨x, hx, hxcode, h1⟩ := exists_large_conditioned_code hF hFne Q
  obtain ⟨y, hy, hycode, h2⟩ := exists_large_conditioned_code hxcode hx U
  obtain ⟨R, C, hC, hCcard, hR, hdist⟩ :=
    exists_fin_binary_expansion (Function.Embedding.refl (Fin s → Bool)) hycode hdeg hfar
  have hU : U.card ≤ Q.card := by simpa using U.card_le_univ
  have hQ : Q.card ≤ n := by simpa [n] using Q.card_le_univ
  have htotal : Qᶜ.card + Uᶜ.card = n - U.card := by
    simp only [card_compl, Fintype.card_fin, Fintype.card_coe]
    dsimp [n] at hQ ⊢
    omega
  have hg' : β * Γ.card ≤ n := by exact_mod_cast (show (β * Γ.card : ℝ) ≤ n by simpa [n] using hg)
  refine ⟨Fintype.card U, R, C, by simpa using hU.trans hQ, ?_, ?_, hC, ?_, hR, hdist⟩
  · simpa only [Fintype.card_coe,B,n,packetFan] using packet_trim_retention hheavy hshort
  · exact card_pos.mp (hCcard.symm ▸ hy.card_pos)
  · have hcount := hcard.trans (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2)))
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcount
    rw [hCcard, Fintype.card_coe]
    simp only [← pow_mul, ← Nat.mul_assoc, ← pow_add] at hcount
    apply hcount.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) ?_))
    rw [← htotal, Nat.mul_add]
    omega

end TapeStorageRates

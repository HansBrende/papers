import TapeStorageRates.NativeTypical
import TapeStorageRates.NativeTypicalDegree
import TapeStorageRates.NativeTypicalResources
import TapeStorageRates.NativeJointPartition

/-! # Typical high-rate codes on induced physical bit cones

The machine, cap, and simulator are fixed before the distance test and dimension. Every
positive entry width is allowed. At full success the only rate loss is the native degree
envelope; an arbitrary successful subensemble pays its own logarithmic deficit. -/

namespace TapeStorageRates

open Filter Finset Transpose MergeDepth DirectedRecovery

set_option autoImplicit false
noncomputable section

namespace NativeTypicalPartition

variable {M : TM} {d b Δ r D : ℕ} {c ε : ℝ} {G : Finset (Fin (d*d*b) → Bool)}
variable (P : NativeTypicalPartition M d b c ε Δ r G D)

open Classical in
/-- The fraction of inputs in G whose own projected code has rate strictly below ρ. -/
def lowRateProbability (ρ : ℝ) : ℝ :=
  (((univ : Finset G).filter fun x => storageCodeRate (P.code x) < ρ).card : ℝ) / G.card

/-- Convert an absolute deficit tail to a rate tail using each cell's actual size.
A nonpositive rate threshold contributes an empty event. -/
theorem lowRateProbability_le_badProbability {ρ bill : ℝ}
    (hpos : ∀ x : G, 0 < (P.cut x).U.card)
    (hbudget : ∀ x : G, 0 < ρ → ρ*(P.cut x).U.card ≤ (P.cut x).U.card - bill) :
    P.lowRateProbability ρ ≤ P.badProbability bill := by
  classical
  apply div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_)) (Nat.cast_nonneg _)
  intro x hx
  have h := (mem_filter.mp hx).2
  simp only [storageCodeRate,Fintype.card_bool,Nat.cast_ofNat,Fintype.card_coe] at h
  have hm : 0 < ((P.cut x).U.card : ℝ) := by exact_mod_cast hpos x
  have hcard : 1 ≤ ((P.code x).card : ℝ) := by
    exact_mod_cast (show (P.code x).Nonempty from ⟨_,P.projected_mem x⟩).card_pos
  have hρ := (div_nonneg (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hcard) hm.le).trans_lt h
  exact mem_filter.mpr ⟨mem_univ _, by
    change bill < ((P.cut x).U.card : ℝ) - Real.logb 2 (P.code x).card
    linarith only [(div_lt_iff₀ hm).mp h, hbudget x hρ]⟩

/-- A two-sided cap and an explicit bound on the fraction of omitted native bit positions.
The partition also supplies the true append roots and the paired-distance certificate. -/
def coversAtCap : Prop :=
  packetFan M.k D ≤ Δ ∧
    ∀ x : G, (1-nativeFanBound Δ/(Δ:ℝ))*((d*d*b : ℕ):ℝ) ≤ (P.cut x).U.card

end NativeTypicalPartition

/-- One partition witnesses both coordinate coverage and the fraction of inputs below ρ. -/
def HasTypicalNativeRate (N : TM) (d b Δ r : ℕ) (C ε : ℝ) (G : Finset (Fin (d*d*b) → Bool))
    (ρ failure : ℝ) : Prop :=
  ∃ D : ℕ, ∃ P : NativeTypicalPartition N d b C ε Δ r G D, P.coversAtCap ∧ P.lowRateProbability ρ ≤ failure

/-- At a fixed cap, radius, dimension and success set, one partition works at *every*
excess loss u. The rate baseline is the log-cardinality rate of the successful inputs
themselves. Its coefficient is one, even for exponentially sparse success sets. -/
theorem typical_native_rate_tail (M : TM) {c : ℝ} (hc : 0 ≤ c) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, ∃ hs : 0 < s,
      1 / (s:ℝ) ≤ K * inverseDegreeScale (4*M.k^2+1) Δ ∧
      inverseDegreeScale (4*M.k^2+1) Δ ≤ 1 / s ∧
      ∀ r : ℕ, ∀ᶠ d : ℕ in atTop, ∀ b : ℕ, 1 ≤ b →
        ∀ G : Finset (Fin (d*d*b) → Bool), G.Nonempty →
          (∀ x ∈ G, TransposesInput M d b c x) →
          let L : ℝ := (d*d*b : ℕ)
          ∃ P : NativeTypicalPartition (Native.machine M hs) d b (11*c+1) (1/(s:ℝ)) Δ r G
              (jointPhysicalDepth M.k (nativeJointCoefficient M c) s),
            P.coversAtCap ∧ ∀ u : ℝ, P.lowRateProbability
              (Real.logb 2 G.card/L - A*inverseDegreeScale (4*M.k^2+1) Δ - u) ≤
              (2:ℝ)^(-u*L) := by
  let C := 11*c+1
  let a := (2*c+1) * Real.logb 2 (1+2*3^(M.k+1) : ℕ)
  have ha : 0 ≤ a := mul_nonneg (by linarith) (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.le_add_right 1 _))
  obtain ⟨K,hK,hbatch⟩ := native_batch_size_for_cap M.k (nativeJointCoefficient M c) (nativeJointCoefficient_pos M c)
  refine ⟨K,(a+2)*K,hK,by positivity,?_⟩
  filter_upwards [hbatch,eventually_ge_atTop 4,
    nativeFanBound_eventually_le_power (a := 1/2) (by norm_num)] with Δ hb hdg hbound
  obtain ⟨s,hs,hfan,hspread,hsmall⟩ := hb
  refine ⟨s,hs,hspread,hsmall,fun r => ?_⟩
  let ε := 1/(s:ℝ)
  let D := jointPhysicalDepth M.k (nativeJointCoefficient M c) s
  let B := packetFan M.k D
  let loss := nativeFanBound Δ / (Δ:ℝ)
  have hΔ : 0 < (Δ:ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have hsB : ((max s B : ℕ):ℝ) ≤ nativeFanBound Δ := by
    exact hfan
  have hB : (B:ℝ) ≤ nativeFanBound Δ := (Nat.cast_le.mpr (le_max_right s B)).trans hsB
  have hs' : (s:ℝ) ≤ nativeFanBound Δ := (Nat.cast_le.mpr (le_max_left s B)).trans hsB
  rw [← Real.sqrt_eq_rpow] at hbound
  have hsq := Real.sq_sqrt hΔ.le
  have hroot : 2 ≤ Real.sqrt (Δ:ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hdg : (2:ℝ)^2 ≤ Δ)
  have hBle : B ≤ Δ := by
    exact_mod_cast (show (B:ℝ) ≤ Δ by nlinarith only [hB,hbound,hsq,sq_nonneg (Real.sqrt Δ-1),hroot])
  have hpay : loss ≤ 1/(s:ℝ) := (div_le_div_iff₀ hΔ hsR).mpr (by
    have h := mul_le_mul hbound (hs'.trans hbound) hsR.le (Real.sqrt_nonneg _)
    linarith only [h, Real.mul_self_sqrt hΔ.le])
  have hlt : loss < 1 := (div_lt_one hΔ).mpr (by
    nlinarith only [hbound,hsq,mul_nonneg (sub_nonneg.mpr hroot) (Real.sqrt_nonneg (Δ:ℝ)),hroot])
  have hslack : 0 < loss - (B:ℝ)/((Δ:ℝ)+1) := by
    apply sub_pos.mpr
    exact (div_le_div_of_nonneg_right hB (by positivity)).trans_lt <|
      div_lt_div_of_pos_left (hsR.trans_le hs') hΔ (by linarith)
  let J := shortPairCost M.k B Δ r C
  have ht : Tendsto (fun d : ℕ => Real.logb 2 (d:ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (11*s+2),
    ht.eventually_ge_atTop (J / (loss-(B:ℝ)/((Δ:ℝ)+1)))] with d hd hj
  intro b hb G hG hgood L
  have hd2 : 2 ≤ d := by omega
  have hdL : d ≤ d*d*b := (Nat.le_mul_self d).trans (Nat.le_mul_of_pos_right _ hb)
  have hL : 0 < L := by change 0 < ((d*d*b:ℕ):ℝ); exact_mod_cast (by omega : 0 < d*d*b)
  have hy : 0 < Real.logb 2 (d:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hd2)
  obtain ⟨_,htr⟩ := native_success_resources M hs hc (show 11*s+1 ≤ d*d*b+1 by omega) G hgood
  obtain ⟨P⟩ := native_joint_typical_partition M hs hc hd2 hb
    (show 11*s+1 ≤ d*d*b+1 by omega) G hgood Δ r
  have hret (x : G) : (1-loss)*L ≤ (P.cut x).U.card :=
    retained_fraction_of_trim (θ := Δ) hL.le hy
      (by simpa only [J,C,mul_comm] using (div_le_iff₀ hslack).mp hj) (P.cut x).retention
  refine ⟨P,⟨hBle,hret⟩,fun u => ?_⟩
  let bill := L-Real.logb 2 G.card+(a+1)*L/s+u*L
  apply (P.lowRateProbability_le_badProbability (bill := bill) (fun x => by
    exact_mod_cast (mul_pos (sub_pos.mpr hlt) hL).trans_le (hret x)) ?_).trans
  · have htail := P.tail hG (h := a*L/s) htr (u*L)
    convert htail using 1 <;> congr 1 <;> dsimp only [bill,ε,L] <;> ring
  · intro x hρ
    have hm : ((P.cut x).U.card : ℝ) ≤ L := by
      change ((P.cut x).U.card : ℝ) ≤ ((d*d*b : ℕ):ℝ)
      exact_mod_cast ((P.cut x).U.card_le_univ.trans_eq (Fintype.card_coe _)).trans
        ((P.cut x).Q.card_le_univ.trans_eq (Fintype.card_fin _))
    have hsCost := mul_le_mul_of_nonneg_left hspread (show 0 ≤ a+2 by linarith)
    have hcharge : loss + (a+1)/s ≤ (a+2)*K*inverseDegreeScale (4*M.k^2+1) Δ := by
      calc
        _ ≤ 1/(s:ℝ) + (a+1)/s := add_le_add hpay le_rfl
        _ = (a+2)*(1/s) := by ring
        _ ≤ _ := hsCost.trans_eq (by ring)
    have htotal := mul_le_mul_of_nonneg_right hcharge hL.le
    dsimp only [bill]
    have hlog : Real.logb 2 G.card / L * L = Real.logb 2 G.card := div_mul_cancel₀ _ hL.ne'
    have hrate := mul_le_mul_of_nonneg_left hm hρ.le
    apply hrate.trans
    rw [sub_mul,sub_mul,hlog]
    have hkeep := hret x
    rw [sub_mul,one_mul] at hkeep
    rw [add_mul,show (a+1)/(s:ℝ)*L = (a+1)*L/s by ring] at htotal
    linarith only [hkeep,htotal]

/-- Spending one more bit per batch gives an exceptional input fraction at most 2^(-L/s).
The retained proportion and the leading success-set rate are both explicit. -/
theorem typical_native_rates (M : TM) {c : ℝ} (hc : 0 < c) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, ∃ hs : 0 < s,
      1 / (s:ℝ) ≤ K * inverseDegreeScale (4*M.k^2+1) Δ ∧
      inverseDegreeScale (4*M.k^2+1) Δ ≤ 1 / s ∧
      ∀ r : ℕ, ∀ᶠ d : ℕ in atTop, ∀ b : ℕ, 1 ≤ b →
        ∀ G : Finset (Fin (d*d*b) → Bool), G.Nonempty →
          (∀ x ∈ G, TransposesInput M d b c x) →
          let L : ℝ := (d*d*b : ℕ)
          HasTypicalNativeRate (Native.machine M hs) d b Δ r (11*c+1) (1/(s:ℝ)) G
            (Real.logb 2 G.card / L - A*inverseDegreeScale (4*M.k^2+1) Δ)
            ((2:ℝ)^(-L/s)) := by
  obtain ⟨K,A,hK,hA,he⟩ := typical_native_rate_tail M hc.le
  refine ⟨K,A+K,hK,by positivity,he.mono fun Δ h => ?_⟩
  obtain ⟨s,hs,hspread,hsmall,h⟩ := h
  refine ⟨s,hs,hspread,hsmall,fun r => (h r).mono fun d hd b hb G hG hgood => ?_⟩
  obtain ⟨P,hP,ht⟩ := hd b hb G hG hgood
  refine ⟨_,P,hP,?_⟩
  have hbound := ht (K*inverseDegreeScale (4*M.k^2+1) Δ)
  rw [add_mul,sub_add_eq_sub_sub]
  apply hbound.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ?_)
  have h := mul_le_mul_of_nonneg_right hspread (Nat.cast_nonneg (d*d*b) (α := ℝ))
  convert neg_le_neg h using 1 <;> ring

/-- Full-cube form. At large successful dimensions the rate loss on typical raw inputs
has the native exponent, with no correctness-set deficit to pay. -/
theorem typical_native_rates_full (M : TM) {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, ∃ hs : 0 < s,
      ∀ r : ℕ, ∀ᶠ d : ℕ in atTop, ∀ b : ℕ, 1 ≤ b → TransposesAtWidth M d b c →
        HasTypicalNativeRate (Native.machine M hs) d b Δ r (11*c+1) (1/(s:ℝ)) univ
          (1-A*inverseDegreeScale (4*M.k^2+1) Δ)
          ((2:ℝ)^(-((d*d*b : ℕ):ℝ)/s)) := by
  obtain ⟨_,A,_,hA,he⟩ := typical_native_rates M hc
  refine ⟨A,hA,he.mono fun Δ h => ?_⟩
  obtain ⟨s,hs,_,_,hall⟩ := h
  refine ⟨s,hs,fun r => ((hall r).and (eventually_ge_atTop 1)).mono fun d ⟨hd,hd1⟩ b hb hgood => ?_⟩
  have h := hd b hb univ univ_nonempty (fun x _ => hgood.transposesInput x)
  have hL : d*d*b ≠ 0 := (Nat.mul_pos (Nat.mul_pos hd1 hd1) hb).ne'
  simpa only [card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,
    Nat.cast_ofNat,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one,div_self (Nat.cast_ne_zero.mpr hL : ((d*d*b:ℕ):ℝ) ≠ 0)] using h

end
end TapeStorageRates

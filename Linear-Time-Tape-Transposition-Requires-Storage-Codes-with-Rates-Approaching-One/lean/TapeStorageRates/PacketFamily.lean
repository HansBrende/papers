import TapeStorageRates.FiniteTransfer
import TapeStorageRates.DegreeGenie

/-! # Unbounded packet computations give families with growing minimum distance -/

namespace TapeStorageRates

open Finset DirectedRecovery MergeDepth BoundedNesting MotionDepthCodes Filter
open scoped Topology

set_option autoImplicit false

private theorem rate_of_paid_card {m n s A : ℕ} {keep : ℝ} {C : Finset (Fin (m*s) → Bool)}
    (hm : m ≤ n) (hm0 : 0 < m) (hs : 0 < s) (hk : 0 < keep) (hn : keep*n ≤ m) (hne : C.Nonempty)
    (hcount : 2 ^ (s*n) ≤ 2 ^ (A*n) * (2 ^ (n+s*(n-m)) * C.card)) :
    1 - ((A : ℝ)+1)/(keep*s) ≤ storageCodeRate C := by
  have hC : 0 < (C.card : ℝ) := by exact_mod_cast hne.card_pos
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (show 0 < (2 : ℝ)^(s*n) by positivity)
    (show (2 : ℝ)^(s*n) ≤ 2^(A*n)*(2^(n+s*(n-m))*C.card) by exact_mod_cast hcount)
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hC.ne'] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_mul,
    Nat.cast_add, Nat.cast_sub hm] at hlog
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hdef : (m : ℝ)*s - Real.logb 2 C.card ≤ ((A:ℝ)+1)*n := by linarith only [hlog]
  have hcost := mul_le_mul_of_nonneg_left hn (show 0 ≤ (A:ℝ)+1 by positivity)
  simp only [storageCodeRate,Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat,Nat.cast_mul]
  apply (le_div_iff₀ (mul_pos hm' hs')).mpr
  field_simp [hk.ne',hs'.ne']
  nlinarith only [mul_le_mul_of_nonneg_left hdef hk.le,hcost]

open Classical in
/-- At every sufficiently large dimension, *each* timely packet class of the stated
population yields a separated code on at least the specified fraction of its original
packet count. The dimension threshold is uniform over entry widths and such classes. -/
theorem packet_code_at_threshold {k s β A : ℕ} (hs : 1 ≤ s) (hβ : 1 ≤ β)
    {c : ℝ} (hc : 1 ≤ c) (θ r : ℕ) {keep : ℝ} (hk : 0 < keep)
    (hslack : (packetFan k (BoundedStackDepth.genieDepth k β c 1) : ℝ) / (θ+1) < 1-keep) :
    ∀ᶠ d : ℕ in atTop, ∀ b : ℕ, 1 ≤ b → ∀ W : PacketClass k s β d b,
      (W.time : ℝ) ≤ c*((d*d*b : ℕ)+1) →
      2^(s*(d*d*b)) ≤ 2^(A*(d*d*b))*W.words.card →
      ∃ m ≤ d*d*b, keep*(d*d*b : ℕ) ≤ m ∧
        ∃ (N : Fin (m*s) → Finset (Fin (m*s))) (C : Finset (Fin (m*s) → Bool)),
          C.Nonempty ∧ IsStorageCode N C ∧
          (∀ v, (pairedIncidenceGraph N).degree v ≤ s*max (packetFan k (BoundedStackDepth.genieDepth k β c 1)) θ) ∧
          (∀ q, ¬ (pairedIncidenceGraph N).edist (Sum.inl q) (Sum.inr q) ≤ r) ∧
          1-((A : ℝ)+1)/(keep*s) ≤ storageCodeRate C := by
  let B := packetFan k (BoundedStackDepth.genieDepth k β c 1)
  let K := shortPairCost k B θ r c
  have hmargin : 0 < (1-keep)-(B:ℝ)/(θ+1) := sub_pos.mpr hslack
  have ht := (Real.tendsto_logb_atTop (show (1:ℝ)<2 by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,ht.eventually_ge_atTop (K/((1-keep)-B/(θ+1)))] with d hd hbig
  intro b hb W htime hcost
  obtain ⟨m,N,C,hm,htrim,hne,hC,hcharge,hdeg,hfar⟩ := finite_packet_code hd hb hβ
    (by simp : Fintype.card (Fin (2^β)) ≤ 2^β) W.nonempty W.walks W.unit_walk W.local_record
    W.outputTime W.outputPosition W.outputDetermined hc (by simpa only [Nat.cast_mul] using htime) θ r
  have hl : 0 < Real.logb 2 (d:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hd)
  have hret : keep*(d*d*b : ℕ) ≤ m := by
    simpa only [sub_sub_cancel] using retained_fraction_of_trim (θ := θ) (loss := 1-keep)
      (by positivity : 0 ≤ ((d*d*b : ℕ):ℝ)) hl
      (mul_comm _ (Real.logb 2 d) ▸ (div_le_iff₀ hmargin).mp hbig)
      (by simpa only [Nat.cast_add,Nat.cast_one] using htrim)
  have hn : 0 < d*d*b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  have hm0 : (0:ℝ) < m := (mul_pos hk (by exact_mod_cast hn)).trans_le hret
  exact ⟨m,hm,hret,N,C,hne,hC,hdeg,hfar,rate_of_paid_card hm (by exact_mod_cast hm0) hs hk hret hne
    (hcost.trans (Nat.mul_le_mul_left _ hcharge))⟩

/-- The heavy threshold θ and desired retained fraction can be chosen independently.
At any 0 < keep < 1 - B/(θ+1), the minimum paired distance grows at cap s·max(B,θ)
and each code has rate at least 1-(A+1)/(keep·s). The source dimensions can be required
arbitrarily large before the common-schedule class is selected. -/
theorem family_of_packet_classes_at_threshold {k s β A : ℕ} (hs : 1 ≤ s) (hβ : 1 ≤ β)
    {c : ℝ} (hc : 1 ≤ c) (hclasses : HasPacketClasses k s β A c)
    (θ : ℕ) {keep : ℝ} (hk : 0 < keep)
    (hslack : (packetFan k (BoundedStackDepth.genieDepth k β c 1) : ℝ) / (θ+1) < 1-keep) :
    ∃ F : SeparatedBinaryFamily (s * max (packetFan k (BoundedStackDepth.genieDepth k β c 1)) θ),
      ∀ i, 1 - ((A : ℝ)+1)/(keep*s) ≤ storageCodeRate (F.code i) := by
  classical
  let Δ := s*max (packetFan k (BoundedStackDepth.genieDepth k β c 1)) θ
  have each (r : ℕ) : ∃ ℓ ≥ r+1, ∃ (N : Fin ℓ → Finset (Fin ℓ)) (C : Finset (Fin ℓ → Bool)),
      C.Nonempty ∧ IsStorageCode N C ∧ (∀ v, (pairedIncidenceGraph N).degree v ≤ Δ) ∧
      (∀ q, ¬ (pairedIncidenceGraph N).edist (Sum.inl q) (Sum.inr q) ≤ r) ∧
      1 - ((A:ℝ)+1)/(keep*s) ≤ storageCodeRate C := by
    obtain ⟨d₀,h₀⟩ := eventually_atTop.mp (packet_code_at_threshold (A := A) hs hβ hc θ r hk hslack)
    obtain ⟨d,hd,b,hb,W,htime,hcost⟩ := hclasses (max d₀ ⌈((r:ℝ)+1)/keep⌉₊)
    obtain ⟨m,_,hret,N,C,hne,hC,hdeg,hfar,hrate⟩ := h₀ d ((le_max_left _ _).trans hd) b hb W htime hcost
    have hsize : (r:ℝ)+1 ≤ keep*d := by
      rw [mul_comm]
      exact (div_le_iff₀ hk).mp <| (Nat.le_ceil _).trans <| Nat.cast_le.mpr ((le_max_right _ _).trans hd)
    have hnm : r+1 ≤ m := by
      exact_mod_cast hsize.trans ((mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr ((Nat.le_mul_self d).trans (Nat.le_mul_of_pos_right _ hb))) hk.le).trans hret)
    exact ⟨m*s,hnm.trans (Nat.le_mul_of_pos_right _ hs),N,C,hne,hC,hdeg,hfar,hrate⟩
  choose ℓ hℓ N C hne hC hdeg hfar hrate using each
  refine ⟨{
    length := ℓ
    length_pos := fun i => (Nat.zero_lt_succ i).trans_le (hℓ i)
    length_tendsto := tendsto_atTop.mpr (fun b => (eventually_ge_atTop b).mono (fun i hi => (hi.trans (Nat.le_succ i)).trans (hℓ i)))
    recovery := N
    code := C
    nonempty := hne
    storage := hC
    degree_le := hdeg
    paired_far := fun r => (eventually_ge_atTop r).mono (fun i hi q h =>
      hfar i q (h.trans (by exact_mod_cast hi)))
    }, hrate⟩

/-- At the paper's natural cap, the strict heavy-degree cutoff permits exactly half
the source packet coordinates to be kept even after deleting all short pairs. -/
theorem family_of_packet_classes {k s β A : ℕ} (hs : 1 ≤ s) (hβ : 1 ≤ β)
    {c : ℝ} (hc : 1 ≤ c) (hclasses : HasPacketClasses k s β A c) :
    ∃ F : SeparatedBinaryFamily (packetIncidenceCap k s (BoundedStackDepth.genieDepth k β c 1)),
      ∀ i, 1 - 2 * (A + 1 : ℝ) / s ≤ storageCodeRate (F.code i) := by
  let B := packetFan k (BoundedStackDepth.genieDepth k β c 1)
  have hhalf : (B:ℝ)/((2*B : ℕ)+1) < 1-1/2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    push_cast
    linarith
  obtain ⟨F,hF⟩ := family_of_packet_classes_at_threshold hs hβ hc hclasses (2*B)
    (by norm_num : (0:ℝ)<1/2) hhalf
  have hcap : s*max B (2*B) = packetIncidenceCap k s (BoundedStackDepth.genieDepth k β c 1) := by
    rw [max_eq_right (by omega : B ≤ 2*B)]
    unfold packetIncidenceCap B packetFan
    ring
  refine ⟨F.atCap hcap.le,fun i => ?_⟩
  change 1-2*((A:ℝ)+1)/s ≤ storageCodeRate (F.code i)
  calc
    _ = 1-((A:ℝ)+1)/((1/2)*(s:ℝ)) := by field_simp
    _ ≤ _ := hF i

/-- Apply the rate theorem at every cap once a native construction has supplied the actual
packet classes, with their two uniform resource bounds. All subsequent choices, including the
radius-dependent dimension, are made inside the proof. -/
theorem rates_of_packet_classes (k A b : ℕ) {c : ℝ} (hc : 1 ≤ c) {β : ℕ → ℕ}
    (hβ : ∀ᶠ s in atTop, 1 ≤ β s ∧ β s ≤ b*s)
    (hclass : ∀ᶠ s in atTop, HasPacketClasses k s (β s) A c) :
    RateWitnesses k := by
  apply all_caps_of_packetFamilyBounds
  apply packetFamilyBounds_of_genieFamilies k b (A := 2*((A : ℝ)+1)) hc (by positivity) hβ
  filter_upwards [eventually_ge_atTop 1, hβ, hclass] with s hs hw h
  obtain ⟨F, hr⟩ := family_of_packet_classes hs hw.1 hc h
  refine ⟨F, le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun i =>
    MergeDepth.storageCodeRate_le_one (by simp) (F.code i))) (Eventually.of_forall hr)⟩

end TapeStorageRates

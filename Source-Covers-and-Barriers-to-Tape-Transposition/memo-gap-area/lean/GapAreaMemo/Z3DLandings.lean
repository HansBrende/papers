import GapAreaMemo.Z3DChains

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: landings

The root of column `j` lies in the second rise of bank A's largest zigzag at
relative level `θ = j/d`, and the bank-A chain is exact: zigzag `p` is reached
at level `θ a_p`. The newer exception `g` carries the descent and first-rise
times of zigzag `p` into the second rise of bank B's largest zigzag, at
relative level `1 - o`, where `o = t_p - θ w_p` or `o = t_p - (2-θ) w_p` is an
offset of the covering lemmas. The bank-B chain (with floors) and the older
exception `e` then land in the second rise of `C_q` at relative level within
`1/a_q` of `vdC(q) ± o/4`.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies

variable (P : Index)

/-! ### Arithmetic of the parameters -/

theorem db_eq : P.d * P.b = 2 ^ (P.m + P.ν) := by
  rw [show P.b = 2 ^ P.ν from rfl, show P.d = 2 ^ P.m from rfl, ← pow_add]

theorem lv_eq (c : ℕ) : ∀ k, k + 1 ≤ P.K → lv c k = c / 4 ^ lev (k + 1)
  | 0, _ => by simp [lv, lev]
  | k + 1, hk => by
    rw [lv, lv_eq c k (by omega), Nat.div_div_eq_div_mul]
    congr 1
    unfold fB ratio
    rw [ite_eq_right (by omega), show k + 2 - 1 = k + 1 by omega, ← pow_add]
    congr 1
    have := lev_mono (show k + 1 ≤ k + 1 + 1 by omega)
    omega

theorem a_mul_four_pow {k : ℕ} (hk : k ≤ P.K) : P.a k * 4 ^ lev k = P.a 1 := by
  have he := P.exponent_ok hk
  have h1 : lev 1 = 0 := by simp [lev]
  unfold a
  rw [h1, show (4 : ℕ) ^ lev k = 2 ^ (2 * lev k) by rw [pow_mul]; norm_num, ← pow_add]
  congr 1
  omega

theorem L_eq_a {k : ℕ} (hk : k ≤ P.K) : P.L = 4 * 4 ^ lev k * P.a k := by
  rw [← P.a_one, ← P.a_mul_four_pow hk]; ring

/-- The bank-A level of column `j` at zigzag `p`. -/
def lamA (j p : ℕ) : ℕ := j * 2 ^ (P.m + P.ν - 2 - 2 * lev p)

theorem lv_bankA (j : ℕ) {p : ℕ} (hp1 : 1 ≤ p) (hpK : p ≤ P.K) :
    lv (j * 2 ^ (P.m + P.ν - 2)) (p - 1) = P.lamA j p := by
  rw [P.lv_eq _ _ (by omega), show p - 1 + 1 = p by omega]
  unfold lamA
  have h1 := P.lev_le hpK
  have h2 := P.m_ge
  have hE : P.m + P.ν - 2 = (P.m + P.ν - 2 - 2 * lev p) + 2 * lev p := by omega
  generalize P.m + P.ν - 2 - 2 * lev p = E at hE ⊢
  rw [hE, pow_add, ← mul_assoc, show (4 : ℕ) ^ lev p = 2 ^ (2 * lev p) by rw [pow_mul]; norm_num,
    Nat.mul_div_cancel _ (by positivity)]

theorem lamA_mul_d (j : ℕ) {p : ℕ} (hpK : p ≤ P.K) : P.lamA j p * P.d = j * P.a p := by
  unfold lamA a d n
  have h1 := P.lev_le hpK
  have h2 := P.m_ge
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

theorem lamA_pos {j p : ℕ} (hj : 1 ≤ j) : 0 < P.lamA j p := by
  unfold lamA; positivity

theorem d_pos' : 0 < P.d := pow_pos (by norm_num) _

theorem lamA_lt {j p : ℕ} (hjd : j < P.d) (hpK : p ≤ P.K) : P.lamA j p < P.a p := by
  have h := P.lamA_mul_d j hpK
  have : P.lamA j p * P.d < P.a p * P.d := by
    rw [h, mul_comm (P.a p)]; exact Nat.mul_lt_mul_of_pos_right hjd (P.a_pos p)
  exact Nat.lt_of_mul_lt_mul_right this

theorem OA_sub_σA {k : ℕ} (hk : k ≤ P.K) : P.OA = P.σA k + P.pre k := by
  unfold OA σA pre sumA
  have : Ioc 0 P.K = Ioc 0 k ∪ Ioc k P.K := by
    ext i; simp only [mem_Ioc, mem_union]; omega
  rw [this, sum_union (by rw [disjoint_left]; intro i h1 h2; simp only [mem_Ioc] at h1 h2; omega)]
  ring

theorem w_eq {k : ℕ} (hk : k ≤ P.K) : (P.a k : ℚ) / P.L = Covering.w k := by
  have he := P.exponent_ok hk
  unfold a L Covering.w
  simp only [lev] at he ⊢
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
  congr 1
  omega

theorem pre_div {k : ℕ} (hk : k ≤ P.K) : (P.pre k : ℚ) / P.L = 1 - Covering.t (k + 1) := by
  induction k with
  | zero => simp [P.pre_zero, Covering.t_one]
  | succ k ih =>
    rw [P.pre_succ]
    push_cast
    rw [add_div, ih (by omega), mul_div_assoc, P.w_eq hk]
    have := Covering.t_sub_succ (k := k + 1) (by omega)
    linarith

theorem K_succ : P.K + 1 = 2 ^ (P.ν + 1) := by
  unfold K; have : 1 ≤ 2 ^ (P.ν + 1) := Nat.one_le_two_pow; omega

theorem hg_add_le : P.hg + 2 ≤ P.L := by
  have h := P.pre_div (k := P.K) le_rfl
  rw [P.pre_K, P.K_succ, Covering.t_two_pow] at h
  have hL : (0 : ℚ) < P.L := by exact_mod_cast P.L_pos
  have hq : (P.hg : ℚ) = P.L - P.L / 2 ^ (P.ν + 1) := by
    field_simp at h ⊢; linarith
  have h2 : (2 : ℚ) ≤ P.L / 2 ^ (P.ν + 1) := by
    rw [le_div_iff₀ (by positivity)]
    unfold L
    push_cast
    rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by have := P.m_ge; unfold n; omega)
  have : (P.hg : ℚ) + 2 ≤ P.L := by linarith
  exact_mod_cast this

/-! ### Bank A, the newer exception, bank B and the older exception -/

/-- The root of column `j`: its first output. -/
def root (j : ℕ) : ℕ := P.out (j * (P.d * P.b))

theorem bankA_points (F : Finset (ActualFamily P.heads P.T)) {j p : ℕ} (hj1 : 1 ≤ j)
    (hjd : j < P.d) (hp1 : 1 ≤ p) (hpK : p ≤ P.K)
    (hF : ∀ i, 1 ≤ i → i ≤ p → P.famA i true ∈ F ∧ P.famA i false ∈ F) :
    P.σA p + 2 * P.a p - P.lamA j p ∈ shadowOrbit F (P.root j) ∧
      P.σA p + P.lamA j p ∈ shadowOrbit F (P.root j) := by
  have hσ1 := P.σA_pred (k := 1) le_rfl P.K_pos
  have hdb := P.db_eq
  have hmν : 2 ≤ P.m + P.ν := by have := P.m_ge; omega
  have h4 : 4 * (j * 2 ^ (P.m + P.ν - 2)) = j * (P.d * P.b) := by
    obtain ⟨E, hE⟩ : ∃ E, P.m + P.ν = E + 2 := ⟨P.m + P.ν - 2, by omega⟩
    rw [hdb, hE, show E + 2 - 2 = E by omega, pow_add]; ring
  have hroot : P.root j = P.OA + 1 + j * (P.d * P.b) := rfl
  have hOA : P.OA = P.σA 0 := rfl
  have hc := P.late_chain P.σA (fun k h1 h2 => P.σA_pred h1 h2) (fun k => P.famA k true)
    (fun k => P.famA k false) (fun k h1 h2 => (P.famA_sched h1 h2).1)
    (fun k h1 h2 => (P.famA_sched h1 h2).2) F (P.root j) (j * 2 ^ (P.m + P.ν - 2)) (P.root j)
    (mem_shadowOrbit_self _ _) (by simp only [Nat.sub_self] at hσ1; omega)
    (by simp only [Nat.sub_self] at hσ1; omega) (p - 1) (by omega)
    (fun i hi => hF (i + 1) (by omega) (by omega))
    (fun i hi => by
      have h := P.lv_bankA j (p := i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h
      rw [h]
      exact ⟨P.lamA_pos hj1, P.lamA_lt hjd (by omega)⟩)
  rw [show p - 1 + 1 = p by omega, P.lv_bankA j hp1 hpK] at hc
  exact hc

theorem g_point (F : Finset (ActualFamily P.heads P.T)) (s t : ℕ) (hg : P.gFam ∈ F)
    (ht : t ∈ shadowOrbit F s) (h1 : t < P.OA) (h2 : P.OA - P.hg < t) :
    P.OB + 1 + (P.OA - t) ∈ shadowOrbit F s := by
  have hs := P.g_step (ι := P.OA - t) (by omega) (by omega)
  rw [show P.OA - (P.OA - t) = t by omega] at hs
  have h := shadowOrbit_step ht hg
  rw [hs] at h
  exact h

/-- The bank-B level at zigzag `q` reached from `OB + 1 + ι`. -/
def muB (ι q : ℕ) : ℕ := (1 + ι) / 4 / 4 ^ lev q

theorem bankB_points (F : Finset (ActualFamily P.heads P.T)) (s ι q : ℕ)
    (hι : P.OB + 1 + ι ∈ shadowOrbit F s) (hι1 : 4 ^ (P.ν + 1) ≤ ι) (hι2 : ι + 2 ≤ P.L)
    (hq1 : 1 ≤ q) (hqK : q ≤ P.K)
    (hF : ∀ i, 1 ≤ i → i ≤ q → P.famB i true ∈ F ∧ P.famB i false ∈ F) :
    P.σB q + 2 * P.a q - muB ι q ∈ shadowOrbit F s ∧ P.σB q + muB ι q ∈ shadowOrbit F s ∧
      0 < muB ι q ∧ muB ι q < P.a q := by
  have hσ1 := P.σB_pred (k := 1) le_rfl P.K_pos
  have hOB : P.OB = P.σB 0 := rfl
  have hbounds : ∀ i, 1 ≤ i → i ≤ P.K → 0 < muB ι i ∧ muB ι i < P.a i := by
    intro i hi1 hiK
    have hl := P.lev_le hiK
    have hpow : 4 ^ lev i ≤ 4 ^ P.ν := Nat.pow_le_pow_right (by norm_num) hl
    have hc : 4 ^ P.ν ≤ (1 + ι) / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      rw [pow_succ] at hι1; omega
    have ha := P.a_mul_four_pow hiK
    have ha1 := P.a_one
    unfold muB
    constructor
    · exact Nat.div_pos (hpow.trans hc) (by positivity)
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ha]
      omega
  have hc := P.late_chain P.σB (fun k h1 h2 => P.σB_pred h1 h2) (fun k => P.famB k true)
    (fun k => P.famB k false) (fun k h1 h2 => (P.famB_sched h1 h2).1)
    (fun k h1 h2 => (P.famB_sched h1 h2).2) F s ((1 + ι) / 4) (P.OB + 1 + ι) hι
    (by simp only [Nat.sub_self] at hσ1; omega) (by simp only [Nat.sub_self] at hσ1; omega)
    (q - 1) (by omega) (fun i hi => hF (i + 1) (by omega) (by omega))
    (fun i hi => by
      rw [P.lv_eq _ i (by omega)]
      exact hbounds (i + 1) (by omega) (by omega))
  rw [show q - 1 + 1 = q by omega, P.lv_eq _ (q - 1) (by omega),
    show q - 1 + 1 = q by omega] at hc
  exact ⟨hc.1, hc.2, hbounds q hq1 hqK⟩

theorem e_point (F : Finset (ActualFamily P.heads P.T)) (s q r : ℕ) (he : P.eFam ∈ F)
    (hq1 : 1 ≤ q) (hqK : q ≤ P.K) (hr0 : 0 < r) (hr : r < 2 * P.a q)
    (ht : P.σB q + r ∈ shadowOrbit F s) :
    ∃ v : ℕ, (v : ℤ) = P.landingZ q r ∧ v ∈ shadowOrbit F s := by
  have hpre := P.pre_succ (q - 1)
  rw [Nat.sub_add_cancel hq1] at hpre
  have hpK := P.pre_mono hqK
  rw [P.pre_K] at hpK
  have hOB := P.OB_sub_σB hqK
  have hs := P.e_step (ℓ := P.pre q - r) (by omega) (by omega)
  rw [show P.OB - (P.pre q - r) = P.σB q + r by omega] at hs
  have hv := P.eDepart_eq hq1 hqK (ℓ := P.pre q - r) (by omega) (by omega)
  rw [show P.pre q - (P.pre q - r) = r by omega] at hv
  refine ⟨P.eDepart (P.pre q - r), hv, ?_⟩
  have h := shadowOrbit_step ht he
  rw [hs] at h
  exact h

/-! ### The landing level -/

/-- The covering offset of zigzag `p`: first rise (`true`) or descent (`false`). -/
noncomputable def offs (θ : ℚ) (p : ℕ) (sA : Bool) : ℚ :=
  if sA then Covering.t p - (2 - θ) * Covering.w p else Covering.t p - θ * Covering.w p

/-- The ideal relative landing level in `C_q`. -/
noncomputable def zst (θ : ℚ) (p q : ℕ) (sA sB : Bool) : ℚ :=
  Covering.vdC q + (if sB then 1 else -1) * offs θ p sA / 4

/-- The bank-A time used for the landing. -/
def timeA (j p : ℕ) (sA : Bool) : ℕ :=
  if sA then P.σA p + P.lamA j p else P.σA p + 2 * P.a p - P.lamA j p

/-- Its distance below `OA`. -/
def iotaA (j p : ℕ) (sA : Bool) : ℕ :=
  if sA then P.pre p - P.lamA j p else P.pre (p - 1) + P.lamA j p

theorem iotaA_facts {j p : ℕ} (sA : Bool) (hj1 : 1 ≤ j) (hjd : j < P.d) (hp1 : 1 ≤ p)
    (hpK : p ≤ P.K) :
    P.timeA j p sA + P.iotaA j p sA = P.OA ∧ 0 < P.iotaA j p sA ∧ P.iotaA j p sA < P.hg ∧
      4 ^ (P.ν + 1) ≤ P.iotaA j p sA := by
  have hOA := P.OA_sub_σA hpK
  have hpre := P.pre_succ (p - 1)
  rw [Nat.sub_add_cancel hp1] at hpre
  have hpK' := P.pre_mono hpK
  rw [P.pre_K] at hpK'
  have hl0 := P.lamA_pos (p := p) hj1
  have hl1 := P.lamA_lt hjd hpK
  have hpre1 : P.pre 1 = 2 * P.a 1 := by
    have := P.pre_succ 0; rw [P.pre_zero] at this; simpa using this
  have hmono := P.pre_mono (show 1 ≤ p - 1 + 1 by omega)
  have ha1 := P.a_one
  -- `4^(ν+1) ≤ 2^(m+ν-2) ≤ λ_1` and `≤ a_1`
  have hbig : 4 ^ (P.ν + 1) ≤ 2 ^ (P.m + P.ν - 2) := by
    rw [show (4 : ℕ) ^ (P.ν + 1) = 2 ^ (2 * (P.ν + 1)) by rw [pow_mul]; norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by have := P.m_ge; omega)
  have hbigA : 2 ^ (P.m + P.ν - 2) ≤ P.a 1 := by
    unfold a; simp only [lev, Nat.log_one_right]
    exact Nat.pow_le_pow_right (by norm_num) (by unfold n; omega)
  have hlam1 : 2 ^ (P.m + P.ν - 2) ≤ P.lamA j 1 := by
    unfold lamA; simp only [lev, Nat.log_one_right, mul_zero, Nat.sub_zero]
    exact Nat.le_mul_of_pos_left _ hj1
  cases sA
  · simp only [timeA, iotaA, Bool.false_eq_true, ite_false]
    refine ⟨by omega, by omega, by omega, ?_⟩
    rcases Nat.lt_or_ge p 2 with h | h
    · obtain rfl : p = 1 := by omega
      simp only [Nat.sub_self, P.pre_zero, zero_add]; omega
    · have := P.pre_mono (show 1 ≤ p - 1 by omega); omega
  · simp only [timeA, iotaA, ite_true]
    refine ⟨by omega, by omega, by omega, ?_⟩
    rcases Nat.lt_or_ge p 2 with h | h
    · obtain rfl : p = 1 := by omega
      have := P.lamA_lt (p := 1) hjd P.K_pos
      omega
    · have := P.pre_mono (show 1 ≤ p - 1 by omega); omega

theorem iotaA_div {j p : ℕ} (sA : Bool) (hjd : j < P.d) (hp1 : 1 ≤ p)
    (hpK : p ≤ P.K) :
    (P.iotaA j p sA : ℚ) / P.L = 1 - offs ((j : ℚ) / P.d) p sA := by
  have hd : (0 : ℚ) < P.d := by exact_mod_cast P.d_pos'
  have hL : (0 : ℚ) < P.L := by exact_mod_cast P.L_pos
  have hlam : (P.lamA j p : ℚ) / P.L = (j : ℚ) / P.d * Covering.w p := by
    rw [← P.w_eq hpK]
    have h := P.lamA_mul_d j hpK
    have h' : (P.lamA j p : ℚ) * P.d = j * P.a p := by exact_mod_cast h
    field_simp
    linarith
  have hl1 := P.lamA_lt hjd hpK
  have hpre := P.pre_succ (p - 1)
  rw [Nat.sub_add_cancel hp1] at hpre
  cases sA
  · simp only [iotaA, offs, Bool.false_eq_true, ite_false]
    push_cast
    rw [add_div, hlam, P.pre_div (by omega), Nat.sub_add_cancel hp1]
    ring
  · simp only [iotaA, offs, ite_true]
    rw [Nat.cast_sub (by omega), sub_div, hlam, P.pre_div hpK]
    have := Covering.t_sub_succ hp1
    linarith

theorem muB_bounds (ι q : ℕ) (hqK : q ≤ P.K) :
    (muB ι q : ℚ) / P.a q ≤ (1 + ι) / P.L ∧ (1 + ι) / P.L - 2 / P.a q < (muB ι q : ℚ) / P.a q := by
  have hLe := P.L_eq_a hqK
  have hpow : 0 < 4 ^ lev q := by positivity
  have h1 : 4 * (muB ι q * 4 ^ lev q) ≤ 1 + ι := by
    have := Nat.div_mul_le_self ((1 + ι) / 4) (4 ^ lev q)
    unfold muB; omega
  have h2 : 1 + ι < 4 * 4 ^ lev q * muB ι q + 8 * 4 ^ lev q := by
    have hlt := Nat.lt_mul_div_succ ((1 + ι) / 4) hpow
    have hc : 1 + ι < 4 * ((1 + ι) / 4) + 4 := by omega
    unfold muB
    generalize (1 + ι) / 4 / 4 ^ lev q = μ at hlt ⊢
    generalize (1 + ι) / 4 = c at hlt hc
    generalize 4 ^ lev q = X at hlt hpow ⊢
    nlinarith
  have ha : (0 : ℚ) < P.a q := by exact_mod_cast P.a_pos q
  have hL : (P.L : ℚ) = 4 * 4 ^ lev q * P.a q := by exact_mod_cast hLe
  have h1' : (4 : ℚ) * (muB ι q * 4 ^ lev q) ≤ 1 + ι := by exact_mod_cast h1
  have h2' : (1 : ℚ) + ι < 4 * 4 ^ lev q * muB ι q + 8 * 4 ^ lev q := by exact_mod_cast h2
  have hp : (0 : ℚ) < 4 ^ lev q := by positivity
  constructor
  · rw [div_le_div_iff₀ ha (by rw [hL]; positivity), hL]
    nlinarith
  · have hLpos : (0 : ℚ) < P.L := by rw [hL]; positivity
    have key : (1 + ι) / P.L - 2 / P.a q - (muB ι q : ℚ) / P.a q =
        ((1 + ι) - 8 * 4 ^ lev q - 4 * 4 ^ lev q * muB ι q) / P.L := by
      rw [hL]; field_simp; ring
    have hneg : ((1 : ℚ) + ι) - 8 * 4 ^ lev q - 4 * 4 ^ lev q * muB ι q < 0 := by linarith
    have := div_neg_of_neg_of_pos hneg hLpos
    linarith

theorem landing_error {A L ι μ c4 v : ℚ} (hA : 0 < A) (hLA : 4 * A ≤ L)
    (hμ1 : μ / A ≤ (1 + ι) / L) (hμ2 : (1 + ι) / L - 2 / A < μ / A)
    (hc1 : c4 ≤ 4 * A * v) (hc2 : 4 * A * v < c4 + 1) :
    |(2 * (c4 + A - μ) + 1) / (8 * A) - (v + (1 - ι / L) / 4)| < 1 / A ∧
    |(2 * (c4 - A + μ) + 1) / (8 * A) - (v - (1 - ι / L) / 4)| < 1 / A := by
  have hL : 0 < L := by linarith
  have e1 : (2 * (c4 + A - μ) + 1) / (8 * A) - (v + (1 - ι / L) / 4) =
      (c4 / (4 * A) - v) - (μ / A - ι / L) / 4 + 1 / (8 * A) := by field_simp; ring
  have e2 : (2 * (c4 - A + μ) + 1) / (8 * A) - (v - (1 - ι / L) / 4) =
      (c4 / (4 * A) - v) + (μ / A - ι / L) / 4 + 1 / (8 * A) := by field_simp; ring
  have hC1 : c4 / (4 * A) ≤ v := by rw [div_le_iff₀ (by positivity)]; linarith
  have hC2 : v - 1 / (4 * A) < c4 / (4 * A) := by
    have h : v < (c4 + 1) / (4 * A) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have h' : (c4 + 1) / (4 * A) = c4 / (4 * A) + 1 / (4 * A) := by ring
    linarith
  have hLi : 1 / L ≤ 1 / (4 * A) := one_div_le_one_div_of_le (by positivity) hLA
  have hsplit : (1 + ι) / L = 1 / L + ι / L := by ring
  have hLpos : 0 < 1 / L := by positivity
  have hX1 : μ / A - ι / L ≤ 1 / (4 * A) := by linarith
  have hX2 : -(2 / A) < μ / A - ι / L := by linarith
  have h4 : 1 / (4 * A) = (1 / A) / 4 := by field_simp
  have h8 : 1 / (8 * A) = (1 / A) / 8 := by field_simp
  have h2 : 2 / A = 2 * (1 / A) := by ring
  have hpos : 0 < 1 / A := by positivity
  rw [e1, e2, abs_lt, abs_lt]
  rw [h4] at hC2 hX1
  rw [h2] at hX2
  rw [h8]
  constructor <;> constructor <;> linarith

theorem c4_bounds (q : ℕ) :
    (P.c4 q : ℚ) ≤ 4 * P.a q * Covering.vdC q ∧ 4 * P.a q * Covering.vdC q < P.c4 q + 1 := by
  unfold c4
  have h0 : (0 : ℚ) ≤ 4 * P.a q * Covering.vdC q := by
    have := Covering.vdC_nonneg q; positivity
  exact ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩

/-- **Landing.** For column `j`, bank-A zigzag `p`, bank-B zigzag `q` and the two choices of
descent or first rise, if the ideal level lies in `[2/a_q, 1 - 2/a_q]`, the orbit of the root
contains a time in the second rise of `C_q` at a height `2N` whose relative level
`(2N+1)/cc_q` is within `1/a_q` of the ideal one. -/
theorem landing (F : Finset (ActualFamily P.heads P.T)) {j p q : ℕ} (sA sB : Bool)
    (hj1 : 1 ≤ j) (hjd : j < P.d) (hp1 : 1 ≤ p) (hpK : p ≤ P.K) (hq1 : 1 ≤ q) (hqK : q ≤ P.K)
    (hFA : ∀ i, 1 ≤ i → i ≤ p → P.famA i true ∈ F ∧ P.famA i false ∈ F)
    (hFB : ∀ i, 1 ≤ i → i ≤ q → P.famB i true ∈ F ∧ P.famB i false ∈ F)
    (hg : P.gFam ∈ F) (he : P.eFam ∈ F)
    (hz1 : 2 / (P.a q : ℚ) ≤ zst ((j : ℚ) / P.d) p q sA sB)
    (hz2 : zst ((j : ℚ) / P.d) p q sA sB ≤ 1 - 2 / (P.a q : ℚ)) :
    ∃ N : ℕ, P.U q + 2 * N ∈ shadowOrbit F (P.root j) ∧ 0 < N ∧ 2 * N + 2 ≤ P.cc q ∧
      |((2 * N + 1 : ℕ) : ℚ) / P.cc q - zst ((j : ℚ) / P.d) p q sA sB| < 1 / P.a q := by
  obtain ⟨htA, hι0, hιg, hι4⟩ := P.iotaA_facts sA hj1 hjd hp1 hpK
  have hA := P.bankA_points F hj1 hjd hp1 hpK hFA
  have htime : P.timeA j p sA ∈ shadowOrbit F (P.root j) := by
    cases sA
    · simpa [timeA] using hA.1
    · simpa [timeA] using hA.2
  have hOAe := P.OA_eq
  have hgp := P.g_point F (P.root j) (P.timeA j p sA) hg htime (by omega) (by omega)
  rw [show P.OA - P.timeA j p sA = P.iotaA j p sA by omega] at hgp
  have hιL : P.iotaA j p sA + 2 ≤ P.L := by have := P.hg_add_le; omega
  obtain ⟨hB1, hB2, hμ0, hμa⟩ :=
    P.bankB_points F (P.root j) (P.iotaA j p sA) q hgp hι4 hιL hq1 hqK hFB
  generalize hιdef : P.iotaA j p sA = ι at hB1 hB2 hμ0 hμa hιL
  generalize hμdef : muB ι q = μ at hB1 hB2 hμ0 hμa
  obtain ⟨r, hrdef⟩ : ∃ r, r = if sB then μ else 2 * P.a q - μ := ⟨_, rfl⟩
  have hr0 : 0 < r := by cases sB <;> simp only [hrdef, ite_true, Bool.false_eq_true, ite_false] <;> omega
  have hr2 : r < 2 * P.a q := by
    cases sB <;> simp only [hrdef, ite_true, Bool.false_eq_true, ite_false] <;> omega
  have hrt : P.σB q + r ∈ shadowOrbit F (P.root j) := by
    cases sB
    · simp only [hrdef, Bool.false_eq_true, ite_false]
      rw [show P.σB q + (2 * P.a q - μ) = P.σB q + 2 * P.a q - μ by omega]; exact hB1
    · simpa [hrdef] using hB2
  obtain ⟨v, hv, hvmem⟩ := P.e_point F (P.root j) q r he hq1 hqK hr0 hr2 hrt
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℤ, N₀ = (P.c4 q : ℤ) + P.a q - r := ⟨_, rfl⟩
  -- the error estimate
  have hAq : (0 : ℚ) < P.a q := by exact_mod_cast P.a_pos q
  have hLA : 4 * (P.a q : ℚ) ≤ P.L := by
    have h := P.L_eq_a hqK
    have h1 : 1 ≤ 4 ^ lev q := Nat.one_le_pow _ _ (by norm_num)
    have : 4 * P.a q ≤ P.L := by rw [h]; nlinarith [P.a_pos q]
    exact_mod_cast this
  obtain ⟨hμ1, hμ2⟩ := P.muB_bounds ι q hqK
  rw [hμdef] at hμ1 hμ2
  obtain ⟨hc1, hc2⟩ := P.c4_bounds q
  have hoff := P.iotaA_div sA hjd hp1 hpK
  rw [hιdef] at hoff
  have herr := landing_error hAq hLA hμ1 hμ2 hc1 hc2
  have hclose : |(2 * (N₀ : ℚ) + 1) / (8 * P.a q) - zst ((j : ℚ) / P.d) p q sA sB| < 1 / P.a q := by
    have hz : zst ((j : ℚ) / P.d) p q sA sB =
        Covering.vdC q + (if sB then 1 else -1) * (1 - (ι : ℚ) / P.L) / 4 := by
      rw [hoff]; simp only [zst]; ring
    rw [hz]
    cases sB
    · have hN : (N₀ : ℚ) = P.c4 q - P.a q + μ := by
        rw [hN₀, hrdef]; simp only [Bool.false_eq_true, ite_false]; push_cast
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have e : Covering.vdC q + (if false = true then (1 : ℚ) else -1) * (1 - (ι : ℚ) / P.L) / 4 =
          Covering.vdC q - (1 - (ι : ℚ) / P.L) / 4 := by
        simp only [Bool.false_eq_true, ite_false]; ring
      rw [hN, e]; exact herr.2
    · have hN : (N₀ : ℚ) = P.c4 q + P.a q - μ := by
        rw [hN₀, hrdef]; simp
      have e : Covering.vdC q + (if true = true then (1 : ℚ) else -1) * (1 - (ι : ℚ) / P.L) / 4 =
          Covering.vdC q + (1 - (ι : ℚ) / P.L) / 4 := by
        simp only [ite_true]; ring
      rw [hN, e]; exact herr.1
  -- the landing is in range
  have hlow : (1 : ℚ) / P.a q < (2 * (N₀ : ℚ) + 1) / (8 * P.a q) := by
    have := (abs_lt.mp hclose).1
    have h2 : 2 / (P.a q : ℚ) = 1 / P.a q + 1 / P.a q := by ring
    linarith
  have hhigh : (2 * (N₀ : ℚ) + 1) / (8 * P.a q) < 1 - 1 / P.a q := by
    have := (abs_lt.mp hclose).2
    have h2 : 2 / (P.a q : ℚ) = 1 / P.a q + 1 / P.a q := by ring
    linarith
  rw [div_lt_div_iff₀ hAq (by positivity)] at hlow
  rw [div_lt_iff₀ (by positivity)] at hhigh
  have hN1 : (8 : ℚ) < 2 * N₀ + 1 := by nlinarith
  have hN2 : (2 * (N₀ : ℚ) + 1) < 8 * P.a q - 8 := by
    have : (1 - 1 / (P.a q : ℚ)) * (8 * P.a q) = 8 * P.a q - 8 := by field_simp
    linarith
  have hN1' : 8 < 2 * N₀ + 1 := by exact_mod_cast hN1
  have hN2' : 2 * N₀ + 1 < 8 * (P.a q : ℤ) - 8 := by exact_mod_cast hN2
  have hψ : ψ (P.a q) N₀ = 2 * N₀ := by
    unfold ψ; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have hvN : (v : ℤ) = P.U q + 2 * N₀ := by
    rw [hv]; unfold landingZ; rw [← hN₀, hψ]
  refine ⟨N₀.toNat, ?_, by omega, ?_, ?_⟩
  · have : v = P.U q + 2 * N₀.toNat := by omega
    rw [← this]; exact hvmem
  · unfold cc; omega
  · have hcast : ((2 * N₀.toNat + 1 : ℕ) : ℚ) = 2 * (N₀ : ℚ) + 1 := by
      have : ((N₀.toNat : ℤ) : ℚ) = (N₀ : ℚ) := by rw [Int.toNat_of_nonneg (by omega)]
      push_cast; rw [← this]; push_cast; ring
    have hcc : (P.cc q : ℚ) = 8 * P.a q := by unfold cc; push_cast; ring
    rw [hcast, hcc]; exact hclose

end SourceCovers.Z3D.Index

import GapAreaMemo.Z3DOlder

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: the two bank heads

Bank zigzags with odd index run on head X, those with even index on head Y,
each head in time order: bank C, then bank B, then bank A. After its last bank
zigzag a head performs padding zigzags of height one after the horizon; they
are never reached before the horizon and only make the staircase hypotheses
uniform in the segment index.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag

variable (P : Index)

def NX : ℕ := 2 ^ P.ν
def NY : ℕ := 2 ^ P.ν - 1

theorem K_eq_NX : P.K = 2 * P.NX - 1 := by
  unfold K NX; rw [pow_succ]; ring_nf; try omega

theorem K_eq_NY : P.K = 2 * P.NY + 1 := by
  unfold K NY; have : 1 ≤ 2 ^ P.ν := Nat.one_le_two_pow; rw [pow_succ]; omega

theorem NX_pos : 1 ≤ P.NX := Nat.one_le_two_pow

theorem NY_pos : 1 ≤ P.NY := by
  unfold NY
  have : 2 ≤ 2 ^ P.ν := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ P.ν := Nat.pow_le_pow_right (by norm_num) (by have := P.hν; omega)
  omega

/-- A padding zigzag of height one at time `σ`. -/
def pad (σ : ℕ) : Seg := ⟨1, by norm_num, late σ 1 1 (by norm_num) (by norm_num)⟩

/-- The segments of head X. -/
def segX (j : ℕ) : Seg :=
  if j < P.NX then P.segC (2 * j)
  else if j < 2 * P.NX then P.segB (P.K - 2 * (j - P.NX))
  else if j < 3 * P.NX then P.segA (P.K - 2 * (j - 2 * P.NX))
  else pad (P.T + 10 * j)

def startX (j : ℕ) : ℕ :=
  if j < P.NX then P.U (2 * j)
  else if j < 2 * P.NX then P.σB (P.K - 2 * (j - P.NX))
  else if j < 3 * P.NX then P.σA (P.K - 2 * (j - 2 * P.NX))
  else P.T + 10 * j

/-- The segments of head Y. -/
def segY (j : ℕ) : Seg :=
  if j < P.NY then P.segC (2 * j + 1)
  else if j < 2 * P.NY then P.segB (P.K - 1 - 2 * (j - P.NY))
  else if j < 3 * P.NY then P.segA (P.K - 1 - 2 * (j - 2 * P.NY))
  else pad (P.T + 10 * j)

def startY (j : ℕ) : ℕ :=
  if j < P.NY then P.U (2 * j + 1)
  else if j < 2 * P.NY then P.σB (P.K - 1 - 2 * (j - P.NY))
  else if j < 3 * P.NY then P.σA (P.K - 1 - 2 * (j - 2 * P.NY))
  else P.T + 10 * j

/-! ### Endpoint formulas -/

theorem segC_depart (j : ℕ) (c : Fin (P.segC j).h) :
    P.U j ≤ (P.segC j).Z.P.depart c := by
  show P.U j ≤ P.U j + fC (j + 1) * (c.val + 1) - 1
  have := fC_pos (j + 1)
  have : 1 ≤ fC (j + 1) * (c.val + 1) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  omega

theorem segC_finish (j : ℕ) : (P.segC j).finish = P.U (j + 1) + P.cc (j + 1) := by
  unfold segC Seg.finish
  rw [early_finish]
  show _ = P.U j + fC (j + 1) * P.cc (j + 1) + P.cc (j + 1) + P.cc (j + 1)
  ring

theorem segB_depart (k : ℕ) (c : Fin (P.segB k).h) : P.σB k ≤ (P.segB k).Z.P.depart c := by
  show P.σB k ≤ P.σB k + c.val; omega

theorem segA_depart (k : ℕ) (c : Fin (P.segA k).h) : P.σA k ≤ (P.segA k).Z.P.depart c := by
  show P.σA k ≤ P.σA k + c.val; omega

theorem segB_finish (k : ℕ) : (P.segB k).finish = P.σB k + 2 * P.a k + fB k * P.a k := by
  unfold segB Seg.finish
  rw [late_finish]

theorem segA_finish (k : ℕ) : (P.segA k).finish = P.σA k + 2 * P.a k + fB k * P.a k := by
  unfold segA Seg.finish
  rw [late_finish]

theorem pad_finish (σ : ℕ) : (pad σ).finish = σ + 3 := by
  unfold pad Seg.finish
  rw [late_finish]
  simp

theorem pad_depart (σ : ℕ) (c : Fin (pad σ).h) : σ ≤ (pad σ).Z.P.depart c := by
  show σ ≤ σ + c.val; omega

/-- A bank zigzag of index `k ≥ 2` ends at the peak of zigzag `k - 1`, before its start. -/
theorem segB_finish_le {k : ℕ} (hk : 2 ≤ k) (hK : k ≤ P.K) :
    (P.segB k).finish + P.a (k - 1) ≤ P.σB (k - 2) := by
  rw [P.segB_finish, P.fB_mul hk hK]
  have h1 := P.σB_pred (k := k) (by omega) hK
  have h2 := P.σB_pred (k := k - 1) (by omega) (by omega)
  rw [show k - 1 - 1 = k - 2 by omega] at h2
  omega

theorem segA_finish_le {k : ℕ} (hk : 2 ≤ k) (hK : k ≤ P.K) :
    (P.segA k).finish + P.a (k - 1) ≤ P.σA (k - 2) := by
  rw [P.segA_finish, P.fB_mul hk hK]
  have h1 := P.σA_pred (k := k) (by omega) hK
  have h2 := P.σA_pred (k := k - 1) (by omega) (by omega)
  rw [show k - 1 - 1 = k - 2 by omega] at h2
  omega

theorem segB_one_finish : (P.segB 1).finish = P.OB + P.L := by
  rw [P.segB_finish, P.fB_one]
  have := P.σB_pred (k := 1) le_rfl P.K_pos
  unfold OB
  simp only [Nat.sub_self] at this
  omega

theorem segA_one_finish : (P.segA 1).finish = P.OA + P.L := by
  rw [P.segA_finish, P.fB_one]
  have := P.σA_pred (k := 1) le_rfl P.K_pos
  unfold OA
  simp only [Nat.sub_self] at this
  omega

theorem U_mono {i j : ℕ} (hij : i ≤ j) : P.U i ≤ P.U j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    show P.U i ≤ P.U j + fC (j + 1) * P.cc (j + 1) + P.cc (j + 1)
    omega

theorem U_strictMono : StrictMono P.U := by
  apply strictMono_nat_of_lt_succ
  intro j
  show P.U j < P.U j + fC (j + 1) * P.cc (j + 1) + P.cc (j + 1)
  have := P.cc_pos (j + 1); omega

theorem segC_finish_le {j : ℕ} (hj : j + 2 ≤ P.K) : (P.segC j).finish ≤ P.U (j + 2) := by
  rw [P.segC_finish]
  have := P.U_succ (k := j + 1) (by omega) hj
  rw [show j + 1 + 1 = j + 2 by ring] at this
  omega

/-! ### Validity of the two staircases -/

theorem Seg.walk_after_finish (S : Seg) {t : ℕ} (ht : S.finish ≤ t) : S.walk t = S.h :=
  S.Z.walk_after S.pos ht

theorem segC_before {j t : ℕ} (ht : t ≤ P.U j) : (P.segC j).walk t = 0 :=
  (P.segC j).Z.walk_before (P.segC j).pos (ht.trans (P.segC_depart j _))

theorem segB_before {k t : ℕ} (ht : t ≤ P.σB k) : (P.segB k).walk t = 0 :=
  (P.segB k).Z.walk_before (P.segB k).pos (ht.trans (P.segB_depart k _))

theorem segA_before {k t : ℕ} (ht : t ≤ P.σA k) : (P.segA k).walk t = 0 :=
  (P.segA k).Z.walk_before (P.segA k).pos (ht.trans (P.segA_depart k _))

theorem pad_before {σ t : ℕ} (ht : t ≤ σ) : (pad σ).walk t = 0 :=
  (pad σ).Z.walk_before (pad σ).pos (ht.trans (pad_depart σ _))

theorem valid_of_segs (S : ℕ → Seg) (start : ℕ → ℕ)
    (hbefore : ∀ j t, t ≤ start j → (S j).walk t = 0)
    (hfin : ∀ j, (S j).finish ≤ start (j + 1)) (hmono : StrictMono start) :
    Staircase.Valid (fun j => (S j).walk) (fun j => (S j).h) start where
  walk m := (S m).Z.isWalk (S m).pos
  at_start m := hbefore m _ le_rfl
  nonneg m t := (S m).Z.walk_nonneg t
  le_top m t := (S m).Z.walk_le t
  parked m _ ht := Seg.walk_after_finish (S m) ((hfin m).trans ht)
  start_mono := hmono
  before m t ht := hbefore m t ht

theorem endC_le_σB : P.endC + P.cc P.K ≤ P.σB P.K := by unfold σB; omega

theorem sumA_le_zero (k : ℕ) : P.sumA k ≤ P.sumA 0 := by
  unfold sumA
  exact sum_le_sum_of_subset_of_nonneg (fun i hi => by simp only [mem_Ioc] at hi ⊢; omega)
    (fun _ _ _ => Nat.zero_le _)

theorem σB_le_OB {k : ℕ} : P.σB k ≤ P.OB := by
  unfold OB σB; have := P.sumA_le_zero k; omega

theorem σA_le_OA {k : ℕ} : P.σA k ≤ P.OA := by
  unfold OA σA; have := P.sumA_le_zero k; omega

theorem OB_lt_σA {k : ℕ} : P.OB + P.L + 3 ≤ P.σA k := by unfold σA; omega

theorem U_le_endC {j : ℕ} (hj : j ≤ P.K) : P.U j ≤ P.endC := by
  unfold endC; have := P.U_mono hj; omega

theorem σB_lt_pred {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : P.σB k < P.σB (k - 1) := by
  rw [P.σB_pred hk hK]; have := P.a_pos k; omega

theorem σA_lt_pred {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : P.σA k < P.σA (k - 1) := by
  rw [P.σA_pred hk hK]; have := P.a_pos k; omega

theorem OA_lt_T : P.OA + P.L + 2 = P.T := rfl

theorem segC_last_finish : (P.segC (P.K - 1)).finish = P.endC := by
  rw [P.segC_finish, Nat.sub_add_cancel P.K_pos]; rfl

theorem segX_C {j : ℕ} (h : j < P.NX) : P.segX j = P.segC (2 * j) := by
  unfold segX; rw [ite_eq_left h]
theorem segX_B {j : ℕ} (h1 : P.NX ≤ j) (h2 : j < 2 * P.NX) :
    P.segX j = P.segB (P.K - 2 * (j - P.NX)) := by
  unfold segX; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem segX_A {j : ℕ} (h1 : 2 * P.NX ≤ j) (h2 : j < 3 * P.NX) :
    P.segX j = P.segA (P.K - 2 * (j - 2 * P.NX)) := by
  unfold segX; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
theorem segX_pad {j : ℕ} (h1 : 3 * P.NX ≤ j) : P.segX j = pad (P.T + 10 * j) := by
  unfold segX; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem startX_C {j : ℕ} (h : j < P.NX) : P.startX j = P.U (2 * j) := by
  unfold startX; rw [ite_eq_left h]
theorem startX_B {j : ℕ} (h1 : P.NX ≤ j) (h2 : j < 2 * P.NX) :
    P.startX j = P.σB (P.K - 2 * (j - P.NX)) := by
  unfold startX; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem startX_A {j : ℕ} (h1 : 2 * P.NX ≤ j) (h2 : j < 3 * P.NX) :
    P.startX j = P.σA (P.K - 2 * (j - 2 * P.NX)) := by
  unfold startX; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
theorem startX_pad {j : ℕ} (h1 : 3 * P.NX ≤ j) : P.startX j = P.T + 10 * j := by
  unfold startX; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem beforeX :
    ∀ j t, t ≤ P.startX j → (P.segX j).walk t = 0 := by
  have hK := P.K_eq_NX
  have hN := P.NX_pos
  intro j t ht
  rcases Nat.lt_or_ge j P.NX with h1 | h1
  · rw [P.segX_C h1]; rw [P.startX_C h1] at ht; exact P.segC_before ht
  rcases Nat.lt_or_ge j (2 * P.NX) with h2 | h2
  · rw [P.segX_B h1 h2]; rw [P.startX_B h1 h2] at ht; exact P.segB_before ht
  rcases Nat.lt_or_ge j (3 * P.NX) with h3 | h3
  · rw [P.segX_A h2 h3]; rw [P.startX_A h2 h3] at ht; exact P.segA_before ht
  · rw [P.segX_pad h3]; rw [P.startX_pad h3] at ht; exact pad_before ht

theorem finishX_le :
    ∀ j, (P.segX j).finish ≤ P.startX (j + 1) := by
  have hK := P.K_eq_NX
  have hN := P.NX_pos
  intro j
  rcases Nat.lt_or_ge (j + 1) P.NX with h1 | h1
  · rw [P.segX_C (by omega), P.startX_C h1]
    have := P.segC_finish_le (j := 2 * j) (by omega)
    rwa [show 2 * j + 2 = 2 * (j + 1) by ring] at this
  rcases Nat.eq_or_lt_of_le h1 with h1e | h1
  · rw [P.segX_C (by omega), ← h1e, P.startX_B (by omega) (by omega)]
    rw [show 2 * j = P.K - 1 by omega, P.segC_last_finish]
    simp only [Nat.sub_self, mul_zero, Nat.sub_zero]
    have := P.endC_le_σB; omega
  rcases Nat.lt_or_ge (j + 1) (2 * P.NX) with h2 | h2
  · rw [P.segX_B (by omega) (by omega), P.startX_B (by omega) h2]
    have := P.segB_finish_le (k := P.K - 2 * (j - P.NX)) (by omega) (by omega)
    rw [show P.K - 2 * (j + 1 - P.NX) = P.K - 2 * (j - P.NX) - 2 by omega]
    omega
  rcases Nat.eq_or_lt_of_le h2 with h2e | h2
  · rw [P.segX_B (by omega) (by omega), P.startX_A (by omega) (by omega),
      show P.K - 2 * (j - P.NX) = 1 by omega, P.segB_one_finish]
    have := P.OB_lt_σA (k := P.K - 2 * (j + 1 - 2 * P.NX)); omega
  rcases Nat.lt_or_ge (j + 1) (3 * P.NX) with h3 | h3
  · rw [P.segX_A (by omega) (by omega), P.startX_A (by omega) h3]
    have := P.segA_finish_le (k := P.K - 2 * (j - 2 * P.NX)) (by omega) (by omega)
    rw [show P.K - 2 * (j + 1 - 2 * P.NX) = P.K - 2 * (j - 2 * P.NX) - 2 by omega]
    omega
  rcases Nat.eq_or_lt_of_le h3 with h3e | h3
  · rw [P.segX_A (by omega) (by omega), P.startX_pad (by omega),
      show P.K - 2 * (j - 2 * P.NX) = 1 by omega, P.segA_one_finish]
    have := P.OA_lt_T; omega
  · rw [P.segX_pad (by omega), P.startX_pad (by omega), pad_finish]; omega

theorem startX_strictMono :
    StrictMono P.startX := by
  have hK := P.K_eq_NX
  have hN := P.NX_pos
  apply strictMono_nat_of_lt_succ
  intro j
  rcases Nat.lt_or_ge (j + 1) P.NX with h1 | h1
  · rw [P.startX_C (by omega), P.startX_C h1]
    exact P.U_strictMono (by omega)
  rcases Nat.eq_or_lt_of_le h1 with h1e | h1
  · rw [P.startX_C (by omega), ← h1e, P.startX_B (by omega) (by omega)]
    simp only [Nat.sub_self, mul_zero, Nat.sub_zero]
    have := P.U_le_endC (j := 2 * j) (by omega)
    have := P.endC_le_σB; have := P.cc_pos P.K; omega
  rcases Nat.lt_or_ge (j + 1) (2 * P.NX) with h2 | h2
  · rw [P.startX_B (by omega) (by omega), P.startX_B (by omega) h2,
      show P.K - 2 * (j + 1 - P.NX) = P.K - 2 * (j - P.NX) - 1 - 1 by omega]
    have h1' := P.σB_lt_pred (k := P.K - 2 * (j - P.NX)) (by omega) (by omega)
    have h2' := P.σB_lt_pred (k := P.K - 2 * (j - P.NX) - 1) (by omega) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le h2 with h2e | h2
  · rw [P.startX_B (by omega) (by omega), P.startX_A (by omega) (by omega)]
    have := P.σB_le_OB (k := P.K - 2 * (j - P.NX))
    have := P.OB_lt_σA (k := P.K - 2 * (j + 1 - 2 * P.NX)); omega
  rcases Nat.lt_or_ge (j + 1) (3 * P.NX) with h3 | h3
  · rw [P.startX_A (by omega) (by omega), P.startX_A (by omega) h3,
      show P.K - 2 * (j + 1 - 2 * P.NX) = P.K - 2 * (j - 2 * P.NX) - 1 - 1 by omega]
    have h1' := P.σA_lt_pred (k := P.K - 2 * (j - 2 * P.NX)) (by omega) (by omega)
    have h2' := P.σA_lt_pred (k := P.K - 2 * (j - 2 * P.NX) - 1) (by omega) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le h3 with h3e | h3
  · rw [P.startX_A (by omega) (by omega), P.startX_pad (by omega)]
    have := P.σA_le_OA (k := P.K - 2 * (j - 2 * P.NX)); have := P.OA_lt_T; omega
  · rw [P.startX_pad (by omega), P.startX_pad (by omega)]; omega

theorem validX : Staircase.Valid (fun j => (P.segX j).walk) (fun j => (P.segX j).h) P.startX :=
  valid_of_segs _ _ P.beforeX P.finishX_le P.startX_strictMono

theorem segY_C {j : ℕ} (h : j < P.NY) : P.segY j = P.segC (2 * j + 1) := by
  unfold segY; rw [ite_eq_left h]
theorem segY_B {j : ℕ} (h1 : P.NY ≤ j) (h2 : j < 2 * P.NY) :
    P.segY j = P.segB (P.K - 1 - 2 * (j - P.NY)) := by
  unfold segY; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem segY_A {j : ℕ} (h1 : 2 * P.NY ≤ j) (h2 : j < 3 * P.NY) :
    P.segY j = P.segA (P.K - 1 - 2 * (j - 2 * P.NY)) := by
  unfold segY; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
theorem segY_pad {j : ℕ} (h1 : 3 * P.NY ≤ j) : P.segY j = pad (P.T + 10 * j) := by
  unfold segY; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem startY_C {j : ℕ} (h : j < P.NY) : P.startY j = P.U (2 * j + 1) := by
  unfold startY; rw [ite_eq_left h]
theorem startY_B {j : ℕ} (h1 : P.NY ≤ j) (h2 : j < 2 * P.NY) :
    P.startY j = P.σB (P.K - 1 - 2 * (j - P.NY)) := by
  unfold startY; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem startY_A {j : ℕ} (h1 : 2 * P.NY ≤ j) (h2 : j < 3 * P.NY) :
    P.startY j = P.σA (P.K - 1 - 2 * (j - 2 * P.NY)) := by
  unfold startY; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
theorem startY_pad {j : ℕ} (h1 : 3 * P.NY ≤ j) : P.startY j = P.T + 10 * j := by
  unfold startY; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem segB_two_finish (hK : 2 ≤ P.K) : (P.segB 2).finish = P.σB 1 + P.a 1 := by
  rw [P.segB_finish]
  have h1 := P.fB_mul (k := 2) le_rfl hK
  have h2 := P.σB_pred (k := 2) (by norm_num) hK
  simp only [show (2 : ℕ) - 1 = 1 from rfl] at h1 h2
  omega

theorem segA_two_finish (hK : 2 ≤ P.K) : (P.segA 2).finish = P.σA 1 + P.a 1 := by
  rw [P.segA_finish]
  have h1 := P.fB_mul (k := 2) le_rfl hK
  have h2 := P.σA_pred (k := 2) (by norm_num) hK
  simp only [show (2 : ℕ) - 1 = 1 from rfl] at h1 h2
  omega

theorem σB_one_lt_OB : P.σB 1 + P.a 1 < P.OB := by
  have := P.σB_pred (k := 1) le_rfl P.K_pos
  unfold OB; simp only [Nat.sub_self] at this; have := P.a_pos 1; omega

theorem σA_one_lt_OA : P.σA 1 + P.a 1 < P.OA := by
  have := P.σA_pred (k := 1) le_rfl P.K_pos
  unfold OA; simp only [Nat.sub_self] at this; have := P.a_pos 1; omega

theorem segC_penultimate_finish (hK : 2 ≤ P.K) : (P.segC (P.K - 2)).finish ≤ P.U P.K := by
  rw [P.segC_finish, show P.K - 2 + 1 = P.K - 1 by omega]
  have := P.U_succ (k := P.K - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel P.K_pos] at this
  omega

theorem beforeY :
    ∀ j t, t ≤ P.startY j → (P.segY j).walk t = 0 := by
  have hK := P.K_eq_NY
  have hN := P.NY_pos
  intro j t ht
  rcases Nat.lt_or_ge j P.NY with h1 | h1
  · rw [P.segY_C h1]; rw [P.startY_C h1] at ht; exact P.segC_before ht
  rcases Nat.lt_or_ge j (2 * P.NY) with h2 | h2
  · rw [P.segY_B h1 h2]; rw [P.startY_B h1 h2] at ht; exact P.segB_before ht
  rcases Nat.lt_or_ge j (3 * P.NY) with h3 | h3
  · rw [P.segY_A h2 h3]; rw [P.startY_A h2 h3] at ht; exact P.segA_before ht
  · rw [P.segY_pad h3]; rw [P.startY_pad h3] at ht; exact pad_before ht

theorem finishY_le :
    ∀ j, (P.segY j).finish ≤ P.startY (j + 1) := by
  have hK := P.K_eq_NY
  have hN := P.NY_pos
  intro j
  rcases Nat.lt_or_ge (j + 1) P.NY with h1 | h1
  · rw [P.segY_C (by omega), P.startY_C h1]
    have := P.segC_finish_le (j := 2 * j + 1) (by omega)
    rwa [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring] at this
  rcases Nat.eq_or_lt_of_le h1 with h1e | h1
  · rw [P.segY_C (by omega), ← h1e, P.startY_B (by omega) (by omega)]
    simp only [Nat.sub_self, mul_zero, Nat.sub_zero]
    rw [show 2 * j + 1 = P.K - 2 by omega]
    have := P.segC_penultimate_finish (by omega)
    have := P.U_le_endC (j := P.K) le_rfl
    have := P.endC_le_σB
    have := P.σB_lt_pred (k := P.K) P.K_pos le_rfl
    omega
  rcases Nat.lt_or_ge (j + 1) (2 * P.NY) with h2 | h2
  · rw [P.segY_B (by omega) (by omega), P.startY_B (by omega) h2]
    have := P.segB_finish_le (k := P.K - 1 - 2 * (j - P.NY)) (by omega) (by omega)
    rw [show P.K - 1 - 2 * (j + 1 - P.NY) = P.K - 1 - 2 * (j - P.NY) - 2 by omega]
    omega
  rcases Nat.eq_or_lt_of_le h2 with h2e | h2
  · rw [P.segY_B (by omega) (by omega), P.startY_A (by omega) (by omega),
      show P.K - 1 - 2 * (j - P.NY) = 2 by omega, P.segB_two_finish (by omega)]
    have := P.σB_one_lt_OB
    have := P.OB_lt_σA (k := P.K - 1 - 2 * (j + 1 - 2 * P.NY)); omega
  rcases Nat.lt_or_ge (j + 1) (3 * P.NY) with h3 | h3
  · rw [P.segY_A (by omega) (by omega), P.startY_A (by omega) h3]
    have := P.segA_finish_le (k := P.K - 1 - 2 * (j - 2 * P.NY)) (by omega) (by omega)
    rw [show P.K - 1 - 2 * (j + 1 - 2 * P.NY) = P.K - 1 - 2 * (j - 2 * P.NY) - 2 by omega]
    omega
  rcases Nat.eq_or_lt_of_le h3 with h3e | h3
  · rw [P.segY_A (by omega) (by omega), P.startY_pad (by omega),
      show P.K - 1 - 2 * (j - 2 * P.NY) = 2 by omega, P.segA_two_finish (by omega)]
    have := P.σA_one_lt_OA; have := P.OA_lt_T; omega
  · rw [P.segY_pad (by omega), P.startY_pad (by omega), pad_finish]; omega

theorem startY_strictMono :
    StrictMono P.startY := by
  have hK := P.K_eq_NY
  have hN := P.NY_pos
  apply strictMono_nat_of_lt_succ
  intro j
  rcases Nat.lt_or_ge (j + 1) P.NY with h1 | h1
  · rw [P.startY_C (by omega), P.startY_C h1]
    exact P.U_strictMono (by omega)
  rcases Nat.eq_or_lt_of_le h1 with h1e | h1
  · rw [P.startY_C (by omega), ← h1e, P.startY_B (by omega) (by omega)]
    simp only [Nat.sub_self, mul_zero, Nat.sub_zero]
    have := P.U_le_endC (j := 2 * j + 1) (by omega)
    have := P.endC_le_σB; have := P.cc_pos P.K
    have := P.σB_lt_pred (k := P.K) P.K_pos le_rfl
    omega
  rcases Nat.lt_or_ge (j + 1) (2 * P.NY) with h2 | h2
  · rw [P.startY_B (by omega) (by omega), P.startY_B (by omega) h2,
      show P.K - 1 - 2 * (j + 1 - P.NY) = P.K - 1 - 2 * (j - P.NY) - 1 - 1 by omega]
    have h1' := P.σB_lt_pred (k := P.K - 1 - 2 * (j - P.NY)) (by omega) (by omega)
    have h2' := P.σB_lt_pred (k := P.K - 1 - 2 * (j - P.NY) - 1) (by omega) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le h2 with h2e | h2
  · rw [P.startY_B (by omega) (by omega), P.startY_A (by omega) (by omega)]
    have := P.σB_le_OB (k := P.K - 1 - 2 * (j - P.NY))
    have := P.OB_lt_σA (k := P.K - 1 - 2 * (j + 1 - 2 * P.NY)); omega
  rcases Nat.lt_or_ge (j + 1) (3 * P.NY) with h3 | h3
  · rw [P.startY_A (by omega) (by omega), P.startY_A (by omega) h3,
      show P.K - 1 - 2 * (j + 1 - 2 * P.NY) = P.K - 1 - 2 * (j - 2 * P.NY) - 1 - 1 by omega]
    have h1' := P.σA_lt_pred (k := P.K - 1 - 2 * (j - 2 * P.NY)) (by omega) (by omega)
    have h2' := P.σA_lt_pred (k := P.K - 1 - 2 * (j - 2 * P.NY) - 1) (by omega) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le h3 with h3e | h3
  · rw [P.startY_A (by omega) (by omega), P.startY_pad (by omega)]
    have := P.σA_le_OA (k := P.K - 1 - 2 * (j - 2 * P.NY)); have := P.OA_lt_T; omega
  · rw [P.startY_pad (by omega), P.startY_pad (by omega)]; omega

theorem validY : Staircase.Valid (fun j => (P.segY j).walk) (fun j => (P.segY j).h) P.startY :=
  valid_of_segs _ _ P.beforeY P.finishY_le P.startY_strictMono

end SourceCovers.Z3D.Index

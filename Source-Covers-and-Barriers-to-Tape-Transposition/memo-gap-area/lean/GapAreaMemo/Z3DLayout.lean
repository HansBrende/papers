import GapAreaMemo.Z3DParams

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: time layout

Bank C runs first: zigzag `C_k` (height `cc k`) rises during the second rise
of `C_{k-1}`, slowed by the height ratio, then descends and rises at unit
speed; its trough is `U k`. Bank B follows: zigzag `Z_k` (height `a k`, in the
order `k = K, …, 1`) starts at `σB k`, rises and descends at unit speed and
rises again slowed by the height ratio during the first rise of `Z_{k-1}`;
the second rise of `Z_1` takes `L` steps. Bank A repeats bank B later. The
outputs are the second rise of bank A's `Z_1`.
-/

namespace SourceCovers.Z3D.Index

open Finset

variable (P : Index)

/-- Slowing of the first rise of bank-C zigzag `k`. -/
def fC (k : ℕ) : ℕ := if k ≤ 1 then 1 else ratio (k - 1)

theorem fC_pos (k : ℕ) : 0 < fC k := by
  unfold fC
  split_ifs
  · omega
  · exact ratio_pos _

theorem fC_mul {k : ℕ} (hk : 2 ≤ k) (hK : k ≤ P.K) : fC k * P.cc k = P.cc (k - 1) := by
  unfold fC
  rw [ite_eq_right (by omega)]
  have := P.cc_succ (k := k - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at this
  omega

/-- Troughs of bank C, with `U 0 = 1` the start of bank C. -/
def U : ℕ → ℕ
  | 0 => 1
  | j + 1 => U j + fC (j + 1) * P.cc (j + 1) + P.cc (j + 1)

/-- Bank-C zigzag `C_{j+1}`. -/
def segC (j : ℕ) : Zigzag.Seg :=
  ⟨P.cc (j + 1), P.cc_pos _, Zigzag.early (P.U j) (P.cc (j + 1)) (fC (j + 1)) (P.cc_pos _) (fC_pos _)⟩

def endC : ℕ := P.U P.K + P.cc P.K

/-- Sum of the bank heights above index `k`. -/
def sumA (k : ℕ) : ℕ := ∑ i ∈ Ioc k P.K, P.a i

def hg : ℕ := 2 * P.sumA 0

theorem sumA_pred {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : P.sumA (k - 1) = P.a k + P.sumA k := by
  unfold sumA
  have : Ioc (k - 1) P.K = insert k (Ioc k P.K) := by
    ext i; simp only [mem_Ioc, mem_insert]; omega
  rw [this, sum_insert (by simp)]

theorem sumA_K : P.sumA P.K = 0 := by simp [sumA]

def σB (k : ℕ) : ℕ := P.endC + P.cc P.K + 2 * P.sumA k

def OB : ℕ := P.σB 0

/-- Slowing of the second rise of bank zigzag `k` (`4` for the largest). -/
def fB (k : ℕ) : ℕ := if k ≤ 1 then 4 else ratio (k - 1)

theorem fB_pos (k : ℕ) : 0 < fB k := by
  unfold fB
  split_ifs
  · omega
  · exact ratio_pos _

theorem fB_mul {k : ℕ} (hk : 2 ≤ k) (hK : k ≤ P.K) : fB k * P.a k = P.a (k - 1) := by
  unfold fB
  rw [ite_eq_right (by omega)]
  have := P.a_succ (k := k - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at this
  omega

theorem fB_one : fB 1 * P.a 1 = P.L := by
  have : fB 1 = 4 := by unfold fB; simp
  rw [this]; exact P.a_one

def segB (k : ℕ) : Zigzag.Seg :=
  ⟨P.a k, P.a_pos k, Zigzag.late (P.σB k) (P.a k) (fB k) (P.a_pos k) (fB_pos k)⟩

def σA (k : ℕ) : ℕ := P.OB + P.L + P.hg + 3 + 2 * P.sumA k

def OA : ℕ := P.σA 0

def segA (k : ℕ) : Zigzag.Seg :=
  ⟨P.a k, P.a_pos k, Zigzag.late (P.σA k) (P.a k) (fB k) (P.a_pos k) (fB_pos k)⟩

/-- The horizon: outputs occupy `OA + 1, …, OA + L`. -/
def T : ℕ := P.OA + P.L + 2

theorem σB_pred {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : P.σB (k - 1) = P.σB k + 2 * P.a k := by
  unfold σB; rw [P.sumA_pred hk hK]; ring

theorem σA_pred {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : P.σA (k - 1) = P.σA k + 2 * P.a k := by
  unfold σA; rw [P.sumA_pred hk hK]; ring

theorem OB_eq : P.OB = P.σB P.K + P.hg := by
  unfold OB σB hg; rw [P.sumA_K]; try ring

theorem OA_eq : P.OA = P.σA P.K + P.hg := by
  unfold OA σA hg; rw [P.sumA_K]; try ring

/-- The newer exception: unit rise from `OB + 1`, unit descent over bank A. -/
def gSchedule : LeanMachine.ScheduledExcursion.Schedule P.hg where
  depart := fun i => P.OB + 1 + i
  arrive := fun i => P.OA - i
  depart_strictMono := fun i j hij => by
    show P.OB + 1 + i.val < P.OB + 1 + j.val; have : i.val < j.val := hij; omega
  arrive_strictAnti := fun i j hij => by
    show P.OA - j.val < P.OA - i.val
    have : i.val < j.val := hij; have := j.isLt
    have : P.hg ≤ P.OA := by rw [P.OA_eq]; omega
    omega
  separated := fun i j => by
    show P.OB + 1 + i.val + 1 < P.OA - j.val
    have := i.isLt; have := j.isLt
    rw [P.OA_eq]
    unfold σA
    rw [P.sumA_K]
    omega

end SourceCovers.Z3D.Index

import GapAreaMemo.Z3DLayout

set_option autoImplicit false

/-!
# The older exception

The older exception descends at unit speed over bank B and rises earlier,
during bank C, one level at each landing time. The descent time `σB k + r` of
block `k` (`r < 2 a k`) lands at `U k + ψ (c4 k + a k - r)`, where
`c4 k = ⌊4 a_k vdC(k)⌋` and `ψ` is the identity below `0`, doubles on
`[0, 4 a_k]` (the second rise of `C_k`, relative level `vdC(k) ± (1-y)/4`), and
adds `4 a_k` above. Landings outside the second rise park in the descents of
`C_k` and `C_{k+1}`; consecutive blocks never collide because `a k ≤ 4 a (k+1)`.
-/

namespace SourceCovers.Z3D.Index

open Classical Finset

variable (P : Index)

/-- Twice the heights of blocks `1, …, k`. -/
def pre (k : ℕ) : ℕ := 2 * ∑ i ∈ Ioc 0 k, P.a i

theorem pre_zero : P.pre 0 = 0 := by simp [pre]

theorem pre_succ (k : ℕ) : P.pre (k + 1) = P.pre k + 2 * P.a (k + 1) := by
  unfold pre
  rw [show Ioc 0 (k + 1) = insert (k + 1) (Ioc 0 k) by ext i; simp only [mem_Ioc, mem_insert]; omega,
    sum_insert (by simp)]
  ring

theorem pre_mono {i j : ℕ} (hij : i ≤ j) : P.pre i ≤ P.pre j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [P.pre_succ]; omega

theorem pre_strictMono : StrictMono P.pre := by
  apply strictMono_nat_of_lt_succ
  intro k; rw [P.pre_succ]; have := P.a_pos (k + 1); omega

theorem pre_K : P.pre P.K = P.hg := by
  unfold pre hg sumA
  congr 1

theorem OB_sub_σB {k : ℕ} (hk : k ≤ P.K) : P.OB = P.σB k + P.pre k := by
  unfold OB σB pre sumA
  have : Ioc 0 P.K = Ioc 0 k ∪ Ioc k P.K := by
    ext i; simp only [mem_Ioc, mem_union]; omega
  rw [this, sum_union (by rw [disjoint_left]; intro i h1 h2; simp only [mem_Ioc] at h1 h2; omega)]
  ring

/-- The block of a level `1 ≤ ℓ ≤ pre K`. -/
noncomputable def blockOf (ℓ : ℕ) : ℕ :=
  if h : ∃ k, ℓ ≤ P.pre k then Nat.find h else 0

theorem blockOf_spec {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓK : ℓ ≤ P.pre P.K) :
    1 ≤ P.blockOf ℓ ∧ P.blockOf ℓ ≤ P.K ∧ P.pre (P.blockOf ℓ - 1) < ℓ ∧ ℓ ≤ P.pre (P.blockOf ℓ) := by
  have hex : ∃ k, ℓ ≤ P.pre k := ⟨P.K, hℓK⟩
  unfold blockOf
  rw [dite_eq_left hex]
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ P.K := Nat.find_min' hex hℓK
  have hpos : 1 ≤ Nat.find hex := by
    by_contra h0
    have : Nat.find hex = 0 := by omega
    rw [this, P.pre_zero] at hspec
    omega
  refine ⟨hpos, hle, ?_, hspec⟩
  have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  omega

theorem blockOf_eq {ℓ k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) (h1 : P.pre (k - 1) < ℓ) (h2 : ℓ ≤ P.pre k) :
    P.blockOf ℓ = k := by
  have hℓ : 1 ≤ ℓ := by have := Nat.zero_le (P.pre (k - 1)); omega
  have hℓK : ℓ ≤ P.pre P.K := h2.trans (P.pre_mono hK)
  obtain ⟨hb1, hbK, hb2, hb3⟩ := P.blockOf_spec hℓ hℓK
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := P.pre_mono (show P.blockOf ℓ ≤ k - 1 by omega)
    omega
  · have := P.pre_mono (show k ≤ P.blockOf ℓ - 1 by omega)
    omega

/-- The scaled centre `⌊4 a_k vdC(k)⌋`. -/
noncomputable def c4 (k : ℕ) : ℕ := ⌊(4 * P.a k : ℚ) * Covering.vdC k⌋₊

theorem c4_lt (k : ℕ) : P.c4 k < 4 * P.a k := by
  unfold c4
  have h := (Covering.vdC_mem k)
  have ha : (0 : ℚ) < 4 * P.a k := by have := P.a_pos k; positivity
  have : (4 * P.a k : ℚ) * Covering.vdC k < 4 * P.a k := by nlinarith
  have hf := Nat.floor_le (show (0 : ℚ) ≤ (4 * P.a k : ℚ) * Covering.vdC k by nlinarith)
  have : (⌊(4 * P.a k : ℚ) * Covering.vdC k⌋₊ : ℚ) < 4 * P.a k := lt_of_le_of_lt hf this
  exact_mod_cast this

/-- The landing offset map of a block of height `a`. -/
def ψ (a : ℕ) (N : ℤ) : ℤ := if N < 0 then N else if N ≤ 4 * a then 2 * N else 4 * a + N

theorem ψ_strictMono (a : ℕ) {M N : ℤ} (h : M < N) : ψ a M < ψ a N := by
  unfold ψ
  split_ifs <;> omega

theorem ψ_ge (a : ℕ) (N : ℤ) : N ≤ ψ a N := by unfold ψ; split_ifs <;> omega

theorem ψ_le (a : ℕ) (N : ℤ) (_h : N ≤ 5 * a) : ψ a N ≤ 4 * a + N := by unfold ψ; split_ifs <;> omega

/-- The landing time of the descent time `σB k + r`, as an integer. -/
noncomputable def landingZ (k r : ℕ) : ℤ := (P.U k : ℤ) + ψ (P.a k) ((P.c4 k : ℤ) + P.a k - r)

theorem U_succ {k : ℕ} (hk : 1 ≤ k) (hK : k + 1 ≤ P.K) :
    P.U (k + 1) = P.U k + P.cc k + P.cc (k + 1) := by
  rw [U, fC_mul P (by omega) hK]
  simp

theorem U_ge (k : ℕ) (hk : 1 ≤ k) : P.cc k ≤ P.U k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [U]
  omega

theorem landingZ_lower {k r : ℕ} (hr : r < 2 * P.a k) :
    (P.U k : ℤ) - P.a k + 1 ≤ P.landingZ k r := by
  unfold landingZ
  have := ψ_ge (P.a k) ((P.c4 k : ℤ) + P.a k - r)
  omega

theorem landingZ_upper (k r : ℕ) : P.landingZ k r ≤ (P.U k : ℤ) + 9 * P.a k - 1 := by
  unfold landingZ
  have hc := P.c4_lt k
  have := ψ_le (P.a k) ((P.c4 k : ℤ) + P.a k - r) (by omega)
  omega

theorem landingZ_pos {k r : ℕ} (hk : 1 ≤ k) (hr : r < 2 * P.a k) : 0 < P.landingZ k r := by
  have h1 := P.landingZ_lower hr
  have h2 := P.U_ge k hk
  unfold cc at h2
  omega

/-- The rise of the older exception: level `ℓ ≥ 1` of block `k` departs at its landing. -/
noncomputable def eDepart (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then 0 else (P.landingZ (P.blockOf ℓ) (P.pre (P.blockOf ℓ) - ℓ)).toNat

theorem eDepart_eq {ℓ k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) (h1 : P.pre (k - 1) < ℓ) (h2 : ℓ ≤ P.pre k) :
    (P.eDepart ℓ : ℤ) = P.landingZ k (P.pre k - ℓ) := by
  have hℓ : ℓ ≠ 0 := by have := Nat.zero_le (P.pre (k - 1)); omega
  unfold eDepart
  rw [ite_eq_right hℓ, P.blockOf_eq hk hK h1 h2]
  have hr : P.pre k - ℓ < 2 * P.a k := by
    have := P.pre_succ (k - 1)
    rw [Nat.sub_add_cancel hk] at this
    omega
  exact Int.toNat_of_nonneg (P.landingZ_pos hk hr).le

theorem eDepart_lt_succ {ℓ : ℕ} (hℓ : ℓ + 1 ≤ P.pre P.K) : P.eDepart ℓ < P.eDepart (ℓ + 1) := by
  obtain ⟨hb1, hbK, hb2, hb3⟩ := P.blockOf_spec (ℓ := ℓ + 1) (by omega) hℓ
  generalize P.blockOf (ℓ + 1) = k at hb1 hbK hb2 hb3
  have hpk := P.pre_succ (k - 1)
  rw [Nat.sub_add_cancel hb1] at hpk
  have hnext := P.eDepart_eq hb1 hbK hb2 hb3
  by_cases h0 : ℓ = 0
  · subst h0
    have : P.eDepart 0 = 0 := by simp [eDepart]
    rw [this]
    have hr : P.pre k - 1 < 2 * P.a k := by omega
    have := P.landingZ_pos hb1 hr
    simp only [zero_add] at hnext ⊢
    omega
  · by_cases hsame : P.pre (k - 1) < ℓ
    · have hcur := P.eDepart_eq hb1 hbK hsame (by omega)
      have hlt : P.landingZ k (P.pre k - ℓ) < P.landingZ k (P.pre k - (ℓ + 1)) := by
        unfold landingZ
        have := ψ_strictMono (P.a k) (M := (P.c4 k : ℤ) + P.a k - (P.pre k - ℓ : ℕ))
          (N := (P.c4 k : ℤ) + P.a k - (P.pre k - (ℓ + 1) : ℕ)) (by omega)
        omega
      omega
    · -- `ℓ` closes block `k - 1`, and `ℓ + 1` opens block `k`
      have hℓeq : ℓ = P.pre (k - 1) := by omega
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k = 1 := by omega
        rw [this, show (1 : ℕ) - 1 = 0 from rfl, P.pre_zero] at hℓeq
        exact h0 hℓeq
      have hprev : P.pre (k - 1 - 1) < ℓ := by
        have h1 := P.pre_strictMono (show k - 1 - 1 < k - 1 by omega)
        omega
      have hcur := P.eDepart_eq (k := k - 1) (by omega) (by omega) hprev (by omega)
      have hup := P.landingZ_upper (k - 1) (P.pre (k - 1) - ℓ)
      have hlow := P.landingZ_lower (k := k) (r := P.pre k - (ℓ + 1)) (by omega)
      have hU := P.U_succ (k := k - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hU
      have hfour := P.a_le_four_mul (k := k - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hfour
      unfold cc at hU
      omega

theorem eDepart_strictMono : StrictMonoOn P.eDepart (Set.Iio P.hg) := by
  intro i hi j hj hij
  have hi' : i < P.hg := hi
  have hj' : j < P.hg := hj
  induction j, hij using Nat.le_induction with
  | base => exact P.eDepart_lt_succ (by rw [P.pre_K]; omega)
  | succ j hij ih =>
    have := P.eDepart_lt_succ (ℓ := j) (by rw [P.pre_K]; omega)
    exact (ih (by simp only [Set.mem_Iio]; omega) (by omega)).trans this

theorem eDepart_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.pre P.K) : P.eDepart i ≤ P.eDepart j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (P.eDepart_lt_succ hj).le

theorem eDepart_le {ℓ : ℕ} (hℓ : ℓ ≤ P.pre P.K) : P.eDepart ℓ ≤ P.U P.K + 9 * P.a P.K := by
  have h1 := P.eDepart_mono hℓ le_rfl
  have hK := P.K_pos
  have he := P.eDepart_eq (k := P.K) hK le_rfl (P.pre_strictMono (by omega)) le_rfl
  have hup := P.landingZ_upper P.K (P.pre P.K - P.pre P.K)
  omega

theorem σB_K : P.σB P.K = P.U P.K + 16 * P.a P.K := by
  unfold σB endC cc; rw [P.sumA_K]; ring

/-- The older exception as a scheduled excursion. -/
noncomputable def eSchedule : LeanMachine.ScheduledExcursion.Schedule P.hg where
  depart := fun ℓ => P.eDepart ℓ
  arrive := fun ℓ => P.OB - ℓ
  depart_strictMono := fun i j hij => P.eDepart_strictMono i.isLt j.isLt hij
  arrive_strictAnti := fun i j hij => by
    show P.OB - j.val < P.OB - i.val
    have : i.val < j.val := hij
    have := j.isLt
    have : P.hg ≤ P.OB := by rw [P.OB_eq]; omega
    omega
  separated := fun i j => by
    show P.eDepart i.val + 1 < P.OB - j.val
    have h1 := P.eDepart_le (ℓ := i.val) (by rw [P.pre_K]; exact i.isLt.le)
    have h2 := j.isLt
    have h3 := P.OB_eq
    have h4 := P.σB_K
    have h5 := P.a_pos P.K
    omega

end SourceCovers.Z3D.Index

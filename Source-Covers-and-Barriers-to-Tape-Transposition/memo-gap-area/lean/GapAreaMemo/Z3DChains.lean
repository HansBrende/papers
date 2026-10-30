import GapAreaMemo.Z3DSteps
import GapAreaMemo.LandingOrbits

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: orbit chains

From a time in the second rise of a bank's largest zigzag at cell `c`, the
lower and upper families of zigzags `1, 2, …` alternately reach the descent
and the first rise of each zigzag, at levels `c, c / f₂, (c / f₂) / f₃, …`. In
bank C, from the second rise of `C_k` at cell `η`, the chain reaches the
descent of `C_k`, the second rise of `C_{k-1}` at cell `f (η + 1) - 1`, and so on
down to the first rise of `C_1`.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies

variable (P : Index)

/-- Levels along a late bank: `lv c 0 = c` at zigzag 1, then divide by the slowing. -/
def lv (c : ℕ) : ℕ → ℕ
  | 0 => c
  | n + 1 => lv c n / fB (n + 2)

/-- **Late-bank chain.** Bank zigzag `n + 1` of a late bank with starts `σ`:
its descent time and first-rise time at the chain level are in the orbit. -/
theorem late_chain (σ : ℕ → ℕ) (hσ : ∀ k, 1 ≤ k → k ≤ P.K → σ (k - 1) = σ k + 2 * P.a k)
    (famU famL : ℕ → ActualFamily P.heads P.T)
    (hU : ∀ k, 1 ≤ k → k ≤ P.K → ∃ hd,
      IsSchedFamily (famU k) hd (late (σ k) (P.a k) (fB k) (P.a_pos k) (fB_pos k)).P)
    (hL : ∀ k, 1 ≤ k → k ≤ P.K → ∃ hd,
      IsSchedFamily (famL k) hd (late (σ k) (P.a k) (fB k) (P.a_pos k) (fB_pos k)).Q)
    (F : Finset (ActualFamily P.heads P.T)) (s c t₀ : ℕ)
    (ht₀ : t₀ ∈ shadowOrbit F s)
    (h1 : σ 1 + 2 * P.a 1 + 4 * c ≤ t₀) (h2 : t₀ < σ 1 + 2 * P.a 1 + 4 * (c + 1)) :
    ∀ n, n + 1 ≤ P.K → (∀ i ≤ n, famU (i + 1) ∈ F ∧ famL (i + 1) ∈ F) →
      (∀ i ≤ n, 0 < lv c i ∧ lv c i < P.a (i + 1)) →
      σ (n + 1) + 2 * P.a (n + 1) - lv c n ∈ shadowOrbit F s ∧
        σ (n + 1) + lv c n ∈ shadowOrbit F s := by
  intro n
  induction n with
  | zero =>
    intro hK hF hlv
    obtain ⟨hdL, hqL⟩ := hL 1 le_rfl hK
    obtain ⟨hdU, hqU⟩ := hU 1 le_rfl hK
    have hf1 : fB 1 = 4 := by unfold fB; simp
    have hlv0 := hlv 0 le_rfl
    simp only [lv] at hlv0 ⊢
    have hdn : (famL 1).shadow t₀ = σ 1 + 2 * P.a 1 - c := by
      apply late_lower_step (P.a_pos 1) (fB_pos 1) hqL hlv0.1 hlv0.2
      · rw [hf1]; exact h1
      · rw [hf1]; exact h2
    have hmem := shadowOrbit_step ht₀ (hF 0 le_rfl).2
    rw [hdn] at hmem
    refine ⟨hmem, ?_⟩
    have hup := late_upper_step (P.a_pos 1) (fB_pos 1) hqU hlv0.1 hlv0.2
    have hmem2 := shadowOrbit_step hmem (hF 0 le_rfl).1
    rw [hup] at hmem2
    exact hmem2
  | succ n ih =>
    intro hK hF hlv
    obtain ⟨hprev_dn, hprev_up⟩ := ih (by omega) (fun i hi => hF i (by omega))
      (fun i hi => hlv i (by omega))
    have hk := hσ (n + 2) (by omega) (by omega)
    simp only [show n + 2 - 1 = n + 1 by omega] at hk
    obtain ⟨hdL, hqL⟩ := hL (n + 2) (by omega) hK
    obtain ⟨hdU, hqU⟩ := hU (n + 2) (by omega) hK
    have hl := hlv (n + 1) le_rfl
    have hc : lv c (n + 1) = lv c n / fB (n + 2) := rfl
    have hfpos := fB_pos (n + 2)
    have hd1 : fB (n + 2) * (lv c n / fB (n + 2)) ≤ lv c n := Nat.mul_div_le _ _
    have hd2 : lv c n < fB (n + 2) * (lv c n / fB (n + 2) + 1) := by
      have := Nat.lt_div_mul_add (a := lv c n) hfpos
      rw [mul_comm]; nlinarith [this]
    have hdn : (famL (n + 2)).shadow (σ (n + 1) + lv c n) =
        σ (n + 2) + 2 * P.a (n + 2) - lv c (n + 1) := by
      apply late_lower_step (P.a_pos _) (fB_pos _) hqL hl.1 hl.2
      · rw [hc, ← hk]; omega
      · rw [hc, ← hk]; omega
    have hmem := shadowOrbit_step hprev_up (hF (n + 1) le_rfl).2
    rw [hdn] at hmem
    refine ⟨hmem, ?_⟩
    have hup := late_upper_step (P.a_pos _) (fB_pos _) hqU hl.1 hl.2
    have hmem2 := shadowOrbit_step hmem (hF (n + 1) le_rfl).1
    rw [hup] at hmem2
    exact hmem2

theorem U_eq (i : ℕ) (hi : 1 ≤ i) : P.U i = P.U (i - 1) + fC i * P.cc i + P.cc i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rfl

/-- The bank-C families with their explicit shapes. -/
theorem famC_shape {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P.K) :
    (∃ hd, IsSchedFamily (P.famC i true) hd
      (early (P.U (i - 1)) (P.cc i) (fC i) (P.cc_pos i) (fC_pos i)).P) ∧
    (∃ hd, IsSchedFamily (P.famC i false) hd
      (early (P.U (i - 1)) (P.cc i) (fC i) (P.cc_pos i) (fC_pos i)).Q) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact P.famC_sched h1 h2

/-- One bank-C zigzag: from its second rise at height `e`, its descent and
its first rise at height `e`. -/
theorem early_pair (F : Finset (ActualFamily P.heads P.T)) (s i e : ℕ)
    (hi1 : 1 ≤ i) (hiK : i ≤ P.K) (hFu : P.famC i true ∈ F) (hFl : P.famC i false ∈ F)
    (he0 : 0 < e) (he1 : e < P.cc i) (hu : P.U i + e ∈ shadowOrbit F s) :
    P.U i - e ∈ shadowOrbit F s ∧ P.U (i - 1) + fC i * (e + 1) - 1 ∈ shadowOrbit F s := by
  obtain ⟨⟨hdU, hqU⟩, ⟨hdL, hqL⟩⟩ := P.famC_shape hi1 hiK
  have hUi := P.U_eq i hi1
  have hdn := early_lower_step (P.cc_pos i) (fC_pos i) hqL he0 he1
  have hmem := shadowOrbit_step hu hFl
  rw [show P.U i + e = P.U (i - 1) + fC i * P.cc i + P.cc i + e by omega, hdn] at hmem
  have hup := early_upper_step (P.cc_pos i) (fC_pos i) hqU he0 he1
  have hmem2 := shadowOrbit_step hmem hFu
  rw [hup] at hmem2
  exact ⟨by rw [show P.U i - e = P.U (i - 1) + fC i * P.cc i + P.cc i - e by omega]; exact hmem,
    hmem2⟩

/-- **Bank-C chain.** From the second rise of `C_q` at height `η`, every
lower zigzag `C_i` is reached at height `e` with `(e+1)/cc_i = (η+1)/cc_q`,
in its second rise, its descent and its first rise. -/
theorem early_chain (F : Finset (ActualFamily P.heads P.T)) (s q η : ℕ)
    (hq1 : 1 ≤ q) (hqK : q ≤ P.K) (hstart : P.U q + η ∈ shadowOrbit F s)
    (hF : ∀ i, 1 ≤ i → i ≤ q → P.famC i true ∈ F ∧ P.famC i false ∈ F)
    (h0 : 0 < η) (h1 : η + 1 < P.cc q) :
    ∀ d, d + 1 ≤ q → ∃ e, (e + 1) * P.cc q = P.cc (q - d) * (η + 1) ∧ 0 < e ∧
      e + 1 < P.cc (q - d) ∧ P.U (q - d) + e ∈ shadowOrbit F s ∧
      P.U (q - d) - e ∈ shadowOrbit F s ∧
      P.U (q - d - 1) + fC (q - d) * (e + 1) - 1 ∈ shadowOrbit F s := by
  intro d
  induction d with
  | zero =>
    intro _
    have hp := P.early_pair F s q η hq1 hqK (hF q hq1 le_rfl).1 (hF q hq1 le_rfl).2 h0
      (by omega) hstart
    exact ⟨η, by rw [Nat.sub_zero, mul_comm], h0, by simpa using h1, by simpa using hstart,
      by simpa using hp.1, by simpa using hp.2⟩
  | succ d ih =>
    intro hd
    obtain ⟨e', he'1, he'0, he'2, -, -, hnext⟩ := ih (by omega)
    obtain ⟨i, hi⟩ : ∃ i, q - d = i + 1 := ⟨q - d - 1, by omega⟩
    have hi1 : 1 ≤ i := by omega
    rw [hi] at he'1 he'2 hnext
    rw [show q - (d + 1) = i by omega]
    simp only [Nat.add_sub_cancel] at hnext
    have hfm : fC (i + 1) * P.cc (i + 1) = P.cc i := by
      have := P.fC_mul (k := i + 1) (by omega) (by omega)
      simpa using this
    have hfpos := fC_pos (i + 1)
    have hX : 2 ≤ fC (i + 1) * (e' + 1) := by nlinarith
    have hlt : fC (i + 1) * (e' + 1) < P.cc i := by
      rw [← hfm]; exact Nat.mul_lt_mul_of_pos_left he'2 hfpos
    have hmem : P.U i + (fC (i + 1) * (e' + 1) - 1) ∈ shadowOrbit F s := by
      rw [show P.U i + (fC (i + 1) * (e' + 1) - 1) = P.U i + fC (i + 1) * (e' + 1) - 1 by omega]
      exact hnext
    have hp := P.early_pair F s i _ hi1 (by omega) (hF i hi1 (by omega)).1
      (hF i hi1 (by omega)).2 (by omega) (by omega) hmem
    refine ⟨fC (i + 1) * (e' + 1) - 1, ?_, by omega, by omega, hmem, hp.1, hp.2⟩
    calc (fC (i + 1) * (e' + 1) - 1 + 1) * P.cc q = fC (i + 1) * ((e' + 1) * P.cc q) := by
          rw [Nat.sub_add_cancel (by omega)]; ring
      _ = fC (i + 1) * (P.cc (i + 1) * (η + 1)) := by rw [he'1]
      _ = P.cc i * (η + 1) := by rw [← hfm]; ring

end SourceCovers.Z3D.Index

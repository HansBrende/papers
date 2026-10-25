import PassMemo.Envelope

/-! A native halting run has at most exponentially many steps in its number of passes. -/

namespace PassMemo

open Finset Transpose Transpose.Tape Transpose.Tape.Impl

def passFactor (M : TM) : ℕ := (2 * M.k + 3) * (signatureCount M + 1)

theorem passFactor_pos (M : TM) : 0 < passFactor M := by
  unfold passFactor
  positivity

/-- One monotone pass multiplies the input-plus-time envelope by a machine constant. -/
theorem pass_envelope {M : TM} {w : List Bool} {a e T : ℕ}
    (hae : a ≤ e) (heT : e ≤ T) (hm : AllMono M w a e) (hhalt : HaltsAt M w T) :
    w.length + e + 1 ≤ passFactor M * (w.length + a + 1) := by
  classical
  let R := w.length + a
  let marks := univ.biUnion fun h : Head M => (Ico a e).filter (Marked (trajectory M w h) R)
  have hmarks : marks ⊆ Ico a e := by
    intro t ht
    obtain ⟨h, _, ht⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp ht).1
  have hcard : marks.card ≤ (M.k + 1) * (2 * R + 2) := by
    calc marks.card ≤ ∑ h : Head M, ((Ico a e).filter (Marked (trajectory M w h) R)).card :=
          card_biUnion_le
      _ ≤ ∑ _h : Head M, (2 * R + 2) := sum_le_sum fun h _ =>
          card_marked (trajectory_mono hm h) (fun t _ _ => trajectory_unit M w h t)
      _ = _ := by simp [Head]
  have hlen : e - a ≤ (marks.card + 1) * signatureCount M + marks.card :=
    interval_length_le marks hmarks hae (by
      intro u v hau huv hve hn
      apply unmarked_interval_bound hm hau huv hve heT hhalt
      intro h t hut htv hmarked
      exact hn t (mem_Ico.mpr ⟨hut, htv⟩) (mem_biUnion.mpr
        ⟨h, mem_univ _, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hmarked⟩⟩))
  have hp : 1 ≤ w.length + a + 1 := by omega
  have hmul := Nat.mul_le_mul_right (signatureCount M + 1) hcard
  have hsp := Nat.mul_le_mul_left (signatureCount M) hp
  have hsub := Nat.sub_add_cancel hae
  unfold passFactor
  dsimp [R] at hcard hmul
  nlinarith

/-- No runtime premise: the run is the first paper's actual deterministic tape-machine run. -/
theorem halting_run_length {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hhalt : HaltsAt M w T) (hp : PassPartition M w T r p) :
    w.length + T + 1 ≤ (w.length + 1) * passFactor M ^ r := by
  have hbound : ∀ i ≤ r, w.length + p i + 1 ≤ (w.length + 1) * passFactor M ^ i := by
    intro i
    induction i with
    | zero => intro _; simp [hp.1]
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := pass_envelope (hp.2.2.1 i (by omega))
        (pp_le_T hp hi) (hp.2.2.2 i (by omega)) hhalt
      calc w.length + p (i + 1) + 1 ≤ passFactor M * (w.length + p i + 1) := hstep
        _ ≤ passFactor M * ((w.length + 1) * passFactor M ^ i) := Nat.mul_le_mul_left _ hprev
        _ = (w.length + 1) * passFactor M ^ (i + 1) := by rw [pow_succ]; ring
  simpa [hp.2.1] using hbound r le_rfl

def timeBound (M : TM) (L r : ℕ) : ℕ := (L + 1) * passFactor M ^ r

theorem halting_time_le {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hhalt : HaltsAt M w T) (hp : PassPartition M w T r p) :
    T ≤ timeBound M w.length r := by
  have := halting_run_length hhalt hp
  unfold timeBound
  omega

/-- The logarithm needed by the old adaptive theorem is linear in `r` and `log L`. -/
theorem timeBound_log (M : TM) (L r : ℕ) :
    Nat.clog 2 (2 * timeBound M L r + 1) ≤
      2 + Nat.clog 2 (L + 1) + r * Nat.clog 2 (passFactor M) := by
  have hL := Nat.le_pow_clog (by decide : 1 < 2) (L + 1)
  have hC := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) (passFactor M)) r
  have hLC := Nat.mul_le_mul hL hC
  rw [← pow_mul] at hLC
  have hpos : 0 < (L + 1) * passFactor M ^ r := by
    exact Nat.mul_pos (by omega) (pow_pos (passFactor_pos M) r)
  apply Nat.clog_le_of_le_pow
  unfold timeBound
  rw [pow_add, pow_add, Nat.mul_comm (Nat.clog 2 (passFactor M)) r] at *
  norm_num at *
  nlinarith

end PassMemo

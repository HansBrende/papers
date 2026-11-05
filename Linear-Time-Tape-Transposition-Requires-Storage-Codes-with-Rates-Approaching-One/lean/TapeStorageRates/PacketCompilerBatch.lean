import TapeStorageRates.PacketCompilerCells

/-! # One genuine native batch from three coarse cells

The input alignment may lie strictly inside a long cell. Choosing the rightmost length-s
subinterval of the current cell that is needed to contain the starting head puts Paper 15's
finite native lookup window inside the three actual packet cells.
-/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false

/-- A masked cell contains only the physical addresses of this one packet, padded by `blank`. -/
def tapeCell {s r : ℕ} {α : Type*} (L : CellLayout s r) (blank : α) (f : ℤ → α) (q : ℤ) :
    Fin (s + r) → α :=
  fun i => if L.start q + i.val < L.start (q + 1) then f (L.start q + i.val) else blank

theorem tapeCell_at_offset {s r : ℕ} {α : Type*} (L : CellLayout s r) (hs : 0 < s)
    (blank : α) (f : ℤ → α) (p : ℤ) :
    tapeCell L blank f (L.cell hs p) (L.offset hs p) = f p := by
  simp [tapeCell, L.start_add_offset hs p, (L.contains hs p).2]

/-- When a length-s interval lies in the centre cell, the whole native lookup window is
determined by the three scanned cells. -/
theorem capture_of_three {s r : ℕ} {α : Type*} (L : CellLayout s r) (hs : 0 < s)
    (blank : α) {f g : ℤ → α} {q anchor : ℤ} (hlo : L.start q ≤ anchor)
    (hhi : anchor + s ≤ L.start (q + 1))
    (cells : ∀ u, |u - q| ≤ 1 → tapeCell L blank f u = tapeCell L blank g u) :
    Native.capture s f anchor = Native.capture s g anchor := by
  funext i
  let p : ℤ := anchor + ((i.val : ℤ) - s)
  have hi := i.isLt
  have hp₁ : L.start (q-1) ≤ p := by
    have h := L.lower (q-1)
    rw [show q-1+1=q by omega] at h
    dsimp [p]; omega
  have hp₂ : p < L.start (q+1+1) := by
    have := L.lower (q+1)
    dsimp [p]; omega
  have hh := L.contains hs p
  have hm := (L.strictMono hs).monotone
  have hcell : |L.cell hs p - q| ≤ 1 := by
    apply abs_le.2
    constructor
    · by_contra! bad
      have := hm (show L.cell hs p + 1 ≤ q - 1 by omega)
      omega
    · by_contra! bad
      have := hm (show q+1+1 ≤ L.cell hs p by omega)
      omega
  have h := congrFun (cells _ hcell) (L.offset hs p)
  change f p = g p
  simpa only [tapeCell_at_offset] using h

/-- The fixed-fuel interpreter agrees with the first paper's native run even across a halt. -/
theorem advance_run (M : TM) (w : List Bool) (t n : ℕ) :
    (Native.advance M (readInput w) n (run M w t)).1 = run M w (t + n) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    cases h : Native.lookup M (readInput w) (run M w t) with
    | none =>
      have hh : transAt M w t = none := h
      simpa only [Native.advance, h] using (run_add_of_none hh (n+1)).1.symm
    | some z =>
      have hc : Native.commit (run M w t) z = run M w (t+1) := by
        rw [run_succ, next, Native.step_eq_lookup, h]; rfl
      simp only [Native.advance, h, hc]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (t+1)

/-- For two actual source configurations on a common set of packet centres, equality of the
state, fine positions and the three captured cells on each tape forces equality of the entire
next batch. The fresh output word is shared even when their old output prefixes differ. -/
theorem three_cell_batch {M : TM} {s r : ℕ} (L : CellLayout s r) (hs : 0 < s)
    {w v : List Bool} {c d : Config M} (hq : c.state = d.state) (hi : c.inPos = d.inPos)
    (hw : c.workPos = d.workPos)
    (hin : ∀ u, |u - L.cell hs c.inPos| ≤ 1 →
      tapeCell L none (readInput w) u = tapeCell L none (readInput v) u)
    (hwork : ∀ j u, |u - (workLayout s).cell hs (c.workPos j)| ≤ 1 →
      tapeCell (workLayout s) 0 (c.work j) u = tapeCell (workLayout s) 0 (d.work j) u) :
    let u := Native.advance M (readInput w) s c
    let v' := Native.advance M (readInput v) s d
    u.2 = v'.2 ∧ u.1.state = v'.1.state ∧ u.1.inPos = v'.1.inPos ∧ u.1.workPos = v'.1.workPos ∧
      (∀ j, Native.capture s (u.1.work j) ((workLayout s).start ((workLayout s).cell hs (c.workPos j))) =
        Native.capture s (v'.1.work j) ((workLayout s).start ((workLayout s).cell hs (c.workPos j)))) ∧
      ∃ out : List Bool, out.length ≤ s ∧ u.1.outRev = out ++ c.outRev ∧ v'.1.outRev = out ++ d.outRev := by
  let q := L.cell hs c.inPos
  let ai := min c.inPos (L.start (q+1)-s)
  have hh := L.contains hs c.inPos
  have hlq := L.lower q
  have ha₁ : L.start q ≤ ai := le_min hh.1 (by omega)
  have ha₂ : ai + s ≤ L.start (q+1) := by dsimp [ai]; omega
  have hoi₁ : 0 ≤ c.inPos - ai := sub_nonneg.2 (min_le_left _ _)
  have hend : c.inPos < L.start (q+1) := hh.2
  have hoi₂ : c.inPos - ai < s := by dsimp [ai]; omega
  let oi : Fin s := ⟨(c.inPos-ai).toNat, by omega⟩
  have hi₀ : c.inPos = ai + oi.val := by change c.inPos = ai + ((c.inPos-ai).toNat : ℤ); omega
  let W := workLayout s
  let aw (j : Fin M.k) := W.start (W.cell hs (c.workPos j))
  let ow (j : Fin M.k) : Fin s := W.offset hs (c.workPos j)
  have hw₀ (j : Fin M.k) : c.workPos j = aw j + (ow j).val := (W.start_add_offset hs _).symm
  have hI := capture_of_three L hs none ha₁ ha₂ hin
  have hW (j : Fin M.k) := capture_of_three W hs 0 (le_refl (aw j)) (W.lower _) (hwork j)
  let wrk := fun j => Native.capture s (c.work j) (aw j)
  let cfg := Native.localConfig M s c.state oi ow wrk
  let inp := Native.windowRead (Native.capture s (readInput w) ai) none
  let localRun := Native.advance M inp s cfg
  obtain ⟨h₁, e₁⟩ := Native.native_batch_local M s w c ai aw oi ow hi₀ hw₀
  have h₂ : Native.WindowAgrees s ai aw d.outRev (Native.advance M (readInput v) s d).1 localRun.1 ∧
      (Native.advance M (readInput v) s d).2 = localRun.2 := by
    have hd := Native.native_batch_local M s v d ai aw oi ow (hi.symm.trans hi₀)
      (fun j => (congrFun hw j).symm.trans (hw₀ j))
    dsimp only [localRun, cfg, wrk, inp]
    simpa only [← hq, ← hI, ← hW] using hd
  refine ⟨e₁.trans h₂.2.symm, h₁.state.trans h₂.1.state.symm, h₁.inputPos.trans h₂.1.inputPos.symm,
    funext fun j => (h₁.workPos j).trans (h₂.1.workPos j).symm, ?_, ?_⟩
  · intro j
    funext i
    have hfit : Native.Fits s 0 ((i.val : ℤ) - s) := by
      have := i.isLt
      unfold Native.Fits; omega
    exact (h₁.cells j _ hfit).trans (h₂.1.cells j _ hfit).symm
  · refine ⟨localRun.1.outRev, ?_, h₁.output, h₂.1.output⟩
    change (Native.advance M inp s cfg).1.outRev.length ≤ s
    simpa only [show cfg.outRev.length = 0 from rfl, zero_add] using Native.advance_output_le M inp s cfg

end TapeStorageRates.PacketCompiler

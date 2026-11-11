import AdaptiveTransfer.ScanLoader
import AdaptiveTransfer.ReplayCounting

/-! A total local decoder for completed scan archives from actual spatial
checkpoints. The chosen compatible input is only a definition on messages;
scan locality proves that every compatible input gives the same old symbol.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose Transpose.Tape.Impl

variable {r : ℕ} {S A : Fin r → Type*} {B : Type*}
variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S)

abbrev SpatialLabel (S : Fin r → Type*) (K : ℕ) := Fin K → ScanStates S

def spatialLabel (R K : ℕ) (w : List Bool) : SpatialLabel S K :=
  fun i => scan F s₀ w (i.val * (R + 1))

def rawWindow (R : ℕ) (w : List Bool) (z : ℤ) : Fin (2 * R + 1) → Option Bool :=
  fun i => readInput w (windowAddress z R i)

theorem rawWindow_bits {R i : ℕ} {w x : List Bool}
    (hw : rawWindow R w i = rawWindow R x i)
    {n : ℕ} (hn₁ : i - R ≤ n) (hn₂ : n ≤ i) : w[n]?.getD false = x[n]?.getD false := by
  have hnabs : ((n : ℤ) - (i : ℤ)).natAbs ≤ R := by
    have ha : |(n : ℤ) - (i : ℤ)| ≤ (R : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    rw [← Int.natCast_natAbs] at ha
    exact_mod_cast ha
  obtain ⟨j, hj⟩ := windowAddress_covers hnabs
  have h := congrFun hw j
  simp only [rawWindow, hj, readInput_natCast, nth_eq_getElem?] at h
  exact congrArg (fun a : Option Bool => a.getD false) h

theorem spatialLabel_scan {P R K i : ℕ} {w x : List Bool}
    (hcover : P ≤ (R + 1) * K) (hi : i < P)
    (hl : spatialLabel F s₀ R K w = spatialLabel F s₀ R K x)
    (hw : rawWindow R w i = rawWindow R x i) : scan F s₀ w i = scan F s₀ x i := by
  have hindex : i / (R + 1) < K := (Nat.div_lt_iff_lt_mul (by omega)).mpr
    (by simpa only [Nat.mul_comm] using hi.trans_le hcover)
  let j : Fin K := ⟨i / (R + 1), hindex⟩
  let a := j.val * (R + 1)
  have hdiv : i % (R + 1) + a = i := by
    simpa only [a, j, Nat.mul_comm] using Nat.mod_add_div i (R + 1)
  have hmod := Nat.mod_lt i (by omega : 0 < R + 1)
  have hai : a ≤ i := by omega
  have hgap : i - a ≤ R := by omega
  have ha : scan F s₀ w a = scan F s₀ x a := congrFun hl j
  funext ν
  rw [scan_eq_scanState, scan_eq_scanState]
  apply (scanState_window (fun _ => F ν) (s₀ ν)
    (fun n => w[n]?.getD false) (fun n => x[n]?.getD false) hai hgap ?_ ?_).1
  · simpa only [← scan_eq_scanState] using congrFun ha ν
  · exact fun n hn₁ hn₂ => rawWindow_bits hw hn₁ hn₂

/-- Actual label/window agreement determines every completed archive symbol,
including both markers and every exterior blank. -/
theorem archive_locality {P R K : ℕ} {w x : List Bool}
    (hcover : P ≤ (R + 1) * K) (hwP : w.length = P) (hxP : x.length = P)
    (hl : spatialLabel F s₀ R K w = spatialLabel F s₀ R K x)
    (j : Fin r) (z : ℤ) (hwindow : rawWindow R w z = rawWindow R x z) :
    archive (B := B) F D s₀ w j z = archive F D s₀ x j z := by
  by_cases hdata : 0 ≤ z ∧ z < (P : ℤ)
  · have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hdata.1
    have hi : z.toNat < P := by omega
    have hws : rawWindow R w (z.toNat : ℤ) = rawWindow R x (z.toNat : ℤ) := by
      simpa only [hz] using hwindow
    have hs := spatialLabel_scan F s₀ hcover hi hl hws
    have hb := rawWindow_bits hws (Nat.sub_le z.toNat R) le_rfl
    unfold archive partialArchive
    rw [hwP, hxP]
    have hne : z ≠ (P : ℤ) := by omega
    have hleft : z ≠ -1 := by omega
    simp only [hne, hleft, hdata, ↓reduceIte, codeSymbol, hs, hb]
  · simp only [archive, partialArchive, hwP, hxP, hdata, ↓reduceIte]

/-- A total public function of the label, coordinate and declared local raw
window. Invalid records return blank; no correctness property is an input. -/
noncomputable def archiveGetter (P R K : ℕ) (label : SpatialLabel S K)
    (j : Fin r) (z : ℤ) (raw : Fin (2 * R + 1) → Option Bool) : Symbol A B := by
  classical
  exact if h : ∃ w : List Bool, w.length = P ∧ spatialLabel F s₀ R K w = label ∧
      rawWindow R w z = raw then
    archive F D s₀ (Classical.choose h) j z
  else blank

theorem archiveGetter_correct {P R K : ℕ} (hcover : P ≤ (R + 1) * K)
    (w : List Bool) (hw : w.length = P) (j : Fin r) (z : ℤ) :
    archiveGetter (B := B) F D s₀ P R K (spatialLabel F s₀ R K w) j z
      (rawWindow R w z) = archive F D s₀ w j z := by
  classical
  unfold archiveGetter
  have h : ∃ x : List Bool, x.length = P ∧ spatialLabel F s₀ R K x = spatialLabel F s₀ R K w ∧
      rawWindow R x z = rawWindow R w z := ⟨w, hw, rfl, rfl⟩
  rw [dite_eq_left h]
  obtain ⟨hx, hl, hr⟩ := Classical.choose_spec h
  exact archive_locality F D s₀ hcover hx hw hl j z hr

theorem spatialLabel_card [∀ j, Fintype (S j)] (K : ℕ) :
    Fintype.card (SpatialLabel S K) = (Fintype.card (ScanStates S)) ^ K := by
  simp [SpatialLabel]

/-- The allowed radius uses a fixed number of checkpoint slots, independent
of the input length and entry width. Padding is part of the paid finite label. -/
theorem macroscopic_checkpoint_cover {P K : ℕ} (hK : 0 < K) : P ≤ (P / K + 1) * K := by
  have hd := Nat.mod_add_div P K
  have hm := Nat.mod_lt P hK
  nlinarith

end AdaptiveTransfer.ScanLoader

import SharedDecoders.CapacityMaskLocalWindows
import SharedDecoders.CapacityMaskRunSpectrum

/-! # Actual run expectations, coordinate sensitivity and the random bound

Run starts are expressed by literal windows of mask coordinates. Their two
favourable assignments are counted by an explicit equivalence with `Bool`.
-/

namespace SharedDecoders.CapacityMaskProbability

open Module CapacityRuns
open scoped BigOperators

def RunWindow {r : ℕ} (x : Fin (r+1) → Bool) : Prop :=
  ∀ j : Fin r, x j.succ = !x 0

noncomputable def runWindowIndicator {r : ℕ} (x : Fin (r+1) → Bool) : ℝ := by
  classical
  exact if RunWindow x then 1 else 0

def runWindowEquiv (r : ℕ) : {x : Fin (r+1) → Bool // RunWindow x} ≃ Bool where
  toFun x := x.val 0
  invFun a := ⟨Fin.cons a (fun _ => !a), by intro j; simp⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact (x.property j).symm
  right_inv _ := rfl

theorem avg_runWindowIndicator (r : ℕ) :
    avg (runWindowIndicator (r := r)) = 1/(2 : ℝ)^r := by
  classical
  change prob (RunWindow (r := r)) = _
  rw [prob_eq_card, Fintype.card_congr (runWindowEquiv r)]
  simp only [Fintype.card_bool, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_ofNat, pow_succ]
  field_simp
  push_cast
  ring

def runOffset {d : ℕ} (r : ℕ) (k : Fin (r+1)) : ZMod d := (k.val : ZMod d)-1

@[simp] theorem runOffset_zero {d r : ℕ} : runOffset (d := d) r 0 = -1 := by
  simp [runOffset]

@[simp] theorem runOffset_succ {d r : ℕ} (k : Fin r) :
    runOffset (d := d) r k.succ = (k.val : ZMod d) := by
  simp [runOffset, Nat.cast_add]

theorem start_iff_runWindow {d r : ℕ} (hr : 0<r) (p : ZMod d → Bool) (x : ZMod d) :
    Start p 1 r x ↔ RunWindow (fun k => p (x+runOffset r k)) := by
  simp only [RunWindow,runOffset_succ,runOffset_zero,← sub_eq_add_neg]
  constructor
  · rintro ⟨hchange,hprefix⟩ j
    have hh := hprefix j.val j.isLt
    simp only [nsmul_eq_mul,mul_one] at hh
    exact hh.trans (Bool.eq_not_iff.mpr hchange.symm)
  · intro h
    have hzero := h ⟨0,hr⟩
    simp only [Nat.cast_zero,add_zero] at hzero
    refine ⟨(Bool.eq_not_iff.mp hzero).symm,?_⟩
    intro j hj
    have hh := h ⟨j,hj⟩
    simpa only [nsmul_eq_mul,mul_one] using hh.trans hzero.symm

variable {d : ℕ} [NeZero d]

theorem runCount_eq_windowSum (p : ZMod d → Bool) (r : ℕ) (hr : 0<r) :
    (runCount p 1 r : ℝ) = windowSum (runOffset r) runWindowIndicator p := by
  classical
  simp only [runCount,Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero,windowSum,runWindowIndicator]
  apply Finset.sum_congr rfl
  intro x _
  rw [start_iff_runWindow hr p x]

omit [NeZero d] in
theorem runOffset_injective (r : ℕ) (hr : r<d) :
    Function.Injective (runOffset (d := d) r) := by
  intro i j hij
  have he := congrArg (fun z : ZMod d => z+1) hij
  simp only [runOffset,sub_add_cancel] at he
  apply Fin.ext
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt (show i.val<d by omega),
    ZMod.val_natCast_of_lt (show j.val<d by omega)] using hh

theorem runCount_mean (r : ℕ) (hr : 0<r) (hrd : r<d) :
    avg (fun p : ZMod d → Bool => (runCount p 1 r : ℝ)) = (d : ℝ)/(2 : ℝ)^r := by
  have he : (fun p : ZMod d → Bool => (runCount p 1 r : ℝ)) =
      windowSum (runOffset r) runWindowIndicator := funext fun p => runCount_eq_windowSum p r hr
  rw [he,windowSum_mean _ (runOffset_injective r hrd),avg_runWindowIndicator,ZMod.card]
  ring

theorem runCount_boundedChanges (r : ℕ) (hr : 0<r) :
    BoundedChanges (fun p : ZMod d → Bool => (runCount p 1 r : ℝ))
      (fun _ => (r+1 : ℕ)) := by
  have he : (fun p : ZMod d → Bool => (runCount p 1 r : ℝ)) =
      windowSum (runOffset r) runWindowIndicator := funext fun p => runCount_eq_windowSum p r hr
  rw [he]
  apply windowSum_boundedChanges
  intro x
  dsimp [runWindowIndicator]
  split <;> norm_num

noncomputable def runSpectrum (p : ZMod d → Bool) : ℝ :=
  (1/4)*(runCount p 1 1 : ℝ)+(1/8)*(runCount p 1 4 : ℝ)+(1/8)*(runCount p 1 13 : ℝ)

theorem runSpectrum_mean (hd : 13<d) :
    avg (runSpectrum (d := d)) = (8705/65536 : ℝ)*d := by
  change avg (fun p : ZMod d → Bool => (1/4)*(runCount p 1 1 : ℝ)+
    (1/8)*(runCount p 1 4 : ℝ)+(1/8)*(runCount p 1 13 : ℝ)) = _
  simp only [avg_add,avg_const_mul,
    runCount_mean (d := d) 1 (by omega) (by omega),
    runCount_mean (d := d) 4 (by omega) (by omega),
    runCount_mean (d := d) 13 (by omega) hd]
  ring

theorem runSpectrum_boundedChanges :
    BoundedChanges (runSpectrum (d := d)) (fun _ => (23/8 : ℝ)) := by
  have hh := ((runCount_boundedChanges (d := d) 1 (by omega)).const_mul (1/4) (by norm_num)).add
    ((runCount_boundedChanges (d := d) 4 (by omega)).const_mul (1/8) (by norm_num))
  have hh' := hh.add ((runCount_boundedChanges (d := d) 13 (by omega)).const_mul (1/8) (by norm_num))
  norm_num at hh'
  exact hh'

theorem runSpectrum_upper_tail (hd : 13<d) (ε : ℝ) (hε : 0≤ε) :
    prob (fun p : ZMod d → Bool => (8705/65536+ε)*d ≤ runSpectrum p) ≤
      Real.exp (-128*ε^2*d/529) := by
  have hh := boundedDifferences_upper (runSpectrum (d := d)) (fun _ => (23/8 : ℝ))
    (fun _ => by norm_num) runSpectrum_boundedChanges (ε*d) (by positivity)
  rw [runSpectrum_mean hd] at hh
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card] at hh
  have he : (fun p : ZMod d → Bool => (8705/65536 : ℝ)*d+ε*d≤runSpectrum p) =
      (fun p => (8705/65536+ε)*d≤runSpectrum p) := by
    funext p
    rw [add_mul]
  rw [he] at hh
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  convert hh using 1
  congr 1
  field_simp
  ring

def SpectrumGood (ε : ℝ) (p : ZMod d → Bool) : Prop :=
  runSpectrum p ≤ (8705/65536+ε)*d

theorem spectrum_bad_probability (hd : 13<d) (ε : ℝ) (hε : 0≤ε) :
    prob (fun p : ZMod d → Bool => ¬SpectrumGood ε p) ≤
      Real.exp (-128*ε^2*d/529) := by
  exact (prob_mono (fun _ hp => (lt_of_not_ge hp).le)).trans
    (runSpectrum_upper_tail hd ε hε)

/-- One explicitly defined mask event controls all source dimensions, over
all coefficient fields and with arbitrary coupled entry modules/decoders. -/
theorem SpectrumGood.source_bound {F A : Type*} [Field F] [AddCommGroup A]
    [Module F A] [FiniteDimensional F A] (hd : 1<d) {ε : ℝ} {p : ZMod d → Bool}
    (hp : SpectrumGood ε p) {C : Submodule F (State d A)} (hC : IsSharedCode F p C) :
    (finrank F C : ℝ) ≤ (41473/65536+ε)*(d : ℝ)^2*finrank F A+
      (3/4)*(d : ℝ)*finrank F A := by
  have hn := hC.run_spectrum_three hd
  have hr : (8 : ℝ)*finrank F C ≤ 4*((d : ℝ)*d*finrank F A)+
      2*(d : ℝ)*finrank F A*(runCount p 1 1 : ℝ)+
      (d : ℝ)*finrank F A*(runCount p 1 4 : ℝ)+
      (d : ℝ)*finrank F A*(runCount p 1 13 : ℝ)+6*(d : ℝ)*finrank F A := by
    exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0≤(d : ℝ)*finrank F A by positivity)
  dsimp [SpectrumGood,runSpectrum] at hm
  nlinarith only [hr,hm]

end SharedDecoders.CapacityMaskProbability

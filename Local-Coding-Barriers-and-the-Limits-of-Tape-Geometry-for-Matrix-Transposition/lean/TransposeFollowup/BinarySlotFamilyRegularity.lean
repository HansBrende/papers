import TransposeFollowup.BinarySlotRegularity
import Mathlib.Topology.Sequences
import Mathlib.Algebra.BigOperators.Fin

/-! One finite-product compactness call handles every slot simultaneously.
The optional padding is analytic only. Validity need hold only eventually;
clipping the initial ratios makes the compactness map total. -/
namespace TransposeFollowup.BinaryBankSlot
open Classical Set Filter Topology Finset AffineMotion
set_option autoImplicit false

theorem finite_affine_approximation_subsequence {K : ℕ} {P : ℕ → ℕ}
    (hP : ∀ i, 0 < P i) (ops : ℕ → Fin K → Option BinaryBankOperation.Operation)
    (hv : ∀ᶠ i in atTop, ∀ j, Valid (P i) (ops i j))
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop) {H : ℝ} (hH : 0 ≤ H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (J : ℕ) (es : Fin K → ℕ → ℝ)
      (qs : Fin K → ℕ → ℕ → Fin 2 → ℝ → ℝ),
      0 < J ∧ (∀ j, Tendsto (es j) atTop (𝓝 0)) ∧ ∀ᶠ i in atTop, ∀ j A,
        (∀ h, HasAffineIntervalCover J (qs j i A h) H) ∧
        ∀ h t, |(path (P (φ i)) (ops (φ i) j) h (⌊(P (φ i) : ℝ)*t⌋₊-A) : ℝ)/P (φ i)-
          qs j i A h t| ≤ es j i := by
  let u : ℕ → Fin K → Icc (0 : ℝ) 1 := fun i j =>
    ⟨((min (stride (ops i j)) (P i) : ℕ) : ℝ)/P i,by
      have hp : (0 : ℝ) < P i := by exact_mod_cast hP i
      exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,
        (div_le_one hp).mpr (by exact_mod_cast Nat.min_le_right (stride (ops i j)) (P i))⟩⟩
  obtain ⟨α,φ,hφ,hconv⟩ := CompactSpace.tendsto_subseq u
  have hvalid : ∀ᶠ i in atTop, ∀ j, Valid (P (φ i)) (ops (φ i) j) := hφ.tendsto_atTop.eventually hv
  have hratio (j : Fin K) : Tendsto (fun i => (stride (ops (φ i) j) : ℝ)/P (φ i)) atTop (𝓝 (α j : ℝ)) := by
    have hc := (continuous_subtype_val : Continuous (fun x : Icc (0 : ℝ) 1 => (x : ℝ))).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mp hconv j)
    apply hc.congr'
    filter_upwards [hvalid] with i hi
    simp only [Function.comp_apply,u,Nat.min_eq_left (stride_le _ _ (hi j))]
  have hex (j : Fin K) := affine_approximation_of_ratio (fun i => hP (φ i))
    (fun i => ops (φ i) j) (hvalid.mono fun i hi => hi j) (hPinf.comp hφ.tendsto_atTop)
    (α j).property.1 (hratio j) hH
  choose Js es qs hJs hes hqs using hex
  let J := (∑ j, Js j)+1
  have hj (j : Fin K) : Js j ≤ J :=
    (Finset.single_le_sum (fun a _ => Nat.zero_le (Js a)) (Finset.mem_univ j)).trans (Nat.le_add_right _ _)
  refine ⟨φ,hφ,J,es,qs,by dsimp [J]; omega,hes,?_⟩
  filter_upwards [Filter.eventually_all.mpr hqs] with i hi
  intro j A
  exact ⟨fun h => ((hi j A).1 h).mono (hJs j) (hj j),(hi j A).2⟩

end TransposeFollowup.BinaryBankSlot

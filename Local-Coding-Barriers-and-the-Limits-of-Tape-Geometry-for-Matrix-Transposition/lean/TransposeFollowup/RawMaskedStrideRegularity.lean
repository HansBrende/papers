import TransposeFollowup.RawMaskedStrideSmallCurve

/-! Every sequence of complete raw masked-stride executions has a
subsequence with bounded finite-affine approximants and vanishing error.
The sole subsequence selection uses mathlib compactness of [0,1] for S/P.
All raw phases, padding, clearing and the native frozen halt tail are included. -/
namespace TransposeFollowup.RawMaskedStride
open Classical Set Filter Topology AffineMotion
set_option autoImplicit false

theorem full_affine_approximation_subsequence {P S : ℕ → ℕ}
    (hP : ∀ i, 0<P i) (hS : ∀ i, 0<S i) (hSP : ∀ i, S i ≤ P i)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (modes : ℕ → Bool) (masks : ℕ → ℕ → Bool) (inputs : ℕ → List Bool)
    {H : ℝ} (hH : 0 ≤ H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (J : ℕ) (e : ℕ → ℝ) (q : ℕ → Fin 2 → ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧
        ∀ᶠ i in atTop, (∀ h, HasAffineIntervalCover J (q i h) H) ∧
          ∀ h t, |(Transpose.Tape.workTraj (machine (modes (φ i)) (masks (φ i)) (P (φ i)) (S (φ i)))
              (inputs (φ i)) ⌊(P (φ i) : ℝ)*t⌋₊ ((encoding (P (φ i)) (S (φ i))).port h) : ℝ)/P (φ i)-
              q i h t| ≤ e i := by
  let u : ℕ → Icc (0 : ℝ) 1 := fun i => ⟨(S i : ℝ)/P i,by
    have hp : (0 : ℝ)<P i := by exact_mod_cast hP i
    refine ⟨div_nonneg (Nat.cast_nonneg _) hp.le,(div_le_one hp).mpr ?_⟩
    exact_mod_cast hSP i⟩
  obtain ⟨α,φ,hφ,hconv⟩ := CompactSpace.tendsto_subseq u
  have hratio : Tendsto (fun i => (S (φ i) : ℝ)/P (φ i)) atTop (𝓝 (α : ℝ)) :=
    (continuous_subtype_val : Continuous (fun x : Icc (0 : ℝ) 1 => (x : ℝ))).continuousAt.tendsto.comp hconv
  have hinf := hPinf.comp hφ.tendsto_atTop
  refine ⟨φ,hφ,?_⟩
  by_cases hz : (α : ℝ)=0
  · rw [hz] at hratio
    refine ⟨243,fun i => (9*(S (φ i) : ℝ)+6)/P (φ i),
      fun i h t => if h=0 then smallBankApproximation (P (φ i)) ((P (φ i) : ℝ)*t)/P (φ i) else 0,?_,?_⟩
    · have hrec : Tendsto (fun i => (6 : ℝ)/P (φ i)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hinf
      simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using (hratio.const_mul 9).add hrec
    · exact Filter.Eventually.of_forall fun i => by
        have hc := full_small_affine_approximation (hP (φ i)) (hS (φ i)) hH
          (modes (φ i)) (masks (φ i)) (inputs (φ i))
        constructor
        · intro h
          fin_cases h
          · exact hc.1
          · exact hc.2.1
        · intro h t
          fin_cases h
          · exact (hc.2.2 t).1
          · exact (hc.2.2 t).2
  · have hα : 0<(α : ℝ) := lt_of_le_of_ne α.property.1 (Ne.symm hz)
    obtain ⟨B,hB⟩ := eventually_bounded_groups (fun i => hP (φ i)) hα hratio
    refine ⟨81*9^(B+1),fun i => 2*((B : ℝ)+3)/P (φ i),
      fun i h t => if h=0 then bankApproximation (P (φ i)) (S (φ i)) ((P (φ i) : ℝ)*t)/P (φ i)
        else scratchApproximation (P (φ i)) (S (φ i)) ((P (φ i) : ℝ)*t)/P (φ i),
      tendsto_const_nhds.div_atTop hinf,?_⟩
    filter_upwards [hB] with i hi
    have hc := full_bounded_affine_approximation (hP (φ i)) (hS (φ i)) hi hH
      (modes (φ i)) (masks (φ i)) (inputs (φ i))
    constructor
    · intro h
      fin_cases h
      · exact hc.1
      · exact hc.2.1
    · intro h t
      fin_cases h
      · exact (hc.2.2 t).1
      · exact (hc.2.2 t).2

end TransposeFollowup.RawMaskedStride

import TransposeFollowup.RawMixedBinaryWordRegularity
import TransposeFollowup.RawMixedBinaryWordResources
import TransposeFollowup.PhysicalAffineApproximationObstruction

/-! No bounded mixed binary word family transposes sets of coentropy o(P).
All public types, masks, strides and offsets may vary with size. Every
native premise is derived from the paid executor; no uniform generator,
prepared input or geometric hypothesis is imposed on the word family. -/
namespace TransposeFollowup.RawMixedBinaryWord
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl AffineMotion
open BinaryBankOperation (Operation)
open MixedBinaryWord (Valid)
set_option autoImplicit false

theorem no_high_entropy_transpose {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {K : ℕ} (ops : ℕ → List Operation)
    (hv : ∀ᶠ i in atTop, Valid (inputLength (ns i)) (ops i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w = encode (ns i) (entryBits (ns i)) A ∧
      outputWord (inputLength (ns i)) (ops i) w = encode (ns i) (entryBits (ns i)) (transpose A)) : False := by
  let Ms : ℕ → TM := fun i => machine (inputLength (ns i)) (ops i)
  apply no_subsequential_physical_affine_fast_approximation (k:=2) (G:=3) (c:=7+27*(K : ℝ))
    hns (Ms:=Ms) (fun _ => rfl) (fun i => cellBits_eq _ _)
    (state_bits_vanish hns ops hv hK) hm hmL
  · filter_upwards [hcorr,hv,hK,(inputLength_tendsto hns).eventually_gt_atTop 0] with i hi hvi hki hpi
    intro w hw
    have hp : 0 < inputLength (ns i) := by exact_mod_cast hpi
    obtain ⟨A,hA,hout⟩ := hi w hw
    have ht := bounded_ticks (inputLength (ns i)) K hp (ops i) hvi hki
    have hn := native_correct (inputLength (ns i)) hp (ops i) hvi w
    exact ⟨ticks (inputLength (ns i)) (ops i),by exact_mod_cast ht,hn.2.1,A,hA,hn.2.2.1.trans hout⟩
  · intro φ hφ ws _
    have hinf := (inputLength_tendsto hns).comp hφ.tendsto_atTop
    have hp : ∀ᶠ i in atTop, 0 < inputLength (ns (φ i)) :=
      (hinf.eventually_gt_atTop 0).mono (fun i hi => by
        dsimp only [Function.comp_apply] at hi
        exact_mod_cast hi)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hp
    let shift : ℕ → ℕ := fun i => i+N
    have hshift : StrictMono shift := fun a b hab => Nat.add_lt_add_right hab N
    have hpall (i : ℕ) : 0 < inputLength (ns (φ (shift i))) := hN (shift i) (by dsimp [shift]; omega)
    obtain ⟨ψ,hψ,J,e,q,he,hq⟩ := full_affine_approximation_subsequence hpall
      (fun i => ops (φ (shift i))) ((hφ.comp hshift).tendsto_atTop.eventually hv)
      ((hφ.comp hshift).tendsto_atTop.eventually hK) (hinf.comp hshift.tendsto_atTop)
      (fun i => ws (φ (shift i))) (H:=((7+27*(K : ℝ))*3+1)/3) (by positivity)
    refine ⟨shift ∘ ψ,hshift.comp hψ,J,e,
      fun i t => q i ((encoding (inputLength (ns (φ (shift (ψ i))))) (ops (φ (shift (ψ i))))).port.symm t),he,?_⟩
    filter_upwards [hq] with i hi
    refine ⟨fun t => hi.1 _,?_⟩
    intro t x _
    have hx := hi.2 ((encoding (inputLength (ns (φ (shift (ψ i))))) (ops (φ (shift (ψ i))))).port.symm t) x
    have hp := (encoding (inputLength (ns (φ (shift (ψ i))))) (ops (φ (shift (ψ i))))).port.apply_symm_apply t
    rw [hp] at hx
    exact hx

end TransposeFollowup.RawMixedBinaryWord
